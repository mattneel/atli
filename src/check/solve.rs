use std::collections::{BTreeMap, BTreeSet};
use std::marker::PhantomData;

use crate::grade::Bound;

pub const SOLVER_THRESHOLD_K: usize = 6;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct UnknownId(pub usize);

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BoundExpr {
    Const(Bound),
    Unknown(UnknownId),
    Add(Box<BoundExpr>, Box<BoundExpr>),
    Join(Box<BoundExpr>, Box<BoundExpr>),
}

impl BoundExpr {
    #[must_use]
    pub fn constant(bound: Bound) -> Self {
        Self::Const(bound)
    }

    #[must_use]
    pub fn unknown(id: UnknownId) -> Self {
        Self::Unknown(id)
    }

    #[must_use]
    pub fn seq(self, rhs: Self) -> Self {
        Self::Add(Box::new(self), Box::new(rhs))
    }

    #[must_use]
    pub fn join(self, rhs: Self) -> Self {
        Self::Join(Box::new(self), Box::new(rhs))
    }

    #[must_use]
    pub fn eval(&self, values: &BTreeMap<UnknownId, Bound>) -> Bound {
        match self {
            Self::Const(bound) => *bound,
            Self::Unknown(id) => values.get(id).copied().unwrap_or(Bound::ZERO),
            Self::Add(lhs, rhs) => lhs.eval(values).sequential(rhs.eval(values)),
            Self::Join(lhs, rhs) => lhs.eval(values).join(rhs.eval(values)),
        }
    }

    fn deps(&self, out: &mut BTreeSet<UnknownId>) {
        match self {
            Self::Const(_) => {}
            Self::Unknown(id) => {
                out.insert(*id);
            }
            Self::Add(lhs, rhs) | Self::Join(lhs, rhs) => {
                lhs.deps(out);
                rhs.deps(out);
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Constraint {
    pub target: UnknownId,
    pub expr: BoundExpr,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct ConstraintSystem {
    next: usize,
    constraints: Vec<Constraint>,
}

impl ConstraintSystem {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    pub fn fresh_unknown(&mut self) -> UnknownId {
        let id = UnknownId(self.next);
        self.next += 1;
        id
    }

    pub fn constrain(&mut self, target: UnknownId, expr: BoundExpr) {
        debug_assert!(target.0 < self.next, "constraint target must exist");
        self.constraints.push(Constraint { target, expr });
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.next
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.next == 0
    }

    #[must_use]
    pub fn constraints(&self) -> &[Constraint] {
        &self.constraints
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct SolverStats {
    pub scc_count: usize,
    pub scc_sizes: Vec<usize>,
    pub iterations: Vec<usize>,
    pub widening_fires: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SolverOutput {
    pub values: BTreeMap<UnknownId, Bound>,
    pub stats: SolverStats,
}

/// Pending grade state from `docs/calculus.md §7.3` and the under-allocation warning in
/// §2.3. A `PendingGrade` is write-only solver state; it deliberately has no accessor for
/// allocation consumers.
pub struct PendingGrade<T> {
    expr: BoundExpr,
    _phase: PhantomData<T>,
}

/// Certified grade state from `docs/calculus.md §7.3`: the SCC fixpoint has converged or
/// safely widened upward, so consumers may read the grade.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CertifiedGrade(Bound);

impl<T> PendingGrade<T> {
    #[must_use]
    pub fn new(expr: BoundExpr) -> Self {
        Self {
            expr,
            _phase: PhantomData,
        }
    }

    #[must_use]
    pub fn certify(self, values: &BTreeMap<UnknownId, Bound>) -> CertifiedGrade {
        CertifiedGrade(self.expr.eval(values))
    }
}

impl CertifiedGrade {
    #[must_use]
    pub fn get(self) -> Bound {
        self.0
    }
}

#[must_use]
pub fn solve(system: &ConstraintSystem) -> SolverOutput {
    let mut values = (0..system.next)
        .map(|idx| (UnknownId(idx), Bound::ZERO))
        .collect::<BTreeMap<_, _>>();
    let sccs = strongly_connected_components(system);
    let mut stats = SolverStats {
        scc_count: sccs.len(),
        scc_sizes: sccs.iter().map(Vec::len).collect(),
        ..SolverStats::default()
    };

    for scc in sccs {
        let mut converged = false;
        for iteration in 1..=SOLVER_THRESHOLD_K {
            let next = apply_scc(system, &values, &scc, false);
            if scc.iter().all(|id| values[id] == next[id]) {
                stats.iterations.push(iteration);
                converged = true;
                break;
            }
            for id in &scc {
                values.insert(*id, next[id]);
            }
        }
        if !converged {
            let next = apply_scc(system, &values, &scc, true);
            for id in &scc {
                if next[id] == Bound::Omega && values[id] != Bound::Omega {
                    stats.widening_fires += 1;
                }
                values.insert(*id, next[id]);
            }
            stats.iterations.push(SOLVER_THRESHOLD_K + 1);
        }
    }

    SolverOutput { values, stats }
}

fn apply_scc(
    system: &ConstraintSystem,
    values: &BTreeMap<UnknownId, Bound>,
    scc: &[UnknownId],
    widen: bool,
) -> BTreeMap<UnknownId, Bound> {
    let mut next = values.clone();
    for id in scc {
        let mut rhs = Bound::ZERO;
        for constraint in system.constraints.iter().filter(|c| c.target == *id) {
            rhs = rhs.join(constraint.expr.eval(values));
        }
        let current = values[id];
        let candidate = current.join(rhs);
        let widened = if widen && grows(current, candidate) {
            Bound::Omega
        } else {
            candidate
        };
        next.insert(*id, widened);
    }
    next
}

fn grows(current: Bound, next: Bound) -> bool {
    match (current, next) {
        (Bound::Omega, _) | (_, Bound::Omega) => false,
        (Bound::Finite(a), Bound::Finite(b)) => b > a,
    }
}

fn strongly_connected_components(system: &ConstraintSystem) -> Vec<Vec<UnknownId>> {
    struct Tarjan<'a> {
        system: &'a ConstraintSystem,
        index: usize,
        stack: Vec<UnknownId>,
        on_stack: BTreeSet<UnknownId>,
        indices: BTreeMap<UnknownId, usize>,
        lowlinks: BTreeMap<UnknownId, usize>,
        sccs: Vec<Vec<UnknownId>>,
    }

    impl Tarjan<'_> {
        fn strong_connect(&mut self, v: UnknownId) {
            self.indices.insert(v, self.index);
            self.lowlinks.insert(v, self.index);
            self.index += 1;
            self.stack.push(v);
            self.on_stack.insert(v);

            for w in outgoing(self.system, v) {
                if !self.indices.contains_key(&w) {
                    self.strong_connect(w);
                    let low_v = self.lowlinks[&v].min(self.lowlinks[&w]);
                    self.lowlinks.insert(v, low_v);
                } else if self.on_stack.contains(&w) {
                    let low_v = self.lowlinks[&v].min(self.indices[&w]);
                    self.lowlinks.insert(v, low_v);
                }
            }

            if self.lowlinks[&v] == self.indices[&v] {
                let mut scc = Vec::new();
                loop {
                    let w = self.stack.pop().expect("tarjan stack nonempty");
                    self.on_stack.remove(&w);
                    scc.push(w);
                    if w == v {
                        break;
                    }
                }
                self.sccs.push(scc);
            }
        }
    }

    let mut tarjan = Tarjan {
        system,
        index: 0,
        stack: Vec::new(),
        on_stack: BTreeSet::new(),
        indices: BTreeMap::new(),
        lowlinks: BTreeMap::new(),
        sccs: Vec::new(),
    };
    for idx in 0..system.next {
        let id = UnknownId(idx);
        if !tarjan.indices.contains_key(&id) {
            tarjan.strong_connect(id);
        }
    }
    tarjan.sccs.reverse();
    tarjan.sccs
}

fn outgoing(system: &ConstraintSystem, target: UnknownId) -> BTreeSet<UnknownId> {
    let mut deps = BTreeSet::new();
    for constraint in system.constraints.iter().filter(|c| c.target == target) {
        constraint.expr.deps(&mut deps);
    }
    deps
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn solver_handles_multi_node_scc() {
        let mut system = ConstraintSystem::new();
        let a = system.fresh_unknown();
        let b = system.fresh_unknown();
        system.constrain(
            a,
            BoundExpr::unknown(b).join(BoundExpr::constant(Bound::finite(1))),
        );
        system.constrain(b, BoundExpr::unknown(a));
        let solved = solve(&system);
        assert_eq!(solved.values[&a], Bound::finite(1));
        assert_eq!(solved.values[&b], Bound::finite(1));
        assert!(solved.stats.scc_sizes.contains(&2));
    }

    #[test]
    fn solver_widens_growing_cycle_to_omega() {
        let mut system = ConstraintSystem::new();
        let a = system.fresh_unknown();
        system.constrain(
            a,
            BoundExpr::unknown(a).seq(BoundExpr::constant(Bound::finite(1))),
        );
        let solved = solve(&system);
        assert_eq!(solved.values[&a], Bound::Omega);
        assert!(solved.stats.widening_fires > 0);
    }
}
