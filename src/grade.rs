//! Grade algebra for `λ_Atli`.
//!
//! Implements `docs/calculus.md §2`: uniqueness `Q`, effects `Eff`, boundedness
//! `Bound = ℕ ∪ {ω}`, and a single-arena `Region` model for Sprint 01.

use std::collections::BTreeSet;
use std::fmt;

/// `Q = {0, 1, ω}` with QTT addition/multiplication (`calculus.md §2.1`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Q {
    Zero,
    One,
    Omega,
}

impl Q {
    #[must_use]
    pub const fn add(self, rhs: Self) -> Self {
        use Q::{Omega, One, Zero};
        match (self, rhs) {
            (Zero, q) | (q, Zero) => q,
            (One, One) | (One, Omega) | (Omega, One) | (Omega, Omega) => Omega,
        }
    }

    #[must_use]
    pub const fn mul(self, rhs: Self) -> Self {
        use Q::{Omega, One, Zero};
        match (self, rhs) {
            (Zero, _) | (_, Zero) => Zero,
            (One, q) | (q, One) => q,
            (Omega, Omega) => Omega,
        }
    }
}

/// Interned operation label (`calculus.md §2.2`, Sprint 08 multi-label amendment).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Label(&'static str);

impl Label {
    pub const L: Self = Self("L");

    #[must_use]
    pub fn intern(name: &str) -> Self {
        if name == "L" {
            return Self::L;
        }
        Self(Box::leak(name.to_string().into_boxed_str()))
    }

    #[must_use]
    pub const fn name(self) -> &'static str {
        self.0
    }
}

impl fmt::Display for Label {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.0)
    }
}

/// Effect join-semilattice `Eff = (𝒫(Label), ∪, ∅)` (`calculus.md §2.2`).
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Eff(BTreeSet<Label>);

impl Eff {
    #[must_use]
    pub fn empty() -> Self {
        Self::default()
    }

    #[must_use]
    pub fn singleton(label: Label) -> Self {
        let mut labels = BTreeSet::new();
        labels.insert(label);
        Self(labels)
    }

    #[must_use]
    pub fn join(&self, rhs: &Self) -> Self {
        Self(self.0.union(&rhs.0).copied().collect())
    }

    #[must_use]
    pub fn without(&self, label: Label) -> Self {
        let mut labels = self.0.clone();
        labels.remove(&label);
        Self(labels)
    }

    #[must_use]
    pub fn contains(&self, label: Label) -> bool {
        self.0.contains(&label)
    }

    #[must_use]
    pub fn is_subset(&self, rhs: &Self) -> bool {
        self.0.is_subset(&rhs.0)
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn labels(&self) -> impl Iterator<Item = Label> + '_ {
        self.0.iter().copied()
    }
}

impl fmt::Display for Eff {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.0.is_empty() {
            return f.write_str("∅");
        }
        let labels = self
            .0
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join(",");
        write!(f, "{{{labels}}}")
    }
}

/// Quantitative boundedness `Bound = ℕ ∪ {ω}` (`calculus.md §2.3`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Bound {
    Finite(u32),
    Omega,
}

impl Bound {
    pub const ZERO: Self = Self::Finite(0);

    #[must_use]
    pub const fn finite(value: u32) -> Self {
        Self::Finite(value)
    }

    /// Sequential frame nesting `⊕`: saturating addition with `ω` absorbing.
    #[must_use]
    pub const fn sequential(self, rhs: Self) -> Self {
        match (self, rhs) {
            (Self::Omega, _) | (_, Self::Omega) => Self::Omega,
            (Self::Finite(a), Self::Finite(b)) => match a.checked_add(b) {
                Some(sum) => Self::Finite(sum),
                None => Self::Omega,
            },
        }
    }

    /// Branch join `⊔`: max with `ω` as top.
    #[must_use]
    pub const fn join(self, rhs: Self) -> Self {
        match (self, rhs) {
            (Self::Omega, _) | (_, Self::Omega) => Self::Omega,
            (Self::Finite(a), Self::Finite(b)) => {
                if a >= b {
                    Self::Finite(a)
                } else {
                    Self::Finite(b)
                }
            }
        }
    }

    #[must_use]
    pub const fn is_finite(self) -> bool {
        matches!(self, Self::Finite(_))
    }

    #[must_use]
    pub const fn as_finite(self) -> Option<u32> {
        match self {
            Self::Finite(value) => Some(value),
            Self::Omega => None,
        }
    }
}

impl fmt::Display for Bound {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Bound::Finite(value) => write!(f, "{value}"),
            Bound::Omega => f.write_str("ω"),
        }
    }
}

/// Reduced Sprint 01 region lattice: one arena/top region (`calculus.md §2.4`, §10).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Region {
    Arena,
}

impl Region {
    #[must_use]
    pub const fn meet(self, _rhs: Self) -> Self {
        Self::Arena
    }

    #[must_use]
    pub const fn outlives(self, _rhs: Self) -> bool {
        true
    }
}

impl fmt::Display for Region {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("ρ_arena")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const QS: [Q; 3] = [Q::Zero, Q::One, Q::Omega];
    const BS: [Bound; 4] = [
        Bound::Finite(0),
        Bound::Finite(1),
        Bound::Finite(7),
        Bound::Omega,
    ];

    #[test]
    fn q_addition_and_multiplication_tables_match_spec() {
        assert_eq!(Q::One.add(Q::One), Q::Omega, "1 + 1 = ω, calculus.md §2.1");
        assert_eq!(Q::Omega.mul(Q::Zero), Q::Zero);
        assert_eq!(Q::Omega.mul(Q::One), Q::Omega);
    }

    #[test]
    fn q_semiring_laws_hold_on_finite_carrier() {
        for a in QS {
            assert_eq!(a.add(Q::Zero), a);
            assert_eq!(Q::Zero.add(a), a);
            assert_eq!(a.mul(Q::One), a);
            assert_eq!(Q::One.mul(a), a);
            assert_eq!(a.mul(Q::Zero), Q::Zero);
            assert_eq!(Q::Zero.mul(a), Q::Zero);
            for b in QS {
                assert_eq!(a.add(b), b.add(a));
                for c in QS {
                    assert_eq!(a.add(b).add(c), a.add(b.add(c)));
                    assert_eq!(a.mul(b).mul(c), a.mul(b.mul(c)));
                    assert_eq!(a.mul(b.add(c)), a.mul(b).add(a.mul(c)));
                }
            }
        }
    }

    #[test]
    fn effect_join_laws_hold() {
        let empty = Eff::empty();
        let l = Eff::singleton(Label::L);
        assert_eq!(empty.join(&l), l);
        assert_eq!(l.join(&empty), l);
        assert_eq!(l.join(&l), l, "idempotent union, calculus.md §2.2");
        assert!(empty.is_subset(&l));
        assert_eq!(l.without(Label::L), empty);
    }

    #[test]
    fn bound_operations_match_spec() {
        assert_eq!(
            Bound::Finite(1).sequential(Bound::Finite(2)),
            Bound::Finite(3)
        );
        assert_eq!(Bound::Finite(2).join(Bound::Finite(7)), Bound::Finite(7));
        assert_eq!(Bound::Omega.sequential(Bound::Finite(1)), Bound::Omega);
        assert_eq!(Bound::Omega.join(Bound::Finite(1)), Bound::Omega);
    }

    #[test]
    fn bound_monoid_and_join_laws_hold_on_samples() {
        for a in BS {
            assert_eq!(a.sequential(Bound::ZERO), a);
            assert_eq!(Bound::ZERO.sequential(a), a);
            assert_eq!(a.join(Bound::ZERO), a);
            assert_eq!(a.join(a), a);
            for b in BS {
                assert_eq!(a.join(b), b.join(a));
                for c in BS {
                    assert_eq!(a.sequential(b).sequential(c), a.sequential(b.sequential(c)));
                    assert_eq!(a.join(b).join(c), a.join(b.join(c)));
                }
            }
        }
    }

    #[test]
    fn region_single_arena_laws_are_trivial() {
        let r = Region::Arena;
        assert_eq!(r.meet(r), r);
        assert!(r.outlives(r));
    }
}
