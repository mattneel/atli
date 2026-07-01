COQC ?= coqc
COQFLAGS ?= -Q theories Atli
VFILES := theories/Grade.v theories/Syntax.v theories/Typing.v theories/Step.v theories/Solve.v theories/Meta.v theories/Bridge.v
VOFILES := $(VFILES:.v=.vo)

.PHONY: all clean
all: $(VOFILES)

%.vo: %.v
	$(COQC) $(COQFLAGS) $<

clean:
	find theories \( -name '*.vo' -o -name '*.vos' -o -name '*.vok' -o -name '*.glob' -o -name '.*.aux' \) -delete
	rm -f .lia.cache
