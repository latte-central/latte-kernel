MARKDOWNIZE_PATH = ../../../markdownize
PYTHON = python3

MARKDOWNIZE = $(PYTHON) $(MARKDOWNIZE_PATH)/markdownize.py

MFLAGS = --begin ";;{" --end ";;}" --lang "clojure" --remove-prefix ";;"

OBJS = presyntax.cljc.md syntax.cljc.md norm.cljc.md typing.cljc.md proof.cljc.md nbe.cljc.md

all: markdownize

markdownize: $(OBJS)

%.cljc.md : %.cljc
	$(MARKDOWNIZE) --input $< --output $@ $(MFLAGS)

clean:
	rm -f *~
	rm -f *.md
