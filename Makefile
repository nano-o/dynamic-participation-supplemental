LATEXMK=latexmk
LATEXMK_OPTS=-pdf
SPECS=CommitAdopt NoEquivocation
TARGETS=$(SPECS:=.pdf)
JAR=tla2tools.jar
JAR_URL=https://github.com/tlaplus/tlaplus/releases/download/v1.7.3/tla2tools.jar

all: $(TARGETS)

# Download the JAR if it does not exist
$(JAR):
	wget $(JAR_URL)

# Don't download the JAR every time
.PRECIOUS: $(JAR)

# Rule to produce .tex files from .tla files using the tla2tools.jar
%.tex: %.tla $(JAR)
	set -e; \
	TMPFILE=$$(mktemp --suffix=.tla --tmpdir=./ XXXXXXXX); \
	sed '/\* BEGIN TRANSLATION/,/\* END TRANSLATION/d' $< > "$$TMPFILE"; \
	java -cp tla2tools.jar tla2tex.TLA -shade -noPcalShade -nops "$$TMPFILE" && mv "$${TMPFILE%.tla}.tex" $@; \
	rm -f "$$TMPFILE" "$${TMPFILE%.tla}.log" "$${TMPFILE%.tla}.dvi" "$${TMPFILE%.tla}.aux"

%.pdf: %.tex
	$(LATEXMK) $(LATEXMK_OPTS) $<

clean:
	$(RM) $(SPECS:=.pdf)

define RUN_TLC
	java -cp tla2tools.jar pcal.trans -nocfg $(1).tla;
	java -XX:+UseParallelGC -cp tla2tools.jar tlc2.TLC $(1)_MC.tla;
endef

tlc: $(SPECS:=.pdf) $(SPECS:=_MC.tla) $(SPECS:=_MC.cfg) $(JAR)
	$(foreach spec,$(SPECS),$(call RUN_TLC,$(spec)))

.PHONY: all clean $(SPECS:=.clean) $(SPECS:=.tlc) tlc
