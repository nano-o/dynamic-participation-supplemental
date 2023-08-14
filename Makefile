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

# Rule to produce .tex files from .tla files using the tla2tools.jar
%.tex: %.tla $(JAR)
	bash -x ./create_tex_file.sh $<

%.pdf: %.tex
	$(LATEXMK) $(LATEXMK_OPTS) $<

clean: $(SPECS:=.clean)
	$(RM) $(SPECS:=.pdf)

%.clean: %.tex
	$(LATEXMK) -C $<
	$(RM) $<

.PHONY: all clean $(SPECS:=.clean)
