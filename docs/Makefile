# Build the pen-and-paper proof documents with Typst.
#
#   make            # build all PDFs
#   make watch      # live-rebuild lower-pen-and-paper.pdf on save
#   make clean      # remove generated PDFs

TYPST ?= typst

# Every .typ in this directory produces a same-named .pdf.
SRCS := $(wildcard *.typ)
PDFS := $(SRCS:.typ=.pdf)

.PHONY: all
all: $(PDFS)

%.pdf: %.typ
	$(TYPST) compile $< $@

.PHONY: watch
watch: lower-pen-and-paper.typ
	$(TYPST) watch lower-pen-and-paper.typ lower-pen-and-paper.pdf

.PHONY: clean
clean:
	rm -f $(PDFS)
