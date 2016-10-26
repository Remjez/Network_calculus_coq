SOURCES = \
Rstruct.v \
interval_bounding.v \
network_calculus_def.v \
pseudo_inv.v \
server.v \
left_continuous_ext.v
# $(wildcard *.v)

all: $(SOURCES:.v=.vo)

doc: all html/deps.png
	mkdir -p html
	coqdoc --toc --toc-depth 1 --interpolate --no-lib-name -g -d html $(SOURCES)
	sed -i html/toc.html -e 's#id="main">#id="main"><img src="deps.png" />#'

html/deps.png: all coqgraph
	mkdir -p html
	coqdep -I . -as "" *.v | ./coqgraph - | tred | dot -Tpng > $@

coqgraph: coqgraph.ml
	ocamlc.opt -o coqgraph coqgraph.ml

%.vo: %.v
	coqc $<

depend: .depend

.depend: *.v
	rm -f ./.depend
	coqdep -I . -as "" *.v > ./.depend

include .depend

clean:
	rm -rf .depend *~ *.vo *.glob html coqgraph coqgraph.cmi coqgraph.cmo

.PHONY: clean
