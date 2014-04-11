OC = ocamlopt

all: hm

hm: main.cmx
	$(OC) -o $@ $<

main.cmx: main.ml
	$(OC) -c $^

clean:
	-rm -f *.cmx *.o *.cmi hm
