
exec: clear
	dune exec Titan

build: clear
	dune build

clear: 
	clear

clean: 
	dune clean

.PHONY: exec build clear clean