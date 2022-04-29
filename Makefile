NAME=hazel

.PHONY: all build clean test

all: build

build:
	dune build @install

doc:
	dune build @doc

run:
	dune exec $(NAME)

install:
	dune install

test:
	dune runtest

clean:
	dune clean
