FLAGS=
SRC=src

.PHONY: all proofs

all: proofs

proofs: ${SRC}
	isabelle build -d src Homework14
