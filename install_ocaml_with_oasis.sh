#!/bin/bash
sh <(curl -sL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)
opam init
eval `opam config env`
opam switch create 4.10.0
eval `opam config env`
opam init
eval `opam config env`
opam install ocamlfind oasis
