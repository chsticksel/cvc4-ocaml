# OCaml bindings for CVC4

# Copyright 2013 Christoph Sticksel

# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#  
# http://www.apache.org/licenses/LICENSE-2.0
#  
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

# Adapted from 
# http://www.linux-nantes.org/%7Efmonnier/OCaml/ocaml-wrapping-c.php
#
# Hints: -lstdc++ must always be at the end because the previous -l depend on it 

CXX=g++ -fPIC
CVC4_INCDIR=$(HOME)/include
CVC4_LIBDIR=$(HOME)/lib

# CFLAGS=-I/opt/local/include
# LDFLAGS=-L/opt/local/lib

# OCAMLCFLAGS=-I /opt/local/lib
# OCAMLCCOPT=-ccopt -L/opt/local/lib

# CVC4_INCDIR=/opt/local/include
# CVC4_LIBDIR=/opt/local/lib

all: cvc4.cmxa 

doc:
	mkdir -p doc
	ocamldoc -html -d doc cvc4.mli

cvc4_stubs.o: cvc4_stubs.cpp
	$(CXX) -I$(CVC4_INCDIR) $(CFLAGS) -o cvc4_stubs.o -I`ocamlc -where` -c cvc4_stubs.cpp

dllcvc4_stubs.so: cvc4_stubs.o
	ocamlmklib -o cvc4_stubs $< -L$(CVC4_LIBDIR) -lcvc4 -lstdc++

cvc4.cmi: cvc4.mli
	ocamlc -c $<

cvc4.cmo: cvc4.ml cvc4.cmi
	ocamlc -c $<

cvc4.cma: cvc4.cmo dllcvc4_stubs.so
	ocamlc -a -o $@ $< -dllib -lcvc4_stubs -ccopt -L$(CVC4_LIBDIR) -cclib -lcvc4 -cclib -lgmp -cclib -lstdc++

cvc4.cmx: cvc4.ml cvc4.cmi
	ocamlopt -c $<

cvc4.cmxa: cvc4.cmx dllcvc4_stubs.so
	ocamlopt -a -o $@ $< -cclib -lcvc4_stubs -ccopt -L$(CVC4_LIBDIR) -cclib -lcvc4  -cclib -lgmp -cclib -lstdc++

clean:
	rm -f *.[oa] *.so *.cm[ixoa] *.cmxa

cvc4_test: cvc4.cmxa cvc4_test.ml
	ocamlopt -I . $^ -o $@
