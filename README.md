# latte-kernel

The (very) small kernel of the LaTTe proof assistant in Clojure(script)

[![Clojars Project](https://img.shields.io/clojars/v/latte-kernel.svg)](https://clojars.org/latte-kernel)

```
  _.--'"'.
  (  ( (   )
  (o)_    ) )
      (o)_.'


   _.--'"'.
  (  ( (   )
  (o)_    ) )
      (o)_.'
        )/

   .-.--.
  (  (   ).
  (o)_   ) )
     (o)_.'
       )/

lgbeard
```

## Overview

LaTTe is a proof assistant based on a type theory (a dependently-typed proof theory).
This repository contains the source code of its **small trusted kernel**, developed as a Clojure(script) library. Its design has been driven by the following criterion:

> A Mathematical Assistant satisfying the possibility of independent checking by a small program is said to satisfy the **de Bruijn criterion**.

see: "The Challenge of Computer Mathematics", http://www.cs.ru.nl/~freek/notes/RSpaper.pdf

It is also optimized for readability rather than efficiency, but it has been tested heavily and performs quite "acceptably".

## Organization

Each source file (extension `.cljc`) in the source directory `src/latter_kernel` is accompanied by its *literate programming* companion (extension `.cljc.md`).

The following files compose the kernel:
 - `presyntax.cljc[.md]`: the user-facing syntax and the translation (parsing) to the internal syntax
 - `syntax.cljc[.md]`: the internal syntax of lambda-terms plus syntax-level utilities (term substitution, alpha-normalization, alph-equivalence)
 - `norm.cljc[.md]`: the (beta/delta)-reduction rules, normal forms and equivalences
 - `typing.cljc[.md]`: the type inference algorithm
 - `proof.cljc[.md]`: the internal representation of declarative proofs, and the proof checker implementation

Some auxiliary files are also used (in non-literate forms):
 - `utils.cljc`: misc. utilities
 - `defenv.cljc`: the representation of named abstractions (mathematical definitions, theorems, etc.)
 - `unparser.cljc`: the regeneration of surface syntax for (proof) debugging purpose

## Usage

The kernel is a basis to develop proof assistants, not to be "consumed" directly. The literate files also explain how to develop such a kernel.

The (several) unit tests (in `test/latte_kernel`) can be executed using the following lein command:

```sh
lein test
```

or via the clojure deps `:test` profile

```sh
clj -A:test
```

----
This software is Copyright (C) 2018 Frederic Peschanski, under the MIT License (cf. `LICENSE` file)
