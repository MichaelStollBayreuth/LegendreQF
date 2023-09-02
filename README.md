# LegendreQF
Lean code formalizing a proof of Legendre's theorem on diagonal ternary quadratic forms

This repository contains *lean3* code (using mathlib3; in the `lean3` directory) and
*lean4* code (using mathlib4; in the `lean4` directory)
formalizing a proof of *Legendre's Theorem* on diagonal ternary quadratic forms:

 **Theorem.** Let $a, b, c$ be squarefree integers that are coprime in pairs.
 Then the equation
 $$a x^2 + b y^2 + c z^2 = 0$$
 has a nontrivial (i.e., not all values are zero) solution in integers if and
 only if
 1. $a, b, c$ do not have the same sign,
 2. $-ab$ is a square mod $c$,
 3. $-bc$ is a square mod $a$,
 4. $-ca$ is a sqaure mod $b$.

 It is easy to see that the conditions are necessary; the main part of the
 statement is that they are also sufficient.

 The statement implies the *Hasse Principle* (for the ternary quadratic forms considered):
 A ternary quadratic form as above has a nontrivial rational zero if and only if
 it has a nontrivial real zero and nontrivial $p$-adic zeros for all primes $p$.
 (However, this is not (yet) part of the formalization.)
