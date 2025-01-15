# PLINK: Verified Generation of Constraints for the PLONK protocol
PLINK is a Domain-Specific Language for expressing statements to be proven with
the [PLONK](https://eprint.iacr.org/2019/953) zero-knowledge protocol. In
particular, PLINK programs get compiled to a system of algebraic constraints
that PLONK takes as input.

The compiler is implemented in Haskell, and its correctness is verified using
[Liquid Haskell](https://ucsd-progsys.github.io/liquidhaskell/) as a theorem
proving assistant. Because PLINK itself is implemented as an Embedded DSL in
Haskell, one can also use Liquid Haskell to prove certain properties about PLINK
programs.
