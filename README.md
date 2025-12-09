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

## Security results
This work includes two main security results about the PLINK compiler:
- Theorem 1, stating that the translation from the intermediate representation down to PLONK’s constraint systems preserves satisfiability. This is mechanized in the file `src/CompilerProof.hs`.
- Theorem 2, stating that the translation from the high-level PLINK language to the intermediate representation respects the semantics. This (together with the auxiliary lemma) is mechanized in the file `src/LabelingProof.hs`.

Additionally, the inlining and constant propagation optimizations are proven to preserve the semantics. The proofs are included in the respective files under `src/Optimizations/`.
