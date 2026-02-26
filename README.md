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

## Research paper
The document `plink.pdf` outlines the design of the PLINK compiler, formally states the security results, and includes several examples of verified properties of PLINK programs.

## Work in progress
In addition to the aforementioned theorems, we are working on other results that enhance the metatheory of the language:
1. The labeling process always produces _well-formed_ expressions (i.e. without clashes in the wire indices).
2. Witness generation is _sound_ (i.e. whenever it succeeds, the returned valuation is coherent with the input expression).
3. Witness generation is _complete_ (i.e. it succeeds whenever possible, meaning whenever the corresponding unlabeled expression can be evaluated).
4. If it is possible to define a valuation that is coherent with a labeled expression, then the corresponding unlabeled expression can be evaluated.

Points 2, 3 and 4 above together serve to strengthen Theorem 2: a high-level (unlabeled) expression evaluates to some value $v$ if and only if _there exists_ a valuation coherent with the corresponding IR (labeled) expression (as provided by witness generation), and such that the value in the output wire of the IR expression is $v$ too.
