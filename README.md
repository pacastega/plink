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
- Theorem 1, stating that the translation from the high-level PLINK language to the intermediate representation respects the semantics. This is mechanized in the file `src/FundamentalTheorem.hs` and is proven by relying on a number of auxiliary lemmas:
  - Witness generation is _complete_: it succeeds whenever possible, meaning whenever the corresponding unlabeled expression can be evaluated.
  - Witness generation is _sound_: whenever it succeeds, the returned witness satisfies the constraints defined by the input expression.
  - The solutions to the generated constraint systems are _essentially unique_: if there exists a valuation that satisfies a labeled expression, then the corresponding unlabeled expression can be evaluated to the same value that the valuation assigns to the output wire. In particular, since evaluation is deterministic, every solution agrees on the output values.
- Theorem 2, stating that the translation from the intermediate representation down to PLONK’s constraint systems preserves satisfiability. This is mechanized in the file `src/CompilerProof.hs`.

On top of this, the labeling process always produces correct expressions (i.e. distinct expressions are always assigned distinct wires, and pointers are never left dangling).
Additionally, the inlining and constant propagation optimizations are proven to preserve the semantics. The proofs are included in the respective files under `src/Optimizations/`.
