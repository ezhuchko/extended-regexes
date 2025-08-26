# Lean Formalization of Extended Regular Expression Matching with Lookarounds

This repo contains the Lean formalization files for a matching algorithm based on regular expression derivatives. 

## Quick start

Typecheck the top-level file `Regex/Regex.lean`, which collects all modules of the formalization.

## Brief file overview

Listed below is a brief description of each file of the formalization.

- `EBA` : definition of Effective Boolean Algebra.
- `Span` : definitions of Spans, Locations and useful operations on these.
- `Definitions`: main definitions common to all files i.e. regex, reverse operation.
- `Correctness`: equivalence theorem between `models` and `derives`.
- `Examples`: running examples shown in the paper, showcasing the algorithm in action.
- `Models`: classical matching semantics, defined on locations and spans.
- `ModelsReasoning`: setoid-reasoning for match semantics, used to obtain some lemmas on repetition.
- `Derives`: main mutually-inductive definition of the derivation relation: derivatives, nullability.
- `Metrics`: metrics on regular expression to show termination of theorems/definitions.
- `MatchingAlgorithm`: main matching algorithm `llmatch`, with proofs of correctness.
- `Reversal`: correctness theorem for the reversal function.
