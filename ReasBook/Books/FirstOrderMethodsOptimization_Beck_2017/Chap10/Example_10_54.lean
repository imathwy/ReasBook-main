import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_54

-- Declarations for this item will be appended below by the statement pipeline.

/- Example 10.54 is `bridge/view` in the Chapter 10 smoothing API. Domain sampling in this owner
family identifies

- `M[μ, f]` as the core Moreau-envelope owner;
- `l1n[·]` as the source-facing Euclidean `ℓ¹` penalty owner;
- `H[μ]` as the source-facing scalar Huber owner; and
- `moreau_envelope_l1_sum_toReal_eq_sum_huber` from Example 6.59 as the owner-level bridge from
  the real-valued `ℓ¹` envelope to the coordinatewise Huber sum.

The primitive data already live upstream, and the displayed sum formula is derived API from that
bridge. This file therefore reuses that canonical owner-level bridge directly instead of
introducing a parallel Chapter 10 theorem with the same interface. -/
recall moreau_envelope_l1_sum_toReal_eq_sum_huber
