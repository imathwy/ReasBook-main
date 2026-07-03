import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_54 (from Chap10) -/
open scoped BigOperators

noncomputable section

section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Definition 10.54 is `bridge/view` in Chapter 10's smoothing discussion. Domain sampling in the
Moreau-envelope/Huber API gives:
- `M[μ, f]` from Definition 6.7 as the canonical Moreau-envelope owner;
- `H[μ]` from Definition 6.8 as the scalar Huber owner;
- `moreau_envelope_l1_sum_toReal_eq_sum_huber` from Example 6.59 as the owner-level real-valued
  `ℓ¹` bridge.

The Chapter 10 item adds no new primitive data beyond the Euclidean specialization
`E = EuclideanSpace ℝ (Fin n)`, so the main entry here should be direct reuse of that Chapter 6
bridge rather than a parallel local reproving theorem. -/

/- Definition 10.54: for `h(x) = ‖x‖₁` on `ℝ^n` and any `μ > 0`, the real-valued Moreau envelope
of `h` is the sum of the scalar Huber values on the coordinates:
`M_h^μ(x) = ∑ i, H_μ(x_i)`. -/
#check
  (moreau_envelope_l1_sum_toReal_eq_sum_huber :
    ∀ μ : PosReal,
      ∀ x : E, (M[μ, fun y : E ↦ (‖y‖₁ : EReal)] x).toReal = ∑ i, H[μ] (x i))

end

/-! ### Example_10_54 (from Chap10) -/
/- Example 10.54 is `bridge/view` in the Chapter 10 smoothing API. Domain sampling in this owner
family identifies

- `M[μ, f]` as the core Moreau-envelope owner;
- `‖·‖₁` as the source-facing Euclidean `ℓ¹` penalty owner;
- `H[μ]` as the source-facing scalar Huber owner; and
- `moreau_envelope_l1_sum_toReal_eq_sum_huber` from Example 6.59 as the owner-level bridge from
  the real-valued `ℓ¹` envelope to the coordinatewise Huber sum.

The primitive data already live upstream, and the displayed sum formula is derived API from that
bridge. This file therefore reuses that canonical owner-level bridge directly instead of
introducing a parallel Chapter 10 theorem with the same interface. -/
recall moreau_envelope_l1_sum_toReal_eq_sum_huber
