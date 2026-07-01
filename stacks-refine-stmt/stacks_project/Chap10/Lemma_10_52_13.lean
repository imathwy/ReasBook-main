import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open IsLocalRing

universe u v w

section Length

/-
Domain triage:
* primary domain: finite-length modules under flat local base change and the closed fiber of a
  local homomorphism;
* sampled owner API: `Ideal.Fiber`, `Module.FaithfullyFlat.of_flat_of_isLocalHom`,
  `Module.length_ne_top_iff`, and `IsFiniteLength`;
* source-facing layer: the two textbook statements about the length of `B ⊗[A] M` and the finite
  length criterion after flat local base change;
* core/canonical owners: `Ideal.Fiber` for the closed fiber, `Module.FaithfullyFlat` for
  faithfulness of tensor base change, and `IsFiniteLength` for finiteness of length;
* bridge/view: the file keeps the source-facing length statements while deriving the ambient
  faithful-flat and finite-length notions from the owner abstractions already introduced earlier in
  the chapter.
-/

variable {A : Type u} {B : Type v} {M : Type w}
variable [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
variable [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]
variable [AddCommGroup M] [Module A M]

local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal A) B

-- Proof sketch: a flat local map of local rings is faithfully flat, so tensoring a composition
-- series of `M` with `B` preserves strict inclusions. Each simple quotient `A / maximalIdeal A`
-- becomes the closed fiber `((maximalIdeal A).Fiber B)`, equivalently
-- `B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)`, and additivity of `Module.length` gives the
-- multiplicative formula.
/-- Lemma 10.52.13 (1): for a flat local homomorphism `A → B`, the length of the base change
`B ⊗[A] M` is the length of `M` times the length of the closed fiber
`((maximalIdeal A).Fiber B)`, equivalently
`B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)`. -/
theorem length_base_change_eq_length_mul_closed_fiber :
    Module.length B (B ⊗[A] M) =
      Module.length A M * Module.length ClosedFiber ClosedFiber := sorry

-- Proof sketch: use the length formula in (1) together with `Module.length_ne_top_iff`.
-- If the closed fiber has finite length, then multiplication by its length preserves finiteness of
-- the other factor, yielding the equivalence of finite-length conditions.
/-- Lemma 10.52.13 (2): if the closed fiber `((maximalIdeal A).Fiber B)`, equivalently
`B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)`, has finite length as a module over itself,
then `M` has finite length over `A` if and only if `B ⊗[A] M` has finite
length over `B`. -/
theorem finite_length_iff_finite_length_base_change
    (hclosedFiber : IsFiniteLength ClosedFiber ClosedFiber) :
    IsFiniteLength A M ↔ IsFiniteLength B (B ⊗[A] M) := sorry

end Length
