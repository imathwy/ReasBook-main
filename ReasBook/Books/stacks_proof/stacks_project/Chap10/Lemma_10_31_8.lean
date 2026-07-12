import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.
open scoped TensorProduct

universe u v w

section

variable {k : Type u} [Field k]
variable {K : Type v} [Field K] [Algebra k K] [Algebra.EssFiniteType k K]
variable {R : Type w} [CommRing R] [Algebra k R] [IsNoetherianRing R]

-- Domain triage:
-- * source-facing: the textbook ring `K ⊗[k] R`
-- * core/canonical: `Algebra.EssFiniteType`, already fixed in Definition `9.6.6` as the owner
--   abstraction for finitely generated field extensions
-- * bridge/view: `Algebra.TensorProduct.comm k R K`
--
-- Proof sketch: base change makes `R ⊗[k] K` an essentially finite type `R`-algebra, so the
-- canonical theorem `Algebra.EssFiniteType.isNoetherianRing` makes the owner object Noetherian.
-- The textbook tensor order is then recovered by `TensorProduct.comm`.
/-- Lemma 10.31.8: if `k` is a field, `R` is a Noetherian `k`-algebra, and `K / k` is a finitely
generated field extension, then the textbook base change `K ⊗[k] R` is Noetherian. -/
@[stacks 045I]
theorem isNoetherianRing_tensorProduct_of_finitelyGeneratedFieldExtension :
    IsNoetherianRing (K ⊗[k] R) := by
  let _ : Algebra.EssFiniteType R (R ⊗[k] K) := inferInstance
  let _ : IsNoetherianRing (R ⊗[k] K) := Algebra.EssFiniteType.isNoetherianRing R (R ⊗[k] K)
  simpa using isNoetherianRing_of_ringEquiv _ (Algebra.TensorProduct.comm k R K).toRingEquiv

end
