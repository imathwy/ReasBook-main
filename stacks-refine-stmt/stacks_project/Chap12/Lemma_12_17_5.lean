import Mathlib
import stacks_project.Chap12.Example_12_17_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.GradedObject
open CategoryTheory.GradedObject.Monoidal
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace CategoryTheory

variable {F : Type u} [Field F]

/-
Source/core/bridge triage for Lemma 12.17.5:
- source-facing statement: a left-dualizable graded `F`-vector space has finite total dimension,
  and the evaluation map induces nondegenerate degreewise pairings
- core/canonical owner: `ExactPairing W V` for a chosen left dual `W` of `V`, together with the
  signed graded braiding `GradedObject.Monoidal.koszulBraiding` from Example 12.17.4 and the
  canonical support owner `GradedObject.finrankSupport`
- bridge/view: the degreewise bilinear pairing obtained by restricting the owner evaluation map to
  the summand of total degree `0` and transporting it to the `W^{-n} ⊗ V^n` order used by the
  textbook pairing through the Koszul-signed braiding
-/

/-- A graded `F`-vector space has finite total dimension if only finitely many graded pieces are
nonzero and each graded piece is finite dimensional. We record this using the canonical graded
support `GradedObject.finrankSupport`. -/
abbrev hasFiniteTotalDimension (V : GradedObject ℤ (ModuleCat F)) : Prop :=
  Set.Finite (GradedObject.finrankSupport V) ∧ ∀ n : ℤ, FiniteDimensional F (V n)

/-- For a finite-dimensional graded piece of a graded `F`-vector space, belonging to the
canonical finite-rank support is equivalent to being nonzero. -/
private theorem mem_finrankSupport_iff_not_isZero
    (V : GradedObject ℤ (ModuleCat F)) (n : ℤ) [FiniteDimensional F (V n)] :
    n ∈ GradedObject.finrankSupport V ↔ ¬ IsZero (V n) := by
  have hzero : Module.finrank F (V n) = 0 ↔ IsZero (V n) := by
    rw [Module.finrank_eq_zero_iff_of_free F (V n), ModuleCat.isZero_iff_subsingleton]
  rw [GradedObject.finrankSupport, Function.mem_support]
  exact not_congr hzero

private theorem finrankSupport_eq_nonzero_degrees
    (V : GradedObject ℤ (ModuleCat F)) (hfd : ∀ n : ℤ, FiniteDimensional F (V n)) :
    GradedObject.finrankSupport V = {n : ℤ | ¬ IsZero (V n)} := by
  ext n
  letI := hfd n
  simpa using mem_finrankSupport_iff_not_isZero V n

/-- Textbook reformulation of `hasFiniteTotalDimension`: only finitely many graded pieces are
nonzero, and every graded piece is finite dimensional. -/
theorem hasFiniteTotalDimension_iff
    (V : GradedObject ℤ (ModuleCat F)) :
    hasFiniteTotalDimension V ↔
      Set.Finite {n : ℤ | ¬ IsZero (V n)} ∧ ∀ n : ℤ, FiniteDimensional F (V n) := by
  constructor
  · rintro ⟨hfin, hfd⟩
    rw [finrankSupport_eq_nonzero_degrees V hfd] at hfin
    exact ⟨hfin, hfd⟩
  · rintro ⟨hfin, hfd⟩
    exact ⟨(finrankSupport_eq_nonzero_degrees V hfd).symm ▸ hfin, hfd⟩

variable {V W : GradedObject ℤ (ModuleCat F)} [ExactPairing W V]

/-- The degree-`0` component of the exact-pairing evaluation, restricted to the `(-n,n)` tensor
summand and written in textbook order via the Koszul-signed braiding from Example 12.17.4. -/
private abbrev degreewiseEvaluationHom
    (V W : GradedObject ℤ (ModuleCat F)) [ExactPairing W V] (n : ℤ) :
    W (-n) ⊗ V n ⟶ 𝟙_ (ModuleCat F) :=
  ιTensorObj W V (-n) n 0 (neg_add_cancel n) ≫ (koszulBraiding W V).hom 0 ≫
    ε_ W V 0 ≫ tensorUnit₀.hom

/-- The degreewise bilinear pairing induced from the evaluation of a chosen left dual `W` of `V`,
written in the textbook order `W^{-n} × V^n → F`. -/
noncomputable abbrev degreewiseEvaluation
    (V W : GradedObject ℤ (ModuleCat F)) [ExactPairing W V] (n : ℤ) :
    W (-n) →ₗ[F] V n →ₗ[F] F :=
  TensorProduct.curry (degreewiseEvaluationHom V W n).hom

/-- Lemma 12.17.5: if `V` in the monoidal category of graded `F`-vector spaces has left dual
`W`, then `V` has finite total dimension and the evaluation morphism induces nondegenerate
pairings `W^{-n} × V^n → F` in every degree. -/
-- Proof sketch: write the coevaluation of the exact pairing as a finite sum of homogeneous pure
-- tensors. The triangle identities force the finitely many homogeneous vectors appearing there to
-- generate both graded objects, which gives finite dimensionality of each graded piece and leaves
-- only finitely many nonzero degrees. The same identities identify the degreewise evaluation maps
-- with dual-basis pairings, hence each resulting bilinear map is nondegenerate.
theorem leftDual_hasFiniteTotalDimension_and_nondegenerate_degreewiseEvaluation
    :
    hasFiniteTotalDimension V ∧
      ∀ n : ℤ, (degreewiseEvaluation V W n).Nondegenerate := sorry

end CategoryTheory
