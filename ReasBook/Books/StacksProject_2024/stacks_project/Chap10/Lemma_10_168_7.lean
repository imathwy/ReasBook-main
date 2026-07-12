import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open scoped TensorProduct

universe u v

/-
Domain-style sampling:
- primary domain: étale base-change descent for finitely presented morphisms along filtered colimits
  of commutative algebras;
- sampled owner API:
  `RingHom.Etale`,
  `RingHom.etale_iff_formallyUnramified_and_smooth`,
  `finite_type_unramified_baseChange_descends_to_stage`,
  `smooth_is_baseChange_of_stage_of_isColimit`;
- source-facing: the Stacks lemma saying a finitely presented map whose colimit base change is
  étale is already étale after base change to some stage;
- core/canonical: the owner property `RingHom.Etale`, together with the upstream owner descent
  theorems for its unramified and smooth pieces;
- bridge/view: this file stays at the bridge layer, assembling the owner-level descent statements
  for the specific tensor-product base changes attached to a fixed `A₀`-algebra map `φ₀`.

Primitive data are the filtered diagram `F`, the finitely presented map `φ₀`, and the colimit-stage
étale hypothesis. Smoothness and formal unramifiedness of the base-changed map are derived owner
API, so this file should treat the theorem as a bridge over `RingHom.Etale` rather than introducing
any auxiliary wrapper for the stage data.
-/

section

variable {A₀ : Type u} [CommRing A₀]
variable {J : Type v} [SmallCategory J] [IsFiltered J]
variable (F : J ⥤ CommAlgCat.{u} A₀) [HasColimit F]
variable {B₀ C₀ : Type u} [CommRing B₀] [CommRing C₀] [Algebra A₀ B₀] [Algebra A₀ C₀]

-- Proof sketch: work at the bridge layer over the canonical owner `RingHom.Etale`. The colimit
-- base change is smooth and formally unramified, hence the smooth part descends by the filtered
-- colimit smooth owner theorem and the unramified part descends by
-- `finite_type_unramified_baseChange_descends_to_stage`, using that finite presentation implies
-- finite type. After enlarging to a common stage, reassemble the owner property
-- `RingHom.Etale` there.
/-- Lemma 10.168.7: if `φ₀ : B₀ →ₐ[A₀] C₀` is finitely presented and its base change to the
filtered colimit `colimit F` of `A₀`-algebras is étale, then the base change of `φ₀` to some
stage `F.obj j` is already étale. -/
theorem finitePresentation_etale_baseChange_descends_to_stage
    (φ₀ : B₀ →ₐ[A₀] C₀) (hφ₀ : φ₀.FinitePresentation)
    (hEt : (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(colimit F))).Etale) :
    ∃ j : J, (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j))).Etale := sorry

end
