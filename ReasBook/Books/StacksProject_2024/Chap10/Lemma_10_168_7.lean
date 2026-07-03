import Mathlib
import stacks_project.Chap10.Lemma_10_127_7
import stacks_project.Chap10.Lemma_10_138_15
import stacks_project.Chap10.Lemma_10_168_5

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

/-- Helper for Lemma 10.168.7: an étale colimit base change is already unramified at some stage.
-/
lemma stage_unramified_of_colimit_etale
    (φ₀ : B₀ →ₐ[A₀] C₀) (hφ₀ : φ₀.FinitePresentation)
    (hEt : (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(colimit F))).Etale) :
    ∃ j : J,
      letI :=
        (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j))).toRingHom.toAlgebra
      Algebra.Unramified (B₀ ⊗[A₀] ↑(F.obj j)) (C₀ ⊗[A₀] ↑(F.obj j)) := by
  -- Étaleness supplies the primitive formally-unramified input needed for Lemma `10.168.5`.
  have hfu :
      (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(colimit F))).FormallyUnramified :=
    hEt.formallyUnramified
  -- Finite presentation upgrades to finite type before applying the stagewise unramified descent.
  exact finite_type_unramified_baseChange_descends_to_stage
    (F := F) φ₀ (RingHom.FiniteType.of_finitePresentation hφ₀) hfu

/-- Helper for Lemma 10.168.7: on a fixed stage of the filtered system, the tensor-product
base-change map is étale as soon as its stage algebra is both unramified and smooth. -/
lemma tensor_base_change_etale_of_stage_unramified_and_smooth
    {j : J}
    (φ₀ : B₀ →ₐ[A₀] C₀)
    (hUnramified :
      letI :=
        (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j))).toRingHom.toAlgebra
      Algebra.Unramified (B₀ ⊗[A₀] ↑(F.obj j)) (C₀ ⊗[A₀] ↑(F.obj j)))
    (hSmooth : (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j))).Smooth) :
    (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j))).Etale := by
  let f := (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j))).toRingHom
  -- Reinterpret the stagewise algebra-level unramified owner as the ring-hom owner.
  have hFormallyUnramified : f.FormallyUnramified := by
    letI := f.toAlgebra
    change Algebra.FormallyUnramified
      (B₀ ⊗[A₀] ↑(F.obj j))
      (C₀ ⊗[A₀] ↑(F.obj j))
    exact hUnramified.formallyUnramified
  have hSmooth' : f.Smooth := by
    simpa using hSmooth
  -- The canonical owner characterization of étale closes the fixed-stage problem.
  exact (RingHom.etale_iff_formallyUnramified_and_smooth f).2 ⟨hFormallyUnramified, hSmooth'⟩

/-- Helper for Lemma 10.168.7: the map-level finite-presentation hypothesis on `φ₀` is exactly the
algebra-level finite-presentation instance needed to choose a fixed presentation of `C₀` over
`B₀`. -/
lemma algebra_finitePresentation_of_hom_finitePresentation
    (φ₀ : B₀ →ₐ[A₀] C₀) (hφ₀ : φ₀.FinitePresentation) :
    letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
    Algebra.FinitePresentation B₀ C₀ := by
  -- Unfold the owner predicates once so the map-level and algebra-level formulations coincide.
  simpa [AlgHom.FinitePresentation, RingHom.FinitePresentation] using hφ₀

/-- Helper for Lemma 10.168.7: after tensoring the filtered `A₀`-diagram with `B₀`, the étale
colimit tensor target `C₀ ⊗[A₀] colimit F` comes by base change from a smooth algebra over one
stage of that tensor-base-change diagram. This closes the smooth-model existence part of the
source proof while leaving the comparison with the canonical tensor target for the main stage
assembly lemma. -/
lemma colimit_tensor_has_stage_smooth_model
    (φ₀ : B₀ →ₐ[A₀] C₀)
    (hEt : (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(colimit F))).Etale) :
    let G := tensor_base_change_diagram (A := A₀) F B₀
    let c := tensor_base_change_cocone (A := A₀) F B₀
    ∃ (j : J) (Dⱼ : Type u) (_ : CommRing Dⱼ) (_ : Algebra (G.obj j) Dⱼ),
      letI : Algebra (G.obj j) c.pt := (c.ι.app j).hom.toAlgebra
      let ept := tensor_base_change_cocone_pt_iso_explicit (A := A₀) F B₀
      letI : Algebra c.pt (C₀ ⊗[A₀] ↑(colimit F)) :=
        ((Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(colimit F))).toRingHom.comp
          ept.hom.hom).toAlgebra
      Algebra.Smooth (G.obj j) Dⱼ ∧
        Nonempty ((C₀ ⊗[A₀] ↑(colimit F)) ≃ₐ[c.pt] c.pt ⊗[(G.obj j)] Dⱼ) := by
  let G := tensor_base_change_diagram (A := A₀) F B₀
  let c := tensor_base_change_cocone (A := A₀) F B₀
  let ept := tensor_base_change_cocone_pt_iso_explicit (A := A₀) F B₀
  letI : Algebra c.pt (C₀ ⊗[A₀] ↑(colimit F)) :=
    ((Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(colimit F))).toRingHom.comp
      ept.hom.hom).toAlgebra
  have hept_smooth : ept.hom.hom.Smooth := by
    -- The colimit-point comparison is an isomorphism of rings, hence smooth.
    rw [RingHom.smooth_def]
    exact ⟨RingHom.FormallySmooth.of_bijective (ConcreteCategory.bijective_of_isIso ept.hom),
      RingHom.FinitePresentation.of_bijective (ConcreteCategory.bijective_of_isIso ept.hom)⟩
  have hEt_ring :
      ((Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(colimit F))).toRingHom).Etale := by
    -- Switch to the ring-hom owner API so smoothness can be extracted from étaleness.
    simpa using hEt
  have hEt_smooth :
      ((Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(colimit F))).toRingHom).Smooth :=
    (RingHom.etale_iff_formallyUnramified_and_smooth
      ((Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(colimit F))).toRingHom)).1 hEt_ring |>.2
  have hsmooth_comp :
      (((Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(colimit F))).toRingHom).comp
        ept.hom.hom).Smooth :=
    RingHom.Smooth.comp hept_smooth hEt_smooth
  have hsmooth :
      Algebra.Smooth c.pt (C₀ ⊗[A₀] ↑(colimit F)) := by
    -- Re-express the composed smooth ring map as the ambient algebra structure on the tensor
    -- target over the base-changed colimit point.
    change
      (((Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(colimit F))).toRingHom).comp
        ept.hom.hom).Smooth
    exact hsmooth_comp
  -- Apply the owner-level smooth filtered-colimit descent theorem to the tensor-base-change
  -- diagram of the source ring `B₀`.
  simpa [G, c, ept] using
    (smooth_is_baseChange_of_stage_of_isColimit
      (F := G) (c := c)
      (tensor_base_change_cocone_isColimit (A := A₀) (J := J) F B₀)
      (B := C₀ ⊗[A₀] ↑(colimit F)))

/-- Helper for Lemma 10.168.7: after unramifiedness has descended to one stage, the remaining
source-faithful task is to descend the finite inverse-differential/Jacobian witness attached to
the fixed colimit presentation to some later stage. Once that witness is realized on the canonical
stage tensor presentation, smoothness and then étaleness follow on the actual target map. -/
lemma stage_etale_of_stage_unramified_and_fixed_presentation
    (φ₀ : B₀ →ₐ[A₀] C₀) (hφ₀ : φ₀.FinitePresentation)
    (hEt : (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(colimit F))).Etale)
    {j_unr : J}
    (hUnramified :
      letI :=
        (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j_unr))).toRingHom.toAlgebra
      Algebra.Unramified (B₀ ⊗[A₀] ↑(F.obj j_unr)) (C₀ ⊗[A₀] ↑(F.obj j_unr))) :
    ∃ j : J, (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j))).Etale := by
  letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
  letI : Algebra.FinitePresentation B₀ C₀ :=
    algebra_finitePresentation_of_hom_finitePresentation (A₀ := A₀) φ₀ hφ₀
  let P0 := Algebra.Presentation.ofFinitePresentation B₀ C₀
  let Pinf := P0.baseChange (B₀ ⊗[A₀] ↑(colimit F))
  -- Route correction: the source proof does not descend an auxiliary comparison equivalence.
  -- It fixes one finite presentation of `C₀` over `B₀`, base-changes that presentation to the
  -- colimit, extracts the inverse-differential/Jacobian witness there from `hEt`, and then
  -- descends that finite witness package to a later stage of the same canonical tensor
  -- presentation.
  let _ := P0
  let _ := Pinf
  let _ := hEt
  let _ := hUnramified
  obtain ⟨j_sm, Dⱼ, _, _, hSmoothModel, hCompare⟩ :=
    colimit_tensor_has_stage_smooth_model (F := F) φ₀ hEt
  let _ := j_sm
  let _ := Dⱼ
  let _ := hSmoothModel
  let _ := hCompare
  --
  -- TODO: compare the smooth stage model `Dⱼ` with the canonical stage tensor target
  -- `C₀ ⊗[A₀] F.obj j` using the fixed finite presentation `P0`, enlarge to a common upper stage
  -- where that comparison stabilizes, transport the already-descended `hUnramified` to the same
  -- upper stage, and then finish with
  -- `tensor_base_change_etale_of_stage_unramified_and_smooth`.
  sorry

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
    ∃ j : J, (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j))).Etale := by
  -- The unramified part of the target theorem already descends from the colimit stage.
  obtain ⟨j, hUnramified⟩ := stage_unramified_of_colimit_etale
    (F := F) φ₀ hφ₀ hEt
  -- Route correction: switch from the old `Pinf.HasCoeffs` model route to the textbook route
  -- with one fixed finite presentation of `C₀` over `B₀`. The remaining blocker is now exactly
  -- the descent of the colimit-stage inverse-differential/Jacobian witness on that fixed
  -- presentation.
  exact stage_etale_of_stage_unramified_and_fixed_presentation
    (F := F) φ₀ hφ₀ hEt hUnramified

end
