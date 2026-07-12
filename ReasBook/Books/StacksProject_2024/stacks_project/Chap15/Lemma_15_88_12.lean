import Mathlib
import StacksProject_2024.Chap04.Example_4_22_6
import StacksProject_2024.Chap15.Lemma_15_88_3
import StacksProject_2024.Chap15.Lemma_15_88_11

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open Opposite
open SequentialProObjectMorphismRep

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A]

local notation "SeqMod" => SequentialInverseSystem (ModuleCat A)
local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "DSeq" => DerivedCategory SeqMod

/- Domain-style sampling for Lemma 15.88.12:
- primary domain: fixed-base derived inverse limits of sequential inverse systems of `A`-modules,
  together with the exact tensor-induced functors on `D(\mathbf N^\mathrm{op} \to \mathrm{Mod}_A)`;
- sampled owner declarations:
  `stagewiseModuleDerivedLimitTower`,
  `stagewiseModuleDerivedLimitTowerFunctor`,
  `derivedInverseLimitTensorOnInverseSystemFunctor`,
  `SequentialProObjectMorphismRep.toProObjectHom`;
- best owner abstraction: the source-facing theorem should use the Chapter 15 exact functor
  `derivedInverseLimitTensorOnInverseSystemFunctor K : D(\mathbf N^\mathrm{op} \to \mathrm{Mod}_A)
    ⥤ D(A)`, while the stagewise comparison should be expressed as the canonical stagewise tower
  in `D(A)` obtained from the upstream bridge owner `stagewiseModuleDerivedLimitTowerFunctor`;
- primitive data: a morphism `φ : E ⟶ D` in `D(\mathbf N^\mathrm{op} \to \mathrm{Mod}_A)` and
  its image under the canonical stagewise tower functor in `D(A)`;
- derived API: the induced map of the stagewise tower functor and the induced map of the exact owner functor
  `derivedInverseLimitTensorOnInverseSystemFunctor K`.

Source/core/bridge triage:
- `source-facing`: the isomorphism statement for
  `R \!\varprojlim (\Delta(K) \otimes_A^{\mathbf L} E) ⟶
    R \!\varprojlim (\Delta(K) \otimes_A^{\mathbf L} D)`;
- `core/canonical`: `derivedInverseLimitTensorOnInverseSystemFunctor`,
  `stagewiseModuleDerivedLimitTowerFunctor`, and
  `SequentialProObjectMorphismRep.toProObjectHom`;
- `bridge/view`: the canonical stagewise tower functor
  `stagewiseModuleDerivedLimitTowerFunctor`. -/

-- Proof sketch: the exact owner functor
-- `derivedInverseLimitTensorOnInverseSystemFunctor K` first tensors the inverse system by the
-- fixed factor `K` and then applies `R lim`. Tensoring stagewise preserves the assumed
-- pro-isomorphism of the towers, so Lemma `15.87.13` applied to the tensorized stagewise map
-- yields an isomorphism on the resulting derived inverse limits.
/-- Helper for Lemma 15.88.12: composing sequential representatives matches composition of the
induced pro-object morphisms. -/
private theorem compRep_toProObjectHom
    {X Y Z : ℕᵒᵖ ⥤ DMod}
    (r : SequentialProObjectMorphismRep X Y)
    (s : SequentialProObjectMorphismRep Y Z) :
    (compRep r s).toProObjectHom = r.toProObjectHom ≫ s.toProObjectHom := by
  -- Proof comment: both pro-morphisms evaluate on each test object by the same stagewise
  -- composites `r.map (s.reindex n) ≫ s.map n`.
  ext W x
  rfl

/-- Helper for Lemma 15.88.12: if the pro-object morphism induced by a natural transformation is
an isomorphism, then the natural transformation is a representative-level pro-isomorphism. -/
private theorem ofNatTrans_isProIsomorphism_of_isIso_toProObjectHom
    {X Y : ℕᵒᵖ ⥤ DMod} (α : X ⟶ Y)
    (hαIso : IsIso (ofNatTrans α).toProObjectHom) :
    (ofNatTrans α).IsProIsomorphism := by
  -- Proof comment: choose a representative of the inverse pro-morphism and compare both
  -- composites with the identity representatives via the Chapter 4 equivalence criterion.
  let η := (ofNatTrans α).toProObjectHom
  rcases exists_representative (inv η) with ⟨s, hs⟩
  refine ⟨s, ?_, ?_⟩
  · apply (represents_eq_iff_equivalent (compRep (ofNatTrans α) s) (idRep X)).1
    rw [compRep_toProObjectHom]
    rw [hs]
    exact IsIso.hom_inv_id η
  · apply (represents_eq_iff_equivalent (compRep s (ofNatTrans α)) (idRep Y)).1
    rw [compRep_toProObjectHom]
    rw [hs]
    exact IsIso.inv_hom_id η

/-- Helper for Lemma 15.88.12: applying a functor stagewise to a sequential representative gives
the corresponding representative between the whiskered towers. -/
private def mapRep
    {C D : Type*} [Category C] [Category D]
    {X Y : ℕᵒᵖ ⥤ C} (F : C ⥤ D) (r : SequentialProObjectMorphismRep X Y) :
    SequentialProObjectMorphismRep (X ⋙ F) (Y ⋙ F) where
  reindex := r.reindex
  hom := r.hom.whiskerRight F

/-- Helper for Lemma 15.88.12: common-refinement equivalence is preserved after applying a
functor stagewise. -/
private theorem equivalent_mapRep
    {C D : Type*} [Category C] [Category D]
    {X Y : ℕᵒᵖ ⥤ C}
    {r₁ r₂ : SequentialProObjectMorphismRep X Y}
    (F : C ⥤ D) (h : r₁.Equivalent r₂) :
    (mapRep F r₁).Equivalent (mapRep F r₂) := by
  -- Proof comment: keep the same common refinement and simply apply `F.map` to the level-map
  -- equality witnessing equivalence.
  rcases h with ⟨reindex', h₁, h₂, hmaps⟩
  refine ⟨reindex', h₁, h₂, ?_⟩
  intro n
  simpa [mapRep, Functor.map_comp] using congrArg (fun t ↦ F.map t) (hmaps n)

/-- Helper for Lemma 15.88.12: representative-level pro-isomorphisms are preserved by applying a
functor stagewise. -/
private theorem isProIsomorphism_mapRep
    {C D : Type*} [Category C] [Category D]
    {X Y : ℕᵒᵖ ⥤ C}
    (F : C ⥤ D) {r : SequentialProObjectMorphismRep X Y} (hr : r.IsProIsomorphism) :
    (mapRep F r).IsProIsomorphism := by
  -- Proof comment: map the chosen representative inverse through `F` and transport both
  -- equivalence witnesses with `equivalent_mapRep`.
  rcases hr with ⟨s, hrs, hsr⟩
  refine ⟨mapRep F s, ?_, ?_⟩
  · simpa [mapRep] using equivalent_mapRep F hrs
  · simpa [mapRep] using equivalent_mapRep F hsr

/-- Helper for Lemma 15.88.12: a representative-level pro-isomorphism induces an isomorphism on
the associated pro-object morphism. -/
private theorem isIso_toProObjectHom_of_isProIsomorphism
    {X Y : ℕᵒᵖ ⥤ DMod} {r : SequentialProObjectMorphismRep X Y} (hr : r.IsProIsomorphism) :
    IsIso r.toProObjectHom := by
  -- Proof comment: pointwise bijectivity on the Hom-colimit evaluations upgrades to a natural
  -- isomorphism by `NatIso.isIso_of_isIso_app`.
  let η := r.toProObjectHom
  have hηbij :
      ∀ Z : DMod, Function.Bijective (η.app Z) := fun Z ↦ by
        simpa [η] using
          SequentialProObjectMorphismRep.isProIsomorphism_toProObjectHom_app_bijective hr Z
  letI : ∀ Z : DMod, IsIso (η.app Z) := fun Z ↦
    (CategoryTheory.isIso_iff_bijective (η.app Z)).2 (hηbij Z)
  have hη : IsIso η := NatIso.isIso_of_isIso_app η
  simpa [η] using hη

/-- Helper for Lemma 15.88.12: tensoring each stage by a fixed `K` preserves the assumed
stagewise pro-isomorphism. -/
private theorem tensor_stagewise_proIsomorphism_of_stagewise_proIsomorphism
    {X Y : ℕᵒᵖ ⥤ DMod} (α : X ⟶ Y)
    (hαIso : IsIso (ofNatTrans α).toProObjectHom) (K : DMod) :
    IsIso (ofNatTrans (α.whiskerRight (derivedTensorProduct K))).toProObjectHom := by
  -- Proof comment: first turn the original isomorphism in the pro-category into a
  -- representative-level inverse, then apply `derivedTensorProduct K` stagewise and upgrade back
  -- to an isomorphism of pro-object morphisms.
  have hαPro : (ofNatTrans α).IsProIsomorphism :=
    ofNatTrans_isProIsomorphism_of_isIso_toProObjectHom α hαIso
  have hTensorPro :
      (mapRep (derivedTensorProduct K) (ofNatTrans α)).IsProIsomorphism :=
    isProIsomorphism_mapRep (derivedTensorProduct K) hαPro
  simpa [mapRep, SequentialProObjectMorphismRep.ofNatTrans] using
    isIso_toProObjectHom_of_isProIsomorphism hTensorPro

/-- Lemma 15.88.12: let `A` be a ring and let `φ : E ⟶ D` be a morphism in
`D(\mathbf N^\mathrm{op} \to \mathrm{Mod}_A)`. If the induced stagewise morphism
`(E_n^\bullet) \to (D_n^\bullet)` is an isomorphism of pro-objects in `D(A)`, then for every
`K ∈ D(A)` the corresponding map
`R \!\varprojlim (\Delta(K) \otimes_A^{\mathbf L} E) ⟶
  R \!\varprojlim (\Delta(K) \otimes_A^{\mathbf L} D)`
is an isomorphism. This is the fixed-base owner-level form of the textbook map
`R \!\varprojlim_n (K \otimes_A^{\mathbf L} E_n) ⟶
  R \!\varprojlim_n (K \otimes_A^{\mathbf L} D_n)`. -/
theorem isIso_map_derivedInverseLimitTensorOnInverseSystemFunctor_of_stagewise_proIsomorphism
    {E D : DSeq} (φ : E ⟶ D)
    (hφ : IsIso (ofNatTrans ((stagewiseModuleDerivedLimitTowerFunctor A).map φ)).toProObjectHom)
    (K : DMod) :
    IsIso ((derivedInverseLimitTensorOnInverseSystemFunctor K).map φ) := by
  -- Route correction: the dependency-closed progress in this file is the source-faithful first
  -- half of the textbook argument, namely tensoring the stagewise pro-isomorphism.
  have hTensor :
      IsIso
        (ofNatTrans
          (((stagewiseModuleDerivedLimitTowerFunctor A).map φ).whiskerRight
            (derivedTensorProduct K))).toProObjectHom :=
    tensor_stagewise_proIsomorphism_of_stagewise_proIsomorphism
      ((stagewiseModuleDerivedLimitTowerFunctor A).map φ) hφ K
  -- TODO: identify the stagewise tower attached to the hidden tensor-left-derived endofunctor
  -- inside `derivedInverseLimitTensorOnInverseSystemFunctor K` with the whiskered tower above,
  -- then apply the derived inverse-limit invariance lemma. The natural dependency-closed owner is
  -- the module-valued analogue of Lemma `15.87.13`, but that prerequisite is not currently
  -- available from compiling earlier files in this workspace.
  sorry

end
