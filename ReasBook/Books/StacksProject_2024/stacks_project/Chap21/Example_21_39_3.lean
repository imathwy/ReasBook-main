import StacksProject_2024.Chap21.Example_21_39_2_Computing_homology

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u₁ v₁

namespace CategoryTheory

open scoped CategoryTheory.CategoryHomology

/-
Domain-style sampling for Example 21.39.3:
- primary domain: functoriality of category homology for precomposition of abelian presheaves;
- sampled owner declarations:
  `ComposableArrows`,
  `categoryHomologySimplicialObject`,
  `categoryHomologyComplex`,
  `NatTrans.leftDerived`,
  `ProjectiveResolution.isoLeftDerivedObj`,
  `AlgebraicTopology.alternatingFaceMapComplex`,
  `colimit.pre`;
- best owner abstraction: the source-facing owner from Example 21.39.2 is the explicit bar
  complex `K_•(ℱ)`, so this file should expose the map of those complexes induced by `u` and `t`;
  the induced map on `H_[n](C, ℱ)` should then be built from the canonical left-derived colimit
  functoriality for precomposition, rather than from a choice-built witness extracted from a
  proposition-level comparison theorem;
- primitive data: categories `C`, `C'`, a functor `u : C' ⥤ C`, a map
  `t : ℱ' ⟶ u.op ⋙ ℱ`, and a degree `n`;
- derived API: the explicit bar-complex map `categoryHomologyComplexMap` and the induced homology
  map `categoryHomologyMap`.

Source/core/bridge triage:
- `source-facing`: `categoryHomologyComplexMap` and `categoryHomologyMap`;
- `core/canonical`: `ComposableArrows`, `categoryHomologySimplicialObject`, `K_•`, and
  `HomologicalComplex.homologyFunctor`;
- `bridge/view`: the private simplicial map induced by `u` and `t`, together with the canonical
  colimit comparison for precomposition and the explicit `isoLeftDerivedObj` bridge for the
  precomposed presheaf. -/

section

variable {C : Type u₁} [Category.{v₁} C]
variable {C' : Type u₁} [Category.{v₁} C']

private abbrev categoryHomologyPresheafInverseImage (u : C' ⥤ C) :
    (Cᵒᵖ ⥤ AddCommGrpCat.{max u₁ v₁}) ⥤ (C'ᵒᵖ ⥤ AddCommGrpCat.{max u₁ v₁}) :=
  (Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ AddCommGrpCat.{max u₁ v₁}).obj u.op

private abbrev categoryHomologyMappedChain (u : C' ⥤ C)
    {Δ : SimplexCategoryᵒᵖ} (x : ComposableArrows C' Δ.unop.len) :
    ComposableArrows C Δ.unop.len :=
  (u.mapComposableArrows Δ.unop.len).obj x

@[simp] private lemma categoryHomologyMappedChain_chainMap (u : C' ⥤ C)
    {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ') (x : ComposableArrows C' Δ.unop.len) :
    categoryHomologyMappedChain u ((nerve C').map f x) =
      (nerve C).map f (categoryHomologyMappedChain u x) :=
  rfl

@[simp] private lemma categoryHomologyMappedTerminalMap (u : C' ⥤ C)
    {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ') (x : ComposableArrows C' Δ.unop.len) :
    categoryHomologyTerminalMap C f (categoryHomologyMappedChain u x) =
      u.map (categoryHomologyTerminalMap C' f x) :=
  rfl

private abbrev categoryHomologySimplicialMapApp (u : C' ⥤ C)
    {ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{max u₁ v₁}} {ℱ' : C'ᵒᵖ ⥤ AddCommGrpCat.{max u₁ v₁}}
    (t : ℱ' ⟶ u.op ⋙ ℱ) (Δ : SimplexCategoryᵒᵖ) :
    (categoryHomologySimplicialObject ℱ').obj Δ ⟶ (categoryHomologySimplicialObject ℱ).obj Δ :=
  Sigma.map' (fun x : ComposableArrows C' Δ.unop.len ↦ categoryHomologyMappedChain u x)
    (fun x ↦ t.app (Opposite.op x.right))

private theorem categoryHomologySimplicialMap_naturality (u : C' ⥤ C)
    {ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{max u₁ v₁}} {ℱ' : C'ᵒᵖ ⥤ AddCommGrpCat.{max u₁ v₁}}
    (t : ℱ' ⟶ u.op ⋙ ℱ)
    {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ') :
    (categoryHomologySimplicialObject ℱ').map f ≫ categoryHomologySimplicialMapApp u t Δ' =
      categoryHomologySimplicialMapApp u t Δ ≫ (categoryHomologySimplicialObject ℱ).map f := by
  sorry

/-- The simplicial map on bar constructions induced by `u : C' ⥤ C` and
`t : ℱ' ⟶ u.op ⋙ ℱ`. -/
private noncomputable def categoryHomologySimplicialMap (u : C' ⥤ C)
    {ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{max u₁ v₁}} {ℱ' : C'ᵒᵖ ⥤ AddCommGrpCat.{max u₁ v₁}}
    (t : ℱ' ⟶ u.op ⋙ ℱ) :
    categoryHomologySimplicialObject ℱ' ⟶ categoryHomologySimplicialObject ℱ where
  app := categoryHomologySimplicialMapApp u t
  naturality := fun {_ _} f ↦ categoryHomologySimplicialMap_naturality u t f

section

open scoped CategoryHomology

/-- Example 21.39.3: the explicit bar-complex map
`K_•(ℱ') ⟶ K_•(ℱ)` induced by `u` and `t`. -/
@[stacks 08PH]
abbrev categoryHomologyComplexMap (u : C' ⥤ C)
    {ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{max u₁ v₁}} {ℱ' : C'ᵒᵖ ⥤ AddCommGrpCat.{max u₁ v₁}}
    (t : ℱ' ⟶ u.op ⋙ ℱ) :
    K_•(ℱ') ⟶ K_•(ℱ) :=
  (AlgebraicTopology.alternatingFaceMapComplex AddCommGrpCat.{max u₁ v₁}).map
    (categoryHomologySimplicialMap u t)

end

section

variable [HasColimitsOfShape Cᵒᵖ AddCommGrpCat.{max u₁ v₁}]
variable [HasColimitsOfShape C'ᵒᵖ AddCommGrpCat.{max u₁ v₁}]
variable [HasProjectiveResolutions (Cᵒᵖ ⥤ AddCommGrpCat.{max u₁ v₁})]
variable [HasProjectiveResolutions (C'ᵒᵖ ⥤ AddCommGrpCat.{max u₁ v₁})]

/-- The underived colimit comparison induced by precomposition with `u.op`. -/
private abbrev categoryHomologyColimitComparison (u : C' ⥤ C) :
    (categoryHomologyPresheafInverseImage u) ⋙
        (colim : (C'ᵒᵖ ⥤ AddCommGrpCat.{max u₁ v₁}) ⥤ AddCommGrpCat.{max u₁ v₁}) ⟶
      (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{max u₁ v₁}) ⥤ AddCommGrpCat.{max u₁ v₁}) where
  app ℱ := colimit.pre ℱ u.op
  naturality {ℱ 𝒢} τ := by
    simpa using (colimit.pre_map τ u.op).symm

section

variable (u : C' ⥤ C)
variable
  [((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ AddCommGrpCat.{max u₁ v₁}).obj u.op).PreservesProjectiveObjects]

/-- The explicit left-derived comparison between `H_[n](C', u.op ⋙ ℱ)` and the `n`-th left
derived object of the composite of precomposition with `u.op` and `colim`. -/
private noncomputable abbrev categoryHomologyPrecompLeftDerivedIso
    (ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{max u₁ v₁}) (n : ℕ) :
    H_[n](C', (categoryHomologyPresheafInverseImage u).obj ℱ) ≅
      (((categoryHomologyPresheafInverseImage u) ⋙
          (colim : (C'ᵒᵖ ⥤ AddCommGrpCat.{max u₁ v₁}) ⥤ AddCommGrpCat.{max u₁ v₁})).leftDerived
        n).obj ℱ :=
  (((categoryHomologyPresheafInverseImage u).mapProjectiveResolution
        (projectiveResolution ℱ)).isoLeftDerivedObj
      (colim : (C'ᵒᵖ ⥤ AddCommGrpCat.{max u₁ v₁}) ⥤ AddCommGrpCat.{max u₁ v₁}) n) ≪≫
    ((projectiveResolution ℱ).isoLeftDerivedObj
      ((categoryHomologyPresheafInverseImage u) ⋙
        (colim : (C'ᵒᵖ ⥤ AddCommGrpCat.{max u₁ v₁}) ⥤ AddCommGrpCat.{max u₁ v₁})) n).symm

/-- Example 21.39.3: for a functor `u : C' ⥤ C` and a morphism `t : ℱ' ⟶ u.op ⋙ ℱ`, there is
an induced canonical map `H_[n](C', ℱ') ⟶ H_[n](C, ℱ)`. The explicit bar-complex map
`K_•(ℱ') ⟶ K_•(ℱ)` remains available as `categoryHomologyComplexMap`; the
public map on `H_[n]` is the canonical left-derived colimit morphism induced by `u` and `t`.
-/
@[stacks 08PH]
abbrev categoryHomologyMap (u : C' ⥤ C)
    [((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ AddCommGrpCat.{max u₁ v₁}).obj u.op).PreservesProjectiveObjects]
    {ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{max u₁ v₁}} {ℱ' : C'ᵒᵖ ⥤ AddCommGrpCat.{max u₁ v₁}}
    (t : ℱ' ⟶ u.op ⋙ ℱ)
    (n : ℕ) :
    H_[n](C', ℱ') ⟶ H_[n](C, ℱ) :=
  ((colim : (C'ᵒᵖ ⥤ AddCommGrpCat.{max u₁ v₁}) ⥤ AddCommGrpCat.{max u₁ v₁}).leftDerived n).map
      t ≫
    (categoryHomologyPrecompLeftDerivedIso u ℱ n).hom ≫
    (NatTrans.leftDerived (categoryHomologyColimitComparison u) n).app ℱ

end

end

end

end CategoryTheory
