import Mathlib
import stacks_proof.stacks_project.Chap13.Lemma_13_10_6
import stacks_proof.stacks_project.Chap13.Lemma_13_23_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open ComplexShape
open scoped CategoryTheory

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

attribute [local instance] HasDerivedCategory.standard

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive]

/- Domain-style sampling for Remark 13.25.2:
- primary domain: bounded-below right derived functors computed via injective representatives and
  the induced exact functors on `D^+` and `K^+`;
- sampled owner declarations:
  `Functor.rightDerivedUnique`,
  `Localization.Lifting`,
  `HomotopyResolutionFunctor.lift_unique`,
  `Functor.CommShift.ofComp`,
  `Functor.isTriangulated_iff_comp_right`;
- best owner abstraction: the comparison between the canonical bounded-below right derived functor
  and any functor built from a lift `j'` is owned by `Functor.rightDerivedUnique`, while the
  exactness assertions belong to the owner predicates `Functor.CommShift` and
  `Functor.IsTriangulated`, not to ad hoc existential packages;
- primitive data: the additive functor `F`, the homotopy resolution functor `j`, a lift
  `j' : D^+(\mathcal A) ⥤ K^+(\mathcal I)`, together with the canonical lift datum carried by
  `Localization.Lifting`;
- derived API: the factorization isomorphism for `RF` and the inherited
  `CommShift`/`IsTriangulated` structures on the lifted functors.

Source/core/bridge triage:
- `source-facing`: the factorization of `RF` through `K^+(\mathcal B)` and the exactness of the
  lifted functors in Remark 13.25.2;
- `core/canonical`: `Functor.totalRightDerived`, `Functor.rightDerivedUnique`,
  `Functor.CommShift`, and `Functor.IsTriangulated`;
- `bridge/view`: the composites through `K⁺ᵢ(𝒜)` and `K⁺(ℬ)` built from a chosen lift `j'`.
-/

local notation "DplusA" =>
  @boundedBelowDerivedCategory 𝒜 _ _ (HasDerivedCategory.standard 𝒜)
local notation "DplusB" =>
  @boundedBelowDerivedCategory ℬ _ _ (HasDerivedCategory.standard ℬ)
local notation "Q" =>
  (@mapBoundedBelowHomotopyToDerivedBelow 𝒜 _ _ : K⁺(𝒜) ⥤ DplusA)
local notation "KinjIncl" => ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜)
/-- Helper for Chap13 Remark 13 25 2: the bounded-below homotopy functor induced by `F`,
followed by passage to the bounded-below derived category. -/
  private abbrev mapBoundedBelowHomotopyCategoryToDerivedBelow
    (G : ℬ ⥤ ℬ) [G.Additive] :
    K⁺(ℬ) ⥤ DplusB :=
  mapBoundedBelowHomotopyCategory G ⋙
    (@mapBoundedBelowHomotopyToDerivedBelow ℬ _ _ : K⁺(ℬ) ⥤ DplusB)

local notation "KinjToKplusB" =>
  KinjIncl ⋙ mapBoundedBelowHomotopyCategory F
local notation "KinjToDplusB" =>
  KinjIncl ⋙ mapBoundedBelowHomotopyCategory F ⋙
    (@mapBoundedBelowHomotopyToDerivedBelow ℬ _ _ : K⁺(ℬ) ⥤ DplusB)

/-- Helper for Chap13 Remark 13 25 2: the identity functor acts trivially on cochain maps. -/
private theorem mapHomologicalComplex_id_map
    {K L : HomologicalComplex ℬ (up ℤ)} (f : K ⟶ L) :
    ((𝟭 ℬ).mapHomologicalComplex (up ℤ)).map f = f := by
  -- Proof comment: the identity functor acts termwise, so each component map is unchanged.
  ext i
  simp

/-- Helper for Chap13 Remark 13 25 2: the identity functor acts trivially on homotopy classes. -/
private theorem mapHomotopyCategory_id_map
    {K L : HomotopyCategory ℬ (up ℤ)} (f : K ⟶ L) :
    ((𝟭 ℬ).mapHomotopyCategory (up ℤ)).map f = f := by
  -- Proof comment: descend to an actual cochain map representative and use the previous lemma.
  rw [← HomotopyCategory.quotient_map_out f]
  change
    (HomotopyCategory.quotient ℬ (up ℤ)).map (((𝟭 ℬ).mapHomologicalComplex (up ℤ)).map f.out) =
      (HomotopyCategory.quotient ℬ (up ℤ)).map f.out
  rw [mapHomologicalComplex_id_map (ℬ := ℬ) f.out]
  rfl

/-- Helper for Chap13 Remark 13 25 2: restricting the identity functor to `K⁺(ℬ)` is still the
identity functor. -/
private theorem mapBoundedBelowHomotopyCategory_id :
    mapBoundedBelowHomotopyCategory (𝟭 ℬ) = 𝟭 (K⁺(ℬ)) := by
  -- Route correction: direct simplification leaves the bounded-below lift of `𝟭 ℬ`, so we
  -- identify that lift with the identity functor before closing the main composite equality.
  exact Functor.ext_of_iso
    (NatIso.ofComponents (fun X ↦ Iso.refl X) (by
      intro X Y f
      -- Proof comment: the lift map is just the underlying homotopy map wrapped back into the
      -- full subcategory, and the previous lemma identifies that underlying map with `f.hom`.
      change ObjectProperty.homMk (((𝟭 ℬ).mapHomotopyCategory (up ℤ)).map f.hom) ≫ 𝟙 Y =
          𝟙 X ≫ f
      rw [mapHomotopyCategory_id_map (ℬ := ℬ) f.hom]
      simpa using (show ObjectProperty.homMk f.hom = f by rfl)))
    (fun _ ↦ rfl) (fun _ ↦ rfl)

-- Proof sketch: both sides are the same composite through the inclusion
-- `K^+(\mathcal I) ↪ K^+(\mathcal A)` followed by the canonical bounded-below homotopy and
-- derived functors induced by `F`.
/-- Chap13 Remark 13 25 2: localizing the lifted homotopy-valued functor on the target side
recovers the functor `D^+(\mathcal A) ⥤ D^+(\mathcal B)` obtained by applying `F` to
bounded-below injective complexes and then passing to the derived category. -/
theorem lift_comp_mapBoundedBelowInjectiveHomotopyToHomotopy_toDerived
    (j' : DplusA ⥤ K⁺ᵢ(𝒜)) :
    j' ⋙ KinjToKplusB ⋙
        mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 ℬ) =
      j' ⋙ KinjToDplusB := by
  -- Proof comment: unfold the target-side localization, replace the bounded-below lift of
  -- `𝟭 ℬ` by the identity, and the two composites become definitionally identical.
  rw [mapBoundedBelowHomotopyCategoryToDerivedBelow]
  rw [mapBoundedBelowHomotopyCategory_id (ℬ := ℬ)]
  rfl

end

end CategoryTheory
