import StacksProject_2024.Chap28.Definition_28_23_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Semantic recall note: Definition 28.23.1 already introduced the source-facing owner
`SheafOfModules.IsKappaGenerated`, so this lemma is the ringed-space representative-set statement
for that canonical predicate rather than a second local owner. -/

variable (X : RingedSpace.{u}) (κ : Cardinal.{u})

local notation "ModX" => RingedSpace.Modules X

/-- The canonical object property of `κ`-generated `\mathcal O_X`-modules. -/
private abbrev kappaGeneratedModuleProperty : ObjectProperty ModX :=
  fun ℱ ↦ ℱ.IsKappaGenerated κ

/-- `κ`-generated `\mathcal O_X`-modules are stable under isomorphisms. -/
instance kappaGeneratedModuleProperty_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms (kappaGeneratedModuleProperty X κ) := by
  sorry

/-- The object property of `κ`-generated `\mathcal O_X`-modules is essentially small. -/
instance kappaGeneratedModuleProperty_essentiallySmall :
    ObjectProperty.EssentiallySmall.{u + 1} (kappaGeneratedModuleProperty X κ) := by
  let _ : CategoryTheory.EssentiallySmall.{u + 1} ModX := by
    simpa using (CategoryTheory.essentiallySmallSelf.{0} ModX)
  have hle : kappaGeneratedModuleProperty X κ ≤ (⊤ : ObjectProperty ModX) := by
    intro ℱ hℱ
    simp
  exact ObjectProperty.EssentiallySmall.of_le hle

/-- The full subcategory of `κ`-generated `\mathcal O_X`-modules is essentially small. This is
the canonical categorical owner behind the representative-set statement of
Lemma 28.23.2. -/
theorem kappaGeneratedFullSubcategory_essentiallySmall
    : CategoryTheory.EssentiallySmall.{u + 1}
        (ObjectProperty.FullSubcategory (kappaGeneratedModuleProperty X κ)) := by
  infer_instance

/-- Canonical skeleton companion to Lemma 28.23.2: there is a set of `κ`-generated
`\mathcal O_X`-modules containing exactly one representative of each isomorphism class of
`κ`-generated modules. -/
theorem exists_set_of_kappaGenerated_module_unique_representatives :
    ∃ S : Set ModX,
      (∀ ℱ ∈ S, ℱ.IsKappaGenerated κ) ∧
      ∀ (ℱ : ModX), ℱ.IsKappaGenerated κ →
        ∃! 𝒢 : ModX, 𝒢 ∈ S ∧ Nonempty (𝒢 ≅ ℱ) := by
  obtain ⟨P, _, hP⟩ :=
    ObjectProperty.EssentiallySmall.exists_small.{u + 1} (kappaGeneratedModuleProperty X κ)
  let F : Skeleton P.FullSubcategory ⥤ ModX :=
    fromSkeleton P.FullSubcategory ⋙ P.ι
  let S : Set ModX := Set.range F.obj
  refine ⟨S, ?_, ?_⟩
  · intro ℱ hℱ
    rcases hℱ with ⟨q, rfl⟩
    let Y : P.FullSubcategory := (fromSkeleton P.FullSubcategory).obj q
    have hY : P Y.1 := Y.2
    have hY' : (kappaGeneratedModuleProperty X κ) Y.1 := by
      have hY'' : P.isoClosure Y.1 := ObjectProperty.le_isoClosure P _ hY
      rw [← hP] at hY''
      exact hY''
    simpa [F, Y] using hY'
  · intro ℱ hℱ
    have hℱ' : P.isoClosure ℱ := by
      rw [← hP]
      exact hℱ
    rw [ObjectProperty.prop_isoClosure_iff] at hℱ'
    rcases hℱ' with ⟨M, hM, ⟨e⟩⟩
    let Y : P.FullSubcategory := ⟨M, hM⟩
    refine ⟨F.obj (toSkeleton Y), ?_, ?_⟩
    · constructor
      · exact ⟨toSkeleton Y, rfl⟩
      · exact ⟨(P.ι.mapIso (fromSkeletonToSkeletonIso Y)) ≪≫ e.symm⟩
    · intro 𝒢 h𝒢
      rcases h𝒢 with ⟨⟨q, rfl⟩, ⟨e'⟩⟩
      have hq : q = toSkeleton Y := by
        rw [← toSkeleton_fromSkeleton_obj q]
        exact (toSkeleton_eq_toSkeleton_iff).2 ⟨P.isoMk (e' ≪≫ e)⟩
      simpa using congrArg F.obj hq

/-- Lemma 28.23.2: for a ringed space `(X, \mathcal O_X)` and a cardinal `κ`, there is a set of
`κ`-generated `\mathcal O_X`-modules containing a representative of every isomorphism class of
`κ`-generated modules. This is the source-facing representative-set companion to the essentially
smallness of the full subcategory of `κ`-generated modules recorded above. -/
@[stacks 077M]
theorem exists_set_of_kappaGenerated_module_representatives
    : ∃ S : Set ModX,
      (∀ ℱ ∈ S, ℱ.IsKappaGenerated κ) ∧
      ∀ ℱ : ModX, ℱ.IsKappaGenerated κ →
        ∃ 𝒢 ∈ S, Nonempty (𝒢 ≅ ℱ) := by
  obtain ⟨S, hS, hrep⟩ := exists_set_of_kappaGenerated_module_unique_representatives X κ
  refine ⟨S, hS, ?_⟩
  intro ℱ hℱ
  rcases hrep ℱ hℱ with ⟨𝒢, h𝒢, huniq⟩
  exact ⟨𝒢, h𝒢.1, h𝒢.2⟩

end AlgebraicGeometry.RingedSpace
