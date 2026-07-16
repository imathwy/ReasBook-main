import StacksProject_2024.stacks_project.Chap24.Lemma_24_23_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.MonoidalCategory Limits ComplexShape
open CategoryTheory.ObjectProperty

noncomputable section

set_option checkBinderAnnotations false

universe u v w

namespace SheafOfModules.RingedSite

-- Semantic search note: `lean_leansearch` only surfaced general filtered-colimit infrastructure,
-- so the owner/API choice was fixed against the local Chapter 21 K-flat and pullback files, the
-- neighboring Chapter 24 `IsGood` statement skeleton, and the Stacks source text.

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

local notation "Mod" => ringedSiteModuleCategory J 𝒪
local notation "Cpx" => CochainComplex Mod ℤ
local notation "Good" => (IsGood : ObjectProperty Cpx)

variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalPreadditive (ringedSiteModuleCategory J 𝒪)]
variable [(curriedTensor Mod).Additive]
variable [∀ M : Mod, ((curriedTensor Mod).obj M).Additive]

namespace CochainComplex

private theorem isFlat_of_iso
    {M N : Mod} (e : M ≅ N) (hM : IsFlat 𝒪 M) :
    IsFlat 𝒪 N := by
  sorry

private theorem isTermwiseFlat_of_iso
    {K L : Cpx} (e : K ≅ L) (hK : CochainComplex.IsTermwiseFlat K) :
    CochainComplex.IsTermwiseFlat L := by
  sorry

private theorem isKFlat_of_iso
    {K L : Cpx} (e : K ≅ L) (hK : K.IsKFlat) :
    L.IsKFlat := by
  sorry

/-- Internal `ObjectProperty` scaffolding for the source-facing Chapter 24 good-complex lemmas. -/
local instance isGood_isClosedUnderIsomorphisms :
    Good.IsClosedUnderIsomorphisms where
  of_iso e hK := by
    exact ⟨isTermwiseFlat_of_iso e.symm hK.termwiseFlat, isKFlat_of_iso e.symm hK.kFlat⟩

/-- Internal discrete-colimit closure instance used by `isGood_coproduct`. -/
local instance isGood_isClosedUnderCoproducts
    (I : Type w) :
    Good.IsClosedUnderColimitsOfShape (Discrete I) := by
  sorry

/-- Lemma 24.23.3 (1): an arbitrary direct sum of good differential graded `\mathcal A`-modules on
a ringed site is good. In the canonical API this direct sum is the coproduct `∐ F`. -/
@[stacks 0FSD]
theorem isGood_coproduct
    {I : Type w}
    (F : I → Cpx)
    [HasCoproduct F]
    (hF : ∀ i : I, IsGood (F i)) :
    IsGood (∐ F) := by
  simpa using Good.prop_colimit (Discrete.functor F) (fun i ↦ hF i.as)


/-- Internal filtered-colimit closure instance used by the source-facing colimit lemmas. -/
local instance isGood_isClosedUnderFilteredColimitsOfShape
    {K : Type w} [Category.{v} K] [IsFiltered K] :
    Good.IsClosedUnderColimitsOfShape K := by
  sorry

/-- Lemma 24.23.3 (2): a filtered colimit of good differential graded `\mathcal A`-modules on a
ringed site is good. -/
@[stacks 0FSD]
theorem isGood_colimit_of_isFiltered
    {K : Type w} [Category.{v} K] [IsFiltered K]
    (F : K ⥤ Cpx)
    [HasColimit F]
    (hF : ∀ k : K, IsGood (F.obj k)) :
    IsGood (colimit F) := by
  simpa using Good.prop_colimit F hF

/-- Companion API: the filtered-colimit closure theorem applied to a sequential diagram written
with the canonical owner `Functor.ofSequence`. -/
theorem isGood_colimit_of_sequence
    (X : ℕ → Cpx)
    (u : ∀ n : ℕ, X n ⟶ X (n + 1))
    [HasColimit (Functor.ofSequence u)]
    (hX : ∀ n : ℕ, IsGood (X n)) :
    IsGood (colimit (Functor.ofSequence u)) := by
  exact isGood_colimit_of_isFiltered (Functor.ofSequence u) hX


end CochainComplex

end

end SheafOfModules.RingedSite
