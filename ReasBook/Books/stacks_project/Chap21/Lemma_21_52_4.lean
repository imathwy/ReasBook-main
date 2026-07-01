import Mathlib
import stacks_project.Chap21.Lemma_21_52_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory
open Opposite

noncomputable section

universe u wI

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C]
variable (J : GrothendieckTopology C)
variable [HasFiniteWidePullbacks C]
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})]
variable (𝒪 : Sheaf J CommRingCat.{u})

local notation "Mod" => SheafOfModules (ringSheaf J 𝒪)
local notation "D" => DerivedCategory Mod

/-- The index type of the degree-`n` iterated Čech intersections of a chosen covering `cover`. -/
abbrev selectedCoverCechIntersectionIndex
    {U : C} [HasFiniteProducts (Over U)]
    (cover : FormalCoproduct (Over U)) (n : ℕ) :=
  (cover.cech.obj (op (SimplexCategory.mk n))).I

/-- The underlying object of the `i`-th degree-`n` iterated Čech intersection of `cover`. -/
abbrev selectedCoverCechIntersectionObject
    {U : C} [HasFiniteProducts (Over U)]
    (cover : FormalCoproduct (Over U)) (n : ℕ)
    (i : selectedCoverCechIntersectionIndex cover n) : C :=
  ((cover.cech.obj (op (SimplexCategory.mk n))).obj i).left

/-- The site-theoretic hypothesis that `B` admits a cofinal system `Cov` of finite coverings whose
members and all iterated Čech intersections remain in `B`. -/
structure CofinalFiniteCoverings
    (B : Set C) (Cov : ∀ U : C, Set (FormalCoproduct (Over U))) : Prop where
  cover_mem : ∀ ⦃U : C⦄ (cover : FormalCoproduct (Over U)),
    cover ∈ Cov U → (J.over U).CoversTop cover.obj
  finite : ∀ ⦃U : C⦄ (cover : FormalCoproduct (Over U)),
    cover ∈ Cov U → Finite cover.I
  target_mem : ∀ ⦃U : C⦄ (cover : FormalCoproduct (Over U)),
    cover ∈ Cov U → U ∈ B
  members_mem : ∀ ⦃U : C⦄ (cover : FormalCoproduct (Over U)),
    cover ∈ Cov U → ∀ i : cover.I, (cover.obj i).left ∈ B
  intersections_mem : ∀ ⦃U : C⦄ (cover : FormalCoproduct (Over U)),
    cover ∈ Cov U → ∀ n : ℕ, ∀ i : selectedCoverCechIntersectionIndex cover n,
      selectedCoverCechIntersectionObject cover n i ∈ B
  cofinal : ∀ ⦃U : C⦄, U ∈ B → ∀ ⦃ι : Type wI⦄ (family : ι → Over U),
    (J.over U).CoversTop family →
      ∃ cover : FormalCoproduct (Over U),
        cover ∈ Cov U ∧ Nonempty (cover ⟶ FormalCoproduct.mk ι family)

end

section

variable {C : Type u} [Category.{u} C]
variable (J : GrothendieckTopology C)
variable [HasFiniteWidePullbacks C]
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})]
variable (𝒪 : Sheaf J CommRingCat.{u})

local notation "Mod" => SheafOfModules (ringSheaf J 𝒪)
local notation "D" => DerivedCategory Mod

-- Proof sketch: first use Lemma `21.16.1` to show that for each `U ∈ B` the functors
-- `\mathcal F \mapsto H^p(U,\mathcal F)` commute with direct sums, by writing a direct sum as the
-- filtered colimit of its finite partial sums. Then apply Lemma `21.52.3`, which upgrades this
-- cohomological direct-sum compatibility to the bounded-below Hom-coproduct comparison for
-- `j_{U!}\mathcal O_U[0]`.
/-- Lemma 21.52.4: under the cofinal finite covering hypotheses on `B` and `Cov`, the degree-zero
derived object attached to `j_{U!} O_U` satisfies the bounded-below coproduct comparison over each
`U ∈ B`. -/
theorem localizedStructureModuleExtensionByZeroDegreeZero_hom_coproduct_iso_of_cofinal_finite_coverings
    (B : Set C)
    (Cov : ∀ U : C, Set (FormalCoproduct (Over U)))
    (hCov : CofinalFiniteCoverings J B Cov)
    {U : C} (hU : U ∈ B)
    {ι : Type u} (M : ι → D) [HasCoproduct M]
    (hM : ∃ a : ℤ, (∐ M).IsGE a) :
    PreservesColimit (Discrete.functor M)
      (preadditiveCoyoneda.obj
        (op (localizedStructureModuleExtensionByZeroDegreeZero J 𝒪 U))) := by
  exact
    localizedStructureModuleExtensionByZeroDegreeZero_hom_coproduct_iso_of_boundedBelow J 𝒪 U M
      (by
        intro p ι
        sorry)
      hM

end

end SheafOfModules.RingedSite
