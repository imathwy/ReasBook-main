import StacksProject_2024.Chap18.RingedSiteModuleCategory
import StacksProject_2024.Chap13.Definition_13_33_1
import StacksProject_2024.Chap13.Definition_13_34_1
import StacksProject_2024.Chap21.RingedSiteDerived
import StacksProject_2024.Chap21.Definition_21_47_1
import StacksProject_2024.Chap21.Lemma_21_35_9

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search tool `lean_leansearch` was unavailable in this run; the statement surface below
-- was aligned against the local Chapter 21 owners by repository inspection.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open Opposite
open _root_.RingedSite.Hom (ModuleCat ModuleDerived localizedRestriction)

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard
set_option checkBinderAnnotations false

namespace SheafOfModules.RingedSite

section

open _root_.RingedSite.DerivedCategory
open _root_.RingedSite.Hom.ModuleDerived

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [MonoidalCategory (RingedSiteDerived J 𝒪)]
variable [BraidedCategory (RingedSiteDerived J 𝒪)]
variable [MonoidalClosed (RingedSiteDerived J 𝒪)]

local notation "X" => RingedSite.ofCommRingSheaf J 𝒪
local notation "Mod" => ModuleCat X
local notation "DMod" => ModuleDerived X
local notation "Cpx" => CochainComplex Mod ℤ

/-- The canonical bidual comparison morphism `K ⟶ (K^∨)^∨` in `D(𝒪)`. -/
noncomputable abbrev ringedSiteDerivedBidualComparison
    (K : DMod) :
    K ⟶ (K^∨)^∨ :=
  MonoidalClosed.curry (ringedSiteDerivedDualEvaluation K)

/-
The bidual comparison is the adjoint transpose of the canonical evaluation map
`K^∨ ⊗ K ⟶ 𝟙`.
-/
theorem ringedSiteDerivedBidualComparison_def
    (K : DMod) :
    ringedSiteDerivedBidualComparison K =
      MonoidalClosed.curry (ringedSiteDerivedDualEvaluation K) := by
  rfl

/-
Uncurrying the canonical bidual comparison recovers the canonical evaluation morphism
`K^∨ ⊗ K ⟶ 𝟙`.
-/
@[simp] theorem ringedSiteDerivedBidualComparison_uncurry
    (K : DMod) :
    MonoidalClosed.uncurry (ringedSiteDerivedBidualComparison K) =
      ringedSiteDerivedDualEvaluation K := by
  simp [ringedSiteDerivedBidualComparison]

variable [HasBinaryProducts C]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [∀ U : C, (localizedRestriction (RingedSite.ofCommRingSheaf J 𝒪) U).Additive]
variable [∀ U : C, PreservesFiniteLimits
  (localizedRestriction (RingedSite.ofCommRingSheaf J 𝒪) U)]
variable [∀ U : C, PreservesFiniteColimits
  (localizedRestriction (RingedSite.ofCommRingSheaf J 𝒪) U)]
variable [CategoryWithHomology (ModuleCat (RingedSite.ofCommRingSheaf J 𝒪))]
variable [∀ U : C, CategoryWithHomology
  (ModuleCat ((RingedSite.ofCommRingSheaf J 𝒪).localization U))]
variable [Abelian (ModuleCat (RingedSite.ofCommRingSheaf J 𝒪))]

-- Proof sketch: represent `K` locally by a strictly perfect complex and use the termwise dual
-- complex from Lemma `21.44.9`; local perfectness of the dual then descends to the derived
-- object.
/-- Lemma 21.48.4 (1): if `K` is a perfect object of `D(𝒪)` on a ringed site, then its derived
dual `K^∨` is perfect. -/
@[stacks 08JJ]
theorem isPerfect_derivedDual_of_isPerfect
    {K : DMod} (hK : K.IsPerfect) :
    (K^∨).IsPerfect := sorry

-- Proof sketch: after passing to a local strictly perfect representative of `K`, the bidual map
-- is the degreewise double-dual evaluation map on finite projective terms, hence an isomorphism.
/-- Lemma 21.48.4 (2): for a perfect object `K` of `D(𝒪)`, the canonical bidual comparison
`K ⟶ (K^∨)^∨` is an isomorphism. -/
@[stacks 08JJ]
instance isIso_ringedSiteDerivedBidualComparison_of_isPerfect
    {K : DMod} (hK : K.IsPerfect) :
    IsIso (ringedSiteDerivedBidualComparison K) := by
  sorry

-- Proof sketch: choose a local strictly perfect model of `K`, identify `K^∨` with the
-- termwise dual complex, and compare the tensor product with the internal-Hom complex degreewise
-- on finite projective summands.
/-- Lemma 21.48.4 (3): if `K` is perfect, then for every `M : D(𝒪)` the canonical comparison
`M ⊗ K^∨ ⟶ (ihom K).obj M` is an isomorphism, formalized by
`ringedSiteDerivedEvaluationHom K M`. -/
@[stacks 08JJ]
instance isIso_ringedSiteDerivedEvaluationHom_of_isPerfect
    {K M : DMod} (hK : K.IsPerfect) :
    IsIso (ringedSiteDerivedEvaluationHom K M) := by
  sorry

-- Proof sketch: combine part `(3)` with the Chapter `21.35` identification of degree-zero global
-- cohomology of a derived internal Hom with morphisms in the derived category.
omit [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [∀ U : C, (localizedRestriction X U).Additive]
  [∀ U : C, PreservesFiniteLimits (localizedRestriction X U)]
  [∀ U : C, PreservesFiniteColimits (localizedRestriction X U)]
  [CategoryWithHomology Mod] [Abelian Mod] in
/-- Lemma 21.48.4 (4): if `K` is perfect, then the canonical map
`H⁰(𝒞, M ⊗ K^∨) ⟶ Hom_{D(𝒪)}(K, M)` induced by
`M ⊗ K^∨ ⟶ (ihom K).obj M` is bijective; here `H⁰` is formalized by morphisms
`𝟙_ DMod ⟶ M ⊗ K^∨` out of the monoidal unit, and the comparison is the canonical Chapter `21.35`
map
`ringedSiteDerivedEvaluationH0ToHom K M`. -/
@[stacks 08JJ]
theorem bijective_ringedSiteDerivedEvaluationH0ToHom_of_isPerfect
    {K M : DMod} (hK : K.IsPerfect) :
    Function.Bijective (ringedSiteDerivedEvaluationH0ToHom K M) := by
  letI : IsIso (ringedSiteDerivedEvaluationHom K M) :=
    isIso_ringedSiteDerivedEvaluationHom_of_isPerfect hK
  let postcompEquiv : (𝟙_ DMod ⟶ M ⊗ K^∨) ≃ (𝟙_ DMod ⟶ (ihom K).obj M) :=
    { toFun := fun s ↦ s ≫ ringedSiteDerivedEvaluationHom K M
      invFun := fun t ↦ t ≫ inv (ringedSiteDerivedEvaluationHom K M)
      left_inv := by
        intro s
        simp [Category.assoc]
      right_inv := by
        intro t
        simp [Category.assoc] }
  refine ⟨?_, ?_⟩
  · intro s t hst
    apply postcompEquiv.injective
    apply MonoidalClosed.uncurry'_injective
    simpa [postcompEquiv] using hst
  · intro f
    refine ⟨postcompEquiv.symm (MonoidalClosed.curry' f), ?_⟩
    simp [postcompEquiv, ringedSiteDerivedEvaluationH0ToHom]

section AdditiveComparison

variable [MonoidalPreadditive (RingedSiteDerived J 𝒪)]

/-- Lemma 21.48.4 (4) in `AddCommGrpCat`: under the additive hypotheses, the canonical map
`H⁰(𝒞, M ⊗ K^∨) ⟶ Hom_{D(𝒪)}(K, M)` is an isomorphism of abelian groups. -/
@[stacks 08JJ]
instance isIso_ringedSiteDerivedEvaluationH0ToHomAddCommGrpHom_of_isPerfect
    {K M : DMod} (hK : K.IsPerfect) :
    IsIso (ringedSiteDerivedEvaluationH0ToHomAddCommGrpHom K M) := by
  exact (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).2 <|
    by
      simpa [ringedSiteDerivedEvaluationH0ToHomAddCommGrpHom,
        ringedSiteDerivedEvaluationH0ToHomAddMonoidHom] using
        bijective_ringedSiteDerivedEvaluationH0ToHom_of_isPerfect hK

end AdditiveComparison

end

end SheafOfModules.RingedSite
