import StacksProject_2024.Chap13.Definition_13_33_1
import StacksProject_2024.Chap13.Definition_13_34_1
import StacksProject_2024.Chap21.«21_35_9_1»
import StacksProject_2024.Chap21.Definition_21_47_1

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open CategoryTheory.Pretriangulated
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
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

local notation "X" => RingedSite.ofCommRingSheaf J 𝒪
local notation "Mod" => ModuleCat X
local notation "DMod" => ModuleDerived X
set_option quotPrecheck false in
local notation:20 A " ⟹ " B:19 => (ihom A).obj B

/-
Domain-style sampling for Lemma 21.48.8:
- primary domain: homotopy colimits and derived inverse limits in the monoidal closed
  derived category `D(𝒪_X)` of a ringed site;
- sampled owner declarations:
  `ModuleDerived`,
  `ihom`,
  `ringedSiteDerivedDualObject`,
  `ringedSiteDerivedEvaluationHom`,
  `CategoryTheory.IsHomotopyColimitOf`,
  `CategoryTheory.IsDerivedLimit`,
  `CategoryTheory.SequentialInverseSystem`,
  `Functor.ofSequence`;
- best owner abstraction:
  `source-facing`: the tensor-dual inverse system
    `n ↦ E ⊗ K_n^∨`, exposed directly as a public
    `SequentialInverseSystem DMod`, and the derived-limit statement attached to `K`;
  `core/canonical`: the Chapter 13 owner predicates `IsHomotopyColimitOf` and
    `IsDerivedLimit`, together with the ambient closed-monoidal internal-Hom owner `ihom` and the
    Chapter 21 owners `ringedSiteDerivedDualObject` and `ringedSiteDerivedEvaluationHom`, on the
    bundled ringed-site owner `ModuleDerived X`;
  `bridge/view`: the perfect-stage comparison isomorphisms from Lemma `21.48.4`, applied
    componentwise to compare the source-facing tensor-dual tower with the owner-level
    internal-Hom tower.
- primitive data: the sequential system `K`, its transition maps `f`, the perfectness hypotheses,
  the homotopy-colimit witness, and the test object `E`;
- derived API: the derived-limit statement for `Khocolim ⟹ E`.
-/
section DualTensorTower

variable [MonoidalCategory (RingedSiteDerived J 𝒪)]
variable [MonoidalClosed (RingedSiteDerived J 𝒪)]

set_option quotPrecheck false in
/-- The source-facing inverse system
`⋯ ⟶ E ⊗ (K (n + 1))^∨ ⟶ E ⊗ (K n)^∨`
attached to a sequential diagram `K : ℕ ⥤ D(𝒪_X)`. -/
noncomputable def ringedSiteDerivedDualTensorInverseSystem
    (E : DMod) (K : ℕ ⥤ DMod) :
    SequentialInverseSystem DMod :=
  let F : ℕ → DMod := fun n ↦ E ⊗ (K.obj n)^∨
  Functor.ofOpSequence fun n ↦
    show F (n + 1) ⟶ F n from
      E ◁ (MonoidalClosed.pre (K.map (homOfLE (Nat.le_succ n)))).app (𝟙_ DMod)

/-- The `n`th stage of `ringedSiteDerivedDualTensorInverseSystem E K` is `E ⊗ (K_n)^∨`. -/
@[simp] theorem ringedSiteDerivedDualTensorInverseSystem_obj
    (E : DMod) (K : ℕ ⥤ DMod) (n : ℕ) :
    (ringedSiteDerivedDualTensorInverseSystem E K).obj (Opposite.op n) =
      E ⊗ (K.obj n)^∨ :=
  by
    simp [ringedSiteDerivedDualTensorInverseSystem]

/-- The successor transition map in
`ringedSiteDerivedDualTensorInverseSystem E K` is the tensor of the dual map induced by the
successor morphism of `K`. -/
@[simp] theorem ringedSiteDerivedDualTensorInverseSystem_transitionMap_succ
    (E : DMod) (K : ℕ ⥤ DMod) (n : ℕ) :
    (ringedSiteDerivedDualTensorInverseSystem E K).transitionMap (Nat.le_succ n) =
      E ◁ (MonoidalClosed.pre (K.map (homOfLE (Nat.le_succ n)))).app (𝟙_ DMod) := by
  simpa [ringedSiteDerivedDualTensorInverseSystem, SequentialInverseSystem.transitionMap,
    Functor.ofOpSequence_map_homOfLE_succ]

end DualTensorTower

section PerfectnessContext

variable [HasBinaryProducts C]
variable [∀ U : C, (localizedRestriction (RingedSite.ofCommRingSheaf J 𝒪) U).Additive]
variable [∀ U : C, PreservesFiniteLimits
  (localizedRestriction (RingedSite.ofCommRingSheaf J 𝒪) U)]
variable [∀ U : C, PreservesFiniteColimits
  (localizedRestriction (RingedSite.ofCommRingSheaf J 𝒪) U)]
variable [CategoryWithHomology Mod]
variable [∀ U : C, CategoryWithHomology
  (ModuleCat ((RingedSite.ofCommRingSheaf J 𝒪).localization U))]
variable [Abelian Mod]

section DerivedLimit

variable [MonoidalCategory (RingedSiteDerived J 𝒪)]
variable [BraidedCategory (RingedSiteDerived J 𝒪)]
variable [MonoidalClosed (RingedSiteDerived J 𝒪)]
variable [HasZeroObject (RingedSiteDerived J 𝒪)]
variable [Preadditive (RingedSiteDerived J 𝒪)]
variable [HasShift (RingedSiteDerived J 𝒪) ℤ]
variable [∀ n : ℤ, (shiftFunctor (RingedSiteDerived J 𝒪) n).Additive]
variable [Pretriangulated (RingedSiteDerived J 𝒪)]

/- Lemma 21.48.8: if `Khocolim` is a homotopy colimit of a sequential system of perfect objects
`K₀ ⟶ K₁ ⟶ K₂ ⟶ ⋯` in `D(𝒪_X)`, then for every `E : D(𝒪_X)` the derived internal Hom
`Khocolim ⟹ E` is a derived limit of the canonical Chapter 12/13 sequential inverse system
`ringedSiteDerivedDualTensorInverseSystem E K`, whose successor map
`E ⊗ (K_{n + 1})^∨ ⟶ E ⊗ (K_n)^∨` is induced by the diagram map `K.map (n ⟶ n + 1)`. The
source-facing tensor-dual tower is kept as the public owner, while the owner-level internal-Hom
tower enters only through the componentwise perfect-stage comparison maps from Lemma `21.48.4`. -/
@[stacks 0A0A]
theorem ringedSiteDerivedInternalHom_isDerivedLimit_of_homotopyColimit
    (K : ℕ ⥤ DMod) {Khocolim : DMod} [HasCoproduct K.obj]
    (hperfect : ∀ n, (K.obj n).IsPerfect)
    (hKhocolim : IsHomotopyColimitOf K Khocolim)
    (E : DMod) :
    IsDerivedLimit
      (ringedSiteDerivedDualTensorInverseSystem E K)
      (Khocolim ⟹ E) := by
  -- TODO for Lemma 21.48.8: combine the internal-Hom Milnor triangle with the perfect-stage
  -- tower comparison to transport the derived-limit witness to the source-facing tensor-dual tower.
  sorry

end DerivedLimit

end PerfectnessContext

end

end SheafOfModules.RingedSite
