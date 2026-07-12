import StacksProject_2024.Chap13.Definition_13_33_1
import StacksProject_2024.Chap13.Definition_13_34_1
import StacksProject_2024.Chap20.«20_42_8_1»
import StacksProject_2024.Chap20.Definition_20_49_1

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (RingedSpaceDerived X)]
variable [MonoidalClosed (RingedSpaceDerived X)]

local notation "DMod" => RingedSpaceDerived X
set_option quotPrecheck false in
local notation:20 A " ⟹ " B:19 => (ihom A).obj B

/- Domain-style sampling for Lemma 20.51.1:
- primary domain: homotopy colimits and derived inverse limits in the closed monoidal
  derived category `D(𝒪_X)` of a ringed space;
- sampled owner declarations:
  `CategoryTheory.IsHomotopyColimitOf`,
  `CategoryTheory.IsDerivedLimit`,
  `CategoryTheory.SequentialInverseSystem`,
  `CategoryTheory.Functor.ofSequence`,
  `CategoryTheory.Functor.ofOpSequence`,
  `ringedSpaceDerivedDual`;
- best owner abstraction:
  `source-facing`: the tensor-dual inverse system
    `n ↦ E ⊗ (K n)^∨` attached to a sequential system
    `K₀ ⟶ K₁ ⟶ K₂ ⟶ ⋯` in `D(𝒪_X)`, together with the derived-limit statement for
    `Khocolim ⟹ E`;
  `core/canonical`: the Chapter 13 owners `IsHomotopyColimitOf`, `IsDerivedLimit`, and
    `SequentialInverseSystem`;
  `bridge/view`: the ringed-space dual notation `(K n)^∨` from the Chapter 20 internal Hom API.

This item is source-facing in Chapter 20: the public API should keep the explicit tensor-dual
tower rather than hiding it behind a Chapter 21 ringed-site wrapper. -/

/-- The source-facing inverse system with transition maps
`E ⊗ (K (n + 1))^∨ ⟶ E ⊗ (K n)^∨`
attached to a sequential system `K₀ ⟶ K₁ ⟶ K₂ ⟶ ⋯` in `D(𝒪_X)`. -/
noncomputable abbrev ringedSpaceDerivedDualTensorInverseSystem
    (E : DMod) (K : ℕ → DMod) (f : ∀ n, K n ⟶ K (n + 1)) :
    SequentialInverseSystem DMod :=
  let A : ℕ → DMod := fun n ↦ E ⊗ (K n)^∨
  Functor.ofOpSequence fun n ↦
    show A (n + 1) ⟶ A n from
      E ◁ (MonoidalClosed.pre (f n)).app (𝟙_ DMod)

@[simp] theorem ringedSpaceDerivedDualTensorInverseSystem_obj
    (E : DMod) (K : ℕ → DMod) (f : ∀ n, K n ⟶ K (n + 1)) (n : ℕ) :
    (ringedSpaceDerivedDualTensorInverseSystem E K f).obj (Opposite.op n) = E ⊗ (K n)^∨ :=
  by simp [ringedSpaceDerivedDualTensorInverseSystem]

theorem ringedSpaceDerivedDualTensorInverseSystem_stepMap
    (E : DMod) (K : ℕ → DMod) (f : ∀ n, K n ⟶ K (n + 1)) (n : ℕ) :
    SequentialInverseSystem.stepMap (ringedSpaceDerivedDualTensorInverseSystem E K f) n =
      E ◁ (MonoidalClosed.pre (f n)).app (𝟙_ DMod) := by
  simp [SequentialInverseSystem.stepMap, SequentialInverseSystem.transitionMap,
    ringedSpaceDerivedDualTensorInverseSystem, Functor.ofOpSequence_map_homOfLE_succ]

-- Proof sketch: identify the internal-Hom tower `n ↦ K n ⟹ E` with the source-facing
-- tensor-dual tower by the perfect-stage comparison from Lemma `20.50.5`, then transport the
-- canonical Milnor derived-limit witness for `Khocolim ⟹ E` across that tower isomorphism.
/-- Lemma 20.51.1: if `Khocolim` is a homotopy colimit of a sequential system of perfect objects
`K₀ ⟶ K₁ ⟶ K₂ ⟶ ⋯` in `D(𝒪_X)`, then for every `E : D(𝒪_X)` the object `Khocolim ⟹ E`
is a derived limit of the source-facing tensor-dual
inverse system `ringedSpaceDerivedDualTensorInverseSystem E K f`. -/
@[stacks 0DJI]
theorem ringedSpaceDerivedInternalHom_isDerivedLimit_of_homotopyColimit
    (K : ℕ → DMod) (f : ∀ n, K n ⟶ K (n + 1)) {Khocolim : DMod}
    [HasCoproduct (Functor.ofSequence f).obj]
    (hperfect : ∀ n, DerivedCategory.IsPerfect (K n))
    (hKhocolim : IsHomotopyColimitOf (Functor.ofSequence f) Khocolim)
    (E : DMod) :
    IsDerivedLimit
      (ringedSpaceDerivedDualTensorInverseSystem E K f)
      (Khocolim ⟹ E) := by
  sorry

end

end AlgebraicGeometry.RingedSpace
