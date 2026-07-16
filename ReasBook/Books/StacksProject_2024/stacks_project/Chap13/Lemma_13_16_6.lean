import Mathlib
import StacksProject_2024.stacks_project.Chap12.Definition_12_12_1
import StacksProject_2024.stacks_project.Chap12.Lemma_12_12_4
import StacksProject_2024.stacks_project.Chap13.Lemma_13_4_21
import StacksProject_2024.stacks_project.Chap13.Lemma_13_4_22
import StacksProject_2024.stacks_project.Chap13.Lemma_13_16_3
import StacksProject_2024.stacks_project.Chap13.Lemma_13_16_4

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open ComplexShape
open DerivedCategory.TStructure

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

section BoundedBelow

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]
  [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w} ℬ]

variable (RF : D⁺(𝒜) ⥤ D⁺(ℬ))
variable [RF.CommShift ℤ] [RF.IsTriangulated]

/- Domain-style sampling for Lemma 13.16.6:
- primary domain: bounded-below right derived functors of additive functors between abelian
  categories, expressed through the canonical triangulated-to-cohomological `δ`-functor pipeline;
- source-facing declarations: the bounded-below cohomological `δ`-functor, its degreewise
  identification with `RF.boundedBelowRightDerived`, and the usual universality consequences.

The low-level bounded-below inclusion API changed across mathlib versions, so the transport proofs
are intentionally kept as statement skeletons here rather than spelling brittle preimage maps. -/

local notation "plusι" => ObjectProperty.ι (t.plus : ObjectProperty (D(ℬ)))
local notation "H" => DerivedCategory.homologyFunctor ℬ

/-- Helper for Lemma 13.16.6: the canonical `δ`-functor on degree-zero objects
`single0ToDplus 𝒜 : 𝒜 ⥤ D^+(𝒜)`. -/
private noncomputable def single0ToDplusDeltaFunctor :
    DeltaFunctor 𝒜 D⁺(𝒜) := by
  classical
  exact sorry

/-- The underlying functor of `single0ToDplusDeltaFunctor` is the canonical degree-zero embedding
`𝒜 ⥤ D^+(𝒜)`. -/
@[simp] theorem single0ToDplusDeltaFunctor_toFunctor :
    (single0ToDplusDeltaFunctor : DeltaFunctor 𝒜 D⁺(𝒜)).toFunctor = single0ToDplus 𝒜 := by
  sorry

private noncomputable def boundedBelowRightDerivedDeltaOwner :
    DeltaFunctor 𝒜 (D(ℬ)) :=
  (single0ToDplusDeltaFunctor.postcomposeExactFunctor RF).postcomposeExactFunctor plusι

private theorem boundedBelowRightDerivedDeltaOwner_hneg (X : 𝒜) :
    IsZero (((H 0).shift (-1)).obj
      ((boundedBelowRightDerivedDeltaOwner RF).toFunctor.obj X)) := by
  sorry

/-- Lemma 13.16.6 (1): for an exact bounded-below right derived functor
`RF : D^+(𝒜) ⥤ D^+(ℬ)`, the functors `RF.boundedBelowRightDerived n` carry canonical
connecting morphisms making them into a cohomological `δ`-functor. -/
noncomputable def boundedBelowRightDerivedDeltaFunctor :
    CohomologicalDeltaFunctor 𝒜 ℬ :=
  DeltaFunctor.toCohomologicalDeltaFunctor
    (boundedBelowRightDerivedDeltaOwner RF) (H 0)
    (boundedBelowRightDerivedDeltaOwner_hneg RF)

/-- The degree-`n` branch of `boundedBelowRightDerivedDeltaFunctor RF` is the canonical functor
`A ↦ H^n((RF(A[0])) : D(ℬ))`. -/
@[simp] theorem boundedBelowRightDerivedDeltaFunctor_obj (n : ℕ) :
    ((boundedBelowRightDerivedDeltaFunctor RF n).obj) = RF.boundedBelowRightDerived n := by
  sorry

end BoundedBelow

section Universal

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]
  [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w} ℬ]

variable (F : 𝒜 ⥤ ℬ) [F.Additive] [PreservesFiniteLimits F]
variable [(mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 𝒜)).IsLocalization
  (boundedBelowHomotopyQuasiIso 𝒜)]
variable (RF : D⁺(𝒜) ⥤ D⁺(ℬ))
variable (α : mapBoundedBelowHomotopyCategoryToDerivedBelow F ⟶
  mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 𝒜) ⋙ RF)
variable [RF.IsRightDerivedFunctor α (boundedBelowHomotopyQuasiIso 𝒜)]
variable [RF.CommShift ℤ] [RF.IsTriangulated]

/-- Helper for Lemma 13.16.6: positive degrees of the bounded-below right-derived
cohomological `δ`-functor are weakly effaceable under monomorphisms into bounded-below
right-acyclic objects. -/
private theorem boundedBelowRightDerived_higherDegreesWeaklyEffaceable
    (hacyclic : ∀ X : 𝒜, ∃ (Y : 𝒜) (i : X ⟶ Y), Mono i ∧
      IsBoundedBelowRightAcyclicForAdditiveFunctor F Y)
    (n : ℕ) (hn : 0 < n) (X : 𝒜) :
    ∃ (Y : 𝒜) (u : X ⟶ Y), Mono u ∧ ((boundedBelowRightDerivedDeltaFunctor RF n).obj.map u) = 0 := by
  sorry

/-- Lemma 13.16.6 (2): if every object embeds into a bounded-below right-acyclic object, then the
canonical bounded-below right-derived cohomological `δ`-functor is universal. -/
theorem boundedBelowRightDerivedDeltaFunctor_isUniversal
    (hacyclic : ∀ X : 𝒜, ∃ (Y : 𝒜) (i : X ⟶ Y), Mono i ∧
      IsBoundedBelowRightAcyclicForAdditiveFunctor F Y) :
    CohomologicalDeltaFunctor.IsUniversal (boundedBelowRightDerivedDeltaFunctor RF) := by
  sorry

end Universal

section UnboundedCompanion

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]
  [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w} ℬ]

variable (F : 𝒜 ⥤ ℬ) [F.Additive] [PreservesFiniteLimits F] [HasInjectiveResolutions 𝒜]
variable [(mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 𝒜)).IsLocalization
  (boundedBelowHomotopyQuasiIso 𝒜)]
variable (RF : D⁺(𝒜) ⥤ D⁺(ℬ))
variable (α : mapBoundedBelowHomotopyCategoryToDerivedBelow F ⟶
  mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 𝒜) ⋙ RF)
variable [RF.IsRightDerivedFunctor α (boundedBelowHomotopyQuasiIso 𝒜)]
variable [RF.CommShift ℤ] [RF.IsTriangulated]

/-- Stronger-assumption companion: under injective resolutions, if the bounded-below family is
comparison-isomorphic to the canonical unbounded right derived functors, then the bounded-below
right-derived cohomological `δ`-functor is universal. -/
theorem boundedBelowRightDerivedDeltaFunctor_isUniversal_of_rightDerivedComparison
    (hcompare : ∀ n : ℕ, IsIsomorphic (RF.boundedBelowRightDerived n) (F.rightDerived n))
    (hacyclic : ∀ X : 𝒜, ∃ (Y : 𝒜) (i : X ⟶ Y), Mono i ∧
      IsRightAcyclicForAdditiveFunctor F Y) :
    CohomologicalDeltaFunctor.IsUniversal (boundedBelowRightDerivedDeltaFunctor RF) := by
  sorry

end UnboundedCompanion

end CategoryTheory
