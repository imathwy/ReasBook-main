import Mathlib
import StacksProject_2024.Chap12.Definition_12_12_1
import StacksProject_2024.Chap13.Lemma_13_4_21
import StacksProject_2024.Chap13.Lemma_13_4_22
import StacksProject_2024.Chap13.Lemma_13_16_4

open CategoryTheory
open CategoryTheory.Limits
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
- sampled owner declarations:
  `ShortComplex.ShortExact.singleδ`,
  `DeltaFunctor.postcomposeExactFunctor`,
  `DeltaFunctor.toCohomologicalDeltaFunctor`,
  `Functor.boundedBelowRightDerived`,
  `single0ToDplus`;
- best owner abstraction: the public source-facing object is the canonical bounded-below
  cohomological `δ`-functor whose degree-`n` term is `RF.boundedBelowRightDerived n`, obtained by
  first building the bounded-below `DeltaFunctor` on degree-zero objects and then applying the
  owner construction `DeltaFunctor.toCohomologicalDeltaFunctor`;
- primitive data: the explicit bounded-below degree-zero `DeltaFunctor` and the exact functor
  `RF : D⁺(𝒜) ⥤ D⁺(ℬ)`;
- derived API: the named cohomological `δ`-functor `boundedBelowRightDerivedDeltaFunctor RF`, its
  degreewise identification with `RF.boundedBelowRightDerived n`, and the universality criterion
  once objects embed into bounded-below right-acyclic objects.

Source/core/bridge triage:
- `source-facing`: the bounded-below right-derived cohomological `δ`-functor and its universality.
- `core/canonical`: `DeltaFunctor`, `DeltaFunctor.postcomposeExactFunctor`,
  `DeltaFunctor.toCohomologicalDeltaFunctor`, and `CohomologicalDeltaFunctor.IsUniversal`.
- `bridge/view`: the bounded-below degree-zero `DeltaFunctor` on `single0ToDplus 𝒜`, plus the
  later unbounded comparison with `Functor.rightDerived`.

This file should therefore expose the source-facing cohomological `δ`-functor by direct reuse of
the chapter’s `DeltaFunctor` owners, not by existentially packaging the connecting maps. -/

local notation "plusιA" => ObjectProperty.ι (t.plus : ObjectProperty (D(𝒜)))
local notation "plusι" => ObjectProperty.ι (t.plus : ObjectProperty (D(ℬ)))
local notation "H" => DerivedCategory.homologyFunctor ℬ

private noncomputable def single0ToDerivedIso :
    single0ToDplus 𝒜 ⋙ plusιA ≅ DerivedCategory.singleFunctor 𝒜 0 :=
  (𝟭 𝒜).single0PlusToSingleFunctorIso ≪≫ Functor.leftUnitor _

-- Proof sketch: transport the canonical connecting morphism `hS.singleδ` for short exact
-- sequences in `𝒜` into the bounded-below derived category `D⁺(𝒜)` via the explicit
-- degree-zero comparison `single0PlusToDerivedIso`. The distinguished-triangle and naturality
-- fields are the corresponding transported versions of `hS.singleTriangle_distinguished` and the
-- naturality of `singleδ`.
/-- The canonical `δ`-functor on degree-zero objects
`single0ToDplus 𝒜 : 𝒜 ⥤ D^+(\mathcal A)`. -/
noncomputable def single0ToDplusDeltaFunctor :
    DeltaFunctor 𝒜 D⁺(𝒜) where
  toFunctor := single0ToDplus 𝒜
  additive := inferInstance
  δ := fun {S} hS ↦
    ObjectProperty.homMk
      ((single0ToDerivedIso.hom.app S.X₃) ≫ hS.singleδ ≫
        ((single0ToDerivedIso.inv.app S.X₁)⟦(1 : ℤ)⟧') ≫
          ((Functor.commShiftIso plusιA (1 : ℤ)).inv.app
            ((single0ToDplus 𝒜).obj S.X₁)))
  map_distinguished := by
    intro S hS
    sorry
  δ_naturality := by
    intro S T hS hT φ
    sorry

/-- The underlying functor of `single0ToDplusDeltaFunctor` is the canonical degree-zero embedding
`𝒜 ⥤ D^+(\mathcal A)`. -/
@[simp] theorem single0ToDplusDeltaFunctor_toFunctor :
    (single0ToDplusDeltaFunctor : DeltaFunctor 𝒜 D⁺(𝒜)).toFunctor = single0ToDplus 𝒜 :=
  rfl

private noncomputable def boundedBelowRightDerivedDeltaOwner :
    DeltaFunctor 𝒜 (D(ℬ)) :=
  (single0ToDplusDeltaFunctor.postcomposeExactFunctor RF).postcomposeExactFunctor plusι

private theorem boundedBelowRightDerivedDeltaOwner_hneg (X : 𝒜) :
    IsZero (((H 0).shift (-1)).obj
      ((boundedBelowRightDerivedDeltaOwner RF).toFunctor.obj X)) := by
  sorry

/-- Lemma 13.16.6 (1): for an exact bounded-below right derived functor
`RF : D^+(\mathcal A) ⥤ D^+(\mathcal B)`, the functors
`RF.boundedBelowRightDerived n`, i.e. `A ↦ H^n((RF(A[0])) : D(\mathcal B))`, carry canonical
connecting morphisms making them into a cohomological `δ`-functor. -/
noncomputable def boundedBelowRightDerivedDeltaFunctor :
    CohomologicalDeltaFunctor 𝒜 ℬ :=
  DeltaFunctor.toCohomologicalDeltaFunctor
    (boundedBelowRightDerivedDeltaOwner RF) (H 0)
    (boundedBelowRightDerivedDeltaOwner_hneg RF)

/-- The degree-`n` branch of `boundedBelowRightDerivedDeltaFunctor RF` is the canonical functor
`A ↦ H^n((RF(A[0])) : D(\mathcal B))`. -/
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

-- Proof sketch: if every object embeds into a bounded-below right-acyclic object, then Lemma
-- `13.16.4` turns that acyclicity into vanishing of all positive functors
-- `RF.boundedBelowRightDerived (n + 1)` on the chosen target object. Hence every positive degree
-- of `T` is weakly effaceable, and Lemma
-- `12.12.4` gives universality.
/-- Lemma 13.16.6 (2): if `F` is left exact and every object of `𝒜` is a subobject of an object
right acyclic for the bounded-below right derived functor of `F`, then the canonical bounded-
below right-derived cohomological `δ`-functor is universal. -/
theorem boundedBelowRightDerivedDeltaFunctor_isUniversal
    (hacyclic : ∀ X : 𝒜, ∃ (Y : 𝒜) (i : X ⟶ Y), Mono i ∧
      IsBoundedBelowRightAcyclicForAdditiveFunctor F Y) :
    CohomologicalDeltaFunctor.IsUniversal (boundedBelowRightDerivedDeltaFunctor RF) := sorry

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

-- Proof sketch: specialize the bounded-below universality theorem to the stronger hypothesis
-- that the bounded-below degrees agree with the canonical unbounded `Functor.rightDerived`
-- functors and that every object embeds into an unbounded right-acyclic object.
/-- Stronger-assumption companion: under injective resolutions, if the bounded-below family
`A ↦ H^n((RF(A[0])) : D(\mathcal B))` is degreewise isomorphic to the canonical unbounded right
derived functors `F.rightDerived n`, then the canonical bounded-below right-derived
cohomological `δ`-functor is universal. -/
theorem boundedBelowRightDerivedDeltaFunctor_isUniversal_of_rightDerivedComparison
    (hcompare : ∀ n : ℕ, IsIsomorphic (RF.boundedBelowRightDerived n) (F.rightDerived n))
    (hacyclic : ∀ X : 𝒜, ∃ (Y : 𝒜) (i : X ⟶ Y), Mono i ∧
      IsRightAcyclicForAdditiveFunctor F Y) :
    CohomologicalDeltaFunctor.IsUniversal (boundedBelowRightDerivedDeltaFunctor RF) := sorry

end UnboundedCompanion

end CategoryTheory
