import StacksProject_2024.stacks_project.Chap20.«20_3_0_4»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry
open scoped RingedSpace.Hom

noncomputable section

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow_isLocalization

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.14.1:
- primary domain: bounded-below derived pushforward for sheaves of modules on ringed spaces;
- sampled owner declarations:
  `HomotopyCategory.Plus.quotient`,
  `mapBoundedBelowHomotopyToDerivedBelow`,
  `mapBoundedBelowHomotopyCategoryToDerivedBelow`,
  `Functor.totalRightDerived`,
  `Functor.totalRightDerivedUnit`;
- best owner abstraction:
  `source-facing`: the canonical morphism in `D⁺(Y)` induced by a map of bounded-below complexes
    `𝒢 ⟶ f_* ℱ`,
  `core/canonical`: the Chapter 13 bounded-below localization functors together with
    `Functor.totalRightDerived` and `Functor.totalRightDerivedUnit`,
  `bridge/view`: the passage from a concrete map of bounded-below complexes to its image in the
    bounded-below homotopy category via `HomotopyCategory.Plus.quotient`.
- primitive data: the additive pushforward functor `f _*`, its induced bounded-below complex lift,
  the morphism `φ : 𝒢 ⟶ (pushforwardPlus f).obj ℱ`, and the canonical quotient functors from
  bounded-below complexes to bounded-below homotopy categories;
- derived API: the induced comparison morphism in `D⁺(Y)` and its naturality.

This file is therefore a `bridge/view` layer over the Chapter 13 owners; it should use the
canonical quotient and total-right-derived-unit APIs directly rather than keep a parallel
complex-to-homotopy wrapper.
-/

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)
local notation "ModX" => RingedSpace.Modules X
local notation "ModY" => RingedSpace.Modules Y

variable [(f _*).Additive]

private theorem pushforward_obj_mem_boundedBelow
    (K : Comp⁺(ModX)) :
    CochainComplex.plus ModY
      (((f _*).mapHomologicalComplex (ComplexShape.up ℤ)).obj ((CochainComplex.Plus.ι ModX).obj K)) := by
  -- Reuse a lower bound for `K`; pushforward preserves the corresponding `IsStrictlyGE` witness.
  rcases
      (CochainComplex.plus_iff ModX ((CochainComplex.Plus.ι ModX).obj K)).1 K.property with
    ⟨a, ha⟩
  refine (CochainComplex.plus_iff ModY _).2 ⟨a, ?_⟩
  let _ :
      (((CochainComplex.Plus.ι ModX).obj K) : CochainComplex ModX ℤ).IsStrictlyGE a := ha
  infer_instance

/-- The bounded-below complex-level pushforward functor induced by a morphism of ringed spaces. -/
abbrev pushforwardPlus (f : X ⟶ Y) [(f _*).Additive] : Comp⁺(ModX) ⥤ Comp⁺(ModY) :=
  (CochainComplex.plus ModY).lift
    (CochainComplex.Plus.ι ModX ⋙ (f _*).mapHomologicalComplex (ComplexShape.up ℤ))
    (pushforward_obj_mem_boundedBelow f)

local notation "QX" => (mapBoundedBelowHomotopyToDerivedBelow : K⁺(ModX) ⥤ D⁺(ModX))
local notation "QY" => (mapBoundedBelowHomotopyToDerivedBelow : K⁺(ModY) ⥤ D⁺(ModY))
local notation "qX" => (HomotopyCategory.Plus.quotient ModX : Comp⁺(ModX) ⥤ K⁺(ModX))
local notation "qY" => (HomotopyCategory.Plus.quotient ModY : Comp⁺(ModY) ⥤ K⁺(ModY))
local notation "Rf+" f => Hom.modulePushforwardDerivedPlus f

variable [Functor.HasRightDerivedFunctor
  (mapBoundedBelowHomotopyCategoryToDerivedBelow (f _*))
  (Qis⁺(X.Modules))]

/-- The bounded-below total-right-derived unit for module pushforward on ringed spaces. -/
abbrev modulePushforwardDerivedPlusUnit (f : X ⟶ Y) [(f _*).Additive]
    [Functor.HasRightDerivedFunctor
      (mapBoundedBelowHomotopyCategoryToDerivedBelow (f _*))
      (Qis⁺(X.Modules))] :
    mapBoundedBelowHomotopyCategoryToDerivedBelow (f _*) ⟶
      QX ⋙ Rf+ f :=
  Functor.totalRightDerivedUnit
    (mapBoundedBelowHomotopyCategoryToDerivedBelow (f _*))
    QX
    (Qis⁺(X.Modules))

/-- The bounded-below total-right-derived unit for module pushforward is natural in the complex. -/
theorem modulePushforwardDerivedPlusUnit_naturality_assoc
    {ℱ₁ ℱ₂ : Comp⁺(ModX)}
    (β : ℱ₁ ⟶ ℱ₂) :
    (QY).map ((qY).map ((pushforwardPlus f).map β)) ≫
        (modulePushforwardDerivedPlusUnit f).app ((qX).obj ℱ₂) =
      (modulePushforwardDerivedPlusUnit f).app ((qX).obj ℱ₁) ≫
        (Rf+ f).map ((QX).map ((qX).map β)) :=
  (modulePushforwardDerivedPlusUnit f).naturality ((qX).map β)

/-- Lemma 20.14.1: a morphism of bounded-below complexes `𝒢 ⟶ f_* ℱ` induces the canonical
morphism `𝒢 ⟶ Rf_* ℱ` in `D⁺(Y)`. -/
@[stacks 01F8]
noncomputable def boundedBelowDerivedPushforwardComparison
    {𝒢 : Comp⁺(ModY)}
    {ℱ : Comp⁺(ModX)}
    (φ : 𝒢 ⟶ (pushforwardPlus f).obj ℱ) :
    (QY).obj ((qY).obj 𝒢) ⟶
      Rf_[f] ((QX).obj ((qX).obj ℱ)) :=
  (QY).map ((qY).map φ) ≫
    (modulePushforwardDerivedPlusUnit f).app ((qX).obj ℱ)

-- Proof sketch: apply the functoriality of the bounded-below homotopy quotient `Q`, the
-- localization functor to `D⁺`, and the derived pushforward functor to the commutative square
-- of complexes, then use naturality of the total right derived unit.
/-- The canonical comparison morphism to `Rf_*` is natural in the triple `(𝒢, ℱ, φ)`. -/
theorem boundedBelowDerivedPushforwardComparison_natural
    {𝒢₁ 𝒢₂ : Comp⁺(ModY)}
    {ℱ₁ ℱ₂ : Comp⁺(ModX)}
    (φ₁ : 𝒢₁ ⟶ (pushforwardPlus f).obj ℱ₁)
    (φ₂ : 𝒢₂ ⟶ (pushforwardPlus f).obj ℱ₂)
    (α : 𝒢₁ ⟶ 𝒢₂)
    (β : ℱ₁ ⟶ ℱ₂)
    (hcomm : φ₁ ≫ (pushforwardPlus f).map β = α ≫ φ₂) :
    CommSq
      ((QY).map ((qY).map α))
      (boundedBelowDerivedPushforwardComparison f φ₁)
      (boundedBelowDerivedPushforwardComparison f φ₂)
      ((Rf+ f).map ((QX).map ((qX).map β))) := by
  -- Compose the mapped square of complexes with the naturality square for the derived-unit map.
  refine CommSq.mk ?_
  have hleft :
      (QY).map ((qY).map α) ≫ (QY).map ((qY).map φ₂) =
        (QY).map ((qY).map φ₁) ≫ (QY).map ((qY).map ((pushforwardPlus f).map β)) := by
    -- Functoriality transports the square on complexes to the homotopy and derived levels.
    simpa [Functor.map_comp] using
      congrArg (fun k ↦ (QY).map ((qY).map k)) hcomm.symm
  have hcomp₁ :
      (QY).map ((qY).map α) ≫ boundedBelowDerivedPushforwardComparison f φ₂ =
        (((QY).map ((qY).map α) ≫ (QY).map ((qY).map φ₂)) ≫
          (modulePushforwardDerivedPlusUnit f).app ((qX).obj ℱ₂)) := by
    rw [boundedBelowDerivedPushforwardComparison, Category.assoc]
    rfl
  have hcomp₂ :
      (((QY).map ((qY).map α) ≫ (QY).map ((qY).map φ₂)) ≫
          (modulePushforwardDerivedPlusUnit f).app ((qX).obj ℱ₂)) =
        (((QY).map ((qY).map φ₁) ≫ (QY).map ((qY).map ((pushforwardPlus f).map β))) ≫
          (modulePushforwardDerivedPlusUnit f).app ((qX).obj ℱ₂)) := by
    exact
      congrArg
        (fun k ↦ k ≫ (modulePushforwardDerivedPlusUnit f).app ((qX).obj ℱ₂))
        hleft
  have hcomp₃ :
      (((QY).map ((qY).map φ₁) ≫ (QY).map ((qY).map ((pushforwardPlus f).map β))) ≫
          (modulePushforwardDerivedPlusUnit f).app ((qX).obj ℱ₂)) =
        (boundedBelowDerivedPushforwardComparison f φ₁ ≫
          (Rf+ f).map ((QX).map ((qX).map β))) := by
    simpa [boundedBelowDerivedPushforwardComparison, Category.assoc] using
      congrArg
        (fun k ↦ (QY).map ((qY).map φ₁) ≫ k)
        (modulePushforwardDerivedPlusUnit_naturality_assoc f β)
  exact hcomp₁.trans (hcomp₂.trans hcomp₃)

end AlgebraicGeometry.RingedSpace
