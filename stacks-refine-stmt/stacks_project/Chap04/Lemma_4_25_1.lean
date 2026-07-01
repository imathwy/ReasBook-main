import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits

universe w v u

namespace CategoryTheory

/-
Domain-style sampling for Lemma 4.25.1:
- primary domain: corepresentability of Type-valued functors via their categories of elements
- inspected owner-level declarations:
  `Functor.IsCorepresentable`,
  `Functor.Elements.isInitialOfCorepresentableBy`,
  `CategoryOfElements` limit constructors from `Mathlib.CategoryTheory.Limits.Elements`,
  `has_limits_of_hasEqualizers_and_products`,
  `preservesLimits_of_preservesEqualizers_and_products`
- best owner abstraction: `Functor.IsCorepresentable`

Primitive-vs-derived split:
- primitive data: a small family `(X i, x i)` of elements of `F`
- derived bridge: an initial object of `F.Elements`
- source-facing conclusion: `F.IsCorepresentable`

Source/core/bridge triage:
- `source-facing`: `isCorepresentable_of_preservesLimits_of_generating_family`
- `core/canonical`: `Functor.IsCorepresentable`
- `bridge/view`: `Functor.isCorepresentable_of_hasInitial_elements` and the intermediate
  initial-object statement for `F.Elements` -/

namespace Functor

/-- If the category of elements of a `Type`-valued functor has an initial object, then the functor
is corepresentable. This is the converse direction to the canonical mathlib construction
`Elements.isInitialOfCorepresentableBy`. -/
theorem isCorepresentable_of_hasInitial_elements
    {C : Type u} [Category.{v} C] {F : C ⥤ Type w} [HasInitial F.Elements] :
    F.IsCorepresentable := by
  let A : F.Elements := ⊥_ F.Elements
  refine (show F.CorepresentableBy A.1 from ?_).isCorepresentable
  refine
    { homEquiv :=
        { toFun := fun f ↦ F.map f A.2
          invFun := fun y ↦ (initial.to (F.elementsMk _ y)).1
          left_inv := ?_
          right_inv := ?_ }
      homEquiv_comp := ?_ }
  · intro f
    let B : F.Elements := F.elementsMk _ (F.map f A.2)
    exact congrArg Subtype.val <|
      initialIsInitial.hom_ext _ <| CategoryOfElements.homMk _ B f rfl
  · intro y
    exact (initial.to (F.elementsMk _ y)).2
  · intro _ _
    simp

end Functor

section

variable {C : Type u} [Category.{v} C] [HasProducts.{v} C] [HasEqualizers C]
variable (F : C ⥤ Type w)
variable [∀ J : Type v, PreservesLimitsOfShape (Discrete J) F]
variable [PreservesLimitsOfShape WalkingParallelPair F]
variable {I : Type v} (X : I → C) (x : ∀ i : I, F.obj (X i))

/-- Lemma 4.25.1, categorical form: a small jointly surjective family of elements yields an
initial object in the category of elements. -/
theorem hasInitial_elements_of_preservesLimits_of_generating_family
    (h_generate :
      ∀ ⦃Y : C⦄ (y : F.obj Y), ∃ i : I, ∃ φ : X i ⟶ Y, F.map φ (x i) = y) :
    HasInitial F.Elements := by
  let F' : C ⥤ Type (max v w) := F ⋙ uliftFunctor.{v, w}
  let _ : ∀ J : Type v, PreservesLimitsOfShape (Discrete J) F' := by
    intro J
    infer_instance
  let _ : PreservesLimitsOfShape WalkingParallelPair F' := by
    infer_instance
  let _ : HasProducts.{v} F'.Elements := by
    intro J
    let _ : Small.{max v w} J := by infer_instance
    infer_instance
  let _ : HasWideEqualizers.{v} C := by
    let _ : HasLimitsOfSize.{v, v} C :=
      has_limits_of_hasEqualizers_and_products
    infer_instance
  let _ : ∀ J : Type v, PreservesLimitsOfShape (WalkingParallelFamily J) F' := by
    intro J
    let _ : PreservesLimitsOfSize.{v, v} F' :=
      preservesLimits_of_preservesEqualizers_and_products F'
    infer_instance
  let _ : HasWideEqualizers.{v} F'.Elements := by
    intro J
    let _ : Small.{max v w} (WalkingParallelFamily.{v} J) := by infer_instance
    infer_instance
  have hF' : HasInitial F'.Elements := by
    let B : I → F'.Elements := fun i ↦ F'.elementsMk (X i) (ULift.up (x i))
    have hB : ∀ A : F'.Elements, ∃ i, Nonempty (B i ⟶ A) := by
      intro A
      obtain ⟨i, φ, hφ⟩ := h_generate A.2.down
      exact ⟨i, ⟨CategoryOfElements.homMk (B i) A φ (congrArg ULift.up hφ)⟩⟩
    obtain ⟨T, hT⟩ := has_weakly_initial_of_weakly_initial_set_and_hasProducts hB
    exact hasInitial_of_weakly_initial_and_hasWideEqualizers hT
  have hCorepr' : F'.IsCorepresentable := by
    let _ : HasInitial F'.Elements := hF'
    exact Functor.isCorepresentable_of_hasInitial_elements
  let _ : F.IsCorepresentable :=
    Functor.isCorepresentable_comp_uliftFunctor_iff.mp hCorepr'
  infer_instance

/-- Lemma 4.25.1: a set-valued functor preserving products and equalizers, together with a small
jointly surjective family of elements, is corepresentable. In mathlib's covariant convention, this
is `F.IsCorepresentable`. -/
theorem isCorepresentable_of_preservesLimits_of_generating_family
    (h_generate :
      ∀ ⦃Y : C⦄ (y : F.obj Y), ∃ i : I, ∃ φ : X i ⟶ Y, F.map φ (x i) = y) :
    F.IsCorepresentable := by
  let _ : HasInitial F.Elements :=
    hasInitial_elements_of_preservesLimits_of_generating_family F X x h_generate
  exact Functor.isCorepresentable_of_hasInitial_elements

end

end CategoryTheory
