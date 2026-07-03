import Mathlib
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
import Mathlib.Tactic.Recall
import Mathlib.Topology.Category.TopCat.Limits.Basic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_4_25_1 (from Chap04) -/
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

omit [HasProducts.{v} C] [HasEqualizers C]
    [∀ J : Type v, PreservesLimitsOfShape (Discrete J) F]
    [PreservesLimitsOfShape WalkingParallelPair F] in
/-- Helper for Lemma 4.25.1: after composing with `uliftFunctor`, the chosen family still gives
a weakly initial family in the category of elements. -/
lemma generating_family_yields_weakly_initial_elements_ulift
    (h_generate :
      ∀ ⦃Y : C⦄ (y : F.obj Y), ∃ i : I, ∃ φ : X i ⟶ Y, F.map φ (x i) = y)
    (A : (F ⋙ uliftFunctor.{v, w}).Elements) :
    ∃ i : I,
      Nonempty (((F ⋙ uliftFunctor.{v, w}).elementsMk (X i) (ULift.up (x i))) ⟶ A) := by
  let B : I → (F ⋙ uliftFunctor.{v, w}).Elements :=
    fun i ↦ (F ⋙ uliftFunctor.{v, w}).elementsMk (X i) (ULift.up (x i))
  -- Unpack the target element and invoke the generating-family hypothesis on its underlying value.
  obtain ⟨i, φ, hφ⟩ := h_generate A.2.down
  -- Repackage the generating morphism as a morphism in the category of elements.
  refine ⟨i, ?_⟩
  exact ⟨CategoryOfElements.homMk (B i) A φ (congrArg ULift.up hφ)⟩

/-- Helper for Lemma 4.25.1: products and equalizers in `C`, together with their preservation by
`F`, provide wide equalizers in the lifted category of elements. -/
lemma elements_hasWideEqualizers_via_preserved_products_and_equalizers :
    HasWideEqualizers.{v} (F ⋙ uliftFunctor.{v, w}).Elements := by
  let F' : C ⥤ Type (max v w) := F ⋙ uliftFunctor.{v, w}
  let _ : ∀ J : Type v, PreservesLimitsOfShape (Discrete J) F' := by
    intro J
    infer_instance
  let _ : PreservesLimitsOfShape WalkingParallelPair F' := by
    infer_instance
  -- Products and equalizers generate all small limits in `C`, hence in particular wide equalizers.
  let _ : HasWideEqualizers.{v} C := by
    let _ : HasLimitsOfSize.{v, v} C :=
      has_limits_of_hasEqualizers_and_products
    infer_instance
  -- The lifted functor preserves those wide equalizers because it preserves products and equalizers.
  let _ : ∀ J : Type v, PreservesLimitsOfShape (WalkingParallelFamily J) F' := by
    intro J
    let _ : PreservesLimitsOfSize.{v, v} F' :=
      preservesLimits_of_preservesEqualizers_and_products F'
    infer_instance
  -- The category of elements inherits wide equalizers from the preserved limits.
  intro J
  let _ : Small.{max v w} (WalkingParallelFamily.{v} J) := by infer_instance
  infer_instance

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
  let _ : HasWideEqualizers.{v} F'.Elements := by
    simpa [F'] using
      (elements_hasWideEqualizers_via_preserved_products_and_equalizers (F := F))
  have hF' : HasInitial F'.Elements := by
    let B : I → F'.Elements := fun i ↦ F'.elementsMk (X i) (ULift.up (x i))
    -- After lifting universes, the chosen family is still weakly initial in the category of
    -- elements, so products package it into one weakly initial object.
    have hB : ∀ A : F'.Elements, ∃ i, Nonempty (B i ⟶ A) := by
      intro A
      simpa [B, F'] using
        generating_family_yields_weakly_initial_elements_ulift
          (F := F) (X := X) (x := x) (I := I) h_generate A
    -- Wide equalizers then upgrade that weakly initial object to an initial object, matching the
    -- source proof's passage from surjectivity to uniqueness.
    obtain ⟨T, hT⟩ := has_weakly_initial_of_weakly_initial_set_and_hasProducts hB
    exact hasInitial_of_weakly_initial_and_hasWideEqualizers hT
  have hCorepr' : F'.IsCorepresentable := by
    -- An initial object of the category of elements gives the universal element needed for
    -- corepresentability.
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

/-! ### Remark_4_25_2 (from Chap04) -/
/- Domain-style sampling for Remark 4.25.2:
- primary domain: categorical examples of adjunctions and colimits.
- inspected owner-level declarations:
  `GrpCat.adj`,
  `AddCommGrpCat.adj`,
  `TopCat.topCat_hasColimits`.
- best owner abstraction: the existing mathlib owner declarations above, with no additional local
  wrapper layer.

Primitive-vs-derived split:
- primitive data: none in this recall-only remark.
- derived API: the source examples are already packaged by the canonical adjunction and colimit
  owners in mathlib.

Source/core/bridge triage:
- `source-facing`: the textbook examples "free group", "free abelian group", and "topological
  spaces admit small colimits".
- `core/canonical`: `GrpCat.adj`, `AddCommGrpCat.adj`, and `TopCat.topCat_hasColimits`.
- `bridge/view`: none needed here, since the source statements are direct recalls of the canonical
  owners. -/

/- Remark 4.25.2: the free group on a set is the canonical left adjoint
`GrpCat.free : Type u ⥤ GrpCat` to the forgetful functor `forget GrpCat`, so its universal
property is packaged by the adjunction `GrpCat.adj`. -/
recall GrpCat.adj

/- Companion recall: the free abelian group example is expressed canonically by the adjunction
`AddCommGrpCat.free ⊣ forget AddCommGrpCat`. -/
recall AddCommGrpCat.adj

/- Companion recall: every small diagram of topological spaces has a colimit via the canonical
instance `TopCat.topCat_hasColimits`. -/
recall TopCat.topCat_hasColimits

/-! ### Theorem_4_25_3_Adjoint_functor_theorem (from Chap04) -/
universe v u

namespace CategoryTheory

variable {C D : Type u} [Category.{v} C] [Category.{v} D]

/- Domain-style sampling for Theorem 4.25.3:
- primary domain: the general adjoint functor theorem in category theory.
- inspected owner-level declarations:
  `SolutionSetCondition`,
  `isRightAdjoint_of_preservesLimits_of_solutionSetCondition`,
  `solutionSetCondition_of_isRightAdjoint`.
- best owner abstraction: `G.IsRightAdjoint` as the canonical adjointness predicate for a functor,
  with `isRightAdjoint_of_preservesLimits_of_solutionSetCondition` as the canonical constructor
  from the theorem hypotheses.

Primitive-vs-derived split:
- primitive data: none in this recall-only theorem file.
- derived API: the solution-set hypothesis is already owned by `SolutionSetCondition`, and the
  theorem conclusion is already packaged by the canonical `IsRightAdjoint` owner.

Source/core/bridge triage:
- `source-facing`: the textbook statement of the adjoint functor theorem.
- `core/canonical`: `isRightAdjoint_of_preservesLimits_of_solutionSetCondition`.
- `bridge/view`: the converse theorem `solutionSetCondition_of_isRightAdjoint`, which is related
  but not part of this numbered item. -/

/- Canonical recall: the small-family hypothesis in the general adjoint functor theorem is the
mathlib predicate `SolutionSetCondition G`. -/
recall SolutionSetCondition

/- Theorem 4.25.3 (Adjoint functor theorem): if `G : D ⥤ C` preserves limits, `D` has limits, and
`G` satisfies the solution set condition, then `G` is a right adjoint. This is exactly the
canonical mathlib theorem `isRightAdjoint_of_preservesLimits_of_solutionSetCondition`. -/
recall isRightAdjoint_of_preservesLimits_of_solutionSetCondition

end CategoryTheory
