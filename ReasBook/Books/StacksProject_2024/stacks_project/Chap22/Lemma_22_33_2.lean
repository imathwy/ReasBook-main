import StacksProject_2024.stacks_project.Chap13.Lemma_13_14_15
import StacksProject_2024.stacks_project.Chap22.Lemma_22_26_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty
open DifferentialGradedCategory

noncomputable section

universe u v w x y

namespace DifferentialGradedCategory

section

variable {R : Type u} [CommRing R]
variable {ModdgA : Type v} {ModdgB : Type w}
variable [DA : DifferentialGradedCategory R ModdgA]
variable [DB : DifferentialGradedCategory R ModdgB]

/-- The left-derived tensor functor `- ⊗_A^L N` attached to the underived DG tensor functor
`tensorWithN`. This is the source-facing bridge to the canonical total left derived functor
`(tensorWithN.mapK ⋙ QisB.Q).totalLeftDerived QisA.Q QisA`. -/
abbrev derivedTensor
    (QisA : MorphismProperty (K R ModdgA)) [QisA.IsSaturatedMultiplicativeSystem]
    (QisB : MorphismProperty (K R ModdgB))
    (tensorWithN : DgFunctor R ModdgA ModdgB)
    [(tensorWithN.mapK ⋙ QisB.Q).HasLeftDerivedFunctor QisA] :
    QisA.Localization ⥤ QisB.Localization :=
  (tensorWithN.mapK ⋙ QisB.Q).totalLeftDerived QisA.Q QisA

/- Source-facing notation for the derived tensor functor `- ⊗_A^L N`. -/
scoped notation:max "LTensor[" QisA ", " QisB "](" N ")" =>
  DifferentialGradedCategory.derivedTensor QisA QisB N

end

end DifferentialGradedCategory

section

variable {R : Type u} [CommRing R]
variable {ModdgA : Type v} {ModdgB : Type w} {DerivedB : Type x}
variable [DA : DifferentialGradedCategory R ModdgA]
variable [DB : DifferentialGradedCategory R ModdgB]
variable [Category.{y} DerivedB]

-- Semantic recall hits: `Functor.HasLeftDerivedFunctor`,
-- `Functor.hasLeftDerivedFunctor_of_hasPointwiseLeftDerivedFunctor`, and
-- `Functor.hasPointwiseLeftDerivedFunctor_of_subset`. Local Chapter 22 precedent represents the
-- tensor functor from `22.33.0.1` on homotopy categories as `tensorWithN.mapK`.
--
-- Source/core/bridge triage:
-- * source-facing: Lemma `22.33.2`, asserting existence of the derived tensor functor;
-- * core/canonical: `Functor.HasPointwiseLeftDerivedFunctor` and
--   `Functor.HasLeftDerivedFunctor`;
-- * bridge/view: the specialization of the Chapter `13` subset criterion to
--   `tensorWithN.mapK ⋙ QB`.

/-- The Chapter `13` subset criterion applied to `tensorWithN.mapK ⋙ QB`, producing pointwise
left-derived functors from good resolutions in `P`. -/
theorem tensorWithN_hasPointwiseLeftDerivedFunctor
    (tensorWithN : DgFunctor R ModdgA ModdgB)
    (QisA : MorphismProperty (K R ModdgA)) [QisA.IsSaturatedMultiplicativeSystem]
    (QisB : MorphismProperty (K R ModdgB))
    (QB : K R ModdgB ⥤ DerivedB) [QB.IsLocalization QisB]
    (P : ObjectProperty (K R ModdgA))
    (hP_resolves :
      ∀ M : K R ModdgA,
        ∃ (P' : K R ModdgA) (s : P' ⟶ M), P P' ∧ QisA s)
    (hP_inverts : ∀ {P₁ P₂ : K R ModdgA} (s : P₁ ⟶ P₂),
      P P₁ → P P₂ → QisA s → IsIso ((tensorWithN.mapK ⋙ QB).map s)) :
    (tensorWithN.mapK ⋙ QB).HasPointwiseLeftDerivedFunctor QisA :=
  (tensorWithN.mapK ⋙ QB).hasPointwiseLeftDerivedFunctor_of_subset
    QisA P hP_resolves hP_inverts

/-- Companion instance: for the canonical localization target `QisB.Localization`, the subset
criterion above is available directly to typeclass search. -/
instance instHasPointwiseLeftDerivedFunctorTensorWithNQ
    (tensorWithN : DgFunctor R ModdgA ModdgB)
    (QisA : MorphismProperty (K R ModdgA)) [QisA.IsSaturatedMultiplicativeSystem]
    (QisB : MorphismProperty (K R ModdgB))
    (P : ObjectProperty (K R ModdgA))
    (hP_resolves :
      ∀ M : K R ModdgA,
        ∃ (P' : K R ModdgA) (s : P' ⟶ M), P P' ∧ QisA s)
    (hP_inverts : ∀ {P₁ P₂ : K R ModdgA} (s : P₁ ⟶ P₂),
      P P₁ → P P₂ → QisA s → IsIso ((tensorWithN.mapK ⋙ QisB.Q).map s)) :
    (tensorWithN.mapK ⋙ QisB.Q).HasPointwiseLeftDerivedFunctor QisA :=
  tensorWithN_hasPointwiseLeftDerivedFunctor
    tensorWithN QisA QisB QisB.Q P hP_resolves hP_inverts

/-- Lemma 22.33.2: in the situation above, the functor obtained from tensoring with the
differential graded `(A, B)`-bimodule `N` has a left derived functor. With `QB` a localization of
`K(B, d)` at quasi-isomorphisms, the underived functor is represented by `tensorWithN.mapK ⋙ QB`;
its total left derived functor is the object denoted `- ⊗_A^L N : D(A, d) ⥤ D(B, d)`. -/
@[stacks 09LS]
theorem tensorWithN_hasLeftDerivedFunctor
    (tensorWithN : DgFunctor R ModdgA ModdgB)
    (QisA : MorphismProperty (K R ModdgA)) [QisA.IsSaturatedMultiplicativeSystem]
    (QisB : MorphismProperty (K R ModdgB))
    (QB : K R ModdgB ⥤ DerivedB) [QB.IsLocalization QisB]
    (P : ObjectProperty (K R ModdgA))
    (hP_resolves :
      ∀ M : K R ModdgA,
        ∃ (P' : K R ModdgA) (s : P' ⟶ M), P P' ∧ QisA s)
    (hP_inverts : ∀ {P₁ P₂ : K R ModdgA} (s : P₁ ⟶ P₂),
      P P₁ → P P₂ → QisA s → IsIso ((tensorWithN.mapK ⋙ QB).map s)) :
    (tensorWithN.mapK ⋙ QB).HasLeftDerivedFunctor QisA := by
  let _ : (tensorWithN.mapK ⋙ QB).HasPointwiseLeftDerivedFunctor QisA :=
    tensorWithN_hasPointwiseLeftDerivedFunctor
      tensorWithN QisA QisB QB P hP_resolves hP_inverts
  infer_instance

/-- Companion instance: for the canonical localization target `QisB.Localization`, Lemma
`22.33.2` supplies the total left-derived-functor existence owner needed downstream. -/
instance instHasLeftDerivedFunctorTensorWithNQ
    (tensorWithN : DgFunctor R ModdgA ModdgB)
    (QisA : MorphismProperty (K R ModdgA)) [QisA.IsSaturatedMultiplicativeSystem]
    (QisB : MorphismProperty (K R ModdgB))
    (P : ObjectProperty (K R ModdgA))
    (hP_resolves :
      ∀ M : K R ModdgA,
        ∃ (P' : K R ModdgA) (s : P' ⟶ M), P P' ∧ QisA s)
    (hP_inverts : ∀ {P₁ P₂ : K R ModdgA} (s : P₁ ⟶ P₂),
      P P₁ → P P₂ → QisA s → IsIso ((tensorWithN.mapK ⋙ QisB.Q).map s)) :
    (tensorWithN.mapK ⋙ QisB.Q).HasLeftDerivedFunctor QisA :=
  tensorWithN_hasLeftDerivedFunctor
    tensorWithN QisA QisB QisB.Q P hP_resolves hP_inverts

section DerivedTensorNotation

open scoped DifferentialGradedCategory

variable (tensorWithN : DgFunctor R ModdgA ModdgB)
variable (QisA : MorphismProperty (K R ModdgA)) [QisA.IsSaturatedMultiplicativeSystem]
variable (QisB : MorphismProperty (K R ModdgB))
variable [(tensorWithN.mapK ⋙ QisB.Q).HasLeftDerivedFunctor QisA]

/- The derived tensor functor denoted in the source by
`- ⊗_A^L N : D(A, d) ⥤ D(B, d)` is the canonical total left derived functor below. -/
#check ((LTensor[QisA, QisB](tensorWithN)) :
  QisA.Localization ⥤ QisB.Localization)

end DerivedTensorNotation

end
