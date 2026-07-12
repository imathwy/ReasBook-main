import StacksProject_2024.Chap22.Lemma_22_33_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open DifferentialGradedCategory

noncomputable section

universe u v w

section

variable {R : Type u} [CommRing R]
variable {DGModE : Type v} {ComplexdgO : Type w}
variable [DGModE_dg : DifferentialGradedCategory R DGModE]
variable [ComplexdgO_dg : DifferentialGradedCategory R ComplexdgO]

variable (QisE : MorphismProperty (K R DGModE))
variable (QisO : MorphismProperty (K R ComplexdgO))
variable [QisE.IsSaturatedMultiplicativeSystem]
variable (F : DgFunctor R DGModE ComplexdgO)
variable (P : ObjectProperty (K R DGModE))

-- Semantic recall hits: `tensorWithN_hasPointwiseLeftDerivedFunctor`,
-- `tensorWithN_hasLeftDerivedFunctor`, and `DifferentialGradedCategory.derivedTensor`.
--
-- Source/core/bridge triage:
-- * source-facing: Lemma `22.35.3`, asserting existence of the derived tensor functor with
--   `K^•`;
-- * core/canonical: `Functor.HasPointwiseLeftDerivedFunctor` and
--   `Functor.HasLeftDerivedFunctor`;
-- * bridge/view: the Chapter `22` specialization below of the general derived-tensor API from
--   `Lemma_22_33_2`.

/-- The Chapter `22` subset criterion for `DgFunctor.mapK F ⋙ QisO.Q`, specialized from the
generic derived-tensor API of `Lemma_22.33.2`. -/
theorem tensorWithKFunctor_hasPointwiseLeftDerivedFunctor
    (hP_resolves :
      ∀ X : K R DGModE, ∃ (X' : K R DGModE) (s : X' ⟶ X), P X' ∧ QisE s)
    (hP_inverts :
      ∀ {X X' : K R DGModE} (s : X ⟶ X'),
        P X → P X' → QisE s → IsIso ((DgFunctor.mapK F ⋙ QisO.Q).map s)) :
    (DgFunctor.mapK F ⋙ QisO.Q).HasPointwiseLeftDerivedFunctor QisE :=
  tensorWithN_hasPointwiseLeftDerivedFunctor F QisE QisO QisO.Q P hP_resolves hP_inverts

/-- Companion instance: Lemma `22.35.3` supplies the automation-facing pointwise
left-derived-functor existence owner for `DgFunctor.mapK F ⋙ QisO.Q`. -/
instance instHasPointwiseLeftDerivedFunctorTensorWithKFunctor
    (hP_resolves :
      ∀ X : K R DGModE, ∃ (X' : K R DGModE) (s : X' ⟶ X), P X' ∧ QisE s)
    (hP_inverts :
      ∀ {X X' : K R DGModE} (s : X ⟶ X'),
        P X → P X' → QisE s → IsIso ((DgFunctor.mapK F ⋙ QisO.Q).map s)) :
    (DgFunctor.mapK F ⋙ QisO.Q).HasPointwiseLeftDerivedFunctor QisE :=
  tensorWithKFunctor_hasPointwiseLeftDerivedFunctor QisE QisO F P hP_resolves hP_inverts

/- Lemma 22.35.3: the exact functor `DgFunctor.mapK F : K R DGModE ⥤ K R ComplexdgO` supplied
by Lemma `22.35.2`, after postcomposition with the localization `QisO.Q`, has a left derived
version defined on all of `QisE.Localization`. In the current Chapter `22` API this is the
specialization of `tensorWithN_hasLeftDerivedFunctor` to the canonical localization target
`QisO.Localization`, and its total left derived functor is written `LTensor[QisE, QisO](F)`. -/
@[stacks 09LX]
theorem tensorWithKFunctor_hasLeftDerivedFunctor
    (hP_resolves :
      ∀ X : K R DGModE, ∃ (X' : K R DGModE) (s : X' ⟶ X), P X' ∧ QisE s)
    (hP_inverts :
      ∀ {X X' : K R DGModE} (s : X ⟶ X'),
        P X → P X' → QisE s → IsIso ((DgFunctor.mapK F ⋙ QisO.Q).map s)) :
    (DgFunctor.mapK F ⋙ QisO.Q).HasLeftDerivedFunctor QisE :=
  tensorWithN_hasLeftDerivedFunctor F QisE QisO QisO.Q P hP_resolves hP_inverts

/-- Companion instance: Lemma `22.35.3` supplies the canonical total left-derived-functor
existence owner for `DgFunctor.mapK F ⋙ QisO.Q`. -/
instance instHasLeftDerivedFunctorTensorWithKFunctor
    (hP_resolves :
      ∀ X : K R DGModE, ∃ (X' : K R DGModE) (s : X' ⟶ X), P X' ∧ QisE s)
    (hP_inverts :
      ∀ {X X' : K R DGModE} (s : X ⟶ X'),
        P X → P X' → QisE s → IsIso ((DgFunctor.mapK F ⋙ QisO.Q).map s)) :
    (DgFunctor.mapK F ⋙ QisO.Q).HasLeftDerivedFunctor QisE :=
  tensorWithKFunctor_hasLeftDerivedFunctor QisE QisO F P hP_resolves hP_inverts

section DerivedTensorNotation

open scoped DifferentialGradedCategory

variable [(DgFunctor.mapK F ⋙ QisO.Q).HasLeftDerivedFunctor QisE]

/- The derived functor denoted in the source by
`- ⊗_E^L K^• : D(E, d) ⥤ D(𝒪)` is the canonical total left derived functor below. -/
#check ((LTensor[QisE, QisO](F)) : QisE.Localization ⥤ QisO.Localization)

end DerivedTensorNotation

end
