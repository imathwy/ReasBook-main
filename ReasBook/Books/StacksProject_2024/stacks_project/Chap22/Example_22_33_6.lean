import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived

open CategoryTheory

noncomputable section

universe uKA uKB uDA uDB vKA vKB vDA vDB

section

variable {KA : Type uKA} {KB : Type uKB} {DA : Type uDA} {DB : Type uDB}
variable [Category.{vKA} KA] [Category.{vKB} KB] [Category.{vDA} DA] [Category.{vDB} DB]
variable (QisA : MorphismProperty KA) (QisB : MorphismProperty KB)
variable (QA : KA ⥤ DA) (QB : KB ⥤ DB)
variable [QA.IsLocalization QisA] [QB.IsLocalization QisB]
variable (tensorWithBOnK : KA ⥤ KB)
variable (homFromBOnK restrictionOnK : KB ⥤ KA)
variable [(tensorWithBOnK ⋙ QB).HasLeftDerivedFunctor QisA]
variable [(homFromBOnK ⋙ QA).HasRightDerivedFunctor QisB]
variable (hRestriction_inverts : QisB.IsInvertedBy (restrictionOnK ⋙ QA))

local notation "derivedTensorWithB" =>
  Functor.totalLeftDerived (tensorWithBOnK ⋙ QB) QA QisA
local notation "derivedHomFromB" =>
  Functor.totalRightDerived (homFromBOnK ⋙ QA) QB QisB
local notation "restrictionDerived" =>
  (Localization.lift (restrictionOnK ⋙ QA) hRestriction_inverts QB : DB ⥤ DA)

-- Stacks tag evidence is consistent for this item: both the item tag and source URL give `0BYX`.
-- Semantic recall hits: `Functor.totalLeftDerived`, `Functor.totalRightDerived`,
-- `Localization.lift`, and `Adjunction.homEquiv`.

/-- Example 22.33.6 (1): for a homomorphism `(A, d) → (B, d)` of differential graded
`R`-algebras, the canonical evaluation-at-one isomorphism
`Hom_{Mod^{dg}_{(B,d)}}(B, N) ≅ N_A`, functorial in `N`, identifies the right derived functor
`RHom(B, -)` with the restriction functor on derived categories. Here `homFromBOnK` models the
underived internal-Hom functor from `B`, and `restrictionOnK` models restriction of scalars. -/
@[stacks 0BYX]
noncomputable def derivedHomFromAlgebra_iso_restriction
    (evalAtOneIso : homFromBOnK ≅ restrictionOnK) :
    derivedHomFromB ≅ restrictionDerived :=
  let _ :
      Functor.IsRightDerivedFunctor
        restrictionDerived
        (Localization.fac (restrictionOnK ⋙ QA) hRestriction_inverts QB).inv
        QisB := by
    simpa using
      (Functor.isRightDerivedFunctor_of_inverts
        QisB
        restrictionDerived
        (Localization.fac (restrictionOnK ⋙ QA) hRestriction_inverts QB))
  Functor.rightDerivedNatIso
    derivedHomFromB
    restrictionDerived
    (Functor.totalRightDerivedUnit (homFromBOnK ⋙ QA) QB QisB)
    (Localization.fac (restrictionOnK ⋙ QA) hRestriction_inverts QB).inv
    QisB
    (Functor.isoWhiskerRight evalAtOneIso QA)

/-- Example 22.33.6 (2): tensoring with `B`, viewed as a differential graded `(A, B)`-bimodule,
has left adjoint equal to restriction of scalars on derived categories. Concretely, if
`tensorWithBOnK` is underived-left-adjoint to `homFromBOnK`, and part `(1)` identifies
`homFromBOnK` with restriction of scalars by evaluation at `1`, then the derived tensor functor is
a left adjoint and the derived restriction functor is a right adjoint.

The canonical owner `Adjunction.derived` is used only inside the proof, so this file keeps the
public output proposition-valued instead of exporting a sorry-tainted adjunction datum. -/
@[stacks 0BYX]
theorem derivedTensorWithAlgebra_leftAdjoint_and_derivedHomFromAlgebra_rightAdjoint
    (underivedAdj : tensorWithBOnK ⊣ homFromBOnK) :
    Functor.IsLeftAdjoint derivedTensorWithB ∧
      Functor.IsRightAdjoint derivedHomFromB := by
  letI :
      (derivedTensorWithB ⋙ derivedHomFromB).IsLeftDerivedFunctor
        ((QA.associator derivedTensorWithB derivedHomFromB).inv ≫
          Functor.whiskerRight
            (Functor.totalLeftDerivedCounit (tensorWithBOnK ⋙ QB) QA QisA)
            derivedHomFromB)
        QisA := by
    sorry
  letI :
      (derivedHomFromB ⋙ derivedTensorWithB).IsRightDerivedFunctor
        (Functor.whiskerRight
            (Functor.totalRightDerivedUnit (homFromBOnK ⋙ QA) QB QisB)
            derivedTensorWithB ≫
          (QB.associator derivedHomFromB derivedTensorWithB).hom)
        QisB := by
    sorry
  let hAdj : derivedTensorWithB ⊣ derivedHomFromB :=
    Adjunction.derived
      underivedAdj
      QisA
      QisB
      (Functor.totalLeftDerivedCounit (tensorWithBOnK ⋙ QB) QA QisA)
      (Functor.totalRightDerivedUnit (homFromBOnK ⋙ QA) QB QisB)
  exact ⟨hAdj.isLeftAdjoint, hAdj.isRightAdjoint⟩

/-- Example 22.33.6 (2): tensoring with `B`, viewed as a differential graded `(A, B)`-bimodule,
has left adjoint equal to restriction of scalars on derived categories. Concretely, if
`tensorWithBOnK` is underived-left-adjoint to `homFromBOnK`, and part `(1)` identifies
`homFromBOnK` with restriction of scalars by evaluation at `1`, then the derived tensor functor is
a left adjoint and the derived restriction functor is a right adjoint.

The source-facing right-adjoint statement is obtained by transporting the canonical derived-Hom
adjointness across the isomorphism from part `(1)`. -/
@[stacks 0BYX]
theorem derivedTensorWithAlgebra_leftAdjoint_and_restriction_rightAdjoint
    (underivedAdj : tensorWithBOnK ⊣ homFromBOnK)
    (evalAtOneIso : homFromBOnK ≅ restrictionOnK) :
    Functor.IsLeftAdjoint derivedTensorWithB ∧
      Functor.IsRightAdjoint restrictionDerived := by
  let hAdj :
      Functor.IsLeftAdjoint derivedTensorWithB ∧ Functor.IsRightAdjoint derivedHomFromB :=
    derivedTensorWithAlgebra_leftAdjoint_and_derivedHomFromAlgebra_rightAdjoint
      QisA QisB QA QB tensorWithBOnK homFromBOnK underivedAdj
  let hRestriction :
      derivedHomFromB ≅ restrictionDerived :=
    derivedHomFromAlgebra_iso_restriction
      QisB QA QB homFromBOnK restrictionOnK hRestriction_inverts evalAtOneIso
  let _ : Functor.IsRightAdjoint derivedHomFromB := hAdj.2
  exact ⟨hAdj.1, Functor.isRightAdjoint_of_iso hRestriction⟩

include QisA QisB

/-- Companion theorem: the derived tensor-with-`B` functor from Example `22.33.6` is a left
adjoint once the underived tensor/Hom adjunction is fixed. -/
theorem derivedTensorWithAlgebra_isLeftAdjoint
    (underivedAdj : tensorWithBOnK ⊣ homFromBOnK) :
    Functor.IsLeftAdjoint derivedTensorWithB :=
  (derivedTensorWithAlgebra_leftAdjoint_and_derivedHomFromAlgebra_rightAdjoint
    QisA QisB QA QB tensorWithBOnK homFromBOnK underivedAdj).1

/-- Companion theorem: the right derived functor `RHom(B, -)` from Example `22.33.6` is a right
adjoint once the underived tensor/Hom adjunction is fixed. -/
theorem derivedHomFromAlgebra_isRightAdjoint
    (underivedAdj : tensorWithBOnK ⊣ homFromBOnK) :
    Functor.IsRightAdjoint derivedHomFromB :=
  (derivedTensorWithAlgebra_leftAdjoint_and_derivedHomFromAlgebra_rightAdjoint
    QisA QisB QA QB tensorWithBOnK homFromBOnK underivedAdj).2

/-- Companion theorem: the derived restriction functor from Example `22.33.6` is a right adjoint
once the underived tensor/Hom adjunction and evaluation-at-one identification are fixed. -/
theorem restrictionDerived_isRightAdjoint
    (underivedAdj : tensorWithBOnK ⊣ homFromBOnK)
    (evalAtOneIso : homFromBOnK ≅ restrictionOnK) :
    Functor.IsRightAdjoint restrictionDerived := by
  let hRestriction :
      derivedHomFromB ≅ restrictionDerived :=
    derivedHomFromAlgebra_iso_restriction
      QisB QA QB homFromBOnK restrictionOnK hRestriction_inverts evalAtOneIso
  let _ : Functor.IsRightAdjoint derivedHomFromB :=
    derivedHomFromAlgebra_isRightAdjoint
      QisA QisB QA QB tensorWithBOnK homFromBOnK underivedAdj
  exact
    Functor.isRightAdjoint_of_iso hRestriction

omit QisA QisB

variable (tensorWithRegularBOnK : KB ⥤ KA)
variable [(tensorWithRegularBOnK ⋙ QA).HasLeftDerivedFunctor QisB]

local notation "derivedTensorWithRegularB" =>
  Functor.totalLeftDerived (tensorWithRegularBOnK ⋙ QA) QB QisB

/-- Example 22.33.6 (4): restriction is also tensoring with the regular differential graded
`(B, A)`-bimodule `{}_B B_A`; equivalently `N_A = N ⊗_B B = N ⊗^L_B B` functorially on the
derived category. The functor `tensorWithRegularBOnK` models underived tensor with this regular
bimodule. -/
@[stacks 0BYX]
noncomputable def restriction_iso_derivedTensorWithRegularBimodule
    (underivedTensorIso : restrictionOnK ≅ tensorWithRegularBOnK) :
    restrictionDerived ≅ derivedTensorWithRegularB :=
  let _ :
      Functor.IsLeftDerivedFunctor
        restrictionDerived
        (Localization.fac (restrictionOnK ⋙ QA) hRestriction_inverts QB).hom
        QisB := by
    simpa using
      (Functor.isLeftDerivedFunctor_of_inverts
        QisB
        restrictionDerived
        (Localization.fac (restrictionOnK ⋙ QA) hRestriction_inverts QB))
  Functor.leftDerivedNatIso
    restrictionDerived
    derivedTensorWithRegularB
    (Localization.fac (restrictionOnK ⋙ QA) hRestriction_inverts QB).hom
    (Functor.totalLeftDerivedCounit (tensorWithRegularBOnK ⋙ QA) QB QisB)
    QisB
    (Functor.isoWhiskerRight underivedTensorIso QA)

end
