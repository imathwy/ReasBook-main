import StacksProject_2024.Chap04.Definition_4_27_20
import StacksProject_2024.Chap13.Lemma_13_14_15
import StacksProject_2024.Chap22.Lemma_22_31_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MorphismProperty
open DifferentialGradedCategory

noncomputable section

universe u v w

namespace DifferentialGradedCategory

section

variable {R : Type u} [CommRing R]
variable {DGModB : Type v} {DGModA : Type w}
variable [DifferentialGradedCategory R DGModB] [DifferentialGradedCategory R DGModA]

/-- The right-derived internal-Hom functor `RHom(N, -)` attached to the represented DG internal-Hom
functor `homOverBFromN`. This is the source-facing bridge to the canonical total right derived
functor `(homOverBFromN.mapK ⋙ QisA.Q).totalRightDerived QisB.Q QisB`. -/
abbrev derivedHom
    (QisB : MorphismProperty (K R DGModB)) [IsSaturatedMultiplicativeSystem QisB]
    (QisA : MorphismProperty (K R DGModA)) [IsSaturatedMultiplicativeSystem QisA]
    (homOverBFromN : DgFunctor R DGModB DGModA)
    [(homOverBFromN.mapK ⋙ QisA.Q).HasRightDerivedFunctor QisB] :
    QisB.Localization ⥤ QisA.Localization :=
  (homOverBFromN.mapK ⋙ QisA.Q).totalRightDerived QisB.Q QisB

/- Source notation for the derived internal-Hom functor `RHom(N, -)`. -/
scoped notation:max "RHom[" QisB ", " QisA "](" N ")" =>
  DifferentialGradedCategory.derivedHom QisB QisA N

end

end DifferentialGradedCategory

section

variable {R : Type u} [CommRing R]
variable {DGModB : Type v} {DGModA : Type w}
variable [DifferentialGradedCategory R DGModB] [DifferentialGradedCategory R DGModA]
variable (QisB : MorphismProperty (K R DGModB)) [IsSaturatedMultiplicativeSystem QisB]
variable (QisA : MorphismProperty (K R DGModA))
variable (homOverBFromN : DgFunctor R DGModB DGModA)
variable (I : ObjectProperty (K R DGModB))

local notation "homToDerived" => (homOverBFromN.mapK ⋙ QisA.Q)

-- Semantic recall hits:
-- `CategoryTheory.Functor.totalRightDerived`,
-- `CategoryTheory.Functor.HasRightDerivedFunctor`,
-- `CategoryTheory.Functor.hasPointwiseRightDerivedFunctor_of_subset`.
-- Local Chapter 22 precedent represents the underived internal-Hom functor by
-- `homOverBFromN.mapK`; the target derived category is represented as the localization
-- `QisA.Localization`.

/-- The Chapter `13` subset criterion applied to `homOverBFromN.mapK ⋙ QisA.Q`, producing
pointwise right-derived functors from good replacements in `I`. -/
theorem homOverBFromNOnHomotopyCategory_hasPointwiseRightDerivedFunctor
    (hI_reaches :
      ∀ X : K R DGModB, ∃ (X' : K R DGModB) (s : X ⟶ X'), I X' ∧ QisB s)
    (hI_inverts :
      ∀ {X X' : K R DGModB} (s : X ⟶ X'),
        I X → I X' → QisB s →
          IsIso ((homOverBFromN.mapK ⋙ QisA.Q).map s)) :
    Functor.HasPointwiseRightDerivedFunctor homToDerived QisB :=
  Functor.hasPointwiseRightDerivedFunctor_of_subset homToDerived QisB I hI_reaches hI_inverts

/-- Lemma 22.31.2: for the internal-Hom DG functor attached to a differential graded
`(A, B)`-bimodule `N`, assume the source quasi-isomorphisms in `K(Mod_(B,d))` satisfy the
property-`(I)` criterion from Lemma `13.14.15`: every object maps by a quasi-isomorphism to an
object of `I`, and quasi-isomorphisms between objects of `I` are inverted after applying
`Hom(N, -)` and localizing the target. Then the right derived functor exists. In Stacks notation
this is the functor
`RHom(N, -) : D(B, d) ⥤ D(A, d)`. -/
@[stacks 09LI]
theorem homOverBFromNOnHomotopyCategory_hasRightDerivedFunctor
    (hI_reaches :
      ∀ X : K R DGModB, ∃ (X' : K R DGModB) (s : X ⟶ X'), I X' ∧ QisB s)
    (hI_inverts :
      ∀ {X X' : K R DGModB} (s : X ⟶ X'),
        I X → I X' → QisB s →
          IsIso ((homOverBFromN.mapK ⋙ QisA.Q).map s)) :
    Functor.HasRightDerivedFunctor homToDerived QisB := by
  let _ : Functor.HasPointwiseRightDerivedFunctor homToDerived QisB :=
    homOverBFromNOnHomotopyCategory_hasPointwiseRightDerivedFunctor
      QisB QisA homOverBFromN I hI_reaches hI_inverts
  infer_instance

/- Source notation: under any ambient instance
`[(homOverBFromN.mapK ⋙ QisA.Q).HasRightDerivedFunctor QisB]`, the right-derived internal-Hom
functor is the canonical total right derived functor below. -/
section Notation

open scoped DifferentialGradedCategory

variable [IsSaturatedMultiplicativeSystem QisA]
variable [(homOverBFromN.mapK ⋙ QisA.Q).HasRightDerivedFunctor QisB]

#check (RHom[QisB, QisA](homOverBFromN) : QisB.Localization ⥤ QisA.Localization)

end Notation

end
