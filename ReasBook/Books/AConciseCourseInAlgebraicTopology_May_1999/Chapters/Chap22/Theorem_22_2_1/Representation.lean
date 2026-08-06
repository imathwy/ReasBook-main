import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap19.Theorem_19_2_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.BasedHomotopyClasses
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap15.Problem_15_3_6

open CategoryTheory Limits
open HomotopicalAlgebra

noncomputable section

local notation "BasedSpace" => Under (⊤_ TopCat)
local notation "BasedCWComplex" =>
  CategoryTheory.ObjectProperty.FullSubcategory IsBasedCWComplex

/-- The canonical pointed-set functor underlying an additive commutative group. -/
def addCommGrpCatToPointed : AddCommGrpCat ⥤ Pointed where
  obj A := Pointed.of (0 : A)
  map f := ⟨f, map_zero f.hom⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The discrete based space with underlying additive group `π` and basepoint `0`, used as the
source-facing model for `K(π, 0)`. -/
abbrev additiveDiscreteBasedSpace (π : Type) [AddCommGroup π] : BasedSpace :=
  Under.mk
    (@TopCat.ofHom (⊤_ TopCat) π inferInstance ⊥
      (@ContinuousMap.const (⊤_ TopCat) π inferInstance ⊥ (0 : π)))

/-- A based space models `K(π, n)` in the source-facing additive notation: in degree `0` this is
the discrete based group `π`, while in positive degree it is the Chapter 22 owner
`IsEilenbergMacLaneSpace (Multiplicative π) n.succPNat`. -/
def IsAdditiveEilenbergMacLaneSpaceAtDegree
    (π : Type) [AddCommGroup π] (n : ℕ) (K : BasedSpace) : Prop :=
  match n with
  | 0 => Nonempty (K ≅ additiveDiscreteBasedSpace π)
  | m + 1 =>
      IsEilenbergMacLaneSpace (Multiplicative π) m.succPNat K.right (underTopBasepoint K)

/-- The type of a natural comparison isomorphism from degree-`n` reduced cohomology with
coefficients in `π`, named by an explicit reduced cohomology theory `theory` on a chosen
based-CW setup, to pointed homotopy classes into a based space `K`. -/
abbrev reducedCohomologyToBasedHomotopyClassesIso
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations BasedCWComplex]
    [CategoryWithWeakEquivalences BasedCWComplex]
    {setup : BasedCWReducedSuspensionCofiberSetup}
    (theory : BundledReducedCohomologyTheory setup)
    (n : ℕ) (K : BasedSpace) :=
  (((theory.cohomology (n : ℤ)) ⋙ addCommGrpCatToPointed) ≅
    BasedHomotopyClasses.onBasedCWComplexes K)

/-- A source-facing datum exhibiting degree-`n` reduced cohomology with coefficients in `π` on a
chosen based-CW setup as represented by a based space `K(π, n)`. This owner is reusable across
later Chapter 22 constructions; Theorem 22.2.1 itself is the existential statement that such a
datum exists. -/
structure ReducedCohomologyEilenbergMacLaneRepresentation
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations BasedCWComplex]
    [CategoryWithWeakEquivalences BasedCWComplex]
    (π : Type) [AddCommGroup π] (n : ℕ) where
  /-- The chosen based-CW suspension/cofiber setup used to name `H̃^*(-; π)`. -/
  setup : BasedCWReducedSuspensionCofiberSetup
  /-- The reduced cohomology theory with coefficients in `π` on the chosen setup. -/
  theory : BundledReducedCohomologyTheory setup
  /-- The chosen representing space `K(π, n)`. -/
  space : BasedSpace
  /-- The chosen representing space is an additive `K(π, n)` in the source-facing degree
  convention. -/
  isAdditiveEilenbergMacLane :
    IsAdditiveEilenbergMacLaneSpaceAtDegree π n space
  /-- The natural comparison from degree-`n` reduced cohomology with coefficients in `π` to
  pointed homotopy classes into the chosen representing space. -/
  comparison :
    reducedCohomologyToBasedHomotopyClassesIso theory n space

/-- The reduced cohomology theory carried by an explicit degree-`n` representation datum. -/
abbrev reducedCohomologyWithCoefficientsOnBasedCWComplexes
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations BasedCWComplex]
    [CategoryWithWeakEquivalences BasedCWComplex]
    {π : Type} [AddCommGroup π] {n : ℕ}
    (R : ReducedCohomologyEilenbergMacLaneRepresentation π n) :
    BundledReducedCohomologyTheory R.setup :=
  R.theory

/-- An explicit degree-`n` reduced-cohomology representation datum supplies the natural
comparison from reduced cohomology to pointed homotopy classes into its chosen `K(π, n)`. -/
abbrev reducedCohomology_isRepresentedByAdditiveEilenbergMacLaneSpace
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations BasedCWComplex]
    [CategoryWithWeakEquivalences BasedCWComplex]
    {π : Type} [AddCommGroup π] {n : ℕ}
    (R : ReducedCohomologyEilenbergMacLaneRepresentation π n) :
    reducedCohomologyToBasedHomotopyClassesIso R.theory n R.space :=
  R.comparison

namespace ReducedCohomologyEilenbergMacLaneRepresentation

/-- The representing space carried by an explicit degree-`n` reduced-cohomology representation
datum is an additive `K(π, n)` in the source-facing degree convention. -/
theorem isAdditiveEilenbergMacLaneSpaceAtDegree
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations BasedCWComplex]
    [CategoryWithWeakEquivalences BasedCWComplex]
    {π : Type} [AddCommGroup π] {n : ℕ}
    (R : ReducedCohomologyEilenbergMacLaneRepresentation π n) :
    IsAdditiveEilenbergMacLaneSpaceAtDegree π n R.space :=
  R.isAdditiveEilenbergMacLane

end ReducedCohomologyEilenbergMacLaneRepresentation
