import Mathlib
import StacksProject_2024.Chap31.Lemma_31_23_6
import StacksProject_2024.Chap31.Lemma_31_5_12

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory Opposite TopologicalSpace
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry nonZeroDivisors

noncomputable section

universe u

namespace AlgebraicGeometry

variable (X : Scheme.{u}) [IsReduced X]

local notation "JX" => Opens.grothendieckTopology X.toTopCat
local notation "ModX" => ringedSiteModuleCategory JX X.toLocallyRingedSpace.𝒪
local notation "MerModX" =>
  ringedSiteModuleCategory JX X.toLocallyRingedSpace.meromorphicFunctionSheaf
local notation "KX" => X.toLocallyRingedSpace.meromorphicFunctionSheaf

/- Semantic recall: `lean_leansearch` surfaced only analytic meromorphic-function owners, while
the local Chapter 31 source-facing owners are `LocallyRingedSpace.meromorphicFunctionSheaf`,
`LocallyRingedSpace.meromorphicSectionSheaf`, and the generic-point product statement from
Lemma 31.23.6. The Stacks tag evidence is consistent: item tag `02OW` matches
`https://stacks.math.columbia.edu/tag/02OW`. -/

/-- The canonical residue-field point map `j_η : Spec(κ(η)) -> X` attached to a generic point of
an irreducible component. -/
abbrev genericPointResidueFieldMap (η : genericIrreducibleComponentPoints X) :
    Spec (X.residueField η.1) ⟶ X :=
  X.fromSpecResidueField η.1

/-- The sheaf `j_{η,*} κ(η)` on `X`. -/
abbrev genericPointResidueFieldPushforwardSheaf
    (η : genericIrreducibleComponentPoints X) :
    TopCat.Sheaf CommRingCat X.toTopCat :=
  (TopCat.Sheaf.pushforward CommRingCat (genericPointResidueFieldMap X η).base).obj
    (Spec (X.residueField η.1)).sheaf

/-- The product sheaf `∏_η j_{η,*} κ(η)` over the generic points of irreducible components. -/
abbrev genericPointResidueFieldPushforwardProductSheaf :
    TopCat.Sheaf CommRingCat X.toTopCat :=
  ∏ᶜ fun η : genericIrreducibleComponentPoints X ↦
    genericPointResidueFieldPushforwardSheaf X η

/-- Lemma 31.25.1 (1): for a reduced scheme whose quasi-compact opens have finitely many
irreducible components, the sheaf of meromorphic functions is the product of the pushforwards from
the generic points of the irreducible components. This records
`𝒦_X = ⨁_{η ∈ X⁰} j_{η,*}κ(η) = ∏_{η ∈ X⁰} j_{η,*}κ(η)`. -/
@[stacks 02OW]
theorem reduced_meromorphicFunctionSheaf_iso_genericPointResidueFieldPushforwardProduct
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X] :
    Nonempty (KX ≅ genericPointResidueFieldPushforwardProductSheaf X) := sorry

/-- Lemma 31.25.1 (2): under the same reduced and finite-component hypotheses, the sheaf
`𝒦_X` is quasi-coherent as an `𝒪_X`-algebra, recorded on the underlying `𝒪_X`-module obtained by
restriction of scalars from `𝒦_X`. -/
@[stacks 02OW]
theorem reduced_meromorphicFunctionSheaf_isQuasicoherent
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X] :
    ((restrictionAlong
      (X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom)).obj
        (SheafOfModules.unit (ringSheaf JX KX) : MerModX)).IsQuasicoherent := sorry

/-- Lemma 31.25.1 (3): if `𝒜F` is a quasi-coherent `𝒪_X`-module, then the sheaf of meromorphic
sections `𝒦_X(𝒜F)` is quasi-coherent. The displayed direct-sum/product formula is represented by
the existing owner `X.toLocallyRingedSpace.meromorphicSectionSheaf 𝒜F`. -/
@[stacks 02OW]
theorem reduced_meromorphicSectionSheaf_isQuasicoherent
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
    (𝒜F : ModX) [𝒜F.IsQuasicoherent] :
    ((restrictionAlong
      (X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom)).obj
        (X.toLocallyRingedSpace.meromorphicSectionSheaf 𝒜F)).IsQuasicoherent := sorry

/-- Lemma 31.25.1 (4): at every point `x`, the denominator system `𝒮_x` is the set of
nonzerodivisors in the local ring `𝒪_{X,x}`. -/
@[stacks 02OW]
theorem reduced_meromorphicDenominatorStalk_eq_nonZeroDivisors
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X] (x : X) :
    meromorphicDenominatorStalk X x = nonZeroDivisors (X.presheaf.stalk x) := sorry

/-- Lemma 31.25.1 (5): at every point `x`, the meromorphic stalk `𝒦_{X,x}` is the total quotient
ring of the local ring `𝒪_{X,x}`. -/
@[stacks 02OW]
theorem reduced_meromorphicStalk_isLocalization
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X] (x : X) :
    IsLocalization (nonZeroDivisors (X.presheaf.stalk x)) ((KX).presheaf.stalk x) := sorry

/-- Lemma 31.25.1 (6): on an affine open `U`, meromorphic functions over `U` are the total
quotient ring of the affine coordinate ring `𝒪_X(U)`. -/
@[stacks 02OW]
theorem reduced_meromorphicSections_isLocalization_of_isAffineOpen
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
    (U : X.Opens) (hU : IsAffineOpen U) :
    IsLocalization (nonZeroDivisors Γ(X, U)) ((KX).presheaf.obj (op U)) := sorry

/-- Lemma 31.25.1 (7): the ring of rational functions of `X` is the ring of global meromorphic
functions, in formula form `R(X) = Γ(X, 𝒦_X)`. -/
@[stacks 02OW]
theorem reduced_rationalFunctionRing_iso_meromorphicFunctions
    (X : Scheme) [IsReduced X]
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X] :
    Nonempty (X.rationalFunctionRing ≅ X.toLocallyRingedSpace.meromorphicFunctions) := sorry

end AlgebraicGeometry
