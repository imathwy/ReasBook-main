import Mathlib
import StacksProject_2024.stacks_project.Chap29.Definition_29_49_4
import StacksProject_2024.stacks_project.Chap29.Definition_29_50_1
import StacksProject_2024.stacks_project.Chap29.Remark_29_49_13
import StacksProject_2024.stacks_project.Chap31.Definition_31_5_1
import StacksProject_2024.stacks_project.Chap31.Definition_31_23_3

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory Opposite TopologicalSpace
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry nonZeroDivisors

noncomputable section

universe u

namespace AlgebraicGeometry

variable (X : Scheme.{u})

local notation "JX" => Opens.grothendieckTopology X.toTopCat
local notation "ModX" => ringedSiteModuleCategory JX X.toLocallyRingedSpace.𝒪
local notation "MerModX" =>
  ringedSiteModuleCategory JX X.toLocallyRingedSpace.meromorphicFunctionSheaf
local notation "KX" => X.toLocallyRingedSpace.meromorphicFunctionSheaf

/- Semantic recall: `lean_leansearch` surfaced the mathlib owner
`TopCat.Presheaf.totalQuotientPresheaf`; the local Chapter 31 owner is
`LocallyRingedSpace.meromorphicFunctionSheaf`, and `Scheme.fromSpecStalk` is the canonical
map `Spec(𝒪_{X,η}) -> X` from Schemes, Section 26.13. -/

/-- The generic points of the irreducible components of `X`, as a subtype. -/
abbrev genericIrreducibleComponentPoints : Type u :=
  {η : X // η ∈ genericPointsOfIrreducibleComponents X}

/-- The canonical map `j_η : Spec(𝒪_{X,η}) -> X` attached to a generic point of an irreducible
component. -/
abbrev genericPointStalkMap (η : genericIrreducibleComponentPoints X) :
    Spec (CommRingCat.of (X.presheaf.stalk η.1)) ⟶ X :=
  X.fromSpecStalk η.1

/-- The sheaf `j_{η,*} 𝒪_{X,η}` on `X`. -/
abbrev genericPointStalkPushforwardSheaf
    (η : genericIrreducibleComponentPoints X) :
    TopCat.Sheaf CommRingCat X.toTopCat :=
  (TopCat.Sheaf.pushforward CommRingCat (genericPointStalkMap X η).base).obj
    (Spec (CommRingCat.of (X.presheaf.stalk η.1))).sheaf

/-- The product sheaf `∏_η j_{η,*} 𝒪_{X,η}` over the generic points of irreducible components. -/
abbrev genericPointStalkPushforwardProductSheaf :
    TopCat.Sheaf CommRingCat X.toTopCat :=
  ∏ᶜ fun η : genericIrreducibleComponentPoints X ↦
    genericPointStalkPushforwardSheaf X η

/-- The denominator submonoid in the stalk used by the total-quotient construction of
meromorphic functions. -/
abbrev meromorphicDenominatorStalk (x : X) : Submonoid (X.presheaf.stalk x) :=
  nonZeroDivisors (X.presheaf.stalk x)

/-- Lemma 31.23.6 (1): under the weak-association and finite-component hypotheses, the
meromorphic-function sheaf is the product of the pushforwards from the generic points of the
irreducible components. This records the displayed identity
`𝒦_X = ⨁_{η ∈ X⁰} j_{η,*}𝒪_{X,η} = ∏_{η ∈ X⁰} j_{η,*}𝒪_{X,η}` at the sheaf-of-rings level. -/
@[stacks 0EMF]
theorem meromorphicFunctionSheaf_iso_genericPointStalkPushforwardProduct
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak :
      ∀ x : X, x ∈ X.weakAss → x ∈ genericPointsOfIrreducibleComponents X) :
    Nonempty (KX ≅ genericPointStalkPushforwardProductSheaf X) := sorry

/-- Lemma 31.23.6 (2): with the same hypotheses, the sheaf of meromorphic functions is
quasi-coherent as an `𝒪_X`-algebra, recorded on the underlying `𝒪_X`-module obtained by
restriction of scalars from `𝒦_X`. -/
@[stacks 0EMF]
theorem meromorphicFunctionSheaf_isQuasicoherent
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak :
      ∀ x : X, x ∈ X.weakAss → x ∈ genericPointsOfIrreducibleComponents X) :
    ((restrictionAlong
      (X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom)).obj
        (SheafOfModules.unit (ringSheaf JX KX) : MerModX)).IsQuasicoherent := sorry

/-- Lemma 31.23.6 (3): for every quasi-coherent `𝒪_X`-module `ℱ`, the sheaf of meromorphic
sections `𝒦_X(ℱ)` is quasi-coherent. The displayed direct-sum/product formula is represented by
the existing owner `X.toLocallyRingedSpace.meromorphicSectionSheaf ℱ`. -/
@[stacks 0EMF]
theorem meromorphicSectionSheaf_isQuasicoherent
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak :
      ∀ x : X, x ∈ X.weakAss → x ∈ genericPointsOfIrreducibleComponents X)
    (ℱ : ModX) [ℱ.IsQuasicoherent] :
    ((restrictionAlong
      (X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom)).obj
        (X.toLocallyRingedSpace.meromorphicSectionSheaf ℱ)).IsQuasicoherent := sorry

/-- Lemma 31.23.6 (4): at every point `x`, the denominator system `𝒮_x` is the set of
nonzerodivisors in the local ring `𝒪_{X,x}`. -/
@[stacks 0EMF]
theorem meromorphicDenominatorStalk_eq_nonZeroDivisors
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak :
      ∀ x : X, x ∈ X.weakAss → x ∈ genericPointsOfIrreducibleComponents X)
    (x : X) :
    meromorphicDenominatorStalk X x = nonZeroDivisors (X.presheaf.stalk x) := sorry

/-- Lemma 31.23.6 (5): at every point `x`, the meromorphic stalk `𝒦_{X,x}` is the total quotient
ring of the local ring `𝒪_{X,x}`. -/
@[stacks 0EMF]
theorem meromorphicStalk_isLocalization
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak :
      ∀ x : X, x ∈ X.weakAss → x ∈ genericPointsOfIrreducibleComponents X)
    (x : X) :
    IsLocalization (nonZeroDivisors (X.presheaf.stalk x)) ((KX).presheaf.stalk x) := sorry

/-- Lemma 31.23.6 (6): on an affine open `U`, meromorphic functions over `U` are the total
quotient ring of the affine coordinate ring `𝒪_X(U)`. -/
@[stacks 0EMF]
theorem meromorphicSections_isLocalization_of_isAffineOpen
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak :
      ∀ x : X, x ∈ X.weakAss → x ∈ genericPointsOfIrreducibleComponents X)
    (U : X.Opens) (hU : IsAffineOpen U) :
    IsLocalization (nonZeroDivisors Γ(X, U)) ((KX).presheaf.obj (op U)) := sorry

/-- Lemma 31.23.6 (7): the ring of rational functions of `X` is the ring of global meromorphic
functions, in formula form `R(X) = Γ(X, 𝒦_X)`. -/
@[stacks 0EMF]
theorem rationalFunctionRing_iso_meromorphicFunctions
    (X : Scheme)
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak :
      ∀ x : X, x ∈ X.weakAss → x ∈ genericPointsOfIrreducibleComponents X) :
    Nonempty (X.rationalFunctionRing ≅ X.toLocallyRingedSpace.meromorphicFunctions) := sorry

end AlgebraicGeometry
