import Mathlib
import StacksProject_2024.Chap15.Definition_15_112_1
import StacksProject_2024.Chap15.Definition_15_112_7
import StacksProject_2024.Chap15.Lemma_15_116_13

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial IsLocalRing
open IsExtensionOfDiscreteValuationRings
open scoped IntermediateField

universe u v

section

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {p : ℕ} [Fact p.Prime] [MixedCharZero A p] {ζ : A}
variable {P : A[X]}
variable {L : Type v} [Field L] [Algebra A L] [Algebra (FractionRing A) L]
variable [IsScalarTower A (FractionRing A) L]
variable {ξ : FractionRing A}

local notation "K" => FractionRing A
local notation "B" => integralClosure A L
local notation "κA" => ResidueField A

/- Domain-style sampling:
* primary domain: ramification theory for finite Kummer-type extensions of the fraction field of a
  mixed-characteristic discrete valuation ring;
* sampled owner declarations:
  `IsAlgebraic`,
  `IntermediateField.adjoin.finiteDimensional`,
  `finiteDimensional_residueField_of_finiteDimensional_fractionField_extension`,
  `IsUnramifiedWithRespectTo`,
  `IsTotallyRamifiedWithRespectTo`,
  `WeaklyUnramified`,
  `residueDegree`;
* best owner abstraction: the chapter ramification owners on `L / FractionRing A` and on the
  induced extension `A ⊆ integralClosure A L`, with the Kummer root hypotheses kept as the
  source-facing primitive data;
* primitive data: the quotient-polynomial owner `IsOneSubZetaQuotientPolynomial` and the
  root-generation hypothesis for `P(z) = ξ`;
* derived API: the Galois conclusion, the unramified and totally ramified degree-`p`
  alternatives, and the weakly unramified purely inseparable residue-field alternative.

Layer triage:
* `source-facing`: the Kummer extension statements in this file;
* `core/canonical`: `IsUnramifiedWithRespectTo`, `IsTotallyRamifiedWithRespectTo`, and
  `WeaklyUnramified`;
* `bridge/view`: the separability and local-extension instances derived from the Galois conclusion
  and the integral-closure setup.
-/

private theorem isAlgebraic_of_primitiveRootElimination_generator
    (hP : IsOneSubZetaQuotientPolynomial p ζ P)
    (z : L)
    (hz : aeval z (P.map (algebraMap A K)) = algebraMap K L ξ) :
    IsAlgebraic K z := by
  sorry

private theorem finiteDimensional_of_primitiveRootElimination_generator
    (hP : IsOneSubZetaQuotientPolynomial p ζ P)
    (z : L)
    (hz : aeval z (P.map (algebraMap A K)) = algebraMap K L ξ)
    (hgen : K⟮z⟯ = ⊤) :
    FiniteDimensional K L := by
  sorry

private theorem finiteDimensional_residueField_of_integralClosure
    [FiniteDimensional K L]
    [IsDiscreteValuationRing B] :
    FiniteDimensional κA (ResidueField B) := by
  sorry

section PrimitiveRootEliminationGenerator

variable (hζ : IsPrimitiveRoot ζ p)
variable (hP : IsOneSubZetaQuotientPolynomial p ζ P)
variable (z : L)
variable (hz : aeval z (P.map (algebraMap A K)) = algebraMap K L ξ)
variable (hgen : K⟮z⟯ = ⊤)

-- Proof sketch: use Lemma `15.116.13` to convert the equation `P(z) = ξ` into a Kummer equation
-- `y ^ p = w ^ p * (1 + ξ)` over `K = FractionRing A`, where `K` already contains a primitive
-- `p`th root of unity `ζ`. Kummer theory shows that adjoining a root produces a finite normal
-- separable extension, hence a Galois extension.
/-- Lemma 15.116.14 (1): let `A` be a mixed-characteristic discrete valuation ring containing a
primitive `p`th root of unity `ζ`, let `P ∈ A[X]` be a polynomial satisfying the conclusion of
Lemma `15.116.13`, let `ξ : K = FractionRing A`, and let `L` be generated over `K` by a root `z`
of `P(z) = ξ`. Then `L / K` is Galois. -/
theorem primitiveRootElimination_extension_isGalois
    (hζ : IsPrimitiveRoot ζ p)
    (hP : IsOneSubZetaQuotientPolynomial p ζ P)
    (z : L)
    (hz : aeval z (P.map (algebraMap A K)) = algebraMap K L ξ)
    (hgen : K⟮z⟯ = ⊤) :
    IsGalois K L := sorry

local instance : FiniteDimensional K L := by
  sorry

local instance : Algebra.IsSeparable K L :=
  by
    sorry

local instance : Algebra.EssFiniteType A B := by
  sorry

local instance [IsDiscreteValuationRing B] :
    FiniteDimensional κA (ResidueField B) := by
  sorry

-- Proof sketch: use the same Kummer-theoretic reduction as in part (1). The classification of
-- degree-`p` Kummer extensions over a mixed-characteristic discrete valuation ring yields the
-- four mutually exclusive possibilities recorded below.
/-- Lemma 15.116.14 (2): in the situation of part (1), either the extension is trivial, or it is
unramified of degree `p`, or it is totally ramified of degree `p`, or the integral closure of `A`
in `L` is a discrete valuation ring such that `A ⊆ integralClosure A L` is weakly unramified and
the residue-field extension is purely inseparable of degree `p`. -/
theorem primitiveRootElimination_has_ramification_case
    :
    Module.finrank K L = 1 ∨
      (Module.finrank K L = p ∧ IsUnramifiedWithRespectTo A L) ∨
      (Module.finrank K L = p ∧ IsTotallyRamifiedWithRespectTo A L) ∨
      ∃ (_ : IsDiscreteValuationRing B),
        WeaklyUnramified A B ∧
          IsPurelyInseparable κA (ResidueField B) ∧
          residueDegree A B = p := sorry

-- Proof sketch: when `ξ` lies in `A`, the transformed Kummer equation is defined by a unit on the
-- right-hand side, so the corresponding degree-`p` algebra over `A` is finite étale. Over a
-- discrete valuation ring, this leaves only the trivial case or the unramified degree-`p` case.
/-- If `ξ` lies in `A`, then the extension defined by adjoining a root of `P(z) = ξ` is either
trivial or unramified of degree `p`. -/
theorem primitiveRootElimination_eq_or_unramified_of_mem_ring
    (hξ : ∃ a : A, algebraMap A K a = ξ)
    :
    Module.finrank K L = 1 ∨ (Module.finrank K L = p ∧ IsUnramifiedWithRespectTo A L) := sorry

-- Proof sketch: write the chosen root in a localization of the integral closure and compare
-- valuations in the transformed Kummer equation. If `ξ = a / π^n` with `n > 0` and `p ∤ n`, the
-- valuation of the root forces the ramification index to be divisible by `p`, hence equal to `p`
-- because the extension degree is at most `p`.
/-- If `ξ = π^{-n} a` with `n > 0`, `p ∤ n`, and `a` a unit of `A`, then the extension defined by
adjoining a root of `P(z) = ξ` is in the totally ramified degree-`p` case. -/
theorem primitiveRootElimination_totally_ramified_of_uniformizer_denominator
    (π : A) (hπ : maximalIdeal A = Ideal.span ({π} : Set A))
    {n : ℕ} (hn : 0 < n) (hndiv : ¬ p ∣ n) (a : Aˣ)
    (hξ : ξ = algebraMap A K (a : A) / (algebraMap A K π) ^ n)
    :
    Module.finrank K L = p ∧ IsTotallyRamifiedWithRespectTo A L := sorry

-- Proof sketch: after multiplying the transformed Kummer equation by `π^n` with `p ∣ n`, rewrite
-- it as an integral equation over `A`. The resulting normalization is weakly unramified over `A`,
-- and the non-`p`th-power residue of `a` forces the residue-field extension to be purely
-- inseparable of degree `p`.
/-- If `ξ = π^{-n} a` with `n > 0`, `p ∣ n`, and the residue class of the unit `a` is not a `p`th
power, then the extension defined by adjoining a root of `P(z) = ξ` is in the weakly unramified
purely inseparable residue-field case of degree `p`. -/
theorem primitiveRootElimination_weakly_unramified_residue_case_of_uniformizer_denominator
    (π : A) (hπ : maximalIdeal A = Ideal.span ({π} : Set A))
    {n : ℕ} (hn : 0 < n) (hdiv : p ∣ n) (a : Aˣ)
    (ha : ¬ ∃ b : κA, b ^ p = residue A (a : A))
    (hξ : ξ = algebraMap A K (a : A) / (algebraMap A K π) ^ n) :
    ∃ (_ : IsDiscreteValuationRing B),
      WeaklyUnramified A B ∧
        IsPurelyInseparable κA (ResidueField B) ∧
        residueDegree A B = p := sorry

end PrimitiveRootEliminationGenerator

end
