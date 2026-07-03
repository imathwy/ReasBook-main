import Mathlib
import StacksProject_2024.Chap15.Definition_15_112_1
import StacksProject_2024.Chap15.Definition_15_112_7

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open IsExtensionOfDiscreteValuationRings
open scoped IntermediateField

universe u v

section

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {L : Type v} [Field L] [Algebra A L] [Algebra (FractionRing A) L]
variable [IsScalarTower A (FractionRing A) L]
variable {p : ℕ} [Fact p.Prime] [CharP (FractionRing A) p]
variable {ξ : FractionRing A}

local notation "K" => FractionRing A
local notation "κA" => ResidueField A
local notation "B" => integralClosure A L

/- Domain-style sampling:
* primary domain: ramification theory for Artin-Schreier extensions of the fraction field of a
  discrete valuation ring in characteristic `p`;
* sampled owner declarations:
  `IntermediateField.adjoin_simple_eq_top_iff_of_isAlgebraic`,
  `IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic`,
  `IntermediateField.isSeparable_adjoin_simple_iff_isSeparable`,
  `uniformizerRootFractionPolynomial_irreducible`,
  `primitiveRootElimination_weakly_unramified_residue_case_of_uniformizer_denominator`,
  `IsUnramifiedWithRespectTo`,
  `IsTotallyRamifiedWithRespectTo`,
  `WeaklyUnramified`,
  `residueDegree`,
  `residue`;
* best owner abstraction: the chapter ramification owners on `L / FractionRing A` and on the
  induced extension `A ⊆ integralClosure A L`, with the simple intermediate field `K⟮z⟯` as the
  canonical source-facing owner for the Artin-Schreier generator data;
* primitive data: a root `z` of `X ^ p - X - ξ` together with the owner-level generator condition
  `K⟮z⟯ = ⊤`, plus the denominator data `ξ = a / π^n`;
* derived API: the Galois and ramification alternatives, and in the `p ∣ n` branch the single
  existential weakly-unramified residue-field case, along with the finite-dimensionality and
  separability companion lemmas derived from the simple-generator owner.

Layer triage:
* `source-facing`: the Artin-Schreier extension statements in this file;
* `core/canonical`: `IsUnramifiedWithRespectTo`, `IsTotallyRamifiedWithRespectTo`,
  `WeaklyUnramified`, and `residue A`;
* `bridge/view`: the bridge back to `Algebra.adjoin K ({z} : Set L) = ⊤` when an implementation
  needs the subalgebra form, together with the local-extension and residue-field instances for
  `integralClosure A L`.
-/

private theorem finiteDimensional_of_artinSchreier_generator
    (z : L) (hz : z ^ p - z = algebraMap K L ξ)
    (hgen : K⟮z⟯ = ⊤) :
    FiniteDimensional K L := by
  sorry

private theorem isSeparable_of_artinSchreier_generator
    (z : L) (hz : z ^ p - z = algebraMap K L ξ)
    (hgen : K⟮z⟯ = ⊤) :
    Algebra.IsSeparable K L := by
  sorry

private theorem finiteDimensional_residueField_of_integralClosure
    [FiniteDimensional K L]
    [IsDiscreteValuationRing B] :
    FiniteDimensional κA (ResidueField B) := by
  sorry

section ArtinSchreierGenerator

variable (z : L) (hz : z ^ p - z = algebraMap K L ξ)
variable (hgen : K⟮z⟯ = ⊤)

local instance : FiniteDimensional K L :=
  finiteDimensional_of_artinSchreier_generator z hz hgen

local instance : Algebra.IsSeparable K L :=
  isSeparable_of_artinSchreier_generator z hz hgen

local instance [IsDiscreteValuationRing B] :
    FiniteDimensional κA (ResidueField B) :=
  finiteDimensional_residueField_of_integralClosure

-- Proof sketch: the polynomial `X ^ p - X - ξ` has derivative `-1`, so adjoining a root gives a
-- separable extension of degree dividing `p`; in characteristic `p` this is the Artin-Schreier
-- situation, hence the extension is Galois. The ramification alternatives come from the
-- classification of Artin-Schreier extensions over a discrete valuation ring, with the trivial
-- case recorded by `Module.finrank K L = 1` because the extension field is an arbitrary `K`-algebra
-- rather than literally the same type as `K`.
/-- Lemma 15.116.11: let `A` be a discrete valuation ring with fraction field `K = FractionRing A`
of characteristic `p > 0`, let `ξ : K`, and let `L` be obtained by adjoining to `K` a root `z`
of `z ^ p - z = ξ`. Then `L / K` is Galois and one of the following happens: the extension is
trivial, recorded as `Module.finrank K L = 1`; the extension is unramified of degree `p`; the
extension is totally ramified of degree `p`; or `B = integralClosure A L` is a discrete valuation
ring such that `A ⊆ B` is weakly unramified and the induced residue-field extension
`ResidueField B / ResidueField A` is purely inseparable of degree `p`. -/
theorem artin_schreier_extension_galois_and_has_ramification_case
    (z : L) (hz : z ^ p - z = algebraMap K L ξ)
    (hgen : K⟮z⟯ = ⊤)
    :
    IsGalois K L ∧
      (Module.finrank K L = 1 ∨
        (Module.finrank K L = p ∧ IsUnramifiedWithRespectTo A L) ∨
        (Module.finrank K L = p ∧ IsTotallyRamifiedWithRespectTo A L) ∨
        ∃ (_ : IsDiscreteValuationRing B),
          WeaklyUnramified A B ∧
            IsPurelyInseparable κA (ResidueField B) ∧
            residueDegree A B = p) := sorry

-- Proof sketch: if `ξ` comes from `A`, then the Artin-Schreier polynomial defines a finite étale
-- `A`-algebra. Over a discrete valuation ring this forces either the trivial case or the
-- unramified degree-`p` case.
/-- If `ξ` lies in the discrete valuation ring `A`, then the associated Artin-Schreier extension is
either trivial or unramified of degree `p`. -/
theorem artin_schreier_eq_or_unramified_of_mem_ring
    (z : L) (hz : z ^ p - z = algebraMap K L ξ)
    (hgen : K⟮z⟯ = ⊤)
    (hξ : ∃ a : A, algebraMap A K a = ξ) :
    Module.finrank K L = 1 ∨ (Module.finrank K L = p ∧ IsUnramifiedWithRespectTo A L) := sorry

-- Proof sketch: write the chosen root `z` in a localization of the integral closure of `A` and
-- compare valuations in the equation `z ^ p - z = ξ`. When the pole order `n` of `ξ` is positive
-- and not divisible by `p`, the valuation computation shows that the ramification index is
-- divisible by `p`; since the degree is at most `p`, the integral closure must be a discrete
-- valuation ring and the extension is totally ramified with ramification index `p`.
/-- If `ξ = π^{-n} a` with `n > 0`, `p ∤ n`, and `a` a unit of `A`, then the associated
Artin-Schreier extension is in the totally ramified case with ramification index `p`. -/
theorem artin_schreier_totally_ramified_of_uniformizer_denominator
    (z : L) (hz : z ^ p - z = algebraMap K L ξ)
    (hgen : K⟮z⟯ = ⊤)
    (π : A) (hπ : maximalIdeal A = Ideal.span ({π} : Set A))
    {n : ℕ} (hn : 0 < n) (hndiv : ¬ p ∣ n) (a : Aˣ)
    (hξ : ξ = algebraMap A K (a : A) / (algebraMap A K π) ^ n) :
    Module.finrank K L = p ∧ IsTotallyRamifiedWithRespectTo A L := sorry

-- Proof sketch: after multiplying the Artin-Schreier equation by the `p`th power of a
-- uniformizer, rewrite it in integral form over `A`. The resulting integral closure is weakly
-- unramified over `A`, and the assumption that the residue of `a` is not a `p`th power forces the
-- residue-field extension to be purely inseparable of degree `p`.
/-- If `ξ = π^{-n} a` with `n > 0`, `p ∣ n`, and the residue class of the unit `a` is not a `p`th
power in `ResidueField A`, then `B = integralClosure A L` is a discrete valuation ring such that
`A ⊆ B` is weakly unramified and the residue-field extension `ResidueField B / ResidueField A` is
purely inseparable of degree `p`. -/
theorem artin_schreier_weakly_unramified_residue_case_of_uniformizer_denominator
    (z : L) (hz : z ^ p - z = algebraMap K L ξ)
    (hgen : K⟮z⟯ = ⊤)
    (π : A) (hπ : maximalIdeal A = Ideal.span ({π} : Set A))
    {n : ℕ} (hn : 0 < n) (hdiv : p ∣ n) (a : Aˣ)
    (ha : ¬ ∃ b : κA, b ^ p = residue A (a : A))
    (hξ : ξ = algebraMap A K (a : A) / (algebraMap A K π) ^ n) :
    ∃ (_ : IsDiscreteValuationRing B),
      WeaklyUnramified A B ∧
        IsPurelyInseparable κA (ResidueField B) ∧
        residueDegree A B = p := sorry

end ArtinSchreierGenerator

end
