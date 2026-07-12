import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.CentralizerPPartDivisibilityInfraFinal
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.PrimeToPRootLift

/-!
Unit denominator lemmas for Serre `18.5(a)`.

The prime-to-`p` factor `ordCompl[p] |C_G(s)|` of a centralizer order is a unit in the
coefficient DVR.  Hence a fraction-field coefficient with denominator `|C_G(s)|` has only the
centralizer `p`-part as a genuine divisibility obstruction after the coefficient is known to come
from `A`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section CentralizerUnitDenominatorWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local instance centralizerUnitDenominatorWorkerFintypeG : Fintype G :=
  Fintype.ofFinite G

/-- The prime-to-`p` centralizer factor, packaged as a unit of the DVR `A`. -/
noncomputable def centralizerPrimeToPUnit
    (c : PRegularConjClass G p) : Aˣ :=
  (ordCompl_centralizerCard_isUnit (p := p) (A := A) (G := G) c).unit

/-- The chosen unit has value `ordCompl[p] |C_G(c)|`. -/
@[simp] theorem centralizerPrimeToPUnit_val
    (c : PRegularConjClass G p) :
    ((centralizerPrimeToPUnit (p := p) (A := A) (G := G) c : Aˣ) : A) =
      (ordCompl[p] (ConjClasses.centralizerCard c.1) : A) := by
  exact
    IsUnit.unit_spec
      (ordCompl_centralizerCard_isUnit (p := p) (A := A) (G := G) c)

/-- The inverse of the prime-to-`p` centralizer factor is represented by an element of `A`. -/
theorem centralizerPrimeToPUnit_inv_mul_ordCompl
    (c : PRegularConjClass G p) :
    (((centralizerPrimeToPUnit (p := p) (A := A) (G := G) c)⁻¹ : Aˣ) : A) *
        (ordCompl[p] (ConjClasses.centralizerCard c.1) : A) =
      1 := by
  rw [← centralizerPrimeToPUnit_val (p := p) (A := A) (G := G) c]
  exact Units.inv_mul (centralizerPrimeToPUnit (p := p) (A := A) (G := G) c)

/-- Same unit inverse identity after mapping to the fraction field. -/
theorem algebraMap_centralizerPrimeToPUnit_inv_mul_ordCompl
    (c : PRegularConjClass G p) :
    algebraMap A K
        (((centralizerPrimeToPUnit (p := p) (A := A) (G := G) c)⁻¹ : Aˣ) : A) *
        algebraMap A K (ordCompl[p] (ConjClasses.centralizerCard c.1) : A) =
      1 := by
  simpa [map_mul] using
    congrArg (algebraMap A K)
      (centralizerPrimeToPUnit_inv_mul_ordCompl (p := p) (A := A) (G := G) c)

/-- In `A`, the full centralizer order is the centralizer `p`-part times a unit. -/
theorem centralizerCard_natCast_eq_centralizerPPart_mul_primeToPUnit
    (c : PRegularConjClass G p) :
    (ConjClasses.centralizerCard c.1 : A) =
      (ConjClasses.centralizerPPart p c.1 : A) *
        ((centralizerPrimeToPUnit (p := p) (A := A) (G := G) c : Aˣ) : A) := by
  have hcard :
      ConjClasses.centralizerCard c.1 =
        ConjClasses.centralizerPPart p c.1 *
          ordCompl[p] (ConjClasses.centralizerCard c.1) :=
    ConjClasses.centralizerCard_eq_centralizerPPart_mul_ordCompl
      (p := p) (G := G) c.1
  simpa [Nat.cast_mul, centralizerPrimeToPUnit_val (p := p) (A := A) (G := G) c] using
    congrArg (fun n : ℕ => (n : A)) hcard

/-- The centralizer order has nonzero image in the characteristic-zero fraction field. -/
theorem algebraMap_centralizerCard_ne_zero
    (c : PRegularConjClass G p) :
    algebraMap A K (ConjClasses.centralizerCard c.1 : A) ≠ 0 := by
  have hpos : 0 < ConjClasses.centralizerCard c.1 := by
    dsimp [ConjClasses.centralizerCard]
    exact
      Finite.card_pos
        (α := Subgroup.centralizer
          ({Classical.choose (ConjClasses.mk_surjective c.1)} : Set G))
  have hneK : ((ConjClasses.centralizerCard c.1 : ℕ) : K) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hpos
  simpa using hneK

/-- In the reciprocal of `|C_G(c)|`, the prime-to-`p` denominator is an `A`-unit; the only
non-unit denominator displayed in `K` is the centralizer `p`-part. -/
theorem centralizerCard_inv_eq_primeToPUnit_inv_mul_centralizerPPart_inv
    (c : PRegularConjClass G p) :
    (algebraMap A K (ConjClasses.centralizerCard c.1 : A))⁻¹ =
      algebraMap A K
          (((centralizerPrimeToPUnit (p := p) (A := A) (G := G) c)⁻¹ : Aˣ) : A) *
        (algebraMap A K (ConjClasses.centralizerPPart p c.1 : A))⁻¹ := by
  let zK : K := algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)
  let uA : Aˣ := centralizerPrimeToPUnit (p := p) (A := A) (G := G) c
  let uK : K := algebraMap A K ((uA : Aˣ) : A)
  have hcard :
      algebraMap A K (ConjClasses.centralizerCard c.1 : A) = zK * uK := by
    calc
      algebraMap A K (ConjClasses.centralizerCard c.1 : A) =
          algebraMap A K
            ((ConjClasses.centralizerPPart p c.1 : A) *
              ((centralizerPrimeToPUnit (p := p) (A := A) (G := G) c : Aˣ) : A)) := by
            rw [centralizerCard_natCast_eq_centralizerPPart_mul_primeToPUnit
              (p := p) (A := A) (G := G) c]
      _ = zK * uK := by
            simp [zK, uK, uA, map_mul]
  rw [hcard, mul_inv_rev]
  have hu_inv :
      uK⁻¹ =
        algebraMap A K (((centralizerPrimeToPUnit (p := p) (A := A) (G := G) c)⁻¹ : Aˣ) : A) := by
    rw [show uK = algebraMap A K ((uA : Aˣ) : A) by rfl]
    symm
    apply eq_inv_of_mul_eq_one_left
    simpa [uA, uK, map_mul] using
      algebraMap_centralizerPrimeToPUnit_inv_mul_ordCompl
        (p := p) (A := A) (K := K) (G := G) c
  rw [hu_inv]

/-- If an `A`-valued row difference equals `|C_G(c)|` times an `A`-valued pairing coefficient
in the fraction field, then the row difference is divisible by the centralizer `p`-part in `A`.
-/
theorem centralizerPPart_dvd_of_centralizerCard_mul_pairingCoefficient
    (c : PRegularConjClass G p) {rowDiff coeff : A}
    (hcoeff :
      algebraMap A K rowDiff =
        algebraMap A K (ConjClasses.centralizerCard c.1 : A) * algebraMap A K coeff) :
    (ConjClasses.centralizerPPart p c.1 : A) ∣ rowDiff := by
  refine
    ⟨((centralizerPrimeToPUnit (p := p) (A := A) (G := G) c : Aˣ) : A) * coeff, ?_⟩
  apply IsFractionRing.injective A K
  calc
    algebraMap A K rowDiff =
        algebraMap A K (ConjClasses.centralizerCard c.1 : A) * algebraMap A K coeff := hcoeff
    _ =
        algebraMap A K
            ((ConjClasses.centralizerPPart p c.1 : A) *
              ((centralizerPrimeToPUnit (p := p) (A := A) (G := G) c : Aˣ) : A)) *
          algebraMap A K coeff := by
          rw [centralizerCard_natCast_eq_centralizerPPart_mul_primeToPUnit
            (p := p) (A := A) (G := G) c]
    _ =
        algebraMap A K
          ((ConjClasses.centralizerPPart p c.1 : A) *
            (((centralizerPrimeToPUnit (p := p) (A := A) (G := G) c : Aˣ) : A) * coeff)) := by
          simp [map_mul, mul_assoc]

/-- Multiplier form of
`centralizerPPart_dvd_of_centralizerCard_mul_pairingCoefficient`. -/
theorem exists_eq_centralizerPPart_mul_of_centralizerCard_mul_pairingCoefficient
    (c : PRegularConjClass G p) {rowDiff coeff : A}
    (hcoeff :
      algebraMap A K rowDiff =
        algebraMap A K (ConjClasses.centralizerCard c.1 : A) * algebraMap A K coeff) :
    ∃ a : A, rowDiff = (ConjClasses.centralizerPPart p c.1 : A) * a :=
  centralizerPPart_dvd_of_centralizerCard_mul_pairingCoefficient
    (p := p) (A := A) (K := K) (G := G) c hcoeff

/-- Denominator form: if the fraction-field pairing coefficient
`rowDiff / |C_G(c)|` is represented by an element of `A`, then `rowDiff` is divisible by the
centralizer `p`-part in `A`. -/
theorem centralizerPPart_dvd_of_pairingCoefficient_eq_mul_centralizerCard_inv
    (c : PRegularConjClass G p) {rowDiff coeff : A}
    (hcoeff :
      algebraMap A K coeff =
        algebraMap A K rowDiff *
          (algebraMap A K (ConjClasses.centralizerCard c.1 : A))⁻¹) :
    (ConjClasses.centralizerPPart p c.1 : A) ∣ rowDiff := by
  have hcard_ne :
      algebraMap A K (ConjClasses.centralizerCard c.1 : A) ≠ 0 :=
    algebraMap_centralizerCard_ne_zero (p := p) (A := A) (K := K) (G := G) c
  apply centralizerPPart_dvd_of_centralizerCard_mul_pairingCoefficient
    (p := p) (A := A) (K := K) (G := G) c
  calc
    algebraMap A K rowDiff =
        (algebraMap A K rowDiff *
          (algebraMap A K (ConjClasses.centralizerCard c.1 : A))⁻¹) *
            algebraMap A K (ConjClasses.centralizerCard c.1 : A) := by
          rw [mul_assoc, inv_mul_cancel₀ hcard_ne, mul_one]
    _ =
        algebraMap A K coeff *
          algebraMap A K (ConjClasses.centralizerCard c.1 : A) := by
          rw [← hcoeff]
    _ =
        algebraMap A K (ConjClasses.centralizerCard c.1 : A) *
          algebraMap A K coeff := by
          rw [mul_comm]

/-- Multiplier form of the denominator cancellation lemma. -/
theorem exists_eq_centralizerPPart_mul_of_pairingCoefficient_eq_mul_centralizerCard_inv
    (c : PRegularConjClass G p) {rowDiff coeff : A}
    (hcoeff :
      algebraMap A K coeff =
        algebraMap A K rowDiff *
          (algebraMap A K (ConjClasses.centralizerCard c.1 : A))⁻¹) :
    ∃ a : A, rowDiff = (ConjClasses.centralizerPPart p c.1 : A) * a :=
  centralizerPPart_dvd_of_pairingCoefficient_eq_mul_centralizerCard_inv
    (p := p) (A := A) (K := K) (G := G) c hcoeff

end CentralizerUnitDenominatorWorker

end Representation
