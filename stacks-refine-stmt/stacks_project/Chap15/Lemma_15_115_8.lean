import Mathlib
import stacks_project.Chap15.Definition_15_112_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

section

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {L : Type v} [Field L] [Algebra A L] [Algebra (FractionRing A) L]
variable [IsScalarTower A (FractionRing A) L]
variable [FiniteDimensional (FractionRing A) L]
variable [Algebra.IsSeparable (FractionRing A) L]

-- Proof sketch: apply the uniformizer-root criterion for tame ramification to replace `L` by an
-- extension unramified over a radical extension `K[π^(1/e)] / FractionRing A`, take the normal
-- closure over `FractionRing A`, and use the unramified Galois closure result together with the
-- stability of tame ramification under the intermediate and tower steps.
/-- Lemma 15.115.8 (1): if `L / FractionRing A` is a finite separable extension tamely ramified
with respect to the discrete valuation ring `A`, then `L` is contained in a finite Galois
extension of `FractionRing A` that is still tamely ramified with respect to `A`. -/
theorem exists_isGalois_tamelyRamifiedWithRespectTo
    (hL : IsTamelyRamifiedWithRespectTo A L) :
    ∃ (M : Type w) (_ : Field M) (_ : Algebra A M) (_ : Algebra (FractionRing A) M)
      (_ : Algebra L M) (_ : IsScalarTower A (FractionRing A) M)
      (_ : IsScalarTower (FractionRing A) L M)
      (_ : FiniteDimensional (FractionRing A) M)
      (_ : Algebra.IsSeparable (FractionRing A) M),
      IsGalois (FractionRing A) M ∧ IsTamelyRamifiedWithRespectTo A M := sorry

section

variable {L₁ : Type v} [Field L₁] [Algebra A L₁] [Algebra (FractionRing A) L₁]
variable [IsScalarTower A (FractionRing A) L₁]
variable [FiniteDimensional (FractionRing A) L₁]
variable [Algebra.IsSeparable (FractionRing A) L₁]
variable {L₂ : Type w} [Field L₂] [Algebra A L₂] [Algebra (FractionRing A) L₂]
variable [IsScalarTower A (FractionRing A) L₂]
variable [FiniteDimensional (FractionRing A) L₂]
variable [Algebra.IsSeparable (FractionRing A) L₂]

-- Proof sketch: use the uniformizer-root criterion for both `L₁` and `L₂` with a common
-- prime-to-residue-characteristic radical extension of `FractionRing A`, take a common unramified
-- overfield there via the corresponding unramified existence theorem, and then descend tameness
-- back to `FractionRing A`.
/-- Lemma 15.115.8 (2): if `L₁ / FractionRing A` and `L₂ / FractionRing A` are finite separable
extensions tamely ramified with respect to the discrete valuation ring `A`, then they are both
contained in a finite separable extension of `FractionRing A` that is still tamely ramified with
respect to `A`. -/
theorem exists_common_tamelyRamifiedWithRespectTo_extension
    (hL₁ : IsTamelyRamifiedWithRespectTo A L₁)
    (hL₂ : IsTamelyRamifiedWithRespectTo A L₂) :
    ∃ (L : Type x) (_ : Field L) (_ : Algebra A L) (_ : Algebra (FractionRing A) L)
      (_ : Algebra L₁ L) (_ : Algebra L₂ L) (_ : IsScalarTower A (FractionRing A) L)
      (_ : IsScalarTower (FractionRing A) L₁ L)
      (_ : IsScalarTower (FractionRing A) L₂ L)
      (_ : FiniteDimensional (FractionRing A) L) (_ : Algebra.IsSeparable (FractionRing A) L),
      IsTamelyRamifiedWithRespectTo A L := sorry

end

end
