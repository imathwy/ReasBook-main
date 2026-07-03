import Mathlib
import StacksProject_2024.Chap15.Lemma_15_116_4

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

universe u v w

section

variable {A : Type u} {B : Type v} {K : Type w} {L : Type (max u v w)}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra B L] [Algebra K L] [IsFractionRing B L]
variable [IsScalarTower A B L] [IsScalarTower A K L]

-- Proof sketch: if `ResidueField A` has characteristic `0`, the hypothesis is vacuous and one
-- applies the prime-to-residue-characteristic case handled earlier in the chapter. In positive
-- characteristic, use Lemma `15.116.5` to pass to separably closed residue fields, then the
-- completion and Cohen-structure reductions from the textbook proof reduce the problem to
-- Lemma `15.116.17`, which yields the required finite weak solution.
/-- Theorem 15.116.18 (Epp): let `A ⊆ B` be an extension of discrete valuation rings with
fraction field `K` of `A`. Assume that whenever `ResidueField A` has positive characteristic,
every element of the stable intersection of the `p^n`-power subsets of `ResidueField B` is
separable algebraic over `ResidueField A`, where `p = ringChar (ResidueField A)`. Then there
exists a finite extension `K₁ / K` which is a weak solution for `A → B`. -/
theorem exists_finite_extension_weakSolution_of_epp_hypothesis
    (hsep :
      ringChar (ResidueField A) ≠ 0 →
        ∀ x : ResidueField B,
          x ∈ ⋂ n : ℕ+, Set.range
            (fun y : ResidueField B ↦ y ^ (ringChar (ResidueField A) ^ (n : ℕ))) →
            IsAlgebraic (ResidueField A) x ∧ IsSeparable (ResidueField A) x) :
    ∃ (K1 : Type (max u v w)) (_ : Field K1) (_ : Algebra A K1) (_ : Algebra K K1)
      (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1),
      IsWeakSolutionFor A B K L K1 := sorry

end
