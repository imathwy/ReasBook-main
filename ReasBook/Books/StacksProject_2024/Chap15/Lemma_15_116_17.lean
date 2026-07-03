import Mathlib
import StacksProject_2024.Chap10.Definition_10_160_1
import StacksProject_2024.Chap15.Lemma_15_116_4

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open IsExtensionOfDiscreteValuationRings

universe u v w x y z

section

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [IsCompleteLocalRing B]
variable [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
variable [IsExtensionOfDiscreteValuationRings A B]
variable [IsExtensionOfDiscreteValuationRings B C]
variable [IsExtensionOfDiscreteValuationRings A C]
variable {K : Type x} {L : Type y} {M : Type z}
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra B L] [IsFractionRing B L] [Algebra K L]
variable [Field M] [Algebra C M] [IsFractionRing C M] [Algebra L M] [Algebra K M]
variable [Algebra A M] [IsScalarTower A C M] [IsScalarTower A K M]
variable [IsScalarTower K L M] [FiniteDimensional L M]
variable {p : ℕ} [Fact p.Prime] [CharP (ResidueField A) p] [IsAlgClosed (ResidueField A)]

-- Proof sketch: replace `M / L` by a finite normal closure and use Lemma `15.116.4` to reduce to
-- the normal case. Filter the resulting extension into purely inseparable degree-`p`, totally
-- ramified degree-`p`, prime-to-`p` cyclic totally ramified, and unramified steps, then induct on
-- the length of this filtration. The four basic cases are handled by Lemmas `15.116.9`,
-- `15.116.12`, `15.116.15`, and `15.116.16`, while completeness and the algebraically closed
-- residue field ensure the intermediate base changes remain in the same setup.
/-- Lemma 15.116.17: let `A ⊆ B ⊆ C` be extensions of discrete valuation rings with fraction
fields `K ⊆ L ⊆ M`. Assume the residue field of `A` is algebraically closed of characteristic
`p > 0`, `A` and `B` are complete, `A ⊆ B` is weakly unramified, `M / L` is finite, and the image
of `ResidueField A` in `ResidueField B` is exactly `⋂_{n ≥ 1} (ResidueField B)^(p^n)`. Then there
exists a finite extension `K₁ / K` which is a weak solution for `A → C`. -/
theorem exists_finite_extension_weakSolution_of_complete_of_residueField_pPowerIntersection
    (hAB : WeaklyUnramified A B)
    (hκ :
      (Set.range (algebraMap (ResidueField A) (ResidueField B)) : Set (ResidueField B)) =
        ⋂ n : ℕ+, Set.range (fun y : ResidueField B ↦ y ^ (p ^ (n : ℕ)))) :
    ∃ (K1 : Type (max u v w x y z)) (_ : Field K1) (_ : Algebra A K1) (_ : Algebra K K1)
      (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1),
      IsWeakSolutionFor A C K M K1 := sorry

end
