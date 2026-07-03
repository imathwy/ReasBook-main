import Mathlib
import StacksProject_2024.Chap15.Definition_15_112_7
import StacksProject_2024.Chap15.Lemma_15_116_4

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open IsExtensionOfDiscreteValuationRings

universe u v w x y z

section

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
variable [IsExtensionOfDiscreteValuationRings A B]
variable [IsExtensionOfDiscreteValuationRings B C]
variable [IsExtensionOfDiscreteValuationRings A C]
variable {K : Type x} {L : Type y} {M : Type z}
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra B L] [Algebra A L] [Algebra K L] [IsFractionRing B L]
variable [IsScalarTower A B L] [IsScalarTower A K L]
variable [Field M] [Algebra A M] [Algebra K M] [Algebra C M] [Algebra L M] [IsFractionRing C M]
variable [IsScalarTower A C M] [IsScalarTower A K M]
variable {p : ℕ} [Fact p.Prime] [CharP K p] [FiniteDimensional L M] [IsGalois L M]

-- Proof sketch: choose an Artin-Schreier generator for the degree-`p` Galois extension `M / L`,
-- apply the ramification trichotomy over `B`, and use the hypothesis on
-- `⋂_{n ≥ 1} (ResidueField B)^(p^n)` together with the totally ramified degree-`p^r` extensions
-- from Lemma `15.116.7` to eliminate the bad residue terms inductively until the base change over
-- `C` becomes weakly unramified.
/-- Lemma 15.116.12: let `A ⊆ B ⊆ C` be extensions of discrete valuation rings with fraction
fields `K ⊆ L ⊆ M`. Assume `A ⊆ B` is weakly unramified, `K` has characteristic `p`, `M / L` is
a degree-`p` Galois extension, and the image of `ResidueField A` in `ResidueField B` is exactly
the intersection of the subsets of `p^n`-powers in `ResidueField B`. Then there exists a finite
Galois extension `K₁ / K`, totally ramified with respect to `A`, which is a weak solution for the
extension `A → C`. -/
theorem exists_totallyRamified_galois_weakSolution_of_degree_p_galois_extension
    (hAB : WeaklyUnramified A B)
    (hLM : Module.finrank L M = p)
    (hκ :
      (Set.range (algebraMap (ResidueField A) (ResidueField B)) : Set (ResidueField B)) =
        ⋂ n : ℕ+, Set.range (fun y : ResidueField B ↦ y ^ (p ^ (n : ℕ)))) :
    ∃ (K1 : Type (max u v w x y z)) (_ : Field K1) (_ : Algebra A K1) (_ : Algebra K K1)
      (_ : IsScalarTower A K K1) (_ : Algebra (FractionRing A) K1)
      (_ : IsScalarTower A (FractionRing A) K1)
      (_ : FiniteDimensional K K1) (_ : FiniteDimensional (FractionRing A) K1)
      (_ : IsGalois K K1) (_ : Algebra.IsSeparable (FractionRing A) K1)
      (_ : IsTotallyRamifiedWithRespectTo A K1),
        IsWeakSolutionFor A C K M K1 := sorry

end
