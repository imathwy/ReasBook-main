import Mathlib
import Serre.GroupTheory.ConjClassesPower
import Serre.Chap02.Corollary_2_2_4_3
import Serre.Chap12.CharacterRingOverFieldScalarExtension
import Serre.Chap06.Exercise_6_6_3_3
import Serre.Chap13.Exercise_13_13_1_15
import Serre.Chap13.Exercise_13_13_1_16.Index

open CategoryTheory
open IsCyclotomicExtension.Rat
open scoped MonoidAlgebra Representation
open Representation

noncomputable section

universe u

section ExerciseClauses

variable {G : Type u} [Group G] [Finite G]
variable {K : Type u} [Field K] [NumberField K]
variable [IsCyclotomicExtension {Monoid.exponent G} ℚ K]

section PartA

variable {ι : Type u} [MulAction ((ZMod (Monoid.exponent G))ˣ) ι]
variable (π : ι → Rep K G) [∀ i, FiniteDimensional K (π i)]

/-- Exercise 13-13.1-16 (1): source part (a). If `ι` indexes the irreducible `K`-characters of
`G` for a cyclotomic realization `K` of `ℚ(m)` with `m = exp(G)`, and the `Γ_ℚ`-action on `ι`
matches Galois conjugation of characters, then the `Γ_ℚ`-sets of irreducible characters and
conjugacy classes are weakly isomorphic in the sense of Exercise `13-13.1-15`. -/
theorem irreducible_character_index_weaklyIsomorphic_conjClasses
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (hπ_galois : IrreducibleCharacterIndexGaloisCompatible π) :
    let _ : Fintype G := Fintype.ofFinite G
    let _ : Finite ι := by
      exact finite_index_of_complete_pairwise_nonisomorphic_rep
        (π := π) hπ_pairwise hπ_complete
    let _ : Fintype ι := Fintype.ofFinite ι
    Action.WeaklyIsomorphic
      (Action.FintypeCat.ofMulAction (Γ_ℚ(G)) (FintypeCat.of ι))
      (Action.FintypeCat.ofMulAction (Γ_ℚ(G)) (FintypeCat.of (ConjClasses G))) := by
  admit

end PartA

section PartB

variable {ι : Type u} [MulAction ((ZMod (Monoid.exponent G))ˣ) ι]
variable (π : ι → Rep K G) [∀ i, FiniteDimensional K (π i)]

/-- Exercise 13-13.1-16 (2): source part (b). The `Γ_ℚ`-set of irreducible `K`-characters can be
identified with the `Γ_ℚ`-set of `ℚ`-algebra homomorphisms from the center of `ℚ[G]` to the
cyclotomic field `K`, provided the given `Γ_ℚ`-action on the index set matches Galois
conjugation of irreducible characters. -/
theorem irreducible_character_index_isomorphic_center_algHom
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (hπ_galois : IrreducibleCharacterIndexGaloisCompatible π) :
    IsIsomorphic
      (Action.ofMulAction (Γ_ℚ(G)) ι)
      (Action.ofMulAction (Γ_ℚ(G)) (Subalgebra.center ℚ (ℚ[G]) →ₐ[ℚ] K)) := by
  admit

/-- Exercise 13-13.1-16 (3): source part (b). The `Γ_ℚ`-set of conjugacy classes of `G` can be
identified with the `Γ_ℚ`-set of `ℚ`-algebra homomorphisms from `ℚ ⊗ R_K(G)`, where `K` is the
cyclotomic splitting field `ℚ(m)` from the source statement. Using the `ℚ`-valued owner here
instead packages rational-power orbit data and is false for examples such as `C₄`. -/
theorem conjClasses_isomorphic_rationalCharacterRing_algHom :
    IsIsomorphic
      (Action.ofMulAction (Γ_ℚ(G)) (ConjClasses G))
      (Action.ofMulAction (Γ_ℚ(G))
        (characterRingOverFieldScalarExtensionSubalgebra K G →ₐ[ℚ] K)) := by
  admit

/-- Exercise 13-13.1-16 (4): source part (b). Once the two source sets are identified with the
corresponding cyclotomic character sets of `Subalgebra.center ℚ (ℚ[G])` and the split-field
character algebra `characterRingOverFieldScalarExtensionSubalgebra K G`, the `Γ_ℚ`-sets of
irreducible characters and conjugacy classes are isomorphic if and only if those two `ℚ`-algebras
are isomorphic. -/
theorem
    irreducible_character_index_isomorphic_to_conjClasses_iff_center_algEquiv_rationalCharacterRing
    {ι : Type u} [MulAction ((ZMod (Monoid.exponent G))ˣ) ι]
    (hX : IsIsomorphic
      (Action.ofMulAction (Γ_ℚ(G)) ι)
      (Action.ofMulAction (Γ_ℚ(G)) (Subalgebra.center ℚ (ℚ[G]) →ₐ[ℚ] K)))
    (hY : IsIsomorphic
      (Action.ofMulAction (Γ_ℚ(G)) (ConjClasses G))
      (Action.ofMulAction (Γ_ℚ(G))
        (characterRingOverFieldScalarExtensionSubalgebra K G →ₐ[ℚ] K))) :
    IsIsomorphic
      (Action.ofMulAction (Γ_ℚ(G)) ι)
      (Action.ofMulAction (Γ_ℚ(G)) (ConjClasses G)) ↔
      Nonempty
        (Subalgebra.center ℚ (ℚ[G]) ≃ₐ[ℚ]
          characterRingOverFieldScalarExtensionSubalgebra K G) := by
  admit

end PartB

/-- Helper for Exercise 13-13.1-16: if `G` is a finite `p`-group with `p ≠ 2`, then the rational
power automorphism group `Γ_ℚ(G)` is cyclic. -/
theorem gammaRat_isCyclic_of_isPGroup_and_prime_ne_two
    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G) (hp2 : p ≠ 2) :
    IsCyclic (Γ_ℚ(G)) := by
  rcases (IsPGroup.iff_card (p := p) (G := G)).1 hG with ⟨n, hn⟩
  by_cases hexp1 : Monoid.exponent G = 1
  · rw [hexp1]
    simpa using ZMod.isCyclic_units_one
  · have hdiv : Monoid.exponent G ∣ p ^ n := by
      simpa [hn] using (Group.exponent_dvd_nat_card (G := G))
    obtain ⟨k, _, hkexp⟩ := (Nat.dvd_prime_pow Fact.out).1 hdiv
    rw [hkexp]
    simpa using ZMod.isCyclic_units_of_prime_pow p Fact.out hp2 k

/-- Exercise 13-13.1-16 (5): source part `(c₁)`. If `G` is abelian, then the center of `ℚ[G]` is
isomorphic, as a `ℚ`-algebra, to the split cyclotomic character algebra `ℚ ⊗ R_K(G)`, realized
here as `characterRingOverFieldScalarExtensionSubalgebra K G`. -/
theorem center_groupAlgebra_algEquiv_rationalCharacterRing_of_isMulCommutative
    [IsMulCommutative G] :
    Nonempty
      (Subalgebra.center ℚ (ℚ[G]) ≃ₐ[ℚ]
        characterRingOverFieldScalarExtensionSubalgebra K G) := by
  admit

/-- Exercise 13-13.1-16 (6): source part `(c₂)`. If `G` is a finite `p`-group with `p ≠ 2`, then
the center of `ℚ[G]` is isomorphic, as a `ℚ`-algebra, to the split cyclotomic character algebra
`ℚ ⊗ R_K(G)`, realized here as `characterRingOverFieldScalarExtensionSubalgebra K G`. -/
theorem center_groupAlgebra_algEquiv_rationalCharacterRing_of_isPGroup_and_prime_ne_two
    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G) (hp2 : p ≠ 2) :
    Nonempty
      (Subalgebra.center ℚ (ℚ[G]) ≃ₐ[ℚ]
        characterRingOverFieldScalarExtensionSubalgebra K G) := by
  admit

end ExerciseClauses

end
