import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

universe u

section GroupIdentity

variable {G : Type u} [MulOneClass G]

-- Proof sketch: evaluate the left-identity condition at `1`, or the right-identity condition at
-- `1`, to conclude that any two-sided identity element must coincide with the canonical identity
-- `1`.
/-- Exercise 1.1.54 (1): any left identity element in a type with multiplication and unit, hence in
particular any two-sided identity element in a group, is exactly the canonical identity element
`1`. -/
theorem group_identity_eq_one (e : G) (hleft : ∀ g : G, e * g = g) : e = 1 := by
  simpa using hleft 1

end GroupIdentity

section SubgroupIntersections

variable {G : Type u} [Group G] (S : Set (Subgroup G))

/- Exercise 1.1.54 (2): the intersection of any family of subgroups of `G` is again a subgroup,
namely the infimum subgroup `sInf S`, whose carrier is the set-theoretic intersection of the
carriers. -/
#check Subgroup.coe_sInf

end SubgroupIntersections

section SubgroupUnions

variable {G : Type u} [Group G]

-- Proof sketch: if the union is the carrier of some subgroup `K`, then `K ⊆ H₁ ∪ H₂`; applying
-- `SubgroupClass.subset_union` to `K` shows `K ≤ H₁` or `K ≤ H₂`, and the carrier equality forces
-- the reverse inclusion for the remaining subgroup.
/-- Exercise 1.1.54 (2): if the union of two subgroups of `G` is itself the carrier of a subgroup,
then one of the two subgroups is contained in the other. -/
theorem subgroup_union_isSubgroup_implies (H₁ H₂ : Subgroup G)
    (hK : ∃ K : Subgroup G, (K : Set G) = (H₁ : Set G) ∪ (H₂ : Set G)) :
    H₁ ≤ H₂ ∨ H₂ ≤ H₁ := by
  rcases hK with ⟨K, hK⟩
  have hH₁K : H₁ ≤ K := by
    intro x hx
    simpa [hK.symm] using (show x ∈ (H₁ : Set G) ∪ (H₂ : Set G) from Or.inl hx)
  have hH₂K : H₂ ≤ K := by
    intro x hx
    simpa [hK.symm] using (show x ∈ (H₁ : Set G) ∪ (H₂ : Set G) from Or.inr hx)
  have hsubset : (K : Set G) ⊆ (H₁ : Set G) ∪ (H₂ : Set G) := by
    simp [hK]
  rcases (SubgroupClass.subset_union).1 hsubset with hK₁ | hK₂
  · exact Or.inr (hH₂K.trans hK₁)
  · exact Or.inl (hH₁K.trans hK₂)

end SubgroupUnions

section CongruenceClasses

variable (n : ℕ)

/- Exercise 1.1.54 (4): the congruence classes modulo `n` carry the canonical commutative ring
structure `ZMod n`. -/
#check (inferInstance : CommRing (ZMod n))

end CongruenceClasses

section NilpotentElements

variable {R : Type u} [Ring R]

/- Exercise 1.1.54 (5): for a nilpotent element `x` in a unital ring, the element `1 - x` is a
unit; this is the canonical theorem `IsNilpotent.isUnit_one_sub`. -/
#check IsNilpotent.isUnit_one_sub

end NilpotentElements

section NilpotentGeometricProduct

variable {R : Type u} [CommSemiring R]

-- Proof sketch: expand the product inductively, using the finite geometric-series identity for
-- `∑ i < 2^(n+1), x^i` and the doubling relation between successive factors `1 + x^(2^k)`.
/-- Exercise 1.1.54 (3): the product `∏_{k=0}^{n} (1 + x^(2^k))` simplifies to the finite
geometric sum `∑_{i=0}^{2^(n+1)-1} x^i`. -/
theorem prod_one_add_pow_two_pow_eq_sum_powers (x : R) (n : ℕ) :
    (∏ k ∈ Finset.range (n + 1), (1 + x ^ (2 ^ k))) = ∑ i ∈ Finset.range (2 ^ (n + 1)), x ^ i :=
  by
    induction n with
    | zero =>
        simp [add_comm]
    | succ n ih =>
        rw [Finset.prod_range_succ, ih]
        let m : ℕ := 2 ^ (n + 1)
        have hm : 2 ^ (n + 1 + 1) = m + m := by
          simp [m, Nat.two_pow_succ]
        rw [hm, mul_add, mul_one, Finset.sum_range_add]
        rw [show (∑ i ∈ Finset.range m, x ^ (m + i)) = (∑ i ∈ Finset.range m, x ^ i) * x ^ m by
          rw [mul_comm, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          rw [pow_add, mul_comm]]

end NilpotentGeometricProduct
