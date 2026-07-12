import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

namespace Representation

section RootDescent

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]

local notation "k" => IsLocalRing.ResidueField A

omit [IsDiscreteValuationRing A] in
private theorem dvr_eq_one_of_pow_eq_one_of_residue_eq_one
    {a : A} {n : ℕ} (hn : ((n : ℕ) : k) ≠ 0)
    (ha : a ^ n = 1) (hres : IsLocalRing.residue A a = 1) :
    a = 1 := by
  let s : A := ∑ i ∈ Finset.range n, a ^ i
  have hs_res : IsLocalRing.residue A s = (n : k) := by
    calc
      IsLocalRing.residue A s
          = ∑ i ∈ Finset.range n, IsLocalRing.residue A (a ^ i) := by
              simp [s]
      _ = ∑ i ∈ Finset.range n, (1 : k) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [map_pow]
            simp [hres]
      _ = (n : k) := by simp
  have hs_unit : IsUnit s := by
    have hs_res_ne : IsLocalRing.residue A s ≠ 0 := by
      simpa [hs_res] using hn
    have hs_not_mem : s ∉ IsLocalRing.maximalIdeal A := by
      intro hs_mem
      exact hs_res_ne ((IsLocalRing.residue_eq_zero_iff s).2 hs_mem)
    exact (IsLocalRing.notMem_maximalIdeal).1 hs_not_mem
  have hgeom : (a - 1) * s = 0 := by
    rw [mul_comm]
    simpa [s, ha] using (geom_sum_mul a n)
  have hsub : a - 1 = 0 :=
    (IsUnit.mul_left_eq_zero hs_unit).1 hgeom
  exact sub_eq_zero.mp hsub

/-- DVR root descent for the prime-to-residue-character part: if `K = Frac A` contains a
primitive `n`-th root and `n` is nonzero in the residue field, then the root is represented by an
element of `A` whose residue is again a primitive `n`-th root. -/
theorem exists_lift_isPrimitiveRoot_residue_of_isPrimitiveRoot_fraction
    {ζ : K} {n : ℕ} (hn : ((n : ℕ) : k) ≠ 0)
    (hζ : IsPrimitiveRoot ζ n) :
    ∃ a : A, algebraMap A K a = ζ ∧ IsPrimitiveRoot (IsLocalRing.residue A a) n := by
  have hnpos : 0 < n := by
    by_contra hnpos
    have hnzero : n = 0 := Nat.eq_zero_of_not_pos hnpos
    subst n
    simp at hn
  have hζint : IsIntegral A (ζ ^ n) := by
    rw [hζ.pow_eq_one]
    exact isIntegral_one
  obtain ⟨a, ha⟩ :=
    IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (R := A) (K := K)
      hnpos hζint
  have ha_pow : a ^ n = 1 := by
    apply IsFractionRing.injective A K
    rw [map_pow, ha, hζ.pow_eq_one, map_one]
  refine ⟨a, ha, ?_⟩
  refine ⟨?_, ?_⟩
  · rw [← map_pow, ha_pow, map_one]
  · intro l hl
    apply hζ.dvd_of_pow_eq_one
    have h_al : a ^ l = 1 := by
      apply dvr_eq_one_of_pow_eq_one_of_residue_eq_one (A := A) (n := n) hn
      · rw [← pow_mul, Nat.mul_comm, pow_mul, ha_pow, one_pow]
      · rw [map_pow]
        exact hl
    rw [← ha, ← map_pow, h_al, map_one]

/-- A prime-to-residue-character form of Serre's root descent: enough `n`-th roots in the fraction
field descend to enough `n`-th roots in the residue field when `n` is nonzero downstairs. -/
theorem residueField_hasEnoughRootsOfUnity_of_fraction_of_natCast_ne_zero
    {n : ℕ} (hn : ((n : ℕ) : k) ≠ 0) [HasEnoughRootsOfUnity K n] :
    HasEnoughRootsOfUnity k n := by
  haveI : NeZero n := ⟨by
    intro hn0
    subst n
    simp at hn⟩
  exact
    { prim := by
        obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K n
        obtain ⟨a, _ha, hres⟩ :=
          exists_lift_isPrimitiveRoot_residue_of_isPrimitiveRoot_fraction
            (A := A) (K := K) hn hζ
        exact ⟨IsLocalRing.residue A a, hres⟩
      cyc := rootsOfUnity.isCyclic k n }

end RootDescent

end Representation
