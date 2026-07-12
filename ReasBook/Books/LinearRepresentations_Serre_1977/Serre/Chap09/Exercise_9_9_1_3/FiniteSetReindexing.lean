import Mathlib
import LinearRepresentations_Serre_1977.Chap11.Theorem_11_11_2_1
import LinearRepresentations_Serre_1977.RepresentationTheory.SymmetricExterior
import LinearRepresentations_Serre_1977.Chap09.Exercise_9_9_1_3.PolynomialIdentities

open scoped Representation

noncomputable section

universe u v w

namespace Representation

open PowerSeries

section

variable {k : Type} [Field k]
variable {G : Type u} [Monoid G]
variable {V : Type v}
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]

theorem sum_powersetCard_eq_sum_attach_powersetCard
    {ι : Type*} [Fintype ι] [DecidableEq ι] {β : Type*} [AddCommMonoid β]
    (n : ℕ) (F : Set.powersetCard ι n → β) :
    (∑ s : Set.powersetCard ι n, F s) =
      Finset.sum (((Finset.univ : Finset ι).powersetCard n).attach) fun t ↦
        F ⟨t.1, (Finset.mem_powersetCard.mp t.2).2⟩ := by
  classical
  let e : {t // t ∈ ((Finset.univ : Finset ι).powersetCard n)} → Set.powersetCard ι n :=
    fun t ↦ ⟨t.1, (Finset.mem_powersetCard.mp t.2).2⟩
  have he : Function.Bijective e := by
    refine ⟨?_, ?_⟩
    · intro t u h
      apply Subtype.ext
      exact congrArg (fun x : Set.powersetCard ι n => (x : Finset ι)) h
    · intro s
      refine ⟨⟨s, Finset.mem_powersetCard.mpr ?_⟩, ?_⟩
      · exact ⟨by simp, s.prop⟩
      · apply Subtype.ext
        rfl
  -- Reindex the finite sum along the obvious bijection between the two owners of `n`-subsets.
  calc
    (∑ s : Set.powersetCard ι n, F s)
        = ∑ t : {t // t ∈ ((Finset.univ : Finset ι).powersetCard n)}, F (e t) := by
            symm
            exact Fintype.sum_bijective e he (fun t ↦ F (e t)) F (fun t ↦ rfl)
    _ = Finset.sum (((Finset.univ : Finset ι).powersetCard n).attach) fun t ↦
          F ⟨t.1, (Finset.mem_powersetCard.mp t.2).2⟩ := by
            rfl
/-- Helper for Exercise 9-9.1-3: the principal submatrix indexed by `s`, written using the
canonical `Fin n` parametrization of `s`, has the same determinant as the corresponding square
block of `M`. -/
theorem principal_submatrix_det_eq_block_det
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (M : Matrix ι ι k) (n : ℕ) (s : Set.powersetCard ι n) :
    Matrix.det (Matrix.of fun i j ↦
      M ((Set.powersetCard.ofFinEmbEquiv.symm s) i) ((Set.powersetCard.ofFinEmbEquiv.symm s) j) :
        Matrix (Fin n) (Fin n) k) =
      (Matrix.toSquareBlockProp M (fun i ↦ i ∈ (s : Finset ι))).det := by
  let e : {i // i ∈ (s : Finset ι)} ≃ Fin n := ((s : Finset ι).orderIsoOfFin s.prop).symm
  have hreindex :
      (Matrix.of fun i j ↦
        M ((Set.powersetCard.ofFinEmbEquiv.symm s) i) ((Set.powersetCard.ofFinEmbEquiv.symm s) j) :
          Matrix (Fin n) (Fin n) k) =
        Matrix.reindex e e (Matrix.toSquareBlockProp M (fun i ↦ i ∈ (s : Finset ι))) := by
    ext i j
    have hi : ((Set.powersetCard.ofFinEmbEquiv.symm s) i) = ↑(e.symm i) := by
      change ((s : Finset ι).orderEmbOfFin s.prop i) = ↑(((s : Finset ι).orderIsoOfFin s.prop) i)
      exact (Finset.coe_orderIsoOfFin_apply (s := (s : Finset ι)) (h := s.prop) i).symm
    have hj : ((Set.powersetCard.ofFinEmbEquiv.symm s) j) = ↑(e.symm j) := by
      change ((s : Finset ι).orderEmbOfFin s.prop j) = ↑(((s : Finset ι).orderIsoOfFin s.prop) j)
      exact (Finset.coe_orderIsoOfFin_apply (s := (s : Finset ι)) (h := s.prop) j).symm
    simp [Matrix.reindex_apply, Matrix.toSquareBlockProp, Matrix.toBlock, hi, hj]
  rw [hreindex]
  exact Matrix.det_reindex_self e (Matrix.toSquareBlockProp M (fun i ↦ i ∈ (s : Finset ι)))
/-- Helper for Exercise 9-9.1-3: the positive indices `1, …, n` are obtained from `range n` by
applying `Nat.succPNat`; this is the reindexing used in the Newton recurrences. -/
theorem pnat_Icc_one_eq_map_range
    (n : ℕ+) :
    Finset.Icc 1 n = (Finset.range n).map ⟨Nat.succPNat, Nat.succPNat_injective⟩ := by
  -- Rewrite each positive index by its predecessor and recover it with `succPNat`.
  ext m
  constructor
  · intro hm
    refine Finset.mem_map.mpr ?_
    refine ⟨m.natPred, ?_, ?_⟩
    · refine Finset.mem_range.mpr ?_
      have hm_le : m ≤ n := (Finset.mem_Icc.mp hm).2
      have hm_lt : m.natPred < n := by
        have h' : m.natPred + 1 ≤ n := by
          simpa [PNat.natPred_add_one] using hm_le
        exact lt_of_lt_of_le (Nat.lt_succ_self m.natPred) h'
      simpa using hm_lt
    · simp
  · intro hm
    rcases Finset.mem_map.mp hm with ⟨i, hi, rfl⟩
    refine Finset.mem_Icc.mpr ?_
    constructor
    · simp
    · simpa using hi
/-- Helper for Exercise 9-9.1-3: mapping coefficients through an injective ring homomorphism
commutes with polynomial reversal. -/
theorem polynomial_reverse_map
    {R : Type u} {S : Type v} [Semiring R] [Semiring S] (f : R →+* S)
    (hf : Function.Injective f)
    (p : Polynomial R) :
    p.reverse.map f = (p.map f).reverse := by
  ext n
  by_cases hn : n ≤ p.natDegree
  · rw [Polynomial.coeff_map, Polynomial.coeff_reverse, Polynomial.coeff_reverse,
      Polynomial.revAt_le hn]
    rw [Polynomial.revAt_le]
    · rw [Polynomial.natDegree_map_eq_of_injective hf, Polynomial.coeff_map]
    · simpa [Polynomial.natDegree_map_eq_of_injective hf] using hn
  · have hnlt : p.natDegree < n := lt_of_not_ge hn
    rw [Polynomial.coeff_map, Polynomial.coeff_eq_zero_of_natDegree_lt]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
      · simp
      · exact lt_of_le_of_lt (p.map f).reverse_natDegree_le <|
            by simpa [Polynomial.natDegree_map_eq_of_injective hf] using hnlt
    · exact lt_of_le_of_lt p.reverse_natDegree_le hnlt

end

end Representation
