import Mathlib.Algebra.BigOperators.Ring.Multiset
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.ZMod.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Lemma_23_4_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Problem_23_9_1

open scoped EuclideanSpace Manifold TopCat

noncomputable section

-- Chapter 23 already records the source-facing tangential-number owner by
-- `tangentialStiefelWhitneyNumber` and its intrinsic vanishing predicate
-- `allTangentialStiefelWhitneyNumbersVanish`. For `RP^q`, Problem 23.9.1 supplies the standard
-- representative of `w(RP^q)`. This file keeps the partition-indexed product formula only as a
-- local computational bridge derived from that representative, while the public API stays on the
-- intrinsic Chapter 23 vanishing predicate.

/- The standard partition-indexed product formula for the tangential Stiefel-Whitney number of
`RP^q`, obtained by multiplying the coefficients of
`realProjectiveSpaceTotalStiefelWhitneyRepresentative q` indexed by the parts of `σ`. -/
private def realProjectiveSpaceTangentialStiefelWhitneyNumberFormula
    (q : ℕ) (σ : Nat.Partition q) : ZMod 2 :=
  (σ.parts.map fun i ↦ (realProjectiveSpaceTotalStiefelWhitneyRepresentative q).coeff i).prod

private theorem even_sum_of_forall_even (s : Multiset ℕ) (hs : ∀ i ∈ s, Even i) :
    Even s.sum := by
  induction s using Multiset.induction_on with
  | empty =>
      simp
  | @cons a s ih =>
      have ha : Even a := hs a (by simp)
      have hs' : ∀ i ∈ s, Even i := by
        intro i hi
        exact hs i (by simp [hi])
      simp [Multiset.sum_cons, Nat.even_add, ha, ih hs']

private theorem exists_odd_of_odd_sum (s : Multiset ℕ) (hsum : Odd s.sum) :
    ∃ i ∈ s, Odd i := by
  by_contra h
  have hall : ∀ i ∈ s, Even i := by
    intro i hi
    exact Nat.not_odd_iff_even.mp (by
      intro hi_odd
      exact h ⟨i, hi, hi_odd⟩)
  exact (Nat.not_even_iff_odd.mpr hsum) (even_sum_of_forall_even s hall)

private theorem choose_even_odd_even {n k : ℕ} (hn : Even n) (hk : Odd k) :
    Even (n.choose k) := by
  rcases hn with ⟨a, rfl⟩
  rcases hk with ⟨b, rfl⟩
  rw [← ZMod.natCast_eq_zero_iff_even]
  change (((a + a).choose (2 * b + 1) : ℕ) : ZMod 2) = ((0 : ℕ) : ZMod 2)
  rw [ZMod.natCast_eq_natCast_iff]
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hmod :
      (2 * a).choose (2 * b + 1) ≡ 0 [MOD 2] := by
    simpa using
      (Choose.choose_modEq_choose_mod_mul_choose_div_nat :
        (2 * a).choose (2 * b + 1) ≡
          (2 * a % 2).choose ((2 * b + 1) % 2) *
            ((2 * a) / 2).choose ((2 * b + 1) / 2) [MOD 2])
  simpa [two_mul] using hmod

/- Unfolding the local `RP^q` tangential-number formula gives the product of the coefficients of
the standard total Stiefel-Whitney representative indexed by the parts of `σ`. -/
@[simp] private theorem realProjectiveSpaceTangentialStiefelWhitneyNumberFormula_eq_prod_coeff
    (q : ℕ) (σ : Nat.Partition q) :
    realProjectiveSpaceTangentialStiefelWhitneyNumberFormula q σ =
      (σ.parts.map fun i ↦
        (realProjectiveSpaceTotalStiefelWhitneyRepresentative q).coeff i).prod := rfl

/- The local `RP^q` tangential-number formula can be rewritten as the usual product of binomial
coefficients `((q + 1).choose i : ZMod 2)` indexed by the parts of `σ`. -/
private theorem realProjectiveSpaceTangentialStiefelWhitneyNumberFormula_eq_prod_choose
    (q : ℕ) (σ : Nat.Partition q) :
    realProjectiveSpaceTangentialStiefelWhitneyNumberFormula q σ =
      (σ.parts.map fun i ↦ ((q + 1).choose i : ZMod 2)).prod := by
  rw [realProjectiveSpaceTangentialStiefelWhitneyNumberFormula_eq_prod_coeff]
  refine congrArg Multiset.prod ?_
  refine Multiset.map_congr rfl ?_
  intro i hi
  rw [realProjectiveSpaceTotalStiefelWhitneyRepresentative_coeff]
  exact if_pos (Nat.Partition.le_of_mem_parts hi)

/- For the indiscrete partition of `q`, the local `RP^q` tangential-number formula is the top-degree
coefficient `((q + 1).choose q : ZMod 2)`. -/
private theorem realProjectiveSpaceTangentialStiefelWhitneyNumberFormula_indiscrete (q : ℕ) :
    realProjectiveSpaceTangentialStiefelWhitneyNumberFormula q (Nat.Partition.indiscrete q) =
      ((q + 1).choose q : ZMod 2) := by
  rw [realProjectiveSpaceTangentialStiefelWhitneyNumberFormula_eq_prod_choose]
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  · simp [Nat.Partition.indiscrete_parts, hq.ne']

/- The intrinsic Chapter 23 vanishing predicate for tangential Stiefel-Whitney numbers of `RP^q`
is equivalent to the vanishing of the standard partition-indexed product formula. This is the
bridge from the source-facing owner `allTangentialStiefelWhitneyNumbersVanish` to the explicit
binomial-coefficient computation. -/
private theorem allTangentialStiefelWhitneyNumbersVanish_realProjectiveSpace_iff_formula
    (q : ℕ)
    [ChartedSpace (EuclideanSpace ℝ (Fin q)) (RealProjectiveSpace q)]
    [IsManifold (𝓡 q) ⊤ (RealProjectiveSpace q)]
    [TopologicalSpace
      (Bundle.TotalSpace
        (Fin q → ℝ) (TangentSpace (𝓡 q) : TopCat.of (RealProjectiveSpace q) → Type _))]
    [FiberBundle
      (Fin q → ℝ) (TangentSpace (𝓡 q) : TopCat.of (RealProjectiveSpace q) → Type _)]
    [VectorBundle
      ℝ (Fin q → ℝ) (TangentSpace (𝓡 q) : TopCat.of (RealProjectiveSpace q) → Type _)] :
    allTangentialStiefelWhitneyNumbersVanish q (RealProjectiveSpace q) ↔
      ∀ σ : Nat.Partition q,
        realProjectiveSpaceTangentialStiefelWhitneyNumberFormula q σ = 0 := sorry

/- The standard partition-indexed product formula for the tangential Stiefel-Whitney numbers of
`RP^q` vanishes for every partition of `q` exactly when `q` is odd. -/
private theorem realProjectiveSpaceTangentialStiefelWhitneyNumberFormula_vanishes_iff_odd
    (q : ℕ) :
    (∀ σ : Nat.Partition q,
      realProjectiveSpaceTangentialStiefelWhitneyNumberFormula q σ = 0) ↔ Odd q := by
  constructor
  · intro hvanish
    by_contra hq
    have heven : Even q := Nat.not_odd_iff_even.mp hq
    have hindiscrete := hvanish (Nat.Partition.indiscrete q)
    rw [realProjectiveSpaceTangentialStiefelWhitneyNumberFormula_indiscrete] at hindiscrete
    have hnonzero : (((q + 1).choose q : ℕ) : ZMod 2) ≠ 0 := by
      rw [Nat.choose_succ_self_right, ZMod.natCast_ne_zero_iff_odd]
      exact Even.add_one heven
    exact hnonzero hindiscrete
  · intro hq σ
    rw [realProjectiveSpaceTangentialStiefelWhitneyNumberFormula_eq_prod_choose]
    have hparts_odd : Odd σ.parts.sum := by
      simpa [σ.parts_sum] using hq
    obtain ⟨i, hi, hiodd⟩ := exists_odd_of_odd_sum σ.parts hparts_odd
    have hcoeff_zero : (((q + 1).choose i : ℕ) : ZMod 2) = 0 := by
      rw [ZMod.natCast_eq_zero_iff_even]
      exact choose_even_odd_even (Odd.add_one hq) hiodd
    have hmem :
        (0 : ZMod 2) ∈ σ.parts.map fun j ↦ ((q + 1).choose j : ZMod 2) := by
      exact hcoeff_zero ▸ Multiset.mem_map_of_mem (fun j ↦ ((q + 1).choose j : ZMod 2)) hi
    exact Multiset.prod_eq_zero hmem

/-- Problem 23.9.3. All tangential Stiefel-Whitney numbers of `RP^q` vanish if and only if `q` is
odd. The main statement uses the intrinsic Chapter 23 owner
`allTangentialStiefelWhitneyNumbersVanish`, with the explicit binomial-coefficient formula kept as
the computation bridge. -/
theorem realProjectiveSpaceTangentialStiefelWhitneyNumbers_vanish_iff_odd
    (q : ℕ)
    [ChartedSpace (EuclideanSpace ℝ (Fin q)) (RealProjectiveSpace q)]
    [IsManifold (𝓡 q) ⊤ (RealProjectiveSpace q)]
    [TopologicalSpace
      (Bundle.TotalSpace
        (Fin q → ℝ) (TangentSpace (𝓡 q) : TopCat.of (RealProjectiveSpace q) → Type _))]
    [FiberBundle
      (Fin q → ℝ) (TangentSpace (𝓡 q) : TopCat.of (RealProjectiveSpace q) → Type _)]
    [VectorBundle
      ℝ (Fin q → ℝ) (TangentSpace (𝓡 q) : TopCat.of (RealProjectiveSpace q) → Type _)] :
    allTangentialStiefelWhitneyNumbersVanish q (RealProjectiveSpace q) ↔ Odd q := by
  rw [allTangentialStiefelWhitneyNumbersVanish_realProjectiveSpace_iff_formula q]
  exact realProjectiveSpaceTangentialStiefelWhitneyNumberFormula_vanishes_iff_odd q
