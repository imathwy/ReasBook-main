module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Order.Interval.Finset.Fin

public section

namespace Remark50_2.BarycentricParity

/-- Helper for Remark 50.2: the rank-`k` member of a permutation flag is the
image of the initial segment through `k`. -/
def flagPrefix {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (k : Fin (n + 1)) : Finset (Fin (n + 1)) :=
  (Finset.Iic k).image σ

/-- Helper for Remark 50.2: deleting rank `r` from a maximal permutation flag
gives its ordered codimension-one face. -/
def flagFace (n : ℕ) (σ : Equiv.Perm (Fin (n + 2))) (r : Fin (n + 2)) :
    Fin (n + 1) → Finset (Fin (n + 2)) :=
  fun k ↦ flagPrefix σ (r.succAbove k)

/-- Helper for Remark 50.2: a permutation flag on the facet opposite `r`,
viewed inside the ambient vertex set. -/
def facetFlag (n : ℕ) (r : Fin (n + 2))
    (τ : Equiv.Perm (Fin (n + 1))) : Fin (n + 1) → Finset (Fin (n + 2)) :=
  fun k ↦ (flagPrefix τ k).image r.succAbove

/-- Helper for Remark 50.2: swapping two ranks on the same side of a flag
prefix leaves that prefix unchanged. -/
lemma flagPrefix_mul_swap_of_sameSide {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) (r s k : Fin (n + 1))
    (hside : (r ≤ k ∧ s ≤ k) ∨ (k < r ∧ k < s)) :
    flagPrefix (σ * Equiv.swap r s) k = flagPrefix σ k := by
  -- The transposition preserves membership in the controlling initial segment.
  have hpreserve (x : Fin (n + 1)) :
      x ≤ k ↔ Equiv.swap r s x ≤ k := by
    by_cases hxr : x = r
    · subst x
      rw [Equiv.swap_apply_left]
      rcases hside with hin | hout
      · exact iff_of_true hin.1 hin.2
      · exact iff_of_false (not_le_of_gt hout.1) (not_le_of_gt hout.2)
    · by_cases hxs : x = s
      · subst x
        rw [Equiv.swap_apply_right]
        rcases hside with hin | hout
        · exact iff_of_true hin.2 hin.1
        · exact iff_of_false (not_le_of_gt hout.2) (not_le_of_gt hout.1)
      · rw [Equiv.swap_apply_of_ne_of_ne hxr hxs]
  have hprefixSwap :
      (Finset.Iic k).image (Equiv.swap r s) = Finset.Iic k := by
    ext x
    simp only [Finset.mem_image, Finset.mem_Iic]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hpreserve y).mp hy
    · intro hx
      refine ⟨Equiv.swap r s x, (hpreserve x).mp hx, ?_⟩
      exact Equiv.swap_apply_self r s x
  -- Reindex the preserved prefix and then apply the original permutation.
  calc
    flagPrefix (σ * Equiv.swap r s) k =
        (Finset.Iic k).image (fun x ↦ σ (Equiv.swap r s x)) := by
      apply Finset.image_congr
      intro x _
      exact Equiv.Perm.mul_apply σ (Equiv.swap r s) x
    _ = ((Finset.Iic k).image (Equiv.swap r s)).image σ :=
      Finset.image_image.symm
    _ = flagPrefix σ k := by
      rw [hprefixSwap]
      rfl

/-- Helper for Remark 50.2: after deleting rank `r`, the adjacent swap of
`r` and `r + 1` leaves every retained flag prefix unchanged. -/
lemma flagPrefix_mul_adjacentSwap {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) (r : Fin n) (k : Fin (n + 1))
    (hk : k ≠ r.castSucc) :
    flagPrefix (σ * Equiv.swap r.castSucc r.succ) k = flagPrefix σ k := by
  -- An adjacent pair can straddle `k` only when `k` is its lower member.
  apply flagPrefix_mul_swap_of_sameSide
  by_cases hupper : r.succ ≤ k
  · exact Or.inl ⟨(Fin.castSucc_le_succ r).trans hupper, hupper⟩
  · have hkUpper : k < r.succ := lt_of_not_ge hupper
    have hkLower : k ≤ r.castSucc := Fin.le_castSucc_iff.mpr hkUpper
    exact Or.inr ⟨lt_of_le_of_ne hkLower hk, hkUpper⟩

/-- Helper for Remark 50.2: the adjacent transposition pairs equal internal
flag faces. -/
lemma flagFace_mul_adjacentSwap (n : ℕ) (σ : Equiv.Perm (Fin (n + 2)))
    (r : Fin (n + 1)) :
    flagFace n (σ * Equiv.swap r.castSucc r.succ) r.castSucc =
      flagFace n σ r.castSucc := by
  -- Compare every retained rank and invoke prefix invariance.
  funext k
  apply flagPrefix_mul_adjacentSwap
  exact Fin.succAbove_ne r.castSucc k

/-- Helper for Remark 50.2: right multiplication by an adjacent rank swap is
a fixed-point-free involution on permutation flags. -/
lemma adjacentSwap_ne_involutive (n : ℕ) (σ : Equiv.Perm (Fin (n + 2)))
    (r : Fin (n + 1)) :
    σ * Equiv.swap r.castSucc r.succ ≠ σ ∧
      (σ * Equiv.swap r.castSucc r.succ) *
        Equiv.swap r.castSucc r.succ = σ := by
  -- The first adjacent rank moves, and applying the swap twice cancels it.
  constructor
  · intro heq
    have happly := congrArg
      (fun τ : Equiv.Perm (Fin (n + 2)) ↦ τ r.castSucc) heq
    have hranks : r.succ ≠ r.castSucc :=
      (Fin.ne_of_lt r.castSucc_lt_succ).symm
    exact hranks (σ.injective (by simpa only [Equiv.Perm.mul_apply,
      Equiv.swap_apply_left] using happly))
  · simp only [mul_assoc, Equiv.swap_mul_self, mul_one]

/-- Helper for Remark 50.2: for one internal rank, arbitrary mod-two face
weights cancel in adjacent-transposition pairs. -/
lemma interiorFaceWeight_sum_eq_zero (n : ℕ) (r : Fin (n + 1))
    (W : (Fin (n + 1) → Finset (Fin (n + 2))) → ZMod 2) :
    ∑ σ : Equiv.Perm (Fin (n + 2)), W (flagFace n σ r.castSucc) = 0 := by
  classical
  let swap : Equiv.Perm (Fin (n + 2)) :=
    Equiv.swap r.castSucc r.succ
  -- Pair every permutation with the adjacent swap; equal terms add to zero.
  apply Finset.sum_ninvolution (s := Finset.univ) (fun σ ↦ σ * swap)
  · intro σ
    have hface : flagFace n (σ * swap) r.castSucc =
        flagFace n σ r.castSucc := by
      exact flagFace_mul_adjacentSwap n σ r
    rw [hface]
    exact CharTwo.add_self_eq_zero _
  · intro σ _ hfixed
    exact (adjacentSwap_ne_involutive n σ r).1 hfixed
  · intro σ
    exact Finset.mem_univ _
  · intro σ
    exact (adjacentSwap_ne_involutive n σ r).2

/-- Helper for Remark 50.2: the combined arbitrary mod-two weight of all
internal flag faces vanishes. -/
lemma interiorBoundaryWeight_sum_eq_zero (n : ℕ)
    (W : (Fin (n + 1) → Finset (Fin (n + 2))) → ZMod 2) :
    ∑ σ : Equiv.Perm (Fin (n + 2)),
      ∑ r : Fin (n + 1), W (flagFace n σ r.castSucc) = 0 := by
  classical
  -- Exchange the finite sums and cancel one internal rank at a time.
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro r _
  exact interiorFaceWeight_sum_eq_zero n r W

/-- Helper for Remark 50.2: order the vertices of the face opposite `r` by
`τ`, then append `r` as the last vertex. -/
def lastPermutation (n : ℕ) (r : Fin (n + 2))
    (τ : Equiv.Perm (Fin (n + 1))) : Equiv.Perm (Fin (n + 2)) :=
  Fin.cycleIcc r (Fin.last (n + 1)) *
    τ.extendDomain (finSuccAboveEquiv (Fin.last (n + 1)))

/-- Helper for Remark 50.2: the final value of the last-vertex permutation is
the omitted facet vertex. -/
lemma lastPermutation_last (n : ℕ) (r : Fin (n + 2))
    (τ : Equiv.Perm (Fin (n + 1))) :
    lastPermutation n r τ (Fin.last (n + 1)) = r := by
  classical
  -- The extension fixes the missing point, then the interval cycle returns it to `r`.
  unfold lastPermutation
  rw [Equiv.Perm.mul_apply, Equiv.Perm.extendDomain_apply_not_subtype]
  · exact Fin.cycleIcc_of_last (Fin.le_last r)
  · simp only [not_ne_iff]

/-- Helper for Remark 50.2: before its final value, the last-vertex
permutation follows the ordered facet inclusion. -/
lemma lastPermutation_castSucc (n : ℕ) (r : Fin (n + 2))
    (τ : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 1)) :
    lastPermutation n r τ k.castSucc = r.succAbove (τ k) := by
  classical
  unfold lastPermutation
  rw [Equiv.Perm.mul_apply]
  have hext :
      τ.extendDomain (finSuccAboveEquiv (Fin.last (n + 1))) k.castSucc =
        (τ k).castSucc := by
    simpa only [finSuccAboveEquiv_apply, Fin.succAbove_last_apply] using
      Equiv.Perm.extendDomain_apply_image τ
        (finSuccAboveEquiv (Fin.last (n + 1))) k
  rw [hext]
  -- The interval cycle transports the standard last-facet inclusion to `r.succAbove`.
  have hcycle := congrFun
    (Fin.cycleIcc_comp_succAbove r (Fin.last (n + 1)) (Fin.le_last r)) (τ k)
  simpa only [Function.comp_apply, Fin.succAbove_last_apply] using hcycle

/-- Helper for Remark 50.2: the omitted vertex and its facet ordering
parameterize all ambient permutations bijectively. -/
lemma lastPermutation_bijective (n : ℕ) :
    Function.Bijective
      (fun p : Fin (n + 2) × Equiv.Perm (Fin (n + 1)) ↦
        lastPermutation n p.1 p.2) := by
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · rintro ⟨r, τ⟩ ⟨r', τ'⟩ h
    have hr : r = r' := by
      have happ := congrArg
        (fun π : Equiv.Perm (Fin (n + 2)) ↦ π (Fin.last (n + 1))) h
      simpa only [lastPermutation_last] using happ
    subst r'
    have hτ : τ = τ' := by
      apply Equiv.ext
      intro k
      have happ := congrArg
        (fun π : Equiv.Perm (Fin (n + 2)) ↦ π k.castSucc) h
      rw [lastPermutation_castSucc, lastPermutation_castSucc] at happ
      exact Fin.succAbove_right_injective happ
    subst τ'
    rfl
  · -- Both finite parameter spaces have cardinality `(n + 2)!`.
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_perm,
      Nat.factorial_succ]

/-- Helper for Remark 50.2: every retained prefix of a last-vertex
permutation is the corresponding facet prefix included by `r.succAbove`. -/
lemma flagPrefix_lastPermutation_castSucc (n : ℕ) (r : Fin (n + 2))
    (τ : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 1)) :
    flagPrefix (lastPermutation n r τ) k.castSucc =
      (flagPrefix τ k).image r.succAbove := by
  -- Reindex the ambient initial segment by `Fin.castSucc`, then compute pointwise.
  unfold flagPrefix
  rw [← Fin.finsetImage_castSucc_Iic k, Finset.image_image,
    Finset.image_image]
  apply Finset.image_congr
  intro j _
  exact lastPermutation_castSucc n r τ j

/-- Helper for Remark 50.2: deleting the final rank of a last-vertex flag
produces precisely the barycentric flag on the selected facet. -/
lemma flagFace_lastPermutation_last (n : ℕ) (r : Fin (n + 2))
    (τ : Equiv.Perm (Fin (n + 1))) :
    flagFace n (lastPermutation n r τ) (Fin.last (n + 1)) =
      facetFlag n r τ := by
  -- The last-face inclusion is `Fin.castSucc`; apply the retained-prefix formula.
  funext k
  simpa only [flagFace, facetFlag, Fin.succAbove_last_apply] using
    flagPrefix_lastPermutation_castSucc n r τ k

/-- Helper for Remark 50.2: arbitrary mod-two weights on final flag faces
reindex as weights on flags of the original facets. -/
lemma lastFaceWeight_sum (n : ℕ)
    (W : (Fin (n + 1) → Finset (Fin (n + 2))) → ZMod 2) :
    ∑ σ : Equiv.Perm (Fin (n + 2)),
        W (flagFace n σ (Fin.last (n + 1))) =
      ∑ r : Fin (n + 2), ∑ τ : Equiv.Perm (Fin (n + 1)),
        W (facetFlag n r τ) := by
  classical
  let e := fun p : Fin (n + 2) × Equiv.Perm (Fin (n + 1)) ↦
    lastPermutation n p.1 p.2
  have he : Function.Bijective e := lastPermutation_bijective n
  -- Reindex by the last vertex and normalize each final face.
  calc
    ∑ σ : Equiv.Perm (Fin (n + 2)),
        W (flagFace n σ (Fin.last (n + 1))) =
      ∑ p : Fin (n + 2) × Equiv.Perm (Fin (n + 1)),
        W (flagFace n (e p) (Fin.last (n + 1))) := by
      exact (Fintype.sum_bijective e he _ _ (fun _ ↦ rfl)).symm
    _ = ∑ p : Fin (n + 2) × Equiv.Perm (Fin (n + 1)),
        W (facetFlag n p.1 p.2) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [flagFace_lastPermutation_last]
    _ = ∑ r : Fin (n + 2), ∑ τ : Equiv.Perm (Fin (n + 1)),
        W (facetFlag n r τ) := by
      rw [Fintype.sum_prod_type]

/-- Helper for Remark 50.2: the arbitrary weighted mod-two boundary of all
maximal permutation flags is the subdivision of the original boundary. -/
lemma modTwoBoundary (n : ℕ)
    (W : (Fin (n + 1) → Finset (Fin (n + 2))) → ZMod 2) :
    ∑ σ : Equiv.Perm (Fin (n + 2)),
        ∑ r : Fin (n + 2), W (flagFace n σ r) =
      ∑ r : Fin (n + 2), ∑ τ : Equiv.Perm (Fin (n + 1)),
        W (facetFlag n r τ) := by
  classical
  -- Split every boundary into internal faces and its final face.
  calc
    ∑ σ : Equiv.Perm (Fin (n + 2)),
        ∑ r : Fin (n + 2), W (flagFace n σ r) =
      ∑ σ : Equiv.Perm (Fin (n + 2)),
        ((∑ r : Fin (n + 1), W (flagFace n σ r.castSucc)) +
          W (flagFace n σ (Fin.last (n + 1)))) := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [Fin.sum_univ_castSucc]
    _ = (∑ σ : Equiv.Perm (Fin (n + 2)),
          ∑ r : Fin (n + 1), W (flagFace n σ r.castSucc)) +
        ∑ σ : Equiv.Perm (Fin (n + 2)),
          W (flagFace n σ (Fin.last (n + 1))) := by
      rw [Finset.sum_add_distrib]
    _ = ∑ σ : Equiv.Perm (Fin (n + 2)),
        W (flagFace n σ (Fin.last (n + 1))) := by
      rw [interiorBoundaryWeight_sum_eq_zero, zero_add]
    _ = ∑ r : Fin (n + 2), ∑ τ : Equiv.Perm (Fin (n + 1)),
        W (facetFlag n r τ) := lastFaceWeight_sum n W

end Remark50_2.BarycentricParity
