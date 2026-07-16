import Mathlib
import chapter1_reference_format.Chap01.Proposition_1_4_18

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]

/-- The supremum of the submodules in a finite family with index strictly smaller than `i`. -/
def submodulePrefixSup {n : ℕ} (Vᵢ : Fin n → Submodule R M) (i : Fin n) : Submodule R M :=
  ⨆ j : Fin i.1, Vᵢ (Fin.castLT j (Nat.lt_trans j.isLt i.isLt))

/-- The prefix supremum before the first summand is trivial. -/
theorem submodulePrefixSup_zero {n : ℕ} (Vᵢ : Fin (n + 1) → Submodule R M) :
    submodulePrefixSup Vᵢ 0 = ⊥ := by
  simp [submodulePrefixSup]

/-- Helper for Exercise 1.4.19: truncating a family along `Fin.castSucc` preserves the ordered
prefix supremum. -/
lemma submodulePrefixSup_castSucc {n : ℕ} (Vᵢ : Fin (n + 1) → Submodule R M) (i : Fin n) :
    submodulePrefixSup (fun j : Fin n ↦ Vᵢ j.castSucc) i = submodulePrefixSup Vᵢ i.castSucc := by
  -- Both sides index the same earlier summands; only the bookkeeping on `Fin` differs.
  unfold submodulePrefixSup
  congr

/-- Helper for Exercise 1.4.19: the prefix before the last summand is the supremum of the first
`n` summands. -/
lemma submodulePrefixSup_last_eq_image_sup {n : ℕ} (Vᵢ : Fin (n + 1) → Submodule R M) :
    submodulePrefixSup Vᵢ (Fin.last n) = (Finset.image Fin.castSucc Finset.univ).sup Vᵢ := by
  -- Rewrite the finitary supremum over the image of `Fin.castSucc` back into an `iSup`.
  suffices (⨆ j : Fin n, Vᵢ j.castSucc) = (Finset.image Fin.castSucc Finset.univ).sup Vᵢ by
    simpa [submodulePrefixSup] using this
  rw [Finset.sup_image, Finset.sup_eq_iSup]
  simp

/-- Helper for Exercise 1.4.19: for a finite ordered family, independence is equivalent to each
summand being disjoint from the sum of its predecessors. -/
lemma iSupIndep_iff_prefixSup_disjoint {n : ℕ} (Vᵢ : Fin n → Submodule R M) :
    iSupIndep Vᵢ ↔ ∀ i : Fin n, Disjoint (submodulePrefixSup Vᵢ i) (Vᵢ i) := by
  constructor
  · intro h i
    -- The prefix supremum is bounded by the supremum of all summands indexed away from `i`.
    refine (h i).symm.mono_left ?_
    unfold submodulePrefixSup
    refine iSup_le fun j => ?_
    have hlt :
        Fin.castLT j (Nat.lt_trans j.isLt i.isLt) < i :=
      Fin.lt_def.mpr j.isLt
    exact
      le_iSup_of_le (Fin.castLT j (Nat.lt_trans j.isLt i.isLt)) <|
        le_iSup_of_le (ne_of_lt hlt) le_rfl
  · induction n with
    | zero =>
        intro _
        -- The empty family is independent for formal reasons.
        simp
    | succ n ih =>
        intro hprefix
        let W : Fin n → Submodule R M := fun i ↦ Vᵢ i.castSucc
        have hprefixW : ∀ i : Fin n, Disjoint (submodulePrefixSup W i) (W i) := by
          -- The induction hypothesis sees exactly the first `n` summands.
          intro i
          simpa [W, submodulePrefixSup_castSucc] using hprefix i.castSucc
        have hW : iSupIndep W := ih W hprefixW
        have hs : (Finset.image Fin.castSucc Finset.univ).SupIndep Vᵢ := by
          -- Transport the independence of the truncated family onto its image in `Fin (n + 1)`.
          exact Finset.SupIndep.image ((iSupIndep_iff_supIndep_univ.mp hW))
        have hlast :
            Disjoint (Vᵢ (Fin.last n)) ((Finset.image Fin.castSucc Finset.univ).sup Vᵢ) := by
          -- The last hypothesis is exactly the disjointness needed to insert the final summand.
          simpa [submodulePrefixSup_last_eq_image_sup, disjoint_comm] using hprefix (Fin.last n)
        have huniv : insert (Fin.last n) (Finset.image Fin.castSucc Finset.univ) = Finset.univ := by
          ext i
          simp
        -- Insert the last summand back into the independent prefix family.
        rw [iSupIndep_iff_supIndep_univ]
        simpa [huniv] using Finset.SupIndep.insert hs hlast

-- Proof sketch: prove the forward implication by induction on the index, using the two-summand
-- criterion for the predecessor sum and the next summand; for the converse, repeatedly split off
-- the last summand from the prefix direct sum.
/-- Exercise 1.4.19 (2): assuming the family spans the whole module, it is an internal direct sum
exactly when each summand meets the sum of its predecessors trivially. -/
theorem directSum_isInternal_iff_prefixSup_inf_eq_bot {n : ℕ}
    (Vᵢ : Fin n → Submodule R M) (hsum : (⨆ i, Vᵢ i : Submodule R M) = ⊤) :
    DirectSum.IsInternal Vᵢ ↔
      ∀ i : Fin n, submodulePrefixSup Vᵢ i ⊓ Vᵢ i = ⊥ := by
  -- Replace internality by the canonical `iSupIndep` criterion and then rewrite independence
  -- through the ordered-prefix disjointness lemma proved above.
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  simp [hsum, iSupIndep_iff_prefixSup_disjoint, disjoint_iff]

end

section

/-- Helper for Exercise 1.4.19: the horizontal axis, vertical axis, and diagonal line in `ℝ²`
span the whole plane, are pairwise disjoint, and the diagonal meets the sum of its predecessors
nontrivially. -/
lemma three_coordinate_lines_counterexample_data :
    ∃ W : Fin 3 → Submodule ℝ (ℝ × ℝ),
      (⨆ i, W i : Submodule ℝ (ℝ × ℝ)) = ⊤ ∧
      Pairwise (fun i j ↦ Disjoint (W i) (W j)) ∧
      submodulePrefixSup W (Fin.last 2) ⊓ W (Fin.last 2) ≠ ⊥ := by
  let U : Submodule ℝ (ℝ × ℝ) := ℝ ∙ (((1 : ℝ), (0 : ℝ)) : ℝ × ℝ)
  let V : Submodule ℝ (ℝ × ℝ) := ℝ ∙ (((0 : ℝ), (1 : ℝ)) : ℝ × ℝ)
  let D : Submodule ℝ (ℝ × ℝ) := ℝ ∙ (((1 : ℝ), (1 : ℝ)) : ℝ × ℝ)
  let W : Fin 3 → Submodule ℝ (ℝ × ℝ) := ![U, V, D]
  refine ⟨W, ?_, ?_, ?_⟩
  · -- The first two coordinate axes already span every vector in `ℝ²`.
    refine top_unique ?_
    intro p hp
    have hx0 : ((p.1 : ℝ), (0 : ℝ)) ∈ U := by
      rw [Submodule.mem_span_singleton]
      refine ⟨p.1, ?_⟩
      ext <;> simp
    have hy0 : ((0 : ℝ), (p.2 : ℝ)) ∈ V := by
      rw [Submodule.mem_span_singleton]
      refine ⟨p.2, ?_⟩
      ext <;> simp
    have hx : ((p.1 : ℝ), (0 : ℝ)) ∈ ⨆ i, W i := (le_iSup W 0) hx0
    have hy : ((0 : ℝ), (p.2 : ℝ)) ∈ ⨆ i, W i := (le_iSup W 1) hy0
    have hsum : ((p.1 : ℝ), (0 : ℝ)) + ((0 : ℝ), (p.2 : ℝ)) = p := by
      ext <;> simp
    simpa [hsum] using Submodule.add_mem (⨆ i, W i) hx hy
  · have hUV : Disjoint U V := by
      -- A vector on both coordinate axes must have both coordinates equal to zero.
      rw [disjoint_iff, Submodule.eq_bot_iff]
      intro p hp
      rcases Submodule.mem_inf.mp hp with ⟨hpU, hpV⟩
      rcases Submodule.mem_span_singleton.mp hpU with ⟨a, rfl⟩
      rcases Submodule.mem_span_singleton.mp hpV with ⟨b, hb⟩
      have ha0 : a = 0 := by
        simpa using (congrArg Prod.fst hb).symm
      ext <;> simp [ha0]
    have hUD : Disjoint U D := by
      -- The diagonal has equal coordinates, while the horizontal axis has second coordinate zero.
      rw [disjoint_iff, Submodule.eq_bot_iff]
      intro p hp
      rcases Submodule.mem_inf.mp hp with ⟨hpU, hpD⟩
      rcases Submodule.mem_span_singleton.mp hpU with ⟨a, rfl⟩
      rcases Submodule.mem_span_singleton.mp hpD with ⟨b, hb⟩
      have hb0 : b = 0 := by
        simpa using congrArg Prod.snd hb
      have ha0 : a = 0 := by
        simpa [hb0] using (congrArg Prod.fst hb).symm
      ext <;> simp [ha0]
    have hVD : Disjoint V D := by
      -- The same coordinate comparison works for the vertical axis and the diagonal.
      rw [disjoint_iff, Submodule.eq_bot_iff]
      intro p hp
      rcases Submodule.mem_inf.mp hp with ⟨hpV, hpD⟩
      rcases Submodule.mem_span_singleton.mp hpV with ⟨a, rfl⟩
      rcases Submodule.mem_span_singleton.mp hpD with ⟨b, hb⟩
      have hb0 : b = 0 := by
        simpa using congrArg Prod.fst hb
      have ha0 : a = 0 := by
        simpa [hb0] using (congrArg Prod.snd hb).symm
      ext <;> simp [ha0]
    -- With only three indices, `fin_cases` reduces pairwise disjointness to the three checks above.
    intro i j hij
    fin_cases i <;> fin_cases j
    · contradiction
    · simpa [U, V] using hUV
    · simpa [U, D] using hUD
    · simpa [disjoint_comm, U, V] using hUV
    · contradiction
    · simpa [V, D] using hVD
    · simpa [disjoint_comm, U, D] using hUD
    · simpa [disjoint_comm, V, D] using hVD
    · contradiction
  · intro hbot
    have hU0 : (((1 : ℝ), (0 : ℝ)) : ℝ × ℝ) ∈ U := by
      rw [Submodule.mem_span_singleton]
      refine ⟨1, ?_⟩
      ext <;> simp
    have hV0 : (((0 : ℝ), (1 : ℝ)) : ℝ × ℝ) ∈ V := by
      rw [Submodule.mem_span_singleton]
      refine ⟨1, ?_⟩
      ext <;> simp
    have hU : (((1 : ℝ), (0 : ℝ)) : ℝ × ℝ) ∈ submodulePrefixSup W (Fin.last 2) := by
      -- The first basis vector belongs to the prefix through the first summand.
      unfold submodulePrefixSup
      exact
        (le_iSup
          (fun j : Fin 2 ↦ W (Fin.castLT j (Nat.lt_trans j.isLt (Fin.last 2).isLt))) 0) <|
          by simpa [W] using hU0
    have hV : (((0 : ℝ), (1 : ℝ)) : ℝ × ℝ) ∈ submodulePrefixSup W (Fin.last 2) := by
      -- The second basis vector belongs to the prefix through the second summand.
      unfold submodulePrefixSup
      exact
        (le_iSup
          (fun j : Fin 2 ↦ W (Fin.castLT j (Nat.lt_trans j.isLt (Fin.last 2).isLt))) 1) <|
          by simpa [W] using hV0
    have hprefix : (((1 : ℝ), (1 : ℝ)) : ℝ × ℝ) ∈ submodulePrefixSup W (Fin.last 2) := by
      -- Adding those two prefix vectors gives the diagonal witness.
      have hsum :
          (((1 : ℝ), (0 : ℝ)) : ℝ × ℝ) + (((0 : ℝ), (1 : ℝ)) : ℝ × ℝ) =
            (((1 : ℝ), (1 : ℝ)) : ℝ × ℝ) := by
        ext <;> simp
      simpa [hsum] using Submodule.add_mem (submodulePrefixSup W (Fin.last 2)) hU hV
    have hdiag : (((1 : ℝ), (1 : ℝ)) : ℝ × ℝ) ∈ W (Fin.last 2) := by
      -- The same witness lies on the diagonal line itself.
      change (((1 : ℝ), (1 : ℝ)) : ℝ × ℝ) ∈ D
      rw [Submodule.mem_span_singleton]
      refine ⟨1, ?_⟩
      ext <;> simp
    have hmem :
        (((1 : ℝ), (1 : ℝ)) : ℝ × ℝ) ∈ submodulePrefixSup W (Fin.last 2) ⊓ W (Fin.last 2) := by
      exact Submodule.mem_inf.mpr ⟨hprefix, hdiag⟩
    have hzero : (((1 : ℝ), (1 : ℝ)) : ℝ × ℝ) = 0 := by
      have hbotMem := hmem
      rwa [hbot] at hbotMem
    norm_num at hzero

/-- Helper for Exercise 1.4.19: the horizontal axis in `ℝ²` has two different complementary
lines, namely the vertical axis and the diagonal. -/
lemma horizontal_axis_has_two_distinct_complements :
    IsCompl (ℝ ∙ (((1 : ℝ), (0 : ℝ)) : ℝ × ℝ)) (ℝ ∙ (((0 : ℝ), (1 : ℝ)) : ℝ × ℝ)) ∧
      IsCompl (ℝ ∙ (((1 : ℝ), (0 : ℝ)) : ℝ × ℝ)) (ℝ ∙ (((1 : ℝ), (1 : ℝ)) : ℝ × ℝ)) ∧
      (ℝ ∙ (((0 : ℝ), (1 : ℝ)) : ℝ × ℝ) : Submodule ℝ (ℝ × ℝ)) ≠
        ℝ ∙ (((1 : ℝ), (1 : ℝ)) : ℝ × ℝ) := by
  have hsupUV :
      (ℝ ∙ (((1 : ℝ), (0 : ℝ)) : ℝ × ℝ) : Submodule ℝ (ℝ × ℝ)) ⊔
        (ℝ ∙ (((0 : ℝ), (1 : ℝ)) : ℝ × ℝ) : Submodule ℝ (ℝ × ℝ)) = ⊤ := by
    -- Split any vector into its horizontal and vertical parts.
    refine top_unique ?_
    intro p hp
    have hx : ((p.1 : ℝ), (0 : ℝ)) ∈
        (ℝ ∙ (((1 : ℝ), (0 : ℝ)) : ℝ × ℝ) : Submodule ℝ (ℝ × ℝ)) := by
      rw [Submodule.mem_span_singleton]
      refine ⟨p.1, ?_⟩
      ext <;> simp
    have hy : ((0 : ℝ), (p.2 : ℝ)) ∈
        (ℝ ∙ (((0 : ℝ), (1 : ℝ)) : ℝ × ℝ) : Submodule ℝ (ℝ × ℝ)) := by
      rw [Submodule.mem_span_singleton]
      refine ⟨p.2, ?_⟩
      ext <;> simp
    have hsum : ((p.1 : ℝ), (0 : ℝ)) + ((0 : ℝ), (p.2 : ℝ)) = p := by
      ext <;> simp
    simpa [hsum] using Submodule.add_mem_sup hx hy
  have hinfUV :
      (ℝ ∙ (((1 : ℝ), (0 : ℝ)) : ℝ × ℝ) : Submodule ℝ (ℝ × ℝ)) ⊓
        (ℝ ∙ (((0 : ℝ), (1 : ℝ)) : ℝ × ℝ) : Submodule ℝ (ℝ × ℝ)) = ⊥ := by
    -- The two coordinate axes only meet at the origin.
    rw [Submodule.eq_bot_iff]
    intro p hp
    rcases Submodule.mem_inf.mp hp with ⟨hpU, hpV⟩
    rcases Submodule.mem_span_singleton.mp hpU with ⟨a, rfl⟩
    rcases Submodule.mem_span_singleton.mp hpV with ⟨b, hb⟩
    have ha0 : a = 0 := by
      simpa using (congrArg Prod.fst hb).symm
    ext <;> simp [ha0]
  have hsupUD :
      (ℝ ∙ (((1 : ℝ), (0 : ℝ)) : ℝ × ℝ) : Submodule ℝ (ℝ × ℝ)) ⊔
        (ℝ ∙ (((1 : ℝ), (1 : ℝ)) : ℝ × ℝ) : Submodule ℝ (ℝ × ℝ)) = ⊤ := by
    -- Split `(x, y)` into `(x - y, 0)` on the horizontal axis and `(y, y)` on the diagonal.
    refine top_unique ?_
    intro p hp
    have hx : ((p.1 - p.2 : ℝ), (0 : ℝ)) ∈
        (ℝ ∙ (((1 : ℝ), (0 : ℝ)) : ℝ × ℝ) : Submodule ℝ (ℝ × ℝ)) := by
      rw [Submodule.mem_span_singleton]
      refine ⟨p.1 - p.2, ?_⟩
      ext <;> simp
    have hd : ((p.2 : ℝ), (p.2 : ℝ)) ∈
        (ℝ ∙ (((1 : ℝ), (1 : ℝ)) : ℝ × ℝ) : Submodule ℝ (ℝ × ℝ)) := by
      rw [Submodule.mem_span_singleton]
      refine ⟨p.2, ?_⟩
      ext <;> simp
    have hsum : ((p.1 - p.2 : ℝ), (0 : ℝ)) + ((p.2 : ℝ), (p.2 : ℝ)) = p := by
      ext
      · simp
      · simp
    simpa [hsum] using Submodule.add_mem_sup hx hd
  have hinfUD :
      (ℝ ∙ (((1 : ℝ), (0 : ℝ)) : ℝ × ℝ) : Submodule ℝ (ℝ × ℝ)) ⊓
        (ℝ ∙ (((1 : ℝ), (1 : ℝ)) : ℝ × ℝ) : Submodule ℝ (ℝ × ℝ)) = ⊥ := by
    -- A diagonal vector on the horizontal axis must have zero second coordinate, hence be zero.
    rw [Submodule.eq_bot_iff]
    intro p hp
    rcases Submodule.mem_inf.mp hp with ⟨hpU, hpD⟩
    rcases Submodule.mem_span_singleton.mp hpU with ⟨a, rfl⟩
    rcases Submodule.mem_span_singleton.mp hpD with ⟨b, hb⟩
    have hb0 : b = 0 := by
      simpa using congrArg Prod.snd hb
    have ha0 : a = 0 := by
      simpa [hb0] using (congrArg Prod.fst hb).symm
    ext <;> simp [ha0]
  have hneq :
      (ℝ ∙ (((0 : ℝ), (1 : ℝ)) : ℝ × ℝ) : Submodule ℝ (ℝ × ℝ)) ≠
        ℝ ∙ (((1 : ℝ), (1 : ℝ)) : ℝ × ℝ) := by
    -- The vector `(0, 1)` lies on the vertical axis but not on the diagonal.
    intro hEq
    have hmem :
        (((0 : ℝ), (1 : ℝ)) : ℝ × ℝ) ∈
          (ℝ ∙ (((1 : ℝ), (1 : ℝ)) : ℝ × ℝ) : Submodule ℝ (ℝ × ℝ)) := by
      rw [← hEq, Submodule.mem_span_singleton]
      refine ⟨1, ?_⟩
      ext <;> simp
    rcases Submodule.mem_span_singleton.mp hmem with ⟨a, ha⟩
    have ha0 : a = 0 := by
      simpa using congrArg Prod.fst ha
    have : (1 : ℝ) = 0 := by
      simpa [ha0] using congrArg Prod.snd ha
    norm_num at this
  -- Proposition 1.4.18 packages the span/intersection data as complementarity.
  refine ⟨?_, ?_, hneq⟩
  · exact (subspace_isCompl_iff_sup_eq_top_and_inf_eq_bot _ _).2 ⟨hsupUV, hinfUV⟩
  · exact (subspace_isCompl_iff_sup_eq_top_and_inf_eq_bot _ _).2 ⟨hsupUD, hinfUD⟩

-- Proof sketch: take the three one-dimensional subspaces of `ℝ²` spanned by `(1, 0)`, `(0, 1)`,
-- and `(1, 1)`; they span `ℝ²` and are pairwise disjoint, but the third line lies in the sum of
-- the first two, so the family is not an internal direct sum.
/-- Exercise 1.4.19 (1): for three subspaces, pairwise disjointness together with total span does
not force an internal direct sum. -/
theorem pairwise_inf_bot_and_iSup_eq_top_not_sufficient_for_internal_direct_sum :
    ∃ W : Fin 3 → Submodule ℝ (ℝ × ℝ),
      (⨆ i, W i : Submodule ℝ (ℝ × ℝ)) = ⊤ ∧
      Pairwise (fun i j ↦ Disjoint (W i) (W j)) ∧
      ¬ DirectSum.IsInternal W := by
  rcases three_coordinate_lines_counterexample_data with ⟨W, htop, hpair, hbad⟩
  refine ⟨W, htop, hpair, ?_⟩
  -- Route correction: pairwise disjointness is not enough once a later summand can lie in the
  -- sum of its predecessors; the ordered prefix criterion detects exactly that failure.
  intro hinternal
  have hcriterion := (directSum_isInternal_iff_prefixSup_inf_eq_bot W htop).mp hinternal
  exact hbad (hcriterion (Fin.last 2))

-- Proof sketch: fix a common summand `U` in `ℝ²`, choose two distinct complements such as the
-- vertical axis and the diagonal line, and observe that both direct sums equal the whole space.
/-- Exercise 1.4.19 (3): internal direct sums do not satisfy cancellation: a subspace can have
two distinct complements. -/
theorem direct_sum_cancellation_counterexample :
    ∃ U W₁ W₂ : Submodule ℝ (ℝ × ℝ),
      IsCompl U W₁ ∧ IsCompl U W₂ ∧ W₁ ≠ W₂ := by
  -- Use the horizontal axis together with the vertical axis and the diagonal line.
  refine ⟨
    ℝ ∙ (((1 : ℝ), (0 : ℝ)) : ℝ × ℝ),
    ℝ ∙ (((0 : ℝ), (1 : ℝ)) : ℝ × ℝ),
    ℝ ∙ (((1 : ℝ), (1 : ℝ)) : ℝ × ℝ),
    ?_⟩
  simpa using horizontal_axis_has_two_distinct_complements

end
