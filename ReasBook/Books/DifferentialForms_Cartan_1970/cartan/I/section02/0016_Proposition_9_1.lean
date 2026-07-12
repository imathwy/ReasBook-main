import DifferentialForms_Cartan_1970.I.section01.«0014_Proposition_7_1»
import DifferentialForms_Cartan_1970.I.section02.«0004_Definition_I_2_extra_3»

-- Declarations for this item will be appended below by the statement pipeline.

open PowerSeries
open scoped PowerSeries

universe u

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

-- Source/core/bridge triage:
-- * source-facing: Proposition 9.1 on scalar substitution right inverses;
-- * core/canonical: Mathlib's analytic inverse-radius theorem
--   `FormalMultilinearSeries.radius_rightInv_pos_of_radius_pos`, specialized through
--   `PowerSeries.substInvOfIsUnit`;
-- * bridge/view: the section01 theorem
--   `powerSeries_subst_right_inverse_eq_substInvOfIsUnit`, which identifies any source-facing
--   right inverse with the canonical owner.

/-- Helper for Proposition 9.1: a scalar formal multilinear series is determined by its scalar
coefficients. -/
lemma ofScalars_coeff_eq_self (p : FormalMultilinearSeries 𝕜 𝕜 𝕜) :
    FormalMultilinearSeries.ofScalars 𝕜 p.coeff = p := by
  -- Compare both scalar series through the canonical `mkPiRing` normal form.
  ext n
  rw [← FormalMultilinearSeries.mkPiRing_coeff_eq p n,
    ← FormalMultilinearSeries.mkPiRing_coeff_eq (FormalMultilinearSeries.ofScalars 𝕜 p.coeff) n,
    FormalMultilinearSeries.coeff_ofScalars]

/-- Helper for Proposition 9.1: if the inner series has vanishing constant term, the `m`th
coefficient of a substitution only depends on outer degrees at most `m`. -/
lemma coeff_subst_eq_sum_range_of_constantCoeff_zero
    {A U : 𝕜⟦X⟧}
    (hU0 : U.constantCoeff = 0)
    (m : ℕ) :
    coeff m (A.subst U) = ∑ d ∈ Finset.range (m + 1), coeff d A * coeff m (U ^ d) := by
  -- Replace the infinite substitution formula by a finite range using the order bound on `U ^ d`.
  have hU : HasSubst U := HasSubst.of_constantCoeff_zero' hU0
  rw [coeff_subst' hU, finsum_eq_sum_of_support_subset (s := Finset.range (m + 1))]
  · simp [smul_eq_mul]
  · intro d hd
    rw [Function.mem_support] at hd
    by_contra hdm
    have hdm' : ¬ d < m + 1 := by
      simpa [Finset.mem_range] using hdm
    have hmd : m < d := Nat.lt_of_lt_of_le (Nat.lt_succ_self m) (Nat.not_lt.mp hdm')
    have hzero : coeff m (U ^ d) = 0 := by
      -- A power with exponent `d > m` has order strictly larger than `m`.
      apply coeff_of_lt_order
      exact lt_of_lt_of_le (by exact_mod_cast hmd) (le_order_pow_of_constantCoeff_eq_zero d hU0)
    exact hd <| by simp [hzero]

/-- Helper for Proposition 9.1: composing scalar owners expands to the expected sum over
compositions of the target degree. -/
lemma ofScalars_comp_coeff_eq_sum_compositions
    (A U : 𝕜⟦X⟧)
    (m : ℕ) :
    ((FormalMultilinearSeries.ofScalars 𝕜 (fun n ↦ coeff n A)).comp
      (FormalMultilinearSeries.ofScalars 𝕜 (fun n ↦ coeff n U))).coeff m =
      ∑ c : Composition m, coeff c.length A * ∏ i : Fin c.length, coeff (c.blocksFun i) U := by
  -- Unfold the composition coefficient and read each multilinear term through its scalar
  -- coefficient at the all-ones vector.
  rw [FormalMultilinearSeries.coeff, FormalMultilinearSeries.comp,
    ContinuousMultilinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro c hc
  rw [FormalMultilinearSeries.compAlongComposition_apply,
    FormalMultilinearSeries.apply_eq_prod_smul_coeff]
  simp only [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul]
  rw [mul_comm]
  -- Every block of the composition also sees only ones, so each inner term is its scalar
  -- coefficient.
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [FormalMultilinearSeries.applyComposition, FormalMultilinearSeries.apply_eq_prod_smul_coeff]
  simp [FormalMultilinearSeries.coeff_ofScalars]

/-- Helper for Proposition 9.1: the coefficient of `U ^ d` can be rewritten as a sum over ordered
`d`-tuples of nonnegative integers with total sum `m`. -/
lemma coeff_pow_eq_sum_fin_antidiagonal
    (U : 𝕜⟦X⟧)
    (m d : ℕ) :
    coeff m (U ^ d) = ∑ e ∈ Finset.finAntidiagonal d m, ∏ i : Fin d, coeff (e i) U := by
  classical
  -- Rewrite the power as a product indexed by `Fin d`, then transfer the antidiagonal from
  -- finitely supported functions to ordinary functions on the finite type `Fin d`.
  calc
    coeff m (U ^ d) = coeff m (∏ _i : Fin d, U) := by simp
    _ = ∑ l ∈ Finset.finsuppAntidiag (Finset.univ : Finset (Fin d)) m,
          ∏ i ∈ (Finset.univ : Finset (Fin d)), coeff (l i) U := by
        simpa using PowerSeries.coeff_prod (f := fun _ : Fin d => U) (d := m)
          (s := (Finset.univ : Finset (Fin d)))
    _ = ∑ e ∈ (Finset.finsuppAntidiag (Finset.univ : Finset (Fin d)) m).map
          Finsupp.equivFunOnFinite.toEmbedding, ∏ i : Fin d, coeff (e i) U := by
        rw [Finset.sum_map]
        apply Finset.sum_congr rfl
        intro l hl
        simp
    _ = ∑ e ∈ Finset.finAntidiagonal d m, ∏ i : Fin d, coeff (e i) U := by
        congr 1
        ext e
        simp [Finset.mem_finAntidiagonal, Finset.mem_finsuppAntidiag]

/-- Helper for Proposition 9.1: an antidiagonal tuple with one zero entry contributes `0` when
`U(0) = 0`. -/
lemma fin_antidiagonal_prod_coeff_eq_zero_of_has_zero
    {U : 𝕜⟦X⟧}
    (hU0 : U.constantCoeff = 0)
    {m d : ℕ} {e : Fin d → ℕ}
    (_he : e ∈ Finset.finAntidiagonal d m)
    (hzero : ∃ i, e i = 0) :
    (∏ i : Fin d, coeff (e i) U) = 0 := by
  rcases hzero with ⟨i, hi⟩
  -- The chosen zero coordinate forces the whole product to vanish.
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [hi, coeff_zero_eq_constantCoeff, hU0]

/-- Helper for Proposition 9.1: when `U(0) = 0`, only strictly positive blocks contribute to
`coeff m (U ^ d)`. -/
lemma coeff_pow_eq_sum_positive_tuples_of_constantCoeff_zero
    {U : 𝕜⟦X⟧}
    (hU0 : U.constantCoeff = 0)
    (m d : ℕ) :
    coeff m (U ^ d) =
      ∑ e ∈ Fintype.piFinset (fun _ : Fin d => Finset.Ico 1 (m + 1)),
        if (∑ i, e i = m) then ∏ i : Fin d, coeff (e i) U else 0 := by
  have hfilter :
      (Finset.finAntidiagonal d m).filter (fun e => ∀ i : Fin d, 1 ≤ e i) =
        (Fintype.piFinset (fun _ : Fin d => Finset.Ico 1 (m + 1))).filter
          (fun e => ∑ i, e i = m) := by
    -- On the antidiagonal, positivity is equivalent to membership in `Ico 1 (m + 1)`.
    ext e
    constructor
    · intro he
      rcases Finset.mem_filter.mp he with ⟨heanti, hpos⟩
      refine Finset.mem_filter.mpr ?_
      refine ⟨?_, ?_⟩
      · simp only [Fintype.mem_piFinset, Finset.mem_Ico]
        intro i
        refine ⟨hpos i, ?_⟩
        have hi_le_sum : e i ≤ ∑ j, e j := by
          exact Finset.single_le_sum (fun j _ ↦ Nat.zero_le _) (Finset.mem_univ i)
        have hi_le_m : e i ≤ m := by
          exact hi_le_sum.trans <| le_of_eq (Finset.mem_finAntidiagonal.mp heanti)
        exact Nat.lt_succ_of_le hi_le_m
      · exact Finset.mem_finAntidiagonal.mp heanti
    · intro he
      rcases Finset.mem_filter.mp he with ⟨hepi, hsum⟩
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · exact Finset.mem_finAntidiagonal.mpr hsum
      · have hepi' : ∀ i : Fin d, e i ∈ Finset.Ico 1 (m + 1) := by
          simpa [Fintype.mem_piFinset] using hepi
        intro i
        exact (Finset.mem_Ico.mp (hepi' i)).1
  -- First prune the zero coordinates from the antidiagonal sum, then rewrite the surviving
  -- positive tuples as the source-faithful `Ico` product domain.
  calc
    coeff m (U ^ d) = ∑ e ∈ Finset.finAntidiagonal d m, ∏ i : Fin d, coeff (e i) U := by
      exact coeff_pow_eq_sum_fin_antidiagonal U m d
    _ = ∑ e ∈ Finset.finAntidiagonal d m,
          if ∀ i : Fin d, 1 ≤ e i then ∏ i : Fin d, coeff (e i) U else 0 := by
        apply Finset.sum_congr rfl
        intro e he
        by_cases hpos : ∀ i : Fin d, 1 ≤ e i
        · simp [hpos]
        · rcases not_forall.mp hpos with ⟨i, hi⟩
          have hi0 : e i = 0 := by
            apply Nat.eq_zero_of_not_pos
            simpa [Nat.succ_le_iff] using hi
          simp [hpos, fin_antidiagonal_prod_coeff_eq_zero_of_has_zero hU0 he ⟨i, hi0⟩]
    _ = ∑ e ∈ (Finset.finAntidiagonal d m).filter (fun e => ∀ i : Fin d, 1 ≤ e i),
          ∏ i : Fin d, coeff (e i) U := by
        rw [Finset.sum_filter]
    _ = ∑ e ∈ (Fintype.piFinset (fun _ : Fin d => Finset.Ico 1 (m + 1))).filter
          (fun e => ∑ i, e i = m), ∏ i : Fin d, coeff (e i) U := by
        rw [hfilter]
    _ = ∑ e ∈ Fintype.piFinset (fun _ : Fin d => Finset.Ico 1 (m + 1)),
          if (∑ i, e i = m) then ∏ i : Fin d, coeff (e i) U else 0 := by
        rw [Finset.sum_filter]

/-- Helper for Proposition 9.1: grouping compositions by their length recovers the full
composition sum. -/
lemma sum_compositions_grouped_by_length
    (m : ℕ)
    (F : Composition m → 𝕜) :
    ∑ d ∈ Finset.range (m + 1),
        ∑ c ∈ Finset.univ.filter (fun c : Composition m => c.length = d), F c =
      ∑ c : Composition m, F c := by
  -- Rewrite each fiber sum by an indicator, then interchange the two finite summations.
  calc
    ∑ d ∈ Finset.range (m + 1),
        ∑ c ∈ Finset.univ.filter (fun c : Composition m => c.length = d), F c =
      ∑ d ∈ Finset.range (m + 1),
        ∑ c : Composition m, if c.length = d then F c else 0 := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [Finset.sum_filter]
    _ = ∑ c : Composition m,
        ∑ d ∈ Finset.range (m + 1), if c.length = d then F c else 0 := by
        rw [Finset.sum_comm]
    _ = ∑ c : Composition m, F c := by
        apply Finset.sum_congr rfl
        intro c hc
        have hlen : c.length ∈ Finset.range (m + 1) := by
          exact Finset.mem_range.mpr <| lt_of_le_of_lt c.length_le (Nat.lt_succ_self m)
        rw [Finset.sum_eq_single_of_mem c.length hlen]
        · simp
        · intro d hd hne
          simp [eq_comm, hne]

/-- Helper for Proposition 9.1: reindexing positive tuples of fixed length by compositions of the
same total degree and length. -/
lemma sum_positive_tuples_eq_sum_compPartialSumSource
    (U : 𝕜⟦X⟧)
    (m d : ℕ) :
    (∑ e ∈ Fintype.piFinset (fun _ : Fin d => Finset.Ico 1 (m + 1)),
      if (∑ i, e i = m) then ∏ i : Fin d, coeff (e i) U else 0) =
      ∑ e ∈ FormalMultilinearSeries.compPartialSumSource d (d + 1) (m + 1),
        if (∑ i, e.2 i = m) then ∏ i : Fin e.1, coeff (e.2 i) U else 0 := by
  -- Expand the source sigma finset and rewrite the sigma-sum in the canonical direction.
  rw [FormalMultilinearSeries.compPartialSumSource, Nat.Ico_succ_singleton]
  rw [← Finset.sum_sigma' ({d} : Finset ℕ)
    (fun n : ℕ => Fintype.piFinset (fun _ : Fin n => Finset.Ico 1 (m + 1)))
    (fun n e => if (∑ i, e i = m) then ∏ i : Fin n, coeff (e i) U else 0)]
  simp

/-- Helper for Proposition 9.1: a sigma-indexed composition belongs to the target partial sum
exactly when its length is the prescribed one. -/
lemma mem_compPartialSumTarget_mk_iff
    (m d : ℕ)
    {c : Composition m} :
    ((Sigma.mk m c : Sigma fun n => Composition n) ∈
        FormalMultilinearSeries.compPartialSumTarget d (d + 1) (m + 1)) ↔
      c.length = d := by
  -- The target inequalities force the composition length into the singleton interval
  -- `[d, d + 1)`, while the block-size bound is automatic for compositions of `m`.
  rw [FormalMultilinearSeries.mem_compPartialSumTarget_iff]
  constructor
  · intro h
    rcases h with ⟨hd, hlt, -⟩
    exact Nat.le_antisymm (Nat.lt_succ_iff.mp hlt) hd
  · intro hlen
    subst hlen
    refine ⟨le_rfl, by simp, ?_⟩
    intro j
    exact lt_of_le_of_lt (c.blocksFun_le j) (Nat.lt_succ_self m)

/-- Helper for Proposition 9.1: filtering the target sigma finset by first coordinate `m`
identifies it with the fixed-length compositions of `m`. -/
lemma compPartialSumTarget_filter_fst_eq_map_compositions_of_length
    (m d : ℕ) :
    (FormalMultilinearSeries.compPartialSumTarget d (d + 1) (m + 1)).filter
        (fun e => e.1 = m) =
      (Finset.univ.filter (fun c : Composition m => c.length = d)).map
        (Function.Embedding.sigmaMk m) := by
  -- Compare membership after splitting on the first sigma coordinate.
  ext e
  rcases e with ⟨n, c⟩
  by_cases hnm : n = m
  · subst n
    constructor
    · intro h
      have hlen : c.length = d := by
        exact mem_compPartialSumTarget_mk_iff m d |>.mp (Finset.mem_filter.mp h).1
      exact Finset.mem_map.mpr ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ c, hlen⟩, rfl⟩
    · intro h
      rcases Finset.mem_map.mp h with ⟨c', hc', hEq⟩
      cases hEq
      exact Finset.mem_filter.mpr ⟨
        mem_compPartialSumTarget_mk_iff m d |>.mpr (Finset.mem_filter.mp hc').2,
        rfl⟩
  · rw [Finset.mem_filter]
    simp only [hnm]
    constructor
    · intro hfalse
      exact False.elim hfalse.2
    · intro hmem
      rcases Finset.mem_map.mp hmem with ⟨x, hx, hxeq⟩
      exact False.elim <| hnm (congrArg Sigma.fst hxeq).symm

/-- Helper for Proposition 9.1: the target sigma-valued sum collapses to a sum over
compositions of `m` with fixed length `d`. -/
lemma sum_compPartialSumTarget_eq_sum_compositions_of_length
    (U : 𝕜⟦X⟧)
    (m d : ℕ) :
    (∑ e ∈ FormalMultilinearSeries.compPartialSumTarget d (d + 1) (m + 1),
      if e.1 = m then ∏ i : Fin e.2.length, coeff (e.2.blocksFun i) U else 0) =
      ∑ c ∈ Finset.univ.filter (fun c : Composition m => c.length = d),
        ∏ i : Fin c.length, coeff (c.blocksFun i) U := by
  -- First remove the `if` by filtering to the `e.1 = m` fiber, then rewrite that fiber
  -- using the fixed-length composition finset from the previous lemma.
  rw [← Finset.sum_filter]
  rw [compPartialSumTarget_filter_fst_eq_map_compositions_of_length]
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro c hc
  rfl

/-- Helper for Proposition 9.1: reindexing positive tuples of fixed length by compositions of the
same total degree and length. -/
lemma sum_positive_tuples_eq_sum_compositions_of_length
    (U : 𝕜⟦X⟧)
    (m d : ℕ) :
    (∑ e ∈ Fintype.piFinset (fun _ : Fin d => Finset.Ico 1 (m + 1)),
      if (∑ i, e i = m) then ∏ i : Fin d, coeff (e i) U else 0) =
      ∑ c ∈ Finset.univ.filter (fun c : Composition m => c.length = d),
        ∏ i : Fin c.length, coeff (c.blocksFun i) U := by
  -- Route correction: the remaining work is the source-faithful change of variables from positive
  -- tuples to compositions, using `compChangeOfVariables_sum`.
  let f : (Σ n : ℕ, Fin n → ℕ) → 𝕜 := fun e =>
    if (∑ i, e.2 i = m) then ∏ i : Fin e.1, coeff (e.2 i) U else 0
  let g : (Σ n, Composition n) → 𝕜 := fun e =>
    if e.1 = m then ∏ i : Fin e.2.length, coeff (e.2.blocksFun i) U else 0
  have hsource :
      (∑ e ∈ Fintype.piFinset (fun _ : Fin d => Finset.Ico 1 (m + 1)),
        if (∑ i, e i = m) then ∏ i : Fin d, coeff (e i) U else 0) =
        ∑ e ∈ FormalMultilinearSeries.compPartialSumSource d (d + 1) (m + 1), f e := by
    -- This is the source-side sigma packaging requested by the change-of-variables theorem.
    simpa [f] using sum_positive_tuples_eq_sum_compPartialSumSource U m d
  have hchange :
      ∑ e ∈ FormalMultilinearSeries.compPartialSumSource d (d + 1) (m + 1), f e =
        ∑ e ∈ FormalMultilinearSeries.compPartialSumTarget d (d + 1) (m + 1), g e := by
    -- `compChangeOfVariables_sum` performs the source-faithful tuple-to-composition reindexing.
    apply FormalMultilinearSeries.compChangeOfVariables_sum d (d + 1) (m + 1)
    rintro ⟨k, blocksFun⟩ H
    have hk :
        (FormalMultilinearSeries.compChangeOfVariables
          d (d + 1) (m + 1) ⟨k, blocksFun⟩ H).2.length =
          k := by
      simp
    have hsum :
        (FormalMultilinearSeries.compChangeOfVariables
          d (d + 1) (m + 1) ⟨k, blocksFun⟩ H).1 =
          ∑ i, blocksFun i := by
      simp [FormalMultilinearSeries.compChangeOfVariables]
    dsimp [f, g]
    by_cases hm : ∑ i, blocksFun i = m
    · have hm' :
          (FormalMultilinearSeries.compChangeOfVariables d (d + 1) (m + 1) ⟨k, blocksFun⟩ H).1 =
            m := by
        simpa [hsum] using hm
      rw [if_pos hm, if_pos hm']
      congr 2 <;> try rw [hk]
      rw [Fin.heq_fun_iff hk.symm]
      intro j
      rw [FormalMultilinearSeries.compChangeOfVariables_blocksFun]
    · have hm' :
          ¬(FormalMultilinearSeries.compChangeOfVariables d (d + 1) (m + 1) ⟨k, blocksFun⟩ H).1 =
            m := by
        simpa [hsum] using hm
      rw [if_neg hm, if_neg hm']
  have htarget :
      ∑ e ∈ FormalMultilinearSeries.compPartialSumTarget d (d + 1) (m + 1), g e =
        ∑ c ∈ Finset.univ.filter (fun c : Composition m => c.length = d),
          ∏ i : Fin c.length, coeff (c.blocksFun i) U := by
    -- The new target-side helpers isolate the `e.1 = m` fiber before rewriting the sum.
    simpa [g] using sum_compPartialSumTarget_eq_sum_compositions_of_length U m d
  -- The remaining gap is now exactly the target-side collapse of the sigma-valued target.
  calc
    (∑ e ∈ Fintype.piFinset (fun _ : Fin d => Finset.Ico 1 (m + 1)),
      if (∑ i, e i = m) then ∏ i : Fin d, coeff (e i) U else 0) =
        ∑ e ∈ FormalMultilinearSeries.compPartialSumSource d (d + 1) (m + 1), f e := hsource
    _ = ∑ e ∈ FormalMultilinearSeries.compPartialSumTarget d (d + 1) (m + 1), g e := hchange
    _ =
        ∑ c ∈ Finset.univ.filter (fun c : Composition m => c.length = d),
          ∏ i : Fin c.length, coeff (c.blocksFun i) U := htarget

/-- Helper for Proposition 9.1: scalar substitution coefficients agree with the coefficients of the
composition of the associated scalar formal multilinear series. -/
lemma scalar_subst_coeff_eq_ofScalars_comp_coeff
    (A U : 𝕜⟦X⟧)
    (hU0 : U.constantCoeff = 0)
    (m : ℕ) :
    coeff m (A.subst U) =
      ((FormalMultilinearSeries.ofScalars 𝕜 (fun n ↦ coeff n A)).comp
        (FormalMultilinearSeries.ofScalars 𝕜 (fun n ↦ coeff n U))).coeff m := by
  -- Route correction: both sides are now normalized, respectively, to a finite substitution sum
  -- and to the source-faithful composition sum over `Composition m`; the remaining gap is the
  -- fixed-length bridge between `coeff m (U ^ d)` and compositions of length `d`.
  have hsubst :
      coeff m (A.subst U) = ∑ d ∈ Finset.range (m + 1), coeff d A * coeff m (U ^ d) :=
    coeff_subst_eq_sum_range_of_constantCoeff_zero hU0 m
  have hcomp :
      ((FormalMultilinearSeries.ofScalars 𝕜 (fun n ↦ coeff n A)).comp
        (FormalMultilinearSeries.ofScalars 𝕜 (fun n ↦ coeff n U))).coeff m =
        ∑ c : Composition m, coeff c.length A * ∏ i : Fin c.length, coeff (c.blocksFun i) U :=
    ofScalars_comp_coeff_eq_sum_compositions A U m
  have hpow :
      ∀ d,
        coeff m (U ^ d) =
          ∑ c ∈ Finset.univ.filter (fun c : Composition m => c.length = d),
            ∏ i : Fin c.length, coeff (c.blocksFun i) U := by
    intro d
    -- First pass from `coeff_pow` to positive tuples, then reindex those tuples by compositions.
    calc
      coeff m (U ^ d) =
          ∑ e ∈ Fintype.piFinset (fun _ : Fin d => Finset.Ico 1 (m + 1)),
            if (∑ i, e i = m) then ∏ i : Fin d, coeff (e i) U else 0 := by
        exact coeff_pow_eq_sum_positive_tuples_of_constantCoeff_zero hU0 m d
      _ =
          ∑ c ∈ Finset.univ.filter (fun c : Composition m => c.length = d),
            ∏ i : Fin c.length, coeff (c.blocksFun i) U := by
        exact sum_positive_tuples_eq_sum_compositions_of_length U m d
  -- The scalar substitution sum and the multilinear composition sum now differ only by grouping
  -- the compositions according to their length.
  calc
    coeff m (A.subst U) =
        ∑ d ∈ Finset.range (m + 1),
          ∑ c ∈ Finset.univ.filter (fun c : Composition m => c.length = d),
            coeff d A * ∏ i : Fin c.length, coeff (c.blocksFun i) U := by
      rw [hsubst]
      apply Finset.sum_congr rfl
      intro d hd
      rw [hpow d]
      rw [Finset.mul_sum]
    _ =
        ∑ d ∈ Finset.range (m + 1),
          ∑ c ∈ Finset.univ.filter (fun c : Composition m => c.length = d),
            coeff c.length A * ∏ i : Fin c.length, coeff (c.blocksFun i) U := by
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro c hc
      have hc_len : c.length = d := (Finset.mem_filter.mp hc).2
      simp [hc_len]
    _ = ∑ c : Composition m, coeff c.length A * ∏ i : Fin c.length, coeff (c.blocksFun i) U := by
      simpa using sum_compositions_grouped_by_length m
        (fun c : Composition m => coeff c.length A * ∏ i : Fin c.length, coeff (c.blocksFun i) U)
    _ =
        ((FormalMultilinearSeries.ofScalars 𝕜 (fun n ↦ coeff n A)).comp
          (FormalMultilinearSeries.ofScalars 𝕜 (fun n ↦ coeff n U))).coeff m := hcomp.symm

/-- Helper for Proposition 9.1: truncating a scalar series keeps the coefficients below the
truncation index and kills the higher ones. -/
lemma coeff_truncation_sum_C_mul_X_pow
    (U : 𝕜⟦X⟧)
    (N k : ℕ) :
    coeff k (∑ i : Fin N, C (coeff i U) * X ^ (i : ℕ)) = if k < N then coeff k U else 0 := by
  -- Compute the coefficient termwise, then isolate the unique summand indexed by `k`.
  classical
  rw [map_sum]
  by_cases hk : k < N
  · rw [if_pos hk]
    rw [Finset.sum_eq_single ⟨k, hk⟩]
    · rw [PowerSeries.coeff_C_mul_X_pow]
      simp
    · intro i _ hik
      have hki : k ≠ (i : ℕ) := by
        intro hEq
        apply hik
        exact Fin.ext (by simpa using hEq.symm)
      rw [PowerSeries.coeff_C_mul_X_pow]
      simp [hki]
    · intro hik
      simp at hik
  · rw [if_neg hk]
    apply Finset.sum_eq_zero
    intro i _
    have hki : k ≠ (i : ℕ) := by
      intro hEq
      exact hk (hEq ▸ i.2)
    rw [PowerSeries.coeff_C_mul_X_pow]
    simp [hki]

/-- Helper for Proposition 9.1: scalarizing a truncated scalar series gives the multilinear
prefix determined by the known scalar coefficients. -/
lemma ofScalars_trunc_eq_prefix
    (U : 𝕜⟦X⟧)
    (q : FormalMultilinearSeries 𝕜 𝕜 𝕜)
    (N : ℕ)
    (hprefix : ∀ k < N, coeff k U = q.coeff k) :
    FormalMultilinearSeries.ofScalars 𝕜
        (fun k ↦ coeff k (∑ i : Fin N, C (coeff i U) * X ^ (i : ℕ))) =
      fun k ↦ if k < N then q k else 0 := by
  -- Compare the scalar coefficients first, then rebuild the truncated scalar series.
  have hcoeffs :
      (fun k ↦ coeff k (∑ i : Fin N, C (coeff i U) * X ^ (i : ℕ))) =
        fun k ↦ if k < N then q.coeff k else 0 := by
    funext k
    by_cases hk : k < N
    · rw [coeff_truncation_sum_C_mul_X_pow, if_pos hk, if_pos hk, hprefix k hk]
    · rw [coeff_truncation_sum_C_mul_X_pow, if_neg hk, if_neg hk]
  let qtrunc : FormalMultilinearSeries 𝕜 𝕜 𝕜 := fun k ↦ if k < N then q k else 0
  have hqtrunc_coeff : qtrunc.coeff = fun k ↦ if k < N then q.coeff k else 0 := by
    funext k
    by_cases hk : k < N
    · rw [FormalMultilinearSeries.coeff]
      simp [qtrunc, hk]
    · rw [FormalMultilinearSeries.coeff]
      simp [qtrunc, hk]
  calc
    FormalMultilinearSeries.ofScalars 𝕜
        (fun k ↦ coeff k (∑ i : Fin N, C (coeff i U) * X ^ (i : ℕ))) =
      FormalMultilinearSeries.ofScalars 𝕜 (fun k ↦ if k < N then q.coeff k else 0) := by
        rw [hcoeffs]
    _ = FormalMultilinearSeries.ofScalars 𝕜 qtrunc.coeff := by rw [hqtrunc_coeff.symm]
    _ = qtrunc := ofScalars_coeff_eq_self qtrunc
    _ = fun k ↦ if k < N then q k else 0 := rfl

/-- Helper for Proposition 9.1: the canonical substitution inverse inherits positive radius from
the original scalar series. -/
lemma substInvOfIsUnit_radius_pos_of_radius_pos
    (S : 𝕜⟦X⟧)
    (hS0 : S.constantCoeff = 0)
    (hS1 : IsUnit (coeff 1 S))
    (hSpos : 0 < S.radius) :
    0 < (S.substInvOfIsUnit hS1).radius := by
  let p : FormalMultilinearSeries 𝕜 𝕜 𝕜 := FormalMultilinearSeries.ofScalars 𝕜 fun n ↦ coeff n S
  let q : FormalMultilinearSeries 𝕜 𝕜 𝕜 :=
    p.rightInv (ContinuousLinearEquiv.unitsEquivAut 𝕜 hS1.unit) 0
  let Q : 𝕜⟦X⟧ := PowerSeries.mk fun n ↦ q.coeff n
  let i : 𝕜 ≃L[𝕜] 𝕜 := ContinuousLinearEquiv.unitsEquivAut 𝕜 hS1.unit
  have hp : 0 < p.radius := by
    simpa [p, PowerSeries.radius] using hSpos
  have hp1 : p 1 = (continuousMultilinearCurryFin1 𝕜 𝕜 𝕜).symm i := by
    apply ContinuousMultilinearMap.ext
    intro v
    simp [p, i, FormalMultilinearSeries.ofScalars, mul_comm]
  have hid_coeff :
      ∀ n, (FormalMultilinearSeries.id 𝕜 𝕜 0).coeff n = coeff n (X : 𝕜⟦X⟧) := by
    intro n
    cases n with
    | zero =>
        change ((FormalMultilinearSeries.id 𝕜 𝕜 0) 0 fun _ ↦ (1 : 𝕜)) = coeff 0 (X : 𝕜⟦X⟧)
        rw [FormalMultilinearSeries.id_apply_zero, coeff_zero_X]
    | succ n =>
        cases n with
        | zero =>
            change ((FormalMultilinearSeries.id 𝕜 𝕜 0) 1 fun _ ↦ (1 : 𝕜)) = coeff 1 (X : 𝕜⟦X⟧)
            rw [FormalMultilinearSeries.id_apply_one, coeff_one_X]
        | succ n =>
            change ((FormalMultilinearSeries.id 𝕜 𝕜 0) (n + 2) fun _ ↦ (1 : 𝕜)) =
              coeff (n + 2) (X : 𝕜⟦X⟧)
            rw [FormalMultilinearSeries.id_apply_of_one_lt]
            · simp [coeff_X]
            · omega
  have hcomp : p.comp q = FormalMultilinearSeries.id 𝕜 𝕜 0 := by
    simpa [p, q, i, coeff_zero_eq_constantCoeff, hS0] using
      FormalMultilinearSeries.comp_rightInv p i 0 hp1
  have hQseries : FormalMultilinearSeries.ofScalars 𝕜 (fun n ↦ coeff n Q) = q := by
    simpa [Q] using ofScalars_coeff_eq_self q
  have hQ0 : Q.constantCoeff = 0 := by
    rw [← coeff_zero_eq_constantCoeff]
    change coeff 0 (PowerSeries.mk (fun n ↦ q.coeff n)) = 0
    rw [PowerSeries.coeff_mk, FormalMultilinearSeries.coeff]
    change p.rightInv i 0 0 (fun _ ↦ (1 : 𝕜)) = 0
    rw [FormalMultilinearSeries.rightInv_coeff_zero]
    simp
  have hQ : S.subst Q = X := by
    ext n
    calc
      coeff n (S.subst Q) =
          ((FormalMultilinearSeries.ofScalars 𝕜 (fun m ↦ coeff m S)).comp
            (FormalMultilinearSeries.ofScalars 𝕜 (fun m ↦ coeff m Q))).coeff n := by
        simpa using scalar_subst_coeff_eq_ofScalars_comp_coeff S Q hQ0 n
      _ = (p.comp q).coeff n := by
        rw [hQseries]
      _ = coeff n (X : 𝕜⟦X⟧) := by rw [hcomp, hid_coeff n]
  have hQeq : Q = S.substInvOfIsUnit hS1 :=
    powerSeries_subst_right_inverse_eq_substInvOfIsUnit hQ0 hQ
  have hQrad : 0 < Q.radius := by
    -- The scalar power series extracted from the multilinear right inverse inherits its radius.
    calc
      0 < q.radius := by
        simpa [q, p, i] using
          FormalMultilinearSeries.radius_rightInv_pos_of_radius_pos (p := p) (i := i) (x := 0) hp
      _ = Q.radius := by
        rw [PowerSeries.radius]
        rw [hQseries]
  rw [← hQeq]
  exact hQrad

/-- Proposition 9.1: if a scalar power series `S` has nonzero radius of convergence and `T` is a
compositional right inverse with `T(0) = 0`, then `T` also has nonzero radius of convergence. -/
theorem radius_ne_zero_of_subst_eq_X
    (S T : 𝕜⟦X⟧)
    (hT0 : T.constantCoeff = 0)
    (hST : S.subst T = X)
    (hS : S.radius ≠ 0) :
    T.radius ≠ 0 := by
  -- Replace the source-facing inverse by the canonical substitution inverse from Proposition 7.1.
  rw [powerSeries_subst_right_inverse_eq_substInvOfIsUnit hT0 hST]
  -- The right-inverse equation forces the constant term of `S` to vanish and its linear term to
  -- be a unit, so the canonical inverse theorem applies.
  have hS0 : S.constantCoeff = 0 :=
    (powerSeries_exists_subst_right_inverse_iff.mp ⟨T, hT0, hST⟩).1
  have hS1 : IsUnit (coeff 1 S) :=
    powerSeries_subst_right_inverse_coeff_one_isUnit hT0 hST
  have hSpos : 0 < S.radius := pos_iff_ne_zero.2 hS
  -- The canonical inverse has positive radius, hence in particular nonzero radius.
  exact pos_iff_ne_zero.1 <|
    substInvOfIsUnit_radius_pos_of_radius_pos S hS0 hS1 hSpos
