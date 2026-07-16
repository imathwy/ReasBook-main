import DifferentialForms_Cartan_1970.cartan.VII.section29.«0004_Exercise_2».RecursiveCoefficientVariableBounds

open scoped BigOperators MvPowerSeries PowerSeries MvPowerSeries.WithPiTopology
open PowerSeries

universe u

section FormalRecursiveImplicitSystem

variable {𝕜 : Type u} [CommRing 𝕜]
variable {n p : ℕ}

/-- Helper for Cartan section29 0004_Exercise_2: if two solution families agree below the
cutoff `N`, then every coefficient of a pure `x`-monomial of total `x`-degree at least `2`
computed at total parameter degree at most `N` agrees for the two families. -/
lemma coeff_finsuppProd_xPowers_eq_of_lowerCoeffEq
    {x y : Fin n → MvPowerSeries (ParamIndex n p) 𝕜}
    (hx : ∀ j, MvPowerSeries.constantCoeff (x j) = 0)
    (hy : ∀ j, MvPowerSeries.constantCoeff (y j) = 0)
    {N : ℕ}
    (hxy : ∀ j d', paramDegree d' < N →
      MvPowerSeries.coeff d' (x j) = MvPowerSeries.coeff d' (y j))
    (m : Fin n →₀ ℕ)
    (hm : 2 ≤ m.sum fun _ q ↦ q)
    (d : ParamIndex n p →₀ ℕ)
    (hd : paramDegree d ≤ N) :
    MvPowerSeries.coeff d (m.prod fun j q ↦ (x j) ^ q) =
      MvPowerSeries.coeff d (m.prod fun j q ↦ (y j) ^ q) := by
  classical
  -- Expand the coefficient of the finite product and compare each antidiagonal term separately.
  rw [Finsupp.prod, Finsupp.prod, MvPowerSeries.coeff_prod, MvPowerSeries.coeff_prod]
  refine Finset.sum_congr rfl ?_
  intro l hl
  have hl' := Finset.mem_finsuppAntidiag.mp hl
  have hsumdeg : paramDegree d = ∑ j ∈ m.support, paramDegree (l j) := by
    rw [paramDegree_eq_degree, ← hl'.1]
    simp [paramDegree_eq_degree, map_sum]
  by_cases hlt : ∀ j ∈ m.support, paramDegree (l j) < paramDegree d
  · -- If every factor already lives below degree `d`, the low-degree agreement hypothesis applies
    -- directly factorwise.
    refine Finset.prod_congr rfl ?_
    intro j hj
    exact coeff_pow_eq_of_coeff_eq_below_paramDegree (n := n) (p := p)
      (N := N) (fun e he ↦ hxy j e he) (m j) (l j) ((hlt j hj).trans_le hd)
  · -- Otherwise one factor carries the full degree `d`; every other positive `x`-factor is forced
    -- into degree `0`, so the whole product vanishes unless this is the unique factor, in which
    -- case its exponent is at least `2` and the dedicated power lemma applies.
    push Not at hlt
    rcases hlt with ⟨i, hi, hige⟩
    have hil : paramDegree (l i) ≤ paramDegree d := by
      simpa [hsumdeg] using
        (Finset.single_le_sum (fun j hj ↦ Nat.zero_le (paramDegree (l j))) hi :
          paramDegree (l i) ≤ ∑ j ∈ m.support, paramDegree (l j))
    have hieq : paramDegree (l i) = paramDegree d := le_antisymm hil hige
    by_cases hs : (m.support.erase i).Nonempty
    · rcases hs with ⟨k, hk⟩
      have hsplit :
          ∑ j ∈ m.support, paramDegree (l j) =
            paramDegree (l i) + ∑ j ∈ m.support.erase i, paramDegree (l j) := by
        simpa [Finset.sdiff_singleton_eq_erase] using
          (Finset.sum_eq_add_sum_diff_singleton_of_mem (f := fun j ↦ paramDegree (l j)) hi :
            ∑ j ∈ m.support, paramDegree (l j) =
              paramDegree (l i) + ∑ x ∈ m.support \ {i}, paramDegree (l x))
      have hsumErase : ∑ j ∈ m.support.erase i, paramDegree (l j) = 0 := by
        omega
      have hkdeg0 : paramDegree (l k) = 0 := by
        have hle : paramDegree (l k) ≤ ∑ j ∈ m.support.erase i, paramDegree (l j) := by
          simpa using
            (Finset.single_le_sum (fun j hj ↦ Nat.zero_le (paramDegree (l j))) hk :
              paramDegree (l k) ≤ ∑ j ∈ m.support.erase i, paramDegree (l j))
        rw [hsumErase] at hle
        exact Nat.eq_zero_of_le_zero hle
      have hkcoeffx : MvPowerSeries.coeff (l k) ((x k) ^ m k) = 0 := by
        have hk0 : l k = 0 := (paramDegree_eq_zero_iff (n := n) (p := p) (l k)).mp hkdeg0
        have hmk : 0 < m k := Nat.pos_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp ((Finset.mem_erase.mp hk).2))
        simpa [hk0, hmk.ne'] using
          (show MvPowerSeries.coeff 0 ((x k) ^ m k) = 0 by
            rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
            simp [hx k, hmk.ne'])
      have hkcoeffy : MvPowerSeries.coeff (l k) ((y k) ^ m k) = 0 := by
        have hk0 : l k = 0 := (paramDegree_eq_zero_iff (n := n) (p := p) (l k)).mp hkdeg0
        have hmk : 0 < m k := Nat.pos_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp ((Finset.mem_erase.mp hk).2))
        simpa [hk0, hmk.ne'] using
          (show MvPowerSeries.coeff 0 ((y k) ^ m k) = 0 by
            rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
            simp [hy k, hmk.ne'])
      -- The extra positive `x`-factor in the support kills this antidiagonal term on both sides.
      rw [← Finset.mul_prod_erase (s := m.support)
        (f := fun j ↦ MvPowerSeries.coeff (l j) ((x j) ^ m j)) ((Finset.mem_erase.mp hk).2),
        hkcoeffx, zero_mul]
      rw [← Finset.mul_prod_erase (s := m.support)
        (f := fun j ↦ MvPowerSeries.coeff (l j) ((y j) ^ m j)) ((Finset.mem_erase.mp hk).2),
        hkcoeffy, zero_mul]
    · have hsupp : m.support = {i} := by
        apply Finset.eq_singleton_iff_nonempty_unique_mem.mpr
        refine ⟨⟨i, hi⟩, ?_⟩
        intro j hj
        by_contra hji
        exact hs ⟨j, by simpa [hji] using hj⟩
      have hmi : 2 ≤ m i := by
        simpa [Finsupp.sum, hsupp] using hm
      -- In the singleton-support case the whole product is just one power, so the `q ≥ 2`
      -- comparison lemma finishes directly.
      simp [Finsupp.prod, hsupp]
      exact coeff_pow_eq_of_coeff_eq_below_paramDegree_of_two_le
        (n := n) (p := p) (N := paramDegree d) (q := m i) hmi (hx i) (hy i)
        (fun e he ↦ hxy i e (lt_of_lt_of_le he hd)) (l i) hieq

/-- Helper for Cartan section29 0004_Exercise_2: the coefficient of a substituted nonlinear
monomial only depends on solution coefficients of strictly smaller total parameter degree. -/
lemma coeff_finsuppProd_solutionSubst_eq_of_lowerCoeffEq
    {x y : Fin n → MvPowerSeries (ParamIndex n p) 𝕜}
    (hx : ∀ j, MvPowerSeries.constantCoeff (x j) = 0)
    (hy : ∀ j, MvPowerSeries.constantCoeff (y j) = 0)
    (d : ParamIndex n p →₀ ℕ)
    (hxy : ∀ j d', paramDegree d' < paramDegree d →
      MvPowerSeries.coeff d' (x j) = MvPowerSeries.coeff d' (y j))
    (m : (Fin n ⊕ Fin p) →₀ ℕ)
    (hm : 2 ≤ xDegree m) :
    MvPowerSeries.coeff d
      (m.prod fun s q ↦
        (solutionSubst x (higherToSystem s)) ^ q) =
      MvPowerSeries.coeff d
        (m.prod fun s q ↦
          (solutionSubst y (higherToSystem s)) ^ q) := by
  classical
  let mx : Fin n →₀ ℕ :=
    Finsupp.comapDomain Sum.inl m Sum.inl_injective.injOn
  let mz : Fin p →₀ ℕ :=
    Finsupp.comapDomain Sum.inr m Sum.inr_injective.injOn
  have hmdecomp : mx.sumElim mz = m := by
    simpa [mx, mz] using Finsupp.comapDomain_sumElim_comapDomain m
  have hmxsum : mx.sum (fun _ q ↦ q) = xDegree m := by
    rw [Finsupp.sum]
    refine Finset.sum_subset (by simp) ?_
    intro j _ hj
    have hj' : Sum.inl j ∉ m.support := by
      simpa using hj
    simpa [mx, xDegree, Finsupp.mem_support_iff] using hj'
  have hmx : 2 ≤ mx.sum fun _ q ↦ q := by
    rw [hmxsum]
    exact hm
  have hsplitx :
      (m.prod fun s q ↦ (solutionSubst x (higherToSystem s)) ^ q) =
        mx.prod (fun j q ↦ (x j) ^ q) *
          mz.prod (fun k q ↦ (MvPowerSeries.X (Sum.inr k) :
            MvPowerSeries (ParamIndex n p) 𝕜) ^ q) := by
    -- Split the substituted monomial into its `x`-part and its unchanged `z`-part.
    rw [← hmdecomp, Finsupp.prod_sumElim]
    rw [Finsupp.prod, Finsupp.prod]
    refine congrArg₂ (· * ·) ?_ ?_
    · refine Finset.prod_subset (by simp) ?_
      intro j _ hj
      have hmj0 : mx j = 0 := by
        simpa [Finsupp.mem_support_iff] using hj
      simp [solutionSubst, higherToSystem, hmj0]
    · refine Finset.prod_subset (by simp) ?_
      intro k _ hk
      have hmk0 : mz k = 0 := by
        simpa [Finsupp.mem_support_iff] using hk
      simp [solutionSubst, higherToSystem, zToSystem, hmk0]
  have hsplity :
      (m.prod fun s q ↦ (solutionSubst y (higherToSystem s)) ^ q) =
        mx.prod (fun j q ↦ (y j) ^ q) *
          mz.prod (fun k q ↦ (MvPowerSeries.X (Sum.inr k) :
            MvPowerSeries (ParamIndex n p) 𝕜) ^ q) := by
    -- The same decomposition holds for the second candidate solution.
    rw [← hmdecomp, Finsupp.prod_sumElim]
    rw [Finsupp.prod, Finsupp.prod]
    refine congrArg₂ (· * ·) ?_ ?_
    · refine Finset.prod_subset (by simp) ?_
      intro j _ hj
      have hmj0 : mx j = 0 := by
        simpa [Finsupp.mem_support_iff] using hj
      simp [solutionSubst, higherToSystem, hmj0]
    · refine Finset.prod_subset (by simp) ?_
      intro k _ hk
      have hmk0 : mz k = 0 := by
        simpa [Finsupp.mem_support_iff] using hk
      simp [solutionSubst, higherToSystem, zToSystem, hmk0]
  -- After separating the parameter monomial, coefficient comparison reduces to the pure `x`
  -- product from the previous lemma.
  rw [hsplitx, hsplity, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  refine Finset.sum_congr rfl ?_
  intro e he
  have he' := Finset.mem_antidiagonal.mp he
  have hdegle : paramDegree e.1 ≤ paramDegree d := by
    have hsum : paramDegree e.1 + paramDegree e.2 = paramDegree d := by
      rw [← he']
      simp [paramDegree, Finset.sum_add_distrib]
    omega
  congr 1
  exact coeff_finsuppProd_xPowers_eq_of_lowerCoeffEq (n := n) (p := p) hx hy hxy
    mx hmx e.1 hdegle

/-- Helper for Cartan section29 0004_Exercise_2: the degree-`d` coefficient of the nonlinear
substitution depends only on lower-degree solution coefficients. -/
lemma coeff_subst_higher_eq_of_lowerCoeffEq
    (S : RecursiveImplicitSystem 𝕜 n p)
    {x y : Fin n → MvPowerSeries (ParamIndex n p) 𝕜}
    (hx : ∀ j, MvPowerSeries.constantCoeff (x j) = 0)
    (hy : ∀ j, MvPowerSeries.constantCoeff (y j) = 0)
    (j : Fin n) (d : ParamIndex n p →₀ ℕ)
    (hxy : ∀ j' d', paramDegree d' < paramDegree d →
      MvPowerSeries.coeff d' (x j') = MvPowerSeries.coeff d' (y j')) :
    MvPowerSeries.coeff d
      (MvPowerSeries.subst (solutionSubst x)
        (MvPowerSeries.rename (higherToSystem : Fin n ⊕ Fin p → SystemIndex n p) (S.higher j))) =
      MvPowerSeries.coeff d
        (MvPowerSeries.subst (solutionSubst y)
          (MvPowerSeries.rename (higherToSystem : Fin n ⊕ Fin p → SystemIndex n p)
            (S.higher j))) := by
  have hxSubst : MvPowerSeries.HasSubst (solutionSubst x) :=
    solutionSubst_hasSubst x hx
  have hySubst : MvPowerSeries.HasSubst (solutionSubst y) :=
    solutionSubst_hasSubst y hy
  have hxHigherSubst :
      MvPowerSeries.HasSubst (fun s : Fin n ⊕ Fin p ↦ solutionSubst x (higherToSystem s)) := by
    refine MvPowerSeries.hasSubst_of_constantCoeff_zero ?_
    intro s
    cases s with
    | inl i => simpa [solutionSubst, higherToSystem] using hx i
    | inr k => simp [solutionSubst, higherToSystem, zToSystem]
  have hyHigherSubst :
      MvPowerSeries.HasSubst (fun s : Fin n ⊕ Fin p ↦ solutionSubst y (higherToSystem s)) := by
    refine MvPowerSeries.hasSubst_of_constantCoeff_zero ?_
    intro s
    cases s with
    | inl i => simpa [solutionSubst, higherToSystem] using hy i
    | inr k => simp [solutionSubst, higherToSystem, zToSystem]
  have hxComp :
      (fun s : Fin n ⊕ Fin p ↦
        MvPowerSeries.subst (solutionSubst x)
          (MvPowerSeries.X ((higherToSystem : Fin n ⊕ Fin p → SystemIndex n p) s) :
            MvPowerSeries (SystemIndex n p) 𝕜)) =
        fun s : Fin n ⊕ Fin p ↦ solutionSubst x (higherToSystem s) := by
    funext s
    simpa using
      (MvPowerSeries.subst_X hxSubst
        (s := (higherToSystem : Fin n ⊕ Fin p → SystemIndex n p) s))
  have hyComp :
      (fun s : Fin n ⊕ Fin p ↦
        MvPowerSeries.subst (solutionSubst y)
          (MvPowerSeries.X ((higherToSystem : Fin n ⊕ Fin p → SystemIndex n p) s) :
            MvPowerSeries (SystemIndex n p) 𝕜)) =
        fun s : Fin n ⊕ Fin p ↦ solutionSubst y (higherToSystem s) := by
    funext s
    simpa using
      (MvPowerSeries.subst_X hySubst
        (s := (higherToSystem : Fin n ⊕ Fin p → SystemIndex n p) s))
  -- Rewrite both substituted higher remainders as substitutions on `S.higher j` itself so that
  -- each monomial term can be compared through the previous monomial helper.
  calc
    MvPowerSeries.coeff d
        (MvPowerSeries.subst (solutionSubst x)
          (MvPowerSeries.rename (higherToSystem : Fin n ⊕ Fin p → SystemIndex n p) (S.higher j))) =
      MvPowerSeries.coeff d
        (MvPowerSeries.subst
          (fun s : Fin n ⊕ Fin p ↦ solutionSubst x (higherToSystem s))
          (S.higher j)) := by
            rw [show
              MvPowerSeries.rename (higherToSystem : Fin n ⊕ Fin p → SystemIndex n p)
                  (S.higher j) =
                MvPowerSeries.subst
                  (MvPowerSeries.X ∘
                    (higherToSystem : Fin n ⊕ Fin p → SystemIndex n p))
                  (S.higher j) by
                rw [MvPowerSeries.rename_eq_subst]]
            rw [MvPowerSeries.subst_comp_subst_apply
              (MvPowerSeries.HasSubst.X_comp
                (higherToSystem : Fin n ⊕ Fin p → SystemIndex n p)) hxSubst]
            simp [hxComp]
    _ =
      MvPowerSeries.coeff d
        (MvPowerSeries.subst
          (fun s : Fin n ⊕ Fin p ↦ solutionSubst y (higherToSystem s))
          (S.higher j)) := by
            rw [MvPowerSeries.coeff_subst hxHigherSubst, MvPowerSeries.coeff_subst hyHigherSubst]
            refine finsum_congr ?_
            intro m
            by_cases hm : 2 ≤ xDegree m
            · congr 1
              exact coeff_finsuppProd_solutionSubst_eq_of_lowerCoeffEq
                (n := n) (p := p) hx hy d hxy m hm
            · have hmcoeff : MvPowerSeries.coeff m (S.higher j) = 0 := by
                exact S.higher_xDegree_ge_two j m (by omega)
              simp [hmcoeff]
    _ =
      MvPowerSeries.coeff d
        (MvPowerSeries.subst (solutionSubst y)
          (MvPowerSeries.rename (higherToSystem : Fin n ⊕ Fin p → SystemIndex n p)
            (S.higher j))) := by
            rw [show
              MvPowerSeries.rename (higherToSystem : Fin n ⊕ Fin p → SystemIndex n p)
                  (S.higher j) =
                MvPowerSeries.subst
                  (MvPowerSeries.X ∘
                    (higherToSystem : Fin n ⊕ Fin p → SystemIndex n p))
                  (S.higher j) by
                rw [MvPowerSeries.rename_eq_subst]]
            rw [MvPowerSeries.subst_comp_subst_apply
              (MvPowerSeries.HasSubst.X_comp
                (higherToSystem : Fin n ⊕ Fin p → SystemIndex n p)) hySubst]
            simp [hyComp]

/-- Helper for Cartan section29 0004_Exercise_2: the degree-`d` coefficient of the recursive-system substitution is
unchanged after replacing a solution family by its cutoff at total parameter degree
`paramDegree d`. -/
theorem coeff_subst_higher_eq_of_truncatedSolution
    (S : RecursiveImplicitSystem 𝕜 n p)
    (x : Fin n → MvPowerSeries (ParamIndex n p) 𝕜)
    (hx : ∀ j, MvPowerSeries.constantCoeff (x j) = 0)
    (j : Fin n) (d : ParamIndex n p →₀ ℕ)
    (hd : 0 < paramDegree d) :
    MvPowerSeries.coeff d
      (MvPowerSeries.subst
        (solutionSubst (truncatedSolution (n := n) (p := p) (paramDegree d) x))
        (MvPowerSeries.rename (higherToSystem : Fin n ⊕ Fin p → SystemIndex n p) (S.higher j))) =
      MvPowerSeries.coeff d
        (MvPowerSeries.subst
          (solutionSubst x)
          (MvPowerSeries.rename (higherToSystem : Fin n ⊕ Fin p → SystemIndex n p)
            (S.higher j))) := by
  have htrunc :
      ∀ j', MvPowerSeries.constantCoeff
        (truncatedSolution (n := n) (p := p) (paramDegree d) x j') = 0 :=
    truncatedSolution_constantCoeff (n := n) (p := p) (paramDegree d) x
  -- Route correction: instead of reopening the concrete `q = 1` antidiagonal branch, compare the
  -- higher substitution against the cutoff family through the monomial product lemma above.
  exact coeff_subst_higher_eq_of_lowerCoeffEq (n := n) (p := p) (S := S)
    (x := truncatedSolution (n := n) (p := p) (paramDegree d) x) (y := x)
    htrunc hx j d
    (fun j' d' hd' ↦
      coeff_truncatedSolution_eq_of_lt_paramDegree (n := n) (p := p) (paramDegree d) x hx j' d' hd')

/-- Helper for Cartan section29 0004_Exercise_2: the degree-`d` coefficient of the recursive-system substitution is
unchanged after replacing a solution family by its cutoff at total parameter degree
`paramDegree d`. -/
theorem coeff_subst_eq_of_truncatedSolution
    (S : RecursiveImplicitSystem 𝕜 n p)
    (x : Fin n → MvPowerSeries (ParamIndex n p) 𝕜)
    (hx : ∀ j, MvPowerSeries.constantCoeff (x j) = 0)
    (j : Fin n) (d : ParamIndex n p →₀ ℕ)
    (hd : 0 < paramDegree d) :
    MvPowerSeries.coeff d
      (MvPowerSeries.subst
        (solutionSubst (truncatedSolution (n := n) (p := p) (paramDegree d) x))
        (S j)) =
      MvPowerSeries.coeff d
        (MvPowerSeries.subst (solutionSubst x) (S j)) := by
  classical
  let linearPart : MvPowerSeries (SystemIndex n p) 𝕜 :=
    ∑ i : Fin n,
      MvPowerSeries.rename (zToSystem : Fin p → SystemIndex n p) (S.linearCoeff j i) *
        MvPowerSeries.X (Sum.inr (Sum.inl i))
  let higherPart : MvPowerSeries (SystemIndex n p) 𝕜 :=
    MvPowerSeries.rename (higherToSystem : Fin n ⊕ Fin p → SystemIndex n p) (S.higher j)
  let trunc := truncatedSolution (n := n) (p := p) (paramDegree d) x
  have htoSeries : S j = linearPart + higherPart := by
    -- Split the recursive-system series into its linear `Γ(z) y` part and its higher remainder.
    simp [RecursiveImplicitSystem.toSeries, linearPart, higherPart]
  have htruncSubst : MvPowerSeries.HasSubst (solutionSubst trunc) := by
    -- The cutoff solution is still admissible because the positive-degree truncation kills the
    -- constant coefficient.
    simpa [trunc] using truncatedSolution_hasSubst (n := n) (p := p) (paramDegree d) x
  have hxSubst : MvPowerSeries.HasSubst (solutionSubst x) :=
    solutionSubst_hasSubst x hx
  have hlinearCoeff_trunc (i : Fin n) :
      MvPowerSeries.subst (solutionSubst trunc)
        (MvPowerSeries.rename (zToSystem : Fin p → SystemIndex n p) (S.linearCoeff j i)) =
        MvPowerSeries.rename (Sum.inr : Fin p → ParamIndex n p) (S.linearCoeff j i) := by
    -- The linear coefficient series only uses the parameter variables `z`, so substituting the
    -- cutoff solution has no effect on it.
    calc
      MvPowerSeries.subst (solutionSubst trunc)
          (MvPowerSeries.rename (zToSystem : Fin p → SystemIndex n p) (S.linearCoeff j i)) =
          MvPowerSeries.subst (solutionSubst trunc)
            (MvPowerSeries.subst
              (MvPowerSeries.X ∘ (zToSystem : Fin p → SystemIndex n p))
              (S.linearCoeff j i)) := by
                rw [← MvPowerSeries.rename_eq_subst]
      _ = MvPowerSeries.subst
            (fun s ↦
              MvPowerSeries.subst (solutionSubst trunc)
                ((MvPowerSeries.X ∘ (zToSystem : Fin p → SystemIndex n p)) s))
            (S.linearCoeff j i) := by
              rw [MvPowerSeries.subst_comp_subst_apply
                (MvPowerSeries.HasSubst.X_comp (zToSystem : Fin p → SystemIndex n p))
                htruncSubst]
      _ = MvPowerSeries.subst
            (MvPowerSeries.X ∘ (Sum.inr : Fin p → ParamIndex n p))
            (S.linearCoeff j i) := by
              congr 1
              funext s
              simpa [zToSystem] using
                (MvPowerSeries.subst_X htruncSubst
                  (s := (Sum.inr (Sum.inr s) : SystemIndex n p)))
      _ = MvPowerSeries.rename (Sum.inr : Fin p → ParamIndex n p) (S.linearCoeff j i) := by
            simpa using
              (MvPowerSeries.rename_eq_subst (f := (Sum.inr : Fin p → ParamIndex n p))
                (p := S.linearCoeff j i)).symm
  have hlinearCoeff_full (i : Fin n) :
      MvPowerSeries.subst (solutionSubst x)
        (MvPowerSeries.rename (zToSystem : Fin p → SystemIndex n p) (S.linearCoeff j i)) =
        MvPowerSeries.rename (Sum.inr : Fin p → ParamIndex n p) (S.linearCoeff j i) := by
    -- The same parameter-only argument applies to the full solution substitution.
    calc
      MvPowerSeries.subst (solutionSubst x)
          (MvPowerSeries.rename (zToSystem : Fin p → SystemIndex n p) (S.linearCoeff j i)) =
          MvPowerSeries.subst (solutionSubst x)
            (MvPowerSeries.subst
              (MvPowerSeries.X ∘ (zToSystem : Fin p → SystemIndex n p))
              (S.linearCoeff j i)) := by
                rw [← MvPowerSeries.rename_eq_subst]
      _ = MvPowerSeries.subst
            (fun s ↦
              MvPowerSeries.subst (solutionSubst x)
                ((MvPowerSeries.X ∘ (zToSystem : Fin p → SystemIndex n p)) s))
            (S.linearCoeff j i) := by
              rw [MvPowerSeries.subst_comp_subst_apply
                (MvPowerSeries.HasSubst.X_comp (zToSystem : Fin p → SystemIndex n p))
                hxSubst]
      _ = MvPowerSeries.subst
            (MvPowerSeries.X ∘ (Sum.inr : Fin p → ParamIndex n p))
            (S.linearCoeff j i) := by
              congr 1
              funext s
              simpa [zToSystem] using
                (MvPowerSeries.subst_X hxSubst
                  (s := (Sum.inr (Sum.inr s) : SystemIndex n p)))
      _ = MvPowerSeries.rename (Sum.inr : Fin p → ParamIndex n p) (S.linearCoeff j i) := by
            simpa using
              (MvPowerSeries.rename_eq_subst (f := (Sum.inr : Fin p → ParamIndex n p))
                (p := S.linearCoeff j i)).symm
  have hlinear_trunc :
      MvPowerSeries.subst (solutionSubst trunc) linearPart =
        ∑ i : Fin n,
          MvPowerSeries.rename (Sum.inr : Fin p → ParamIndex n p) (S.linearCoeff j i) *
            MvPowerSeries.X (Sum.inl i) := by
    -- Distribute substitution across the finite linear sum and simplify each term.
    calc
      MvPowerSeries.subst (solutionSubst trunc) linearPart =
          ∑ i : Fin n,
            MvPowerSeries.subst (solutionSubst trunc)
              (MvPowerSeries.rename (zToSystem : Fin p → SystemIndex n p) (S.linearCoeff j i) *
                MvPowerSeries.X (Sum.inr (Sum.inl i))) := by
                  rw [show linearPart =
                    ∑ i : Fin n,
                      MvPowerSeries.rename (zToSystem : Fin p → SystemIndex n p)
                          (S.linearCoeff j i) *
                        MvPowerSeries.X (Sum.inr (Sum.inl i)) by
                    rfl]
                  simpa [MvPowerSeries.substAlgHom_apply] using
                    (map_sum (MvPowerSeries.substAlgHom htruncSubst)
                      (fun i : Fin n ↦
                        MvPowerSeries.rename (zToSystem : Fin p → SystemIndex n p)
                            (S.linearCoeff j i) *
                          MvPowerSeries.X (Sum.inr (Sum.inl i)))
                      Finset.univ)
      _ = ∑ i : Fin n,
            MvPowerSeries.rename (Sum.inr : Fin p → ParamIndex n p) (S.linearCoeff j i) *
              MvPowerSeries.X (Sum.inl i) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                rw [MvPowerSeries.subst_mul htruncSubst, hlinearCoeff_trunc]
                rw [MvPowerSeries.subst_X htruncSubst]
                simp [solutionSubst]
  have hlinear_full :
      MvPowerSeries.subst (solutionSubst x) linearPart =
        ∑ i : Fin n,
          MvPowerSeries.rename (Sum.inr : Fin p → ParamIndex n p) (S.linearCoeff j i) *
            MvPowerSeries.X (Sum.inl i) := by
    -- The same simplification shows that the full substitution produces the identical linear sum.
    calc
      MvPowerSeries.subst (solutionSubst x) linearPart =
          ∑ i : Fin n,
            MvPowerSeries.subst (solutionSubst x)
              (MvPowerSeries.rename (zToSystem : Fin p → SystemIndex n p) (S.linearCoeff j i) *
                MvPowerSeries.X (Sum.inr (Sum.inl i))) := by
                  rw [show linearPart =
                    ∑ i : Fin n,
                      MvPowerSeries.rename (zToSystem : Fin p → SystemIndex n p)
                          (S.linearCoeff j i) *
                        MvPowerSeries.X (Sum.inr (Sum.inl i)) by
                    rfl]
                  simpa [MvPowerSeries.substAlgHom_apply] using
                    (map_sum (MvPowerSeries.substAlgHom hxSubst)
                      (fun i : Fin n ↦
                        MvPowerSeries.rename (zToSystem : Fin p → SystemIndex n p)
                            (S.linearCoeff j i) *
                          MvPowerSeries.X (Sum.inr (Sum.inl i)))
                      Finset.univ)
      _ = ∑ i : Fin n,
            MvPowerSeries.rename (Sum.inr : Fin p → ParamIndex n p) (S.linearCoeff j i) *
              MvPowerSeries.X (Sum.inl i) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                rw [MvPowerSeries.subst_mul hxSubst, hlinearCoeff_full]
                rw [MvPowerSeries.subst_X hxSubst]
                simp [solutionSubst]
  -- Route correction: after splitting off the linear part, the only remaining work is the
  -- nonlinear cutoff-invariance statement for the higher remainder.
  rw [htoSeries, MvPowerSeries.subst_add htruncSubst, MvPowerSeries.subst_add hxSubst]
  change
    MvPowerSeries.coeff d (MvPowerSeries.subst (solutionSubst trunc) linearPart) +
        MvPowerSeries.coeff d (MvPowerSeries.subst (solutionSubst trunc) higherPart) =
      MvPowerSeries.coeff d (MvPowerSeries.subst (solutionSubst x) linearPart) +
        MvPowerSeries.coeff d (MvPowerSeries.subst (solutionSubst x) higherPart)
  congr 1
  · rw [hlinear_trunc, hlinear_full]
  · simpa [higherPart, trunc] using
      coeff_subst_higher_eq_of_truncatedSolution (n := n) (p := p) (S := S) (x := x) hx j d hd

/-- Exercise 2 (1): for the recursive system `(3)`, the coefficients of a formal solution `(4)`
are characterized by a family of integer-coefficient polynomials in the coefficients of `(3)` and
in lower-total-degree coefficients of the same solution. -/
theorem exists_recursive_coefficient_polynomials
    (S : RecursiveImplicitSystem 𝕜 n p) :
    ∃ Q : Fin n → (ParamIndex n p →₀ ℕ) → MvPolynomial (RecursiveCoeffVar n p) ℤ,
      (∀ j d u,
        u ∈ (Q j d).vars →
          match u with
          | Sum.inl _ => True
          | Sum.inr ⟨_, d'⟩ =>
              paramDegree d' < paramDegree d) ∧
      ∀ x : Fin n → MvPowerSeries (ParamIndex n p) 𝕜,
        FormalImplicitSolution S x ↔
          RecursiveCoefficientRecurrence S Q x := by
  classical
  let Q : Fin n → (ParamIndex n p →₀ ℕ) → MvPolynomial (RecursiveCoeffVar n p) ℤ :=
    recursiveCoefficientPolynomial (n := n) (p := p)
  refine ⟨Q, ?_, ?_⟩
  · intro j d u hu
    -- Route correction: the variable bound is read directly from the existing universal cutoff
    -- polynomial, rather than by redesigning the universal system encoding.
    cases u with
    | inl a =>
        trivial
    | inr a =>
        simpa [Q] using
          vars_recursiveCoefficientPolynomial (n := n) (p := p) j d (Sum.inr a) hu
  · intro x
    constructor
    · intro hx
      refine ⟨hx.constantCoeff_eq_zero, ?_⟩
      intro j d hd
      -- Evaluate the universal degree-`d` coefficient polynomial on the concrete cutoff solution.
      rw [show Q j d =
        recursiveCoefficientPolynomial (n := n) (p := p) j d by rfl]
      rw [eval_recursiveCoefficientPolynomial (S := S) (x := x) (j := j) (d := d)]
      -- The positive-degree coefficient is cutoff-invariant, so the recursive polynomial computes
      -- the same coefficient as the full substitution appearing in the formal-solution equation.
      simpa [hx.eq_subst j] using
        (coeff_subst_eq_of_truncatedSolution (n := n) (p := p) (S := S) (x := x)
          hx.constantCoeff_eq_zero j d hd).symm
    · intro hx
      refine ⟨hx.constantCoeff_eq_zero, ?_⟩
      intro j
      ext d
      by_cases hd0 : paramDegree d = 0
      · -- The constant coefficient vanishes on both sides.
        have hd_eq : d = 0 := (paramDegree_eq_zero_iff (n := n) (p := p) d).mp hd0
        subst hd_eq
        rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
          MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hx.constantCoeff_eq_zero,
          MvPowerSeries.constantCoeff_subst_eq_zero]
        · exact solutionSubst_hasSubst x hx.constantCoeff_eq_zero
        · intro s
          cases s with
          | inl j' =>
              exact hx.constantCoeff_eq_zero j'
          | inr u =>
              simp [solutionSubst]
        · -- Each right-hand side series has zero constant coefficient by construction.
          simpa using S.constantCoeff_toSeries j
      · have hd : 0 < paramDegree d := Nat.pos_iff_ne_zero.mpr hd0
        -- Reduce the positive-degree coefficient equality to the same cutoff substitution formula.
        rw [hx.coeff_eq_eval j d hd]
        rw [show Q j d =
          recursiveCoefficientPolynomial (n := n) (p := p) j d by rfl]
        rw [eval_recursiveCoefficientPolynomial (S := S) (x := x) (j := j) (d := d)]
        -- The same cutoff invariance identifies the recurrence value with the full substitution
        -- coefficient, which closes the positive-degree branch of the extensionality proof.
        exact coeff_subst_eq_of_truncatedSolution (n := n) (p := p) (S := S) (x := x)
          hx.constantCoeff_eq_zero j d hd

/-- Helper for Cartan section29 0004_Exercise_2: evaluating a recursive coefficient polynomial is
unchanged when two candidate solutions agree on all strictly lower total parameter degrees used by
that polynomial. -/
lemma evalRecursiveCoefficientPolynomial_eq_of_lowerCoeffEq
    (S : RecursiveImplicitSystem 𝕜 n p)
    {Q : Fin n → (ParamIndex n p →₀ ℕ) → MvPolynomial (RecursiveCoeffVar n p) ℤ}
    (hQvars : ∀ j d u,
      u ∈ (Q j d).vars →
        match u with
        | Sum.inl _ => True
        | Sum.inr ⟨_, d'⟩ => paramDegree d' < paramDegree d)
    {x y : Fin n → MvPowerSeries (ParamIndex n p) 𝕜}
    {j : Fin n} {d : ParamIndex n p →₀ ℕ}
    (hxy : ∀ j' d', paramDegree d' < paramDegree d →
      MvPowerSeries.coeff d' (x j') = MvPowerSeries.coeff d' (y j')) :
    MvPolynomial.eval₂ (Int.castRingHom 𝕜) (recursiveCoeffAssignment S x) (Q j d) =
      MvPolynomial.eval₂ (Int.castRingHom 𝕜) (recursiveCoeffAssignment S y) (Q j d) := by
  -- The variable bound on `Q j d` reduces the comparison to the lower-degree solution
  -- coefficients, where `x` and `y` already agree by hypothesis.
  apply MvPolynomial.eval₂Hom_congr' rfl
  · intro u hu _
    cases u with
    | inl a =>
        cases a <;> rfl
    | inr a =>
        rcases a with ⟨j', d'⟩
        simpa [recursiveCoeffAssignment] using
          hxy j' d' (hQvars j d (Sum.inr ⟨j', d'⟩) hu)
  · rfl

/-- Helper for Cartan section29 0004_Exercise_2: a recursive coefficient recurrence has at most
one solution once its defining polynomials only use strictly lower-degree solution coefficients. -/
lemma recursiveCoefficientRecurrence_eq
    (S : RecursiveImplicitSystem 𝕜 n p)
    {Q : Fin n → (ParamIndex n p →₀ ℕ) → MvPolynomial (RecursiveCoeffVar n p) ℤ}
    (hQvars : ∀ j d u,
      u ∈ (Q j d).vars →
        match u with
        | Sum.inl _ => True
        | Sum.inr ⟨_, d'⟩ => paramDegree d' < paramDegree d)
    {x y : Fin n → MvPowerSeries (ParamIndex n p) 𝕜}
    (hx : RecursiveCoefficientRecurrence S Q x)
    (hy : RecursiveCoefficientRecurrence S Q y) :
    x = y := by
  -- Compare coefficients by strong induction on the total parameter degree.
  have hcoeff :
      ∀ N, ∀ j d, paramDegree d = N →
        MvPowerSeries.coeff d (x j) = MvPowerSeries.coeff d (y j) := by
    intro N
    refine Nat.strongRecOn' N ?_
    intro N ih j d hdN
    by_cases hN0 : N = 0
    · have hd0 : paramDegree d = 0 := by simpa [hN0] using hdN
      have hdzero : d = 0 := (paramDegree_eq_zero_iff (n := n) (p := p) d).mp hd0
      subst hdzero
      simp [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hx.constantCoeff_eq_zero,
        hy.constantCoeff_eq_zero]
    · have hd : 0 < paramDegree d := by
        rw [hdN]
        exact Nat.pos_iff_ne_zero.mpr hN0
      rw [hx.coeff_eq_eval j d hd, hy.coeff_eq_eval j d hd]
      apply evalRecursiveCoefficientPolynomial_eq_of_lowerCoeffEq (S := S) hQvars
      intro j' d' hd'
      exact ih (paramDegree d') (by simpa [hdN] using hd') j' d' rfl
  funext j
  ext d
  exact hcoeff (paramDegree d) j d rfl

/-- Helper for Cartan section29 0004_Exercise_2: the stage-`N` approximant records all recursive
coefficients of total parameter degree at most `N`, leaving higher degrees at zero. -/
private noncomputable def recursiveCoefficientApproximant
    (S : RecursiveImplicitSystem 𝕜 n p)
    (Q : Fin n → (ParamIndex n p →₀ ℕ) → MvPolynomial (RecursiveCoeffVar n p) ℤ) :
    ℕ → Fin n → MvPowerSeries (ParamIndex n p) 𝕜
  | 0 => 0
  | N + 1 => fun j d ↦
      if hdeg : paramDegree d = N + 1 then
        MvPolynomial.eval₂ (Int.castRingHom 𝕜)
          (recursiveCoeffAssignment S (recursiveCoefficientApproximant S Q N)) (Q j d)
      else
        MvPowerSeries.coeff d (recursiveCoefficientApproximant S Q N j)
/-- Helper for Cartan section29 0004_Exercise_2: stage `N + 1` only inserts degree `N + 1`. -/
private lemma recursiveCoefficientApproximant_coeff_step_eq
    (S : RecursiveImplicitSystem 𝕜 n p)
    (Q : Fin n → (ParamIndex n p →₀ ℕ) → MvPolynomial (RecursiveCoeffVar n p) ℤ)
    (N : ℕ) (j : Fin n) (d : ParamIndex n p →₀ ℕ)
    (hd : paramDegree d ≠ N + 1) :
    MvPowerSeries.coeff d (recursiveCoefficientApproximant S Q (N + 1) j) =
      MvPowerSeries.coeff d (recursiveCoefficientApproximant S Q N j) := by
  change
    (if hdeg : paramDegree d = N + 1 then
        MvPolynomial.eval₂ (Int.castRingHom 𝕜)
          (recursiveCoeffAssignment S (recursiveCoefficientApproximant S Q N)) (Q j d)
      else
        MvPowerSeries.coeff d (recursiveCoefficientApproximant S Q N j)) =
      MvPowerSeries.coeff d (recursiveCoefficientApproximant S Q N j)
  simp [hd]
/-- Helper for Cartan section29 0004_Exercise_2: degrees above stage `N` still vanish. -/
private lemma recursiveCoefficientApproximant_coeff_eq_zero_of_lt
    (S : RecursiveImplicitSystem 𝕜 n p)
    (Q : Fin n → (ParamIndex n p →₀ ℕ) → MvPolynomial (RecursiveCoeffVar n p) ℤ) :
    ∀ N j d, N < paramDegree d →
      MvPowerSeries.coeff d (recursiveCoefficientApproximant S Q N j) = 0
  | 0, j, d, _ => by
      simp [recursiveCoefficientApproximant]
  | N + 1, j, d, hd => by
      have hne : paramDegree d ≠ N + 1 := by omega
      rw [recursiveCoefficientApproximant_coeff_step_eq (S := S) (Q := Q) (N := N) (j := j)
        (d := d) hne]
      exact recursiveCoefficientApproximant_coeff_eq_zero_of_lt S Q N j d (by omega)
/-- Helper for Cartan section29 0004_Exercise_2: later approximants keep each created degree. -/
private lemma recursiveCoefficientApproximant_stabilizes
    (S : RecursiveImplicitSystem 𝕜 n p)
    (Q : Fin n → (ParamIndex n p →₀ ℕ) → MvPolynomial (RecursiveCoeffVar n p) ℤ)
    (j : Fin n) (d : ParamIndex n p →₀ ℕ) :
    ∀ k,
      MvPowerSeries.coeff d
          (recursiveCoefficientApproximant S Q (paramDegree d + k) j) =
        MvPowerSeries.coeff d
          (recursiveCoefficientApproximant S Q (paramDegree d) j)
  | 0 => by
      rfl
  | k + 1 => by
      have hstep :
          MvPowerSeries.coeff d
              (recursiveCoefficientApproximant S Q (paramDegree d + k + 1) j) =
            MvPowerSeries.coeff d
              (recursiveCoefficientApproximant S Q (paramDegree d + k) j) := by
        have hne : paramDegree d ≠ paramDegree d + k + 1 := by omega
        simpa [Nat.add_assoc] using
          recursiveCoefficientApproximant_coeff_step_eq (S := S) (Q := Q)
            (N := paramDegree d + k) (j := j) (d := d) hne
      calc
        MvPowerSeries.coeff d
            (recursiveCoefficientApproximant S Q (paramDegree d + (k + 1)) j)
            = MvPowerSeries.coeff d
                (recursiveCoefficientApproximant S Q (paramDegree d + k + 1) j) := by
                  simp [Nat.add_assoc]
        _ = MvPowerSeries.coeff d
              (recursiveCoefficientApproximant S Q (paramDegree d + k) j) := hstep
        _ = MvPowerSeries.coeff d
              (recursiveCoefficientApproximant S Q (paramDegree d) j) :=
            recursiveCoefficientApproximant_stabilizes S Q j d k
/-- Helper for Cartan section29 0004_Exercise_2: the stabilized coefficients define the limit
series. -/
private noncomputable def recursiveCoefficientSolution
    (S : RecursiveImplicitSystem 𝕜 n p)
    (Q : Fin n → (ParamIndex n p →₀ ℕ) → MvPolynomial (RecursiveCoeffVar n p) ℤ) :
    Fin n → MvPowerSeries (ParamIndex n p) 𝕜 :=
  fun j d ↦
    MvPowerSeries.coeff d (recursiveCoefficientApproximant S Q (paramDegree d) j)
/-- Helper for Cartan section29 0004_Exercise_2: the limit agrees with every later approximant. -/
private lemma recursiveCoefficientSolution_coeff_eq_approximant
    (S : RecursiveImplicitSystem 𝕜 n p)
    (Q : Fin n → (ParamIndex n p →₀ ℕ) → MvPolynomial (RecursiveCoeffVar n p) ℤ)
    (j : Fin n) (d : ParamIndex n p →₀ ℕ) {N : ℕ}
    (hd : paramDegree d ≤ N) :
    MvPowerSeries.coeff d (recursiveCoefficientSolution S Q j) =
      MvPowerSeries.coeff d (recursiveCoefficientApproximant S Q N j) := by
  calc
    MvPowerSeries.coeff d (recursiveCoefficientSolution S Q j) =
        MvPowerSeries.coeff d
          (recursiveCoefficientApproximant S Q (paramDegree d) j) := rfl
    _ = MvPowerSeries.coeff d
          (recursiveCoefficientApproximant S Q (paramDegree d + (N - paramDegree d)) j) := by
            symm
            exact recursiveCoefficientApproximant_stabilizes S Q j d (N - paramDegree d)
    _ = MvPowerSeries.coeff d (recursiveCoefficientApproximant S Q N j) := by
          rw [Nat.add_sub_of_le hd]
/-- Helper for Cartan section29 0004_Exercise_2: every lower-degree recurrence has a solution. -/
private lemma existsRecursiveCoefficientRecurrence
    (S : RecursiveImplicitSystem 𝕜 n p)
    {Q : Fin n → (ParamIndex n p →₀ ℕ) → MvPolynomial (RecursiveCoeffVar n p) ℤ}
    (hQvars : ∀ j d u,
      u ∈ (Q j d).vars →
        match u with
        | Sum.inl _ => True
        | Sum.inr ⟨_, d'⟩ => paramDegree d' < paramDegree d) :
    ∃ x : Fin n → MvPowerSeries (ParamIndex n p) 𝕜,
      RecursiveCoefficientRecurrence S Q x := by
  classical
  let x := recursiveCoefficientSolution S Q
  refine ⟨x, ?_⟩
  refine ⟨?_, ?_⟩
  · intro j
    change
      MvPowerSeries.coeff (0 : ParamIndex n p →₀ ℕ)
          (recursiveCoefficientApproximant S Q (paramDegree (0 : ParamIndex n p →₀ ℕ)) j) = 0
    simp [recursiveCoefficientApproximant, paramDegree]
  · intro j d hd
    obtain ⟨N, hN⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
    calc
      MvPowerSeries.coeff d (x j) =
          MvPowerSeries.coeff d (recursiveCoefficientApproximant S Q (N + 1) j) := by
            simpa [x, hN] using
              recursiveCoefficientSolution_coeff_eq_approximant
                (S := S) (Q := Q) (j := j) (d := d) (N := N + 1)
                (by simpa [hN])
      _ =
          MvPolynomial.eval₂ (Int.castRingHom 𝕜)
            (recursiveCoeffAssignment S (recursiveCoefficientApproximant S Q N)) (Q j d) := by
              change
                (if hdeg : paramDegree d = N + 1 then
                    MvPolynomial.eval₂ (Int.castRingHom 𝕜)
                      (recursiveCoeffAssignment S (recursiveCoefficientApproximant S Q N))
                      (Q j d)
                  else
                    MvPowerSeries.coeff d (recursiveCoefficientApproximant S Q N j)) =
                  MvPolynomial.eval₂ (Int.castRingHom 𝕜)
                    (recursiveCoeffAssignment S (recursiveCoefficientApproximant S Q N))
                    (Q j d)
              simp [hN]
      _ =
          MvPolynomial.eval₂ (Int.castRingHom 𝕜) (recursiveCoeffAssignment S x) (Q j d) := by
            apply evalRecursiveCoefficientPolynomial_eq_of_lowerCoeffEq (S := S) hQvars
            intro j' d' hd'
            symm
            exact recursiveCoefficientSolution_coeff_eq_approximant (S := S) (Q := Q)
              (j := j') (d := d') (N := N) (by omega)
/-- Helper for Cartan section29 0004_Exercise_2: the recursive-system formal solution is unique. -/
lemma formalImplicitSolution_eq
    (S : RecursiveImplicitSystem 𝕜 n p)
    {x y : Fin n → MvPowerSeries (ParamIndex n p) 𝕜}
    (hx : FormalImplicitSolution S x)
    (hy : FormalImplicitSolution S y) :
    x = y := by
  -- Transfer both solutions to the coefficient recurrence and apply the strong-induction
  -- uniqueness lemma there.
  rcases exists_recursive_coefficient_polynomials (n := n) (p := p) S with ⟨Q, hQvars, hQiff⟩
  exact recursiveCoefficientRecurrence_eq (n := n) (p := p) (S := S) hQvars
    ((hQiff x).mp hx) ((hQiff y).mp hy)

/-- Exercise 2 (2): every recursive system `(3)` admits a unique formal solution `(4)`. -/
theorem existsUnique_formalImplicitSolution
    (S : RecursiveImplicitSystem 𝕜 n p) :
    ∃! x : Fin n → MvPowerSeries (ParamIndex n p) 𝕜,
      FormalImplicitSolution S x := by
  classical
  have huniq :
      ∀ {x y : Fin n → MvPowerSeries (ParamIndex n p) 𝕜},
        FormalImplicitSolution S x → FormalImplicitSolution S y → x = y := by
    intro x y hx hy
    exact formalImplicitSolution_eq (n := n) (p := p) (S := S) hx hy
  rcases exists_recursive_coefficient_polynomials (n := n) (p := p) S with ⟨Q, hQvars, hQiff⟩
  rcases existsRecursiveCoefficientRecurrence (n := n) (p := p) (S := S) hQvars with ⟨x, hx⟩
  refine ⟨x, (hQiff x).mpr hx, ?_⟩
  intro y hy
  exact huniq hy ((hQiff x).mpr hx)
end FormalRecursiveImplicitSystem
