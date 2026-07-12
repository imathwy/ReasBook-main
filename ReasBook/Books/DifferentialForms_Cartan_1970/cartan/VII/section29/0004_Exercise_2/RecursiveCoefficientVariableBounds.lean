import DifferentialForms_Cartan_1970.VII.section29.«0004_Exercise_2».UniversalCutoffModel

open scoped BigOperators MvPowerSeries PowerSeries
open PowerSeries

universe u

section FormalRecursiveImplicitSystem

variable {𝕜 : Type u} [CommRing 𝕜]
variable {n p : ℕ}

/-- Helper for Exercise 2: every coefficient of the cutoff substitution uses only the allowed
right-summand variables of total parameter degree strictly below the cutoff. -/
lemma vars_coeff_solutionSubst_truncatedUniversalSolution
    (N : ℕ) (s : SystemIndex n p) (e : ParamIndex n p →₀ ℕ) (u : RecursiveCoeffVar n p)
    (hu : u ∈ (MvPowerSeries.coeff e
      (solutionSubst (truncatedUniversalSolution (n := n) (p := p) N) s)).vars) :
    match u with
    | Sum.inl _ => True
    | Sum.inr ⟨_, d⟩ => paramDegree d < N := by
  classical
  -- Read the substituted series coefficientwise. Only the `x`-variable branch can contribute a
  -- right-summand coefficient variable, and there it appears exactly in the kept cutoff range.
  cases s with
  | inl j =>
      by_cases hcut : 0 < paramDegree e ∧ paramDegree e < N
      · cases u with
        | inl a =>
            trivial
        | inr a =>
            rcases a with ⟨j', d⟩
            change (Sum.inr ⟨j', d⟩ : RecursiveCoeffVar n p) ∈
              ((truncatedUniversalSolution (n := n) (p := p) N j) e).vars at hu
            simp [truncatedUniversalSolution, hcut, MvPolynomial.vars_X] at hu
            rcases hu with ⟨rfl, rfl⟩
            simpa using hcut.2
      · change u ∈ ((truncatedUniversalSolution (n := n) (p := p) N j) e).vars at hu
        simp [truncatedUniversalSolution, hcut] at hu
  | inr a =>
      cases a with
      | inl i =>
          cases u with
          | inl a =>
              trivial
          | inr a =>
              rcases a with ⟨j', d⟩
              exact False.elim <| by
                change (Sum.inr ⟨j', d⟩ : RecursiveCoeffVar n p) ∈
                  (MvPowerSeries.coeff e
                    (MvPowerSeries.X (Sum.inl i) :
                      MvPowerSeries (ParamIndex n p) (MvPolynomial (RecursiveCoeffVar n p) ℤ))).vars
                  at hu
                by_cases he : e = Finsupp.single (Sum.inl i) 1
                · simp [MvPowerSeries.coeff_X, he] at hu
                · simp [MvPowerSeries.coeff_X, he] at hu
      | inr k =>
          cases u with
          | inl a =>
              trivial
          | inr a =>
              rcases a with ⟨j', d⟩
              exact False.elim <| by
                change (Sum.inr ⟨j', d⟩ : RecursiveCoeffVar n p) ∈
                  (MvPowerSeries.coeff e
                    (MvPowerSeries.X (Sum.inr k) :
                      MvPowerSeries (ParamIndex n p) (MvPolynomial (RecursiveCoeffVar n p) ℤ))).vars
                  at hu
                by_cases he : e = Finsupp.single (Sum.inr k) 1
                · simp [MvPowerSeries.coeff_X, he] at hu
                · simp [MvPowerSeries.coeff_X, he] at hu

/-- Helper for Exercise 2: the cutoff bound on right-summand variables is preserved when passing to
coefficients of powers of a substituted series. -/
lemma vars_coeff_pow_below_cutoff
    {φ : MvPowerSeries (ParamIndex n p) (MvPolynomial (RecursiveCoeffVar n p) ℤ)}
    {N : ℕ}
    (hφ : ∀ e u, u ∈ (MvPowerSeries.coeff e φ).vars →
      match u with
      | Sum.inl _ => True
      | Sum.inr ⟨_, d⟩ => paramDegree d < N)
    (q : ℕ) (e : ParamIndex n p →₀ ℕ) (u : RecursiveCoeffVar n p)
    (hu : u ∈ (MvPowerSeries.coeff e (φ ^ q)).vars) :
    match u with
    | Sum.inl _ => True
    | Sum.inr ⟨_, d⟩ => paramDegree d < N := by
  classical
  -- Expand the coefficient of the power into antidiagonal products, then descend to a single
  -- factor coefficient where the cutoff hypothesis `hφ` applies directly.
  rw [MvPowerSeries.coeff_pow] at hu
  have hsum :
      (∑ l ∈ Finset.finsuppAntidiag (Finset.range q) e,
          ∏ i ∈ Finset.range q, MvPowerSeries.coeff (l i) φ).vars ⊆
        (Finset.finsuppAntidiag (Finset.range q) e).biUnion fun l =>
          (∏ i ∈ Finset.range q, MvPowerSeries.coeff (l i) φ).vars := by
    simpa using
      (MvPolynomial.vars_sum_subset
        (t := Finset.finsuppAntidiag (Finset.range q) e)
        (φ := fun l => ∏ i ∈ Finset.range q, MvPowerSeries.coeff (l i) φ))
  rcases Finset.mem_biUnion.mp (hsum hu) with ⟨l, hl, hul⟩
  have hprod :
      (∏ i ∈ Finset.range q, MvPowerSeries.coeff (l i) φ).vars ⊆
        (Finset.range q).biUnion fun i => (MvPowerSeries.coeff (l i) φ).vars := by
    simpa using
      (MvPolynomial.vars_prod
        (s := Finset.range q)
        (f := fun i => MvPowerSeries.coeff (l i) φ))
  rcases Finset.mem_biUnion.mp (hprod hul) with ⟨i, hi, hui⟩
  cases u with
  | inl a =>
      trivial
  | inr a =>
      simpa using hφ (l i) (Sum.inr a) hui

/-- Helper for Exercise 2: the cutoff bound on right-summand variables is preserved under the
finite products appearing in the substitution coefficient formula. -/
lemma vars_coeff_prod_below_cutoff
    {ι : Type*} [DecidableEq ι]
    {f : ι → MvPowerSeries (ParamIndex n p) (MvPolynomial (RecursiveCoeffVar n p) ℤ)}
    {s : Finset ι} {N : ℕ}
    (hf : ∀ i ∈ s, ∀ e u, u ∈ (MvPowerSeries.coeff e (f i)).vars →
      match u with
      | Sum.inl _ => True
      | Sum.inr ⟨_, d⟩ => paramDegree d < N)
    (e : ParamIndex n p →₀ ℕ) (u : RecursiveCoeffVar n p)
    (hu : u ∈ (MvPowerSeries.coeff e (∏ i ∈ s, f i)).vars) :
    match u with
    | Sum.inl _ => True
    | Sum.inr ⟨_, d⟩ => paramDegree d < N := by
  classical
  -- Expand the coefficient of the finite product into antidiagonal products, then descend to a
  -- single factor coefficient where the cutoff hypothesis `hf` applies.
  rw [MvPowerSeries.coeff_prod] at hu
  have hsum :
      (∑ l ∈ Finset.finsuppAntidiag s e,
          ∏ i ∈ s, MvPowerSeries.coeff (l i) (f i)).vars ⊆
        (Finset.finsuppAntidiag s e).biUnion fun l =>
          (∏ i ∈ s, MvPowerSeries.coeff (l i) (f i)).vars := by
    simpa using
      (MvPolynomial.vars_sum_subset
        (t := Finset.finsuppAntidiag s e)
        (φ := fun l => ∏ i ∈ s, MvPowerSeries.coeff (l i) (f i)))
  rcases Finset.mem_biUnion.mp (hsum hu) with ⟨l, hl, hul⟩
  have hprod :
      (∏ i ∈ s, MvPowerSeries.coeff (l i) (f i)).vars ⊆
        s.biUnion fun i => (MvPowerSeries.coeff (l i) (f i)).vars := by
    simpa using
      (MvPolynomial.vars_prod
        (s := s)
        (f := fun i => MvPowerSeries.coeff (l i) (f i)))
  rcases Finset.mem_biUnion.mp (hprod hul) with ⟨i, hi, hui⟩
  cases u with
  | inl a =>
      trivial
  | inr a =>
      simpa using hf i hi (l i) (Sum.inr a) hui

/-- Helper for Exercise 2: the monomial products arising from the substitution formula only use
cutoff solution variables of strictly smaller total parameter degree. -/
lemma vars_coeff_finsuppProd_solutionSubst_truncatedUniversalSolution
    (N : ℕ) (m : SystemIndex n p →₀ ℕ) (e : ParamIndex n p →₀ ℕ)
    (u : RecursiveCoeffVar n p)
    (hu : u ∈ (MvPowerSeries.coeff e
      (m.prod fun s q =>
        (solutionSubst (truncatedUniversalSolution (n := n) (p := p) N) s) ^ q)).vars) :
    match u with
    | Sum.inl _ => True
    | Sum.inr ⟨_, d⟩ => paramDegree d < N := by
  classical
  -- Rewrite the `Finsupp` product over `m.support`, then apply the finite-product support lemma
  -- with the cutoff bound for each substituted power factor.
  cases u with
  | inl a =>
      trivial
  | inr a =>
      simpa [Finsupp.prod] using
        (vars_coeff_prod_below_cutoff
          (n := n) (p := p)
          (f := fun s =>
            (solutionSubst (truncatedUniversalSolution (n := n) (p := p) N) s) ^ m s)
          (s := m.support)
          (N := N)
          (hf := by
            intro s hs e' u' hu'
            cases u' with
            | inl a =>
                trivial
            | inr a =>
                simpa using vars_coeff_pow_below_cutoff
                  (n := n) (p := p)
                  (φ := solutionSubst (truncatedUniversalSolution (n := n) (p := p) N) s)
                  (N := N)
                  (hφ := by
                    intro e'' u'' hu''
                    cases u'' with
                    | inl a =>
                        trivial
                    | inr a =>
                        simpa using vars_coeff_solutionSubst_truncatedUniversalSolution
                          (n := n) (p := p) N s e'' (Sum.inr a) hu'')
                  (q := m s) (e := e') (u := Sum.inr a) hu')
          (e := e) (u := Sum.inr a) hu)

/-- Helper for Exercise 2: coefficients of the renamed universal linear coefficient series only
involve primitive system variables. -/
lemma vars_coeff_rename_universalLinearCoeff_left
    (j i : Fin n) (e : SystemIndex n p →₀ ℕ) (j' : Fin n)
    (d' : ParamIndex n p →₀ ℕ)
    (hu : Sum.inr ⟨j', d'⟩ ∈
      (MvPowerSeries.coeff e
        (MvPowerSeries.rename (zToSystem : Fin p → SystemIndex n p)
          (universalLinearCoeff (n := n) (p := p) j i))).vars) :
    False := by
  classical
  let ez : Fin p ↪ SystemIndex n p := ⟨zToSystem, by
    intro a b h
    simpa [zToSystem] using h⟩
  by_cases hpre : ∃ d : Fin p →₀ ℕ, Finsupp.embDomain ez d = e
  · rcases hpre with ⟨d, rfl⟩
    -- On coefficients in the range of `zToSystem`, renaming simply recovers the unique universal
    -- linear coefficient indexed by that `z`-multi-index.
    have hcoeff :
        MvPowerSeries.coeff (Finsupp.embDomain ez d)
          (MvPowerSeries.rename (zToSystem : Fin p → SystemIndex n p)
            (universalLinearCoeff (n := n) (p := p) j i)) =
          MvPowerSeries.coeff d
            (universalLinearCoeff (n := n) (p := p) j i) := by
      simpa [ez] using
        (MvPowerSeries.coeff_embDomain_rename
          (e := ez)
          (p := universalLinearCoeff (n := n) (p := p) j i)
          (x := d))
    rw [hcoeff] at hu
    change (Sum.inr (j', d') : RecursiveCoeffVar n p) ∈
      (MvPolynomial.X (Sum.inl (Sum.inl (j, i, d)))).vars at hu
    have : False := by
      simpa [MvPolynomial.vars_X] using hu
    exact this
  · have hrange : e ∉ Set.range (Finsupp.mapDomain zToSystem) := by
      intro he
      rcases he with ⟨d, hd⟩
      exact hpre ⟨d, by simpa [Finsupp.embDomain_eq_mapDomain, ez] using hd⟩
    -- Off the `zToSystem` range, the renamed coefficient vanishes.
    rw [MvPowerSeries.coeff_rename_eq_zero
      (f := zToSystem)
      (p := universalLinearCoeff (n := n) (p := p) j i)
      hrange] at hu
    simpa using hu

/-- Helper for Exercise 2: coefficients of a universal linear summand only involve primitive
system variables. -/
lemma vars_coeff_universalLinearTerm_left
    (j i : Fin n) (e : SystemIndex n p →₀ ℕ) (j' : Fin n)
    (d' : ParamIndex n p →₀ ℕ)
    (hu : Sum.inr ⟨j', d'⟩ ∈
      (MvPowerSeries.coeff e
        (MvPowerSeries.rename (zToSystem : Fin p → SystemIndex n p)
          (universalLinearCoeff (n := n) (p := p) j i) *
          MvPowerSeries.X (Sum.inr (Sum.inl i)))).vars) :
    False := by
  classical
  let yIndex : SystemIndex n p := Sum.inr (Sum.inl i)
  let yMonomial : SystemIndex n p →₀ ℕ := Finsupp.single yIndex 1
  have hcoeff :
      MvPowerSeries.coeff e
        (MvPowerSeries.rename (zToSystem : Fin p → SystemIndex n p)
          (universalLinearCoeff (n := n) (p := p) j i) *
          MvPowerSeries.X yIndex) =
        if yMonomial ≤ e then
          MvPowerSeries.coeff (e - yMonomial)
              (MvPowerSeries.rename (zToSystem : Fin p → SystemIndex n p)
                (universalLinearCoeff (n := n) (p := p) j i)) *
            (1 : MvPolynomial (RecursiveCoeffVar n p) ℤ)
        else
          0 := by
    -- The explicit `y_i` factor shifts the coefficient by one unit in that `y`-direction.
    simpa [yIndex, yMonomial, MvPowerSeries.X] using
      (MvPowerSeries.coeff_mul_monomial
        (m := e)
        (φ := MvPowerSeries.rename (zToSystem : Fin p → SystemIndex n p)
          (universalLinearCoeff (n := n) (p := p) j i))
        (n := yMonomial)
        (a := (1 : MvPolynomial (RecursiveCoeffVar n p) ℤ)))
  rw [hcoeff] at hu
  split_ifs at hu with hmono
  · -- After peeling off the explicit `y_i`, the remaining renamed coefficient is already known to
    -- use only left primitive-system variables.
    have hmul :
        Sum.inr ⟨j', d'⟩ ∈
          (MvPowerSeries.coeff (e - yMonomial)
              (MvPowerSeries.rename (zToSystem : Fin p → SystemIndex n p)
                (universalLinearCoeff (n := n) (p := p) j i))).vars ∪
            (1 : MvPolynomial (RecursiveCoeffVar n p) ℤ).vars := by
      exact (MvPolynomial.vars_mul _ _) hu
    rcases Finset.mem_union.mp hmul with hleft | hright
    · exact vars_coeff_rename_universalLinearCoeff_left
        (n := n) (p := p) j i (e - yMonomial) j' d' hleft
    · simpa using hright
  · simpa using hu

/-- Helper for Exercise 2: coefficients of the renamed universal higher remainder only involve
primitive system variables. -/
lemma vars_coeff_rename_universalHigherCoeff_left
    (j : Fin n) (e : SystemIndex n p →₀ ℕ) (j' : Fin n)
    (d' : ParamIndex n p →₀ ℕ)
    (hu : Sum.inr ⟨j', d'⟩ ∈
      (MvPowerSeries.coeff e
        (MvPowerSeries.rename (higherToSystem : Fin n ⊕ Fin p → SystemIndex n p)
          (universalHigherCoeff (n := n) (p := p) j))).vars) :
    False := by
  classical
  let eh : Fin n ⊕ Fin p ↪ SystemIndex n p := ⟨higherToSystem, by
    intro a b h
    cases a <;> cases b <;> simpa [higherToSystem, zToSystem] using h⟩
  by_cases hpre : ∃ d : (Fin n ⊕ Fin p) →₀ ℕ, Finsupp.embDomain eh d = e
  · rcases hpre with ⟨d, rfl⟩
    -- On coefficients in the range of `higherToSystem`, renaming recovers the unique universal
    -- higher coefficient indexed by that `(x, z)`-multi-index.
    have hcoeff :
        MvPowerSeries.coeff (Finsupp.embDomain eh d)
          (MvPowerSeries.rename (higherToSystem : Fin n ⊕ Fin p → SystemIndex n p)
            (universalHigherCoeff (n := n) (p := p) j)) =
          MvPowerSeries.coeff d
            (universalHigherCoeff (n := n) (p := p) j) := by
      simpa [eh] using
        (MvPowerSeries.coeff_embDomain_rename
          (e := eh)
          (p := universalHigherCoeff (n := n) (p := p) j)
          (x := d))
    rw [hcoeff] at hu
    change (Sum.inr (j', d') : RecursiveCoeffVar n p) ∈
      (if 2 ≤ xDegree d then MvPolynomial.X (Sum.inl (Sum.inr (j, d))) else 0).vars at hu
    by_cases hdeg : 2 ≤ xDegree d
    · have : False := by
        simpa [hdeg, MvPolynomial.vars_X] using hu
      exact this
    · have : False := by
        simpa [hdeg] using hu
      exact this
  · have hrange : e ∉ Set.range (Finsupp.mapDomain higherToSystem) := by
      intro he
      rcases he with ⟨d, hd⟩
      exact hpre ⟨d, by simpa [Finsupp.embDomain_eq_mapDomain, eh] using hd⟩
    -- Off the `higherToSystem` range, the renamed higher coefficient vanishes.
    rw [MvPowerSeries.coeff_rename_eq_zero
      (f := higherToSystem)
      (p := universalHigherCoeff (n := n) (p := p) j)
      hrange] at hu
    simpa using hu

/-- Helper for Exercise 2: a coefficient of the universal recursive system only involves primitive
system coefficient variables, never solution-coefficient variables. -/
lemma vars_coeff_universalRecursiveImplicitSystem_left
    (j : Fin n) (e : SystemIndex n p →₀ ℕ) (j' : Fin n)
    (d' : ParamIndex n p →₀ ℕ)
    (hu : Sum.inr ⟨j', d'⟩ ∈
      (MvPowerSeries.coeff e
        (universalRecursiveImplicitSystem (n := n) (p := p) j)).vars) :
    False := by
  classical
  let linearTerm : Fin n → MvPowerSeries (SystemIndex n p)
      (MvPolynomial (RecursiveCoeffVar n p) ℤ) :=
    fun i =>
      MvPowerSeries.rename (zToSystem : Fin p → SystemIndex n p)
          (universalLinearCoeff (n := n) (p := p) j i) *
        MvPowerSeries.X (Sum.inr (Sum.inl i))
  let higherTerm : MvPowerSeries (SystemIndex n p)
      (MvPolynomial (RecursiveCoeffVar n p) ℤ) :=
    MvPowerSeries.rename (higherToSystem : Fin n ⊕ Fin p → SystemIndex n p)
      (universalHigherCoeff (n := n) (p := p) j)
  have hu' : Sum.inr ⟨j', d'⟩ ∈
      (MvPowerSeries.coeff e ((∑ i : Fin n, linearTerm i) + higherTerm)).vars := by
    -- Route correction: rather than chasing support inside the universal system directly, split it
    -- into its linear and higher parts and handle their coefficients separately.
    simpa [RecursiveImplicitSystem.toSeries, universalRecursiveImplicitSystem, linearTerm,
      higherTerm] using hu
  have hadd :
      (MvPowerSeries.coeff e ((∑ i : Fin n, linearTerm i) + higherTerm)).vars ⊆
        (MvPowerSeries.coeff e (∑ i : Fin n, linearTerm i)).vars ∪
          (MvPowerSeries.coeff e higherTerm).vars := by
    simpa using
      (MvPolynomial.vars_add_subset
        (MvPowerSeries.coeff e (∑ i : Fin n, linearTerm i))
        (MvPowerSeries.coeff e higherTerm))
  rcases Finset.mem_union.mp (hadd hu') with hlinear | hhigher
  · have hsum :
        (MvPowerSeries.coeff e (∑ i : Fin n, linearTerm i)).vars ⊆
          Finset.univ.biUnion fun i => (MvPowerSeries.coeff e (linearTerm i)).vars := by
      simpa [linearTerm] using
        (MvPolynomial.vars_sum_subset
          (t := Finset.univ)
          (φ := fun i : Fin n => MvPowerSeries.coeff e (linearTerm i)))
    rcases Finset.mem_biUnion.mp (hsum hlinear) with ⟨i, hi, hui⟩
    exact vars_coeff_universalLinearTerm_left
      (n := n) (p := p) j i e j' d' (by simpa [linearTerm] using hui)
  · exact vars_coeff_rename_universalHigherCoeff_left
      (n := n) (p := p) j e j' d' (by simpa [higherTerm] using hhigher)

/-- Helper for Exercise 2: any solution-coefficient variable appearing in the universal degree-`d`
coefficient polynomial comes from the cutoff solution, hence has strictly smaller total parameter
degree than `d`. -/
theorem vars_recursiveCoefficientPolynomial
    (j : Fin n) (d : ParamIndex n p →₀ ℕ) (u : RecursiveCoeffVar n p)
    (hu : u ∈ (recursiveCoefficientPolynomial (n := n) (p := p) j d).vars) :
    match u with
    | Sum.inl _ => True
    | Sum.inr ⟨_, d'⟩ => paramDegree d' < paramDegree d := by
  classical
  -- Expand the universal substituted coefficient into the finite substitution sum, then split a
  -- surviving variable between the universal-system coefficient factor and the substituted
  -- monomial-product factor.
  cases u with
  | inl a =>
      trivial
  | inr a =>
      rcases a with ⟨j', d'⟩
      let N : ℕ := paramDegree d
      let aSubst :
          SystemIndex n p →
            MvPowerSeries (ParamIndex n p) (MvPolynomial (RecursiveCoeffVar n p) ℤ) :=
        solutionSubst (truncatedUniversalSolution (n := n) (p := p) N)
      have hSubst : MvPowerSeries.HasSubst aSubst := by
        simpa [aSubst, N] using truncatedUniversalSolution_hasSubst (n := n) (p := p) N
      let G : (SystemIndex n p →₀ ℕ) → MvPolynomial (RecursiveCoeffVar n p) ℤ :=
        fun m =>
          MvPowerSeries.coeff m
              (universalRecursiveImplicitSystem (n := n) (p := p) j) •
            MvPowerSeries.coeff d (m.prod fun s q => (aSubst s) ^ q)
      have hGfinite : G.HasFiniteSupport := by
        simpa [G, aSubst, N] using
          (MvPowerSeries.coeff_subst_finite hSubst
            (universalRecursiveImplicitSystem (n := n) (p := p) j) d)
      rw [recursiveCoefficientPolynomial, MvPowerSeries.coeff_subst hSubst,
        finsum_eq_sum G hGfinite] at hu
      have hsum :
          (∑ m ∈ hGfinite.toFinset, G m).vars ⊆
            hGfinite.toFinset.biUnion fun m => (G m).vars := by
        simpa [G] using
          (MvPolynomial.vars_sum_subset
            (t := hGfinite.toFinset)
            (φ := G))
      rcases Finset.mem_biUnion.mp (hsum hu) with ⟨m, hm, hmu⟩
      have hmul :
          (G m).vars ⊆
            (MvPowerSeries.coeff m
                (universalRecursiveImplicitSystem (n := n) (p := p) j)).vars ∪
              (MvPowerSeries.coeff d (m.prod fun s q => (aSubst s) ^ q)).vars := by
        simpa [G, smul_eq_mul] using
          (MvPolynomial.vars_mul
            (MvPowerSeries.coeff m
              (universalRecursiveImplicitSystem (n := n) (p := p) j))
            (MvPowerSeries.coeff d (m.prod fun s q => (aSubst s) ^ q)))
      rcases Finset.mem_union.mp (hmul hmu) with hleft | hright
      · exact False.elim <|
          vars_coeff_universalRecursiveImplicitSystem_left
            (n := n) (p := p) j m j' d' hleft
      · simpa [aSubst, N] using
          vars_coeff_finsuppProd_solutionSubst_truncatedUniversalSolution
            (n := n) (p := p) N m d (Sum.inr ⟨j', d'⟩) hright

end FormalRecursiveImplicitSystem
