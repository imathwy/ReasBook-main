import Mathlib
import StacksProject_2024.Chap15.Definition_15_65_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory Limits

universe v

variable {R : Type v} [Ring R]
variable {ι : Type*} [Finite ι]

/-- Helper for Lemma 15.127.2: the bottom subobject is bounded and termwise finite free. -/
private theorem botSubobject_bounded_termwiseFiniteFree
    (F : CochainComplex (ModuleCat.{v} R) ℤ) :
    (∃ a b : ℤ,
        ((⊥ : Subobject F) : CochainComplex (ModuleCat.{v} R) ℤ).IsStrictlyGE a ∧
          ((⊥ : Subobject F) : CochainComplex (ModuleCat.{v} R) ℤ).IsStrictlyLE b) ∧
      (((⊥ : Subobject F) : CochainComplex (ModuleCat.{v} R) ℤ).IsTermwiseFiniteFree) := by
  -- Transport both boundedness owners from the zero complex across `Subobject.botCoeIsoZero`.
  have hGE :
      ((⊥ : Subobject F) : CochainComplex (ModuleCat.{v} R) ℤ).IsStrictlyGE (0 : ℤ) := by
    simpa using CochainComplex.isStrictlyGE_of_iso (Subobject.botCoeIsoZero.symm) (0 : ℤ)
  have hLE :
      ((⊥ : Subobject F) : CochainComplex (ModuleCat.{v} R) ℤ).IsStrictlyLE (0 : ℤ) := by
    simpa using CochainComplex.isStrictlyLE_of_iso (Subobject.botCoeIsoZero.symm) (0 : ℤ)
  refine ⟨⟨0, 0, hGE, hLE⟩, ?_⟩
  have hcomplexZero :
      Limits.IsZero (((⊥ : Subobject F) : CochainComplex (ModuleCat.{v} R) ℤ)) := by
    exact (isZero_zero _).of_iso Subobject.botCoeIsoZero
  · refine ⟨?_⟩
    intro i
    -- Evaluate the zero-complex witness at degree `i` and use subsingleton freeness there.
    have hzero :
        Limits.IsZero ((((⊥ : Subobject F) : CochainComplex (ModuleCat.{v} R) ℤ).X i)) := by
      exact
        (HomologicalComplex.eval (ModuleCat.{v} R) (ComplexShape.up ℤ) i).map_isZero
          hcomplexZero
    letI : Subsingleton ((((⊥ : Subobject F) : CochainComplex (ModuleCat.{v} R) ℤ).X i)) :=
      ModuleCat.subsingleton_of_isZero hzero
    letI :
        Module.Free R ((((⊥ : Subobject F) : CochainComplex (ModuleCat.{v} R) ℤ).X i)) :=
      Module.Free.of_subsingleton R
        ((((⊥ : Subobject F) : CochainComplex (ModuleCat.{v} R) ℤ).X i))
    letI :
        Module.Finite R ((((⊥ : Subobject F) : CochainComplex (ModuleCat.{v} R) ℤ).X i)) := ⟨∅, by
      ext x
      simp [Subsingleton.elim x 0]⟩
    exact ⟨inferInstance, inferInstance⟩

/-- Helper for Lemma 15.127.2: a finite family in a free module is contained in the span of
finitely many chosen basis vectors. -/
private theorem exists_finite_basis_support_family
    {κ : Type*} [Finite κ]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Free R M]
    (x : κ → M) :
    ∃ S : Finset (Module.Free.ChooseBasisIndex R M),
      ∀ k : κ,
        x k ∈ Submodule.span R (Set.image (Module.Free.chooseBasis R M) {i | i ∈ S}) := by
  classical
  let _ : Fintype κ := Fintype.ofFinite κ
  let b := Module.Free.chooseBasis R M
  let S : Finset (Module.Free.ChooseBasisIndex R M) :=
    Finset.univ.biUnion fun k => (b.repr (x k)).support
  refine ⟨S, ?_⟩
  intro k
  -- The chosen basis support of `x k` spans `x k`, and that support sits inside the global union.
  have hx :
      x k ∈ Submodule.span R ((b : Module.Free.ChooseBasisIndex R M → M) '' ↑((b.repr (x k)).support : Finset _)) := by
    simpa using Module.Basis.mem_span_repr_support b (x k)
  have hsubset :
    ((b : Module.Free.ChooseBasisIndex R M → M) '' ↑((b.repr (x k)).support : Finset _)) ⊆
        Set.image (b : Module.Free.ChooseBasisIndex R M → M) {i | i ∈ S} := by
    intro y hy
    rcases hy with ⟨i, hi, rfl⟩
    refine ⟨i, ?_, rfl⟩
    exact Finset.mem_biUnion.2 ⟨k, Finset.mem_univ k, hi⟩
  exact (Submodule.span_mono hsubset) hx

/-- Helper for Lemma 15.127.2: finitely many source basis vectors and finitely many target
elements are jointly contained in the span of finitely many target basis vectors after applying a
linear map. -/
private theorem exists_finite_basis_support_image_and_family
    {κ : Type*} [Finite κ]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Free R M]
    {N : Type*} [AddCommGroup N] [Module R N] [Module.Free R N]
    (d : M →ₗ[R] N)
    (S : Finset (Module.Free.ChooseBasisIndex R M))
    (y : κ → N) :
    ∃ T : Finset (Module.Free.ChooseBasisIndex R N),
      (∀ i ∈ S,
        d ((Module.Free.chooseBasis R M) i) ∈
          Submodule.span R (Set.image (Module.Free.chooseBasis R N) {j | j ∈ T})) ∧
      ∀ k : κ,
        y k ∈ Submodule.span R (Set.image (Module.Free.chooseBasis R N) {j | j ∈ T}) := by
  classical
  let z : ({i // i ∈ S} ⊕ κ) → N := fun s =>
    match s with
    | Sum.inl i => d ((Module.Free.chooseBasis R M) i.1)
    | Sum.inr k => y k
  obtain ⟨T, hT⟩ := exists_finite_basis_support_family (R := R) (M := N) z
  refine ⟨T, ?_, ?_⟩
  · intro i hi
    simpa [z] using hT (Sum.inl ⟨i, hi⟩)
  · intro k
    simpa [z] using hT (Sum.inr k)

/-- Helper for Lemma 15.127.2: from a finite chosen support in degree `n`, one can enlarge to a
finite chosen support in degree `n + 1` containing both the differentials of the chosen basis
vectors and the prescribed elements already living in degree `n + 1`. -/
private theorem exists_next_basis_support
    (F : CochainComplex (ModuleCat.{v} R) ℤ)
    (hfree : ∀ n : ℤ, Module.Free R (F.X n))
    (degrees : ι → ℤ) (elements : ∀ i : ι, F.X (degrees i))
    (n : ℤ)
    (S : Finset (Module.Free.ChooseBasisIndex R (F.X n))) :
    ∃ T : Finset (Module.Free.ChooseBasisIndex R (F.X (n + 1))),
      (∀ i ∈ S,
        (F.d n (n + 1)).hom ((Module.Free.chooseBasis R (F.X n)) i) ∈
          Submodule.span R
            (Set.image (Module.Free.chooseBasis R (F.X (n + 1))) {j | j ∈ T})) ∧
      ∀ k : {i // degrees i = n + 1},
        k.2 ▸ elements k.1 ∈
          Submodule.span R
            (Set.image (Module.Free.chooseBasis R (F.X (n + 1))) {j | j ∈ T}) := by
  let _ : Module.Free R (F.X n) := hfree n
  let _ : Module.Free R (F.X (n + 1)) := hfree (n + 1)
  let nextFamily : {i // degrees i = n + 1} → F.X (n + 1) := fun k => k.2 ▸ elements k.1
  -- Apply the joint finite-support lemma to the differential and the prescribed next-degree family.
  simpa [nextFamily] using
    exists_finite_basis_support_image_and_family
      (R := R) (M := F.X n) (N := F.X (n + 1))
      (F.d n (n + 1)).hom S nextFamily

/-- Helper for Lemma 15.127.2: any element in the span of finitely many chosen basis vectors
admits explicit coordinates on that finite support. -/
private theorem exists_finsupp_of_mem_span_chooseBasis_image
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Free R M]
    (S : Finset (Module.Free.ChooseBasisIndex R M))
    {x : M}
    (hx : x ∈ Submodule.span R (Set.image (Module.Free.chooseBasis R M) {i | i ∈ S})) :
    ∃ c : (↑S →₀ R),
      Finsupp.linearCombination R
          (fun i : ↑S => (Module.Free.chooseBasis R M) i.1) c = x := by
  classical
  let b := Module.Free.chooseBasis R M
  -- Rephrase span membership as a supported coordinate vector on the chosen basis.
  obtain ⟨l, hl, rfl⟩ :=
    (Finsupp.mem_span_image_iff_linearCombination (R := R) (v := b)
      (s := (↑S : Set (Module.Free.ChooseBasisIndex R M))) (x := x)).1 hx
  let c : (↑S →₀ R) :=
    Finsupp.supportedEquivFinsupp (M := R) (R := R)
      (↑S : Set (Module.Free.ChooseBasisIndex R M)) ⟨l, hl⟩
  -- Evaluate the supported coordinates through the restricted basis and unfold the cod-restriction.
  refine ⟨c, ?_⟩
  rw [show (fun i : ↑S => b i.1) = ((↑S : Set (Module.Free.ChooseBasisIndex R M)).restrict b) by
    rfl]
  rw [Finsupp.linearCombination_restrict]
  simpa [c, Finsupp.linearCombinationOn]

/-- Helper for Lemma 15.127.2: the integer endpoint `b` is `a` plus the natural length of the
interval `[a, b]`. -/
private theorem add_toNat_sub_eq_right {a b : ℤ} (hab : a ≤ b) :
    a + ((Int.toNat (b - a) : ℕ) : ℤ) = b := by
  -- Rewrite the naturalized difference back to the original integer difference.
  rw [Int.toNat_of_nonneg (sub_nonneg.mpr hab)]
  omega

/-- Helper for Lemma 15.127.2: span membership transports along an equality of degrees when both
the vector and the finite chosen support are transported by the same equality. -/
private theorem mem_span_transport
    (F : CochainComplex (ModuleCat.{v} R) ℤ)
    (hfree : ∀ n : ℤ, Module.Free R (F.X n))
    {n m : ℤ}
    (h : n = m)
    {x : F.X n}
    {T : Finset (Module.Free.ChooseBasisIndex R (F.X m))}
    (hx :
      h ▸ x ∈
        Submodule.span R
          (Set.image (Module.Free.chooseBasis R (F.X m)) {j | j ∈ T})) :
    x ∈
      Submodule.span R
        (Set.image (Module.Free.chooseBasis R (F.X n)) {j | j ∈ (h ▸ T)}) := by
  cases h
  simpa using hx

/-- Helper for Lemma 15.127.2: starting from the support in minimal degree `a`, one can enlarge
supports degree by degree up to `a + m` while keeping the family empty outside that prefix. -/
private theorem exists_support_family_through
    (F : CochainComplex (ModuleCat.{v} R) ℤ)
    (hfree : ∀ n : ℤ, Module.Free R (F.X n))
    (degrees : ι → ℤ) (elements : ∀ i : ι, F.X (degrees i))
    (a : ℤ)
    (ha_min : ∀ i : ι, a ≤ degrees i)
    (ha_support :
      ∃ S : Finset (Module.Free.ChooseBasisIndex R (F.X a)),
        ∀ i : {i // degrees i = a},
          i.2 ▸ elements i.1 ∈
            Submodule.span R (Set.image (Module.Free.chooseBasis R (F.X a)) {j | j ∈ S}))
    (m : ℕ) :
    ∃ S : ∀ n : ℤ, Finset (Module.Free.ChooseBasisIndex R (F.X n)),
      (∀ n : ℤ, n < a → S n = ∅) ∧
      (∀ n : ℤ, a + (m : ℤ) < n → S n = ∅) ∧
      (∀ i : ι, degrees i ≤ a + (m : ℤ) →
        elements i ∈
          Submodule.span R
            (Set.image (Module.Free.chooseBasis R (F.X (degrees i))) {j | j ∈ S (degrees i)})) ∧
      ∀ n : ℤ, a ≤ n → n < a + (m : ℤ) →
        ∀ j ∈ S n,
          (F.d n (n + 1)).hom ((Module.Free.chooseBasis R (F.X n)) j) ∈
            Submodule.span R
              (Set.image (Module.Free.chooseBasis R (F.X (n + 1))) {k | k ∈ S (n + 1)}) := by
  classical
  induction m with
  | zero =>
      obtain ⟨S₀, hS₀⟩ := ha_support
      let S : ∀ n : ℤ, Finset (Module.Free.ChooseBasisIndex R (F.X n)) := fun n =>
        if h : n = a then h ▸ S₀ else ∅
      refine ⟨S, ?_⟩
      constructor
      · intro n hn
        -- Below the minimal degree, the support family is empty by definition.
        simp [S, ne_of_lt hn]
      constructor
      · intro n hn
        -- Above `a = a + 0`, the base support is again empty by definition.
        have hne : ¬ n = a := by omega
        simp [S, hne]
      constructor
      · intro i hi
        -- Any prescribed degree `≤ a` must equal the minimal degree `a`.
        have hdeg : degrees i = a := by
          have hamin : a ≤ degrees i := ha_min i
          omega
        subst hdeg
        simpa [S] using hS₀ ⟨i, rfl⟩
      · intro n hna hlt
        -- There is no differential-closure condition inside the empty interval `[a, a)`.
        have : False := by
          omega
        exact this.elim
  | succ m ih =>
      obtain ⟨Sprev, hbelow_prev, habove_prev, hmem_prev, hchain_prev⟩ := ih
      obtain ⟨T, hTdiff, hTmem⟩ :=
        exists_next_basis_support
          (R := R) (ι := ι) F hfree degrees elements (a + (m : ℤ)) (Sprev (a + (m : ℤ)))
      let endpoint : ℤ := a + (m : ℤ) + 1
      let S : ∀ n : ℤ, Finset (Module.Free.ChooseBasisIndex R (F.X n)) := fun n =>
        if h : n = endpoint then h ▸ T else Sprev n
      refine ⟨S, ?_⟩
      constructor
      · intro n hn
        -- The successor step only changes the support at the new endpoint, which is still `≥ a`.
        have hne : ¬ n = endpoint := by
          omega
        simp [S, endpoint, hne, hbelow_prev n hn]
      constructor
      · intro n hn
        -- Outside the enlarged prefix `[a, a + m + 1]`, the family remains empty.
        have hne : ¬ n = endpoint := by
          omega
        have hn' : a + (m : ℤ) < n := by
          omega
        simp [S, endpoint, hne, habove_prev n hn']
      constructor
      · intro i hi
        by_cases hle : degrees i ≤ a + (m : ℤ)
        · -- Earlier prescribed degrees keep the previous support witness.
          have hne : ¬ degrees i = endpoint := by
            omega
          simpa [S, endpoint, hne] using hmem_prev i hle
        · -- The only new prescribed degree is exactly the freshly added endpoint.
          have hdeg_succ : degrees i = endpoint := by
            omega
          -- Route correction: transport first to the casted copy of `T`, then normalize the
          -- endpoint branch of the `if`-defined support family by rewriting `degrees i = endpoint`.
          have htransport :=
            mem_span_transport (R := R) (F := F) hfree (h := hdeg_succ)
              (x := elements i) (T := T) (hTmem ⟨i, hdeg_succ⟩)
          simpa [S, endpoint, hdeg_succ] using htransport
      · intro n hna hlt j hj
        by_cases hendpoint : n = a + (m : ℤ)
        · -- At the old endpoint, the new target support is exactly the set chosen by one step.
          subst hendpoint
          have hne : ¬ a + (m : ℤ) = endpoint := by
            omega
          have hj' : j ∈ Sprev (a + (m : ℤ)) := by
            simpa [S, endpoint, hne] using hj
          have hmem := hTdiff j hj'
          simpa [S, endpoint] using hmem
        · -- Strictly before the endpoint, the inductive differential-closure remains unchanged.
          have hlt_prev : n < a + (m : ℤ) := by
            omega
          have hne : ¬ n = endpoint := by
            omega
          have hj' : j ∈ Sprev n := by
            simpa [S, endpoint, hne] using hj
          have hmem := hchain_prev n hna hlt_prev j hj'
          have hne_next : ¬ n + 1 = endpoint := by
            omega
          simpa [S, endpoint, hne_next] using hmem

/-- Helper for Lemma 15.127.2: the recursive prefix family extends to interval support on
`[a, b]`, and elements above `b` vanish by bounded-above support. -/
private theorem exists_interval_basis_support_data
    (F : CochainComplex (ModuleCat.{v} R) ℤ)
    (hfree : ∀ n : ℤ, Module.Free R (F.X n))
    (degrees : ι → ℤ) (elements : ∀ i : ι, F.X (degrees i))
    (a b : ℤ) (hab : a ≤ b) (hb : F.IsStrictlyLE b)
    (ha_min : ∀ i : ι, a ≤ degrees i)
    (ha_support :
      ∃ S : Finset (Module.Free.ChooseBasisIndex R (F.X a)),
        ∀ i : {i // degrees i = a},
          i.2 ▸ elements i.1 ∈
            Submodule.span R (Set.image (Module.Free.chooseBasis R (F.X a)) {j | j ∈ S})) :
    ∃ S : ∀ n : ℤ, Finset (Module.Free.ChooseBasisIndex R (F.X n)),
      (∀ n : ℤ, n < a → S n = ∅) ∧
      (∀ n : ℤ, b < n → S n = ∅) ∧
      (∀ i : ι,
        elements i ∈
          Submodule.span R
            (Set.image (Module.Free.chooseBasis R (F.X (degrees i))) {j | j ∈ S (degrees i)})) ∧
      ∀ n : ℤ, a ≤ n → n < b →
        ∀ j ∈ S n,
          (F.d n (n + 1)).hom ((Module.Free.chooseBasis R (F.X n)) j) ∈
            Submodule.span R
              (Set.image (Module.Free.chooseBasis R (F.X (n + 1))) {k | k ∈ S (n + 1)}) := by
  classical
  let N : ℕ := Int.toNat (b - a)
  have hendpoint : a + (N : ℤ) = b := add_toNat_sub_eq_right hab
  obtain ⟨S, hbelow, habove, hmem, hchain⟩ :=
    exists_support_family_through
      (R := R) (ι := ι) F hfree degrees elements a ha_min ha_support N
  refine ⟨S, ?_⟩
  constructor
  · exact hbelow
  constructor
  · intro n hn
    -- The recursive upper-emptiness transfers from `a + N` to `b`.
    have hn' : a + (N : ℤ) < n := by
      simpa [hendpoint] using hn
    exact habove n hn'
  constructor
  · intro i
    by_cases hdeg : degrees i ≤ b
    · -- Inside the interval, the recursive family already contains the prescribed element.
      have hdeg' : degrees i ≤ a + (N : ℤ) := by
        simpa [hendpoint] using hdeg
      exact hmem i hdeg'
    · -- Above the bounded-above cutoff, the prescribed element is zero and the support is empty.
      have hgt : b < degrees i := lt_of_not_ge hdeg
      have hzero : Limits.IsZero (F.X (degrees i)) := F.isZero_of_isStrictlyLE b (degrees i) hgt
      have hSempty : S (degrees i) = ∅ := by
        have hgt' : a + (N : ℤ) < degrees i := by
          simpa [hendpoint] using hgt
        exact habove (degrees i) hgt'
      letI : Subsingleton (F.X (degrees i)) := ModuleCat.subsingleton_of_isZero hzero
      have helem : elements i = 0 := Subsingleton.elim _ _
      simpa [hSempty, helem] using
        (Submodule.zero_mem
          (Submodule.span R
            ((Module.Free.chooseBasis R (F.X (degrees i))) ''
              (↑(∅ : Finset (Module.Free.ChooseBasisIndex R (F.X (degrees i)))) : Set _))))
  · intro n hna hnb
    -- The differential-closure clause is unchanged inside the interior of `[a, b]`.
    have hnb' : n < a + (N : ℤ) := by
      simpa [hendpoint] using hnb
    exact hchain n hna hnb'

/-- Helper for Lemma 15.127.2: once the interval support family is fixed, one can choose explicit
coordinate vectors for the differential of every supported basis element. -/
private theorem exists_interval_basis_support_coefficients
    (F : CochainComplex (ModuleCat.{v} R) ℤ)
    (hfree : ∀ n : ℤ, Module.Free R (F.X n))
    (a b : ℤ)
    (S : ∀ n : ℤ, Finset (Module.Free.ChooseBasisIndex R (F.X n)))
    (hS_chain :
      ∀ n : ℤ, a ≤ n → n < b →
        ∀ j ∈ S n,
          (F.d n (n + 1)).hom
              ((@Module.Free.chooseBasis R (F.X n) _ _ _ (hfree n)) j) ∈
            Submodule.span R
              ((@Module.Free.chooseBasis R (F.X (n + 1)) _ _ _ (hfree (n + 1))) ''
                {k | k ∈ S (n + 1)})) :
    ∃ coeff : ∀ n : ℤ, ↑(S n) → (↑(S (n + 1)) →₀ R),
      ∀ n : ℤ, a ≤ n → n < b →
        ∀ j : ↑(S n),
          Finsupp.linearCombination R
              (fun k : ↑(S (n + 1)) =>
                (@Module.Free.chooseBasis R (F.X (n + 1)) _ _ _ (hfree (n + 1))) k.1)
              (coeff n j) =
            (F.d n (n + 1)).hom
              ((@Module.Free.chooseBasis R (F.X n) _ _ _ (hfree n)) j.1) := by
  classical
  let coeff : ∀ n : ℤ, ↑(S n) → (↑(S (n + 1)) →₀ R) := fun n j =>
    if h : a ≤ n ∧ n < b then
      Classical.choose <|
        exists_finsupp_of_mem_span_chooseBasis_image
          (R := R) (M := F.X (n + 1)) (S (n + 1))
          (hS_chain n h.1 h.2 j.1 j.2)
    else 0
  refine ⟨coeff, ?_⟩
  intro n hna hnb j
  -- Inside the interval, the chosen coordinates are exactly the ones provided by the span witness.
  let _ : Module.Free R (F.X (n + 1)) := hfree (n + 1)
  have hmem :
      (F.d n (n + 1)).hom
          ((@Module.Free.chooseBasis R (F.X n) _ _ _ (hfree n)) j.1) ∈
        Submodule.span R
          ((@Module.Free.chooseBasis R (F.X (n + 1)) _ _ _ (hfree (n + 1))) ''
            {k | k ∈ S (n + 1)}) :=
    hS_chain n hna hnb j.1 j.2
  have hcoeff :=
    Classical.choose_spec <|
      exists_finsupp_of_mem_span_chooseBasis_image
        (R := R) (M := F.X (n + 1)) (S (n + 1)) hmem
  simpa [coeff, hna, hnb]
    using hcoeff

/-- Helper for Lemma 15.127.2: restricting the chosen basis to a finite support preserves the
injectivity of the coordinate evaluation map. -/
private theorem support_span_eval_injective
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Free R M]
    (S : Finset (Module.Free.ChooseBasisIndex R M)) :
    Function.Injective
      (Finsupp.linearCombination R
        (fun i : ↑S => (Module.Free.chooseBasis R M) i.1)) := by
  classical
  let basis := Module.Free.chooseBasis R M
  have hlin : LinearIndependent R (fun i : ↑S => basis i.1) := by
    -- The ambient chosen basis stays linearly independent after restricting the index type.
    exact basis.linearIndependent.comp (fun i : ↑S => i.1) fun i j hij => Subtype.ext hij
  -- A linear combination map indexed by a linearly independent family has unique coordinates.
  simpa [basis] using hlin

/-- Helper for Lemma 15.127.2: the finite-support coordinate carrier attached to the chosen support
in degree `n`. -/
private abbrev supportSpanCarrier
    (F : CochainComplex (ModuleCat.{v} R) ℤ)
    (hfree : ∀ n : ℤ, Module.Free R (F.X n))
    (S : ∀ n : ℤ, Finset (Module.Free.ChooseBasisIndex R (F.X n)))
    (n : ℤ) :=
  ↑(S n) →₀ R

/-- Helper for Lemma 15.127.2: the degreewise evaluation linear map from coordinate vectors on the chosen
support back to the ambient free module. -/
private noncomputable def supportSpanEvaluation
    (F : CochainComplex (ModuleCat.{v} R) ℤ)
    (hfree : ∀ n : ℤ, Module.Free R (F.X n))
    (S : ∀ n : ℤ, Finset (Module.Free.ChooseBasisIndex R (F.X n)))
    (n : ℤ) : supportSpanCarrier F hfree S n →ₗ[R] F.X n :=
  Finsupp.linearCombination R
    (fun i : ↑(S n) => (@Module.Free.chooseBasis R (F.X n) _ _ _ (hfree n)) i.1)

/-- Helper for Lemma 15.127.2: the chosen coefficient vectors define the coordinate differential on
the support span over the interior degrees `a ≤ n < b`, and vanish outside that interval. -/
private noncomputable def supportSpanDifferential
    (F : CochainComplex (ModuleCat.{v} R) ℤ)
    (hfree : ∀ n : ℤ, Module.Free R (F.X n))
    (a b : ℤ)
    (S : ∀ n : ℤ, Finset (Module.Free.ChooseBasisIndex R (F.X n)))
    (coeff : ∀ n : ℤ, ↑(S n) → (↑(S (n + 1)) →₀ R))
    (n : ℤ) :
    supportSpanCarrier F hfree S n →ₗ[R] supportSpanCarrier F hfree S (n + 1) :=
  if _ : a ≤ n ∧ n < b then
    Finsupp.linearCombination R (coeff n)
  else
    0

/-- Helper for Lemma 15.127.2: the new evaluation notation still exposes the old coordinate
injectivity degreewise. -/
private theorem support_span_evaluation_injective
    (F : CochainComplex (ModuleCat.{v} R) ℤ)
    (hfree : ∀ n : ℤ, Module.Free R (F.X n))
    (S : ∀ n : ℤ, Finset (Module.Free.ChooseBasisIndex R (F.X n)))
    (n : ℤ) :
    Function.Injective (supportSpanEvaluation (R := R) F hfree S n) := by
  -- Unfold the evaluation map once and reuse the basis-restriction injectivity established above.
  simpa [supportSpanEvaluation] using
    (support_span_eval_injective (R := R) (M := F.X n) (S := S n))

/-- Helper for Lemma 15.127.2: on a supported basis vector in an interior degree, evaluating the
coordinate differential agrees with the ambient differential of the chosen basis vector. -/
private theorem support_span_inclusion_basis_d
    (F : CochainComplex (ModuleCat.{v} R) ℤ)
    (hfree : ∀ n : ℤ, Module.Free R (F.X n))
    (a b : ℤ)
    (S : ∀ n : ℤ, Finset (Module.Free.ChooseBasisIndex R (F.X n)))
    (coeff : ∀ n : ℤ, ↑(S n) → (↑(S (n + 1)) →₀ R))
    (hcoeff :
      ∀ n : ℤ, a ≤ n → n < b →
        ∀ j : ↑(S n),
          Finsupp.linearCombination R
              (fun k : ↑(S (n + 1)) =>
                (@Module.Free.chooseBasis R (F.X (n + 1)) _ _ _ (hfree (n + 1))) k.1)
              (coeff n j) =
            (F.d n (n + 1)).hom
              ((@Module.Free.chooseBasis R (F.X n) _ _ _ (hfree n)) j.1))
    {n : ℤ}
    (hna : a ≤ n) (hnb : n < b)
    (j : ↑(S n)) :
    (supportSpanEvaluation (R := R) F hfree S (n + 1))
        ((supportSpanDifferential (R := R) F hfree a b S coeff n)
          (Finsupp.single j (1 : R))) =
      (F.d n (n + 1)).hom
        ((@Module.Free.chooseBasis R (F.X n) _ _ _ (hfree n)) j.1) := by
  -- Route correction: the difficult transport step is now isolated at a basis vector, so the
  -- packaging phase can extend this identity linearly instead of mixing transport with `Subobject`.
  simpa [supportSpanEvaluation, supportSpanDifferential, hna, hnb] using hcoeff n hna hnb j

/-- Helper for Lemma 15.127.2: the basis-vector differential identity extends linearly to every
coordinate vector on an interior degree. -/
private theorem support_span_inclusion_linear_d
    (F : CochainComplex (ModuleCat.{v} R) ℤ)
    (hfree : ∀ n : ℤ, Module.Free R (F.X n))
    (a b : ℤ)
    (S : ∀ n : ℤ, Finset (Module.Free.ChooseBasisIndex R (F.X n)))
    (coeff : ∀ n : ℤ, ↑(S n) → (↑(S (n + 1)) →₀ R))
    (hcoeff :
      ∀ n : ℤ, a ≤ n → n < b →
        ∀ j : ↑(S n),
          Finsupp.linearCombination R
              (fun k : ↑(S (n + 1)) =>
                (@Module.Free.chooseBasis R (F.X (n + 1)) _ _ _ (hfree (n + 1))) k.1)
              (coeff n j) =
            (F.d n (n + 1)).hom
              ((@Module.Free.chooseBasis R (F.X n) _ _ _ (hfree n)) j.1))
    {n : ℤ}
    (hna : a ≤ n) (hnb : n < b)
    (x : supportSpanCarrier F hfree S n) :
    (supportSpanEvaluation (R := R) F hfree S (n + 1))
        ((supportSpanDifferential (R := R) F hfree a b S coeff n) x) =
      (F.d n (n + 1)).hom
        ((supportSpanEvaluation (R := R) F hfree S n) x) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero =>
      -- Both sides are linear in the coordinate vector, so they vanish at `0`.
      simp [supportSpanEvaluation, supportSpanDifferential, hna, hnb]
  | add x y hx hy =>
      -- Linearity propagates the identity from `x` and `y` to `x + y`.
      simp [map_add, hx, hy]
  | single j r =>
      -- Reduce the single-coordinate case to the previously established basis-vector identity.
      calc
        (supportSpanEvaluation (R := R) F hfree S (n + 1))
            ((supportSpanDifferential (R := R) F hfree a b S coeff n)
              (Finsupp.single j r))
            =
              r •
                (supportSpanEvaluation (R := R) F hfree S (n + 1))
                  ((supportSpanDifferential (R := R) F hfree a b S coeff n)
                    (Finsupp.single j (1 : R))) := by
                simp [supportSpanEvaluation, supportSpanDifferential, hna, hnb,
                  Finsupp.linearCombination_single]
        _ =
            r •
              (F.d n (n + 1)).hom
                ((@Module.Free.chooseBasis R (F.X n) _ _ _ (hfree n)) j.1) := by
              rw [support_span_inclusion_basis_d
                (R := R) F hfree a b S coeff hcoeff hna hnb j]
        _ =
            (F.d n (n + 1)).hom
              (r • ((@Module.Free.chooseBasis R (F.X n) _ _ _ (hfree n)) j.1)) := by
              rw [LinearMap.map_smul]
        _ =
            (F.d n (n + 1)).hom
              ((supportSpanEvaluation (R := R) F hfree S n) (Finsupp.single j r)) := by
              simp [supportSpanEvaluation, Finsupp.linearCombination_single]

/-- Helper for Lemma 15.127.2: the raw adjacent evaluation square commutes in every degree before
any `Subobject` packaging is introduced. -/
private theorem support_span_inclusion_comm
    (F : CochainComplex (ModuleCat.{v} R) ℤ)
    (hfree : ∀ n : ℤ, Module.Free R (F.X n))
    (a b : ℤ)
    (hb : F.IsStrictlyLE b)
    (S : ∀ n : ℤ, Finset (Module.Free.ChooseBasisIndex R (F.X n)))
    (hS_below : ∀ n : ℤ, n < a → S n = ∅)
    (coeff : ∀ n : ℤ, ↑(S n) → (↑(S (n + 1)) →₀ R))
    (hcoeff :
      ∀ n : ℤ, a ≤ n → n < b →
        ∀ j : ↑(S n),
          Finsupp.linearCombination R
              (fun k : ↑(S (n + 1)) =>
                (@Module.Free.chooseBasis R (F.X (n + 1)) _ _ _ (hfree (n + 1))) k.1)
              (coeff n j) =
            (F.d n (n + 1)).hom
              ((@Module.Free.chooseBasis R (F.X n) _ _ _ (hfree n)) j.1))
    (n : ℤ)
    (x : supportSpanCarrier F hfree S n) :
    (supportSpanEvaluation (R := R) F hfree S (n + 1))
        ((supportSpanDifferential (R := R) F hfree a b S coeff n) x) =
      (F.d n (n + 1)).hom
        ((supportSpanEvaluation (R := R) F hfree S n) x) := by
  by_cases hna : a ≤ n
  · by_cases hnb : n < b
    · -- Inside the interval, the previously established linear identity gives the square.
      exact
        support_span_inclusion_linear_d
          (R := R) F hfree a b S coeff hcoeff hna hnb x
    · -- Above the interval, the coordinate differential is zero and the ambient target degree
      -- vanishes because `F` is bounded above by `b`.
      have hgt : b < n + 1 := by
        omega
      have hzero : Limits.IsZero (F.X (n + 1)) :=
        F.isZero_of_isStrictlyLE b (n + 1) hgt
      letI : Subsingleton (F.X (n + 1)) := ModuleCat.subsingleton_of_isZero hzero
      have hz :
          (0 : F.X (n + 1)) =
            (F.d n (n + 1)).hom
              ((supportSpanEvaluation (R := R) F hfree S n) x) := by
        exact Subsingleton.elim _ _
      simpa [supportSpanDifferential, hna, hnb] using hz
  · -- Below the interval, the chosen support is empty, so the source evaluation already vanishes.
    have hlt : n < a := lt_of_not_ge hna
    have hSn : S n = ∅ := hS_below n hlt
    have hx : x = 0 := by
      ext i
      exfalso
      have : i.1 ∈ (∅ : Finset (Module.Free.ChooseBasisIndex R (F.X n))) := by
        simpa [hSn] using i.2
      simpa using this
    rw [hx]
    simp [supportSpanEvaluation, supportSpanDifferential, hna]

/-- Helper for Lemma 15.127.2: the coordinate differential squares to zero before any
`Subobject` packaging is introduced. -/
private theorem support_span_complex_d_sq
    (F : CochainComplex (ModuleCat.{v} R) ℤ)
    (hfree : ∀ n : ℤ, Module.Free R (F.X n))
    (S : ∀ n : ℤ, Finset (Module.Free.ChooseBasisIndex R (F.X n)))
    (diff : ∀ n : ℤ, supportSpanCarrier F hfree S n →ₗ[R] supportSpanCarrier F hfree S (n + 1))
    (hdiff_sq :
      ∀ n : ℤ, (diff (n + 1)).comp (diff n) = 0) :
    ∀ n : ℤ, ModuleCat.ofHom (diff n) ≫ ModuleCat.ofHom (diff (n + 1)) = 0 := by
  intro n
  -- Evaluate the categorical composite on elements and reuse the linear identity directly.
  apply ModuleCat.hom_ext
  simpa using hdiff_sq n

/-- Helper for Lemma 15.127.2: package the interval-support coordinate modules into a concrete
cochain complex. -/
private abbrev supportSpanComplex
    (F : CochainComplex (ModuleCat.{v} R) ℤ)
    (hfree : ∀ n : ℤ, Module.Free R (F.X n))
    (S : ∀ n : ℤ, Finset (Module.Free.ChooseBasisIndex R (F.X n)))
    (diff : ∀ n : ℤ, supportSpanCarrier F hfree S n →ₗ[R] supportSpanCarrier F hfree S (n + 1))
    (hdiff_sq :
      ∀ n : ℤ, (diff (n + 1)).comp (diff n) = 0) :
    CochainComplex (ModuleCat.{v} R) ℤ :=
  CochainComplex.of
    (fun n ↦ ModuleCat.of.{v} R (supportSpanCarrier F hfree S n))
    (fun n ↦ ModuleCat.ofHom (diff n))
    (support_span_complex_d_sq (R := R) F hfree S diff hdiff_sq)

/-- Helper for Lemma 15.127.2: the packaged coordinate complex is bounded on the same interval as
the chosen support family. -/
private theorem support_span_complex_bounds
    (F : CochainComplex (ModuleCat.{v} R) ℤ)
    (hfree : ∀ n : ℤ, Module.Free R (F.X n))
    (a b : ℤ)
    (S : ∀ n : ℤ, Finset (Module.Free.ChooseBasisIndex R (F.X n)))
    (diff : ∀ n : ℤ, supportSpanCarrier F hfree S n →ₗ[R] supportSpanCarrier F hfree S (n + 1))
    (hdiff_sq :
      ∀ n : ℤ, (diff (n + 1)).comp (diff n) = 0)
    (hS_below : ∀ n : ℤ, n < a → S n = ∅)
    (hS_above : ∀ n : ℤ, b < n → S n = ∅) :
    (supportSpanComplex (R := R) F hfree S diff hdiff_sq).IsStrictlyGE a ∧
      (supportSpanComplex (R := R) F hfree S diff hdiff_sq).IsStrictlyLE b := by
  constructor
  · -- Below `a`, the support index set is empty, so the corresponding coordinate module is zero.
    rw [CochainComplex.isStrictlyGE_iff]
    intro n hn
    -- Normalize the degree object by the empty-support identity before using the subsingleton API.
    simpa [supportSpanComplex, supportSpanCarrier, hS_below n hn] using
      (ModuleCat.isZero_of_subsingleton
        (ModuleCat.of R
          ((↑(∅ : Finset (Module.Free.ChooseBasisIndex R (F.X n)))) →₀ R)))
  · -- Above `b`, the same empty-support argument identifies the degree object with zero.
    rw [CochainComplex.isStrictlyLE_iff]
    intro n hn
    -- The upper-bound branch uses the same empty-support identification.
    simpa [supportSpanComplex, supportSpanCarrier, hS_above n hn] using
      (ModuleCat.isZero_of_subsingleton
        (ModuleCat.of R
          ((↑(∅ : Finset (Module.Free.ChooseBasisIndex R (F.X n)))) →₀ R)))

/-- Helper for Lemma 15.127.2: the packaged coordinate complex is termwise finite free because
each degree is a finitely supported function module on a finite index set. -/
private theorem support_span_complex_termwise_finite_free
    (F : CochainComplex (ModuleCat.{v} R) ℤ)
    (hfree : ∀ n : ℤ, Module.Free R (F.X n))
    (S : ∀ n : ℤ, Finset (Module.Free.ChooseBasisIndex R (F.X n)))
    (diff : ∀ n : ℤ, supportSpanCarrier F hfree S n →ₗ[R] supportSpanCarrier F hfree S (n + 1))
    (hdiff_sq :
      ∀ n : ℤ, (diff (n + 1)).comp (diff n) = 0) :
    (supportSpanComplex (R := R) F hfree S diff hdiff_sq).IsTermwiseFiniteFree := by
  refine ⟨?_⟩
  intro n
  -- Expose the degree object as the explicit coordinate module and use the canonical instances.
  constructor
  · change Module.Free R (supportSpanCarrier F hfree S n)
    infer_instance
  · change Module.Finite R (supportSpanCarrier F hfree S n)
    letI : Finite ↥(S n) := inferInstance
    infer_instance

/-- Helper for Lemma 15.127.2: termwise finite freeness transports across isomorphisms of
cochain complexes. -/
private theorem isTermwiseFiniteFree_of_iso
    {K L : CochainComplex (ModuleCat.{v} R) ℤ} (e : K ≅ L) [K.IsTermwiseFiniteFree] :
    L.IsTermwiseFiniteFree := by
  refine ⟨?_⟩
  intro i
  -- Evaluate the complex isomorphism at degree `i` and transport the finite/free owners.
  let eX : K.X i ≅ L.X i :=
    { hom := e.hom.f i
      inv := e.inv.f i
      hom_inv_id := by
        ext x
        exact LinearMap.congr_fun
          (congrArg ModuleCat.Hom.hom (congrArg (fun f => f.f i) e.hom_inv_id)) x
      inv_hom_id := by
        ext x
        exact LinearMap.congr_fun
          (congrArg ModuleCat.Hom.hom (congrArg (fun f => f.f i) e.inv_hom_id)) x }
  exact
    ⟨Module.Free.of_equiv eX.toLinearEquiv,
      Module.Finite.equiv eX.toLinearEquiv⟩

/-- Helper for Lemma 15.127.2: the coordinate differential squares to zero before any
`Subobject` packaging is introduced. -/
private theorem support_span_d_sq_zero
    (F : CochainComplex (ModuleCat.{v} R) ℤ)
    (hfree : ∀ n : ℤ, Module.Free R (F.X n))
    (a b : ℤ)
    (S : ∀ n : ℤ, Finset (Module.Free.ChooseBasisIndex R (F.X n)))
    (coeff : ∀ n : ℤ, ↑(S n) → (↑(S (n + 1)) →₀ R))
    (hcoeff :
      ∀ n : ℤ, a ≤ n → n < b →
        ∀ j : ↑(S n),
          Finsupp.linearCombination R
              (fun k : ↑(S (n + 1)) =>
                (@Module.Free.chooseBasis R (F.X (n + 1)) _ _ _ (hfree (n + 1))) k.1)
              (coeff n j) =
            (F.d n (n + 1)).hom
              ((@Module.Free.chooseBasis R (F.X n) _ _ _ (hfree n)) j.1))
    (n : ℤ) :
    (supportSpanDifferential (R := R) F hfree a b S coeff (n + 1)).comp
        (supportSpanDifferential (R := R) F hfree a b S coeff n) =
      0 := by
  apply LinearMap.ext
  intro x
  -- Evaluate in degree `n + 2`; injectivity of the evaluation map brings the ambient relation
  -- `d ∘ d = 0` down to the coordinate differential.
  change
    (supportSpanDifferential (R := R) F hfree a b S coeff (n + 1))
        ((supportSpanDifferential (R := R) F hfree a b S coeff n) x) =
      (0 : supportSpanCarrier F hfree S (n + 1 + 1))
  have heval := support_span_evaluation_injective (R := R) F hfree S (n + 1 + 1)
  apply heval
  by_cases h₀ : a ≤ n ∧ n < b
  · by_cases h₁ : a ≤ n + 1 ∧ n + 1 < b
    · -- In the interior-interior case, rewrite both differentials through the ambient complex.
      calc
        (supportSpanEvaluation (R := R) F hfree S (n + 1 + 1))
            (((supportSpanDifferential (R := R) F hfree a b S coeff (n + 1)).comp
                (supportSpanDifferential (R := R) F hfree a b S coeff n)) x)
            =
              (F.d (n + 1) (n + 1 + 1)).hom
                ((supportSpanEvaluation (R := R) F hfree S (n + 1))
                  ((supportSpanDifferential (R := R) F hfree a b S coeff n) x)) := by
                simp only [LinearMap.comp_apply]
                rw [support_span_inclusion_linear_d
                  (R := R) F hfree a b S coeff hcoeff h₁.1 h₁.2]
        _ =
            (F.d (n + 1) (n + 1 + 1)).hom
              ((F.d n (n + 1)).hom
                ((supportSpanEvaluation (R := R) F hfree S n) x)) := by
              rw [support_span_inclusion_linear_d
                (R := R) F hfree a b S coeff hcoeff h₀.1 h₀.2]
        _ = 0 := by
              exact LinearMap.congr_fun
                (congrArg ModuleCat.Hom.hom (F.d_comp_d n (n + 1) (n + 1 + 1)))
                ((supportSpanEvaluation (R := R) F hfree S n) x)
    · -- If the second differential is exterior to the interval, it vanishes by definition.
      simp [supportSpanDifferential, h₀, h₁]
  · -- If the first differential is exterior to the interval, it vanishes by definition.
    simp [supportSpanDifferential, h₀]

/-- Helper for Lemma 15.127.2: the degreewise evaluation maps satisfy the cochain-map relation
for the packaged coordinate complex. -/
private theorem support_span_complex_to_ambient_comm
    (F : CochainComplex (ModuleCat.{v} R) ℤ)
    (hfree : ∀ n : ℤ, Module.Free R (F.X n))
    (a b : ℤ)
    (hb : F.IsStrictlyLE b)
    (S : ∀ n : ℤ, Finset (Module.Free.ChooseBasisIndex R (F.X n)))
    (hS_below : ∀ n : ℤ, n < a → S n = ∅)
    (coeff : ∀ n : ℤ, ↑(S n) → (↑(S (n + 1)) →₀ R))
    (hcoeff :
      ∀ n : ℤ, a ≤ n → n < b →
        ∀ j : ↑(S n),
          Finsupp.linearCombination R
              (fun k : ↑(S (n + 1)) =>
                (@Module.Free.chooseBasis R (F.X (n + 1)) _ _ _ (hfree (n + 1))) k.1)
              (coeff n j) =
            (F.d n (n + 1)).hom
              ((@Module.Free.chooseBasis R (F.X n) _ _ _ (hfree n)) j.1))
    (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    ModuleCat.ofHom (supportSpanEvaluation (R := R) F hfree S i) ≫ F.d i j =
      (supportSpanComplex (R := R) F hfree S
        (supportSpanDifferential (R := R) F hfree a b S coeff)
        (fun n ↦ support_span_d_sq_zero (R := R) F hfree a b S coeff hcoeff n)).d i j ≫
        ModuleCat.ofHom (supportSpanEvaluation (R := R) F hfree S j) := by
  have hj : i + 1 = j := by
    simpa using hij
  subst j
  -- Evaluate the categorical square on elements and reuse the raw coordinate-family commutativity.
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simpa [supportSpanComplex] using
    (support_span_inclusion_comm (R := R) F hfree a b hb S hS_below coeff hcoeff i x).symm

/-- Helper for Lemma 15.127.2: the coordinate support complex maps canonically into the ambient
complex by evaluating chosen coordinates degreewise. -/
private abbrev support_span_complex_to_ambient
    (F : CochainComplex (ModuleCat.{v} R) ℤ)
    (hfree : ∀ n : ℤ, Module.Free R (F.X n))
    (a b : ℤ)
    (hb : F.IsStrictlyLE b)
    (S : ∀ n : ℤ, Finset (Module.Free.ChooseBasisIndex R (F.X n)))
    (hS_below : ∀ n : ℤ, n < a → S n = ∅)
    (coeff : ∀ n : ℤ, ↑(S n) → (↑(S (n + 1)) →₀ R))
    (hcoeff :
      ∀ n : ℤ, a ≤ n → n < b →
        ∀ j : ↑(S n),
          Finsupp.linearCombination R
              (fun k : ↑(S (n + 1)) =>
                (@Module.Free.chooseBasis R (F.X (n + 1)) _ _ _ (hfree (n + 1))) k.1)
              (coeff n j) =
            (F.d n (n + 1)).hom
              ((@Module.Free.chooseBasis R (F.X n) _ _ _ (hfree n)) j.1)) :
    supportSpanComplex (R := R) F hfree S
        (supportSpanDifferential (R := R) F hfree a b S coeff)
        (fun n ↦ support_span_d_sq_zero (R := R) F hfree a b S coeff hcoeff n) ⟶
      F :=
  { f := fun n ↦ ModuleCat.ofHom (supportSpanEvaluation (R := R) F hfree S n)
    comm' := support_span_complex_to_ambient_comm
      (R := R) F hfree a b hb S hS_below coeff hcoeff }

/-- Helper for Lemma 15.127.2: the canonical morphism from the coordinate support complex to the
ambient complex is degreewise injective, hence monomorphic. -/
private theorem support_span_complex_to_ambient_mono
    (F : CochainComplex (ModuleCat.{v} R) ℤ)
    (hfree : ∀ n : ℤ, Module.Free R (F.X n))
    (a b : ℤ)
    (hb : F.IsStrictlyLE b)
    (S : ∀ n : ℤ, Finset (Module.Free.ChooseBasisIndex R (F.X n)))
    (hS_below : ∀ n : ℤ, n < a → S n = ∅)
    (coeff : ∀ n : ℤ, ↑(S n) → (↑(S (n + 1)) →₀ R))
    (hcoeff :
      ∀ n : ℤ, a ≤ n → n < b →
        ∀ j : ↑(S n),
          Finsupp.linearCombination R
              (fun k : ↑(S (n + 1)) =>
                (@Module.Free.chooseBasis R (F.X (n + 1)) _ _ _ (hfree (n + 1))) k.1)
              (coeff n j) =
            (F.d n (n + 1)).hom
              ((@Module.Free.chooseBasis R (F.X n) _ _ _ (hfree n)) j.1)) :
    Mono (support_span_complex_to_ambient (R := R) F hfree a b hb S hS_below coeff hcoeff) := by
  -- Check monomorphy degreewise, where the components are just restricted basis-evaluation maps.
  refine HomologicalComplex.mono_of_mono_f
    (support_span_complex_to_ambient (R := R) F hfree a b hb S hS_below coeff hcoeff) ?_
  intro n
  simpa [support_span_complex_to_ambient] using
    (ModuleCat.mono_iff_injective
      (ModuleCat.ofHom (supportSpanEvaluation (R := R) F hfree S n))).2
      (support_span_evaluation_injective (R := R) F hfree S n)

/-- Helper for Lemma 15.127.2: the subobject cut out by the coordinate support complex is bounded
on `[a, b]` and termwise finite free. -/
private theorem support_span_subobject_bounded_termwiseFiniteFree
    (F : CochainComplex (ModuleCat.{v} R) ℤ)
    (hfree : ∀ n : ℤ, Module.Free R (F.X n))
    (a b : ℤ)
    (hb : F.IsStrictlyLE b)
    (S : ∀ n : ℤ, Finset (Module.Free.ChooseBasisIndex R (F.X n)))
    (hS_below : ∀ n : ℤ, n < a → S n = ∅)
    (hS_above : ∀ n : ℤ, b < n → S n = ∅)
    (coeff : ∀ n : ℤ, ↑(S n) → (↑(S (n + 1)) →₀ R))
    (hcoeff :
      ∀ n : ℤ, a ≤ n → n < b →
        ∀ j : ↑(S n),
          Finsupp.linearCombination R
              (fun k : ↑(S (n + 1)) =>
                (@Module.Free.chooseBasis R (F.X (n + 1)) _ _ _ (hfree (n + 1))) k.1)
              (coeff n j) =
            (F.d n (n + 1)).hom
              ((@Module.Free.chooseBasis R (F.X n) _ _ _ (hfree n)) j.1))
    [Mono (support_span_complex_to_ambient (R := R) F hfree a b hb S hS_below coeff hcoeff)] :
    let φ := support_span_complex_to_ambient (R := R) F hfree a b hb S hS_below coeff hcoeff
    let G : Subobject F := Subobject.mk φ
    (∃ a' b' : ℤ, (G : CochainComplex (ModuleCat.{v} R) ℤ).IsStrictlyGE a' ∧ (G : CochainComplex (ModuleCat.{v} R) ℤ).IsStrictlyLE b') ∧
      (G : CochainComplex (ModuleCat.{v} R) ℤ).IsTermwiseFiniteFree := by
  let K :=
    supportSpanComplex (R := R) F hfree S
      (supportSpanDifferential (R := R) F hfree a b S coeff)
      (fun n ↦ support_span_d_sq_zero (R := R) F hfree a b S coeff hcoeff n)
  let φ : K ⟶ F :=
    support_span_complex_to_ambient (R := R) F hfree a b hb S hS_below coeff hcoeff
  let G : Subobject F := Subobject.mk φ
  have hbounds :=
    support_span_complex_bounds (R := R) F hfree a b S
      (supportSpanDifferential (R := R) F hfree a b S coeff)
      (fun n ↦ support_span_d_sq_zero (R := R) F hfree a b S coeff hcoeff n)
      hS_below hS_above
  have hKfinite :=
    support_span_complex_termwise_finite_free (R := R) F hfree S
      (supportSpanDifferential (R := R) F hfree a b S coeff)
      (fun n ↦ support_span_d_sq_zero (R := R) F hfree a b S coeff hcoeff n)
  refine ⟨⟨a, b, ?_, ?_⟩, ?_⟩
  · -- Transfer the lower bound from the coordinate complex across the canonical subobject iso.
    letI : K.IsStrictlyGE a := hbounds.1
    simpa [K, G, φ] using
      (CochainComplex.isStrictlyGE_of_iso (Subobject.underlyingIso φ).symm a)
  · -- Transfer the upper bound along the same canonical iso.
    letI : K.IsStrictlyLE b := hbounds.2
    simpa [K, G, φ] using
      (CochainComplex.isStrictlyLE_of_iso (Subobject.underlyingIso φ).symm b)
  · -- Termwise finite freeness also transports across complex isomorphisms.
    letI : K.IsTermwiseFiniteFree := hKfinite
    simpa [K, G, φ] using
      (isTermwiseFiniteFree_of_iso (R := R) (Subobject.underlyingIso φ).symm)

/-- Helper for Lemma 15.127.2: each prescribed element has a lift to the subobject determined by
the coordinate support complex. -/
private theorem chosen_element_lifts_to_support_span_subobject
    (F : CochainComplex (ModuleCat.{v} R) ℤ)
    (hfree : ∀ n : ℤ, Module.Free R (F.X n))
    (a b : ℤ)
    (hb : F.IsStrictlyLE b)
    (S : ∀ n : ℤ, Finset (Module.Free.ChooseBasisIndex R (F.X n)))
    (hS_below : ∀ n : ℤ, n < a → S n = ∅)
    (coeff : ∀ n : ℤ, ↑(S n) → (↑(S (n + 1)) →₀ R))
    (hcoeff :
      ∀ n : ℤ, a ≤ n → n < b →
        ∀ j : ↑(S n),
          Finsupp.linearCombination R
              (fun k : ↑(S (n + 1)) =>
                (@Module.Free.chooseBasis R (F.X (n + 1)) _ _ _ (hfree (n + 1))) k.1)
              (coeff n j) =
            (F.d n (n + 1)).hom
              ((@Module.Free.chooseBasis R (F.X n) _ _ _ (hfree n)) j.1))
    [Mono (support_span_complex_to_ambient (R := R) F hfree a b hb S hS_below coeff hcoeff)]
    (degrees : ι → ℤ) (elements : ∀ i : ι, F.X (degrees i))
    (hS_mem :
      ∀ i : ι,
        elements i ∈
          Submodule.span R
            (Set.image (Module.Free.chooseBasis R (F.X (degrees i))) {j | j ∈ S (degrees i)}))
    (i : ι) :
    let φ := support_span_complex_to_ambient (R := R) F hfree a b hb S hS_below coeff hcoeff
    let G : Subobject F := Subobject.mk φ
    ∃ g : (G : CochainComplex (ModuleCat.{v} R) ℤ).X (degrees i), G.arrow.f (degrees i) g = elements i := by
  let K : CochainComplex (ModuleCat.{v} R) ℤ :=
    supportSpanComplex (R := R) F hfree S
      (supportSpanDifferential (R := R) F hfree a b S coeff)
      (fun n ↦ support_span_d_sq_zero (R := R) F hfree a b S coeff hcoeff n)
  let φ : K ⟶ F :=
    support_span_complex_to_ambient (R := R) F hfree a b hb S hS_below coeff hcoeff
  let G : Subobject F := Subobject.mk φ
  obtain ⟨x, hx⟩ :=
    exists_finsupp_of_mem_span_chooseBasis_image
      (R := R) (M := F.X (degrees i)) (S (degrees i)) (hS_mem i)
  refine ⟨((Subobject.underlyingIso φ).inv.f (degrees i)) x, ?_⟩
  -- Rewrite the subobject arrow through the canonical `Subobject.underlyingIso`.
  have hmk : (Subobject.underlyingIso φ).hom ≫ φ = G.arrow := by
    simpa [G] using Subobject.underlyingIso_hom_comp_eq_mk φ
  have hcomp : (Subobject.underlyingIso φ).inv ≫ G.arrow = φ := by
    calc
      (Subobject.underlyingIso φ).inv ≫ G.arrow
          = (Subobject.underlyingIso φ).inv ≫ ((Subobject.underlyingIso φ).hom ≫ φ) := by
              rw [hmk.symm]
      _ = ((Subobject.underlyingIso φ).inv ≫ (Subobject.underlyingIso φ).hom) ≫ φ := by
            simp
      _ = φ := by
            simp
  have hcomp_deg :
      ((Subobject.underlyingIso φ).inv ≫ G.arrow).f (degrees i) = φ.f (degrees i) := by
    exact congrArg (fun ψ => ψ.f (degrees i)) hcomp
  -- After the rewrite, the claim is exactly the chosen coordinate expansion of `elements i`.
  change (((Subobject.underlyingIso φ).inv ≫ G.arrow).f (degrees i)) x = elements i
  rw [hcomp_deg]
  simpa [K, φ, support_span_complex_to_ambient, supportSpanEvaluation] using hx

/- Domain-style sampling for Lemma 15.127.2:
- primary domain: subcomplexes of a cochain complex of `R`-modules, together with the chapter
  owner for termwise finite-free complexes and the chapter style for arbitrary finite families;
- sampled owner declarations:
  `CategoryTheory.Subobject`,
  `CategoryTheory.Subobject.arrow`,
  `CochainComplex.IsTermwiseFiniteFree`,
  `isMPseudoCoherent_of_localizationAway_unitIdeal`,
  `hasTorAmplitudeIn_of_localizationAway_unitIdeal`;
- best owner abstraction:
  `source-facing`: a subcomplex `G ⊆ F` containing the chosen finite family of elements;
  `core/canonical`: the owner object `Subobject F`, with boundedness expressed by the ambient
    `IsStrictlyGE`/`IsStrictlyLE` predicates and finite freeness by
    `CochainComplex.IsTermwiseFiniteFree`;
  `bridge/view`: the inclusion morphism `G.arrow : (G : Cpx) ⟶ F`, whose degreewise components
    realize containment of the chosen elements;
- primitive vs. derived:
  the primitive datum is just the canonical subobject `G : Subobject F`;
  boundedness and termwise finite freeness are properties of the underlying complex and should not
  be repackaged as a parallel local structure, while the chosen finite family should be indexed by
  an arbitrary finite type `ι` rather than the coordinate model `Fin N`.
- layer: this file stays `source-facing`, but its theorem should quantify over `Subobject F`
  directly instead of introducing a duplicate wrapper owner, with the finite-family input kept at
  the weaker canonical `ι : Type*` / `[Finite ι]` abstraction level.
-/

-- Proof sketch: let `a` be the minimum of the finitely many prescribed degrees. Choose finitely
-- many basis vectors in degree `a` spanning the specified elements there, enlarge degree `a + 1`
-- by finitely many basis vectors containing their differentials, and then apply descending
-- induction on the lower bound to build a bounded finite free subcomplex containing every chosen
-- element.
/-- Lemma 15.127.2: a bounded above complex of free `R`-modules contains any finite family of
specified elements in a bounded finite free subcomplex. -/
theorem exists_bounded_finite_free_subcomplex_containing
    (F : CochainComplex (ModuleCat.{v} R) ℤ)
    (hbounded : ∃ b : ℤ, F.IsStrictlyLE b)
    (hfree : ∀ n : ℤ, Module.Free R (F.X n))
    (degrees : ι → ℤ) (elements : ∀ i : ι, F.X (degrees i)) :
    ∃ G : Subobject F,
      (∃ a b : ℤ,
          ((G : CochainComplex (ModuleCat.{v} R) ℤ).IsStrictlyGE a) ∧
            ((G : CochainComplex (ModuleCat.{v} R) ℤ).IsStrictlyLE b)) ∧
      ((G : CochainComplex (ModuleCat.{v} R) ℤ).IsTermwiseFiniteFree) ∧
      ∀ i : ι,
        ∃ g : (G : CochainComplex (ModuleCat.{v} R) ℤ).X (degrees i),
          G.arrow.f (degrees i) g = elements i :=
  by
    classical
    by_cases hι : IsEmpty ι
    · -- The empty-family branch is closed by the zero subobject.
      refine ⟨⊥, ?_, ?_, ?_⟩
      · exact botSubobject_bounded_termwiseFiniteFree (R := R) F |>.1
      · exact botSubobject_bounded_termwiseFiniteFree (R := R) F |>.2
      · intro i
        exact (hι.false i).elim
    · let _ : Fintype ι := Fintype.ofFinite ι
      have hι' : Nonempty ι := not_isEmpty_iff.mp hι
      obtain ⟨b, hb⟩ := hbounded
      have hdegrees_nonempty : (Finset.univ.image degrees).Nonempty := by
        rcases hι' with ⟨i⟩
        exact ⟨_, Finset.mem_image.2 ⟨i, Finset.mem_univ i, rfl⟩⟩
      let a : ℤ := (Finset.univ.image degrees).min' hdegrees_nonempty
      let degree_family : {i // degrees i = a} → F.X a := fun i => i.2 ▸ elements i.1
      have ha_min : ∀ i : ι, a ≤ degrees i := by
        intro i
        simpa [a] using
          (Finset.min'_le (Finset.univ.image degrees) (degrees i)
            (Finset.mem_image.2 ⟨i, Finset.mem_univ i, rfl⟩))
      have ha_support :
          ∃ S : Finset (Module.Free.ChooseBasisIndex R (F.X a)),
            ∀ i : {i // degrees i = a},
              degree_family i ∈
                Submodule.span R (Set.image (Module.Free.chooseBasis R (F.X a)) {j | j ∈ S}) := by
        let _ : Module.Free R (F.X a) := hfree a
        exact exists_finite_basis_support_family (R := R) (M := F.X a) degree_family
      by_cases hab : a ≤ b
      · -- Route correction: the categorical packaging is now isolated in `supportSpanComplex`.
        -- The finite support recursion on `[a, b]` is complete; only the coordinate-subcomplex
        -- packaging into a mono `P ⟶ F` and its `Subobject` image remains.
        obtain ⟨S, hS_below, hS_above, hS_mem, hS_chain⟩ :=
          exists_interval_basis_support_data
            (R := R) (ι := ι) F hfree degrees elements a b hab hb ha_min (by
              simpa [degree_family] using ha_support)
        obtain ⟨coeff, hcoeff⟩ :=
          exists_interval_basis_support_coefficients
            (R := R) F hfree a b S hS_chain
        letI :
            Mono (support_span_complex_to_ambient
              (R := R) F hfree a b hb S hS_below coeff hcoeff) :=
          support_span_complex_to_ambient_mono
            (R := R) F hfree a b hb S hS_below coeff hcoeff
        let φ :=
          support_span_complex_to_ambient (R := R) F hfree a b hb S hS_below coeff hcoeff
        let G : Subobject F := Subobject.mk φ
        have hboundedFinite :=
          support_span_subobject_bounded_termwiseFiniteFree
            (R := R) F hfree a b hb S hS_below hS_above coeff hcoeff
        refine ⟨G, ?_, ?_, ?_⟩
        · simpa [G, φ] using hboundedFinite.1
        · simpa [G, φ] using hboundedFinite.2
        · intro i
          simpa [G, φ] using
            chosen_element_lifts_to_support_span_subobject
              (R := R) F hfree a b hb S hS_below coeff hcoeff
              degrees elements hS_mem i
      · -- If the minimal prescribed degree lies above the bounded-above cutoff, every chosen
        -- element is forced to be zero, so the bottom subobject already contains them.
        refine ⟨⊥, ?_, ?_, ?_⟩
        · exact botSubobject_bounded_termwiseFiniteFree (R := R) F |>.1
        · exact botSubobject_bounded_termwiseFiniteFree (R := R) F |>.2
        · intro i
          have hmin : a ≤ degrees i := by
            simpa [a] using
              (Finset.min'_le (Finset.univ.image degrees) (degrees i)
                (Finset.mem_image.2 ⟨i, Finset.mem_univ i, rfl⟩))
          have hdeg : b < degrees i := lt_of_not_ge fun hbi => hab (hmin.trans hbi)
          have hzero : Limits.IsZero (F.X (degrees i)) := F.isZero_of_isStrictlyLE b (degrees i) hdeg
          letI : Subsingleton (F.X (degrees i)) := ModuleCat.subsingleton_of_isZero hzero
          refine ⟨0, ?_⟩
          exact Subsingleton.elim _ _
