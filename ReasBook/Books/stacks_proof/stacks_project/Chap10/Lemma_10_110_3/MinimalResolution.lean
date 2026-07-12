import StacksProject_2024.Chap10.Lemma_10_110_3.ResolutionData

universe u

open CategoryTheory CategoryTheory.Limits IsLocalRing

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

local notation "moduleSingle[" R "]" M =>
  CategoryTheory.Functor.obj (ChainComplex.single₀ (ModuleCat R)) (ModuleCat.of R M)

/-- Helper for Lemma 10.110.3: the induction measure for minimalizing a bounded finite free
resolution is the total displayed rank in positive degrees. -/
private def positiveRankSum {e : ℕ} (C : FiniteFreeComplex R e) : ℕ :=
  ∑ j : Fin e, C.rank j.succ

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Lemma 10.110.3: exactness at a positive degree of a chain complex of modules is the
exactness of the adjacent differentials as linear maps. -/
private lemma exactAt_iff_function_exact
    (K : ChainComplex (ModuleCat R) ℕ) {j : ℕ} (hj : 1 ≤ j) :
    K.ExactAt j ↔ Function.Exact (K.d (j + 1) j).hom (K.d j (j - 1)).hom := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  have hmid : 1 + k = k + 1 := by
    omega
  have hsucc : k + 1 + 1 = k + 2 := by
    omega
  have hpred : k + 1 - 1 = k := by
    omega
  -- Rewrite `ExactAt` through the explicit three-term window around `k + 1`.
  rw [hmid, hsucc, hpred]
  rw [HomologicalComplex.exactAt_iff' K (k + 2) (k + 1) k (by simp) (by simp)]
  -- In `ModuleCat`, categorical exactness is exactly exactness of linear maps.
  simpa [HomologicalComplex.sc'] using
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (K.sc' (k + 2) (k + 1) k))

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Lemma 10.110.3: if the total positive-degree rank is zero, then every individual
positive-degree displayed rank vanishes. -/
private lemma rank_succ_eq_zero_of_positiveRankSum_eq_zero
    {e : ℕ} (C : FiniteFreeComplex R e)
    (hzero : positiveRankSum (R := R) C = 0)
    (j : Fin e) :
    C.rank j.succ = 0 := by
  -- Each positive-degree rank is a nonnegative summand in the total rank sum.
  have hle : C.rank j.succ ≤ positiveRankSum (R := R) C := by
    simpa [positiveRankSum] using
      (Finset.single_le_sum
        (f := fun k : Fin e ↦ C.rank k.succ)
        (fun _ _ ↦ Nat.zero_le _)
        (Finset.mem_univ j))
  rw [hzero] at hle
  exact Nat.eq_zero_of_le_zero hle

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Lemma 10.110.3: a displayed rank-zero term of a finite free complex is a zero
object. -/
private lemma term_isZero_of_rank_eq_zero
    {e : ℕ} (C : FiniteFreeComplex R e) (j : Fin (e + 1)) (hj : C.rank j = 0) :
    Limits.IsZero (C.toChainComplex.X j) := by
  -- Transport the zero-object claim across the chosen `Fin`-coordinate isomorphism in degree `j`.
  exact (C.termIso j).isZero_iff.mpr <|
    by simpa [hj] using ModuleCat.isZero_of_subsingleton (ModuleCat.of R (Fin 0 → R))

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Lemma 10.110.3: if all positive displayed ranks vanish, then the packaged bounded
resolution is concentrated in degree `0`. -/
private lemma positive_degree_sum_zero_iso_single_zero
    {e : ℕ} (C : FiniteFreeComplex R e)
    (hzero : positiveRankSum (R := R) C = 0) :
    Nonempty
      (C.toChainComplex ≅
        ((ChainComplex.single₀ (ModuleCat R)).obj
          (ModuleCat.of R (Fin (C.rank ⟨0, Nat.zero_lt_succ e⟩) → R)))) := by
  let X0 : ModuleCat R := ModuleCat.of R (Fin (C.rank ⟨0, Nat.zero_lt_succ e⟩) → R)
  have hposZero : ∀ j : ℕ, 0 < j → Limits.IsZero (C.toChainComplex.X j) := by
    intro j hj
    by_cases hle : j ≤ e
    · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
      let jPred : Fin e := ⟨n, by omega⟩
      have hrank : C.rank jPred.succ = 0 :=
        rank_succ_eq_zero_of_positiveRankSum_eq_zero (C := C) hzero jPred
      -- Every positive displayed rank vanishes, so the corresponding term is zero.
      simpa [jPred] using term_isZero_of_rank_eq_zero (C := C) (j := jPred.succ) hrank
    · exact C.isZero_toChainComplex_X j (Nat.lt_of_not_ge hle)
  let toSingle : C.toChainComplex ⟶ (ChainComplex.single₀ (ModuleCat R)).obj X0 :=
    (ChainComplex.toSingle₀Equiv C.toChainComplex X0).symm
      ⟨(C.termIso ⟨0, Nat.zero_lt_succ e⟩).hom, by
        -- The source of `d 1 0` is already zero, so the augmentation compatibility is automatic.
        exact (hposZero 1 (by omega)).eq_of_src _ _⟩
  let fromSingle : (ChainComplex.single₀ (ModuleCat R)).obj X0 ⟶ C.toChainComplex :=
    (ChainComplex.fromSingle₀Equiv C.toChainComplex X0).symm
      ((C.termIso ⟨0, Nat.zero_lt_succ e⟩).inv)
  refine ⟨{ hom := toSingle, inv := fromSingle, hom_inv_id := ?_, inv_hom_id := ?_ }⟩
  · apply HomologicalComplex.hom_ext
    intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · -- In degree `0`, the two equivalence constructors recover the chosen coordinate isomorphism.
      ext x
      simpa [toSingle, fromSingle, X0] using
        ((C.termIso ⟨0, Nat.zero_lt_succ e⟩).toLinearEquiv.symm_apply_apply x)
    · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
      -- In positive degrees, both endomorphisms of the zero object coincide automatically.
      exact (hposZero (n + 1) (Nat.succ_pos _)).eq_of_src _ _
  · apply HomologicalComplex.hom_ext
    intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · -- In degree `0`, the backward and forward maps cancel on the chosen basis identification.
      ext x
      simpa [toSingle, fromSingle, X0] using
        ((C.termIso ⟨0, Nat.zero_lt_succ e⟩).toLinearEquiv.apply_symm_apply x)
    · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
      have hsingle :
          Limits.IsZero (((ChainComplex.single₀ (ModuleCat R)).obj X0).X (n + 1)) := by
        exact HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0 X0 (n + 1) (by simp)
      -- Positive degrees of `single₀` are zero, so the component equality is unique.
      exact hsingle.eq_of_src _ _

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Lemma 10.110.3: exactness together with a zero next term makes the owner
differential injective. -/
private lemma owner_diff_injective_of_exactAt_and_next_isZero
    {e : ℕ} (C : FiniteFreeComplex R e) (i : Fin e)
    (hexact : C.toChainComplex.ExactAt (i.1 + 1))
    (hnext : Limits.IsZero (C.toChainComplex.X (i.1 + 2))) :
    Function.Injective ((C.toChainComplex.d (i.1 + 1) i.1).hom) := by
  have hfun :
      Function.Exact ((C.toChainComplex.d (i.1 + 2) (i.1 + 1)).hom)
        ((C.toChainComplex.d (i.1 + 1) i.1).hom) :=
    (exactAt_iff_function_exact (K := C.toChainComplex) (j := i.1 + 1) (by omega)).1 hexact
  have hzero_morph : C.toChainComplex.d (i.1 + 2) (i.1 + 1) = 0 := by
    -- The incoming differential has zero source, so it is the zero map.
    exact hnext.eq_of_src _ _
  have hzero : (C.toChainComplex.d (i.1 + 2) (i.1 + 1)).hom = 0 := by
    simpa using congrArg ModuleCat.Hom.hom hzero_morph
  -- Rewriting the preceding differential to zero reduces exactness to injectivity.
  rw [hzero, LinearMap.exact_zero_iff_injective (P := C.toChainComplex.X (i.1 + 2))] at hfun
  exact hfun

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Lemma 10.110.3: evaluating the target coordinate isomorphism inverse on
`diffAt i v` rewrites it back to the owner differential in chain-complex coordinates. -/
lemma diffAt_termIso_inv_apply
    {e : ℕ} (C : FiniteFreeComplex R e) (i : Fin e) (v : C.term i.succ) :
    (C.termIso i.castSucc).inv.hom (C.diffAt i v) =
      (C.toChainComplex.d (i.1 + 1) i.1).hom ((C.termIso i.succ).inv.hom v) := by
  have hcomp :
      ModuleCat.ofHom (C.diffAt i) ≫ (C.termIso i.castSucc).inv =
        (C.termIso i.succ).inv ≫ C.toChainComplex.d (i.1 + 1) i.1 := by
    -- Record the conjugation identity once, rather than forcing `simp` to rediscover it.
    change
      (C.termIso i.succ).inv ≫ C.toChainComplex.d (i.1 + 1) i.1 ≫
          (C.termIso i.castSucc).hom ≫ (C.termIso i.castSucc).inv =
        (C.termIso i.succ).inv ≫ C.toChainComplex.d (i.1 + 1) i.1
    simp
  -- Evaluating the recorded morphism equality on `v` yields the pointwise transport formula.
  change ((ModuleCat.ofHom (C.diffAt i) ≫ (C.termIso i.castSucc).inv).hom v) =
    (((C.termIso i.succ).inv ≫ C.toChainComplex.d (i.1 + 1) i.1).hom v)
  rw [hcomp]
  rfl

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Lemma 10.110.3: if the next term of a finite free complex is zero, exactness
forces the displayed differential to be injective. -/
private lemma diffAt_injective_of_exactAt_and_next_isZero
    {e : ℕ} (C : FiniteFreeComplex R e) (i : Fin e)
    (hexact : C.toChainComplex.ExactAt (i.1 + 1))
    (hnext : Limits.IsZero (C.toChainComplex.X (i.1 + 2))) :
    Function.Injective (C.diffAt i) := by
  have howner :
      Function.Injective ((C.toChainComplex.d (i.1 + 1) i.1).hom) :=
    owner_diff_injective_of_exactAt_and_next_isZero (C := C) (i := i) hexact hnext
  intro x y hxy
  -- Transport the displayed differential equality to owner coordinates and use owner injectivity.
  have hterm :
      (C.toChainComplex.d (i.1 + 1) i.1).hom ((C.termIso i.succ).inv.hom x) =
        (C.toChainComplex.d (i.1 + 1) i.1).hom ((C.termIso i.succ).inv.hom y) := by
    have hx₁ :
        (C.toChainComplex.d (i.1 + 1) i.1).hom ((C.termIso i.succ).inv.hom x) =
          (C.termIso i.castSucc).inv.hom (C.diffAt i x) := by
      simpa using (diffAt_termIso_inv_apply (C := C) (i := i) (v := x)).symm
    have hx₂ :
        (C.termIso i.castSucc).inv.hom (C.diffAt i x) =
          (C.termIso i.castSucc).inv.hom (C.diffAt i y) := by
      simpa using congrArg (fun z ↦ (C.termIso i.castSucc).inv.hom z) hxy
    have hx₃ :
        (C.termIso i.castSucc).inv.hom (C.diffAt i y) =
          (C.toChainComplex.d (i.1 + 1) i.1).hom ((C.termIso i.succ).inv.hom y) := by
      simpa using diffAt_termIso_inv_apply (C := C) (i := i) (v := y)
    exact hx₁.trans (hx₂.trans hx₃)
  have hxy' :
      (C.termIso i.succ).inv.hom x = (C.termIso i.succ).inv.hom y := howner hterm
  have hy₁ :
      (C.termIso i.succ).hom.hom ((C.termIso i.succ).inv.hom x) = x := by
    simpa using (C.termIso i.succ).toLinearEquiv.apply_symm_apply x
  have hy₂ :
      (C.termIso i.succ).hom.hom ((C.termIso i.succ).inv.hom x) =
        (C.termIso i.succ).hom.hom ((C.termIso i.succ).inv.hom y) := by
    simpa using congrArg (fun z ↦ (C.termIso i.succ).hom.hom z) hxy'
  have hy₃ :
      (C.termIso i.succ).hom.hom ((C.termIso i.succ).inv.hom y) = y := by
    simpa using (C.termIso i.succ).toLinearEquiv.apply_symm_apply y
  exact hy₁.symm.trans (hy₂.trans hy₃)

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Lemma 10.110.3: exactness of a biproduct row in positive degree descends to the
first summand. -/
lemma exactAt_fst_of_biprod_exactAt_local
    {K L : ChainComplex (ModuleCat R) ℕ} {j : ℕ}
    (hj : 1 ≤ j)
    (h : (biprod K L).ExactAt j) :
    K.ExactAt j := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  have hmid : 1 + k = k + 1 := by
    omega
  rw [hmid] at h ⊢
  rw [HomologicalComplex.exactAt_iff_exact_up_to_refinements
      (biprod K L) (k + 2) (k + 1) k (by simp) (by simp)] at h
  rw [HomologicalComplex.exactAt_iff_exact_up_to_refinements
      K (k + 2) (k + 1) k (by simp) (by simp)]
  intro A x₂ hx₂
  -- Insert the cycle into the left summand and use exactness of the split row there.
  have hx₂' :
      x₂ ≫ (biprod.inl : K ⟶ biprod K L).f (k + 1) ≫ (biprod K L).d (k + 1) k = 0 := by
    have hcomm := (biprod.inl : K ⟶ biprod K L).comm (k + 1) k
    calc
      x₂ ≫ (biprod.inl : K ⟶ biprod K L).f (k + 1) ≫ (biprod K L).d (k + 1) k =
          x₂ ≫ (K.d (k + 1) k ≫ (biprod.inl : K ⟶ biprod K L).f k) := by
            simpa [Category.assoc] using congrArg (fun m ↦ x₂ ≫ m) hcomm
      _ = (x₂ ≫ K.d (k + 1) k) ≫ (biprod.inl : K ⟶ biprod K L).f k := by
            simp [Category.assoc]
      _ = 0 := by
            simp [hx₂]
  obtain ⟨A', π, hπ, y₁, hy₁⟩ := h (x₂ ≫ (biprod.inl : K ⟶ biprod K L).f (k + 1)) hx₂'
  refine ⟨A', π, hπ, y₁ ≫ (biprod.fst : biprod K L ⟶ K).f (k + 2), ?_⟩
  -- Project the resulting boundary back to the first summand.
  calc
    π ≫ x₂ = π ≫ x₂ ≫ (biprod.inl : K ⟶ biprod K L).f (k + 1) ≫
        (biprod.fst : biprod K L ⟶ K).f (k + 1) := by
          simp
    _ = y₁ ≫ (biprod K L).d (k + 2) (k + 1) ≫
        (biprod.fst : biprod K L ⟶ K).f (k + 1) := by
          simpa [Category.assoc] using congrArg
            (fun m ↦ m ≫ (biprod.fst : biprod K L ⟶ K).f (k + 1)) hy₁
    _ = y₁ ≫ (biprod.fst : biprod K L ⟶ K).f (k + 2) ≫ K.d (k + 2) (k + 1) := by
          have hcomm := (biprod.fst : biprod K L ⟶ K).comm (k + 2) (k + 1)
          simpa [Category.assoc] using congrArg (fun m ↦ y₁ ≫ m) hcomm.symm
    _ = (y₁ ≫ (biprod.fst : biprod K L ⟶ K).f (k + 2)) ≫ K.d (k + 2) (k + 1) := by
          simp [Category.assoc]

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Lemma 10.110.3: exactness of a split degree-`0` row with differential
`f ⊞ 𝟙` descends to exactness on the first summand. -/
lemma exact_zero_fst_of_biprod_identity_exact
    {A₁ A₀ K P : ModuleCat R}
    {f : A₁ ⟶ A₀} {g : A₀ ⟶ K}
    (hfg : f ≫ g = 0)
    (hexact :
      (ShortComplex.mk (biprod.map f (𝟙 P)) (biprod.desc g (0 : P ⟶ K)) (by
        refine biprod.hom_ext' (biprod.map f (𝟙 P) ≫ biprod.desc g (0 : P ⟶ K)) 0 ?_ ?_
        · simp [hfg]
        · simp)).Exact) :
    (ShortComplex.mk f g hfg).Exact := by
  have hdesc : biprod.desc g (0 : P ⟶ K) = biprod.fst ≫ g := by
    refine biprod.hom_ext' (biprod.desc g (0 : P ⟶ K)) (biprod.fst ≫ g) ?_ ?_
    · simp
    · simp
  have hmap_fst : biprod.map f (𝟙 P) ≫ biprod.fst = biprod.fst ≫ f := by
    refine biprod.hom_ext' (biprod.map f (𝟙 P) ≫ biprod.fst) (biprod.fst ≫ f) ?_ ?_
    · simp
    · simp
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hexact ⊢
  intro x
  constructor
  · intro hx
    let x' := (biprod.inl : A₀ ⟶ A₀ ⊞ P).hom x
    have hinl_fst : (biprod.inl : A₀ ⟶ A₀ ⊞ P) ≫ biprod.fst = 𝟙 A₀ := by
      simp
    have hx_inl : (biprod.fst : A₀ ⊞ P ⟶ A₀).hom x' = x := by
      exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hinl_fst) x
    have hx' : (biprod.desc g (0 : P ⟶ K)).hom x' = 0 := by
      -- The inserted element lives in the first summand, so the split augmentation reduces to `g`.
      calc
        (biprod.desc g (0 : P ⟶ K)).hom x' =
            g.hom ((biprod.fst : A₀ ⊞ P ⟶ A₀).hom x') := by
              exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hdesc) x'
        _ = g.hom x := by rw [hx_inl]
        _ = 0 := hx
    obtain ⟨y, hy⟩ := (hexact x').1 hx'
    refine ⟨(biprod.fst : A₁ ⊞ P ⟶ A₁).hom y, ?_⟩
    have hmap_fst_apply :
        (biprod.fst : A₀ ⊞ P ⟶ A₀).hom ((biprod.map f (𝟙 P)).hom y) =
          f.hom ((biprod.fst : A₁ ⊞ P ⟶ A₁).hom y) := by
      exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hmap_fst) y
    -- Project the preimage equation back to the first summand.
    have hy' := congrArg (fun z ↦ (biprod.fst : A₀ ⊞ P ⟶ A₀).hom z) hy
    calc
      f.hom ((biprod.fst : A₁ ⊞ P ⟶ A₁).hom y) =
          (biprod.fst : A₀ ⊞ P ⟶ A₀).hom ((biprod.map f (𝟙 P)).hom y) := by
            simpa using hmap_fst_apply.symm
      _ = (biprod.fst : A₀ ⊞ P ⟶ A₀).hom x' := hy'
      _ = x := hx_inl
  · rintro ⟨y, rfl⟩
    -- Membership in the image of `f` immediately gives a cycle for `g`.
    exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hfg) y

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Lemma 10.110.3: exactness of a split degree-`0` row on a biproduct target
descends to exactness on the first summand. -/
lemma exact_zero_fst_of_biprod_map_exact
    {A₁ A₀ K P₁ P₀ : ModuleCat R}
    {f : A₁ ⟶ A₀} {u : P₁ ⟶ P₀} {g : A₀ ⟶ K}
    (hfg : f ≫ g = 0)
    (hexact :
      (ShortComplex.mk (biprod.map f u) (biprod.desc g (0 : P₀ ⟶ K)) (by
        refine biprod.hom_ext' (biprod.map f u ≫ biprod.desc g (0 : P₀ ⟶ K)) 0 ?_ ?_
        · simp [hfg]
        · simp)).Exact) :
    (ShortComplex.mk f g hfg).Exact := by
  have hdesc : biprod.desc g (0 : P₀ ⟶ K) = biprod.fst ≫ g := by
    refine biprod.hom_ext' (biprod.desc g (0 : P₀ ⟶ K)) (biprod.fst ≫ g) ?_ ?_
    · simp
    · simp
  have hmap_fst : biprod.map f u ≫ biprod.fst = biprod.fst ≫ f := by
    refine biprod.hom_ext' (biprod.map f u ≫ biprod.fst) (biprod.fst ≫ f) ?_ ?_
    · simp
    · simp
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hexact ⊢
  intro x
  constructor
  · intro hx
    let x' := (biprod.inl : A₀ ⟶ A₀ ⊞ P₀).hom x
    have hinl_fst : (biprod.inl : A₀ ⟶ A₀ ⊞ P₀) ≫ biprod.fst = 𝟙 A₀ := by
      simp
    have hx_inl : (biprod.fst : A₀ ⊞ P₀ ⟶ A₀).hom x' = x := by
      exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hinl_fst) x
    have hx' : (biprod.desc g (0 : P₀ ⟶ K)).hom x' = 0 := by
      -- The inserted cycle lies in the first biproduct summand, so the split augmentation
      -- evaluates to `g` there.
      calc
        (biprod.desc g (0 : P₀ ⟶ K)).hom x' =
            g.hom ((biprod.fst : A₀ ⊞ P₀ ⟶ A₀).hom x') := by
              exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hdesc) x'
        _ = g.hom x := by rw [hx_inl]
        _ = 0 := hx
    obtain ⟨y, hy⟩ := (hexact x').1 hx'
    refine ⟨(biprod.fst : A₁ ⊞ P₁ ⟶ A₁).hom y, ?_⟩
    have hmap_fst_apply :
        (biprod.fst : A₀ ⊞ P₀ ⟶ A₀).hom ((biprod.map f u).hom y) =
          f.hom ((biprod.fst : A₁ ⊞ P₁ ⟶ A₁).hom y) := by
      exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hmap_fst) y
    have hy' := congrArg (fun z ↦ (biprod.fst : A₀ ⊞ P₀ ⟶ A₀).hom z) hy
    -- Project the chosen preimage back to the first summand to recover a preimage for `x`.
    calc
      f.hom ((biprod.fst : A₁ ⊞ P₁ ⟶ A₁).hom y) =
          (biprod.fst : A₀ ⊞ P₀ ⟶ A₀).hom ((biprod.map f u).hom y) := by
            simpa using hmap_fst_apply.symm
      _ = (biprod.fst : A₀ ⊞ P₀ ⟶ A₀).hom x' := hy'
      _ = x := hx_inl
  · rintro ⟨y, rfl⟩
    -- A genuine image element is automatically a cycle because `g ∘ f = 0`.
    exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hfg) y

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Lemma 10.110.3: if the split augmentation `[g, 0]` is surjective, then `g` is
already surjective on the first summand. -/
lemma surjective_fst_of_biprod_desc_zero
    {A K P : ModuleCat R}
    {g : A ⟶ K}
    (hsurj : Function.Surjective (biprod.desc g (0 : P ⟶ K)).hom) :
    Function.Surjective g.hom := by
  have hdesc : biprod.desc g (0 : P ⟶ K) = biprod.fst ≫ g := by
    refine biprod.hom_ext' (biprod.desc g (0 : P ⟶ K)) (biprod.fst ≫ g) ?_ ?_
    · simp
    · simp
  intro z
  obtain ⟨y, hy⟩ := hsurj z
  refine ⟨(biprod.fst : A ⊞ P ⟶ A).hom y, ?_⟩
  -- The second summand contributes nothing to `[g, 0]`, so projecting the chosen preimage works.
  calc
    g.hom ((biprod.fst : A ⊞ P ⟶ A).hom y) = (biprod.desc g (0 : P ⟶ K)).hom y := by
      exact (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hdesc) y).symm
    _ = z := hy

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Lemma 10.110.3: if the second biproduct summand is zero, any map out of the
biproduct is determined by its first component. -/
lemma biprod_desc_eq_desc_zero_of_isZero
    {A P K : ModuleCat R}
    (hP : Limits.IsZero P)
    (g : A ⊞ P ⟶ K) :
    g = biprod.desc ((biprod.inl : A ⟶ A ⊞ P) ≫ g) (0 : P ⟶ K) := by
  -- Compare the two morphisms on the two coproduct injections.
  refine biprod.hom_ext' g _ ?_ ?_
  · simp
  · exact hP.eq_of_src _ _

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Lemma 10.110.3: if the identity-disk summand is supported strictly above degree
`0`, then its degree-`0` term is zero. -/
lemma identityDiskComplex_X_zero_isZero_of_pos
    {e : ℕ} (i : Fin e)
    (hi : 0 < i.1) :
    Limits.IsZero ((FiniteFreeComplex.identityDiskComplex (R := R) i).X 0) := by
  have hX :
      ((FiniteFreeComplex.identityDiskComplex (R := R) i).X 0) =
        ModuleCat.of R (Fin (if 0 = i.1 + 1 ∨ 0 = i.1 then 1 else 0) → R) := by
    rfl
  rw [hX]
  -- Once degree `0` is off the support, the term is the empty free module.
  have hsucc_ne : ¬ 0 = i.1 + 1 := by
    omega
  have hzero_ne : ¬ 0 = i.1 := by
    omega
  have hzero_term :
      Limits.IsZero (ModuleCat.of R (Fin (if 0 = i.1 then 1 else 0) → R)) := by
    simpa [hzero_ne] using
      (ModuleCat.isZero_of_subsingleton (ModuleCat.of R (Fin 0 → R)))
  simpa [hsucc_ne] using hzero_term

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.110.3: every positive-degree component of a map to `single₀` is zero. -/
lemma moduleSingle_component_eq_zero_succ
    {F : ChainComplex (ModuleCat R) ℕ}
    (φ : F ⟶ moduleSingle[R] (ResidueField R))
    (n : ℕ) :
    φ.f (n + 1) = 0 := by
  -- The target complex `single₀` vanishes away from degree `0`, so any higher component is unique.
  apply IsZero.eq_of_tgt
  apply HomologicalComplex.isZero_single_obj_X
  simp

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: every map from an identity-disk complex to `single₀ κ`
has zero degree-`0` component. -/
lemma identityDiskComplex_to_single_f_zero_eq_zero
    {e : ℕ} (i : Fin e)
    (φ : FiniteFreeComplex.identityDiskComplex (R := R) i ⟶
      moduleSingle[R] (ResidueField R)) :
    φ.f 0 = 0 := by
  by_cases hi : i.1 = 0
  · have hcomm :
        (FiniteFreeComplex.identityDiskComplex (R := R) i).d (i.1 + 1) i.1 ≫ φ.f i.1 =
          φ.f (i.1 + 1) ≫
            (moduleSingle[R] (ResidueField R)).d (i.1 + 1) i.1 := by
      -- Use the chain-map square at the supported identity-disk differential.
      exact (φ.comm (i.1 + 1) i.1).symm
    have htarget :
        φ.f (i.1 + 1) ≫
            (moduleSingle[R] (ResidueField R)).d (i.1 + 1) i.1 =
          0 := by
      -- The positive-degree component of the map to `single₀` is already zero.
      rw [moduleSingle_component_eq_zero_succ (R := R) φ i.1]
      simp
    have hdφ :
        (FiniteFreeComplex.identityDiskComplex (R := R) i).d (i.1 + 1) i.1 ≫
            φ.f i.1 =
          0 := by
      simpa [htarget] using hcomm
    have hpre :
        eqToHom (FiniteFreeComplex.identityDiskComplex_X_eq_succ (R := R) (e := e) i).symm ≫
            (FiniteFreeComplex.identityDiskComplex (R := R) i).d (i.1 + 1) i.1 ≫
              φ.f i.1 =
          0 := by
      calc
        eqToHom (FiniteFreeComplex.identityDiskComplex_X_eq_succ (R := R) (e := e) i).symm ≫
            (FiniteFreeComplex.identityDiskComplex (R := R) i).d (i.1 + 1) i.1 ≫
              φ.f i.1 =
          eqToHom (FiniteFreeComplex.identityDiskComplex_X_eq_succ (R := R) (e := e) i).symm ≫
            ((FiniteFreeComplex.identityDiskComplex (R := R) i).d (i.1 + 1) i.1 ≫
              φ.f i.1) := by
            simp
        _ = 0 := by
            rw [hdφ]
            simp
    have hpre' :
        eqToHom (FiniteFreeComplex.identityDiskComplex_X_eq_castSucc (R := R) (e := e) i).symm ≫
            φ.f i.1 =
          0 := by
      -- The supported identity-disk differential is the identity after the displayed transports.
      calc
        eqToHom (FiniteFreeComplex.identityDiskComplex_X_eq_castSucc (R := R) (e := e) i).symm ≫
            φ.f i.1 =
          (eqToHom (FiniteFreeComplex.identityDiskComplex_X_eq_succ (R := R) (e := e) i).symm ≫
              (FiniteFreeComplex.identityDiskComplex (R := R) i).d (i.1 + 1) i.1) ≫
            φ.f i.1 := by
            rw [FiniteFreeComplex.identityDiskComplex_eqToHom_symm_comp_d (R := R) (e := e) i]
        _ =
          eqToHom (FiniteFreeComplex.identityDiskComplex_X_eq_succ (R := R) (e := e) i).symm ≫
            (FiniteFreeComplex.identityDiskComplex (R := R) i).d (i.1 + 1) i.1 ≫
              φ.f i.1 := by
            simp [Category.assoc]
        _ = 0 := hpre
    have hzero_i : φ.f i.1 = 0 := by
      apply (cancel_epi
        (eqToHom
          (FiniteFreeComplex.identityDiskComplex_X_eq_castSucc (R := R) (e := e) i).symm)).1
      simpa using hpre'
    rw [hi] at hzero_i
    exact hzero_i
  · have hzero :
        Limits.IsZero ((FiniteFreeComplex.identityDiskComplex (R := R) i).X 0) :=
      identityDiskComplex_X_zero_isZero_of_pos (R := R) i (Nat.pos_of_ne_zero hi)
    -- Off the supported degree, the source object itself is zero.
    exact hzero.eq_of_src _ _

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: after objectwise biproduct comparison, the differential
of a binary biproduct complex is the biproduct map of the two summand differentials. -/
lemma biprodXIso_differential_hom_local
    {K L : ChainComplex (ModuleCat R) ℕ} (j : ℕ) :
    ((biprod K L).d (j + 1) j) ≫ (HomologicalComplex.biprodXIso K L j).hom =
      (HomologicalComplex.biprodXIso K L (j + 1)).hom ≫
        biprod.map (K.d (j + 1) j) (L.d (j + 1) j) := by
  -- Compare after the two objectwise biproduct projections.
  apply biprod.hom_ext
  · calc
      ((biprod K L).d (j + 1) j) ≫ (HomologicalComplex.biprodXIso K L j).hom ≫
          biprod.fst =
        ((biprod K L).d (j + 1) j) ≫ (biprod.fst : biprod K L ⟶ K).f j := by
          rw [HomologicalComplex.biprodXIso_hom_fst]
      _ = (biprod.fst : biprod K L ⟶ K).f (j + 1) ≫ K.d (j + 1) j := by
          simpa [Category.assoc] using
            ((biprod.fst : biprod K L ⟶ K).comm (j + 1) j).symm
      _ = (HomologicalComplex.biprodXIso K L (j + 1)).hom ≫ biprod.fst ≫
          K.d (j + 1) j := by
          simpa [Category.assoc] using
            congrArg (fun m ↦ m ≫ K.d (j + 1) j)
              (HomologicalComplex.biprodXIso_hom_fst K L (j + 1)).symm
      _ = (HomologicalComplex.biprodXIso K L (j + 1)).hom ≫
          biprod.map (K.d (j + 1) j) (L.d (j + 1) j) ≫ biprod.fst := by
          simp
  · calc
      ((biprod K L).d (j + 1) j) ≫ (HomologicalComplex.biprodXIso K L j).hom ≫
          biprod.snd =
        ((biprod K L).d (j + 1) j) ≫ (biprod.snd : biprod K L ⟶ L).f j := by
          rw [HomologicalComplex.biprodXIso_hom_snd]
      _ = (biprod.snd : biprod K L ⟶ L).f (j + 1) ≫ L.d (j + 1) j := by
          simpa [Category.assoc] using
            ((biprod.snd : biprod K L ⟶ L).comm (j + 1) j).symm
      _ = (HomologicalComplex.biprodXIso K L (j + 1)).hom ≫ biprod.snd ≫
          L.d (j + 1) j := by
          simpa [Category.assoc] using
            congrArg (fun m ↦ m ≫ L.d (j + 1) j)
              (HomologicalComplex.biprodXIso_hom_snd K L (j + 1)).symm
      _ = (HomologicalComplex.biprodXIso K L (j + 1)).hom ≫
          biprod.map (K.d (j + 1) j) (L.d (j + 1) j) ≫ biprod.snd := by
          simp

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: splitting off an identity-disk along a unit entry strictly
decreases the total displayed rank in positive degrees. -/
lemma positiveRankSum_splitRank_lt_of_unit_entry
    {e : ℕ} (C C' : FiniteFreeComplex R e) (i : Fin e)
    (hunit :
      ∃ a : Fin (C.rank i.succ), ∃ b : Fin (C.rank i.castSucc),
        IsUnit (C.diffEntry i a b))
    (hsplit : C'.rank = FiniteFreeComplex.splitRank C.rank i) :
    positiveRankSum (R := R) C' < positiveRankSum (R := R) C := by
  obtain ⟨a, _b, _hu⟩ := hunit
  have hi_pos : 0 < C.rank i.succ :=
    lt_of_le_of_lt (Nat.zero_le a.1) a.2
  -- All summands weakly decrease, and the `i`-summand drops by one.
  refine Finset.sum_lt_sum (fun j _ ↦ ?_) ⟨i, Finset.mem_univ i, ?_⟩
  · rw [hsplit, FiniteFreeComplex.splitRank]
    by_cases hji : j = i
    · subst hji
      simp
    · by_cases hcast : j.succ = i.castSucc
      · simp [hcast]
      · simp [hji, hcast]
  · have hpred : C.rank i.succ - 1 < C.rank i.succ := by
      simpa [Nat.pred_eq_sub_one] using Nat.pred_lt (Nat.ne_of_gt hi_pos)
    simpa [hsplit, FiniteFreeComplex.splitRank] using hpred

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: if no displayed differential entry is a unit, then every entry
lies in the maximal ideal of the local ring. -/
lemma diffEntry_mem_maximal_of_no_unit
    {e : ℕ} (C : FiniteFreeComplex R e)
    (hnoUnit :
      ¬ ∃ i : Fin e, ∃ a : Fin (C.rank i.succ), ∃ b : Fin (C.rank i.castSucc),
          IsUnit (C.diffEntry i a b))
    (i : Fin e) (a : Fin (C.rank i.succ)) (b : Fin (C.rank i.castSucc)) :
    C.diffEntry i a b ∈ maximalIdeal R := by
  -- In a local ring, nonunits are exactly elements of the maximal ideal.
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hunit
  exact hnoUnit ⟨i, a, b, hunit⟩

/-- Helper for Lemma 10.110.3: the projected augmentation after splitting off an
`identityDiskComplex` summand is obtained by composing with the first biproduct inclusion. -/
noncomputable abbrev projected_augmentation
    {e : ℕ} (C C' : FiniteFreeComplex R e) (i : Fin e)
    (ρ : C.toChainComplex ⟶ moduleSingle[R] (ResidueField R))
    (eIso :
      C.toChainComplex ≅
        biprod C'.toChainComplex (FiniteFreeComplex.identityDiskComplex (R := R) i)) :
    C'.toChainComplex ⟶ moduleSingle[R] (ResidueField R) :=
  (biprod.inl :
      C'.toChainComplex ⟶
        biprod C'.toChainComplex (FiniteFreeComplex.identityDiskComplex (R := R) i)) ≫
    eIso.inv ≫ ρ

/-- Helper for Lemma 10.110.3: the augmentation on the split biproduct is the original
augmentation transported across the chosen chain-complex isomorphism. -/
noncomputable abbrev split_augmentation
    {e : ℕ} (C C' : FiniteFreeComplex R e) (i : Fin e)
    (ρ : C.toChainComplex ⟶ moduleSingle[R] (ResidueField R))
    (eIso :
      C.toChainComplex ≅
        biprod C'.toChainComplex (FiniteFreeComplex.identityDiskComplex (R := R) i)) :
    biprod C'.toChainComplex (FiniteFreeComplex.identityDiskComplex (R := R) i) ⟶
      moduleSingle[R] (ResidueField R) :=
  eIso.inv ≫ ρ

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.110.3: transporting the original augmentation across the split
isomorphism preserves exactness in every positive degree. -/
lemma projected_augmentation_exactAt_succ_of_biprod_identityDisk
    {e : ℕ} (C C' : FiniteFreeComplex R e) (i : Fin e)
    (ρ : C.toChainComplex ⟶ moduleSingle[R] (ResidueField R))
    (hρ : ChainComplex.IsFiniteFreeResolution ρ)
    (eIso :
      C.toChainComplex ≅
        biprod C'.toChainComplex (FiniteFreeComplex.identityDiskComplex (R := R) i))
    (n : ℕ) :
    C'.toChainComplex.ExactAt (n + 1) := by
  letI : QuasiIso ρ := hρ.toIsFreeResolution.toQuasiIso
  have hExactC : C.toChainComplex.ExactAt (n + 1) := by
    -- The original augmentation is a quasi-isomorphism to `single₀`, hence exact in positive
    -- degrees.
    exact
      (quasiIsoAt_iff_exactAt' ρ (n + 1)
        (ChainComplex.exactAt_succ_single_obj (ModuleCat.of R (ResidueField R)) n)).1
        inferInstance

  have hExactSplit :
      (biprod C'.toChainComplex (FiniteFreeComplex.identityDiskComplex (R := R) i)).ExactAt
        (n + 1) := by
    -- Transport exactness across the chosen chain-complex isomorphism before projecting.
    exact hExactC.of_iso eIso
  -- Exactness of the biproduct row descends to the first summand.
  exact
    exactAt_fst_of_biprod_exactAt_local (R := R)
      (hj := Nat.succ_le_succ (Nat.zero_le n)) hExactSplit

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.110.3: after transporting the augmentation across a split-off
`identityDiskComplex`, the degree-`0` component becomes `[g, 0]` after rewriting the chain-
complex biproduct term through `HomologicalComplex.biprodXIso`. -/
lemma split_augmentation_f_zero_eq_biprodXIso_hom_desc_zero_of_biprod_identityDisk
    {e : ℕ} (C C' : FiniteFreeComplex R e) (i : Fin e)
    (ρ : C.toChainComplex ⟶ moduleSingle[R] (ResidueField R))
    (eIso :
      C.toChainComplex ≅
        biprod C'.toChainComplex (FiniteFreeComplex.identityDiskComplex (R := R) i)) :
    (split_augmentation (R := R) C C' i ρ eIso).f 0 =
      (HomologicalComplex.biprodXIso C'.toChainComplex
        (FiniteFreeComplex.identityDiskComplex (R := R) i) 0).hom ≫
        biprod.desc ((projected_augmentation (R := R) C C' i ρ eIso).f 0)
          (0 :
            ((FiniteFreeComplex.identityDiskComplex (R := R) i).X 0) ⟶
              ModuleCat.of R (ResidueField R)) := by
  let L := FiniteFreeComplex.identityDiskComplex (R := R) i
  let σ := split_augmentation (R := R) C C' i ρ eIso
  let τ := projected_augmentation (R := R) C C' i ρ eIso
  let q := HomologicalComplex.biprodXIso C'.toChainComplex L 0
  -- It is cheaper to compare after precomposing with the inverse objectwise biproduct
  -- comparison, where the source is the explicit biproduct.
  apply (cancel_epi q.inv).1
  simp only [q, L, Iso.inv_hom_id_assoc]
  refine biprod.hom_ext' (q.inv ≫ σ.f 0)
    (biprod.desc (τ.f 0) (0 : L.X 0 ⟶ ModuleCat.of R (ResidueField R)))
    ?_ ?_
  · calc
      biprod.inl ≫ q.inv ≫ σ.f 0 =
          (biprod.inl : C'.toChainComplex ⟶ biprod C'.toChainComplex L).f 0 ≫ σ.f 0 := by
            simp [q, L]
      _ = τ.f 0 := by
            rfl
      _ = biprod.inl ≫
          biprod.desc (τ.f 0) (0 : L.X 0 ⟶ ModuleCat.of R (ResidueField R)) := by
            simp
  · have hzero :
        (biprod.inr : L ⟶ biprod C'.toChainComplex L).f 0 ≫ σ.f 0 = 0 := by
      have hcomponent :
          ((biprod.inr : L ⟶ biprod C'.toChainComplex L) ≫ σ).f 0 = 0 :=
        identityDiskComplex_to_single_f_zero_eq_zero (R := R) i
          ((biprod.inr : L ⟶ biprod C'.toChainComplex L) ≫ σ)
      simpa [Category.assoc] using hcomponent
    calc
      biprod.inr ≫ q.inv ≫ σ.f 0 =
          (biprod.inr : L ⟶ biprod C'.toChainComplex L).f 0 ≫ σ.f 0 := by
            simp [q, L]
      _ = 0 := hzero
      _ = biprod.inr ≫
          biprod.desc (τ.f 0) (0 : L.X 0 ⟶ ModuleCat.of R (ResidueField R)) := by
            exact (biprod.inr_desc (τ.f 0)
              (0 : L.X 0 ⟶ ModuleCat.of R (ResidueField R))).symm

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.110.3: the projected augmentation is exact in degree `0`. -/
lemma projected_augmentation_exact_zero_of_biprod_identityDisk
    {e : ℕ} (C C' : FiniteFreeComplex R e) (i : Fin e)
    (ρ : C.toChainComplex ⟶ moduleSingle[R] (ResidueField R))
    (hρ : ChainComplex.IsFiniteFreeResolution ρ)
    (eIso :
      C.toChainComplex ≅
        biprod C'.toChainComplex (FiniteFreeComplex.identityDiskComplex (R := R) i)) :
    Function.Exact
      (C'.toChainComplex.d 1 0).hom
      ((projected_augmentation (R := R) C C' i ρ eIso).f 0).hom := by
  let L := FiniteFreeComplex.identityDiskComplex (R := R) i
  let σ := split_augmentation (R := R) C C' i ρ eIso
  let τ := projected_augmentation (R := R) C C' i ρ eIso
  let q₀ := HomologicalComplex.biprodXIso C'.toChainComplex L 0
  let q₁ := HomologicalComplex.biprodXIso C'.toChainComplex L 1
  have hσ_quasi : QuasiIso σ := by
    dsimp [σ, split_augmentation]
    infer_instance
  letI : QuasiIso σ := hσ_quasi
  have hσ_comm :
      (biprod C'.toChainComplex L).d 1 0 ≫ σ.f 0 = 0 := by
    have htarget : σ.f 1 ≫ (moduleSingle[R] (ResidueField R)).d 1 0 = 0 := by
      calc
        σ.f 1 ≫ (moduleSingle[R] (ResidueField R)).d 1 0 =
            (0 : (biprod C'.toChainComplex L).X 1 ⟶
              (moduleSingle[R] (ResidueField R)).X 1) ≫
              (moduleSingle[R] (ResidueField R)).d 1 0 := by
              rw [moduleSingle_component_eq_zero_succ (R := R) σ 0]
        _ = 0 := zero_comp
    -- The split augmentation is a chain map, so its degree-`0` component kills boundaries.
    simpa [htarget] using (σ.comm 1 0).symm
  let Sσ : ShortComplex (ModuleCat R) :=
    ShortComplex.mk ((biprod C'.toChainComplex L).d 1 0) (σ.f 0) hσ_comm
  have hσ_exact :
      Function.Exact ((biprod C'.toChainComplex L).d 1 0).hom (σ.f 0).hom := by
    have hSσ_exact : Sσ.Exact := by
      -- Exactness in degree `0` comes from the quasi-isomorphism to `single₀`.
      simpa [Sσ, σ] using
        quasiIso_single_exact_zero (R := R) (N := ResidueField R)
          (G := biprod C'.toChainComplex L) σ
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact Sσ).1 hSσ_exact
  have hdiff :
      ((biprod C'.toChainComplex L).d 1 0) ≫ q₀.hom =
        q₁.hom ≫ biprod.map (C'.toChainComplex.d 1 0) (L.d 1 0) := by
    simpa [q₀, q₁] using
      biprodXIso_differential_hom_local (R := R) (K := C'.toChainComplex) (L := L) 0
  have haug :
      σ.f 0 = q₀.hom ≫
        biprod.desc (τ.f 0) (0 : L.X 0 ⟶ ModuleCat.of R (ResidueField R)) := by
    simpa [σ, τ, q₀, L] using
      split_augmentation_f_zero_eq_biprodXIso_hom_desc_zero_of_biprod_identityDisk
        (R := R) C C' i ρ eIso
  have h₁₂ :
      (biprod.map (C'.toChainComplex.d 1 0) (L.d 1 0)).hom.comp q₁.hom.hom =
        q₀.hom.hom.comp ((biprod C'.toChainComplex L).d 1 0).hom := by
    ext x
    -- The differential bridge supplies the first ladder square.
    simpa [LinearMap.comp_apply] using
      LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hdiff.symm) x
  have h₂₃ :
      (biprod.desc (τ.f 0) (0 : L.X 0 ⟶ ModuleCat.of R (ResidueField R))).hom.comp
          q₀.hom.hom =
        (LinearEquiv.refl R (ModuleCat.of R (ResidueField R))).toLinearMap.comp
          (σ.f 0).hom := by
    ext x
    -- The augmentation bridge supplies the second ladder square.
    simpa [LinearMap.comp_apply] using
      LinearMap.congr_fun (congrArg ModuleCat.Hom.hom haug.symm) x
  have hbiprod_exact :
      Function.Exact
        (biprod.map (C'.toChainComplex.d 1 0) (L.d 1 0)).hom
        (biprod.desc (τ.f 0) (0 : L.X 0 ⟶ ModuleCat.of R (ResidueField R))).hom :=
    Function.Exact.of_ladder_linearEquiv_of_exact
      (e₁ := q₁.toLinearEquiv) (e₂ := q₀.toLinearEquiv)
      (e₃ := LinearEquiv.refl R (ModuleCat.of R (ResidueField R))) h₁₂ h₂₃ hσ_exact
  have hfg : C'.toChainComplex.d 1 0 ≫ τ.f 0 = 0 := by
    have htarget : τ.f 1 ≫ (moduleSingle[R] (ResidueField R)).d 1 0 = 0 := by
      calc
        τ.f 1 ≫ (moduleSingle[R] (ResidueField R)).d 1 0 =
            (0 : C'.toChainComplex.X 1 ⟶ (moduleSingle[R] (ResidueField R)).X 1) ≫
              (moduleSingle[R] (ResidueField R)).d 1 0 := by
              rw [moduleSingle_component_eq_zero_succ (R := R) τ 0]
        _ = 0 := zero_comp
    -- The projected augmentation is a chain map, hence its degree-`0` part kills boundaries.
    simpa [τ, htarget] using (τ.comm 1 0).symm
  exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 <|
    exact_zero_fst_of_biprod_map_exact (R := R)
      (f := C'.toChainComplex.d 1 0) (u := L.d 1 0) (g := τ.f 0)
      hfg ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2 hbiprod_exact)

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.110.3: the projected augmentation remains surjective in degree `0`. -/
lemma projected_augmentation_epi_zero_of_biprod_identityDisk
    {e : ℕ} (C C' : FiniteFreeComplex R e) (i : Fin e)
    (ρ : C.toChainComplex ⟶ moduleSingle[R] (ResidueField R))
    (hρ : ChainComplex.IsFiniteFreeResolution ρ)
    (eIso :
      C.toChainComplex ≅
        biprod C'.toChainComplex (FiniteFreeComplex.identityDiskComplex (R := R) i)) :
    Function.Surjective ((projected_augmentation (R := R) C C' i ρ eIso).f 0).hom := by
  let L := FiniteFreeComplex.identityDiskComplex (R := R) i
  let σ := split_augmentation (R := R) C C' i ρ eIso
  let τ := projected_augmentation (R := R) C C' i ρ eIso
  let q₀ := HomologicalComplex.biprodXIso C'.toChainComplex L 0
  have hσ_quasi : QuasiIso σ := by
    dsimp [σ, split_augmentation]
    infer_instance
  letI : QuasiIso σ := hσ_quasi
  have hσ_surj : Function.Surjective (σ.f 0).hom := by
    -- The split augmentation is quasi-isomorphic to `single₀`, so it is onto in degree `0`.
    exact (ModuleCat.epi_iff_surjective _).mp
      (quasiIso_single_epi_zero (R := R) (N := ResidueField R)
        (G := biprod C'.toChainComplex L) σ)
  have haug :
      σ.f 0 = q₀.hom ≫
        biprod.desc (τ.f 0) (0 : L.X 0 ⟶ ModuleCat.of R (ResidueField R)) := by
    simpa [σ, τ, q₀, L] using
      split_augmentation_f_zero_eq_biprodXIso_hom_desc_zero_of_biprod_identityDisk
        (R := R) C C' i ρ eIso
  have hdesc_surj :
      Function.Surjective
        (biprod.desc (τ.f 0) (0 : L.X 0 ⟶ ModuleCat.of R (ResidueField R))).hom := by
    intro z
    obtain ⟨x, hx⟩ := hσ_surj z
    refine ⟨q₀.hom.hom x, ?_⟩
    -- Transport the chosen preimage across the degree-`0` objectwise biproduct comparison.
    simpa [Category.assoc] using
      (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom haug.symm) x).trans hx
  exact surjective_fst_of_biprod_desc_zero (R := R) (g := τ.f 0) hdesc_surj

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.110.3: removing an `identityDiskComplex` summand from a bounded finite
free resolution preserves the residue-field resolution property. -/
lemma split_identityDisk_preserves_residueField_resolution
    {e : ℕ} (C C' : FiniteFreeComplex R e) (i : Fin e)
    (ρ : C.toChainComplex ⟶ moduleSingle[R] (ResidueField R))
    (hρ : ChainComplex.IsFiniteFreeResolution ρ)
    (eIso :
      C.toChainComplex ≅
        biprod C'.toChainComplex (FiniteFreeComplex.identityDiskComplex (R := R) i)) :
    ChainComplex.IsFiniteFreeResolution
      (projected_augmentation (R := R) C C' i ρ eIso) := by
  let τ := projected_augmentation (R := R) C C' i ρ eIso
  have hτ_quasi : QuasiIso τ := by
    refine ⟨fun n ↦ ?_⟩
    cases n with
    | zero =>
        rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
        · refine ⟨?_, ?_⟩
          · have hfg : C'.toChainComplex.d 1 0 ≫ τ.f 0 = 0 := by
              have htarget : τ.f 1 ≫ (moduleSingle[R] (ResidueField R)).d 1 0 = 0 := by
                calc
                  τ.f 1 ≫ (moduleSingle[R] (ResidueField R)).d 1 0 =
                      (0 : C'.toChainComplex.X 1 ⟶
                        (moduleSingle[R] (ResidueField R)).X 1) ≫
                        (moduleSingle[R] (ResidueField R)).d 1 0 := by
                        rw [moduleSingle_component_eq_zero_succ (R := R) τ 0]
                  _ = 0 := zero_comp
              simpa [τ, htarget] using (τ.comm 1 0).symm
            let S₀ : ShortComplex (ModuleCat R) :=
              ShortComplex.mk (C'.toChainComplex.d 1 0) (τ.f 0) hfg
            have hExact₀ :
                Function.Exact (C'.toChainComplex.d 1 0).hom (τ.f 0).hom :=
              projected_augmentation_exact_zero_of_biprod_identityDisk
                (R := R) C C' i ρ hρ eIso
            exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S₀).2 hExact₀
          · exact (ModuleCat.epi_iff_surjective _).2 <|
              projected_augmentation_epi_zero_of_biprod_identityDisk
                (R := R) C C' i ρ hρ eIso
        · simp
          rfl
        · rfl
        · rfl
    | succ n =>
        rw [quasiIsoAt_iff_exactAt']
        · -- Positive-degree exactness descends from the split biproduct resolution.
          exact projected_augmentation_exactAt_succ_of_biprod_identityDisk
            (R := R) C C' i ρ hρ eIso n
        · apply ChainComplex.exactAt_succ_single_obj
  exact
    { toIsFreeResolution :=
        { toQuasiIso := hτ_quasi
          termwise_free := FiniteFreeComplex.isTermwiseFree C' }
      termwise_finite := FiniteFreeComplex.isTermwiseFinite C' }

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.110.3: a bounded finite free resolution of the residue field can be
minimalized so that every matrix entry of every differential lies in the maximal ideal. -/
lemma exists_minimal_residueField_finiteFreeComplex
    {e : ℕ} (C : FiniteFreeComplex R e)
    (ρ : C.toChainComplex ⟶ moduleSingle[R] (ResidueField R))
    (hρ : ChainComplex.IsFiniteFreeResolution ρ) :
    ∃ (Cmin : FiniteFreeComplex R e)
      (ρmin : Cmin.toChainComplex ⟶ moduleSingle[R] (ResidueField R)),
      ChainComplex.IsFiniteFreeResolution ρmin ∧
        ∀ i : Fin e, ∀ a : Fin (Cmin.rank i.succ), ∀ b : Fin (Cmin.rank i.castSucc),
          FiniteFreeComplex.diffEntry Cmin i a b ∈ maximalIdeal R := by
  let P : ℕ → Prop := fun n ↦
    ∀ (D : FiniteFreeComplex R e)
      (π : D.toChainComplex ⟶ moduleSingle[R] (ResidueField R)),
      positiveRankSum (R := R) D = n →
        ChainComplex.IsFiniteFreeResolution π →
          ∃ (Dmin : FiniteFreeComplex R e)
            (πmin : Dmin.toChainComplex ⟶ moduleSingle[R] (ResidueField R)),
            ChainComplex.IsFiniteFreeResolution πmin ∧
              ∀ i : Fin e, ∀ a : Fin (Dmin.rank i.succ),
                ∀ b : Fin (Dmin.rank i.castSucc),
                  FiniteFreeComplex.diffEntry Dmin i a b ∈ maximalIdeal R
  have hP : ∀ n : ℕ, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro D π hsum hπ
        by_cases hunit :
            ∃ i : Fin e, ∃ a : Fin (D.rank i.succ), ∃ b : Fin (D.rank i.castSucc),
              IsUnit (D.diffEntry i a b)
        · obtain ⟨i, a, b, hu⟩ := hunit
          obtain ⟨D', hsplit, ⟨eiso⟩⟩ :=
            FiniteFreeComplex.exists_iso_biprod_identityDisk_of_isUnit_diffEntry
              (C := D) (i := i) ⟨a, b, hu⟩
          let π' : D'.toChainComplex ⟶ moduleSingle[R] (ResidueField R) :=
            projected_augmentation (R := R) D D' i π eiso
          have hπ' : ChainComplex.IsFiniteFreeResolution π' :=
            split_identityDisk_preserves_residueField_resolution
              (R := R) D D' i π hπ eiso
          have hlt :
              positiveRankSum (R := R) D' < positiveRankSum (R := R) D :=
            positiveRankSum_splitRank_lt_of_unit_entry (R := R) (C := D) (C' := D')
              (i := i) ⟨a, b, hu⟩ hsplit
          have hlt' : positiveRankSum (R := R) D' < n := by
            simpa [hsum] using hlt
          -- The unit-entry branch recurses on the strictly smaller split complex.
          exact ih (positiveRankSum (R := R) D') hlt' D' π' rfl hπ'
        · have hminimal :
              ∀ i : Fin e, ∀ a : Fin (D.rank i.succ), ∀ b : Fin (D.rank i.castSucc),
                FiniteFreeComplex.diffEntry D i a b ∈ maximalIdeal R := by
            intro i a b
            exact diffEntry_mem_maximal_of_no_unit (R := R) (C := D) hunit i a b
          -- If no unit entry exists, the current finite free resolution is already minimal.
          exact ⟨D, π, hπ, hminimal⟩
  exact hP (positiveRankSum (R := R) C) C ρ rfl hρ


end
