import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_102_3 (from Chap10) -/
open CategoryTheory CategoryTheory.Limits ChainComplex HomologicalComplex IsLocalRing

noncomputable section

universe u

section

variable {R : Type u} [CommRing R]
variable {e : ℕ}

/-- A chain complex is a direct sum of trivial complexes if it is obtained from degree-zero single
complexes and two-term identity-disk complexes by finitely many binary biproducts, up to
isomorphism. -/
inductive IsDirectSumOfTrivialComplexes : ChainComplex (ModuleCat R) ℕ → Prop
  | single₀ (n : ℕ) :
      IsDirectSumOfTrivialComplexes
        ((ChainComplex.single₀ (ModuleCat R)).obj (ModuleCat.of R (Fin n → R)))
  | disk (i n : ℕ) :
      IsDirectSumOfTrivialComplexes
        (HomologicalComplex.double
          (𝟙 (ModuleCat.of R (Fin n → R)))
          (show (ComplexShape.down ℕ).Rel (i + 1) i from rfl))
  | identityDisk {e : ℕ} (i : Fin e) :
      IsDirectSumOfTrivialComplexes (FiniteFreeComplex.identityDiskComplex (R := R) i)
  | biprod {C₁ C₂ : ChainComplex (ModuleCat R) ℕ} :
      IsDirectSumOfTrivialComplexes C₁ →
      IsDirectSumOfTrivialComplexes C₂ →
      IsDirectSumOfTrivialComplexes (biprod C₁ C₂)
  | of_iso {C₁ C₂ : ChainComplex (ModuleCat R) ℕ} :
      IsDirectSumOfTrivialComplexes C₁ →
      (e : C₁ ≅ C₂) →
      IsDirectSumOfTrivialComplexes C₂

variable [IsLocalRing R] [IsNoetherianRing R]

/-- Helper for Lemma 10.102.3: the induction measure is the total rank in positive degrees. -/
private def positiveRankSum (C : FiniteFreeComplex R e) : ℕ :=
  ∑ j : Fin e, C.rank j.succ

/-- Helper for Lemma 10.102.3: exactness at a positive degree of a chain complex of modules is the
exactness of the two consecutive differentials as linear maps. -/
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
  -- Rewrite `ExactAt` through the explicit three-term short complex around `k + 1`.
  rw [hmid, hsucc, hpred]
  rw [HomologicalComplex.exactAt_iff' K (k + 2) (k + 1) k (by simp) (by simp)]
  -- For `ModuleCat`, categorical exactness is exactly `Function.Exact`.
  simpa [HomologicalComplex.sc'] using
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (K.sc' (k + 2) (k + 1) k))

/-- Helper for Lemma 10.102.3: if the positive-degree rank sum vanishes, then every individual
positive-degree rank vanishes. -/
private lemma rank_succ_eq_zero_of_positiveRankSum_eq_zero
    (C : FiniteFreeComplex R e)
    (hzero : positiveRankSum (R := R) C = 0)
    (j : Fin e) :
    C.rank j.succ = 0 := by
  -- The `j.succ` rank is one nonnegative summand in the total positive-degree rank sum.
  have hle : C.rank j.succ ≤ positiveRankSum (R := R) C := by
    simpa [positiveRankSum] using
      (Finset.single_le_sum
        (f := fun k : Fin e ↦ C.rank k.succ)
        (fun _ _ ↦ Nat.zero_le _)
        (Finset.mem_univ j))
  rw [hzero] at hle
  exact Nat.eq_zero_of_le_zero hle

/-- Helper for Lemma 10.102.3: a displayed rank-zero term of a finite free complex is a zero
object. -/
private lemma term_isZero_of_rank_eq_zero
    (C : FiniteFreeComplex R e) (j : Fin (e + 1)) (hj : C.rank j = 0) :
    IsZero (C.toChainComplex.X j) := by
  -- Transport the zero-object claim across the chosen coordinate isomorphism in degree `j`.
  exact (C.termIso j).isZero_iff.mpr <|
    by simpa [hj] using ModuleCat.isZero_of_subsingleton (ModuleCat.of R (Fin 0 → R))

/-- Helper for Lemma 10.102.3: depth zero yields a nonzero ring element annihilated by the
maximal ideal. -/
private lemma exists_nonzero_annihilated_by_maximalIdeal_of_moduleDepth_zero
    (hdepth0 : moduleDepth R R = 0) :
    ∃ x : R, x ≠ 0 ∧ ∀ r ∈ maximalIdeal R, r * x = 0 := by
  -- Convert the depth-zero hypothesis into a nonzero linear functional from the residue field.
  have hExt : residueFieldExtNonzero R R 0 := by
    exact (residueFieldExtNonzero_zero_iff_moduleDepth_eq_zero (R := R) (M := R)).2 hdepth0
  obtain ⟨f, hf⟩ :=
    (residueFieldExtNonzero_zero_iff_exists_nonzero_linearMap (R := R) (M := R)).1 hExt
  have hvalue : ∃ y : ResidueField R, f y ≠ 0 := by
    by_contra hvalue
    apply hf
    ext y
    by_contra hy
    exact hvalue ⟨y, hy⟩
  obtain ⟨y, hy⟩ := hvalue
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
  refine ⟨f (IsLocalRing.residue R a), hy, ?_⟩
  intro r hr
  -- Elements of the maximal ideal kill the residue field, and hence kill its image under `f`.
  have hsmul : r • IsLocalRing.residue R a = 0 := by
    exact smul_residueField_eq_zero_of_mem_maximalIdeal (R := R) hr (IsLocalRing.residue R a)
  change r • f (IsLocalRing.residue R a) = 0
  rw [← map_smul, hsmul, map_zero]

/-- Helper for Lemma 10.102.3: if all positive displayed ranks vanish, then the complex is
concentrated in degree `0`. -/
private lemma positive_degree_sum_zero_iso_single_zero
    (C : FiniteFreeComplex R e)
    (hzero : positiveRankSum (R := R) C = 0) :
    Nonempty
      (C.toChainComplex ≅
        ((ChainComplex.single₀ (ModuleCat R)).obj
          (ModuleCat.of R (Fin (C.rank ⟨0, Nat.zero_lt_succ e⟩) → R)))) := by
  let X0 : ModuleCat R := ModuleCat.of R (Fin (C.rank ⟨0, Nat.zero_lt_succ e⟩) → R)
  have hposZero : ∀ j : ℕ, 0 < j → IsZero (C.toChainComplex.X j) := by
    intro j hj
    by_cases hle : j ≤ e
    · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
      let jPred : Fin e := ⟨n, by omega⟩
      have hrank : C.rank jPred.succ = 0 :=
        rank_succ_eq_zero_of_positiveRankSum_eq_zero (C := C) hzero jPred
      -- Every positive displayed rank vanishes, so the corresponding owner term is zero.
      simpa [jPred] using term_isZero_of_rank_eq_zero (C := C) (j := jPred.succ) hrank
    · exact C.isZero_toChainComplex_X j (Nat.lt_of_not_ge hle)
  let toSingle : C.toChainComplex ⟶ (ChainComplex.single₀ (ModuleCat R)).obj X0 :=
    (ChainComplex.toSingle₀Equiv C.toChainComplex X0).symm
      ⟨(C.termIso ⟨0, Nat.zero_lt_succ e⟩).hom, by
        -- The source of `d 1 0` is already zero, so the required compatibility is automatic.
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
      -- In positive degrees, both endomorphisms of the zero object agree automatically.
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
          IsZero (((ChainComplex.single₀ (ModuleCat R)).obj X0).X (n + 1)) := by
        exact HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0 X0 (n + 1) (by simp)
      -- Positive degrees of `single₀` are zero, so the remaining component equality is unique.
      exact hsingle.eq_of_src _ _

/-- Helper for Lemma 10.102.3: owner-level exactness plus a zero next term makes the owner
differential injective. -/
private lemma owner_diff_injective_of_exactAt_and_next_isZero
    (C : FiniteFreeComplex R e) (i : Fin e)
    (hexact : C.toChainComplex.ExactAt (i.1 + 1))
    (hnext : IsZero (C.toChainComplex.X (i.1 + 2))) :
    Function.Injective ((C.toChainComplex.d (i.1 + 1) i.1).hom) := by
  have hfun :
      Function.Exact ((C.toChainComplex.d (i.1 + 2) (i.1 + 1)).hom)
        ((C.toChainComplex.d (i.1 + 1) i.1).hom) :=
    (exactAt_iff_function_exact (K := C.toChainComplex) (j := i.1 + 1) (by omega)).1 hexact
  have hzero_morph : C.toChainComplex.d (i.1 + 2) (i.1 + 1) = 0 := by
    -- The incoming owner differential has zero source, hence it is the zero map.
    exact hnext.eq_of_src _ _
  have hzero : (C.toChainComplex.d (i.1 + 2) (i.1 + 1)).hom = 0 := by
    simpa using congrArg ModuleCat.Hom.hom hzero_morph
  -- Rewriting the preceding differential to `0` reduces exactness to injectivity.
  rw [hzero, LinearMap.exact_zero_iff_injective (P := C.toChainComplex.X (i.1 + 2))] at hfun
  exact hfun

/-- Helper for Lemma 10.102.3: evaluating the target `termIso` inverse on `diffAt i v` rewrites it
back to the owner differential in chain-complex coordinates. -/
private lemma diffAt_termIso_inv_apply
    (C : FiniteFreeComplex R e) (i : Fin e) (v : C.term i.succ) :
    (C.termIso i.castSucc).inv.hom (C.diffAt i v) =
      (C.toChainComplex.d (i.1 + 1) i.1).hom ((C.termIso i.succ).inv.hom v) := by
  have hcomp :
      ModuleCat.ofHom (C.diffAt i) ≫ (C.termIso i.castSucc).inv =
        (C.termIso i.succ).inv ≫ C.toChainComplex.d (i.1 + 1) i.1 := by
    -- Route correction: record the conjugation equality once, rather than normalizing it inline.
    change
      (C.termIso i.succ).inv ≫ C.toChainComplex.d (i.1 + 1) i.1 ≫
          (C.termIso i.castSucc).hom ≫ (C.termIso i.castSucc).inv =
        (C.termIso i.succ).inv ≫ C.toChainComplex.d (i.1 + 1) i.1
    simp [Category.assoc]
  -- Evaluating the recorded morphism equality on `v` yields the pointwise transport formula.
  change ((ModuleCat.ofHom (C.diffAt i) ≫ (C.termIso i.castSucc).inv).hom v) =
    (((C.termIso i.succ).inv ≫ C.toChainComplex.d (i.1 + 1) i.1).hom v)
  rw [hcomp]
  rfl

/-- Helper for Lemma 10.102.3: if the next term is zero, exactness forces the displayed
differential to be injective. -/
private lemma diffAt_injective_of_exactAt_and_next_isZero
    (C : FiniteFreeComplex R e) (i : Fin e)
    (hexact : C.toChainComplex.ExactAt (i.1 + 1))
    (hnext : IsZero (C.toChainComplex.X (i.1 + 2))) :
    Function.Injective (C.diffAt i) := by
  have howner :
      Function.Injective ((C.toChainComplex.d (i.1 + 1) i.1).hom) :=
    owner_diff_injective_of_exactAt_and_next_isZero (C := C) (i := i) hexact hnext
  intro v w hvw
  have htarget :
      (C.termIso i.castSucc).inv.hom (C.diffAt i v) =
        (C.termIso i.castSucc).inv.hom (C.diffAt i w) := by
    -- Apply the target inverse once so the displayed equality lives in owner coordinates.
    exact congrArg ((C.termIso i.castSucc).inv.hom) hvw
  rw [diffAt_termIso_inv_apply (C := C) (i := i) v,
    diffAt_termIso_inv_apply (C := C) (i := i) w] at htarget
  have hsource :
      (C.termIso i.succ).inv.hom v =
        (C.termIso i.succ).inv.hom w :=
    howner htarget
  -- The source coordinate isomorphism is a linear equivalence, so its inverse is injective.
  exact (C.termIso i.succ).toLinearEquiv.symm.injective hsource

/-- Helper for Lemma 10.102.3: a nonzero element annihilated by the maximal ideal forces a unit
matrix entry in an injective top differential. -/
private lemma exists_isUnit_diffEntry_of_top_degree
    (C : FiniteFreeComplex R e) (i : Fin e)
    (x : R) (hx : x ≠ 0)
    (hann : ∀ r ∈ maximalIdeal R, r * x = 0)
    (hpos : 0 < C.rank i.succ)
    (hinj : Function.Injective (C.diffAt i)) :
    ∃ a : Fin (C.rank i.succ), ∃ b : Fin (C.rank i.castSucc), IsUnit (C.diffEntry i a b) := by
  let a : Fin (C.rank i.succ) := ⟨0, hpos⟩
  let v : C.term i.succ := Pi.single a x
  have hv_nonzero : v ≠ 0 := by
    intro hv
    have hvalue : v a = 0 := by
      simpa [hv]
    exact hx (by simpa [v, a] using hvalue)
  have hdiff_nonzero : C.diffAt i v ≠ 0 := by
    intro hzero
    have hv0 : v = 0 := by
      apply hinj
      simpa using hzero
    exact hv_nonzero hv0
  have hcoord :
      ∃ b : Fin (C.rank i.castSucc), C.diffAt i v b ≠ 0 := by
    by_contra hcoord
    apply hdiff_nonzero
    ext b
    by_contra hb
    exact hcoord ⟨b, hb⟩
  obtain ⟨b, hb⟩ := hcoord
  refine ⟨a, b, ?_⟩
  by_contra hunit
  have hmem : C.diffEntry i a b ∈ maximalIdeal R := by
    by_contra hmem
    exact hunit ((IsLocalRing.notMem_maximalIdeal).mp hmem)
  have hv_eq :
      (v : C.term i.succ) = x • (Pi.single a (1 : R) : C.term i.succ) := by
    ext j
    by_cases hj : j = a
    · subst hj
      simp [v]
    · simp [v, Pi.single_eq_of_ne hj]
  have hzero_coord : C.diffAt i v b = 0 := by
    -- Evaluate the injective image of the chosen basis vector in coordinate `b`.
    calc
      C.diffAt i v b = (C.diffAt i (x • (Pi.single a (1 : R) : C.term i.succ))) b := by
        rw [hv_eq]
      _ = (x • C.diffAt i (Pi.single a (1 : R))) b := by
        rw [LinearMap.map_smul]
      _ = x * C.diffEntry i a b := by
        simp [FiniteFreeComplex.diffEntry]
      _ = C.diffEntry i a b * x := by
        rw [mul_comm]
      _ = 0 := hann _ hmem
  exact hb hzero_coord

/-- Helper for Lemma 10.102.3: exactness of a biproduct row implies exactness of the first
summand row. -/
private lemma exactAt_fst_of_biprod_exactAt
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
  -- Insert the cycle into the left biproduct summand and use exactness there.
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
          simp [Category.assoc]
    _ = y₁ ≫ (biprod K L).d (k + 2) (k + 1) ≫
        (biprod.fst : biprod K L ⟶ K).f (k + 1) := by
          simpa [Category.assoc] using congrArg
            (fun m ↦ m ≫ (biprod.fst : biprod K L ⟶ K).f (k + 1)) hy₁
    _ = y₁ ≫ (biprod.fst : biprod K L ⟶ K).f (k + 2) ≫ K.d (k + 2) (k + 1) := by
          have hcomm := (biprod.fst : biprod K L ⟶ K).comm (k + 2) (k + 1)
          simpa [Category.assoc] using congrArg (fun m ↦ y₁ ≫ m) hcomm.symm
    _ = (y₁ ≫ (biprod.fst : biprod K L ⟶ K).f (k + 2)) ≫ K.d (k + 2) (k + 1) := by
          simp [Category.assoc]

/- Domain triage:
* primary domain: finite free chain complexes over a Noetherian local ring, together with the
  chapter's depth-zero criterion for the base ring;
* sampled owner declarations of the same kind:
  `Ideal.depth`,
  `moduleDepth`,
  `associatedPrimes R R`,
  `moduleDepth_eq_firstNonzeroResidueFieldExtIndex`;
* best owner abstraction: the chapter owner `Ideal.depth` and its local bridge `moduleDepth`,
  with associated-prime membership only as a bridge criterion;
* source/core/bridge layers here:
  `source-facing`: `IsDirectSumOfTrivialComplexes` as the decomposition notion from the item;
  `core/canonical`: depth, via `Ideal.depth`;
  `bridge/view`: `moduleDepth R R` and the associated-prime characterization of depth zero.

Primitive data are the finite free complex and its exactness. The depth-zero hypothesis should sit
at the owner layer, while associated-prime membership remains proof data rather than the main
public interface.
-/

-- Proof sketch: choose a nonzero element annihilated by the maximal ideal from the associated
-- prime criterion for the depth-zero hypothesis. Induct on the total positive-degree rank. If a
-- highest nonzero term occurs in degree `i > 0`, exactness forces a unit entry in the displayed
-- differential; apply Lemma `10.102.2` to split off a trivial disk and continue the induction.
-- The remaining degree-zero piece is a trivial single complex.
/-- Lemma 10.102.3: in Situation 10.102.1, if the bounded finite free complex
`0 → R^{n_e} → R^{n_{e-1}} → ⋯ → R^{n_0}` is exact in degrees `e, …, 1` and `R` has depth `0`,
then the complex is isomorphic to a direct sum of trivial complexes. -/
theorem finiteFreeComplex_isDirectSumOfTrivialComplexes_of_exact_of_depthZero
    (C : FiniteFreeComplex R e)
    (hexact : ∀ j : ℕ, 1 ≤ j → j ≤ e → C.toChainComplex.ExactAt j)
    (hdepth0 : moduleDepth R R = 0) :
    IsDirectSumOfTrivialComplexes C.toChainComplex := by
  obtain ⟨x, hx, hann⟩ :=
    exists_nonzero_annihilated_by_maximalIdeal_of_moduleDepth_zero (R := R) hdepth0
  let P : ℕ → Prop := fun n ↦
    ∀ D : FiniteFreeComplex R e,
      positiveRankSum (R := R) D = n →
      (∀ j : ℕ, 1 ≤ j → j ≤ e → D.toChainComplex.ExactAt j) →
      IsDirectSumOfTrivialComplexes D.toChainComplex
  have hP : ∀ n : ℕ, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro D hsum hexactD
        obtain hzero | hpos : n = 0 ∨ 0 < n := Nat.eq_zero_or_pos n
        · -- Base case: once the positive-degree sum vanishes, the complex is concentrated in
          -- degree `0`, hence is a single trivial complex.
          have hsum_zero : positiveRankSum (R := R) D = 0 := by
            simpa [hzero] using hsum
          rcases positive_degree_sum_zero_iso_single_zero (C := D) hsum_zero with ⟨e0⟩
          exact IsDirectSumOfTrivialComplexes.of_iso
            (IsDirectSumOfTrivialComplexes.single₀ (D.rank ⟨0, Nat.zero_lt_succ e⟩)) e0.symm
        · -- Inductive step: choose the highest positive degree, show its differential is
          -- injective, split off an identity disk, and recurse on the reduced complex.
          have hexists : ∃ j : Fin e, 0 < D.rank j.succ := by
            by_contra hnone
            have hsum_zero : positiveRankSum (R := R) D = 0 := by
              unfold positiveRankSum
              refine Finset.sum_eq_zero ?_
              intro j hj
              exact Nat.eq_zero_of_not_pos (fun hjpos ↦ hnone ⟨j, hjpos⟩)
            have : n = 0 := by simpa [hsum] using hsum_zero
            exact (Nat.ne_of_gt hpos) this
          let s : Finset (Fin e) := Finset.univ.filter (fun j ↦ 0 < D.rank j.succ)
          have hs_nonempty : s.Nonempty := by
            rcases hexists with ⟨j, hj⟩
            exact ⟨j, by simp [s, hj]⟩
          let i : Fin e := s.max' hs_nonempty
          have hi_mem : i ∈ s := Finset.max'_mem s hs_nonempty
          have hi_pos : 0 < D.rank i.succ := by
            simpa [s] using (Finset.mem_filter.mp hi_mem).2
          have hmax :
              ∀ j : Fin e, i < j → D.rank j.succ = 0 := by
            intro j hij
            by_contra hj_nonzero
            have hj_pos : 0 < D.rank j.succ := Nat.pos_of_ne_zero hj_nonzero
            have hj_mem : j ∈ s := by
              simp [s, hj_pos]
            exact (not_le_of_gt hij) (Finset.le_max' s j hj_mem)
          have hnext_zero : IsZero (D.toChainComplex.X (i.1 + 2)) := by
            by_cases htop : i.1 + 1 = e
            · exact D.isZero_toChainComplex_X (i.1 + 2) (by omega)
            · have hi_next_lt : i.1 + 1 < e := by
                omega
              let jNext : Fin e := ⟨i.1 + 1, hi_next_lt⟩
              have hrank_next : D.rank jNext.succ = 0 := by
                exact hmax jNext (by
                  change i.1 < i.1 + 1
                  exact Nat.lt_succ_self _)
              simpa [jNext] using term_isZero_of_rank_eq_zero (C := D) (j := jNext.succ)
                hrank_next
          have hinj : Function.Injective (D.diffAt i) := by
            exact diffAt_injective_of_exactAt_and_next_isZero (C := D) (i := i)
              (hexactD (i.1 + 1) (by omega) (by omega)) hnext_zero
          obtain ⟨a, b, hunit⟩ :=
            exists_isUnit_diffEntry_of_top_degree (C := D) (i := i) x hx hann hi_pos hinj
          obtain ⟨D', hsplit, ⟨eiso⟩⟩ :=
            FiniteFreeComplex.exists_iso_biprod_identityDisk_of_isUnit_diffEntry
              (C := D) (i := i) ⟨a, b, hunit⟩
          have hsum_lt : positiveRankSum (R := R) D' < positiveRankSum (R := R) D := by
            -- The split rank agrees with the old rank away from degree `i + 1`, and it drops by
            -- one at degree `i + 1`, so the positive-degree sum strictly decreases.
            refine Finset.sum_lt_sum (fun j _ ↦ ?_) ⟨i, Finset.mem_univ i, ?_⟩
            · rw [hsplit, FiniteFreeComplex.splitRank]
              by_cases hji : j = i
              · subst hji
                simp
              · by_cases hcast : j.succ = i.castSucc
                · simp [hji, hcast]
                · simp [hji, hcast]
            · have hpred : D.rank i.succ - 1 < D.rank i.succ := by
                simpa [Nat.pred_eq_sub_one] using Nat.pred_lt (Nat.ne_of_gt hi_pos)
              simpa [hsplit, FiniteFreeComplex.splitRank] using hpred
          have hexactD' :
              ∀ j : ℕ, 1 ≤ j → j ≤ e → D'.toChainComplex.ExactAt j := by
            intro j hj hje
            have hbiprod :
                (biprod D'.toChainComplex
                  (FiniteFreeComplex.identityDiskComplex (R := R) i)).ExactAt j := by
              exact (hexactD j hj hje).of_iso eiso
            exact exactAt_fst_of_biprod_exactAt (K := D'.toChainComplex)
              (L := FiniteFreeComplex.identityDiskComplex (R := R) i) hj hbiprod
          have hreduced :
              IsDirectSumOfTrivialComplexes D'.toChainComplex := by
            have hsum_lt' : positiveRankSum (R := R) D' < n := by
              simpa [hsum] using hsum_lt
            exact ih (positiveRankSum (R := R) D') hsum_lt' D' rfl hexactD'
          exact IsDirectSumOfTrivialComplexes.of_iso
            (IsDirectSumOfTrivialComplexes.biprod hreduced
              (IsDirectSumOfTrivialComplexes.identityDisk (R := R) i))
            eiso.symm
  exact hP (positiveRankSum (R := R) C) C rfl hexact

end

/-! ### Lemma_10_102_4 (from Chap10) -/
section

universe u

open IsLocalRing Module.associatedPrimes

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsArtinianRing R]
variable {e : ℕ}

/- Domain triage:
* primary domain: bounded finite free complexes over a local ring, together with the chapter depth
  owner `moduleDepth` and the associated-prime bridge detecting depth `0`;
* sampled owner declarations of the same kind:
  `FiniteFreeComplex`,
  `IsDirectSumOfTrivialComplexes`,
  `finiteFreeComplex_isDirectSumOfTrivialComplexes_of_exact_of_depthZero`,
  `moduleDepth_le_ringKrullDim_quotient_of_mem_associatedPrimes`;
* best owner abstraction: the chapter owner theorem
  `finiteFreeComplex_isDirectSumOfTrivialComplexes_of_exact_of_depthZero`, with the Artinian-local
  hypothesis used only to derive the canonical bridge statement `moduleDepth R R = 0`;
* layer: `source-facing` specialization of that owner theorem, not a second decomposition owner.
-/

-- Proof sketch: apply
-- `finiteFreeComplex_isDirectSumOfTrivialComplexes_of_exact_of_depthZero`. An Artinian local ring
-- has depth `0`; equivalently, its maximal ideal is an associated prime of `R`, which is the
-- bridge criterion used in the proof of Lemma `10.102.3`.
/-- Lemma 10.102.4: in Situation 10.102.1, if `R` is an Artinian local ring and the bounded finite
free complex `0 → R^{n_e} → R^{n_{e-1}} → ⋯ → R^{n_0}` is exact in degrees `e, …, 1`, then the
complex is isomorphic to a direct sum of trivial complexes. -/
theorem finiteFreeComplex_isDirectSumOfTrivialComplexes_of_exact_of_artinianLocal
    (C : FiniteFreeComplex R e)
    (hexact : ∀ j : ℕ, 1 ≤ j → j ≤ e → C.toChainComplex.ExactAt j) :
    IsDirectSumOfTrivialComplexes C.toChainComplex := by
  refine finiteFreeComplex_isDirectSumOfTrivialComplexes_of_exact_of_depthZero C hexact ?_
  haveI : Ring.KrullDimLE 0 R := (isArtinianRing_iff_krullDimLE_zero).mp inferInstance
  have hann : Module.annihilator R R = ⊥ := Module.annihilator_eq_bot.mpr inferInstance
  have hassoc : maximalIdeal R ∈ associatedPrimes R R := by
    have hmin' : maximalIdeal R ∈ (⊥ : Ideal R).minimalPrimes := by
      rw [Ring.KrullDimLE.mem_minimalPrimes_iff_le_of_isPrime]
      exact bot_le
    have hmin : maximalIdeal R ∈ (Module.annihilator R R).minimalPrimes := by
      simpa [hann] using hmin'
    exact minimalPrimes_annihilator_subset_associatedPrimes R R hmin
  have hle : WithBot.some (moduleDepth R R : ℕ∞) ≤ ringKrullDim (R ⧸ maximalIdeal R) :=
    moduleDepth_le_ringKrullDim_quotient_of_mem_associatedPrimes (maximalIdeal R) hassoc
  have hdim : ringKrullDim (R ⧸ maximalIdeal R) = 0 := by
    letI : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field (maximalIdeal R)
    exact ringKrullDim_eq_zero_of_field (R ⧸ maximalIdeal R)
  rw [hdim] at hle
  have hdepth_le : moduleDepth R R ≤ 0 := by
    simpa [WithBot.some_eq_coe] using hle
  exact le_antisymm hdepth_le bot_le

end

/-! ### Definition_10_102_5 (from Chap10) -/
universe u

open Matrix
open exteriorPower

namespace LinearMap

section

variable {R : Type u} [CommRing R] {m n : ℕ}

/-- The exterior rank of a linear map between finite free `R`-modules is the largest `r` such that
the induced map on `r`th exterior powers is nonzero. -/
noncomputable def exteriorRank (φ : (Fin m → R) →ₗ[R] (Fin n → R)) : ℕ :=
  letI : DecidablePred fun r ↦ exteriorPower.map r φ ≠ 0 := Classical.decPred _
  Nat.findGreatest (fun r ↦ exteriorPower.map r φ ≠ 0) (min m n)

/-- The exterior rank of a map `φ : R^m → R^n` is bounded by `min m n`. -/
-- Proof sketch: this is immediate from the definition by `Nat.findGreatest`, whose output is
-- always bounded by the search bound `min m n`.
theorem exteriorRank_le_min (φ : (Fin m → R) →ₗ[R] (Fin n → R)) :
    exteriorRank φ ≤ min m n := sorry

/-- Definition 10.102.5: the ideal `I(φ)` of a map `φ : R^m → R^n` is generated by the minors of
size equal to the exterior rank of `φ`. -/
noncomputable def rankMinorIdeal (φ : (Fin m → R) →ₗ[R] (Fin n → R)) : Ideal R :=
  minorIdeal (exteriorRank φ) <|
    LinearMap.toMatrix (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n)) φ

notation:max "I(" φ ")" => LinearMap.rankMinorIdeal φ

/-- Every minor of the matrix of `φ` of size `LinearMap.exteriorRank φ` belongs to `I(φ)`. -/
-- Proof sketch: unfold `I(φ)` and use the defining generator-set inclusion
-- into `Ideal.span`.
theorem det_submatrix_mem_rankMinorIdeal (φ : (Fin m → R) →ₗ[R] (Fin n → R))
    (e₁ : Fin (exteriorRank φ) ↪ Fin n) (e₂ : Fin (exteriorRank φ) ↪ Fin m) :
    Matrix.det
        ((LinearMap.toMatrix (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n)) φ).submatrix e₁ e₂) ∈
      I(φ) := by
  simpa [rankMinorIdeal] using
    det_submatrix_mem_minorIdeal (exteriorRank φ)
      (LinearMap.toMatrix (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n)) φ) e₁ e₂

end

end LinearMap

/-! ### Lemma_10_102_6 (from Chap10) -/
universe u

section

open CategoryTheory CategoryTheory.Limits LinearMap

variable {R : Type u} [CommRing R]
variable {e : ℕ}

namespace FiniteFreeComplex

variable (C : _root_.FiniteFreeComplex R e)

private abbrev adjacentLeftIndex (i : Fin (e - 1)) : Fin e :=
  ⟨i.1, by omega⟩

private abbrev adjacentRightIndex (i : Fin (e - 1)) : Fin e :=
  ⟨i.1 + 1, by omega⟩

private abbrev adjacentMiddleIndex (i : Fin (e - 1)) : Fin (e + 1) :=
  ⟨i.1 + 1, by omega⟩

/-- Helper for Lemma 10.102.6: the induction measure is the total positive-degree rank. -/
private def positiveRankSum (C : FiniteFreeComplex R e) : ℕ :=
  ∑ j : Fin e, C.rank j.succ

/-- Helper for Lemma 10.102.6: if the total positive-degree rank vanishes, then each positive
displayed rank vanishes. -/
private theorem rank_succ_eq_zero_of_positiveRankSum_eq_zero
    (C : FiniteFreeComplex R e)
    (hzero : positiveRankSum (R := R) C = 0)
    (j : Fin e) :
    C.rank j.succ = 0 := by
  -- The rank in degree `j + 1` is one nonnegative summand in the total positive-degree rank sum.
  have hle : C.rank j.succ ≤ positiveRankSum (R := R) C := by
    simpa [positiveRankSum] using
      (Finset.single_le_sum
        (f := fun k : Fin e ↦ C.rank k.succ)
        (fun _ _ ↦ Nat.zero_le _)
        (Finset.mem_univ j))
  rw [hzero] at hle
  exact Nat.eq_zero_of_le_zero hle

/-- Helper for Lemma 10.102.6: an alternating sum and its tail recover the head term. -/
private theorem alternatingSum_cons_add_tail_eq_head (a : ℤ) :
    ∀ l : List ℤ, List.alternatingSum (a :: l) + List.alternatingSum l = a
  | [] => by
      -- With empty tail the alternating sum is just the head term.
      simp [List.alternatingSum]
  | [b] => by
      -- With a singleton tail the two displayed terms cancel directly.
      simp [List.alternatingSum]
  | b :: c :: t => by
      -- Peel off the first cancelling pair and recurse on the shorter tail.
      have ih : List.alternatingSum (c :: t) + List.alternatingSum t = c :=
        alternatingSum_cons_add_tail_eq_head c t
      simp [List.alternatingSum] at ih ⊢
      linarith

/-- Helper for Lemma 10.102.6: consecutive alternating tails add back up to the middle rank. -/
private theorem adjacent_alternatingRank_add_eq_rank (C : _root_.FiniteFreeComplex R e)
    (i : Fin (e - 1)) :
    C.alternatingRank (adjacentLeftIndex i) + C.alternatingRank (adjacentRightIndex i) =
      C.rank (adjacentMiddleIndex i) := by
  let tail : List ℤ :=
    List.ofFn fun k : Fin (e - (i.1 + 1)) ↦
      (C.rank ⟨i.1 + 2 + k.1, by omega⟩ : ℤ)
  have hleft_length : e - i.1 = (e - (i.1 + 1)) + 1 := by
    omega
  have hleft_list :
      List.ofFn (fun k : Fin (e - i.1) ↦ (C.rank ⟨i.1 + 1 + k.1, by omega⟩ : ℤ)) =
        (C.rank (adjacentMiddleIndex i) : ℤ) :: tail := by
    -- Split the left list into its first entry and the remaining tail.
    have hsucc_eq :
        List.ofFn
            (fun k : Fin ((e - (i.1 + 1)) + 1) ↦
              (C.rank ⟨i.1 + 1 + k.1, by omega⟩ : ℤ)) =
          (C.rank (adjacentMiddleIndex i) : ℤ) ::
            List.ofFn
              (fun k : Fin (e - (i.1 + 1)) ↦
                (C.rank ⟨i.1 + 1 + k.succ.1, by omega⟩ : ℤ)) := by
      rw [List.ofFn_succ]
      simp [adjacentMiddleIndex]
    have htail_eq :
        List.ofFn
            (fun k : Fin (e - (i.1 + 1)) ↦
              (C.rank ⟨i.1 + 1 + k.succ.1, by omega⟩ : ℤ)) = tail := by
      apply congrArg List.ofFn
      funext k
      simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    calc
      List.ofFn (fun k : Fin (e - i.1) ↦ (C.rank ⟨i.1 + 1 + k.1, by omega⟩ : ℤ)) =
          List.ofFn
            (fun k : Fin ((e - (i.1 + 1)) + 1) ↦
              (C.rank ⟨i.1 + 1 + k.1, by omega⟩ : ℤ)) := by
            simpa [hleft_length]
      _ = (C.rank (adjacentMiddleIndex i) : ℤ) ::
            List.ofFn
              (fun k : Fin (e - (i.1 + 1)) ↦
                (C.rank ⟨i.1 + 1 + k.succ.1, by omega⟩ : ℤ)) := hsucc_eq
      _ = (C.rank (adjacentMiddleIndex i) : ℤ) :: tail := by
            rw [htail_eq]
  have hleft :
      C.alternatingRank (adjacentLeftIndex i) =
        List.alternatingSum ((C.rank (adjacentMiddleIndex i) : ℤ) :: tail) := by
    -- Rewrite the left alternating tail through the explicit head-tail list identity.
    change
      List.alternatingSum
          (List.ofFn (fun k : Fin (e - i.1) ↦ (C.rank ⟨i.1 + 1 + k.1, by omega⟩ : ℤ))) =
        List.alternatingSum ((C.rank (adjacentMiddleIndex i) : ℤ) :: tail)
    simpa using congrArg List.alternatingSum hleft_list
  have hright :
      C.alternatingRank (adjacentRightIndex i) =
        List.alternatingSum tail := by
    -- The right alternating tail is definitionally the tail list introduced above.
    change
      List.alternatingSum
          (List.ofFn (fun k : Fin (e - (i.1 + 1)) ↦
            (C.rank ⟨i.1 + 2 + k.1, by omega⟩ : ℤ))) =
        List.alternatingSum tail
    rfl
  -- Apply the elementary alternating-sum identity to the head-tail decomposition.
  rw [hleft, hright]
  simpa [tail] using
    alternatingSum_cons_add_tail_eq_head (a := (C.rank (adjacentMiddleIndex i) : ℤ)) tail

/-- Helper for Lemma 10.102.6: a zero standard finite free module must have rank `0` over a
nontrivial ring. -/
private theorem rank_eq_zero_of_isZero_standard_module [Nontrivial R] (n : ℕ)
    (hzero : CategoryTheory.Limits.IsZero (ModuleCat.of R (Fin n → R))) :
    n = 0 := by
  by_contra hn
  have hpos : 0 < n := Nat.pos_of_ne_zero hn
  let i : Fin n := ⟨0, hpos⟩
  letI : Subsingleton (Fin n → R) := ModuleCat.subsingleton_of_isZero hzero
  -- Evaluate the unique equality between `Pi.single i 1` and `0` in coordinate `i`.
  have hsingle : (Pi.single i (1 : R) : Fin n → R) = 0 := Subsingleton.elim _ _
  have hone_zero : (1 : R) = 0 := by
    simpa [Pi.single_apply, i] using congrArg (fun f : Fin n → R ↦ f i) hsingle
  exact one_ne_zero hone_zero

/-- Helper for Lemma 10.102.6: if `R^n` is identified with a biproduct `R^a ⊞ R^b`, then the
displayed rank is `n = a + b`. -/
private theorem rank_eq_add_of_iso_biprod_standard_module [Nontrivial R]
    (n a b : ℕ)
    (e : ModuleCat.of R (Fin n → R) ≅
      (ModuleCat.of R (Fin a → R) ⊞ ModuleCat.of R (Fin b → R))) :
    n = a + b := by
  -- Convert the categorical biproduct isomorphism to a linear equivalence with the standard
  -- product model, then apply invariant basis number to compare the finite free ranks.
  let eprod : (Fin n → R) ≃ₗ[R] (Fin a → R) × (Fin b → R) :=
    e.toLinearEquiv.trans (ModuleCat.biprodIsoProd _ _).toLinearEquiv
  let esum : (Fin n → R) ≃ₗ[R] (Fin (a + b) → R) :=
    eprod.trans <|
      (LinearEquiv.sumArrowLequivProdArrow (Fin a) (Fin b) R R).symm.trans <|
        (LinearEquiv.piCongrLeft R (fun _ : Fin a ⊕ Fin b ↦ R) finSumFinEquiv.symm).symm
  exact InvariantBasisNumber.eq_of_fin_equiv esum

/-- Helper for Lemma 10.102.6: every positive exterior power of the zero map vanishes. -/
private theorem exteriorPower_map_zero_eq_zero {m n r : ℕ} (hr : 0 < r) :
    exteriorPower.map r (0 : (Fin m → R) →ₗ[R] (Fin n → R)) = 0 := by
  -- Route correction: prove vanishing on the spanning `ιMulti` generators instead of unfolding
  -- the exterior-power presentation by hand.
  ext v
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr) with ⟨s, rfl⟩
  -- After one exterior factor, the induced alternating family already starts with `0`.
  simp

/-- Helper for Lemma 10.102.6: the zero map has exterior rank `0`. -/
private theorem exteriorRank_zero_eq_zero {m n : ℕ} :
    exteriorRank (0 : (Fin m → R) →ₗ[R] (Fin n → R)) = 0 := by
  classical
  letI :
      DecidablePred
        (fun r ↦ exteriorPower.map r (0 : (Fin m → R) →ₗ[R] (Fin n → R)) ≠ 0) :=
    Classical.decPred _
  -- Positive exterior powers of `0` vanish, so `Nat.findGreatest` can only return `0`.
  unfold LinearMap.exteriorRank
  rw [Nat.findGreatest_eq_zero_iff]
  intro r hr hk
  simp [exteriorPower_map_zero_eq_zero (R := R) (m := m) (n := n) hr]

/-- Helper for Lemma 10.102.6: the rank-minor ideal of the zero map is the unit ideal because the
only `0 × 0` minor is `1`. -/
private theorem rankMinorIdeal_zero_eq_top {m n : ℕ} :
    I((0 : (Fin m → R) →ₗ[R] (Fin n → R))) = ⊤ := by
  -- Unfold to size-`0` minors and use the convention `I₀ = R`.
  rw [LinearMap.rankMinorIdeal, exteriorRank_zero_eq_zero (R := R) (m := m) (n := n)]
  simp [Matrix.minorIdeal]

/-- Helper for Lemma 10.102.6: changing coordinates on the source and target by linear
automorphisms does not change the exterior rank. -/
private theorem exteriorRank_eq_of_conj {m n : ℕ}
    (φ : (Fin m → R) →ₗ[R] (Fin n → R))
    (eSource : (Fin m → R) ≃ₗ[R] (Fin m → R))
    (eTarget : (Fin n → R) ≃ₗ[R] (Fin n → R)) :
    exteriorRank (eTarget.toLinearMap.comp (φ.comp eSource.symm.toLinearMap)) =
      exteriorRank φ := by
  have hpred :
      (fun r ↦
        exteriorPower.map r
            (eTarget.toLinearMap.comp (φ.comp eSource.symm.toLinearMap)) ≠
          0) =
        fun r ↦ exteriorPower.map r φ ≠ 0 := by
    funext r
    apply propext
    constructor
    · intro hconj
      intro hφ
      apply hconj
      -- Expand the conjugated exterior-power map and rewrite the middle factor to `0`.
      calc
        exteriorPower.map r (eTarget.toLinearMap.comp (φ.comp eSource.symm.toLinearMap)) =
            exteriorPower.map r eTarget.toLinearMap ∘ₗ
              exteriorPower.map r φ ∘ₗ exteriorPower.map r eSource.symm.toLinearMap := by
              simp [exteriorPower.map_comp]
        _ = 0 := by
              simp [hφ]
    · intro hφ
      intro hconj
      apply hφ
      have hrecover :
          φ =
            eTarget.symm.toLinearMap.comp
              ((eTarget.toLinearMap.comp (φ.comp eSource.symm.toLinearMap)).comp
                eSource.toLinearMap) := by
        -- Cancelling the inverse coordinate changes recovers the original map.
        ext x
        simp
      have hmaprecover :
          exteriorPower.map r φ =
            exteriorPower.map r eTarget.symm.toLinearMap ∘ₗ
              exteriorPower.map r
                (eTarget.toLinearMap.comp (φ.comp eSource.symm.toLinearMap)) ∘ₗ
              exteriorPower.map r eSource.toLinearMap := by
        -- Apply the exterior-power functor to the recovered map and expand the compositions.
        have hmap := congrArg (exteriorPower.map r) hrecover
        simpa [exteriorPower.map_comp] using hmap
      -- Compose on the left and right by the inverse coordinate changes to recover `φ`.
      calc
        exteriorPower.map r φ =
            exteriorPower.map r eTarget.symm.toLinearMap ∘ₗ
              exteriorPower.map r
                (eTarget.toLinearMap.comp (φ.comp eSource.symm.toLinearMap)) ∘ₗ
              exteriorPower.map r eSource.toLinearMap := hmaprecover
        _ = 0 := by
              simp [hconj]
  -- The search bound `min m n` is unchanged, so `Nat.findGreatest` sees the same predicate.
  unfold LinearMap.exteriorRank
  rw [hpred]

/-- Helper for Lemma 10.102.6: transposing a matrix does not change the fixed-size minor ideal,
because transposed minors have the same determinants. -/
private theorem minorIdeal_transpose_eq {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (r : ℕ) (A : Matrix ι κ R) :
    Matrix.minorIdeal r A.transpose = Matrix.minorIdeal r A := by
  refine le_antisymm ?_ ?_
  · -- Every generator on the transpose side is the transpose of a generator on the original side.
    refine Ideal.span_le.2 ?_
    rintro _ ⟨⟨e₁, e₂⟩, rfl⟩
    have hsub :
        A.transpose.submatrix e₁ e₂ = (A.submatrix e₂ e₁).transpose := by
      ext i j
      rfl
    change Matrix.det (A.transpose.submatrix e₁ e₂) ∈ Matrix.minorIdeal r A
    rw [hsub, Matrix.det_transpose]
    exact Matrix.det_submatrix_mem_minorIdeal r A e₂ e₁
  · -- The same generator-wise transpose argument works in the opposite direction.
    refine Ideal.span_le.2 ?_
    rintro _ ⟨⟨e₁, e₂⟩, rfl⟩
    have hsub :
        A.submatrix e₁ e₂ = (A.transpose.submatrix e₂ e₁).transpose := by
      ext i j
      rfl
    change Matrix.det (A.submatrix e₁ e₂) ∈ Matrix.minorIdeal r A.transpose
    rw [hsub, Matrix.det_transpose]
    exact Matrix.det_submatrix_mem_minorIdeal r A.transpose e₂ e₁

/-- Helper for Lemma 10.102.6: right multiplication by a square matrix does not enlarge a fixed
minor ideal. -/
private theorem minorIdeal_mul_right_le {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (r : ℕ) (A : Matrix ι κ R) (C : Matrix κ κ R) :
    Matrix.minorIdeal r (A * C) ≤ Matrix.minorIdeal r A := by
  -- Route correction: reduce right multiplication to the proved left-multiplication statement by
  -- transposing, apply the left-hand lemma there, and transpose back.
  have hleft :
      Matrix.minorIdeal r ((A * C).transpose) ≤ Matrix.minorIdeal r A.transpose := by
    simpa [Matrix.transpose_mul] using
      (Matrix.minorIdeal_mul_left_le (R := R) (r := r) C.transpose A.transpose)
  calc
    Matrix.minorIdeal r (A * C) = Matrix.minorIdeal r ((A * C).transpose) := by
      symm
      exact minorIdeal_transpose_eq (r := r) (A := A * C)
    _ ≤ Matrix.minorIdeal r A.transpose := hleft
    _ = Matrix.minorIdeal r A := minorIdeal_transpose_eq (r := r) (A := A)

/-- Helper for Lemma 10.102.6: if all positive displayed ranks vanish, then the displayed
alternating rank is `0`. -/
private theorem alternatingRank_eq_zero_of_positiveRankSum_eq_zero
    (C : FiniteFreeComplex R e)
    (hzero : positiveRankSum (R := R) C = 0)
    (i : Fin e) :
    C.alternatingRank i = 0 := by
  -- Every entry in the alternating tail lies in a positive degree, hence has rank `0`.
  unfold _root_.FiniteFreeComplex.alternatingRank
  change
    List.alternatingSum
        (List.ofFn (fun k : Fin (e - i) ↦ (C.rank ⟨i.1 + 1 + k.1, by omega⟩ : ℤ))) = 0
  have hentry :
      ∀ k : Fin (e - i),
        (C.rank ⟨i.1 + 1 + k.1, by omega⟩ : ℤ) = 0 := by
    intro k
    let j : Fin e := ⟨i.1 + k.1, by omega⟩
    have hj : C.rank j.succ = 0 :=
      rank_succ_eq_zero_of_positiveRankSum_eq_zero (R := R) (C := C) hzero j
    simpa [j, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      congrArg (fun n : ℕ ↦ (n : ℤ)) hj
  have hzero_list : (List.replicate (e - i) (0 : ℤ)).alternatingSum = 0 := by
    -- The alternating sum of a list of zeros is zero.
    let hzero_replicate : ∀ n : ℕ, (List.replicate n (0 : ℤ)).alternatingSum = 0 :=
      Nat.twoStepInduction
        (by simp [List.alternatingSum])
        (by simp [List.alternatingSum])
        (fun n ih _ ↦ by
          simp [List.replicate, List.alternatingSum, ih])
    simpa using hzero_replicate (e - i)
  simpa [hentry] using hzero_list

/-- Helper for Lemma 10.102.6: if all positive displayed ranks vanish, then every displayed
differential is the zero map because its source module is zero. -/
private theorem diffAt_eq_zero_of_positiveRankSum_eq_zero
    (C : FiniteFreeComplex R e)
    (hzero : positiveRankSum (R := R) C = 0)
    (i : Fin e) :
    C.diffAt i = 0 := by
  have hrank : C.rank i.succ = 0 :=
    rank_succ_eq_zero_of_positiveRankSum_eq_zero (R := R) (C := C) hzero i
  letI : Subsingleton (C.term i.succ) := by
    simpa [FiniteFreeComplex.term, hrank] using (inferInstance : Subsingleton (Fin 0 → R))
  -- With a subsingleton source, every vector is `0`, so the linear map is pointwise zero.
  apply LinearMap.ext
  intro x
  have hx : x = 0 := Subsingleton.elim _ _
  rw [hx]
  simp

/-- Helper for Lemma 10.102.6: at the top displayed differential, the alternating tail has only
one term, so it is exactly the top displayed rank. -/
private theorem alternatingRank_last_eq_rank_top
    (C : FiniteFreeComplex R (e + 1)) :
    C.alternatingRank (Fin.last e) = C.rank ⟨e + 1, by omega⟩ := by
  -- The last alternating tail consists of the single top-degree rank.
  unfold _root_.FiniteFreeComplex.alternatingRank
  simp
  congr

/-- Helper for Lemma 10.102.6: the source descending count is determined by the adjacent-rank
recurrence together with the top boundary value. -/
private theorem alternatingRank_eq_of_profile_recurrence
    (C : FiniteFreeComplex R e)
    (r : Fin e → ℕ)
    (hrec : ∀ j : Fin (e - 1),
      (r (adjacentLeftIndex j) : ℤ) + r (adjacentRightIndex j) =
        C.rank (adjacentMiddleIndex j))
    (htop : ∀ h : 0 < e, (r ⟨e - 1, by omega⟩ : ℤ) = C.rank ⟨e, by omega⟩)
    (i : Fin e) :
    (r i : ℤ) = C.alternatingRank i := by
  cases e with
  | zero =>
      exact Fin.elim0 i
  | succ e =>
      -- Descend from the top index: both the profile counts and alternating ranks satisfy the
      -- same adjacent recurrence, so equality propagates one degree at a time.
      induction i using Fin.reverseInduction with
      | last =>
          calc
            (r (Fin.last e) : ℤ) = C.rank ⟨e + 1, by omega⟩ := htop (Nat.succ_pos _)
            _ = C.alternatingRank (Fin.last e) := by
                  symm
                  exact alternatingRank_last_eq_rank_top (C := C)
      | cast j ih =>
          -- Route correction: use the source recurrence `r_i + r_{i + 1} = n_i` directly, rather
          -- than the abandoned identity-disk peel.
          have hr :
              (r (Fin.castSucc j) : ℤ) + r j.succ = C.rank (adjacentMiddleIndex j) :=
            hrec j
          have halt :
              C.alternatingRank (Fin.castSucc j) + C.alternatingRank j.succ =
                C.rank (adjacentMiddleIndex j) :=
            adjacent_alternatingRank_add_eq_rank (C := C) j
          linarith

/-- Helper for Lemma 10.102.6: exactness in a positive degree of a chain complex of modules is
exactness of the two consecutive differentials as linear maps. -/
private theorem exactAt_iff_function_exact
    (K : ChainComplex (ModuleCat R) ℕ) {j : ℕ} (hj : 1 ≤ j) :
    K.ExactAt j ↔ Function.Exact (K.d (j + 1) j).hom (K.d j (j - 1)).hom := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  have hmid : 1 + k = k + 1 := by
    omega
  have hsucc : k + 1 + 1 = k + 2 := by
    omega
  have hpred : k + 1 - 1 = k := by
    omega
  -- Rewrite `ExactAt` through the explicit three-term short complex around `k + 1`.
  rw [hmid, hsucc, hpred]
  rw [HomologicalComplex.exactAt_iff' K (k + 2) (k + 1) k (by simp) (by simp)]
  -- For `ModuleCat`, categorical exactness is exactly `Function.Exact`.
  simpa [HomologicalComplex.sc'] using
    (CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
      (K.sc' (k + 2) (k + 1) k))

/-- Helper for Lemma 10.102.6: if the middle term is zero, the corresponding positive-degree row
is exact. -/
private theorem exactAt_of_isZero_middle
    (K : ChainComplex (ModuleCat R) ℕ) {j : ℕ} (hj : 1 ≤ j)
    (hzero : CategoryTheory.Limits.IsZero (K.X j)) :
    K.ExactAt j := by
  -- Rewrite to linear-map exactness, then note that every map into the zero middle term is
  -- automatically surjective.
  rw [exactAt_iff_function_exact (R := R) (K := K) hj]
  have hnext : (K.d j (j - 1)).hom = 0 := by
    simpa using congrArg ModuleCat.Hom.hom (hzero.eq_of_src (K.d j (j - 1)) 0)
  rw [hnext]
  letI : Subsingleton (K.X j) := ModuleCat.subsingleton_of_isZero hzero
  exact (LinearMap.exact_zero_iff_surjective
    (R := R) (P := K.X (j - 1)) ((K.d (j + 1) j).hom)).2 <|
    Function.surjective_to_subsingleton _

/-- Helper for Lemma 10.102.6: the degree-zero single complex is exact in every positive degree. -/
private theorem exactAt_single₀
    (n j : ℕ) (hj : 1 ≤ j) :
    (((ChainComplex.single₀ (ModuleCat R)).obj (ModuleCat.of R (Fin n → R))).ExactAt j) := by
  -- Every positive degree of `single₀` is zero, so the middle term of the row vanishes.
  exact exactAt_of_isZero_middle (R := R)
    (((ChainComplex.single₀ (ModuleCat R)).obj (ModuleCat.of R (Fin n → R)))) hj
    (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0
      (ModuleCat.of R (Fin n → R)) j (by omega))

/-- Helper for Lemma 10.102.6: the standard free module on `Fin (a + b)` identifies with the
binary biproduct of the standard free modules on `Fin a` and `Fin b`. -/
private noncomputable def standard_module_sum_iso_biprod (a b : ℕ) :
    ModuleCat.of R (Fin (a + b) → R) ≅
      (ModuleCat.of R (Fin a → R) ⊞ ModuleCat.of R (Fin b → R)) :=
  ((LinearEquiv.piCongrLeft R (fun _ : Fin a ⊕ Fin b ↦ R) finSumFinEquiv.symm).toModuleIso) ≪≫
    (LinearEquiv.sumArrowLequivProdArrow (Fin a) (Fin b) R R).toModuleIso ≪≫
    (ModuleCat.biprodIsoProd (ModuleCat.of R (Fin a → R)) (ModuleCat.of R (Fin b → R))).symm

/-- Helper for Lemma 10.102.6: the standard free module on the empty finite set is a zero
object. -/
private theorem standard_zero_module_isZero :
    CategoryTheory.Limits.IsZero (ModuleCat.of R (Fin 0 → R)) := by
  exact ModuleCat.isZero_of_subsingleton (ModuleCat.of R (Fin 0 → R))

/-- Helper for Lemma 10.102.6: the displayed zero-by-zero biproduct is a zero object. -/
private theorem standard_zero_biprod_isZero :
    CategoryTheory.Limits.IsZero
      ((ModuleCat.of R (Fin 0 → R) ⊞ ModuleCat.of R (Fin 0 → R)) : ModuleCat R) := by
  exact CategoryTheory.Limits.IsZero.of_iso
    (standard_zero_module_isZero (R := R))
    (standard_module_sum_iso_biprod (R := R) 0 0).symm

/-- Helper for Lemma 10.102.6: any zero term can be identified with the standard zero-by-zero
biproduct. -/
private noncomputable def zero_term_iso_standard_biprod {X : ModuleCat R}
    (hzero : CategoryTheory.Limits.IsZero X) :
    X ≅ ((ModuleCat.of R (Fin 0 → R) ⊞ ModuleCat.of R (Fin 0 → R)) : ModuleCat R) :=
  hzero.iso (standard_zero_biprod_isZero (R := R))

/-- Helper for Lemma 10.102.6: a sequence supported in one degree records the basis-count profile
from the source proof. -/
private def supported_rank_sequence (n s : ℕ) : ℕ → ℕ :=
  fun j ↦ if j = s then n else 0

/-- Helper for Lemma 10.102.6: the standard projection shape in the split-basis profile is the
map from the right source summand to the left target summand. -/
private abbrev standard_biprod_projection (r : ℕ → ℕ) (j : ℕ) :
    (ModuleCat.of R (Fin (r (j + 2)) → R) ⊞
        ModuleCat.of R (Fin (r (j + 1)) → R)) ⟶
      (ModuleCat.of R (Fin (r (j + 1)) → R) ⊞
        ModuleCat.of R (Fin (r j) → R)) :=
  (biprod.snd : _ ⟶ ModuleCat.of R (Fin (r (j + 1)) → R)) ≫
    (biprod.inl :
      ModuleCat.of R (Fin (r (j + 1)) → R) ⟶
        (ModuleCat.of R (Fin (r (j + 1)) → R) ⊞
          ModuleCat.of R (Fin (r j) → R)))

/-- Helper for Lemma 10.102.6: the chain-level split-basis profile used to model a direct sum of
trivial complexes in categorical biproduct coordinates. -/
private structure BiprodProjectionProfile (K : ChainComplex (ModuleCat R) ℕ) where
  r : ℕ → ℕ
  coord :
    ∀ j : ℕ,
      K.X j ≅
        (ModuleCat.of R (Fin (r (j + 1)) → R) ⊞
          ModuleCat.of R (Fin (r j) → R))
  differential :
    ∀ j : ℕ,
      (coord (j + 1)).inv ≫ K.d (j + 1) j ≫ (coord j).hom =
        standard_biprod_projection (R := R) r j

/-- Helper for Lemma 10.102.6: in degree `0`, the `single₀` generator identifies with the
supported biproduct coordinate model `0 ⊞ R^n`. -/
private theorem biprodProjectionProfile_single₀_coord_exists
    (n j : ℕ) :
    Nonempty
      ((((ChainComplex.single₀ (ModuleCat R)).obj (ModuleCat.of R (Fin n → R))).X j) ≅
        ((ModuleCat.of R (Fin ((supported_rank_sequence n 0) (j + 1)) → R)) ⊞
          ModuleCat.of R (Fin ((supported_rank_sequence n 0) j) → R))) := by
  by_cases hj : j = 0
  · -- In degree `0`, the supported sequence records `n` basis vectors in the second summand.
    subst hj
    let e₀ : ModuleCat.of R (Fin n → R) ≅ ModuleCat.of R (Fin (0 + n) → R) :=
      (LinearEquiv.piCongrLeft R (fun _ : Fin (0 + n) ↦ R)
        (finCongr (Nat.zero_add n)).symm).toModuleIso
    change Nonempty
      ((ModuleCat.of R (Fin n → R)) ≅
        ((ModuleCat.of R (Fin ((supported_rank_sequence n 0) (0 + 1)) → R)) ⊞
          ModuleCat.of R (Fin ((supported_rank_sequence n 0) 0) → R)))
    refine ⟨?_⟩
    simpa [supported_rank_sequence] using
      (e₀ ≪≫ standard_module_sum_iso_biprod (R := R) 0 n)
  · -- Every positive degree is zero, so its coordinate model is the zero-by-zero biproduct.
    have hjpos : 0 < j := Nat.pos_of_ne_zero hj
    have hzeroj : (supported_rank_sequence n 0) j = 0 := by
      simp [supported_rank_sequence, hj]
    refine ⟨?_⟩
    -- Positive degrees of `single₀` are zero, so the chosen coordinate model is the standard
    -- zero biproduct.
    simpa [ChainComplex.single₀, supported_rank_sequence, hzeroj] using
      zero_term_iso_standard_biprod (R := R)
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0
          (ModuleCat.of R (Fin n → R)) j (by omega))

/-- Helper for Lemma 10.102.6: choose the supported coordinate isomorphism for the `single₀`
generator. -/
private noncomputable def biprodProjectionProfile_single₀_coord
    (n j : ℕ) :
    (((ChainComplex.single₀ (ModuleCat R)).obj (ModuleCat.of R (Fin n → R))).X j) ≅
      ((ModuleCat.of R (Fin ((supported_rank_sequence n 0) (j + 1)) → R)) ⊞
        ModuleCat.of R (Fin ((supported_rank_sequence n 0) j) → R)) :=
  Classical.choice (biprodProjectionProfile_single₀_coord_exists (R := R) n j)

/-- Helper for Lemma 10.102.6: every positive-degree source coordinate in the `single₀` profile is
the standard zero biproduct. -/
private theorem biprodProjectionProfile_single₀_source_isZero (n j : ℕ) :
    CategoryTheory.Limits.IsZero
      (((ModuleCat.of R (Fin ((supported_rank_sequence n 0) (j + 2)) → R)) ⊞
          ModuleCat.of R (Fin ((supported_rank_sequence n 0) (j + 1)) → R)) :
        ModuleCat R) := by
  -- Both supported counts vanish away from degree `0`, so the source coordinate is the zero
  -- biproduct.
  simpa [supported_rank_sequence] using standard_zero_biprod_isZero (R := R)

/-- Helper for Lemma 10.102.6: the `single₀` profile has the required standard-projection
normal form because every positive-degree source coordinate is zero. -/
private theorem biprodProjectionProfile_single₀_differential
    (n j : ℕ) :
    (biprodProjectionProfile_single₀_coord (R := R) n (j + 1)).inv ≫
        (((ChainComplex.single₀ (ModuleCat R)).obj
              (ModuleCat.of R (Fin n → R))).d (j + 1) j) ≫
        (biprodProjectionProfile_single₀_coord (R := R) n j).hom =
      standard_biprod_projection (R := R) (supported_rank_sequence n 0) j := by
  -- Both composites have zero source, so the source-faithful normal form is forced by
  -- uniqueness of morphisms out of the zero object.
  exact
    (biprodProjectionProfile_single₀_source_isZero (R := R) n j).eq_of_src _ _

/-- Helper for Lemma 10.102.6: package the `single₀` generator with its supported coordinate
profile. -/
private noncomputable def biprodProjectionProfile_single₀ (n : ℕ) :
    BiprodProjectionProfile (R := R)
      ((ChainComplex.single₀ (ModuleCat R)).obj (ModuleCat.of R (Fin n → R))) :=
  { r := supported_rank_sequence n 0
    coord := biprodProjectionProfile_single₀_coord (R := R) n
    differential := biprodProjectionProfile_single₀_differential (R := R) n }

/-- Helper for Lemma 10.102.6: the local public model of `identityDiskComplex` with the same
support and differential formulas as in Lemma `10.102.2`. -/
private def local_identityDiskRank {e : ℕ} (i : Fin e) (j : ℕ) : ℕ :=
  if j = i.1 + 1 ∨ j = i.1 then 1 else 0

/-- Helper for Lemma 10.102.6: the matrix of the local identity-disk differential. -/
private def local_identityDiskMatrix {e : ℕ} (i : Fin e) (j : ℕ) :
    Matrix (Fin (local_identityDiskRank i (j + 1)))
      (Fin (local_identityDiskRank i j)) R :=
  fun _ _ ↦ if j = i.1 then 1 else 0

/-- Helper for Lemma 10.102.6: the local identity-disk differential written through the standard
matrix model. -/
private abbrev local_identityDiskDifferential {e : ℕ} (i : Fin e) (j : ℕ) :
    ModuleCat.of R (Fin (local_identityDiskRank i (j + 1)) → R) ⟶
      ModuleCat.of R (Fin (local_identityDiskRank i j) → R) :=
  ModuleCat.ofHom ((local_identityDiskMatrix (R := R) i j).toLinearMapRight')

/-- Helper for Lemma 10.102.6: away from the supported degree, the local identity-disk
differential vanishes. -/
private theorem local_identityDiskDifferential_eq_zero_of_ne {e : ℕ}
    (i : Fin e) {j : ℕ} (hj : j ≠ i.1) :
    local_identityDiskDifferential (R := R) i j =
      (0 :
        ModuleCat.of R (Fin (local_identityDiskRank i (j + 1)) → R) ⟶
          ModuleCat.of R (Fin (local_identityDiskRank i j) → R)) := by
  have hMatrix :
      local_identityDiskMatrix (R := R) i j =
        (0 :
          Matrix (Fin (local_identityDiskRank i (j + 1)))
            (Fin (local_identityDiskRank i j)) R) := by
    ext a b
    simp [local_identityDiskMatrix, hj]
  let M0 :
      Matrix (Fin (local_identityDiskRank i (j + 1)))
        (Fin (local_identityDiskRank i j)) R := 0
  have hLinear :
      M0.toLinearMapRight' =
        (0 :
          (Fin (local_identityDiskRank i (j + 1)) → R) →ₗ[R]
            Fin (local_identityDiskRank i j) → R) := by
    ext x y
    simp [M0]
  rw [local_identityDiskDifferential, hMatrix]
  change ModuleCat.ofHom (M0.toLinearMapRight') = 0
  rw [hLinear]
  rfl

/-- Helper for Lemma 10.102.6: the remaining source-faithful blocker is to extract, from a direct
sum decomposition into trivial complexes, the split-basis profile whose counts satisfy the source
recurrence and whose differentials become standard projections in those coordinates. -/
private theorem exists_standard_projection_profile_of_positiveRankSum_eq_zero
    [Nontrivial R]
    (C : FiniteFreeComplex R e)
    (hzero : positiveRankSum (R := R) C = 0) :
    ∃ r : Fin e → ℕ,
      (∀ j : Fin (e - 1),
        (r (adjacentLeftIndex j) : ℤ) + r (adjacentRightIndex j) =
          C.rank (adjacentMiddleIndex j)) ∧
      (∀ h : 0 < e, (r ⟨e - 1, by omega⟩ : ℤ) = C.rank ⟨e, by omega⟩) ∧
      (∀ i : Fin e, (exteriorRank (C.diffAt i) : ℤ) = r i) ∧
      (∀ i : Fin e, I(C.diffAt i) = ⊤) := by
  refine ⟨fun _ ↦ 0, ?_, ?_, ?_, ?_⟩
  · intro j
    -- Every positive displayed rank vanishes, so the adjacent middle rank is `0`.
    have hmid :
        C.rank (adjacentMiddleIndex j) = 0 := by
      simpa [adjacentLeftIndex, adjacentMiddleIndex] using
        rank_succ_eq_zero_of_positiveRankSum_eq_zero (R := R) (C := C) hzero
          (adjacentLeftIndex j)
    simpa [hmid]
  · intro h
    -- The top displayed rank also vanishes in the zero positive-rank branch.
    have htop :
        C.rank ⟨e, by omega⟩ = 0 := by
      let j : Fin e := ⟨e - 1, by omega⟩
      have hj : C.rank j.succ = 0 :=
        rank_succ_eq_zero_of_positiveRankSum_eq_zero (R := R) (C := C) hzero j
      have hj' : C.rank ⟨e - 1 + 1, by omega⟩ = 0 := by
        simpa [j] using hj
      have hs : e - 1 + 1 = e := by
        omega
      simpa [hs] using hj'
    simpa [htop]
  · intro i
    -- With zero positive-degree source, every displayed differential is the zero map.
    have hdiff :
        C.diffAt i = 0 :=
      diffAt_eq_zero_of_positiveRankSum_eq_zero (R := R) (C := C) hzero i
    rw [hdiff, exteriorRank_zero_eq_zero (R := R) (m := C.rank i.succ) (n := C.rank i.castSucc)]
  · intro i
    -- The zero differential has unit rank-minor ideal by the size-`0` minor convention.
    have hdiff :
        C.diffAt i = 0 :=
      diffAt_eq_zero_of_positiveRankSum_eq_zero (R := R) (C := C) hzero i
    rw [hdiff, rankMinorIdeal_zero_eq_top (R := R) (m := C.rank i.succ) (n := C.rank i.castSucc)]

/-- Helper for Lemma 10.102.6: the remaining source-faithful blocker is to extract, from a direct
sum decomposition into trivial complexes, the split-basis profile whose counts satisfy the source
recurrence and whose differentials become standard projections in those coordinates. -/
private theorem exists_standard_projection_profile_of_isDirectSumOfTrivialComplexes
    [Nontrivial R]
    (C : FiniteFreeComplex R e)
    (hC : IsDirectSumOfTrivialComplexes C.toChainComplex) :
    ∃ r : Fin e → ℕ,
      (∀ j : Fin (e - 1),
        (r (adjacentLeftIndex j) : ℤ) + r (adjacentRightIndex j) =
          C.rank (adjacentMiddleIndex j)) ∧
      (∀ h : 0 < e, (r ⟨e - 1, by omega⟩ : ℤ) = C.rank ⟨e, by omega⟩) ∧
      (∀ i : Fin e, (exteriorRank (C.diffAt i) : ℤ) = r i) ∧
      (∀ i : Fin e, I(C.diffAt i) = ⊤) := by
  by_cases hzero : positiveRankSum (R := R) C = 0
  · -- The zero positive-rank branch is already complete without using the decomposition.
    exact exists_standard_projection_profile_of_positiveRankSum_eq_zero
      (R := R) (C := C) hzero
  · -- Route correction: the open frontier is now only the genuinely positive-rank decomposition.
    -- The source proof counts basis vectors globally in a split basis coming from `hC`, then
    -- reads each differential as a standard projection.
    have hsingle_exact :
        ∀ n j : ℕ, 1 ≤ j →
          (((ChainComplex.single₀ (ModuleCat R)).obj
              (ModuleCat.of R (Fin n → R))).ExactAt j) :=
      fun n j hj ↦ exactAt_single₀ (R := R) n j hj
    -- The zero branch is handled above; the remaining frontier is the source-faithful
    -- split-basis/profile extraction for the positive-rank disk, identity-disk, biproduct, and
    -- transport steps. The numeric bookkeeping from a degreewise block decomposition back to the
    -- displayed ranks is already isolated in `rank_eq_add_of_iso_biprod_standard_module`.
    -- TODO: recurse on `hC`, construct the single-sequence block profile `C_j ≅ R^{r_{j + 1}} ⊞
    -- R^{r_j}` with differential `(x, y) ↦ (y, 0)` in the positive-rank branch, and then read
    -- off the recurrence, exterior ranks, and unit minors from that profile.
    sorry

-- Proof sketch: identify the complex with a split exact sum of two-term identity complexes. In
-- that model each differential is a projection onto a free summand of rank equal to the relevant
-- alternating sum, adjacent projection ranks add to the rank of the middle term, and the maximal
-- minors include a unit so the associated ideal is the unit ideal.
/-- Lemma 10.102.6: if the bounded finite free complex is isomorphic to a direct sum of trivial
two-term complexes, then each differential has the expected alternating rank formula, adjacent
differential ranks add to the rank of the middle term, and each ideal `I(φ_i)` is the unit ideal.
-/
theorem exteriorRank_diffAt_eq_alternatingRankFormula_of_isDirectSumOfTrivialComplexes
    [Nontrivial R]
    (hC : IsDirectSumOfTrivialComplexes C.toChainComplex)
    (i : Fin e) :
    (exteriorRank (C.diffAt i) : ℤ) = C.alternatingRank i := by
  by_cases hzero : positiveRankSum (R := R) C = 0
  · -- Base case: every positive-degree term has rank `0`, so both sides are `0`.
    have hdiff : C.diffAt i = 0 :=
      diffAt_eq_zero_of_positiveRankSum_eq_zero (R := R) (C := C) hzero i
    have halt : C.alternatingRank i = 0 :=
      alternatingRank_eq_zero_of_positiveRankSum_eq_zero (R := R) (C := C) hzero i
    rw [hdiff, exteriorRank_zero_eq_zero (R := R) (m := C.rank i.succ) (n := C.rank i.castSucc), halt]
    norm_num
  · -- Route correction: use the source split-basis profile rather than the abandoned peel route.
    obtain ⟨r, hrec, htop, hexterior, -⟩ :=
      exists_standard_projection_profile_of_isDirectSumOfTrivialComplexes (C := C) hC
    calc
      (exteriorRank (C.diffAt i) : ℤ) = r i := hexterior i
      _ = C.alternatingRank i :=
        alternatingRank_eq_of_profile_recurrence (C := C) r hrec htop i

/-- In the direct-sum-of-trivial-complexes situation, adjacent differential ranks add up to the
rank of the middle term. The index `i` corresponds to the consecutive differentials
`C_{i + 2} → C_{i + 1} → C_i`. -/
theorem adjacent_differential_exteriorRank_add_eq
    [Nontrivial R]
    (hC : IsDirectSumOfTrivialComplexes C.toChainComplex)
    (i : Fin (e - 1)) :
    exteriorRank (C.diffAt (adjacentLeftIndex i)) +
        exteriorRank (C.diffAt (adjacentRightIndex i)) =
      C.rank (adjacentMiddleIndex i) := by
  -- Rewrite both exterior ranks using the main rank formula, then telescope the two alternating
  -- tails to the middle rank.
  have hsum :
      (exteriorRank (C.diffAt (adjacentLeftIndex i)) : ℤ) +
          exteriorRank (C.diffAt (adjacentRightIndex i)) =
        C.rank (adjacentMiddleIndex i) := by
    rw [exteriorRank_diffAt_eq_alternatingRankFormula_of_isDirectSumOfTrivialComplexes
          (C := C) hC (adjacentLeftIndex i)]
    rw [exteriorRank_diffAt_eq_alternatingRankFormula_of_isDirectSumOfTrivialComplexes
          (C := C) hC (adjacentRightIndex i)]
    exact adjacent_alternatingRank_add_eq_rank (C := C) i
  exact_mod_cast hsum

/-- In the direct-sum-of-trivial-complexes situation, the rank-minor ideal of every differential
is the unit ideal. -/
theorem rankMinorIdeal_diffAt_eq_top_of_isDirectSumOfTrivialComplexes
    [Nontrivial R]
    (hC : IsDirectSumOfTrivialComplexes C.toChainComplex)
    (i : Fin e) :
    I(C.diffAt i) = ⊤ := by
  by_cases hzero : positiveRankSum (R := R) C = 0
  · -- Base case: the differential is the zero map, whose rank-minor ideal is `⊤`.
    have hdiff : C.diffAt i = 0 :=
      diffAt_eq_zero_of_positiveRankSum_eq_zero (R := R) (C := C) hzero i
    rw [hdiff, rankMinorIdeal_zero_eq_top (R := R) (m := C.rank i.succ) (n := C.rank i.castSucc)]
  · -- Route correction: the same split-basis profile carries the obvious unit minor.
    obtain ⟨-, -, -, -, hminor⟩ :=
      exists_standard_projection_profile_of_isDirectSumOfTrivialComplexes (C := C) hC
    exact hminor i

end FiniteFreeComplex

end

/-! ### Lemma_10_102_7 (from Chap10) -/
universe u

open CategoryTheory HomologicalComplex

namespace ModuleCat

variable {R : Type u} [CommRing R]

/-- Bridge/view: the endofunctor on `ModuleCat R` induced by the canonical module quotient map
`QuotSMulTop.map x`. Its only role here is to apply `mapHomologicalComplex` to quotient a complex
termwise modulo `x`; the owner-level module data remain `QuotSMulTop` and `QuotSMulTop.map`. -/
def quotSMulTopFunctor (x : R) : ModuleCat R ⥤ ModuleCat R where
  obj M := ModuleCat.of R (QuotSMulTop x M)
  map f := ModuleCat.ofHom (QuotSMulTop.map x f.hom)
  map_id M := by
    change ModuleCat.ofHom (QuotSMulTop.map x (LinearMap.id : M →ₗ[R] M)) =
      ModuleCat.ofHom (LinearMap.id : QuotSMulTop x M →ₗ[R] QuotSMulTop x M)
    exact congrArg ModuleCat.ofHom (QuotSMulTop.map_id x M)
  map_comp f g := by
    change ModuleCat.ofHom (QuotSMulTop.map x (g.hom ∘ₗ f.hom)) =
      ModuleCat.ofHom (QuotSMulTop.map x g.hom ∘ₗ QuotSMulTop.map x f.hom)
    exact congrArg ModuleCat.ofHom (QuotSMulTop.map_comp x g.hom f.hom)

instance (x : R) : (quotSMulTopFunctor x).PreservesZeroMorphisms where
  map_zero X Y := by
    change ModuleCat.ofHom (QuotSMulTop.map x (0 : X →ₗ[R] Y)) =
      ModuleCat.ofHom (0 : QuotSMulTop x X →ₗ[R] QuotSMulTop x Y)
    apply congrArg ModuleCat.ofHom
    ext y
    rfl

end ModuleCat

section

variable {R : Type u} [CommRing R]
variable {e : ℕ}

/-- Helper for Lemma 10.102.7: in a chain complex of `R`-modules, exactness at a positive degree
is equivalent to exactness of the consecutive differentials as linear maps. -/
private lemma exactAt_iff_function_exact
    (K : ChainComplex (ModuleCat R) ℕ) {j : ℕ} (hj : 1 ≤ j) :
    K.ExactAt j ↔ Function.Exact (K.d (j + 1) j).hom (K.d j (j - 1)).hom := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  have hmid : 1 + k = k + 1 := by omega
  have hsucc : k + 1 + 1 = k + 2 := by omega
  have hpred : k + 1 - 1 = k := by omega
  -- Re-index `ExactAt` through the explicit three-term window around a successor degree.
  rw [hmid, hsucc, hpred]
  rw [HomologicalComplex.exactAt_iff' K (k + 2) (k + 1) k (by simp) (by simp)]
  -- For modules, short-complex exactness is exactly `Function.Exact` on the underlying maps.
  simpa [HomologicalComplex.sc'] using
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (K.sc' (k + 2) (k + 1) k))

/-- Helper for Lemma 10.102.7: if two adjacent degrees of a chain complex are exact and the last
term of the resulting four-term window is `x`-torsion-free, then quotienting termwise by `x`
preserves exactness at the middle degree. -/
private lemma exactAt_map_quotSMulTop_of_adjacent_exactAt
    (K : ChainComplex (ModuleCat R) ℕ) {x : R} {j : ℕ} (hj : 2 ≤ j)
    (h_exact_j : K.ExactAt j) (h_exact_prev : K.ExactAt (j - 1))
    (hreg : IsSMulRegular (K.X (j - 2)) x) :
    (((ModuleCat.quotSMulTopFunctor x).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj K).ExactAt j := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  -- Translate the target exactness of the quotient complex into exactness of mapped differentials.
  have h_target :
      (((ModuleCat.quotSMulTopFunctor x).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj K).ExactAt (2 + k) ↔
        Function.Exact
          (QuotSMulTop.map x (K.d (k + 3) (k + 2)).hom)
          (QuotSMulTop.map x (K.d (k + 2) (k + 1)).hom) := by
    simpa [ModuleCat.quotSMulTopFunctor, CategoryTheory.Functor.mapHomologicalComplex_obj_d,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (exactAt_iff_function_exact
        ((((ModuleCat.quotSMulTopFunctor x).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj K)) (show 1 ≤ k + 2 by omega))
  rw [h_target]
  -- The source exactness assumptions provide the two adjacent exact pairs needed by the
  -- four-term quotient exactness lemma.
  have h_exact_j' : K.ExactAt (k + 2) := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h_exact_j
  have h_exact_prev' : K.ExactAt (k + 1) := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h_exact_prev
  have hreg' : IsSMulRegular (K.X k) x := by
    have hdeg : 2 + k - 2 = k := by omega
    rw [hdeg] at hreg
    exact hreg
  have h12 : Function.Exact (K.d (k + 3) (k + 2)).hom (K.d (k + 2) (k + 1)).hom := by
    exact (exactAt_iff_function_exact K (show 1 ≤ k + 2 by omega)).mp h_exact_j'
  have h23 : Function.Exact (K.d (k + 2) (k + 1)).hom (K.d (k + 1) k).hom := by
    exact (exactAt_iff_function_exact K (show 1 ≤ k + 1 by omega)).mp h_exact_prev'
  -- Apply the module-level exactness lemma for termwise quotients modulo a regular element.
  exact QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last h12 h23 hreg'

-- Domain sampling pass:
-- * Primary domain: bounded chain complexes of modules, organized by the chapter owner
--   `FiniteFreeComplex` and the canonical exactness predicate `HomologicalComplex.ExactAt`.
-- * Relevant declarations sampled in this domain: `FiniteFreeComplex.toChainComplex`,
--   `HomologicalComplex.ExactAt`, `ModuleCat.smulShortComplex`, and
--   `QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last`.
-- * Best owner abstraction: exactness lives on `HomologicalComplex.ExactAt`; the primitive
--   quotient data are `QuotSMulTop` and `QuotSMulTop.map`, while
--   `ModuleCat.quotSMulTopFunctor` is only the bridge needed to apply `mapHomologicalComplex`.
-- * Primitive data are the finite free complex `C` and the nonzerodivisor `x`; the displayed
--   quotient complex and its exactness are derived API from `C.toChainComplex` via
--   `ModuleCat.quotSMulTopFunctor`.
--
-- Proof sketch: apply `QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last`
-- successively to the four-term windows of `C.toChainComplex`. Since each term of a
-- `FiniteFreeComplex` is free, a ring nonzerodivisor `x` is regular on every term, and the
-- exactness assumptions in degrees `e, …, 1` propagate to the quotient complex in degrees
-- `e, …, 2`.
/-- Lemma 10.102.7: in Situation 10.102.1, if the finite free complex is exact in degrees
`e, …, 1` and `x` is a nonzerodivisor, then the quotient complex modulo `x` is
exact in degrees `e, …, 2`. -/
theorem exact_mod_nonzerodivisor_of_exact
    (C : FiniteFreeComplex R e) {x : R} (hreg : IsRegular x)
    (hexact : ∀ j : ℕ, 1 ≤ j → j ≤ e → C.toChainComplex.ExactAt j) :
    ∀ j : ℕ, 2 ≤ j → j ≤ e →
      (((ModuleCat.quotSMulTopFunctor x).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj C.toChainComplex).ExactAt j := by
  intro j hj hje
  -- The source proof uses the four-term window around `j`, together with regularity of `x` on the
  -- free term in degree `j - 2`, to deduce quotient exactness at degree `j`.
  have h_exact_j : C.toChainComplex.ExactAt j :=
    hexact j (show 1 ≤ j by omega) hje
  have h_exact_prev : C.toChainComplex.ExactAt (j - 1) :=
    hexact (j - 1) (show 1 ≤ j - 1 by omega) (show j - 1 ≤ e by omega)
  have hsmul : IsSMulRegular (C.toChainComplex.X (j - 2)) x :=
    Module.Flat.isSMulRegular_of_isRegular hreg
  exact exactAt_map_quotSMulTop_of_adjacent_exactAt C.toChainComplex hj h_exact_j h_exact_prev hsmul

end
