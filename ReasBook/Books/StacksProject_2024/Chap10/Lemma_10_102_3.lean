import StacksProject_2024.Chap10.Lemma_10_102_2
import StacksProject_2024.Chap10.Situation_10_102_1
import StacksProject_2024.Chap10.Definition_10_72_1
import StacksProject_2024.Chap10.Lemma_10_72_5

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
