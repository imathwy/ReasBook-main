import StacksProject_2024.Chap10.Remark_10_102_10.InductionBridge

-- Theorem-local support for the minimal local branch in `Remark_10_102_10`.

universe u

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open RingTheory
open scoped ENat

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {e : ℕ}

namespace FiniteFreeComplex

/-- Helper for Remark 10.102.10: every positive exterior power of the zero map vanishes. -/
lemma exteriorPower_map_zero_eq_zero {m n r : ℕ} (hr : 0 < r) :
    exteriorPower.map r (0 : (Fin m → R) →ₗ[R] (Fin n → R)) = 0 := by
  -- Proof comment: on any alternating generator, one exterior factor is already sent to `0`.
  ext v
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr) with ⟨s, rfl⟩
  simp

/-- Helper for Remark 10.102.10: evaluating `diffAt i` on source coordinates carried over from
the chain-complex term rewrites back to the owner differential. -/
lemma diffAt_termIso_hom_apply
    (C : _root_.FiniteFreeComplex R e) (i : Fin e) (v : C.toChainComplex.X (i.1 + 1)) :
    C.diffAt i ((C.termIso i.succ).hom v) =
      (C.termIso i.castSucc).hom ((C.toChainComplex.d (i.1 + 1) i.1).hom v) := by
  have hcomp :
      (C.termIso i.succ).hom ≫ ModuleCat.ofHom (C.diffAt i) =
        C.toChainComplex.d (i.1 + 1) i.1 ≫ (C.termIso i.castSucc).hom := by
    -- Proof comment: expand `diffAt` once and cancel the source-side coordinate isomorphism.
    change
      (C.termIso i.succ).hom ≫ (C.termIso i.succ).inv ≫
          C.toChainComplex.d (i.1 + 1) i.1 ≫ (C.termIso i.castSucc).hom =
        C.toChainComplex.d (i.1 + 1) i.1 ≫ (C.termIso i.castSucc).hom
    simp [Category.assoc]
  -- Proof comment: evaluating the recorded conjugation identity on `v` gives the desired formula.
  change (((C.termIso i.succ).hom ≫ ModuleCat.ofHom (C.diffAt i)).hom v) =
    ((C.toChainComplex.d (i.1 + 1) i.1 ≫ (C.termIso i.castSucc).hom).hom v)
  rw [hcomp]
  rfl

/-- Helper for Remark 10.102.10: the zero map has exterior rank `0`. -/
lemma exteriorRank_zero_eq_zero {m n : ℕ} :
    LinearMap.exteriorRank (0 : (Fin m → R) →ₗ[R] (Fin n → R)) = 0 := by
  classical
  letI :
      DecidablePred
        (fun r ↦ exteriorPower.map r (0 : (Fin m → R) →ₗ[R] (Fin n → R)) ≠ 0) :=
    Classical.decPred _
  -- Proof comment: all positive exterior-power maps vanish, so `Nat.findGreatest` can only be `0`.
  unfold LinearMap.exteriorRank
  rw [Nat.findGreatest_eq_zero_iff]
  intro r hr hk
  simp [exteriorPower_map_zero_eq_zero (R := R) (m := m) (n := n) hr]

/-- Helper for Remark 10.102.10: the rank-minor ideal of the zero map is the unit ideal. -/
lemma rankMinorIdeal_zero_eq_top {m n : ℕ} :
    I((0 : (Fin m → R) →ₗ[R] (Fin n → R))) = ⊤ := by
  -- Proof comment: for rank `0` minors the unique `0 x 0` determinant is `1`.
  rw [LinearMap.rankMinorIdeal, exteriorRank_zero_eq_zero (R := R) (m := m) (n := n)]
  simp [Matrix.minorIdeal]

/-- Helper for Remark 10.102.10: a nonzero map between finite free modules has positive exterior
rank. Equivalently, exterior rank `0` is the same as the zero map. -/
lemma exteriorRank_eq_zero_iff_eq_zero {m n : ℕ}
    (φ : (Fin m → R) →ₗ[R] (Fin n → R)) :
    LinearMap.exteriorRank φ = 0 ↔ φ = 0 := by
  classical
  letI :
      DecidablePred
        (fun r ↦ exteriorPower.map r φ ≠ 0) :=
    Classical.decPred _
  constructor
  · intro hzero
    by_contra hφ
    have hm : 0 < m := by
      by_contra hm
      have hm' : m = 0 := Nat.eq_zero_of_not_pos hm
      subst hm'
      apply hφ
      simpa using
        (Subsingleton.elim φ (0 : (Fin 0 → R) →ₗ[R] (Fin n → R)))
    have hn : 0 < n := by
      by_contra hn
      have hn' : n = 0 := Nat.eq_zero_of_not_pos hn
      subst hn'
      apply hφ
      simpa using
        (Subsingleton.elim φ (0 : (Fin m → R) →ₗ[R] (Fin 0 → R)))
    have hmap1 : exteriorPower.map 1 φ ≠ 0 := by
      intro hmap1_zero
      have hφzero : φ = 0 := by
        apply LinearMap.ext
        intro x
        obtain ⟨y, hy⟩ := (exteriorPower.oneEquiv R (Fin m → R)).surjective x
        rw [← hy]
        have hcomp :
            φ.comp (exteriorPower.oneEquiv R (Fin m → R)).toLinearMap = 0 := by
          rw [← exteriorPower.oneEquiv_naturality (R := R) (M := Fin m → R)
              (N := Fin n → R) φ]
          simp [hmap1_zero]
        exact LinearMap.congr_fun hcomp y
      exact hφ hφzero
    have hle : 1 ≤ LinearMap.exteriorRank φ := by
      -- Proof comment: a nonzero first exterior-power map forces the `findGreatest`
      -- defining `exteriorRank` to be at least `1`.
      have hmn : 1 ≤ min m n := by
        omega
      unfold LinearMap.exteriorRank
      exact Nat.le_findGreatest hmn hmap1
    omega
  · intro hφ
    rw [hφ]
    exact exteriorRank_zero_eq_zero (R := R) (m := m) (n := n)
/-- Helper for Remark 10.102.10: every positive-size minor of a matrix whose entries lie in the
maximal ideal still lies in the maximal ideal. -/
lemma det_submatrix_mem_maximal_of_entries_mem_maximal {m n r : ℕ}
    (hr : 0 < r)
    (φ : (Fin m → R) →ₗ[R] (Fin n → R))
    (hmax : ∀ a : Fin m, ∀ b : Fin n, φ (Pi.single a 1) b ∈ IsLocalRing.maximalIdeal R)
    (e₁ : Fin r ↪ Fin n) (e₂ : Fin r ↪ Fin m) :
    Matrix.det
        ((LinearMap.toMatrix (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n)) φ).submatrix e₁ e₂) ∈
      IsLocalRing.maximalIdeal R := by
  classical
  let M :
      Matrix (Fin r) (Fin r) R :=
    (LinearMap.toMatrix (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n)) φ).submatrix e₁ e₂
  let i0 : Fin r := ⟨0, hr⟩
  -- Proof comment: expand the determinant by Leibniz. Since `r > 0`, every permutation term has
  -- the factor indexed by `i0`, and that factor is one of the original matrix entries in the
  -- maximal ideal.
  rw [show Matrix.det M = ∑ σ : Equiv.Perm (Fin r), Equiv.Perm.sign σ * ∏ i, M (σ i) i by
    simpa [M] using Matrix.det_apply' M]
  refine Ideal.sum_mem _ fun σ _ ↦ ?_
  have hentry : M (σ i0) i0 ∈ IsLocalRing.maximalIdeal R := by
    -- Proof comment: the chosen Leibniz factor is exactly one displayed entry of `φ`.
    dsimp [M]
    simpa [LinearMap.toMatrix_apply] using hmax (e₂ i0) (e₁ (σ i0))
  have hprod : ∏ i, M (σ i) i ∈ IsLocalRing.maximalIdeal R := by
    rw [← Finset.mul_prod_erase Finset.univ (fun i : Fin r ↦ M (σ i) i) (Finset.mem_univ i0)]
    exact Ideal.mul_mem_right _ _ hentry
  exact (IsLocalRing.maximalIdeal R).mul_mem_left _ hprod

/-- Helper for Remark 10.102.10: in the minimal local branch where every displayed matrix entry
lies in the maximal ideal, the unit rank-minor ideal is equivalent to the differential being
zero. -/
lemma rankMinorIdeal_eq_top_iff_eq_zero_of_entries_mem_maximal
    [Nontrivial R]
    (C : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    (hmax :
      ∀ a : Fin (C.rank i.succ), ∀ b : Fin (C.rank i.castSucc),
        C.diffEntry i a b ∈ IsLocalRing.maximalIdeal R) :
    I(C.diffAt i) = ⊤ ↔ C.diffAt i = 0 := by
  constructor
  · intro htop
    by_contra hzero
    have hrpos : 0 < LinearMap.exteriorRank (C.diffAt i) := by
      refine Nat.pos_iff_ne_zero.2 ?_
      intro hrzero
      exact hzero <| (exteriorRank_eq_zero_iff_eq_zero (R := R) (φ := C.diffAt i)).mp hrzero
    have hentry_max :
        ∀ a : Fin (C.rank i.succ), ∀ b : Fin (C.rank i.castSucc),
          (C.diffAt i) (Pi.single a 1) b ∈ IsLocalRing.maximalIdeal R := by
      intro a b
      simpa [FiniteFreeComplex.diffEntry] using hmax a b
    have hle :
        I(C.diffAt i) ≤ IsLocalRing.maximalIdeal R := by
      -- Proof comment: every generator of the rank-minor ideal is one of the positive-size minors
      -- handled by the previous determinant lemma.
      rw [LinearMap.rankMinorIdeal]
      refine Ideal.span_le.2 ?_
      intro x hx
      rcases hx with ⟨⟨e₁, e₂⟩, rfl⟩
      exact det_submatrix_mem_maximal_of_entries_mem_maximal (R := R) (hr := hrpos)
        (φ := C.diffAt i) hentry_max e₁ e₂
    have hne_top : I(C.diffAt i) ≠ ⊤ :=
      ne_top_of_le_ne_top ((IsLocalRing.maximalIdeal.isMaximal R).ne_top) hle
    exact hne_top htop
  · intro hzero
    rw [hzero]
    exact rankMinorIdeal_zero_eq_top (R := R) (m := C.rank i.succ) (n := C.rank i.castSucc)

/-- Helper for Remark 10.102.10: in the minimal local branch, the displayed differential becomes
zero after quotienting by the maximal ideal. -/
lemma quotientMapByIdeal_eq_zero_of_entries_mem_maximal
    (C : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    (hmax :
      ∀ a : Fin (C.rank i.succ), ∀ b : Fin (C.rank i.castSucc),
        C.diffEntry i a b ∈ IsLocalRing.maximalIdeal R) :
    (C.diffAt i).quotientMapByIdeal (IsLocalRing.maximalIdeal R) = 0 := by
  refine LinearMap.ext fun x ↦ ?_
  obtain ⟨y, rfl⟩ :=
    Submodule.mkQ_surjective
      (IsLocalRing.maximalIdeal R • (⊤ : Submodule R (C.term i.succ))) x
  -- Proof comment: every coordinate of `C.diffAt i y` is an `R`-linear combination of displayed
  -- matrix entries already lying in the maximal ideal, so the whole image dies modulo that ideal.
  have hy_mem :
      C.diffAt i y ∈
        IsLocalRing.maximalIdeal R • (⊤ : Submodule R (C.term i.castSucc)) := by
    have hcoeff :
        ∀ b : Fin (C.rank i.castSucc),
          (C.diffAt i y) b ∈ IsLocalRing.maximalIdeal R := by
      intro b
      have hdecomp :
          y =
            ∑ a : Fin (C.rank i.succ),
              y a • (Pi.single a (1 : R) : C.term i.succ) := by
        ext a
        rw [Finset.sum_apply, Finset.sum_eq_single a]
        · change y a = y a * ((Pi.single a (1 : R) : C.term i.succ) a)
          simp
        · intro j _ hja
          change y j * ((Pi.single j (1 : R) : C.term i.succ) a) = 0
          have hsingle : ((Pi.single j (1 : R) : C.term i.succ) a) = 0 := by
            simpa [Pi.single_apply, hja]
          rw [hsingle]
          simp
        · intro ha
          exact (ha (Finset.mem_univ a)).elim
      rw [hdecomp, map_sum, Finset.sum_apply]
      show
        ∑ a : Fin (C.rank i.succ),
            (C.diffAt i (y a • (Pi.single a (1 : R) : C.term i.succ))) b ∈
          IsLocalRing.maximalIdeal R
      refine Ideal.sum_mem _ fun a _ ↦ ?_
      have hentry : C.diffEntry i a b ∈ IsLocalRing.maximalIdeal R := hmax a b
      have hterm :
          (C.diffAt i (y a • (Pi.single a (1 : R) : C.term i.succ))) b =
            y a * C.diffEntry i a b := by
        have hmap :
            C.diffAt i (y a • (Pi.single a (1 : R) : C.term i.succ)) =
              y a • C.diffAt i (Pi.single a (1 : R) : C.term i.succ) := by
          rw [LinearMap.map_smul]
        have hentry_eq :
            (C.diffAt i (Pi.single a (1 : R) : C.term i.succ)) b =
              C.diffEntry i a b := by
          simp [FiniteFreeComplex.diffEntry]
        calc
          (C.diffAt i (y a • (Pi.single a (1 : R) : C.term i.succ))) b =
              (y a • C.diffAt i (Pi.single a (1 : R) : C.term i.succ)) b := by
                simpa using congrArg (fun z : C.term i.castSucc ↦ z b) hmap
          _ = y a * C.diffEntry i a b := by
                change
                  y a * (C.diffAt i (Pi.single a (1 : R) : C.term i.succ)) b =
                    y a * C.diffEntry i a b
                rw [hentry_eq]
      have hmul_mem :
          C.diffEntry i a b * y a ∈ IsLocalRing.maximalIdeal R :=
        Ideal.mul_mem_right (y a) _ hentry
      rw [hterm, mul_comm]
      exact hmul_mem
    have hsum :
        C.diffAt i y =
          ∑ b : Fin (C.rank i.castSucc),
            (C.diffAt i y) b • (Pi.single b (1 : R) : C.term i.castSucc) := by
      ext b
      rw [Finset.sum_apply, Finset.sum_eq_single b]
      · simp [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
      · intro j _ hjb
        simp [Pi.smul_apply, Pi.single_apply, hjb, smul_eq_mul]
      · simp
    rw [hsum]
    refine Submodule.sum_mem _ fun b _ ↦ ?_
    exact Submodule.smul_mem_smul (hcoeff b)
      (by simp : (Pi.single b (1 : R) : C.term i.castSucc) ∈
        (⊤ : Submodule R (C.term i.castSucc)))
  exact (Submodule.Quotient.mk_eq_zero _).2 hy_mem

/-- Helper for Remark 10.102.10: if the exact row ending in `C.diffAt j` has `C.diffAt j = 0`,
then the next differential also vanishes in the minimal local branch. -/
lemma diffAt_next_eq_zero_of_exact_of_zero_of_entries_mem_maximal
    [Nontrivial R]
    (C : _root_.FiniteFreeComplex R e)
    (hExact : C.ExactInPositiveDegrees)
    (hmax :
      ∀ i : Fin e, ∀ a : Fin (C.rank i.succ), ∀ b : Fin (C.rank i.castSucc),
        C.diffEntry i a b ∈ IsLocalRing.maximalIdeal R)
    (j : Fin e)
    (hj : j.1 + 1 < e)
    (hzero : C.diffAt j = 0) :
    C.diffAt ⟨j.1 + 1, hj⟩ = 0 := by
  let k : Fin e := ⟨j.1 + 1, hj⟩
  have hexact :
      Function.Exact (C.toChainComplex.d (j.1 + 2) (j.1 + 1)).hom
        (C.toChainComplex.d (j.1 + 1) j.1).hom := by
    -- Proof comment: exactness at degree `j + 1` gives exactness of the adjacent concrete linear
    -- maps in the underlying chain complex.
    exact (exactAt_iff_function_exact (R := R) (K := C.toChainComplex) (j := j.1 + 1)
      (by omega)).mp (hExact (j.1 + 1) (by omega) (by omega))
  have hzero_owner : (C.toChainComplex.d (j.1 + 1) j.1).hom = 0 := by
    have hzero_morph : C.toChainComplex.d (j.1 + 1) j.1 = 0 := by
      -- Proof comment: conjugate the displayed zero differential back to chain-complex
      -- coordinates by cancelling the chosen term isomorphisms.
      calc
        C.toChainComplex.d (j.1 + 1) j.1 =
            (C.termIso j.succ).hom ≫ (C.termIso j.succ).inv ≫ C.toChainComplex.d (j.1 + 1) j.1 ≫
              (C.termIso j.castSucc).hom ≫ (C.termIso j.castSucc).inv := by
                simp [Category.assoc]
        _ = (C.termIso j.succ).hom ≫ ModuleCat.ofHom (C.diffAt j) ≫
              (C.termIso j.castSucc).inv := by
                rfl
        _ = (C.termIso j.succ).hom ≫
              ModuleCat.ofHom (0 : C.term j.succ →ₗ[R] C.term j.castSucc) ≫
              (C.termIso j.castSucc).inv := by
                rw [hzero]
        _ = 0 := by
              calc
                (C.termIso j.succ).hom ≫
                    ModuleCat.ofHom (0 : C.term j.succ →ₗ[R] C.term j.castSucc) ≫
                    (C.termIso j.castSucc).inv =
                    (C.termIso j.succ).hom ≫
                      (0 : ModuleCat.of R (C.term j.succ) ⟶ ModuleCat.of R (C.term j.castSucc)) ≫
                      (C.termIso j.castSucc).inv := by
                        rfl
                _ = (0 : C.toChainComplex.X (j.1 + 1) ⟶ C.toChainComplex.X j.1) := by
                      simp
                _ = 0 := rfl
    simpa using congrArg ModuleCat.Hom.hom hzero_morph
  have howner_surj :
      Function.Surjective ((C.toChainComplex.d (j.1 + 2) (j.1 + 1)).hom) := by
    -- Proof comment: once the outgoing differential is `0`, exactness says the previous
    -- differential has full range.
    rw [hzero_owner,
      LinearMap.exact_zero_iff_surjective (R := R) (P := C.toChainComplex.X j.1)] at hexact
    exact hexact
  have hsurj : Function.Surjective (C.diffAt k) := by
    intro y
    let y' : C.toChainComplex.X (j.1 + 1) := (C.termIso k.castSucc).inv.hom y
    obtain ⟨x', hx'⟩ := howner_surj y'
    refine ⟨(C.termIso k.succ).hom x', ?_⟩
    calc
      C.diffAt k ((C.termIso k.succ).hom x') =
          (C.termIso k.castSucc).hom ((C.toChainComplex.d (k.1 + 1) k.1).hom x') := by
            simpa [k] using diffAt_termIso_hom_apply (C := C) (i := k) (v := x')
      _ = (C.termIso k.castSucc).hom y' := by
            rw [hx']
      _ = y := by
            simpa [y'] using (C.termIso k.castSucc).toLinearEquiv.apply_symm_apply y
  have hquot_zero :
      (C.diffAt k).quotientMapByIdeal (IsLocalRing.maximalIdeal R) = 0 :=
    quotientMapByIdeal_eq_zero_of_entries_mem_maximal (R := R) (C := C) (i := k) (hmax k)
  have hsmul_top :
      IsLocalRing.maximalIdeal R • (⊤ : Submodule R (C.term j.succ)) = ⊤ := by
    apply top_unique
    intro x hx
    rw [← Submodule.Quotient.mk_eq_zero
      (IsLocalRing.maximalIdeal R • (⊤ : Submodule R (C.term j.succ)))]
    obtain ⟨y, rfl⟩ := hsurj x
    -- Proof comment: the quotient map is zero, so every quotient class in degree `j + 1`
    -- vanishes; equivalently every vector already lies in `𝔪 · C_{j + 1}`.
    have hbar_zero := LinearMap.congr_fun hquot_zero
      ((IsLocalRing.maximalIdeal R • (⊤ : Submodule R (C.term k.succ))).mkQ y)
    simpa [LinearMap.quotientMapByIdeal]
      using hbar_zero
  have hrank_zero : C.rank j.succ = 0 := by
    by_contra hrank_ne
    have hrank_pos : 0 < C.rank j.succ := Nat.pos_iff_ne_zero.mpr hrank_ne
    letI : Nonempty (Fin (C.rank j.succ)) := ⟨⟨0, hrank_pos⟩⟩
    letI : Nontrivial (C.term j.succ) := by
      infer_instance
    exact (maximalIdeal_smul_top_ne_top (R := R) (M := C.term j.succ)) hsmul_top
  have hcast_rank_zero : C.rank k.castSucc = 0 := by
    simpa [k] using hrank_zero
  letI : Subsingleton (C.term k.castSucc) := by
    simpa [FiniteFreeComplex.term, hcast_rank_zero] using
      (inferInstance : Subsingleton (Fin 0 → R))
  -- Proof comment: once the target free module has rank `0`, the next differential is forced to
  -- be the zero map.
  apply LinearMap.ext
  intro x
  exact Subsingleton.elim _ _

/-- Helper for Remark 10.102.10: once a displayed differential vanishes in the minimal local
branch, all later displayed differentials vanish as well. -/
lemma diffAt_eq_zero_propagates_tail_zero_of_entries_mem_maximal
    [Nontrivial R]
    (C : _root_.FiniteFreeComplex R e)
    (hExact : C.ExactInPositiveDegrees)
    (hmax :
      ∀ i : Fin e, ∀ a : Fin (C.rank i.succ), ∀ b : Fin (C.rank i.castSucc),
        C.diffEntry i a b ∈ IsLocalRing.maximalIdeal R)
    {j i : Fin e}
    (hzero : C.diffAt j = 0)
    (hji : j ≤ i) :
    C.diffAt i = 0 := by
  have zero_tail :
      ∀ n : ℕ, ∀ hn : j.1 + n < e, C.diffAt ⟨j.1 + n, hn⟩ = 0 := by
    intro n
    induction n with
    | zero =>
        intro hn
        have hj_eq : (⟨j.1, hn⟩ : Fin e) = j := by
          ext
          rfl
        -- Proof comment: the tail starts at the given zero differential.
        simpa [hj_eq] using hzero
    | succ n ihn =>
        intro hn
        let k : Fin e := ⟨j.1 + n, Nat.lt_of_succ_lt hn⟩
        have hk_zero : C.diffAt k = 0 := by
          simpa [k] using ihn (Nat.lt_of_succ_lt hn)
        -- Proof comment: propagate one step using exactness plus the minimal-branch Nakayama
        -- argument, then continue inductively along the tail.
        simpa [k, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          diffAt_next_eq_zero_of_exact_of_zero_of_entries_mem_maximal (R := R)
            (C := C) hExact hmax k (by simpa [k] using hn) hk_zero
  have hi_zero :
      C.diffAt ⟨j.1 + (i.1 - j.1), by
        have hi_lt : i.1 < e := i.isLt
        omega⟩ = 0 :=
    zero_tail (i.1 - j.1) (by
      have hi_lt : i.1 < e := i.isLt
      omega)
  have hidx :
      (⟨j.1 + (i.1 - j.1), by
        have hi_lt : i.1 < e := i.isLt
        omega⟩ : Fin e) = i := by
    ext
    exact Nat.add_sub_of_le hji
  rw [hidx] at hi_zero
  exact hi_zero

end FiniteFreeComplex



end
