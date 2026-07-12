import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.RingTheory.RegularLocalRing.Defs
import StacksProject_2024.Chap10.Lemma_10_15_5
import StacksProject_2024.Chap10.Lemma_10_71_4
import StacksProject_2024.Chap10.Lemma_10_72_3
import StacksProject_2024.Chap10.Lemma_10_109_7
import StacksProject_2024.Chap10.Lemma_10_110_3
import StacksProject_2024.Chap10.Proposition_10_102_9
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits ChainComplex HomologicalComplex IsLocalRing
open RingTheory

universe u

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

local notation "moduleSingle[" R "]" M =>
  CategoryTheory.Functor.obj (ChainComplex.single₀ (ModuleCat R)) (ModuleCat.of R M)

/-
Source/core/bridge triage:
* primary domain: projective dimension of the residue field versus Krull dimension for Noetherian
  local rings;
* sampled owner declarations:
  `CategoryTheory.projectiveDimension`,
  `CategoryTheory.projectiveDimension_eq_bot_iff`,
  `CategoryTheory.projectiveDimension_ne_top_iff`,
  `IsRegularLocalRing.of_spanFinrank_maximalIdeal_le`;
* core/canonical owners: `projectiveDimension (ModuleCat.of R (ResidueField R))` and
  `ringKrullDim R`;
* layer: the textbook statement below is `source-facing`, while the finite-projective-dimension
  inequality that follows is a `bridge/view` reformulation for downstream use.

Primitive data are only the ambient local Noetherian ring and the canonical invariant
`projectiveDimension` of the residue-field module. There is no additional local owner object to
package here, so the refinement should keep the source-facing comparison theorem and expose only a
thin bridge in the canonical `projectiveDimension ≠ ⊤` language.
-/

/-- Helper for Lemma 10.110.4: a finite projective dimension value for the residue field is a
natural number as soon as the projective dimension is not `⊤`. -/
lemma projectiveDimension_residueField_eq_nat_of_ne_top
    (hpd : projectiveDimension (ModuleCat.of R (ResidueField R)) ≠ ⊤) :
    ∃ n : ℕ, projectiveDimension (ModuleCat.of R (ResidueField R)) = n := by
  -- Exclude both `⊥` and `⊤`, then unpack the remaining `ENat` value.
  have hne_bot :
      projectiveDimension (ModuleCat.of R (ResidueField R)) ≠ ⊥ := by
    intro hbot
    exact residueField_module_not_isZero (R := R) <|
      (CategoryTheory.projectiveDimension_eq_bot_iff
        (X := ModuleCat.of R (ResidueField R))).mp hbot
  obtain ⟨d, hd⟩ :=
    WithBot.ne_bot_iff_exists.mp hne_bot
  have hd_ne_top : d ≠ ⊤ := by
    intro htop
    have : projectiveDimension (ModuleCat.of R (ResidueField R)) = ⊤ := by
      calc
        projectiveDimension (ModuleCat.of R (ResidueField R)) = (d : WithBot ℕ∞) := hd.symm
        _ = ⊤ := by simpa [htop]
    exact hpd this
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hd_ne_top
  refine ⟨n, ?_⟩
  calc
    projectiveDimension (ModuleCat.of R (ResidueField R)) = (d : WithBot ℕ∞) := hd.symm
    _ = n := by
      change ((d : ℕ∞) : WithBot ℕ∞) = (n : WithBot ℕ∞)
      exact congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) hn.symm

/-- Helper for Lemma 10.110.4: a regular sequence in a Noetherian local ring has length at most
the Krull dimension. -/
lemma length_le_ringKrullDim_of_isRegular {xs : List R}
    (hreg : RingTheory.Sequence.IsRegular R xs) :
    xs.length ≤ ringKrullDim R := by
  -- Compare the regular sequence with the quotient-dimension formula.
  have hdimSeq := ringKrullDim_add_length_eq_ringKrullDim_of_isRegular xs hreg
  have hIneTop : Ideal.ofList xs ≠ ⊤ := by
    simpa [ne_comm] using hreg.top_ne_smul
  letI : Nontrivial (R ⧸ Ideal.ofList xs) := Ideal.Quotient.nontrivial_iff.2 hIneTop
  rw [← hdimSeq]
  exact le_add_of_nonneg_left ringKrullDim_nonneg_of_nontrivial

/-- Helper for Lemma 10.110.4: at the top differential of a bounded finite free complex, the
alternating rank is exactly the top displayed rank. -/
lemma alternatingRank_last_eq_rank_top
    {e : ℕ} (C : FiniteFreeComplex R (e + 1)) :
    C.alternatingRank (Fin.last e) = C.rank ⟨e + 1, by omega⟩ := by
  -- The final alternating tail consists of a single rank term.
  unfold _root_.FiniteFreeComplex.alternatingRank
  simp
  congr

/-- Helper for Lemma 10.110.4: a rank-zero displayed top term of a finite free complex is a zero
object. -/
lemma term_isZero_of_rank_eq_zero
    {e : ℕ} (C : FiniteFreeComplex R e) (j : Fin (e + 1)) (hj : C.rank j = 0) :
    Limits.IsZero (C.toChainComplex.X j) := by
  -- Transport the zero-object claim across the chosen coordinate isomorphism.
  exact (C.termIso j).isZero_iff.mpr <|
    by simpa [hj] using ModuleCat.isZero_of_subsingleton (ModuleCat.of R (Fin 0 → R))

/-- Helper for Lemma 10.110.4: any finite free resolution of the residue field is exact in all
positive degrees. -/
lemma exactInPositiveDegrees_of_residueField_resolution
    {e : ℕ} (C : FiniteFreeComplex R e)
    (ρ : C.toChainComplex ⟶ moduleSingle[R] (ResidueField R))
    (hρ : ChainComplex.IsFiniteFreeResolution ρ) :
    C.ExactInPositiveDegrees := by
  -- Make the augmentation available as a quasi-isomorphism and read off exactness away from
  -- degree `0`.
  letI : QuasiIso ρ := hρ.toIsFreeResolution.toQuasiIso
  intro j hj hje
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  have hk : 1 + k = k + 1 := by
    omega
  rw [hk]
  rw [HomologicalComplex.exactAt_iff' C.toChainComplex (k + 2) (k + 1) k (by simp) (by simp)]
  simpa using quasiIso_single_exact_succ
    (R := R) (N := ResidueField R) (G := C.toChainComplex) ρ k

/-- Helper for Lemma 10.110.4: if `pd_R κ = d + 1`, then every length-`d + 1` finite free
resolution of the residue field has nonzero top term. -/
lemma top_term_nonzero_of_projectiveDimension_eq_succ
    {d : ℕ} (C : FiniteFreeComplex R (d + 1))
    (ρ : C.toChainComplex ⟶ moduleSingle[R] (ResidueField R))
    (hρ : ChainComplex.IsFiniteFreeResolution ρ)
    (hpd : projectiveDimension (ModuleCat.of R (ResidueField R)) = d + 1) :
    ¬ Limits.IsZero (C.toChainComplex.X (d + 1)) := by
  intro hzero
  have hbound' : ∀ m : ℕ, d < m → Limits.IsZero (C.toChainComplex.X m) := by
    intro m hm
    by_cases hmd : m = d + 1
    · subst hmd
      simpa using hzero
    · exact C.isZero_toChainComplex_X m (by omega)
  have hres' : HasFiniteFreeResolutionLengthLE R (ResidueField R) d :=
    ⟨C.toChainComplex, ρ, hρ, hbound'⟩
  have hle' :
      HasProjectiveDimensionLE (ModuleCat.of R (ResidueField R)) d :=
    (hasProjectiveDimensionLE_iff_hasFiniteFreeResolutionLengthLE
      (R := R) (M := ResidueField R) d).mpr hres'
  have hlt :
      HasProjectiveDimensionLT (ModuleCat.of R (ResidueField R)) (d + 1) := by
    simpa [CategoryTheory.HasProjectiveDimensionLE] using hle'
  have hnotlt :
      ¬ HasProjectiveDimensionLT (ModuleCat.of R (ResidueField R)) (d + 1) := by
    -- `pd_R κ = d + 1` rules out any shorter finite free resolution.
    rw [← CategoryTheory.projectiveDimension_ge_iff]
    simpa [hpd]
  exact hnotlt hlt

/-- Helper for Lemma 10.110.4: from `pd_R κ = d + 1`, choose a bounded finite free complex
resolving the residue field, exact in positive degrees, with nonzero top term. -/
lemma exists_residueField_finiteFreeComplex_with_nonzero_top
    {d : ℕ} (hpd : projectiveDimension (ModuleCat.of R (ResidueField R)) = d + 1) :
    ∃ (C : FiniteFreeComplex R (d + 1))
      (ρ : C.toChainComplex ⟶ moduleSingle[R] (ResidueField R)),
      ChainComplex.IsFiniteFreeResolution ρ ∧
        C.ExactInPositiveDegrees ∧
        ¬ Limits.IsZero (C.toChainComplex.X (d + 1)) := by
  -- Convert the projective-dimension value to a bounded finite free resolution.
  have hle :
      HasProjectiveDimensionLE (ModuleCat.of R (ResidueField R)) (d + 1) := by
    rw [← CategoryTheory.projectiveDimension_le_iff]
    simpa [hpd]
  have hres :
      HasFiniteFreeResolutionLengthLE R (ResidueField R) (d + 1) :=
    (hasProjectiveDimensionLE_iff_hasFiniteFreeResolutionLengthLE
      (R := R) (M := ResidueField R) (d + 1)).mp hle
  obtain ⟨F, π, hπ, hFfree, hFfinite, hbound⟩ :=
    exists_residueField_finiteFreeResolution_data (R := R) hres
  let C : FiniteFreeComplex R (d + 1) :=
    finiteFreeComplex_of_bounded_resolution (R := R) F hFfree hFfinite hbound
  let ρ : C.toChainComplex ⟶ moduleSingle[R] (ResidueField R) := by
    -- The packaged finite free complex keeps the same augmentation.
    simpa [C, finiteFreeComplex_of_bounded_resolution] using π
  have hρ : ChainComplex.IsFiniteFreeResolution ρ := by
    -- The underlying resolution witness is unchanged by the repackaging step.
    simpa [ρ, C, finiteFreeComplex_of_bounded_resolution] using hπ
  have hExact : C.ExactInPositiveDegrees :=
    exactInPositiveDegrees_of_residueField_resolution (R := R) C ρ hρ
  have htop_nonzero :
      ¬ Limits.IsZero (C.toChainComplex.X (d + 1)) :=
    top_term_nonzero_of_projectiveDimension_eq_succ (R := R) C ρ hρ hpd
  exact ⟨C, ρ, hρ, hExact, htop_nonzero⟩

/-- Helper for Lemma 10.110.4: if the top rank-minor ideal is the unit ideal, then the top
differential has a linear left inverse. -/
lemma top_differential_has_left_inverse_of_rankMinorIdeal_eq_top
    {d : ℕ} (C : FiniteFreeComplex R (d + 1))
    (hrank :
      LinearMap.exteriorRank (C.diffAt (Fin.last d)) = C.rank ⟨d + 1, by omega⟩)
    (hI : I(C.diffAt (Fin.last d)) = ⊤) :
    ∃ σ : C.term (Fin.last d).castSucc →ₗ[R] C.term (Fin.last d).succ,
      σ.comp (C.diffAt (Fin.last d)) = LinearMap.id := by
  -- Rewrite `1 ∈ I(φ_n)` as membership in the maximal-minor ideal of the top matrix.
  have hmem :
      (1 : R) ∈
        Matrix.minorIdeal (C.rank ⟨d + 1, by omega⟩)
          (LinearMap.toMatrix
            (Pi.basisFun R (Fin (C.rank (Fin.last d).succ)))
            (Pi.basisFun R (Fin (C.rank (Fin.last d).castSucc)))
            (C.diffAt (Fin.last d))) := by
    have hmemI : (1 : R) ∈ I(C.diffAt (Fin.last d)) := by
      rw [hI]
      simp
    have hmemI' :
        (1 : R) ∈
          Matrix.minorIdeal
            (LinearMap.exteriorRank (C.diffAt (Fin.last d)))
            ((LinearMap.toMatrix
              (Pi.basisFun R (Fin (C.rank (Fin.last d).succ)))
              (Pi.basisFun R (Fin (C.rank (Fin.last d).castSucc)))
              (C.diffAt (Fin.last d)))) := by
      simpa [LinearMap.rankMinorIdeal] using hmemI
    rw [← hrank]
    exact hmemI'
  obtain ⟨B, hB⟩ :=
    exists_mul_eq_smul_one_of_mem_minorIdeal
      (LinearMap.toMatrix
        (Pi.basisFun R (Fin (C.rank (Fin.last d).succ)))
        (Pi.basisFun R (Fin (C.rank (Fin.last d).castSucc)))
        (C.diffAt (Fin.last d))) hmem
  refine ⟨Matrix.toLin
    (Pi.basisFun R (Fin (C.rank (Fin.last d).castSucc)))
    (Pi.basisFun R (Fin (C.rank (Fin.last d).succ))) B, ?_⟩
  -- Convert the matrix left inverse back to a linear-map left inverse.
  apply (LinearMap.toMatrix
    (Pi.basisFun R (Fin (C.rank (Fin.last d).succ)))
    (Pi.basisFun R (Fin (C.rank (Fin.last d).succ)))).injective
  rw [LinearMap.toMatrix_comp
    (Pi.basisFun R (Fin (C.rank (Fin.last d).succ)))
    (Pi.basisFun R (Fin (C.rank (Fin.last d).castSucc)))
    (Pi.basisFun R (Fin (C.rank (Fin.last d).succ)))]
  repeat rw [LinearMap.toMatrix_toLin]
  rw [LinearMap.toMatrix_id]
  -- The minor-ideal witness already normalizes to the identity matrix.
  calc
    B *
        LinearMap.toMatrix
          (Pi.basisFun R (Fin (C.rank (Fin.last d).succ)))
          (Pi.basisFun R (Fin (C.rank (Fin.last d).castSucc)))
          (C.diffAt (Fin.last d)) =
        (1 : R) • (1 : Matrix (Fin (C.rank (Fin.last d).succ))
          (Fin (C.rank (Fin.last d).succ)) R) := hB
    _ = 1 := by
          change
            (1 : R) •
              (1 : Matrix (Fin (C.rank (Fin.last d).succ))
                (Fin (C.rank (Fin.last d).succ)) R) =
              (1 : Matrix (Fin (C.rank (Fin.last d).succ))
                (Fin (C.rank (Fin.last d).succ)) R)
          rw [one_smul]

/-- Helper for Lemma 10.110.4: in the minimal local branch, the top differential becomes zero
after quotienting by the maximal ideal. -/
lemma quotient_top_differential_eq_zero_of_entries_mem_maximal
    {d : ℕ} (C : FiniteFreeComplex R (d + 1))
    (hmax :
      ∀ a : Fin (C.rank (Fin.last d).succ), ∀ b : Fin (C.rank (Fin.last d).castSucc),
        C.diffEntry (Fin.last d) a b ∈ maximalIdeal R) :
    (C.diffAt (Fin.last d)).quotientMapByIdeal (maximalIdeal R) = 0 := by
  refine LinearMap.ext fun x ↦ ?_
  obtain ⟨y, rfl⟩ :=
    Submodule.mkQ_surjective
      (maximalIdeal R • (⊤ : Submodule R (C.term (Fin.last d).succ))) x
  -- Each coordinate of the top differential is an `R`-linear combination of maximal-ideal
  -- entries, so the image dies modulo `maximalIdeal R`.
  have hy_mem :
      C.diffAt (Fin.last d) y ∈
        maximalIdeal R • (⊤ : Submodule R (C.term (Fin.last d).castSucc)) := by
    have hcoeff :
        ∀ b : Fin (C.rank (Fin.last d).castSucc),
          (C.diffAt (Fin.last d) y) b ∈ maximalIdeal R := by
      intro b
      have hdecomp :
          y =
            ∑ a : Fin (C.rank (Fin.last d).succ),
              y a • (Pi.single a (1 : R) : C.term (Fin.last d).succ) := by
        ext a
        rw [Finset.sum_apply, Finset.sum_eq_single a]
        · change y a = y a * ((Pi.single a (1 : R) : C.term (Fin.last d).succ) a)
          simp
        · intro j _ hja
          change y j * ((Pi.single j (1 : R) : C.term (Fin.last d).succ) a) = 0
          have hsingle :
              ((Pi.single j (1 : R) : C.term (Fin.last d).succ) a) = 0 := by
            by_cases h : j = a
            · exact (hja h).elim
            · change Function.update (0 : C.term (Fin.last d).succ) j (1 : R) a = (0 : R)
              dsimp [Function.update]
              split_ifs with h'
              · exact (h h'.symm).elim
              · rfl
          rw [hsingle]
          simp
        · intro ha
          exact (ha (Finset.mem_univ a)).elim
      rw [hdecomp, map_sum, Finset.sum_apply]
      show
        ∑ a : Fin (C.rank (Fin.last d).succ),
            (C.diffAt (Fin.last d) (y a • (Pi.single a (1 : R) : C.term (Fin.last d).succ))) b ∈
          maximalIdeal R
      refine Ideal.sum_mem _ fun a _ ↦ ?_
      have hentry : C.diffEntry (Fin.last d) a b ∈ maximalIdeal R := hmax a b
      have hterm :
          (C.diffAt (Fin.last d) (y a • (Pi.single a (1 : R) : C.term (Fin.last d).succ))) b =
            y a * C.diffEntry (Fin.last d) a b := by
        have hmap :
            C.diffAt (Fin.last d) (y a • (Pi.single a (1 : R) : C.term (Fin.last d).succ)) =
              y a • C.diffAt (Fin.last d) (Pi.single a (1 : R) : C.term (Fin.last d).succ) := by
          rw [LinearMap.map_smul]
        have hentry_eq :
            (C.diffAt (Fin.last d) (Pi.single a (1 : R) : C.term (Fin.last d).succ)) b =
              C.diffEntry (Fin.last d) a b := by
          simp [FiniteFreeComplex.diffEntry]
        calc
          (C.diffAt (Fin.last d) (y a • (Pi.single a (1 : R) : C.term (Fin.last d).succ))) b =
              (y a • C.diffAt (Fin.last d) (Pi.single a (1 : R) : C.term (Fin.last d).succ)) b := by
                simpa using congrArg (fun z : C.term (Fin.last d).castSucc ↦ z b) hmap
          _ = y a * C.diffEntry (Fin.last d) a b := by
                change
                  y a * (C.diffAt (Fin.last d) (Pi.single a (1 : R) : C.term (Fin.last d).succ)) b =
                    y a * C.diffEntry (Fin.last d) a b
                rw [hentry_eq]
      have hmul_mem : C.diffEntry (Fin.last d) a b * y a ∈ maximalIdeal R :=
        Ideal.mul_mem_right (y a) (maximalIdeal R) hentry
      rw [hterm, mul_comm]
      exact hmul_mem
    have hsum :
        C.diffAt (Fin.last d) y =
          ∑ b : Fin (C.rank (Fin.last d).castSucc),
            (C.diffAt (Fin.last d) y) b •
              (Pi.single b (1 : R) : C.term (Fin.last d).castSucc) := by
      ext b
      rw [Finset.sum_apply, Finset.sum_eq_single b]
      · simp [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
      · intro j _ hjb
        simp [Pi.smul_apply, Pi.single_apply, hjb, smul_eq_mul]
      · simp
    rw [hsum]
    refine Submodule.sum_mem _ fun b _ ↦ ?_
    exact Submodule.smul_mem_smul (hcoeff b)
      (by simp : (Pi.single b (1 : R) : C.term (Fin.last d).castSucc) ∈
        (⊤ : Submodule R (C.term (Fin.last d).castSucc)))
  exact (Submodule.Quotient.mk_eq_zero _).2 <| by
    exact hy_mem

/-- Helper for Lemma 10.110.4: in a minimal residue-field resolution, the top rank-minor ideal
cannot be the unit ideal. -/
lemma top_rankMinorIdeal_ne_top_of_entries_mem_maximal
    {d : ℕ} (C : FiniteFreeComplex R (d + 1))
    (hrank :
      LinearMap.exteriorRank (C.diffAt (Fin.last d)) = C.rank ⟨d + 1, by omega⟩)
    (hmax :
      ∀ a : Fin (C.rank (Fin.last d).succ), ∀ b : Fin (C.rank (Fin.last d).castSucc),
        C.diffEntry (Fin.last d) a b ∈ maximalIdeal R)
    (htop : ¬ Limits.IsZero (C.toChainComplex.X (d + 1))) :
    I(C.diffAt (Fin.last d)) ≠ ⊤ := by
  intro hI
  obtain ⟨σ, hσ⟩ :=
    top_differential_has_left_inverse_of_rankMinorIdeal_eq_top (R := R) C hrank hI
  have hσquot :
      (σ.quotientMapByIdeal (maximalIdeal R)).comp
          ((C.diffAt (Fin.last d)).quotientMapByIdeal (maximalIdeal R)) = LinearMap.id := by
    refine DFunLike.ext _ _ fun x ↦ ?_
    obtain ⟨y, rfl⟩ :=
      Submodule.mkQ_surjective
        (maximalIdeal R • (⊤ : Submodule R (C.term (Fin.last d).succ))) x
    simpa [LinearMap.quotientMapByIdeal] using
      congrArg
        (Submodule.mkQ
          (maximalIdeal R • (⊤ : Submodule R (C.term (Fin.last d).succ))))
        (LinearMap.congr_fun hσ y)
  have hquot_zero :
      (C.diffAt (Fin.last d)).quotientMapByIdeal (maximalIdeal R) = 0 :=
    quotient_top_differential_eq_zero_of_entries_mem_maximal (R := R) C hmax
  have hid_zero :
      (LinearMap.id :
        C.term (Fin.last d).succ ⧸
          (maximalIdeal R • (⊤ : Submodule R (C.term (Fin.last d).succ))) →ₗ[R]
        C.term (Fin.last d).succ ⧸
          (maximalIdeal R • (⊤ : Submodule R (C.term (Fin.last d).succ)))) = 0 := by
    calc
      (LinearMap.id :
        C.term (Fin.last d).succ ⧸
          (maximalIdeal R • (⊤ : Submodule R (C.term (Fin.last d).succ))) →ₗ[R]
        C.term (Fin.last d).succ ⧸
          (maximalIdeal R • (⊤ : Submodule R (C.term (Fin.last d).succ)))) =
          (σ.quotientMapByIdeal (maximalIdeal R)).comp
            ((C.diffAt (Fin.last d)).quotientMapByIdeal (maximalIdeal R)) := hσquot.symm
      _ = (σ.quotientMapByIdeal (maximalIdeal R)).comp 0 := by rw [hquot_zero]
      _ = 0 := by rw [LinearMap.comp_zero]
  have htop_rank_pos : 0 < C.rank ⟨d + 1, by omega⟩ := by
    by_contra hzero
    have hrank_zero : C.rank ⟨d + 1, by omega⟩ = 0 := Nat.eq_zero_of_not_pos hzero
    have hz : Limits.IsZero (C.toChainComplex.X (d + 1)) := by
      simpa using term_isZero_of_rank_eq_zero (R := R) C ⟨d + 1, by omega⟩ hrank_zero
    exact htop hz
  let a : Fin (C.rank ⟨d + 1, by omega⟩) := ⟨0, htop_rank_pos⟩
  let v : C.term (Fin.last d).succ := Pi.single a 1
  have hv_nonzero :
      (Submodule.mkQ
        (maximalIdeal R • (⊤ : Submodule R (C.term (Fin.last d).succ))) v) ≠ 0 := by
    intro hv
    have hv_mem :
        v ∈ maximalIdeal R • (⊤ : Submodule R (C.term (Fin.last d).succ)) :=
      (Submodule.Quotient.mk_eq_zero _).1 hv
    have hone_mem : (1 : R) ∈ maximalIdeal R := by
      have hcoeff_mem : v a ∈ maximalIdeal R := by
        refine Submodule.smul_induction_on hv_mem ?_ ?_
        · intro r hr y hy
          change r * y a ∈ maximalIdeal R
          exact Ideal.mul_mem_right (y a) (maximalIdeal R) hr
        · intro y z hy hz
          exact Ideal.add_mem _ hy hz
      simpa [v, a] using hcoeff_mem
    have hone_not_mem : (1 : R) ∉ maximalIdeal R := by
      intro hone
      exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top <|
        (maximalIdeal R).eq_top_of_isUnit_mem hone (by simpa using (isUnit_one : IsUnit (1 : R)))
    exact hone_not_mem hone_mem
  have hvalue_zero :
      Submodule.mkQ
        (maximalIdeal R • (⊤ : Submodule R (C.term (Fin.last d).succ))) v = 0 := by
    simpa using LinearMap.congr_fun hid_zero
      (Submodule.mkQ
        (maximalIdeal R • (⊤ : Submodule R (C.term (Fin.last d).succ))) v)
  exact hv_nonzero hvalue_zero

-- Proof sketch: choose a finite free resolution of `ResidueField R` of length `n`, replace it by a
-- minimal one over the local ring, apply the Buchsbaum--Eisenbud criterion to the top differential
-- to obtain a regular sequence of length `n`, and then bound that length by `ringKrullDim R` using
-- the depth-dimension inequality for Noetherian local rings.
/-- Lemma 10.110.4: if the residue field of a Noetherian local ring `R` has projective dimension
`n` over `R`, then the Krull dimension of `R` is at least `n`. -/
@[stacks 00OB]
theorem projectiveDimension_residueField_le_ringKrullDim
    {n : ℕ} (hpd : projectiveDimension (ModuleCat.of R (ResidueField R)) = n) :
    n ≤ ringKrullDim R := by
  cases n with
  | zero =>
      -- The zero case is immediate.
      simpa using (ringKrullDim_nonneg_of_nontrivial (R := R))
  | succ d =>
      obtain ⟨C, ρ, hρ, _, _⟩ :=
        exists_residueField_finiteFreeComplex_with_nonzero_top (R := R) hpd
      obtain ⟨Cmin, ρmin, hρmin, hminimal⟩ :=
        exists_minimal_residueField_finiteFreeComplex (R := R) C ρ hρ
      have hExact :
          Cmin.ExactInPositiveDegrees :=
        exactInPositiveDegrees_of_residueField_resolution (R := R) Cmin ρmin hρmin
      have htop_nonzero :
          ¬ Limits.IsZero (Cmin.toChainComplex.X (d + 1)) :=
        top_term_nonzero_of_projectiveDimension_eq_succ (R := R) Cmin ρmin hρmin hpd
      let jTop : Fin (d + 2) := ⟨d + 1, by omega⟩
      have hcriterion :=
        (FiniteFreeComplex.exactInPositiveDegrees_iff_buchsbaumEisenbud_criterion
          (R := R) (C := Cmin)).mp hExact (Fin.last d)
      rcases hcriterion with ⟨hrank, htop⟩
      have hrank_top :
          LinearMap.exteriorRank (Cmin.diffAt (Fin.last d)) = Cmin.rank jTop := by
        have hEqInt :
            (LinearMap.exteriorRank (Cmin.diffAt (Fin.last d)) : ℤ) = Cmin.rank jTop := by
          calc
            (LinearMap.exteriorRank (Cmin.diffAt (Fin.last d)) : ℤ) =
                Cmin.alternatingRank (Fin.last d) := hrank
            _ = Cmin.rank jTop := by
                simpa [jTop] using alternatingRank_last_eq_rank_top (R := R) Cmin
        exact Int.ofNat.inj hEqInt
      rcases htop with hI | ⟨rs, hreg, _, hlen⟩
      · -- Route correction: use minimality modulo `maximalIdeal R`, not split shortening.
        exact False.elim <| (top_rankMinorIdeal_ne_top_of_entries_mem_maximal
          (R := R) Cmin hrank_top (hminimal (Fin.last d)) htop_nonzero) hI
      · -- The regular-sequence branch is exactly the source conclusion.
        have hlen_le : rs.length ≤ ringKrullDim R :=
          length_le_ringKrullDim_of_isRegular (R := R) hreg
        simpa [hlen] using hlen_le

-- Proof sketch: unpack `projectiveDimension ≠ ⊤` into the finite-value case for the residue field
-- and then apply the source-facing theorem above.
/-- Bridge/view: if the residue field of a Noetherian local ring has finite projective dimension,
then that projective dimension is bounded above by the Krull dimension of the ring. -/
theorem projectiveDimension_residueField_le_ringKrullDim_of_ne_top
    (hpd : projectiveDimension (ModuleCat.of R (ResidueField R)) ≠ ⊤) :
    projectiveDimension (ModuleCat.of R (ResidueField R)) ≤ ringKrullDim R := by
  obtain ⟨n, hn⟩ := projectiveDimension_residueField_eq_nat_of_ne_top (R := R) hpd
  -- Once the projective dimension is a natural number, the source-facing theorem applies.
  rw [hn]
  exact projectiveDimension_residueField_le_ringKrullDim (R := R) hn

end
