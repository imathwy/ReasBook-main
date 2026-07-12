import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_8_1
import ConvexAnalysis_Rockafellar_1970.Chap02.Corollary_8_3_3
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_8_4

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u v w

open Bornology
open scoped Pointwise

variable {ι : Type v}
variable {𝕜 : Type w} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜] [NormSMulClass ℤ 𝕜] [Archimedean 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [ProperSpace E]

/-!
Source/core/bridge triage:

- `source-facing`: Text 21.3.3 characterizes when a family of nonempty closed convex subsets of a
  proper normed `𝕜`-space with the finite intersection property has trivial common
  recession cone. The source's `R^n` model is not mathematically essential here, because the
  chapter owner theorems already live at the intrinsic proper-space ambient layer.
- `core/canonical`: the owner objects already present in the project are the recession cone
  `0⁺[𝕜]`, arbitrary intersections `⋂ i, ...`, `Finset`-indexed finite-subfamily
  intersections `⋂ i : J, ...`, and bornological boundedness `IsBounded`.
- `bridge/view`: clause (b) is kept source-facing as existence of a finite subfamily, indexed by a
  `Finset ι`, whose intersection is bounded; its nonemptiness stays in the hypotheses through the
  `Finset`-indexed finite intersection property. The “in particular” sentence becomes a separate
  consequence saying that one bounded nonempty member forces the common recession cone to be
  trivial.

Domain-style sampling used here:
- `0⁺[𝕜]`;
- `recessionCone_iInter_eq_iInter_recessionCone`;
- `Convex.isBounded_iff_recessionCone_eq_singleton_zero`;
- the bornological owner predicate `IsBounded`.

Primitive data vs derived API:
- primitive inputs: the indexed family `C : ι → Set E`, closedness and convexity of each member,
  the `Finset`-indexed finite intersection property, and in the second clause the existence of one
  bounded nonempty member;
- derived outputs: the equivalence between trivial common recession cone and a bounded finite
  intersection, and the bounded-member corollary.

Layer target: `source-facing`, stated directly with the chapter owner `0⁺[𝕜]` rather than through
an auxiliary wrapper around recession directions.
-/

omit [NormedAddCommGroup E] [NormedSpace 𝕜 E] in
private theorem finite_iInter_nonempty (C : ι → Set E)
    (hFIP : ∀ J : Finset ι, (⋂ i : J, C i).Nonempty) (J : Finset ι) :
    (⋂ i : J, C i).Nonempty := by
  exact hFIP J

omit [NormedSpace 𝕜 E] [ProperSpace E] in
private theorem finite_iInter_closed (C : ι → Set E)
    (hC_closed : ∀ i, IsClosed (C i)) (J : Finset ι) :
    IsClosed (⋂ i : J, C i) := by
  simpa using isClosed_iInter fun i : J ↦ hC_closed i

omit [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜] [NormSMulClass ℤ 𝕜] [Archimedean 𝕜]
    [ProperSpace E] in
private theorem finite_iInter_convex (C : ι → Set E)
    (hC_convex : ∀ i, Convex 𝕜 (C i)) (J : Finset ι) :
    Convex 𝕜 (⋂ i : J, C i) := by
  simpa using convex_iInter fun i : J ↦ hC_convex i

omit [NormSMulClass ℤ 𝕜] [Archimedean 𝕜] [ProperSpace E] in
private theorem recessionCone_finite_iInter_eq_iInter_recessionCone
    (C : ι → Set E) (hC_closed : ∀ i, IsClosed (C i)) (hC_convex : ∀ i, Convex 𝕜 (C i))
    (hFIP : ∀ J : Finset ι, (⋂ i : J, C i).Nonempty) (J : Finset ι) :
    0⁺[𝕜] (⋂ i : J, C i) = ⋂ i : J, 0⁺[𝕜] (C i) := by
  simpa using
    Convex.recessionCone_iInter_eq_iInter_recessionCone
      (fun i : J ↦ hC_convex i)
      (fun i : J ↦ hC_closed i)
      (finite_iInter_nonempty C hFIP J)

-- Internal subset-to-singleton bridge used to derive the canonical singleton-equality statement.
-- Proof sketch: for `(b) → (a)`, the `Finset`-indexed finite intersection property gives the
-- needed nonemptiness of the bounded finite intersection. Apply Theorem 8.4 to that
-- subintersection and use Corollary 8.3.3 to identify its recession cone with the intersection of
-- the corresponding finite family of recession cones; then the full intersection is a subset of
-- that singleton. For `(a) → (b)`, argue by contradiction: if every finite intersection were
-- unbounded, the finite intersection property would make each one nonempty, so Theorem 8.4 gives
-- a nonzero recession direction for each. Rescale each by `ℕ`-scalars into a fixed compact
-- annulus, apply the finite intersection property there, and obtain a nonzero vector lying in
-- every `0⁺[𝕜] (C i)`, contradicting `(a)`.
private theorem iInter_recessionCone_subset_singleton_zero_iff_exists_finite_bounded_iInter
    (C : ι → Set E) (hC_closed : ∀ i, IsClosed (C i)) (hC_convex : ∀ i, Convex 𝕜 (C i))
    (hFIP : ∀ J : Finset ι, (⋂ i : J, C i).Nonempty) :
    (⋂ i, 0⁺[𝕜] (C i)) ⊆ ({0} : Set E) ↔
      ∃ J : Finset ι, IsBounded (⋂ i : J, C i) :=
  by
  constructor
  · intro hcommon
    by_contra hbounded
    let A : Set E := Metric.closedBall (0 : E) 2 ∩ (Metric.ball (0 : E) 1)ᶜ
    have h_unbounded : ∀ J : Finset ι, ¬ IsBounded (⋂ i : J, C i) := by
      simpa using hbounded
    have hfinite :
        ∀ J : Finset ι,
          (A ∩ ⋂ i ∈ J, 0⁺[𝕜] (C i)).Nonempty := by
      intro J
      let SJ : Set E := ⋂ i : J, C i
      have hSJ_nonempty : SJ.Nonempty := by
        simpa [SJ] using finite_iInter_nonempty C hFIP J
      have hSJ_closed : IsClosed SJ := by
        simpa [SJ] using finite_iInter_closed C hC_closed J
      have hSJ_convex : Convex 𝕜 SJ := by
        simpa [SJ] using finite_iInter_convex C hC_convex J
      have hSJ_not_singleton : 0⁺[𝕜] SJ ≠ ({0} : Set E) := by
        intro hSJ_singleton
        exact h_unbounded J <|
          (hSJ_convex.isBounded_iff_recessionCone_eq_singleton_zero hSJ_closed hSJ_nonempty).2
            hSJ_singleton
      have hy_exists : ∃ y : E, y ≠ 0 ∧ y ∈ 0⁺[𝕜] SJ := by
        by_contra hy_exists
        have h_all_zero : ∀ y : E, y ∈ 0⁺[𝕜] SJ → y = 0 := by
          intro y hy
          by_contra hy_ne
          exact hy_exists ⟨y, hy_ne, hy⟩
        have hSJ_singleton : 0⁺[𝕜] SJ = ({0} : Set E) := by
          exact Set.eq_singleton_iff_unique_mem.mpr
            ⟨zero_mem_recessionCone (R := 𝕜) SJ, h_all_zero⟩
        exact hSJ_not_singleton hSJ_singleton
      rcases hy_exists with ⟨y, hy_ne, hy_recession⟩
      have hy_norm_pos : 0 < ‖y‖ := norm_pos_iff.mpr hy_ne
      obtain ⟨n, hn⟩ := exists_nat_gt ‖y‖
      have hn_ne_zero : n ≠ 0 := by
        intro hn_zero
        have : ‖y‖ < 0 := by simpa [hn_zero] using hn
        exact (not_lt_of_ge (le_of_lt hy_norm_pos)) this
      have hn_pos : 0 < n := Nat.pos_of_ne_zero hn_ne_zero
      let y' : E := (n : 𝕜)⁻¹ • y
      have hy'_recession : y' ∈ 0⁺[𝕜] SJ := by
        rw [Set.mem_recessionCone_iff] at hy_recession ⊢
        intro x hx a ha
        have := hy_recession x hx (a * (n : 𝕜)⁻¹) <|
          mul_nonneg ha (inv_nonneg.mpr (Nat.cast_nonneg n))
        simpa [y', smul_smul, mul_assoc, mul_left_comm, mul_comm] using this
      have hy'_norm_lt_one : ‖y'‖ < 1 := by
        have hn_real_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos
        calc
          ‖y'‖ = ‖y‖ / (n : ℝ) := by
            simp [y', norm_smul, norm_inv, norm_natCast, inv_mul_eq_div]
          _ < 1 := (div_lt_one hn_real_pos).2 hn
      have hy'_ne : y' ≠ 0 := by
        exact smul_ne_zero (inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn_pos))) hy_ne
      have hy'_norm_pos : 0 < ‖y'‖ := norm_pos_iff.mpr hy'_ne
      have hP_exists : ∃ m : ℕ, 1 ≤ ‖((m : ℕ) : 𝕜) • y'‖ := by
        obtain ⟨m, hm⟩ := exists_nat_gt (‖y'‖⁻¹)
        refine ⟨m, le_of_lt ?_⟩
        have hm' : 1 < (m : ℝ) * ‖y'‖ := by
          have hm_mul := mul_lt_mul_of_pos_right hm hy'_norm_pos
          simpa [inv_mul_cancel₀ (ne_of_gt hy'_norm_pos), mul_comm, mul_left_comm, mul_assoc] using
            hm_mul
        calc
          1 < (m : ℝ) * ‖y'‖ := hm'
          _ = ‖((m : ℕ) : 𝕜)‖ * ‖y'‖ := by simp [norm_natCast]
          _ = ‖((m : ℕ) : 𝕜) • y'‖ := by simp [norm_smul]
      let m : ℕ := Nat.find hP_exists
      have hm : 1 ≤ ‖((m : ℕ) : 𝕜) • y'‖ := Nat.find_spec hP_exists
      have hm_ne_zero : m ≠ 0 := by
        intro hm_zero
        have : (1 : ℝ) ≤ 0 := by simpa [hm_zero] using hm
        exact not_le_of_gt zero_lt_one this
      have hpred_not : ¬ 1 ≤ ‖((Nat.pred m : ℕ) : 𝕜) • y'‖ := by
        exact Nat.find_min hP_exists (Nat.pred_lt hm_ne_zero)
      have hpred_norm_lt_one : ‖((Nat.pred m : ℕ) : 𝕜) • y'‖ < 1 := lt_of_not_ge hpred_not
      have hm_pos : 0 < m := Nat.pos_of_ne_zero hm_ne_zero
      let z : E := ((m : ℕ) : 𝕜) • y'
      have hz_eq : z = ((Nat.pred m : ℕ) : 𝕜) • y' + y' := by
        dsimp [z]
        calc
          ((m : ℕ) : 𝕜) • y' = (((Nat.pred m + 1 : ℕ) : 𝕜) • y') := by
            rw [← Nat.succ_eq_add_one, Nat.succ_pred_eq_of_pos hm_pos]
          _ = ((((Nat.pred m : ℕ) : 𝕜) + 1) • y') := by
                simp [Nat.cast_add]
          _ = ((Nat.pred m : ℕ) : 𝕜) • y' + y' := by simp [add_smul]
      have hz_norm_lt_two : ‖z‖ < 2 := by
        calc
          ‖z‖ = ‖((Nat.pred m : ℕ) : 𝕜) • y' + y'‖ := by rw [hz_eq]
          _ ≤ ‖((Nat.pred m : ℕ) : 𝕜) • y'‖ + ‖y'‖ := norm_add_le _ _
          _ < 1 + 1 := add_lt_add hpred_norm_lt_one hy'_norm_lt_one
          _ = 2 := by norm_num
      have hz_recession : z ∈ 0⁺[𝕜] SJ := by
        rw [Set.mem_recessionCone_iff] at hy'_recession ⊢
        intro x hx a ha
        have := hy'_recession x hx (a * (m : 𝕜)) (mul_nonneg ha (Nat.cast_nonneg m))
        simpa [z, smul_smul, mul_assoc, mul_left_comm, mul_comm] using this
      have hSJ_recession :
          0⁺[𝕜] SJ = ⋂ i : J, 0⁺[𝕜] (C i) := by
        simpa [SJ] using
          recessionCone_finite_iInter_eq_iInter_recessionCone C hC_closed hC_convex hFIP J
      have hz_common : z ∈ ⋂ i ∈ J, 0⁺[𝕜] (C i) := by
        have hz_common_subtype : z ∈ ⋂ i : J, 0⁺[𝕜] (C i) := by
          simpa [hSJ_recession] using hz_recession
        simpa using hz_common_subtype
      have hz_not_ball : z ∉ Metric.ball (0 : E) 1 := by
        intro hz_ball
        have hz_norm_lt_one : ‖z‖ < 1 := by
          simpa [Metric.mem_ball, dist_eq_norm] using hz_ball
        have hz_norm_ge_one : 1 ≤ ‖z‖ := by simpa [z] using hm
        exact not_lt_of_ge hz_norm_ge_one hz_norm_lt_one
      have hz_in_A : z ∈ A := by
        refine ⟨?_, hz_not_ball⟩
        rw [Metric.mem_closedBall]
        simpa [dist_eq_norm] using (le_of_lt hz_norm_lt_two : ‖z‖ ≤ 2)
      exact ⟨z, hz_in_A, hz_common⟩
    have hcone_closed : ∀ i, IsClosed (0⁺[𝕜] (C i)) := by
      intro i
      exact (hC_convex i).isClosed_recessionCone (hC_closed i)
    have hA_compact : IsCompact A := by
      refine (isCompact_closedBall (0 : E) 2).inter_right ?_
      exact isClosed_compl_iff.mpr Metric.isOpen_ball
    obtain ⟨z, hzA, hz_common⟩ :=
      hA_compact.inter_iInter_nonempty
        (fun i ↦ 0⁺[𝕜] (C i))
        hcone_closed
        hfinite
    have hz_zero : z = 0 := Set.mem_singleton_iff.mp (hcommon hz_common)
    have hz_not_ball : z ∉ Metric.ball (0 : E) 1 := hzA.2
    have hzero_ball : (0 : E) ∈ Metric.ball (0 : E) 1 := by
      simp [Metric.mem_ball]
    exact hz_not_ball (hz_zero ▸ hzero_ball)
  · rintro ⟨J, hJ_bounded⟩
    intro y hy
    let SJ : Set E := ⋂ i : J, C i
    have hSJ_nonempty : SJ.Nonempty := by
      simpa [SJ] using finite_iInter_nonempty C hFIP J
    have hSJ_closed : IsClosed SJ := by
      simpa [SJ] using finite_iInter_closed C hC_closed J
    have hSJ_convex : Convex 𝕜 SJ := by
      simpa [SJ] using finite_iInter_convex C hC_convex J
    have hSJ_recession :
        0⁺[𝕜] SJ = ⋂ i : J, 0⁺[𝕜] (C i) := by
      simpa [SJ] using
        recessionCone_finite_iInter_eq_iInter_recessionCone C hC_closed hC_convex hFIP J
    have hSJ_singleton : 0⁺[𝕜] SJ = ({0} : Set E) :=
      (hSJ_convex.isBounded_iff_recessionCone_eq_singleton_zero hSJ_closed hSJ_nonempty).mp
        hJ_bounded
    have hySJ : y ∈ 0⁺[𝕜] SJ := by
      have hyJ : y ∈ ⋂ i : J, 0⁺[𝕜] (C i) := by
        exact Set.mem_iInter.mpr fun i ↦ Set.mem_iInter.mp hy i
      simpa [hSJ_recession] using hyJ
    rw [hSJ_singleton] at hySJ
    simpa using hySJ

/-- Canonical owner form of Text 21.3.3: for a family of closed convex subsets of a proper normed
`𝕜`-space with the finite intersection property, triviality of the common recession cone is
equivalent to boundedness of some finite subintersection. -/
theorem iInter_recessionCone_eq_singleton_zero_iff_exists_finite_bounded_iInter
    (C : ι → Set E) (hC_closed : ∀ i, IsClosed (C i)) (hC_convex : ∀ i, Convex 𝕜 (C i))
    (hFIP : ∀ J : Finset ι, (⋂ i : J, C i).Nonempty) :
    (⋂ i, 0⁺[𝕜] (C i)) = ({0} : Set E) ↔
      ∃ J : Finset ι, IsBounded (⋂ i : J, C i) := by
  have hcommon_nonempty : (⋂ i, 0⁺[𝕜] (C i)).Nonempty := by
    refine ⟨0, Set.mem_iInter.mpr ?_⟩
    intro i
    simpa using (show (0 : E) ∈ 0⁺[𝕜] (C i) from zero_mem_recessionCone (R := 𝕜) (C i))
  exact (hcommon_nonempty.subset_singleton_iff).symm.trans
    (iInter_recessionCone_subset_singleton_zero_iff_exists_finite_bounded_iInter
      (C := C) hC_closed hC_convex hFIP)

end

section

universe u v w

open Bornology
open scoped Pointwise

variable {ι : Type u}
variable {K : Type v} [NormedField K] [LinearOrder K] [IsStrictOrderedRing K]
variable [NormSMulClass ℤ K]
variable {E : Type w} [NormedAddCommGroup E] [Module K E] [NormSMulClass K E]

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem not_isBounded_range_add_natCast_smul (x y : E) (hy : y ≠ 0) :
    ¬ IsBounded (Set.range fun n : ℕ ↦ x + (n : K) • y) := by
  intro hbounded
  obtain ⟨R, hR⟩ := hbounded.subset_closedBall (0 : E)
  have hy_norm : 0 < ‖y‖ := norm_pos_iff.mpr hy
  obtain ⟨n, hn⟩ := exists_nat_gt ((R + ‖x‖) / ‖y‖)
  have hnorm : ‖x + (n : K) • y‖ ≤ R := by
    have hxR : x + (n : K) • y ∈ Metric.closedBall (0 : E) R := hR ⟨n, rfl⟩
    simpa [Metric.mem_closedBall, dist_eq_norm] using hxR
  have hny : ‖(n : K)‖ * ‖y‖ ≤ R + ‖x‖ := by
    calc
      ‖(n : K)‖ * ‖y‖ = ‖(n : K) • y‖ := by
        simpa using (norm_smul (n : K) y).symm
      _ = ‖(x + (n : K) • y) - x‖ := by simp
      _ ≤ ‖x + (n : K) • y‖ + ‖x‖ := norm_sub_le _ _
      _ ≤ R + ‖x‖ := add_le_add hnorm le_rfl
  have hgt' : R + ‖x‖ < (n : ℝ) * ‖y‖ := (div_lt_iff₀ hy_norm).mp hn
  have hgt : R + ‖x‖ < ‖(n : K)‖ * ‖y‖ := by
    calc
      R + ‖x‖ < (n : ℝ) * ‖y‖ := hgt'
      _ = ‖(n : K)‖ * ‖y‖ := by simp [norm_natCast]
  exact not_lt_of_ge hny hgt

private theorem recessionCone_subset_singleton_zero_of_nonempty_isBounded (C : Set E)
    (hC_nonempty : C.Nonempty) (hC_bounded : IsBounded C) :
    0⁺[K] C ⊆ ({0} : Set E) := by
  obtain ⟨x, hx⟩ := hC_nonempty
  intro y hy
  by_contra hy_ne
  have hrange_subset : Set.range (fun n : ℕ ↦ x + (n : K) • y) ⊆ C := by
    rintro _ ⟨n, rfl⟩
    exact (Set.mem_recessionCone_iff.mp hy) x hx (n : K) (Nat.cast_nonneg n)
  exact not_isBounded_range_add_natCast_smul x y hy_ne (hC_bounded.subset hrange_subset)

/-- Canonical owner form: a bounded nonempty subset of a normed `K`-module has trivial
`K`-recession cone. -/
theorem recessionCone_eq_singleton_zero_of_nonempty_isBounded (C : Set E)
    (hC_nonempty : C.Nonempty) (hC_bounded : IsBounded C) :
    0⁺[K] C = ({0} : Set E) := by
  have hcone_nonempty : (0⁺[K] C).Nonempty := by
    refine ⟨0, ?_⟩
    simpa using (show (0 : E) ∈ 0⁺[K] C from zero_mem_recessionCone (R := K) C)
  exact (hcone_nonempty.subset_singleton_iff).mp
    (recessionCone_subset_singleton_zero_of_nonempty_isBounded
      (C := C) hC_nonempty hC_bounded)

private theorem
    iInter_recessionCone_subset_singleton_zero_of_exists_finite_nonempty_isBounded_iInter
    (C : ι → Set E)
    (h_bounded_finite_iInter :
      ∃ J : Finset ι, (⋂ i : J, C i).Nonempty ∧ IsBounded (⋂ i : J, C i)) :
    (⋂ i, 0⁺[K] (C i)) ⊆ ({0} : Set E) := by
  rcases h_bounded_finite_iInter with ⟨J, hJ_nonempty, hJ_bounded⟩
  have hJ_recession :
      0⁺[K] (⋂ i : J, C i) ⊆ ({0} : Set E) :=
    recessionCone_subset_singleton_zero_of_nonempty_isBounded
      (C := ⋂ i : J, C i) hJ_nonempty hJ_bounded
  intro y hy
  have hyJ : y ∈ 0⁺[K] (⋂ i : J, C i) := by
    rw [Set.mem_recessionCone_iff]
    intro x hx a ha
    exact Set.mem_iInter.mpr fun i : J ↦
      (Set.mem_recessionCone_iff.mp (Set.mem_iInter.mp hy i)) x (Set.mem_iInter.mp hx i) a ha
  exact hJ_recession hyJ

/-- Canonical owner form: if a finite subintersection of a family is bounded and nonempty, then
the family has trivial common `K`-recession cone. -/
theorem iInter_recessionCone_eq_singleton_zero_of_exists_finite_nonempty_isBounded_iInter
    (C : ι → Set E)
    (h_bounded_finite_iInter :
      ∃ J : Finset ι, (⋂ i : J, C i).Nonempty ∧ IsBounded (⋂ i : J, C i)) :
    (⋂ i, 0⁺[K] (C i)) = ({0} : Set E) := by
  have hcommon_nonempty : (⋂ i, 0⁺[K] (C i)).Nonempty := by
    refine ⟨0, Set.mem_iInter.mpr ?_⟩
    intro i
    simpa using (show (0 : E) ∈ 0⁺[K] (C i) from zero_mem_recessionCone (R := K) (C i))
  exact (hcommon_nonempty.subset_singleton_iff).mp
    (iInter_recessionCone_subset_singleton_zero_of_exists_finite_nonempty_isBounded_iInter
      C h_bounded_finite_iInter)

private theorem iInter_recessionCone_subset_singleton_zero_of_exists_finite_isBounded_iInter
    (C : ι → Set E)
    (hFIP : ∀ J : Finset ι, (⋂ i : J, C i).Nonempty)
    (h_bounded_finite_iInter : ∃ J : Finset ι, IsBounded (⋂ i : J, C i)) :
    (⋂ i, 0⁺[K] (C i)) ⊆ ({0} : Set E) := by
  rcases h_bounded_finite_iInter with ⟨J, hJ_bounded⟩
  exact iInter_recessionCone_subset_singleton_zero_of_exists_finite_nonempty_isBounded_iInter
    C ⟨J, hFIP J, hJ_bounded⟩

/-- Canonical owner form: if the family has the finite intersection property and one finite
subintersection is bounded, then the family has trivial common `K`-recession cone. -/
theorem iInter_recessionCone_eq_singleton_zero_of_exists_finite_isBounded_iInter
    (C : ι → Set E)
    (hFIP : ∀ J : Finset ι, (⋂ i : J, C i).Nonempty)
    (h_bounded_finite_iInter : ∃ J : Finset ι, IsBounded (⋂ i : J, C i)) :
    (⋂ i, 0⁺[K] (C i)) = ({0} : Set E) := by
  have hcommon_nonempty : (⋂ i, 0⁺[K] (C i)).Nonempty := by
    refine ⟨0, Set.mem_iInter.mpr ?_⟩
    intro i
    simpa using (show (0 : E) ∈ 0⁺[K] (C i) from zero_mem_recessionCone (R := K) (C i))
  exact (hcommon_nonempty.subset_singleton_iff).mp
    (iInter_recessionCone_subset_singleton_zero_of_exists_finite_isBounded_iInter
      C hFIP h_bounded_finite_iInter)

private theorem iInter_recessionCone_subset_singleton_zero_of_exists_nonempty_isBounded
    (C : ι → Set E)
    (h_bounded_member : ∃ i, (C i).Nonempty ∧ IsBounded (C i)) :
    (⋂ i, 0⁺[K] (C i)) ⊆ ({0} : Set E) := by
  rcases h_bounded_member with ⟨i, hCi_nonempty, hCi_bounded⟩
  have h_singleton_iInter_eq : (⋂ j : ({i} : Finset ι), C j) = C i := by
    ext x
    constructor
    · intro hx
      exact Set.mem_iInter.mp hx ⟨i, by simp⟩
    · intro hx
      exact Set.mem_iInter.mpr fun j ↦ by
        have hj : (j : ι) = i := Finset.mem_singleton.mp j.2
        simpa [hj] using hx
  have h_singleton_nonempty : (⋂ j : ({i} : Finset ι), C j).Nonempty := by
    simpa [h_singleton_iInter_eq] using hCi_nonempty
  have h_singleton_bounded : IsBounded (⋂ j : ({i} : Finset ι), C j) := by
    simpa [h_singleton_iInter_eq] using hCi_bounded
  exact iInter_recessionCone_subset_singleton_zero_of_exists_finite_nonempty_isBounded_iInter
    C ⟨{i}, h_singleton_nonempty, h_singleton_bounded⟩

/-- Canonical owner form: if one member of a family is bounded and nonempty, then the family has
trivial common `K`-recession cone. -/
theorem iInter_recessionCone_eq_singleton_zero_of_exists_nonempty_isBounded
    (C : ι → Set E)
    (h_bounded_member : ∃ i, (C i).Nonempty ∧ IsBounded (C i)) :
    (⋂ i, 0⁺[K] (C i)) = ({0} : Set E) := by
  have hcommon_nonempty : (⋂ i, 0⁺[K] (C i)).Nonempty := by
    refine ⟨0, Set.mem_iInter.mpr ?_⟩
    intro i
    simpa using (show (0 : E) ∈ 0⁺[K] (C i) from zero_mem_recessionCone (R := K) (C i))
  exact (hcommon_nonempty.subset_singleton_iff).mp
    (iInter_recessionCone_subset_singleton_zero_of_exists_nonempty_isBounded
      C h_bounded_member)

end
