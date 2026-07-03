import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_21_3_1 (from Chap04) -/
open scoped Rockafellar
open Set

section

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {I : Type v}
variable {C : Set E}
variable (f : I → E → EReal)
variable (hf : ∀ i : I, Function.IsClosedProperConvex (𝕜 := ℝ) (f i))
variable (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
variable (hno_common :
  ¬ ∃ y : E, Set.RecedesInDirection ℝ C y ∧
    ∀ i : I, y ∈ Function.recessionCone ((f i)₀⁺))

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 21.3.1 says that an arbitrary family of closed proper convex
  inequalities on a closed convex set `C` has a common nonpositive point whenever every finite
  subsystem of size at most `dim E + 1` is strictly feasible at every positive level and there is
  no common recession direction for the family inside `C`.
- `core/canonical`: the chapter owner abstraction is the source-facing alternative
  `xor_exists_nonpositive_point_or_finitely_supported_nonnegative_multiplier_certificate` from
  `Theorem_21_3`, together with the support-bounded multiplier refinement
  `exists_finitely_supported_nonnegative_multiplier_certificate_with_support_card_le`.
- `bridge/view`: the only extra work in this corollary is to show that the multiplier branch of
  the Chapter 21 alternative is impossible under the small-subsystem strict-feasibility
  hypothesis; that contradiction is exposed as a companion theorem, while the main corollary stays
  in the textbook pointwise language.

Domain-style sampling used here:
- `xor_exists_nonpositive_point_or_finitely_supported_nonnegative_multiplier_certificate`;
- `exists_finitely_supported_nonnegative_multiplier_certificate_with_support_card_le`.

Primitive data vs derived API:
- primitive inputs: the family `f`, the owner hypothesis `∀ i, (f i).IsClosedProperConvex`, the
  closed convex set `C`, the direct no-common-recession hypothesis, and strict finite-subsystem
  feasibility;
- derived companion owner output: impossibility of a finitely supported nonnegative multiplier
  certificate on `C`;
- derived public output: a point `x ∈ C` with `f i x ≤ 0` for every `i`, obtained directly from
  the source-facing Chapter 21 alternative.

Layer target:
- `source-facing` for `exists_point_of_small_subsystems_strictly_feasible`, with the owner
  certificate-elimination step exposed as a reusable companion theorem.
-/

include f hf hC_closed hC_convex hno_common

theorem no_nonnegative_multiplier_certificate_of_small_subsystems_strictly_feasible
    (h_small_feasible :
      ∀ (J : Finset I) (_ : J.card ≤ Module.finrank ℝ E + 1) (ε : ℝ) (_ : 0 < ε),
        ∃ x : E, x ∈ C ∧ ∀ i ∈ J, f i x < ε)
    :
    ¬ ∃ weights : I →₀ ℝ, ∃ epsilon : ℝ,
      weights.IsNonnegativeMultiplierCertificateOn C f epsilon := by
  intro hcert
  rcases
      exists_finitely_supported_nonnegative_multiplier_certificate_with_support_card_le
        f hf hC_closed hC_convex hno_common hcert with
    ⟨weights, epsilon, hcard, hcertificate⟩
  rcases hcertificate with ⟨hweights_nonneg, hepsilon_pos, hcertificate_on_C⟩
  -- Choose a point that strictly satisfies the support subsystem at a sufficiently small positive
  -- level relative to the total multiplier mass. Evaluating the certificate there yields
  -- `epsilon < epsilon`, a contradiction.
  sorry

/-- Corollary 21.3.1: let `fᵢ`, `i ∈ I`, be closed proper convex functions on a finite-dimensional
real normed space, and let `C` be a closed convex set. If there is no common recession direction
for the family that is also a recession direction of `C`, and if for every `ε > 0` every finite
subsystem with at most `Module.finrank ℝ E + 1` inequalities `fᵢ(x) < ε` has a solution in `C`,
then there exists `x ∈ C` such that `fᵢ x ≤ 0` for every `i`. Specializing
`E = EuclideanSpace ℝ (Fin n)` recovers the textbook `R^n` statement with the bound `n + 1`. -/
theorem exists_point_of_small_subsystems_strictly_feasible
    (h_small_feasible :
      ∀ (J : Finset I) (_ : J.card ≤ Module.finrank ℝ E + 1) (ε : ℝ) (_ : 0 < ε),
        ∃ x : E, x ∈ C ∧ ∀ i ∈ J, f i x < ε)
    :
    ∃ x : E, x ∈ C ∧ ∀ i : I, f i x ≤ 0 := by
  have hxor :
      Xor'
        (∃ x : E, x ∈ C ∧ ∀ i : I, f i x ≤ 0)
        (∃ weights : I →₀ ℝ, ∃ epsilon : ℝ,
          weights.IsNonnegativeMultiplierCertificateOn C f epsilon) :=
    xor_exists_nonpositive_point_or_finitely_supported_nonnegative_multiplier_certificate
      f hf hC_closed hC_convex hno_common
  rcases hxor.or with hpoint | hcert
  · exact hpoint
  · exact False.elim <|
      (no_nonnegative_multiplier_certificate_of_small_subsystems_strictly_feasible
        f hf hC_closed hC_convex hno_common h_small_feasible) hcert

omit f hf hC_closed hC_convex hno_common

end

/-! ### Corollary_21_3_2_Helly_s_Theorem (from Chap04) -/
section

universe u v

open Set
open scoped Rockafellar

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {I : Type v}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 21.3.2 is Helly's theorem for an arbitrary family of closed convex
  sets, assuming that every subfamily with at most `Module.finrank ℝ E + 1` members intersects and
  that the family has no common nonzero recession direction.
- `core/canonical`: the owner abstraction is the Chapter 21 source-facing inequality corollary
  `exists_point_of_small_subsystems_strictly_feasible`, together with the project bridge theorems
  `indicatorFunction_isClosedProperConvex_of_nonempty` and
  `functionRecessionCone_indicatorFunction_eq_recessionCone`.
- `bridge/view`: the source family of sets is passed to the Chapter 21 owner theorem through the
  canonical indicator family `fun i ↦ δ(· | C i)`. The common-recession hypothesis is
  transferred through the canonical bridge
  `functionRecessionCone_indicatorFunction_eq_recessionCone`, while closed/proper/convexity of the
  indicator family comes from `indicatorFunction_isClosedProperConvex_of_nonempty`.

Domain-style sampling used here:
- `exists_point_of_small_subsystems_strictly_feasible`;
- `indicatorFunction_isClosedProperConvex_of_nonempty`;
- `functionRecessionCone_indicatorFunction_eq_recessionCone`;
- `indicatorFunction` with source-facing notation `δ(· | ·)`.

Primitive data vs derived API:
- primitive inputs: the family `C`, closedness and convexity of each member, the triviality of the
  common recession cone, and nonemptiness of every finite subintersection of size at most
  `Module.finrank ℝ E + 1`;
- derived output: nonemptiness of the total intersection.

Layer target: `source-facing`, stated directly for the family of sets as a thin bridge to the
Chapter 21 owner theorem rather than via a parallel local recession-direction package or a
duplicate local Helly alternative.
-/

-- Proof sketch: apply `exists_point_of_small_subsystems_strictly_feasible` to the indicator family
-- `fun i ↦ δ(· | C i)` on ambient set `univ`. For a closed convex set, the
-- indicator is a closed proper convex function by
-- `indicatorFunction_isClosedProperConvex_of_nonempty`, its function recession cone is
-- `0⁺[ℝ] (C i)`
-- by `functionRecessionCone_indicatorFunction_eq_recessionCone`, and strict feasibility of a
-- finite subsystem at any level `ε > 0` is exactly nonemptiness of the corresponding finite
-- intersection. The resulting joint nonpositive point is therefore a point of `⋂ i, C i`.

/-- Corollary 21.3.2 (Helly's Theorem): let `(C i)_{i ∈ I}` be a family of closed convex sets in a
finite-dimensional real normed space. If the common recession cone `⋂ i, 0⁺[ℝ] (C i)` is trivial and
every subcollection of at most `Module.finrank ℝ E + 1` sets has nonempty intersection, then the
whole family has nonempty intersection. Specializing to `E = EuclideanSpace ℝ (Fin n)` recovers
the textbook `R^n` bound `n + 1`. -/
theorem helly_theorem_of_trivial_common_recessionCone
    (C : I → Set E) (hC_closed : ∀ i : I, IsClosed (C i)) (hC_convex : ∀ i : I, Convex ℝ (C i))
    (h_common_recession : (⋂ i, 0⁺[ℝ] (C i)) = ({0} : Set E))
    (h_small_intersection :
      ∀ J : Finset I, J.card ≤ Module.finrank ℝ E + 1 → (⋂ i ∈ (J : Set I), C i).Nonempty) :
    (⋂ i, C i).Nonempty := sorry

end

/-! ### Text_21_3_3 (from Chap04) -/
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

/-! ### Theorem_21_3 (from Chap04) -/
open scoped BigOperators Rockafellar
open Set

noncomputable section

universe u v

section

variable {E : Type u}
variable {I : Type v}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 21.3 is Rockafellar's infinite-family alternative for closed proper
  convex inequalities on a closed convex set `C`: either there is a point of `C` where
  every constraint is nonpositive, or there is a finitely supported nonnegative multiplier
  certificate uniformly separating `C` from the feasible region.
- `core/canonical`: the existing project owners already matching the mathematics are
  `Function.IsClosedProperConvex`, `weakConvexInequalitySolutionSet`,
  `Set.RecedesInDirection`, `Function.recessionCone`, the no-common-recession owner
  `Set.NoCommonRecessionDirectionOn`, the finitely-supported multiplier owner predicate
  `Finsupp.IsNonnegativeMultiplierCertificateOn`, and the logical exclusive-or `Xor'`.
- `bridge/view`: the textbook phrase "no common direction of recession" is carried by the owner
  `C.NoCommonRecessionDirectionOn f`, whose definitional expansion is exactly the existence-negated
  conjunction of a source-facing recession direction of `C` and membership in every
  function recession cone `Function.recessionCone ((f i)₀⁺)`. The finitely many nonzero
  multipliers are expressed by a single `Finsupp`, and the weak feasible region is the Chapter 21
  owner `weakConvexInequalitySolutionSet f`.

Domain-style sampling used here:
- `Function.IsClosedProperConvex` from `Text_12_3_6`;
- `weakConvexInequalitySolutionSet` and `mem_weakConvexInequalitySolutionSet` from `Text_21_0_1`;
- `Set.RecedesInDirection` from `Definition_8_0_1`;
- `Function.recessionCone` from `Definiton_8_5_0`;
- `Xor'` and `Finsupp` from the canonical logical and finitely supported APIs.

Primitive data vs derived API:
- primitive inputs: an arbitrary index family `f : I → E → WithTopBot ℝ` with
  `∀ i, (f i).IsClosedProperConvex` and a closed convex set `C`;
- primitive hypothesis layer: the no-common-recession condition is the owner
  `C.NoCommonRecessionDirectionOn f`;
- owner feasible-set data: `C ∩ weakConvexInequalitySolutionSet f`;
- derived API: the pointwise restatement `∃ x ∈ C, ∀ i, f i x ≤ 0` of owner feasible-set
  nonemptiness, the exclusive alternative between that owner feasible set and a finitely
  supported nonnegative multiplier certificate, recorded as a predicate on the actual
  `Finsupp` of weights, and the Caratheodory-type support bound
  `Module.finrank ℝ E + 1` for the certificate under the full Theorem 21.3 hypotheses when the
  multiplier alternative occurs.

Layer target: `source-facing`, with the feasible-point side routed through the Chapter 21 weak
inequality owner and the textbook pointwise phrasing retained only as a thin companion bridge.
-/

namespace Finsupp

/-- A nonnegative multiplier family with a positive uniform lower bound for its weighted sum on
`C`. The finite-support data is carried canonically by `weights : I →₀ 𝕜`. -/
def IsNonnegativeMultiplierCertificateOn
    {𝕜 : Type*} [Semiring 𝕜] [LinearOrder 𝕜]
    (weights : I →₀ 𝕜) (C : Set E) (f : I → E → WithTopBot 𝕜) (epsilon : 𝕜) : Prop :=
  (∀ i : I, 0 ≤ weights i) ∧
    0 < epsilon ∧
    ∀ x : E, x ∈ C →
      (epsilon : WithTopBot 𝕜) ≤
        weights.sum (fun i a ↦ (a : WithTopBot 𝕜) * f i x)

end Finsupp

-- Proof sketch: add the indicator of `C` to the family to reduce to the unconstrained case
-- `C = R^n`. If the pointwise nonpositive alternative fails, form the convex hull of the
-- conjugates `fᵢ*`, pass to its positively homogeneous envelope, and use the empty-feasible-set
-- hypothesis to force the value at `0` to be negative after closure. The recession-direction
-- hypothesis rules out the boundary case in which that value could drop only after closure, so one
-- obtains a genuine negative value at `0`; Caratheodory then yields finitely many nonnegative
-- multipliers producing a uniform lower bound `ε > 0` on `C`. Mutual exclusivity is immediate by
-- evaluating a certificate at a feasible point.
/-- The owner weak-feasible set for the family `f` on `C` is exactly the textbook set of points
`x ∈ C` with `f i x ≤ 0` for every constraint `i`. -/
theorem nonpositive_convexInequalitySolutionSet_nonempty_iff
    {ι : Sort v} {β : Type*} [LE β] [Zero β]
    {C : Set E} (f : ι → E → β) :
    (C ∩ weakConvexInequalitySolutionSet f).Nonempty ↔
      ∃ x : E, x ∈ C ∧ ∀ i : ι, f i x ≤ 0 := by
  constructor
  · rintro ⟨x, hxC, hxfeasible⟩
    exact ⟨x, hxC, mem_weakConvexInequalitySolutionSet.mp hxfeasible⟩
  · rintro ⟨x, hxC, hxfeasible⟩
    exact ⟨x, hxC, mem_weakConvexInequalitySolutionSet.mpr hxfeasible⟩

section

variable {𝕜 α : Type*}
variable [Zero 𝕜] [LE 𝕜]
variable [Add E] [Zero E] [SMul 𝕜 E]
variable [AddCommGroup α] [ConditionallyCompleteLattice α]

namespace Set

/-- Owner hypothesis for Chapter 21 alternatives: there is no nonzero recession direction of `C`
that belongs to every recession cone `Function.recessionCone ((f i)₀⁺)`.

This owner keeps the ambient scalar (`𝕜`) and function codomain base (`α`) independent: recession
directions of `C` live in the scalar geometry, while recession cones of `(f i)₀⁺` live in the
`WithTopBot α` codomain layer. -/
def NoCommonRecessionDirectionOn {ι : Sort v}
    (C : Set E) (f : ι → E → WithTopBot α) : Prop :=
  ¬ ∃ y : E, C.RecedesInDirection 𝕜 y ∧
    ∀ i : ι, y ∈ Function.recessionCone ((f i)₀⁺)

@[simp] theorem noCommonRecessionDirectionOn_iff {ι : Sort v}
    (C : Set E) (f : ι → E → WithTopBot α) :
    C.NoCommonRecessionDirectionOn f ↔
      ¬ ∃ y : E, C.RecedesInDirection 𝕜 y ∧
        ∀ i : ι, y ∈ Function.recessionCone ((f i)₀⁺) :=
  Iff.rfl

end Set

end

section

variable [TopologicalSpace E] [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
variable {C : Set E} {f : I → E → WithTopBot ℝ}
local notation "IsClosedProperConvex[ℝ]" => Function.IsClosedProperConvex (𝕜 := ℝ)

/-- Theorem 21.3: let `fᵢ`, `i ∈ I`, be closed proper convex functions on `R^n`, and let `C` be a
closed convex set. If there is no nonzero recession direction of `C` along which every
`fᵢ` has nonpositive recession value, then exactly one of the following holds: either the weak
feasible set `C ∩ weakConvexInequalitySolutionSet f` is nonempty, or there is
a finitely supported nonnegative multiplier family `λ` and some `ε > 0` such that
`ε ≤ ∑ i, λᵢ fᵢ x` for every `x ∈ C`. The source ambient `R^n` is represented here by the
chapter's canonical finite-dimensional real topological vector-space layer. -/
theorem
    xor_nonpositive_convexInequalitySolutionSet_nonempty_or_finitely_supported_nonnegative_multiplier_certificate
    (f : I → E → WithTopBot ℝ)
    (hf : ∀ i : I, IsClosedProperConvex[ℝ] (f i))
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (hno_common : C.NoCommonRecessionDirectionOn f)
    :
    Xor'
      (C ∩ weakConvexInequalitySolutionSet f).Nonempty
      (∃ weights : I →₀ ℝ, ∃ epsilon : ℝ,
        weights.IsNonnegativeMultiplierCertificateOn C f epsilon) := sorry

/-- Source-facing pointwise restatement of Theorem 21.3: the owner weak-feasible-set alternative
is equivalent to existence of `x ∈ C` with `f i x ≤ 0` for every `i`. -/
theorem xor_exists_nonpositive_point_or_finitely_supported_nonnegative_multiplier_certificate
    (f : I → E → WithTopBot ℝ)
    (hf : ∀ i : I, IsClosedProperConvex[ℝ] (f i))
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (hno_common : C.NoCommonRecessionDirectionOn f)
    :
    Xor'
      (∃ x : E, x ∈ C ∧ ∀ i : I, f i x ≤ 0)
      (∃ weights : I →₀ ℝ, ∃ epsilon : ℝ,
        weights.IsNonnegativeMultiplierCertificateOn C f epsilon) := by
  have hiff :
      (C ∩ weakConvexInequalitySolutionSet f).Nonempty ↔
        (∃ x : E, x ∈ C ∧ ∀ i : I, f i x ≤ 0) :=
    nonpositive_convexInequalitySolutionSet_nonempty_iff (C := C) f
  rcases
      xor_nonpositive_convexInequalitySolutionSet_nonempty_or_finitely_supported_nonnegative_multiplier_certificate
        f hf hC_closed hC_convex hno_common with
    hxor | hxor
  · exact Or.inl ⟨hiff.mp hxor.1, hxor.2⟩
  · exact Or.inr ⟨hxor.1, fun hpoint ↦ hxor.2 (hiff.mpr hpoint)⟩

-- Proof sketch: under the full hypotheses of Theorem 21.3, if the multiplier alternative holds,
-- rerun the same convex-hull/separation construction behind that alternative and apply
-- Caratheodory's theorem in ambient dimension `Module.finrank ℝ E`. This directly produces a
-- multiplier certificate with support cardinality at most `Module.finrank ℝ E + 1`; it is not a
-- free-standing reduction theorem for an arbitrary pre-existing certificate on an arbitrary family.
/-- Under the hypotheses of Theorem 21.3, whenever the multiplier alternative occurs, it can be
chosen with at most `Module.finrank ℝ E + 1` nonzero multipliers. -/
theorem exists_finitely_supported_nonnegative_multiplier_certificate_with_support_card_le
    (f : I → E → WithTopBot ℝ)
    (hf : ∀ i : I, IsClosedProperConvex[ℝ] (f i))
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (hno_common : C.NoCommonRecessionDirectionOn f)
    (hcert : ∃ weights : I →₀ ℝ, ∃ epsilon : ℝ,
      weights.IsNonnegativeMultiplierCertificateOn C f epsilon) :
    ∃ weights : I →₀ ℝ, ∃ epsilon : ℝ,
      weights.support.card ≤ Module.finrank ℝ E + 1 ∧
        weights.IsNonnegativeMultiplierCertificateOn C f epsilon := sorry

end

end

/-! ### Text_21_3_4 (from Chap04) -/
open Set
open scoped Rockafellar

noncomputable section

section

local notation "R2" => ℝ × ℝ
local notation "e₁" => ((1 : ℝ), (0 : ℝ))
local notation "e₂" => ((0 : ℝ), (1 : ℝ))

/-- The intrinsic two-branch index for Text 21.3.4. -/
inductive Branch where
  | first
  | second
deriving DecidableEq

/-- Canonical owner of the positive-level weak-sublevel family attached to `f`. -/
def positiveWeakSublevelFamily {E : Type*} {ι : Type*} {α : Type*} [Preorder α] [Zero α]
    (f : ι → E → WithTopBot α) : Set (Set E) :=
  {S | ∃ i : ι, ∃ ε : α, 0 < ε ∧
      S = (f i) ⁻¹' Set.Iic (ε : WithTopBot α)}

/-- Membership in a positive-level weak-sublevel family is exactly membership in one branch weak
sublevel set at a positive threshold, encoded intrinsically by a subtype. -/
theorem mem_positiveWeakSublevelFamily_iff {E : Type*} {ι : Type*} {α : Type*}
    [Preorder α] [Zero α] (f : ι → E → WithTopBot α) (S : Set E) :
    S ∈ positiveWeakSublevelFamily f ↔
      ∃ i : ι, ∃ ε : {ε : α // 0 < ε},
        S = (f i) ⁻¹' Set.Iic ((ε : α) : WithTopBot α) := by
  constructor
  · rintro ⟨i, ε, hε, rfl⟩
    exact ⟨i, ⟨ε, hε⟩, rfl⟩
  · rintro ⟨i, ε, rfl⟩
    exact ⟨i, ε, ε.2, rfl⟩

/-!
Source/core/bridge triage:

- `source-facing`: this example fixes two explicit real-valued functions on `R²`, their `0`
  sublevel sets, the failure of a common nonpositive point, strict feasibility at every positive
  level, and a common recession direction.
- `core/canonical`: the owner abstractions are the two functions themselves on the canonical
  ambient space `R2 = ℝ × ℝ`, the canonical codomain lift
  `Function.toWithTopBot`, the derived owner family `recessionExampleFamily` valued in
  `WithTopBot ℝ`, its convex-on-universe owner
  `ConvexOn ℝ Set.univ (recessionExampleFamily k)` and global bridge
  `(recessionExampleFamily k).IsConvex ℝ`, the source-facing branch owners
  `recessionExampleZeroSublevelSet` and `recessionExampleStrictSublevelSet`, the Chapter 8 owner
  recession cones `recessionCone` and `recessionExampleBranchRecessionCone`, together with the
  source-facing recession-direction owner `C.RecedesInDirection ℝ y`.
- `bridge/view`: the special `0`-sublevel sets are the owner sets
  `recessionExampleZeroSublevelSet k`, and the textbook phrase "common direction of recession" is
  recorded concretely by membership of the direction in the corresponding function-recession cones
  and by the explicit witness
  `∃ y, (univ : Set R2).RecedesInDirection ℝ y ∧
    ∀ k : Branch, y ∈ recessionExampleBranchRecessionCone k`.

Domain-style sampling used here:
- `ConvexOn`;
- `Function.IsConvex`;
- `Function.isConvex_coe_of_convexOn_univ`;
- `Function.IsConvex.convex_le`;
- sublevel owners `f ⁻¹' Set.Iic μ` and `f ⁻¹' Set.Iio μ`;
- `recessionCone`;
- `Function.recessionCone` and `Function.mem_recessionCone_iff`;
- `C.RecedesInDirection ℝ y`.

Primitive data vs derived API:
- primitive data: the explicit formulas for the two functions and the direction `e₁ + e₂`;
- derived API: the canonical `WithTopBot ℝ` lift of the two branch functions into the owner family
  `recessionExampleFamily`, global convexity of each family branch, disjointness of the `0`-
  sublevel sets, the absence of a common nonpositive point,
  strict feasibility at every positive level, and the explicit common
  function-recession-direction witness.

Layer target: `source-facing`, with the owner level chosen to match the surrounding chapter API for
convex functions and recession directions.

Scalar/ambient note:
- this source item is intrinsically real and two-dimensional (`Real.sqrt`, coordinate formulas,
  explicit `e₁ + e₂` geometry), so `ℝ` and `R2` are kept on purpose;
- the codomain owner layer is normalized away from `EReal` to the weaker canonical
  `WithTopBot ℝ` layer used by Chapter 21 owners.
-/

/-- The first function in the counterexample from Text 21.3.4. -/
def recessionExampleF1 (x : R2) : ℝ :=
  Real.sqrt (x.1 ^ 2 + 1) - x.2

/-- The second function in the counterexample from Text 21.3.4. -/
def recessionExampleF2 (x : R2) : ℝ :=
  Real.sqrt (x.2 ^ 2 + 1) - x.1

/-- The common direction `e₁ + e₂` used in Text 21.3.4. -/
def recessionExampleDirection : R2 :=
  e₁ + e₂

/-- The canonical two-branch extended-codomain family attached to the counterexample in Text
21.3.4, exposed at the `WithTopBot ℝ` layer. -/
def recessionExampleFamily : Branch → R2 → WithTopBot ℝ
  | .first => recessionExampleF1.toWithTopBot
  | .second => recessionExampleF2.toWithTopBot

/-- The weak `μ`-sublevel set of branch `k` in the counterexample family. -/
abbrev recessionExampleWeakSublevelSet (k : Branch) (μ : WithTopBot ℝ) : Set R2 :=
  (recessionExampleFamily k) ⁻¹' Set.Iic μ

/-- The weak `0`-sublevel set of branch `k` in the counterexample family. -/
abbrev recessionExampleZeroSublevelSet (k : Branch) : Set R2 :=
  recessionExampleWeakSublevelSet k 0

/-- Positive threshold layer used to index weak positive-level sublevel sets. -/
abbrev PositiveLevel : Type := {ε : ℝ // 0 < ε}

/-- The weak positive-level sublevel set of branch `k` in the counterexample family. -/
abbrev recessionExamplePositiveWeakSublevelSet (k : Branch) (ε : PositiveLevel) : Set R2 :=
  recessionExampleWeakSublevelSet k (ε : ℝ)

/-- The function recession cone of branch `k` in the counterexample family. -/
abbrev recessionExampleBranchRecessionCone (k : Branch) : Set R2 :=
  Function.recessionCone ((recessionExampleFamily k)₀⁺)

/-- The strict `ε`-sublevel set of branch `k` in the counterexample family. -/
abbrev recessionExampleStrictSublevelSet (k : Branch) (ε : ℝ) : Set R2 :=
  (recessionExampleFamily k) ⁻¹' Set.Iio (ε : WithTopBot ℝ)

/-- The source family `{C_{k, ε} | k : Branch, ε > 0}` as a set-family owner. -/
abbrev recessionExamplePositiveWeakSublevelFamily : Set (Set R2) :=
  positiveWeakSublevelFamily recessionExampleFamily

/-- Membership in the source set-family is exactly membership in one branch weak sublevel set at
some positive level. -/
theorem mem_recessionExamplePositiveWeakSublevelFamily_iff (S : Set R2) :
    S ∈ recessionExamplePositiveWeakSublevelFamily ↔
      ∃ k : Branch, ∃ ε : PositiveLevel,
        S = recessionExamplePositiveWeakSublevelSet k ε := by
  simpa [recessionExamplePositiveWeakSublevelFamily, recessionExamplePositiveWeakSublevelSet] using
    (mem_positiveWeakSublevelFamily_iff (f := recessionExampleFamily) (S := S))

/-- Each branch of the canonical `WithTopBot ℝ`-valued counterexample family is convex on `univ`
in the primitive set-owner sense. -/
-- Proof sketch: for `k = Branch.first` and `k = Branch.second`, first prove convexity of the
-- corresponding real-valued branch on all of `R²`; then pass to the `WithTopBot` codomain via
-- the canonical lift theorem `Function.isConvex_coe_of_convexOn_univ`.
theorem recessionExampleFamily_convexOn (k : Branch) :
    ConvexOn ℝ Set.univ (recessionExampleFamily k) := sorry

/-- Global-owner bridge form of `recessionExampleFamily_convexOn`. -/
theorem recessionExampleFamily_isConvex (k : Branch) :
    (recessionExampleFamily k).IsConvex ℝ := by
  simpa [Function.IsConvex] using recessionExampleFamily_convexOn (k := k)

/-- The two displayed `0`-sublevel sets in Text 21.3.4 are disjoint. -/
-- Proof sketch: if a point lay in both sublevel sets, then
-- `x.2 ≥ Real.sqrt (x.1 ^ 2 + 1)` and `x.1 ≥ Real.sqrt (x.2 ^ 2 + 1)`. Squaring both
-- inequalities gives `x.2 ^ 2 ≥ x.1 ^ 2 + 1` and `x.1 ^ 2 ≥ x.2 ^ 2 + 1`, whose sum is
-- impossible.
theorem recessionExample_zeroSublevelSets_disjoint :
    Disjoint
      (recessionExampleZeroSublevelSet Branch.first)
      (recessionExampleZeroSublevelSet Branch.second) :=
  sorry

/-- The canonical two-branch family never takes simultaneously nonpositive values. -/
-- Proof sketch: a common nonpositive point would belong to both `0`-sublevel sets, contradicting
-- `recessionExample_zeroSublevelSets_disjoint`.
theorem recessionExample_no_joint_nonpositive_point :
    ¬ ∃ x : R2, ∀ k : Branch, x ∈ recessionExampleZeroSublevelSet k := sorry

/-- At every positive level `ε`, the two-branch family is jointly strictly feasible. -/
-- Proof sketch: along the diagonal ray `t ↦ t • recessionExampleDirection` both branch values are
-- `Real.sqrt (t ^ 2 + 1) - t`, which decreases to `0` through positive values, so for any
-- `ε > 0` some diagonal point satisfies both inequalities strictly.
theorem recessionExample_joint_strict_feasibility {ε : ℝ} (hε : 0 < ε) :
    ∃ x : R2, ∀ k : Branch, x ∈ recessionExampleStrictSublevelSet k ε := sorry

/-- The direction `e₁ + e₂` is a recession direction of the ambient set `R² = univ`. -/
theorem recessionExampleDirection_recedesIn_univ :
    (univ : Set R2).RecedesInDirection ℝ recessionExampleDirection := sorry

/-- The direction `e₁ + e₂` lies in the function recession cone of each branch, recorded in the
canonical Chapter 8 owner language. -/
-- Proof sketch: write `φ(s) = Real.sqrt (s ^ 2 + 1) - s`. The translate profiles of both branch
-- functions along `recessionExampleDirection` are obtained from the decreasing function `φ`, so
-- the corresponding recession-function values are nonpositive.
theorem recessionExampleDirection_mem_functionRecessionCone (k : Branch) :
    recessionExampleDirection ∈ recessionExampleBranchRecessionCone k :=
  sorry

/-- Text 21.3.4 supplies an explicit common nonpositive recession direction for the two-branch
family, thereby witnessing failure of the no-common-recession hypothesis in Theorem 21.3. -/
theorem recessionExample_exists_common_nonpositive_recession_direction :
    ∃ y : R2,
      (univ : Set R2).RecedesInDirection ℝ y ∧
        ∀ k : Branch,
          y ∈ recessionExampleBranchRecessionCone k :=
  sorry

end

/-! ### Text_21_3_5 (from Chap04) -/
noncomputable section

/-!
Source/core/bridge triage:

- `source-facing`: Text 21.3.5 gives a family of closed convex sets showing that Helly's
  conclusion can fail without a no-common-recession-direction hypothesis.
- `core/canonical`: the owner abstraction is the upstream set-family owner
  `recessionExamplePositiveWeakSublevelFamily : Set (Set (ℝ × ℝ))`, built from positive-level weak
  sublevel sets.
- `bridge/view`: the textbook member notation `C[k, ε]` is kept as a thin surface for concrete
  branch/level sets, while theorem surfaces are stated on owner membership
  `S ∈ recessionExamplePositiveWeakSublevelFamily`.

Domain-style sampling used here:
- `positiveWeakSublevelFamily` from `Text_21_3_4`;
- `recessionExamplePositiveWeakSublevelFamily` from `Text_21_3_4`;
- `recessionExample_joint_strict_feasibility`;
- `sInter` for the total and finite intersections of the owner set-family.

Primitive data vs derived API:
- primitive data: the upstream owner `recessionExamplePositiveWeakSublevelFamily`;
- derived API: member-wise nonemptiness/closedness/convexity, finite-subfamily
  intersection-nonemptiness, and emptiness of the total intersection.

Layer target: `source-facing`, since the mathematics is the explicit counterexample family itself.

Scalar/ambient note:
- this item is the explicit two-branch counterexample on `R²` from Text 21.3.4, so `ℝ` and
  `ℝ × ℝ`
  are mathematically essential in this file rather than proof-accidental defaults;
- codomain thresholds and owner surfaces are normalized to `WithTopBot ℝ` (not
  `EReal`-named APIs) to match the Chapter 21 canonical layer.
-/

namespace HellyCounterexample

local notation "R2" => ℝ × ℝ

/-- The source-facing textbook member `C_{k,ε}` of Text 21.3.5. -/
scoped notation "C[" k "," ε "]" =>
  recessionExamplePositiveWeakSublevelSet k ε

/-- Short owner notation for the canonical set-family `{C_{k, ε} | k : Branch, ε > 0}`. -/
scoped notation "𝓒" => recessionExamplePositiveWeakSublevelFamily

/-- Owner bridge: membership in `𝓒` is exactly membership in one positive-level textbook member
`C[k, ε]`. -/
theorem mem_family_iff (S : Set R2) :
    S ∈ 𝓒 ↔ ∃ k : Branch, ∃ ε : PositiveLevel, S = C[k, ε] := by
  simpa using mem_recessionExamplePositiveWeakSublevelFamily_iff S

/-- Each textbook member belongs to the canonical owner family. -/
theorem C_mem_family (k : Branch) (ε : PositiveLevel) :
    C[k, ε] ∈ 𝓒 := by
  exact (mem_family_iff _).2 ⟨k, ε, rfl⟩

/-- Every owner member of the canonical counterexample family is nonempty. -/
-- Proof sketch: `recessionExample_joint_strict_feasibility hε` gives a point where both branch
-- functions are `< ε`, hence in particular a point of
-- `recessionExamplePositiveWeakSublevelSet k ε`.
theorem family_nonempty {S : Set R2}
    (hS : S ∈ 𝓒) :
    S.Nonempty := sorry

/-- Textbook member view: each `C[k, ε]` at positive level `ε` is nonempty. -/
theorem C_nonempty (k : Branch) (ε : PositiveLevel) :
    (C[k, ε]).Nonempty := by
  exact family_nonempty (C_mem_family k ε)

/-- Every owner member of the canonical counterexample family is closed. -/
-- Proof sketch: `recessionExampleFamily k` is the `WithTopBot ℝ` lift of one of the two continuous
-- branch functions from `Text 21.3.4`, so the owner solution set
-- `recessionExamplePositiveWeakSublevelSet k ε` is the corresponding
-- closed sublevel set. Since these are subsets of the full ambient space `R²` (not of a proper
-- ambient subset), ambient `IsClosed` is already the intrinsic topology statement here.
theorem family_isClosed {S : Set R2}
    (hS : S ∈ 𝓒) :
    IsClosed S := sorry

/-- Textbook member view: each `C[k, ε]` at positive level `ε` is closed. -/
theorem C_isClosed (k : Branch) (ε : PositiveLevel) :
    IsClosed (C[k, ε]) := by
  exact family_isClosed (C_mem_family k ε)

/-- Every owner member of the canonical counterexample family is convex. -/
-- Proof sketch: apply the canonical single-constraint owner theorem
-- `ConvexInequalityRelation.convex_solutionSet` to the branch owner
-- `recessionExampleFamily k`, using the primitive owner
-- `recessionExampleFamily_convexOn k` and its global bridge
-- `recessionExampleFamily_isConvex k`.
theorem family_convex {S : Set R2}
    (hS : S ∈ 𝓒) :
    Convex ℝ S := sorry

/-- Textbook member view: each `C[k, ε]` at positive level `ε` is convex. -/
theorem C_convex (k : Branch) (ε : PositiveLevel) :
    Convex ℝ (C[k, ε]) := by
  exact family_convex (C_mem_family k ε)

/-- Every finite subfamily of the canonical counterexample family has nonempty intersection. In
particular, this implies the three-member intersection clause in Text 21.3.5 (1). -/
-- Canonical finite-family owner surface: use `Set.Finite` and subset inclusion instead of a
-- `Finset` encoding.
-- Proof sketch: for a finite parameter set `S`, choose `λ` at least as large as the maximum of
-- the thresholds `(1 - ε^2) / (2 ε)` over the positive levels appearing in `S`. Then the diagonal
-- point `λ • recessionExampleDirection` lies in every corresponding member `C[k, ε]`.
theorem finite_subfamily_nonempty {F : Set (Set R2)}
    (hF_finite : F.Finite) (hF_subset : F ⊆ 𝓒) :
    (⋂₀ F).Nonempty :=
  sorry

/-- Text 21.3.5 (2): the total intersection of all sets `C_{k, ε}` with `k ∈ {1, 2}` and
`ε > 0` is empty. -/
-- Proof sketch: a point in the total intersection would satisfy both branch inequalities
-- `recessionExampleF1 x ≤ ε` and `recessionExampleF2 x ≤ ε` for every positive `ε`, hence both
-- branch values are `≤ 0`. The disjointness result from `Text 21.3.4` rules this out.
theorem total_intersection_eq_empty :
    ⋂₀ 𝓒 = (∅ : Set R2) := sorry

end HellyCounterexample
