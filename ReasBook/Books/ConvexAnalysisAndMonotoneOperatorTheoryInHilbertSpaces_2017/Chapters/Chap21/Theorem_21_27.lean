import Mathlib
import BauschkeLean.Chap01.Corollary_1_45
import BauschkeLean.Chap01.Text_1_0_14
import BauschkeLean.Chap17.Proposition_17_39.SelectionContinuity
import BauschkeLean.Chap18.Proposition_18_4
import BauschkeLean.Chap20.Definition_20_20
import BauschkeLean.Chap20.Proposition_20_38
import BauschkeLean.Chap21.Proposition_21_12
import BauschkeLean.Chap21.Theorem_21_18

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped InnerProductSpace SetValuedOperator

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Source/core/bridge triage:
-- - `source-facing`: Theorem 21.27 is an existential regularity statement for a maximally
--   monotone operator on the interior of its domain.
-- - `core/canonical`: local regularity of a single-valued realization is expressed by
--   `SelectionContinuousAt A`, while singleton fibers are canonically recorded by equalities
--   `A x = ({u} : Set H)` rather than a parallel unique-existence wrapper.
-- - `bridge/view`: density and `Gδ` regularity on `closure A.dom` are recorded through the
--   closure-subtype view `Subtype.val ⁻¹' C`, following the nearby Chapter 18/21 precedent.
--
-- Semantic recall: `lean_leansearch` only surfaced generic `Dense`/`IsGδ` infrastructure, so the
-- verified local owners used here are `Selection A`, `SelectionContinuousAt A`, singleton-fiber
-- equalities `A x = ({u} : Set H)`, and the
-- closure-subtype dense-`Gδ` convention from Corollary 21.28.

/-- Helper for Theorem 21.27: `smallDiameterNeighborhoodLocus A ε` is the set of points admitting
an open ball on which `A` has bounded image of diameter `< ε`. The boundedness clause keeps the
Lean `Metric.diam` statement faithful to the textbook bounded-diameter meaning. -/
private def smallDiameterNeighborhoodLocus
    (A : SetValuedOperator H H) (ε : Set.Ioi (0 : ℝ)) : Set H :=
  {x | ∃ ρ : Set.Ioi (0 : ℝ),
      Metric.ball x (ρ : ℝ) ⊆ A.dom ∧
      Bornology.IsBounded (A.image (Metric.ball x (ρ : ℝ))) ∧
      Metric.diam (A.image (Metric.ball x (ρ : ℝ))) < (ε : ℝ)}

/-- Helper for Theorem 21.27: every small-diameter neighborhood witness can be shrunk, so
`smallDiameterNeighborhoodLocus A ε` is open. -/
private theorem isOpen_smallDiameterNeighborhoodLocus
    (A : SetValuedOperator H H) (ε : Set.Ioi (0 : ℝ)) :
    IsOpen (smallDiameterNeighborhoodLocus A ε) := by
  rw [Metric.isOpen_iff]
  intro x hx
  rcases hx with ⟨ρ, hdom, hbounded, hdiam⟩
  have hρpos : 0 < (ρ : ℝ) := by
    exact ρ.2
  have hρhalf : 0 < (ρ : ℝ) / 2 := by
    linarith
  refine ⟨(ρ : ℝ) / 2, hρhalf, ?_⟩
  intro y hy
  refine ⟨⟨(ρ : ℝ) / 2, hρhalf⟩, ?_, ?_, ?_⟩
  · intro z hz
    have hy' : dist y x < ρ / 2 := by
      simpa [Metric.mem_ball, dist_comm] using hy
    have hz' : dist z y < ρ / 2 := by
      simpa [Metric.mem_ball, dist_comm] using hz
    have hzx : dist z x < ρ := by
      calc
        dist z x ≤ dist z y + dist y x := by
          simpa [dist_comm, add_comm] using dist_triangle z y x
        _ < ρ / 2 + ρ / 2 := by
          linarith
        _ = ρ := by ring
    exact hdom (by simpa [Metric.mem_ball, dist_comm] using hzx)
  · refine hbounded.subset ?_
    rintro u hu
    rcases (SetValuedOperator.mem_image A (Metric.ball y (ρ / 2)) u).1 hu with ⟨z, hz, hzu⟩
    refine (SetValuedOperator.mem_image A (Metric.ball x ρ) u).2 ⟨z, ?_, hzu⟩
    have hy' : dist y x < ρ / 2 := by
      simpa [Metric.mem_ball, dist_comm] using hy
    have hz' : dist z y < ρ / 2 := by
      simpa [Metric.mem_ball, dist_comm] using hz
    have hzx : dist z x < ρ := by
      calc
        dist z x ≤ dist z y + dist y x := by
          simpa [dist_comm, add_comm] using dist_triangle z y x
        _ < ρ / 2 + ρ / 2 := by
          linarith
        _ = ρ := by ring
    simpa [Metric.mem_ball, dist_comm] using hzx
  · refine lt_of_le_of_lt ?_ hdiam
    refine Metric.diam_mono ?_ hbounded
    intro u hu
    rcases (SetValuedOperator.mem_image A (Metric.ball y (ρ / 2)) u).1 hu with ⟨z, hz, hzu⟩
    refine (SetValuedOperator.mem_image A (Metric.ball x ρ) u).2 ⟨z, ?_, hzu⟩
    have hy' : dist y x < ρ / 2 := by
      simpa [Metric.mem_ball, dist_comm] using hy
    have hz' : dist z y < ρ / 2 := by
      simpa [Metric.mem_ball, dist_comm] using hz
    have hzx : dist z x < ρ := by
      calc
        dist z x ≤ dist z y + dist y x := by
          simpa [dist_comm, add_comm] using dist_triangle z y x
        _ < ρ / 2 + ρ / 2 := by
          linarith
        _ = ρ := by ring
    simpa [Metric.mem_ball, dist_comm] using hzx

/-- Helper for Theorem 21.27: a small-diameter neighborhood is in particular a neighborhood inside
`A.dom`, so every point of the locus belongs to `interior A.dom`. -/
private theorem smallDiameterNeighborhoodLocus_subset_interior_dom
    (A : SetValuedOperator H H) (ε : Set.Ioi (0 : ℝ)) :
    smallDiameterNeighborhoodLocus A ε ⊆ interior A.dom := by
  intro x hx
  rcases hx with ⟨ρ, hdom, _, _⟩
  refine mem_interior_iff_mem_nhds.2 ?_
  exact Filter.mem_of_superset (Metric.ball_mem_nhds x ρ.2) hdom

/-- Helper for Theorem 21.27: a nonempty bounded support slice contains an actual point whose
inner product is within the prescribed margin of the support value. -/
private theorem existsMemSupportSliceOfNonemptyOfBounded
    (C : Set H) (hC_nonempty : C.Nonempty) (hC_bounded : Bornology.IsBounded C)
    (z : H) (α : Set.Ioi (0 : ℝ)) :
    ∃ u ∈ C, (σ[C] z).toReal - (α : ℝ) < ⟪z, u⟫_ℝ := by
  let S : Set EReal := (fun u : H ↦ ((⟪u, z⟫_ℝ : ℝ) : EReal)) '' C
  have hS_nonempty : S.Nonempty := by
    exact hC_nonempty.image fun u : H ↦ ((⟪u, z⟫_ℝ : ℝ) : EReal)
  have hσ_bot : σ[C] z ≠ ⊥ :=
    ne_of_gt (ERealFunction.bot_lt_supportFunction_of_nonempty C hC_nonempty z)
  have hσ_top : σ[C] z ≠ ⊤ :=
    ne_of_lt
      (ERealFunction.example_11_2_5_supportFunction_realValued_of_bounded
        C hC_nonempty hC_bounded z).2
  have hlt :
      (((σ[C] z).toReal - (α : ℝ) : ℝ) : EReal) < sSup S := by
    -- Step 1: rewrite the support value as a real `EReal` so the margin inequality is literal.
    have hlt' :
        (((σ[C] z).toReal - (α : ℝ) : ℝ) : EReal) <
          (((σ[C] z).toReal : ℝ) : EReal) := by
      exact_mod_cast sub_lt_self ((σ[C] z).toReal) α.2
    simpa [S, supportFunction_eq_sSup_image, EReal.coe_toReal hσ_top hσ_bot] using hlt'
  -- Step 2: approximate the supremum by an actual point of the support slice.
  rcases exists_lt_of_lt_csSup hS_nonempty hlt with ⟨s, hsS, hslt⟩
  rcases hsS with ⟨u, huC, rfl⟩
  refine ⟨u, huC, ?_⟩
  have hu_slice : (σ[C] z).toReal - (α : ℝ) < ⟪u, z⟫_ℝ := by
    exact EReal.coe_lt_coe_iff.mp (by simpa using hslt)
  simpa [real_inner_comm] using hu_slice

/-- Helper for Theorem 21.27: one graph point satisfying a strict support inequality can be pushed
inside the same ball to a point whose entire fiber satisfies that strict halfspace inequality. -/
private theorem existsPointInBallWithFiberSubsetStrictHalfspace
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A)
    {y x₁ z u₁ : H} {r β : ℝ}
    (hx₁ : x₁ ∈ Metric.ball y r) (hu₁ : u₁ ∈ A x₁)
    (hβu₁ : β < ⟪z, u₁⟫_ℝ) :
    ∃ x₀ ∈ Metric.ball y r, ∀ u ∈ A x₀, β < ⟪z, u⟫_ℝ := by
  by_cases hz : z = 0
  · -- If the direction vanishes, the strict halfspace is already the whole fiber inequality.
    refine ⟨x₁, hx₁, ?_⟩
    intro u hu
    simpa [hz] using hβu₁
  · have hz_norm : 0 < ‖z‖ := norm_pos_iff.2 hz
    have hball_open : IsOpen (Metric.ball y r) := Metric.isOpen_ball
    rw [Metric.isOpen_iff] at hball_open
    rcases hball_open x₁ hx₁ with ⟨δ, hδ, hδball⟩
    let γ : ℝ := δ / (2 * ‖z‖)
    let x₀ : H := x₁ + γ • z
    have hγpos : 0 < γ := by
      dsimp [γ]
      positivity
    have hx₀sub : x₀ - x₁ = γ • z := by
      dsimp [x₀]
      abel
    have hγnorm : γ * ‖z‖ = δ / 2 := by
      dsimp [γ]
      field_simp [hz_norm.ne']
    have hx₀x₁ : x₀ ∈ Metric.ball x₁ δ := by
      rw [Metric.mem_ball, dist_eq_norm, hx₀sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hγpos.le]
      calc
        γ * ‖z‖ = δ / 2 := hγnorm
        _ < δ := by linarith
    have hx₀ : x₀ ∈ Metric.ball y r := hδball hx₀x₁
    refine ⟨x₀, hx₀, ?_⟩
    intro u hu
    -- Step 1: monotonicity against `(x₁, u₁)` turns the shift in the `z` direction into a
    -- lower bound on the support functional.
    have hmono :
        0 ≤ γ * (⟪z, u⟫_ℝ - ⟪z, u₁⟫_ℝ) := by
      have hmono' :
          0 ≤ ⟪x₀ - x₁, u - u₁⟫_ℝ :=
        (SetValuedOperator.isMonotone_iff A).1 hA.1 hu hu₁
      simpa [hx₀sub, real_inner_smul_left, inner_sub_right, mul_sub] using hmono'
    have hu₁_le_u : ⟪z, u₁⟫_ℝ ≤ ⟪z, u⟫_ℝ := by
      nlinarith [hmono, hγpos]
    -- Step 2: combine the monotonicity lower bound with the original strict slice inequality.
    linarith

/-- Helper for Theorem 21.27: if one fiber lies in a strict inner-product halfspace and the local
image is bounded, then a smaller ball has image contained in the same strict halfspace. -/
private theorem existsBallImageSubsetStrictHalfspaceOfFiberSubset
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A)
    {y x₀ z : H} {r β : ℝ}
    (hx₀ : x₀ ∈ Metric.ball y r)
    (hbounded : Bornology.IsBounded (A.image (Metric.ball y r)))
    (hfiber : ∀ u ∈ A x₀, β < ⟪z, u⟫_ℝ) :
    ∃ ρ : Set.Ioi (0 : ℝ),
      Metric.ball x₀ (ρ : ℝ) ⊆ Metric.ball y r ∧
      A.image (Metric.ball x₀ (ρ : ℝ)) ⊆ {u | β < ⟪z, u⟫_ℝ} := by
  let η : ℝ := (r - dist x₀ y) / 2
  have hηpos : 0 < η := by
    rw [Metric.mem_ball] at hx₀
    dsimp [η]
    linarith
  have hηsubset : Metric.ball x₀ η ⊆ Metric.ball y r := by
    intro x hx
    rw [Metric.mem_ball] at hx hx₀ ⊢
    calc
      dist x y ≤ dist x x₀ + dist x₀ y := by
        simpa [dist_comm, add_comm] using dist_triangle x x₀ y
      _ < η + dist x₀ y := by
        linarith
      _ < r := by
        dsimp [η]
        linarith
  by_contra hρ
  have hcounter :
      ∀ n : ℕ, ∃ x u,
        x ∈ Metric.ball x₀ (min η (1 / (n + 1 : ℝ))) ∧
        u ∈ A x ∧
        ⟪z, u⟫_ℝ ≤ β := by
    intro n
    let ρ : Set.Ioi (0 : ℝ) := ⟨min η (1 / (n + 1 : ℝ)), by
      refine lt_min hηpos ?_
      positivity⟩
    have hρsubset : Metric.ball x₀ (ρ : ℝ) ⊆ Metric.ball y r := by
      intro x hx
      refine hηsubset ?_
      rw [Metric.mem_ball] at hx ⊢
      exact lt_of_lt_of_le hx (min_le_left _ _)
    have hρnot :
        ¬ A.image (Metric.ball x₀ (ρ : ℝ)) ⊆ {u | β < ⟪z, u⟫_ℝ} := by
      intro himage
      exact hρ ⟨ρ, hρsubset, himage⟩
    have hρnot' :
        ∃ u, u ∈ A.image (Metric.ball x₀ (ρ : ℝ)) ∧ u ∉ {u | β < ⟪z, u⟫_ℝ} :=
      Set.not_subset.1 hρnot
    rcases hρnot' with ⟨u, huImage, huNot⟩
    rcases (SetValuedOperator.mem_image A (Metric.ball x₀ (ρ : ℝ)) u).1 huImage with
      ⟨x, hx, hu⟩
    exact ⟨x, u, by simpa [ρ] using hx, hu, not_lt.1 huNot⟩
  choose xSeq uSeq hxSeq huSeq huSeq_le using hcounter
  have hxSeq_ambient : ∀ n, xSeq n ∈ Metric.ball y r := by
    intro n
    refine hηsubset ?_
    have hxSeqn : dist (xSeq n) x₀ < min η (1 / (n + 1 : ℝ)) := by
      have hxSeqn' := hxSeq n
      rw [Metric.mem_ball] at hxSeqn'
      exact hxSeqn'
    rw [Metric.mem_ball]
    exact lt_of_lt_of_le hxSeqn (min_le_left _ _)
  have hx_tendsto : Tendsto xSeq atTop (nhds x₀) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    rcases exists_nat_one_div_lt hε with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    have hstep :
        dist (xSeq n) x₀ < 1 / (n + 1 : ℝ) := by
      exact lt_of_lt_of_le (by simpa [dist_comm] using hxSeq n) (min_le_right _ _)
    have hmono : (1 / (n + 1 : ℝ)) ≤ 1 / (N + 1 : ℝ) := by
      have hcast : (N + 1 : ℝ) ≤ n + 1 := by
        exact_mod_cast Nat.succ_le_succ hn
      exact one_div_le_one_div_of_le (by positivity) hcast
    exact lt_trans (lt_of_lt_of_le hstep hmono) hN
  have hu_bounded : Bornology.IsBounded (Set.range uSeq) := by
    refine hbounded.subset ?_
    rintro u ⟨n, rfl⟩
    exact (SetValuedOperator.mem_image A (Metric.ball y r) (uSeq n)).2
      ⟨xSeq n, hxSeq_ambient n, huSeq n⟩
  rcases bounded_sequence_has_weakly_convergent_subsequence uSeq hu_bounded with
    ⟨uLim, φ, hφ, hφweak⟩
  have hx_sub : Tendsto (fun n ↦ xSeq (φ n)) atTop (nhds x₀) :=
    hx_tendsto.comp hφ.tendsto_atTop
  have hu_sub_bounded : Bornology.IsBounded (Set.range fun n ↦ uSeq (φ n)) := by
    refine hu_bounded.subset ?_
    rintro _ ⟨n, rfl⟩
    exact ⟨φ n, rfl⟩
  have hx_sub_bounded : Bornology.IsBounded (Set.range fun n ↦ xSeq (φ n)) :=
    Metric.isBounded_range_of_tendsto _ hx_sub
  have hgraph_bounded :
      Bornology.IsBounded (Set.range fun n ↦ (xSeq (φ n), uSeq (φ n))) := by
    refine (hx_sub_bounded.prod hu_sub_bounded).subset ?_
    rintro _ ⟨n, rfl⟩
    exact ⟨⟨n, rfl⟩, ⟨n, rfl⟩⟩
  have hgraph : ∀ n, (xSeq (φ n), uSeq (φ n)) ∈ gra A := by
    intro n
    simpa using huSeq (φ n)
  have huLim_graph : (x₀, uLim) ∈ gra A :=
    SetValuedOperator.Maximal.mem_graph_of_tendsto_of_tendsto_weakly hA
      hgraph hgraph_bounded hx_sub hφweak
  have hinner_tendsto :
      Tendsto (fun n ↦ ⟪uSeq (φ n), z⟫_ℝ) atTop (nhds ⟪uLim, z⟫_ℝ) := by
    simpa using
      ((weakSpace_continuous_inner_right (H := H) z).tendsto
        (toWeakSpace ℝ H uLim)).comp hφweak
  have hlimit_le : ⟪uLim, z⟫_ℝ ≤ β := by
    refine le_of_tendsto_of_tendsto hinner_tendsto tendsto_const_nhds ?_
    exact Filter.Eventually.of_forall fun n ↦ by
      simpa [real_inner_comm] using huSeq_le (φ n)
  have huLim : uLim ∈ A x₀ := by
    simpa using huLim_graph
  have hstrict : β < ⟪z, uLim⟫_ℝ := hfiber uLim huLim
  exact (not_lt_of_ge (by simpa [real_inner_comm] using hlimit_le)) hstrict

/-- Helper for Theorem 21.27: every ball around a point of `interior A.dom` contains a point of
`smallDiameterNeighborhoodLocus A ε`. -/
private theorem existsSmallDiameterNeighborhoodPointInBallOfMemInteriorDom
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A)
    {y : H} (hy : y ∈ interior A.dom) (ε : Set.Ioi (0 : ℝ)) {r : ℝ} (hr : 0 < r) :
    ∃ x, x ∈ Metric.ball y r ∧ x ∈ smallDiameterNeighborhoodLocus A ε := by
  have hyDom : y ∈ A.dom := interior_subset hy
  have hLoc : A.IsLocallyBoundedAt y := by
    refine (isLocallyBoundedAt_iff_not_mem_frontier_dom_of_maximal A hA y).2 ?_
    rw [mem_frontier_iff_notMem_interior hyDom]
    exact not_not_intro hy
  rcases Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hy) with ⟨ρdom, hρdom, hρdomSubset⟩
  rcases hLoc with ⟨ρloc, hρloc, hρlocBounded⟩
  let δ : ℝ := min ρdom (min ρloc (r / 2))
  have hδpos : 0 < δ := by
    dsimp [δ]
    refine lt_min hρdom ?_
    refine lt_min hρloc ?_
    linarith
  have hδ_subset_dom : Metric.ball y δ ⊆ A.dom := by
    intro x hx
    refine hρdomSubset ?_
    rw [Metric.mem_ball] at hx ⊢
    exact lt_of_lt_of_le hx (min_le_left _ _)
  have hδ_le_loc : δ ≤ ρloc := by
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ_le_rhalf : δ ≤ r / 2 := by
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hδ_subset_r : Metric.ball y δ ⊆ Metric.ball y r := by
    intro x hx
    rw [Metric.mem_ball] at hx ⊢
    exact lt_of_lt_of_le hx (by linarith [hδ_le_rhalf])
  have hδ_bounded : Bornology.IsBounded (A.image (Metric.ball y δ)) := by
    refine hρlocBounded.subset ?_
    intro u hu
    rcases (SetValuedOperator.mem_image A (Metric.ball y δ) u).1 hu with ⟨x, hx, hux⟩
    refine (SetValuedOperator.mem_image A (Metric.ball y ρloc) u).2 ⟨x, ?_, hux⟩
    rw [Metric.mem_ball] at hx ⊢
    exact lt_of_lt_of_le hx hδ_le_loc
  have hyBallδ : y ∈ Metric.ball y δ := by
    simpa [Metric.mem_ball] using hδpos
  have hC_nonempty : (A.image (Metric.ball y δ)).Nonempty := by
    rcases (SetValuedOperator.mem_dom_iff A y).1 hyDom with ⟨u, hu⟩
    exact ⟨u, (SetValuedOperator.mem_image A (Metric.ball y δ) u).2 ⟨y, hyBallδ, hu⟩⟩
  have hεpos : 0 < (ε : ℝ) := by
    exact ε.2
  have hεhalf_pos : 0 < (ε : ℝ) / 2 := by
    linarith
  let εhalf : ERealFunction.PosReal := ⟨(ε : ℝ) / 2, hεhalf_pos⟩
  let C : Set H := A.image (Metric.ball y δ)
  rcases ERealFunction.exists_support_slice_diam_le_of_nonempty_of_bounded
      C hC_nonempty hδ_bounded εhalf with
    ⟨z, α, hdiamSlice⟩
  rcases existsMemSupportSliceOfNonemptyOfBounded C hC_nonempty hδ_bounded z α with
    ⟨u₁, hu₁C, hu₁slice⟩
  rcases (SetValuedOperator.mem_image A (Metric.ball y δ) u₁).1 hu₁C with
    ⟨x₁, hx₁δ, hu₁⟩
  rcases existsPointInBallWithFiberSubsetStrictHalfspace A hA hx₁δ hu₁ hu₁slice with
    ⟨x₀, hx₀δ, hx₀fiber⟩
  rcases existsBallImageSubsetStrictHalfspaceOfFiberSubset A hA hx₀δ hδ_bounded hx₀fiber with
    ⟨ρ, hρsubset, hρhalf⟩
  let S : Set H := {u ∈ C | (σ[C] z).toReal - (α : ℝ) < ⟪z, u⟫_ℝ}
  have hsmall_subset_C :
      A.image (Metric.ball x₀ (ρ : ℝ)) ⊆ C := by
    intro u hu
    rcases (SetValuedOperator.mem_image A (Metric.ball x₀ (ρ : ℝ)) u).1 hu with ⟨x, hx, hux⟩
    exact (SetValuedOperator.mem_image A (Metric.ball y δ) u).2 ⟨x, hρsubset hx, hux⟩
  have hsmall_subset_S :
      A.image (Metric.ball x₀ (ρ : ℝ)) ⊆ S := by
    intro u hu
    exact ⟨hsmall_subset_C hu, hρhalf hu⟩
  have hS_bounded : Bornology.IsBounded S := by
    refine hδ_bounded.subset ?_
    intro u hu
    exact hu.1
  refine ⟨x₀, hδ_subset_r hx₀δ, ⟨ρ, ?_, ?_, ?_⟩⟩
  · intro x hx
    exact hδ_subset_dom (hρsubset hx)
  · refine hδ_bounded.subset ?_
    intro u hu
    exact hsmall_subset_C hu
  · -- Step 1: the smaller image sits inside the strict support slice from Proposition 18.4.
    calc
      Metric.diam (A.image (Metric.ball x₀ (ρ : ℝ)))
          ≤ Metric.diam S := Metric.diam_mono hsmall_subset_S hS_bounded
      _ ≤ (εhalf : ℝ) := hdiamSlice
      _ < (ε : ℝ) := by
        have hhalf_lt : ((εhalf : ERealFunction.PosReal) : ℝ) < (ε : ℝ) := by
          dsimp [εhalf]
          simpa using half_lt_self hεpos
        exact hhalf_lt

/-- Helper for Theorem 21.27: each small-diameter locus is dense in `interior A.dom`. The
intended route is the textbook support-slice argument: use Theorem 21.18 to bound `A` on a ball,
Proposition 18.4 to cut a support slice of diameter `< ε`, use monotonicity to find `x₀` whose
whole fiber lies in that slice, and then upgrade pointwise slice containment to a neighborhood via
Proposition 20.38. -/
private theorem interiorDom_subset_closure_smallDiameterNeighborhoodLocus
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (ε : Set.Ioi (0 : ℝ)) :
    interior A.dom ⊆ closure (smallDiameterNeighborhoodLocus A ε) := by
  intro y hy
  -- Route correction: first prove the explicit ball-witness theorem, then wrap it with
  -- `Metric.mem_closure_iff` instead of fighting the ambient closure directly.
  rw [Metric.mem_closure_iff]
  intro r hr
  rcases existsSmallDiameterNeighborhoodPointInBallOfMemInteriorDom A hA hy ε hr with
    ⟨x, hxball, hxsmall⟩
  exact ⟨x, hxsmall, by simpa [Metric.mem_ball, dist_comm] using hxball⟩

/-- Helper for Theorem 21.27: the closure-subtype pullback of the small-diameter locus is dense
in `closure A.dom`. -/
private theorem dense_preimage_smallDiameterNeighborhoodLocus_in_closure
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A)
    (hinter : (interior A.dom).Nonempty) (ε : Set.Ioi (0 : ℝ)) :
    Dense (Subtype.val ⁻¹' smallDiameterNeighborhoodLocus A ε : Set (closure A.dom)) := by
  rw [Subtype.dense_iff]
  have hclosure_eq :
      closure (interior A.dom) = closure A.dom :=
    closure_interior_dom_eq_closure_dom_of_interior_nonempty A hA hinter
  have hambient :
      closure A.dom ⊆ closure (smallDiameterNeighborhoodLocus A ε) := by
    calc
      closure A.dom = closure (interior A.dom) := by
        exact hclosure_eq.symm
      _ ⊆ closure (closure (smallDiameterNeighborhoodLocus A ε)) := by
        exact
          closure_mono
            (interiorDom_subset_closure_smallDiameterNeighborhoodLocus A hA ε)
      _ = closure (smallDiameterNeighborhoodLocus A ε) := by
        rw [closure_closure]
  have himage :
      (((↑) : closure A.dom → H) ''
          (Subtype.val ⁻¹' smallDiameterNeighborhoodLocus A ε :
            Set (closure A.dom))) =
        smallDiameterNeighborhoodLocus A ε := by
    ext z
    constructor
    · rintro ⟨z', hz', rfl⟩
      exact hz'
    · intro hz
      have hzInterior :
          z ∈ interior A.dom :=
        smallDiameterNeighborhoodLocus_subset_interior_dom A ε hz
      refine ⟨⟨z, subset_closure (interior_subset hzInterior)⟩, hz, rfl⟩
  simpa [himage] using hambient

/-- Theorem 21.27 (Kenderov): if `A : H → 2^H` is maximally monotone and `interior A.dom` is
nonempty, then there exists a subset `C ⊆ interior A.dom` whose closure-subtype view is a dense
`Gδ` subset of `closure A.dom`, and such that, for every `x ∈ C`, the value `A x` is a singleton
and every selection of `A` is continuous at `x`. -/
theorem exists_dense_isGδ_singleton_selectionContinuous_locus_of_maximal_of_interior_nonempty
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A)
    (hinter : (interior A.dom).Nonempty) :
    ∃ C : Set H,
      C ⊆ interior A.dom ∧
      ∃ hDense : Dense (Subtype.val ⁻¹' C : Set (closure A.dom)),
        ∃ hIsGδ : IsGδ (Subtype.val ⁻¹' C : Set (closure A.dom)),
          ∀ x ∈ C,
            (∃ u : H, A x = ({u} : Set H)) ∧
              ∀ G : Selection A,
                SelectionContinuousAt A (fun z : A.dom ↦ (G z : H)) x := by
  let _ : CompleteSpace (closure A.dom) :=
    (isClosed_closure : IsClosed (closure A.dom)).completeSpace_coe
  let εn : ℕ → Set.Ioi (0 : ℝ) := fun n ↦
    ⟨1 / (n + 1 : ℝ), by
      have hn : (0 : ℝ) < n + 1 := by positivity
      exact one_div_pos.mpr hn⟩
  let Cn : ℕ → Set H := fun n ↦ smallDiameterNeighborhoodLocus A (εn n)
  let Csub : ℕ → Set (closure A.dom) := fun n ↦ Subtype.val ⁻¹' Cn n
  have hOpen : ∀ n, IsOpen (Csub n) := by
    intro n
    -- The ambient openness of each locus transfers directly to the closure subtype.
    exact (isOpen_smallDiameterNeighborhoodLocus A (εn n)).preimage continuous_subtype_val
  have hDense : ∀ n, Dense (Csub n) := by
    intro n
    -- Density is proved ambiently on `H` and then transported to the closure subtype.
    exact dense_preimage_smallDiameterNeighborhoodLocus_in_closure A hA hinter (εn n)
  have hBaire :
      Dense (⋂ n, Csub n) ∧ IsGδ (⋂ n, Csub n) :=
    dense_isGδ_iInter_of_dense_open Csub hOpen hDense
  let C : Set H := ⋂ n, Cn n
  refine ⟨C, ?_, ?_, ?_, ?_⟩
  · intro x hx
    -- Any one sampled locus already places the point inside `interior A.dom`.
    exact
      smallDiameterNeighborhoodLocus_subset_interior_dom A (εn 0)
        (Set.mem_iInter.mp hx 0)
  · simpa [C, Csub, Cn] using hBaire.1
  · simpa [C, Csub, Cn] using hBaire.2
  · intro x hx
    have hxCn : ∀ n, x ∈ Cn n := fun n ↦ Set.mem_iInter.mp hx n
    have hxInterior : x ∈ interior A.dom :=
      smallDiameterNeighborhoodLocus_subset_interior_dom A (εn 0) (hxCn 0)
    have hxDom : x ∈ A.dom := interior_subset hxInterior
    rcases (SetValuedOperator.mem_dom_iff A x).1 hxDom with ⟨u, hu⟩
    have hsinglex : (A x).Subsingleton := by
      intro v hv w hw
      by_contra hvw
      have hvw_pos : 0 < dist v w := dist_pos.mpr hvw
      rcases exists_nat_one_div_lt hvw_pos with ⟨n, hn⟩
      rcases hxCn n with ⟨ρ, _, hbounded, hdiam⟩
      have hρpos : 0 < (ρ : ℝ) := by
        exact ρ.2
      have hxBall : x ∈ Metric.ball x (ρ : ℝ) := by
        change dist x x < (ρ : ℝ)
        simpa using hρpos
      have hvImage : v ∈ A.image (Metric.ball x (ρ : ℝ)) := by
        exact (SetValuedOperator.mem_image A (Metric.ball x (ρ : ℝ)) v).2 ⟨x, hxBall, hv⟩
      have hwImage : w ∈ A.image (Metric.ball x (ρ : ℝ)) := by
        exact (SetValuedOperator.mem_image A (Metric.ball x (ρ : ℝ)) w).2 ⟨x, hxBall, hw⟩
      have hdist_le :
          dist v w ≤ Metric.diam (A.image (Metric.ball x (ρ : ℝ))) :=
        Metric.dist_le_diam_of_mem hbounded hvImage hwImage
      exact not_lt_of_ge hdist_le (lt_trans hdiam hn)
    refine ⟨⟨u, Set.Subsingleton.eq_singleton_of_mem hsinglex hu⟩, ?_⟩
    intro G hxdom'
    let x0 : A.dom := ⟨x, hxdom'⟩
    have hcont0 : ContinuousAt (fun z : A.dom ↦ (G z : H)) x0 := by
      -- The defining small-diameter neighborhood for a sufficiently fine sampled tolerance
      -- simultaneously controls `G z` and `G x`.
      rw [Metric.continuousAt_iff]
      intro ε hε
      rcases exists_nat_one_div_lt hε with ⟨n, hn⟩
      rcases hxCn n with ⟨ρ, _, hbounded, hdiam⟩
      refine ⟨ρ, by
        change 0 < (ρ : ℝ)
        exact ρ.2, ?_⟩
      intro z hz
      have hρpos : 0 < (ρ : ℝ) := by
        exact ρ.2
      have hzBall : (z : H) ∈ Metric.ball x (ρ : ℝ) := by
        simpa [Metric.mem_ball, Subtype.dist_eq, x0] using hz
      have hxBall : x ∈ Metric.ball x (ρ : ℝ) := by
        change dist x x < (ρ : ℝ)
        simpa using hρpos
      have hGz : (G z : H) ∈ A.image (Metric.ball x (ρ : ℝ)) := by
        exact
          (SetValuedOperator.mem_image A (Metric.ball x (ρ : ℝ)) (G z : H)).2
            ⟨(z : H), hzBall, selection_apply_mem G z⟩
      have hGx : (G x0 : H) ∈ A.image (Metric.ball x (ρ : ℝ)) := by
        exact
          (SetValuedOperator.mem_image A (Metric.ball x (ρ : ℝ)) (G x0 : H)).2
            ⟨x, hxBall, selection_apply_mem G x0⟩
      calc
        dist (G z : H) (G x0 : H)
            ≤ Metric.diam (A.image (Metric.ball x (ρ : ℝ))) :=
          Metric.dist_le_diam_of_mem hbounded hGz hGx
        _ < (εn n : ℝ) := hdiam
        _ < ε := hn
    -- Transport continuity back to the requested domain point over `x`.
    simpa [x0] using hcont0

end SetValuedOperator
