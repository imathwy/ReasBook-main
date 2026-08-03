import BauschkeLean.Chap02.Lemma_2_51
import BauschkeLean.Chap03.Corollary_3_35
import BauschkeLean.Chap03.Definition_3_8
import BauschkeLean.Chap04.Proposition_4_19
import BauschkeLean.Chap20.Corollary_20_59
import BauschkeLean.Chap20.Definition_20_1

-- Declarations for this item will be appended below by the statement pipeline.

open EuclideanGeometry
open Filter
open scoped InnerProductSpace SetValuedOperator Topology

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

section

variable {C D : AffineSubspace ℝ H}
variable (hC_nonempty : (C : Set H).Nonempty) (hC_closed : IsClosed (C : Set H))
variable (hD_nonempty : (D : Set H).Nonempty) (hD_closed : IsClosed (D : Set H))

local notation "hC" =>
  isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed C.convex

local notation "hD" =>
  isChebyshev_of_nonempty_isClosed_convex hD_nonempty hD_closed D.convex

/- Source/core/bridge triage:
- `source-facing`: Proposition 20.60 is the weak-graph convergence statement with asymptotic
  membership in the affine subspaces `C` and `D`.
- `core/canonical`: the owner abstraction is maximal monotonicity
  `Maximal SetValuedOperator.IsMonotone A` together with graph membership in `gra A`.
- `bridge/view`: the affine-subspace compatibility condition `D.direction = C.directionᗮ` is the
  Lean form of the textbook identity `D - D = (C - C)ᗮ`. -/

-- Semantic recall: semantic search only surfaced generic order-theoretic monotonicity owners, and
-- local Chapter 20 precedent uses the public predicate `SetValuedOperator.IsMonotone`, so this
-- file keeps the source-facing affine-subspace statement shape with that canonical owner.
-- `Corollary 3.35` supplies membership of weak limits in closed convex sets, `Proposition 4.19`
-- gives weak continuity of affine metric projections, and `Corollary 20.59` turns the pairing
-- limit into graph membership for maximally monotone operators.
/-- Helper for Proposition 20.60: subtracting a strongly null residual does not change the weak
limit of a sequence in a real Hilbert space. -/
private lemma tendsto_weakly_of_sub_tendsto_zero
    {aSeq bSeq : ℕ → H} {a : H}
    (ha :
      Tendsto (fun n ↦ toWeakSpace ℝ H (aSeq n)) atTop
        (𝓝 (toWeakSpace ℝ H a)))
    (hsub : Tendsto (fun n ↦ aSeq n - bSeq n) atTop (𝓝 (0 : H))) :
    Tendsto (fun n ↦ toWeakSpace ℝ H (bSeq n)) atTop
      (𝓝 (toWeakSpace ℝ H a)) := by
  -- Send the strong residual convergence through `toWeakSpace`, then subtract in `WeakSpace`.
  have hsubWeak :
      Tendsto (fun n ↦ toWeakSpace ℝ H (aSeq n - bSeq n)) atTop
        (𝓝 (toWeakSpace ℝ H (0 : H))) := by
    simpa [toWeakSpaceCLM_eq_toWeakSpace] using
      ((toWeakSpaceCLM ℝ H).continuous.tendsto (0 : H)).comp hsub
  simpa [sub_sub_cancel] using ha.sub hsubWeak

/-- Helper for Proposition 20.60: if the projection residuals onto a nonempty closed affine
subspace converge strongly to `0`, then the weak limit lies in that affine subspace. -/
private lemma mem_of_projection_residual_tendsto_zero_of_tendsto_weakly
    {xSeq : ℕ → H} {x : H}
    (hxSeq :
      Tendsto (fun n ↦ toWeakSpace ℝ H (xSeq n)) atTop
        (𝓝 (toWeakSpace ℝ H x)))
    (hproj : Tendsto (fun n ↦ xSeq n - P[C, hC] (xSeq n)) atTop (𝓝 (0 : H))) :
    x ∈ (C : Set H) := by
  let pSeq : ℕ → H := fun n ↦ P[C, hC] (xSeq n)
  -- The projected sequence stays in `C` and keeps the same weak limit.
  have hpMem : ∀ n, pSeq n ∈ (C : Set H) := by
    intro n
    simpa [pSeq] using projectionPoint_mem C hC (xSeq n)
  have hpWeak :
      Tendsto (fun n ↦ toWeakSpace ℝ H (pSeq n)) atTop
        (𝓝 (toWeakSpace ℝ H x)) :=
    tendsto_weakly_of_sub_tendsto_zero hxSeq <| by simpa [pSeq] using hproj
  exact mem_of_tendsto_weakly_of_isClosed_convex hC_closed C.convex hpMem hpWeak

/-- Helper for Proposition 20.60: points in affine subspaces whose direction spaces are orthogonal
split the inner product at the anchor points. -/
private lemma inner_eq_inner_anchor_split_of_mem_orthogonal_affine_subspaces
    {x u c d : H}
    (hx : x ∈ (C : Set H)) (hu : u ∈ (D : Set H))
    (hc : c ∈ (C : Set H)) (hd : d ∈ (D : Set H))
    (hCD : D.direction = C.directionᗮ) :
    ⟪c, d⟫_ℝ = ⟪c, u⟫_ℝ + ⟪x, d⟫_ℝ - ⟪x, u⟫_ℝ := by
  have hc_dir : c - x ∈ C.direction := by
    simpa [vsub_eq_sub] using C.vsub_mem_direction hc hx
  have hd_orth : d - u ∈ C.directionᗮ := by
    simpa [hCD, vsub_eq_sub] using D.vsub_mem_direction hd hu
  have horth : ⟪c - x, d - u⟫_ℝ = 0 :=
    Submodule.inner_right_of_mem_orthogonal hc_dir hd_orth
  -- Expand at the anchors `x` and `u`, and the mixed term vanishes by orthogonality.
  calc
    ⟪c, d⟫_ℝ = ⟪c, d - u + u⟫_ℝ := by rw [sub_add_cancel]
    _ = ⟪c, d - u⟫_ℝ + ⟪c, u⟫_ℝ := by rw [inner_add_right]
    _ = ⟪c - x + x, d - u⟫_ℝ + ⟪c, u⟫_ℝ := by rw [sub_add_cancel]
    _ = (⟪c - x, d - u⟫_ℝ + ⟪x, d - u⟫_ℝ) + ⟪c, u⟫_ℝ := by
          rw [inner_add_left]
    _ = ⟪x, d - u⟫_ℝ + ⟪c, u⟫_ℝ := by rw [horth, zero_add]
    _ = (⟪x, d⟫_ℝ - ⟪x, u⟫_ℝ) + ⟪c, u⟫_ℝ := by rw [inner_sub_right]
    _ = ⟪c, u⟫_ℝ + ⟪x, d⟫_ℝ - ⟪x, u⟫_ℝ := by ring

/-- Helper for Proposition 20.60: once the projected sequences stay in orthogonal affine
subspaces, weak convergence of each coordinate already gives convergence of their pairings. -/
private lemma tendsto_inner_of_tendsto_weakly_in_orthogonal_affine_subspaces
    {x u : H} {cSeq dSeq : ℕ → H}
    (hcSeq :
      Tendsto (fun n ↦ toWeakSpace ℝ H (cSeq n)) atTop
        (𝓝 (toWeakSpace ℝ H x)))
    (hdSeq :
      Tendsto (fun n ↦ toWeakSpace ℝ H (dSeq n)) atTop
        (𝓝 (toWeakSpace ℝ H u)))
    (hcMem : ∀ n, cSeq n ∈ (C : Set H))
    (hdMem : ∀ n, dSeq n ∈ (D : Set H))
    (hx : x ∈ (C : Set H)) (hu : u ∈ (D : Set H))
    (hCD : D.direction = C.directionᗮ) :
    Tendsto (fun n ↦ ⟪cSeq n, dSeq n⟫_ℝ) atTop (𝓝 ⟪x, u⟫_ℝ) := by
  have hcInner :
      Tendsto (fun n ↦ ⟪cSeq n, u⟫_ℝ) atTop (𝓝 ⟪x, u⟫_ℝ) := by
    -- Keep the second slot fixed and use weak continuity in the first coordinate.
    simpa using ((weakSpace_continuous_inner_right u).tendsto (toWeakSpace ℝ H x)).comp hcSeq
  have hdInner :
      Tendsto (fun n ↦ ⟪x, dSeq n⟫_ℝ) atTop (𝓝 ⟪x, u⟫_ℝ) := by
    -- Swap the arguments so the same weak continuity lemma applies.
    simpa [real_inner_comm] using
      ((weakSpace_continuous_inner_right x).tendsto (toWeakSpace ℝ H u)).comp hdSeq
  have hsplit :
      Tendsto
        (fun n ↦ ⟪cSeq n, u⟫_ℝ + ⟪x, dSeq n⟫_ℝ - ⟪x, u⟫_ℝ)
        atTop (𝓝 (⟪x, u⟫_ℝ + ⟪x, u⟫_ℝ - ⟪x, u⟫_ℝ)) := by
    exact (hcInner.add hdInner).sub tendsto_const_nhds
  -- Rewrite each projected pairing by the anchor-splitting identity.
  have hrewrite :
      (fun n ↦ ⟪cSeq n, dSeq n⟫_ℝ) =
        (fun n ↦ ⟪cSeq n, u⟫_ℝ + ⟪x, dSeq n⟫_ℝ - ⟪x, u⟫_ℝ) := by
    funext n
    exact inner_eq_inner_anchor_split_of_mem_orthogonal_affine_subspaces
      hx hu (hcMem n) (hdMem n) hCD
  rw [hrewrite]
  simpa using hsplit

/-- Helper for Proposition 20.60: the projection residual hypotheses force the weak limit pair
into `C × D` and yield convergence of the inner products. -/
private theorem mem_and_tendsto_inner_of_projection_residual_zero_of_tendsto_weakly_seq
    (hCD : D.direction = C.directionᗮ)
    {xSeq uSeq : ℕ → H} {x u : H}
    (hxSeq :
      Tendsto (fun n ↦ toWeakSpace ℝ H (xSeq n)) atTop
        (𝓝 (toWeakSpace ℝ H x)))
    (huSeq :
      Tendsto (fun n ↦ toWeakSpace ℝ H (uSeq n)) atTop
        (𝓝 (toWeakSpace ℝ H u)))
    (hCproj : Tendsto (fun n ↦ xSeq n - P[C, hC] (xSeq n)) atTop (𝓝 (0 : H)))
    (hDproj : Tendsto (fun n ↦ uSeq n - P[D, hD] (uSeq n)) atTop (𝓝 (0 : H))) :
    x ∈ (C : Set H) ∧ u ∈ (D : Set H) ∧
      Tendsto (fun n ↦ ⟪xSeq n, uSeq n⟫_ℝ) atTop (𝓝 ⟪x, u⟫_ℝ) := by
  let cSeq : ℕ → H := fun n ↦ P[C, hC] (xSeq n)
  let dSeq : ℕ → H := fun n ↦ P[D, hD] (uSeq n)
  -- First recover that the weak limits lie in the affine subspaces.
  have hx : x ∈ (C : Set H) :=
    mem_of_projection_residual_tendsto_zero_of_tendsto_weakly
      (hC_nonempty := hC_nonempty) (hC_closed := hC_closed) hxSeq hCproj
  have hu : u ∈ (D : Set H) :=
    mem_of_projection_residual_tendsto_zero_of_tendsto_weakly
      (C := D)
      (hC_nonempty := hD_nonempty) (hC_closed := hD_closed) huSeq hDproj
  have hcSeq :
      Tendsto (fun n ↦ toWeakSpace ℝ H (cSeq n)) atTop
        (𝓝 (toWeakSpace ℝ H x)) :=
    tendsto_weakly_of_sub_tendsto_zero hxSeq <| by simpa [cSeq] using hCproj
  have hdSeq :
      Tendsto (fun n ↦ toWeakSpace ℝ H (dSeq n)) atTop
        (𝓝 (toWeakSpace ℝ H u)) :=
    tendsto_weakly_of_sub_tendsto_zero huSeq <| by simpa [dSeq] using hDproj
  have hcMem : ∀ n, cSeq n ∈ (C : Set H) := by
    intro n
    simpa [cSeq] using projectionPoint_mem C hC (xSeq n)
  have hdMem : ∀ n, dSeq n ∈ (D : Set H) := by
    intro n
    simpa [dSeq] using projectionPoint_mem D hD (uSeq n)
  -- The projected terms already satisfy the source orthogonal-affine pairing identity.
  have hprojInner :
      Tendsto (fun n ↦ ⟪cSeq n, dSeq n⟫_ℝ) atTop (𝓝 ⟪x, u⟫_ℝ) :=
    tendsto_inner_of_tendsto_weakly_in_orthogonal_affine_subspaces
      (C := C) (D := D) hcSeq hdSeq hcMem hdMem hx hu hCD
  have hResidualLeft :
      Tendsto (fun n ↦ ⟪cSeq n, uSeq n - dSeq n⟫_ℝ) atTop (𝓝 (0 : ℝ)) := by
    -- The `D`-residual tends strongly to `0`, so its pairing with the weakly convergent
    -- projected `C`-sequence vanishes.
    simpa [dSeq] using
      tendsto_inner_of_tendsto_weakly_of_tendsto cSeq
        (fun n ↦ uSeq n - dSeq n) x 0 hcSeq <| by
          simpa [dSeq] using hDproj
  have hResidualRight :
      Tendsto (fun n ↦ ⟪xSeq n - cSeq n, uSeq n⟫_ℝ) atTop (𝓝 (0 : ℝ)) := by
    -- Apply the same weak-strong pairing lemma after swapping the inner-product arguments.
    simpa [cSeq, real_inner_comm] using
      tendsto_inner_of_tendsto_weakly_of_tendsto uSeq
        (fun n ↦ xSeq n - cSeq n) u 0 huSeq <| by
          simpa [cSeq] using hCproj
  have hsplit :
      Tendsto
        (fun n ↦
          ⟪cSeq n, dSeq n⟫_ℝ +
            ⟪cSeq n, uSeq n - dSeq n⟫_ℝ +
              ⟪xSeq n - cSeq n, uSeq n⟫_ℝ)
        atTop (𝓝 (⟪x, u⟫_ℝ + 0 + 0)) :=
    (hprojInner.add hResidualLeft).add hResidualRight
  -- Expand the original pairing into the projected term plus the two residual errors.
  have hrewrite :
      (fun n ↦ ⟪xSeq n, uSeq n⟫_ℝ) =
        (fun n ↦
          ⟪cSeq n, dSeq n⟫_ℝ +
            ⟪cSeq n, uSeq n - dSeq n⟫_ℝ +
              ⟪xSeq n - cSeq n, uSeq n⟫_ℝ) := by
    funext n
    have huDecomp :
        ⟪cSeq n, uSeq n⟫_ℝ = ⟪cSeq n, dSeq n + (uSeq n - dSeq n)⟫_ℝ := by
      congr 1
      abel_nf
    calc
      ⟪xSeq n, uSeq n⟫_ℝ = ⟪cSeq n + (xSeq n - cSeq n), uSeq n⟫_ℝ := by abel_nf
      _ = ⟪cSeq n, uSeq n⟫_ℝ + ⟪xSeq n - cSeq n, uSeq n⟫_ℝ := by rw [inner_add_left]
      _ = ⟪cSeq n, dSeq n + (uSeq n - dSeq n)⟫_ℝ +
            ⟪xSeq n - cSeq n, uSeq n⟫_ℝ := by
            rw [huDecomp]
      _ = (⟪cSeq n, dSeq n⟫_ℝ + ⟪cSeq n, uSeq n - dSeq n⟫_ℝ) +
            ⟪xSeq n - cSeq n, uSeq n⟫_ℝ := by
            rw [inner_add_right]
      _ = ⟪cSeq n, dSeq n⟫_ℝ +
            ⟪cSeq n, uSeq n - dSeq n⟫_ℝ +
              ⟪xSeq n - cSeq n, uSeq n⟫_ℝ := by ring
  refine ⟨hx, hu, ?_⟩
  rw [hrewrite]
  simpa using hsplit

/-- Proposition 20.60 (1): let `C` and `D` be nonempty closed affine subspaces of `H` such that
`D.direction = C.directionᗮ`, let `A : SetValuedOperator H H` be maximally monotone, and let
`(xSeq n, uSeq n)` be a sequence in `gra A` converging weakly to `(x, u)`. If
`xSeq n - P[C, hC] (xSeq n) → 0` and `uSeq n - P[D, hD] (uSeq n) → 0`, then
`(x, u) ∈ ((C : Set H) ×ˢ (D : Set H)) ∩ gra A`. -/
theorem Maximal.mem_prod_inter_graph_of_projection_residual_zero_of_tendsto_weakly_seq
    {A : SetValuedOperator H H} (hA : Maximal SetValuedOperator.IsMonotone A)
    (hCD : D.direction = C.directionᗮ)
    {xSeq uSeq : ℕ → H} {x u : H}
    (hgraph : ∀ n, (xSeq n, uSeq n) ∈ gra A)
    (hxSeq : Tendsto (fun n ↦ toWeakSpace ℝ H (xSeq n)) atTop (𝓝 (toWeakSpace ℝ H x)))
    (huSeq : Tendsto (fun n ↦ toWeakSpace ℝ H (uSeq n)) atTop (𝓝 (toWeakSpace ℝ H u)))
    (hCproj : Tendsto (fun n ↦ xSeq n - P[C, hC] (xSeq n)) atTop (𝓝 (0 : H)))
    (hDproj : Tendsto (fun n ↦ uSeq n - P[D, hD] (uSeq n)) atTop (𝓝 (0 : H))) :
    (x, u) ∈ ((C : Set H) ×ˢ (D : Set H)) ∩ gra A := by
  -- Recover affine-subspace membership and the pairing limit from the projection residuals.
  obtain ⟨hx, hu, hinner⟩ :=
    mem_and_tendsto_inner_of_projection_residual_zero_of_tendsto_weakly_seq
      (C := C) (D := D)
      (hC_nonempty := hC_nonempty) (hC_closed := hC_closed)
      (hD_nonempty := hD_nonempty) (hD_closed := hD_closed)
      hCD hxSeq huSeq hCproj hDproj
  have hlimsup :
      limsup (fun n ↦ ⟪xSeq n, uSeq n⟫_ℝ) atTop ≤ ⟪x, u⟫_ℝ := by
    simpa using hinner.limsup_eq.le
  -- Corollary 20.59 then upgrades the pairing limit to graph membership of the weak limit.
  have hgraphLimit :
      (x, u) ∈ gra A :=
    Maximal.mem_graph_of_limsup_inner_le_of_tendsto_weakly_seq
      (A := A) hA hgraph hxSeq huSeq hlimsup
  exact ⟨⟨hx, hu⟩, hgraphLimit⟩

/-- Proposition 20.60 (2): under the same hypotheses, the pairings satisfy
`⟪xSeq n, uSeq n⟫_ℝ → ⟪x, u⟫_ℝ`. -/
theorem Maximal.tendsto_inner_of_projection_residual_zero_of_tendsto_weakly_seq
    {A : SetValuedOperator H H} (hA : Maximal SetValuedOperator.IsMonotone A)
    (hCD : D.direction = C.directionᗮ)
    {xSeq uSeq : ℕ → H} {x u : H}
    (hgraph : ∀ n, (xSeq n, uSeq n) ∈ gra A)
    (hxSeq : Tendsto (fun n ↦ toWeakSpace ℝ H (xSeq n)) atTop (𝓝 (toWeakSpace ℝ H x)))
    (huSeq : Tendsto (fun n ↦ toWeakSpace ℝ H (uSeq n)) atTop (𝓝 (toWeakSpace ℝ H u)))
    (hCproj : Tendsto (fun n ↦ xSeq n - P[C, hC] (xSeq n)) atTop (𝓝 (0 : H)))
    (hDproj : Tendsto (fun n ↦ uSeq n - P[D, hD] (uSeq n)) atTop (𝓝 (0 : H))) :
    Tendsto (fun n ↦ ⟪xSeq n, uSeq n⟫_ℝ) atTop (𝓝 ⟪x, u⟫_ℝ) := by
  let _ := hA
  let _ := hgraph
  -- Reuse the source-faithful decomposition proved in the common helper theorem.
  exact
    (mem_and_tendsto_inner_of_projection_residual_zero_of_tendsto_weakly_seq
      (C := C) (D := D)
      (hC_nonempty := hC_nonempty) (hC_closed := hC_closed)
      (hD_nonempty := hD_nonempty) (hD_closed := hD_closed)
      hCD hxSeq huSeq hCproj hDproj).2.2

end

end SetValuedOperator
