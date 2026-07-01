import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Add
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_5_24_3
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_5_24_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators Rockafellar SetRel

universe u v

section

variable {𝕜 : Type v} [AddCommMonoid 𝕜] [Preorder 𝕜]
variable [AddLeftMono 𝕜] [AddRightMono 𝕜] [AddRightReflectLE 𝕜]
variable {E : Type u} [Sub E]

/-- Primitive cyclic inequality for subgradient cycles: if each `xStar i` is a subgradient of `f`
at `x i`, then the cyclic pairing sum is nonpositive. This is the owner-level inequality behind
cyclic monotonicity of the subdifferential graph. -/
theorem sum_nonpos_of_subgradient_cycle
    {f : E → WithTopBot 𝕜} {Y : Type (max u v)} [HasPairing E Y 𝕜]
    {m : ℕ} {x : Fin (m + 1) → E} {xStar : Fin (m + 1) → Y}
    (hf : f.IsProper) (hx : ∀ i, xStar i ∈ ∂[Y]f(x i)) :
    ∑ i : Fin (m + 1), ⟪x (i + 1) - x i, xStar i⟫ₚ ≤ (0 : 𝕜) := by
  rcases hf.nonempty_dom with ⟨y, hy⟩
  have hsub :
      ∀ i z, f z ≥ f (x i) + (((⟪z - x i, xStar i⟫ₚ : 𝕜)) : WithTopBot 𝕜) := by
    intro i z
    exact (mem_subdifferentialAt_pairing.mp (hx i)) z
  have hx_top : ∀ i, f (x i) ≠ ⊤ := by
    intro i htop
    have hsub_y :
        f y ≥ f (x i) + (((⟪y - x i, xStar i⟫ₚ : 𝕜)) : WithTopBot 𝕜) := by
      simpa using hsub i y
    have htop_le_aux :
        (⊤ : WithTopBot 𝕜) + (((⟪y - x i, xStar i⟫ₚ : 𝕜)) : WithTopBot 𝕜) ≤ f y := by
      simpa [htop] using hsub_y
    have htop_le : (⊤ : WithTopBot 𝕜) ≤ f y := by
      calc
        (⊤ : WithTopBot 𝕜) =
            (⊤ : WithTopBot 𝕜) + (((⟪y - x i, xStar i⟫ₚ : 𝕜) : WithTopBot 𝕜)) := by
              simp
        _ ≤ f y := htop_le_aux
    exact (not_le_of_gt hy) htop_le
  have hx_bot : ∀ i, f (x i) ≠ ⊥ := fun i ↦ hf.ne_bot (x i)
  have hx_finite : ∀ i, ∃ v : 𝕜, ((v : 𝕜) : WithTopBot 𝕜) = f (x i) := by
    intro i
    rcases (WithBotTop.canLift_iff_ne_top_ne_bot).2 ⟨hx_top i, hx_bot i⟩ with ⟨v, hv⟩
    exact ⟨v, hv⟩
  choose v hv using hx_finite
  let Δ : Fin (m + 1) → 𝕜 := fun i ↦ ⟪x (i + 1) - x i, xStar i⟫ₚ
  have hstep : ∀ i, v i + Δ i ≤ v (i + 1) := by
    intro i
    have hsub_step :
        f (x (i + 1)) ≥
          f (x i) + (((Δ i : 𝕜)) : WithTopBot 𝕜) := by
      simpa [Δ] using hsub i (x (i + 1))
    have hsub' :
        ((v i : 𝕜) : WithTopBot 𝕜) + (((Δ i : 𝕜)) : WithTopBot 𝕜) ≤
          ((v (i + 1) : 𝕜) : WithTopBot 𝕜) := by
      calc
        ((v i : 𝕜) : WithTopBot 𝕜) +
              (((Δ i : 𝕜)) : WithTopBot 𝕜)
            = f (x i) + (((Δ i : 𝕜)) : WithTopBot 𝕜) := by rw [hv i]
        _ ≤ f (x (i + 1)) := hsub_step
        _ = ((v (i + 1) : 𝕜) : WithTopBot 𝕜) := by rw [hv (i + 1)]
    have hsub'' :
        ((v i + Δ i : 𝕜) : WithTopBot 𝕜) ≤
          ((v (i + 1) : 𝕜) : WithTopBot 𝕜) := by
      simpa [WithBotTop.coe_add] using hsub'
    exact (WithBotTop.coe_le_coe).1 hsub''
  have hshift :
      ∑ i : Fin (m + 1), v (i + 1) = ∑ i : Fin (m + 1), v i := by
    simpa using
      (Fintype.sum_equiv (Equiv.addRight (1 : Fin (m + 1)))
        (fun i ↦ v (i + 1)) (fun i ↦ v i) fun i ↦ rfl)
  have hsum_nonpos :
      ∑ i : Fin (m + 1), Δ i + ∑ i : Fin (m + 1), v i ≤
        ∑ i : Fin (m + 1), v i := by
    calc
      ∑ i : Fin (m + 1), Δ i + ∑ i : Fin (m + 1), v i
          = ∑ i : Fin (m + 1), (v i + Δ i) := by
            rw [add_comm]
            symm
            rw [Finset.sum_add_distrib]
      _ ≤ ∑ i : Fin (m + 1), v (i + 1) := by
            exact Finset.sum_le_sum (fun i _ ↦ hstep i)
      _ = ∑ i : Fin (m + 1), v i := hshift
  exact (add_le_iff_nonpos_left).1 hsum_nonpos

/-- Proposition 5.24.3: the subdifferential graph relation is cyclically monotone. The theorem is
stated on the intrinsic pairing-defined graph relation
`{p : E × Y | p.2 ∈ ∂[Y]f(p.1)}`, which is definitionally the same relation as `gph∂[Y](f)` when
the Chapter 5 graph owner is available. -/
theorem subdifferentialGraph_cyclicallyMonotone
    {f : E → WithTopBot 𝕜} {Y : Type (max u v)} [HasPairing E Y 𝕜]
    (hf : f.IsProper) :
    CMon[𝕜](({p : E × Y | p.2 ∈ ∂[Y]f(p.1)} : SetRel E Y)) := by
  refine ⟨fun m x xStar hx ↦ ?_⟩
  exact sum_nonpos_of_subgradient_cycle (hf := hf)
    (x := x) (xStar := xStar)
    (fun i ↦ by simpa using hx i)

end
