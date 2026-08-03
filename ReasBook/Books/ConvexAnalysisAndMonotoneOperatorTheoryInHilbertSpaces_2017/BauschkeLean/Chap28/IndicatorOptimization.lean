import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap12.Corollary_12_31

universe u

namespace ERealFunction

section IndicatorProjection

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- For a nonempty closed convex set `C`, the scaled proximal operator of its indicator is the
metric projection onto `C`. This is the Chapter 28 bridge from proximal notation to the projector
notation used in projected algorithms. -/
theorem proxIndicator_eq_projectionPoint_of_nonempty_isClosed_convex
    {C : Set H} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (γ : PosReal) :
    Prox[γ, ι[C],
      indicator_mem_gammaZero_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex] =
        P[C, isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex] := by
  have hsmul_indicator : γ • ι[C] = ι[C] := by
    funext z
    apply Subtype.ext
    by_cases hz : z ∈ C
    · simp [ERealFunction.indicator, hz]
    · simpa [ERealFunction.indicator, hz] using
        (EReal.coe_mul_top_of_pos γ.2 : ((γ : ℝ) : EReal) * ⊤ = ⊤)
  change
      Prox[γ • ι[C],
        smul_mem_gammaZero (ι[C])
          (indicator_mem_gammaZero_of_nonempty_isClosed_convex
            hC_nonempty hC_closed hC_convex)
          γ] =
      P[C, isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex]
  ext z
  simpa [hsmul_indicator] using
    congrArg (fun T : H → H ↦ T z) <|
      proximityOperator_indicator_eq_projectionPoint_of_nonempty_isClosed_convex
        hC_nonempty hC_closed hC_convex

end IndicatorProjection

/-- Constrained minimizers of an `EReal`-valued objective coming from
`g : X → Set.Ioi (⊥ : EReal)` are exactly the feasible global minimizers of `ι[C] + g`. -/
theorem argminOn_asEReal_eq_inter_argmin_indicator_add
    {X : Type u} (g : X → Set.Ioi (⊥ : EReal)) (C : Set X) :
    (Argmin[C] g.asEReal : Set X) = C ∩ Argmin ((ι[C] + g).asEReal) := by
  simpa [Function.asEReal_apply, add_comm, add_left_comm, add_assoc] using
    (argminOn_eq_inter_argmin_add_indicator
      g.asEReal
      C
      (fun x _ ↦ ne_of_gt (g x).2))

/-- Real-valued constrained minimizers are exactly the feasible global minimizers of the indicator
augmented objective `(ι[C] + f.toEReal).asEReal`. -/
theorem argminOn_toEReal_eq_inter_argmin_indicator_add
    {X : Type u} (f : X → ℝ) (C : Set X) :
    (Argmin[C] f.toEReal.asEReal : Set X) = C ∩ Argmin ((ι[C] + f.toEReal).asEReal) := by
  simpa using argminOn_asEReal_eq_inter_argmin_indicator_add (f.toEReal) C

end ERealFunction
