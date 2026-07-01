import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Rockafellar

/-
Source/core/bridge triage:
- `source-facing`: Text 6.4 records that the chapter unit ball `B` is closed and convex.
- `core/canonical`: the owner object is `closedBall (0 : E) 1`, with derived owner facts
  `Metric.isClosed_closedBall`; convexity is a derived property from the norm inequality at the
  primitive real-scalar action layer.
- `bridge/view`: Text 6.3 already provides the source-facing chapter notation `B` directly for the
  canonical owner `closedBall (0 : E) 1`, so this file states the textbook facts in that notation.
- Primitive data vs derived API: `B` is the only primitive object here; closedness and convexity
  are derived properties and should remain theorem-level API.
- Domain-style sampling used here: the source-facing chapter notation `B` from Text 6.3, the
  canonical owner `closedBall`, `Metric.isClosed_closedBall`, and the primitive norm inequalities
  `norm_add_le` and `norm_smul`.
- Owner choice: keep `closedBall` as the canonical owner and expose source-facing theorem surfaces
  through the chapter notation `B`.
- Layer target: source-facing theorem API over the canonical owner.
-/

section

variable {E : Type*} [PseudoMetricSpace E] [Zero E]

/- Owner-level closedness for Text 6.4: the canonical unit closed ball `closedBall (0 : E) 1`
is closed at the primitive pseudometric layer. -/
private theorem isClosed_unitClosedBall : IsClosed (Metric.closedBall (0 : E) (1 : ℝ)) := by
  simpa using (Metric.isClosed_closedBall : IsClosed (Metric.closedBall (0 : E) (1 : ℝ)))

/- Text 6.4 source-facing bridge: the chapter notation `B` for the unit closed ball is closed. -/
theorem isClosed_B : IsClosed (B : Set E) := by
  simpa [B_eq_closedBall] using (isClosed_unitClosedBall (E := E))

end

section

variable {E : Type*} [SeminormedAddCommGroup E] [SMul ℝ E] [NormSMulClass ℝ E]

/- Owner-level convexity for Text 6.4: the canonical unit closed ball `closedBall (0 : E) 1`
is convex. This only needs real scalar action and `norm_smul`. -/
private theorem convex_unitClosedBall : Convex ℝ (Metric.closedBall (0 : E) (1 : ℝ)) := by
  intro x hx y hy a b ha hb hab
  have hx' : ‖x‖ ≤ (1 : ℝ) := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hx
  have hy' : ‖y‖ ≤ (1 : ℝ) := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hy
  have hnorm : ‖a • x + b • y‖ ≤ (1 : ℝ) := by
    calc
      ‖a • x + b • y‖ ≤ ‖a • x‖ + ‖b • y‖ := norm_add_le _ _
      _ = ‖a‖ * ‖x‖ + ‖b‖ * ‖y‖ := by rw [norm_smul, norm_smul]
      _ = a * ‖x‖ + b * ‖y‖ := by rw [Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      _ ≤ a * 1 + b * 1 := by gcongr
      _ = 1 := by linarith [hab]
  simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm

/- Text 6.4 source-facing bridge: the chapter notation `B` for the unit closed ball is convex. -/
theorem convex_B : Convex ℝ (B : Set E) := by
  simpa [B_eq_closedBall] using (convex_unitClosedBall (E := E))

end
