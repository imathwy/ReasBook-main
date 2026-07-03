

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_10_15 (from Items/Chap10) -/
open MeasureTheory

universe u v

variable {Ω : Type u} {ι : Type v}
variable [mΩ : MeasurableSpace Ω] [LinearOrder ι] [Countable ι] [Nonempty ι]
variable {μ : Measure Ω} {ℱ : Filtration ι mΩ} [SigmaFiniteFiltration μ ℱ]
variable {X : ι → Ω → ℝ} {τ : Ω → WithTop ι}

/- Theorem 10.15 is `source-facing`: its public statement stays on the chapter's stopped-process
and stopped-filtration layer from Definition 10.13 for a countable time index set. The discrete
owner theorem `Submartingale.stoppedProcess` is used only as an internal bridge after reindexing to
an appropriate discrete model of the time set, not as the public theorem statement itself. -/

/- Internal `bridge/view`: the submartingale case is the owner-shaped core in this file. The
martingale and supermartingale clauses are derived from it through the canonical API
`martingale_iff` and negation. -/
private theorem stoppedProcess_submartingale
    (hX : Submartingale X ℱ μ) (hτ : IsStoppingTime ℱ τ) :
    Submartingale (stoppedProcess X τ) ℱ μ ∧
      Submartingale (stoppedProcess X τ) (stoppedFiltration ℱ hτ) μ := by
  sorry

omit mΩ [Countable ι] in
private theorem neg_stoppedProcess_neg :
    -stoppedProcess (-X) τ = stoppedProcess X τ := by
  ext i ω
  simp [stoppedProcess]

-- Proof sketch: apply the core stopped-submartingale bridge to `X` and to `-X`, then recover the
-- martingale conclusion by the canonical characterization `martingale_iff`.
/-- Theorem 10.15 (1): if `X` is a martingale and `τ` is a stopping time, then the stopped process
`X^τ` is again a martingale both for the ambient filtration `ℱ` and for the stopped filtration
`ℱ^τ`. -/
theorem martingale_stoppedProcess (hX : Martingale X ℱ μ) (hτ : IsStoppingTime ℱ τ) :
    Martingale (stoppedProcess X τ) ℱ μ ∧
      Martingale (stoppedProcess X τ) (stoppedFiltration ℱ hτ) μ := by
  have hsub :
      Submartingale (stoppedProcess X τ) ℱ μ ∧
        Submartingale (stoppedProcess X τ) (stoppedFiltration ℱ hτ) μ :=
    stoppedProcess_submartingale hX.submartingale hτ
  have hsuper :
      Submartingale (stoppedProcess (-X) τ) ℱ μ ∧
        Submartingale (stoppedProcess (-X) τ) (stoppedFiltration ℱ hτ) μ :=
    stoppedProcess_submartingale hX.neg.submartingale hτ
  refine ⟨?_, ?_⟩
  · exact (martingale_iff).2 ⟨by simpa [neg_stoppedProcess_neg] using hsuper.1.neg, hsub.1⟩
  · exact (martingale_iff).2 ⟨by simpa [neg_stoppedProcess_neg] using hsuper.2.neg, hsub.2⟩

-- Proof sketch: this is the owner-shaped core source-facing bridge. For the ambient filtration it
-- reduces to the canonical stopped-submartingale theorem after discrete reindexing; the stopped
-- filtration clause is the matching bridge for Definition 10.13.
/-- Theorem 10.15 (2): if `X` is a submartingale and `τ` is a stopping time, then the stopped
process `X^τ` is again a submartingale both for the ambient filtration `ℱ` and for the stopped
filtration `ℱ^τ`. -/
theorem submartingale_stoppedProcess (hX : Submartingale X ℱ μ) (hτ : IsStoppingTime ℱ τ) :
    Submartingale (stoppedProcess X τ) ℱ μ ∧
      Submartingale (stoppedProcess X τ) (stoppedFiltration ℱ hτ) μ := by
  exact stoppedProcess_submartingale hX hτ

-- Proof sketch: apply the core stopped-submartingale bridge to `-X` and convert back using the
-- canonical equivalence between supermartingales and negated submartingales.
/-- Theorem 10.15 (3): if `X` is a supermartingale and `τ` is a stopping time, then the stopped
process `X^τ` is again a supermartingale both for the ambient filtration `ℱ` and for the stopped
filtration `ℱ^τ`. -/
theorem supermartingale_stoppedProcess (hX : Supermartingale X ℱ μ) (hτ : IsStoppingTime ℱ τ) :
    Supermartingale (stoppedProcess X τ) ℱ μ ∧
      Supermartingale (stoppedProcess X τ) (stoppedFiltration ℱ hτ) μ := by
  have hneg :
      Submartingale (stoppedProcess (-X) τ) ℱ μ ∧
        Submartingale (stoppedProcess (-X) τ) (stoppedFiltration ℱ hτ) μ :=
    stoppedProcess_submartingale hX.neg hτ
  refine ⟨?_, ?_⟩
  · simpa [neg_stoppedProcess_neg] using hneg.1.neg
  · simpa [neg_stoppedProcess_neg] using hneg.2.neg
