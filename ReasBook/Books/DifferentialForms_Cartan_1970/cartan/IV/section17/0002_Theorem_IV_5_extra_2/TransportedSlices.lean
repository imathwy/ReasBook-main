import DifferentialForms_Cartan_1970.cartan.IV.section14.«0002_Definition_IV_2_extra_2»
import DifferentialForms_Cartan_1970.cartan.IV.section17.«0001_Definition_IV_5_extra_1»
import DifferentialForms_Cartan_1970.cartan.IV.section17.«0002_Theorem_IV_5_extra_2».DimensionTransport

/-- Helper for Theorem IV.5-extra-2: fixing the transported last coordinate reduces the block
variables to the lower-dimensional Hartogs theorem. -/
lemma transportedFixedLastSlice_analyticOnNhd
    {m : ℕ} {D : Set (Fin (m + 2) → ℂ)} {f : (Fin (m + 2) → ℂ) → ℂ}
    (ih :
      ∀ {D' : Set (Fin (m + 1) → ℂ)} {f' : (Fin (m + 1) → ℂ) → ℂ},
        IsOpen D' →
        (∀ z ∈ D', ∀ i : Fin (m + 1),
          AnalyticAt ℂ (fun w ↦ f' (Function.update z i w)) (z i)) →
        AnalyticOnNhd ℂ f' D')
    (hD : IsOpen D)
    (hsep : ∀ z ∈ D, ∀ i : Fin (m + 2), AnalyticAt ℂ (fun w ↦ f (Function.update z i w)) (z i))
    (w : ℂ) :
    let e := Fin.succFunEquiv ℂ (m + 1)
    let g : (Fin (m + 1) → ℂ) × ℂ → ℂ := f ∘ e.symm
    let Dw : Set (Fin (m + 1) → ℂ) := {x | e.symm (x, w) ∈ D}
    AnalyticOnNhd ℂ (fun x ↦ g (x, w)) Dw := by
  dsimp
  refine ih ?_ ?_
  · -- The fixed-last-coordinate slice domain is the preimage of `D` under the transported block
    -- inclusion `x ↦ e.symm (x, w)`.
    have hpair :
        Continuous (fun x : Fin (m + 1) → ℂ ↦ (x, (fun _ : Fin 1 ↦ w))) := by
      exact continuous_id.prodMk continuous_const
    have hcont :
        Continuous (fun x : Fin (m + 1) → ℂ ↦
          (Fin.succFunEquiv ℂ (m + 1)).symm (x, w)) := by
      simpa [Fin.succFunEquiv_symm_apply] using
        (Fin.continuous_append (m + 1) 1).comp hpair
    simpa using hD.preimage hcont
  · intro x hx i
    -- The transported block-slice identity turns the lower-dimensional slice hypothesis for the
    -- fixed `w` slice into the original separate analyticity hypothesis for `f`.
    simpa [Function.comp] using
      transportedBlockSlice_analyticAt (m := m) (D := D) (f := f) hsep
        (z := (Fin.succFunEquiv ℂ (m + 1)).symm (x, w)) hx i

/-- Helper for Theorem IV.5-extra-2: once a transported closed cylinder stays inside `D`, the
boundary values in the last variable inherit the lower-dimensional block analyticity on the whole
interior block ball. -/
lemma transportedBoundaryBlockSlices_analyticOnNhd_ball
    {m : ℕ} {D : Set (Fin (m + 2) → ℂ)} {f : (Fin (m + 2) → ℂ) → ℂ}
    (ih :
      ∀ {D' : Set (Fin (m + 1) → ℂ)} {f' : (Fin (m + 1) → ℂ) → ℂ},
        IsOpen D' →
        (∀ z ∈ D', ∀ i : Fin (m + 1),
          AnalyticAt ℂ (fun w ↦ f' (Function.update z i w)) (z i)) →
        AnalyticOnNhd ℂ f' D')
    (hD : IsOpen D)
    (hsep : ∀ z ∈ D, ∀ i : Fin (m + 2), AnalyticAt ℂ (fun w ↦ f (Function.update z i w)) (z i))
    {z : Fin (m + 2) → ℂ} {r R : ℝ}
    (hcyl :
      Metric.ball ((Fin.succFunEquiv ℂ (m + 1) z).1) r ×ˢ
          Metric.closedBall ((Fin.succFunEquiv ℂ (m + 1) z).2) R ⊆
        {p | (Fin.succFunEquiv ℂ (m + 1)).symm p ∈ D}) :
    let e := Fin.succFunEquiv ℂ (m + 1)
    let g : (Fin (m + 1) → ℂ) × ℂ → ℂ := f ∘ e.symm
    ∀ ζ ∈ Metric.sphere (e z).2 R,
      AnalyticOnNhd ℂ (fun x ↦ g (x, ζ)) (Metric.ball (e z).1 r) := by
  dsimp
  intro ζ hζ x hx
  -- Restrict the fixed-last-coordinate lower-dimensional theorem to the chosen block ball.
  exact
    (transportedFixedLastSlice_analyticOnNhd (m := m) (D := D) (f := f) ih hD hsep ζ) x <|
      hcyl ⟨hx, Metric.sphere_subset_closedBall hζ⟩

/-- Helper for Theorem IV.5-extra-2: inside a transported closed cylinder, every fixed block point
sees an analytic last-variable slice on the whole closed disc. -/
lemma transportedLastSlices_analyticOnNhd_closedBall
    {m : ℕ} {D : Set (Fin (m + 2) → ℂ)} {f : (Fin (m + 2) → ℂ) → ℂ}
    (hsep : ∀ z ∈ D, ∀ i : Fin (m + 2), AnalyticAt ℂ (fun w ↦ f (Function.update z i w)) (z i))
    {z : Fin (m + 2) → ℂ} {r R : ℝ}
    (hcyl :
      Metric.ball ((Fin.succFunEquiv ℂ (m + 1) z).1) r ×ˢ
          Metric.closedBall ((Fin.succFunEquiv ℂ (m + 1) z).2) R ⊆
        {p | (Fin.succFunEquiv ℂ (m + 1)).symm p ∈ D}) :
    let e := Fin.succFunEquiv ℂ (m + 1)
    let g : (Fin (m + 1) → ℂ) × ℂ → ℂ := f ∘ e.symm
    ∀ x ∈ Metric.ball (e z).1 r,
      AnalyticOnNhd ℂ (fun w ↦ g (x, w)) (Metric.closedBall (e z).2 R) := by
  dsimp
  intro x hx w hw
  -- The cylinder containment lets us transport the original last-coordinate slice hypothesis to
  -- every point of the closed disc over the chosen block point.
  simpa using
    transportedLastSlice_analyticAt (m := m) (D := D) (f := f) hsep
      (z := (Fin.succFunEquiv ℂ (m + 1)).symm (x, w)) (hz := hcyl ⟨hx, hw⟩)
