import DifferentialForms_Cartan_1970.IV.section17.«0002_Theorem_IV_5_extra_2».TransportedSlices

/-- Helper for Theorem IV.5-extra-2: fixing the transported last coordinate and staying away from
the Cauchy pole keeps the weighted block slice analytic in the chosen block coordinate. -/
lemma analyticAt_weightedTransportedBlockSlice
    {m : ℕ} {D : Set (Fin (m + 2) → ℂ)} {f : (Fin (m + 2) → ℂ) → ℂ}
    (hsep : ∀ z ∈ D, ∀ i : Fin (m + 2), AnalyticAt ℂ (fun w ↦ f (Function.update z i w)) (z i))
    {x : Fin (m + 1) → ℂ} {ζ w0 : ℂ} {i : Fin (m + 1)}
    (hz : (Fin.succFunEquiv ℂ (m + 1)).symm (x, ζ) ∈ D)
    (n : ℕ) :
    let e := Fin.succFunEquiv ℂ (m + 1)
    let g : (Fin (m + 1) → ℂ) × ℂ → ℂ := f ∘ e.symm
    AnalyticAt ℂ
      (fun u ↦ ((ζ - w0)⁻¹) ^ n * ((ζ - w0)⁻¹ * g (Function.update x i u, ζ)))
      (x i) := by
  dsimp
  have hslice :
      AnalyticAt ℂ
        (fun u ↦
          f
            ((Fin.succFunEquiv ℂ (m + 1)).symm
              (Function.update x i u, ζ)))
        (x i) := by
    simpa using
      transportedBlockSlice_analyticAt (m := m) (D := D) (f := f) hsep
        (z := (Fin.succFunEquiv ℂ (m + 1)).symm (x, ζ)) hz i
  have hkernel : AnalyticAt ℂ (fun _ : ℂ ↦ (ζ - w0)⁻¹) (x i) := analyticAt_const
  convert (hkernel.pow n).mul (hkernel.mul hslice) using 1

/-- Helper for Theorem IV.5-extra-2: fixing the transported block point and staying away from the
pole keeps the weighted last-variable slice analytic. -/
lemma analyticAt_weightedTransportedLastSlice
    {m : ℕ} {D : Set (Fin (m + 2) → ℂ)} {f : (Fin (m + 2) → ℂ) → ℂ}
    (hsep : ∀ z ∈ D, ∀ i : Fin (m + 2), AnalyticAt ℂ (fun w ↦ f (Function.update z i w)) (z i))
    {x : Fin (m + 1) → ℂ} {ζ w0 : ℂ}
    (hz : (Fin.succFunEquiv ℂ (m + 1)).symm (x, ζ) ∈ D)
    (hζne : ζ ≠ w0) (n : ℕ) :
    let e := Fin.succFunEquiv ℂ (m + 1)
    let g : (Fin (m + 1) → ℂ) × ℂ → ℂ := f ∘ e.symm
    AnalyticAt ℂ
      (fun w ↦ ((w - w0)⁻¹) ^ n * ((w - w0)⁻¹ * g (x, w)))
      ζ := by
  dsimp
  have hslice :
      AnalyticAt ℂ
        (fun w ↦
          f
            ((Fin.succFunEquiv ℂ (m + 1)).symm
              (x, w)))
        ζ := by
    simpa using
      transportedLastSlice_analyticAt (m := m) (D := D) (f := f) hsep
        (z := (Fin.succFunEquiv ℂ (m + 1)).symm (x, ζ)) hz
  have hkernel :
      AnalyticAt ℂ (fun w : ℂ ↦ (w - w0)⁻¹) ζ := by
    exact (analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr hζne)
  convert (hkernel.pow n).mul (hkernel.mul hslice) using 1
