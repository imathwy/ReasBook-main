import cartan.IV.section14.«0002_Definition_IV_2_extra_2»
import cartan.IV.section17.«0001_Definition_IV_5_extra_1»

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: the dedicated `lean_leansearch` tool requested by the statement policy
-- was unavailable in this environment, so the statement surface was matched against the local
-- several-complex-variable precedent using `DifferentiableOn ℂ` for holomorphicity and
-- `AnalyticOnNhd ℂ` for analyticity on open sets. Here the primitive source-facing data are the
-- open domain and the coordinate-slice `AnalyticAt` hypothesis; continuity on the domain is
-- derived API rather than part of the canonical theorem interface.

section

variable {n : ℕ}
variable {D : Set (Fin n → ℂ)} {f : (Fin n → ℂ) → ℂ}

/-- Helper for Theorem IV.5-extra-2: the Hartogs/Osgood core statement upgrading coordinatewise
holomorphy on an open subset of `ℂ^n` to analyticity on a neighborhood of the domain. -/
theorem separately_holomorphic_analyticOnNhd_core
    (hD : IsOpen D)
    (hsep : ∀ z ∈ D, ∀ i : Fin n, AnalyticAt ℂ (fun w ↦ f (Function.update z i w)) (z i)) :
    AnalyticOnNhd ℂ f D := by
  -- Route correction: the solvable wrappers are reduced to this single Hartogs core statement.
  -- TODO: follow the source-faithful local Hartogs route from separate analyticity to joint
  -- analyticity, then lift the pointwise conclusion to `AnalyticOnNhd`.
  sorry

/-- Theorem IV.5-extra-2 (1): if `D ⊆ ℂ^n` is open and for every `z ∈ D` each coordinate slice
`w ↦ f (Function.update z i w)` is holomorphic at `z i`, then `f` is holomorphic on `D`. -/
theorem separately_holomorphic_differentiableOn
    (hD : IsOpen D)
    (hsep : ∀ z ∈ D, ∀ i : Fin n, AnalyticAt ℂ (fun w ↦ f (Function.update z i w)) (z i)) :
    DifferentiableOn ℂ f D := by
  -- First upgrade separate holomorphy to joint analyticity on a neighborhood of `D`.
  have hanalytic : AnalyticOnNhd ℂ f D := separately_holomorphic_analyticOnNhd_core hD hsep
  -- Analyticity on a neighborhood of the open set gives the desired holomorphicity owner.
  exact hanalytic.differentiableOn

/-- Theorem IV.5-extra-2 (2): if `D ⊆ ℂ^n` is open and for every `z ∈ D` each coordinate slice
`w ↦ f (Function.update z i w)` is holomorphic at `z i`, then `f` is analytic on `D`. -/
theorem separately_holomorphic_analyticOnNhd
    (hD : IsOpen D)
    (hsep : ∀ z ∈ D, ∀ i : Fin n, AnalyticAt ℂ (fun w ↦ f (Function.update z i w)) (z i)) :
    AnalyticOnNhd ℂ f D := by
  -- This is the source-facing analytic formulation of the Hartogs/Osgood conclusion.
  exact separately_holomorphic_analyticOnNhd_core hD hsep

/-- On an open subset of `ℂ^n`, complex Fréchet differentiability implies analyticity on a
neighborhood of the domain. -/
theorem _root_.DifferentiableOn.analyticOnNhd_pi
    (hf : DifferentiableOn ℂ f D) (hD : IsOpen D) :
    AnalyticOnNhd ℂ f D := by
  -- Reduce joint differentiability to the coordinate-slice analyticity required by Hartogs.
  refine separately_holomorphic_analyticOnNhd hD ?_
  intro z hz i
  let g : ℂ → Fin n → ℂ := Function.update z i
  let s : Set ℂ := g ⁻¹' D
  -- The coordinate insertion map is differentiable, hence continuous, on the source line.
  have hg_diff : Differentiable ℂ g := by
    intro w
    simpa [g] using (hasFDerivAt_update z (i := i) w).differentiableAt
  have hs_open : IsOpen s := by
    exact hD.preimage hg_diff.continuous
  have hg_on : DifferentiableOn ℂ g s := by
    intro w hw
    exact (hasFDerivAt_update z (i := i) w).differentiableAt.differentiableWithinAt
  have hg_maps : Set.MapsTo g s D := by
    intro w hw
    exact hw
  have hslice : DifferentiableOn ℂ (fun w ↦ f (g w)) s := hf.comp hg_on hg_maps
  have hz_slice : z i ∈ s := by
    simpa [s, g] using hz
  -- The one-variable open-set theorem upgrades the slice to analyticity at the base point.
  simpa [g] using (hslice.analyticOnNhd hs_open) (z i) hz_slice

end
