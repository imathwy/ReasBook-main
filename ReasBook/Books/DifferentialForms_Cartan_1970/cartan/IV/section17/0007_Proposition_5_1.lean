import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- Domain sampling: Proposition IV.5.1 is a several-complex-variable composition statement. The
-- source-facing open-set owner is mathlib's `AnalyticOnNhd`, with the canonical composition and
-- product API `AnalyticOnNhd.comp` and `analyticOnNhd_pi_iff`; the chapter's core holomorphicity
-- owner `DifferentiableOn ℂ` remains available as a stronger bridge/view via
-- `DifferentiableOn.comp` and `differentiableOn_pi''`. The primitive data are `f`, `g`, and the
-- coordinatewise regularity hypotheses; assembling `g` as a map into `ℂ^n` is derived API.

open Set

/-- Proposition 5.1: if `f` is holomorphic on `D ⊆ ℂ^n` and the coordinate functions of
`g : ℂ^p → ℂ^n` are holomorphic on `D' ⊆ ℂ^p`, with `g(D') ⊆ D`, then `f ∘ g` is holomorphic on
`D'`. The source-facing open-set semantics are expressed by the canonical owner
`AnalyticOnNhd ℂ`. -/
theorem analyticOnNhd_comp_of_holomorphic_coordinates
    {n p : ℕ} {D : Set (Fin n → ℂ)} {D' : Set (Fin p → ℂ)}
    {f : (Fin n → ℂ) → ℂ} {g : (Fin p → ℂ) → (Fin n → ℂ)}
    (hf : AnalyticOnNhd ℂ f D)
    (hg : ∀ i : Fin n, AnalyticOnNhd ℂ (fun t ↦ g t i) D')
    (h_maps : MapsTo g D' D) :
    AnalyticOnNhd ℂ (f ∘ g) D' := by
  have hg' : AnalyticOnNhd ℂ g D' := by
    simpa using (analyticOnNhd_pi_iff : AnalyticOnNhd ℂ (fun t ↦ fun i ↦ g t i) D' ↔ _).2 hg
  exact hf.comp hg' h_maps

/-- Bridge/view: the same composition statement in the chapter's core owner `DifferentiableOn ℂ`.
This is a stronger formulation than the open-set textbook statement, not a reformulation of the
meaning of `DifferentiableOn`. -/
theorem differentiableOn_comp_of_holomorphic_coordinates
    {n p : ℕ} {D : Set (Fin n → ℂ)} {D' : Set (Fin p → ℂ)}
    {f : (Fin n → ℂ) → ℂ} {g : (Fin p → ℂ) → (Fin n → ℂ)}
    (hf : DifferentiableOn ℂ f D)
    (hg : ∀ i : Fin n, DifferentiableOn ℂ (fun t ↦ g t i) D')
    (h_maps : MapsTo g D' D) :
    DifferentiableOn ℂ (f ∘ g) D' :=
  hf.comp (differentiableOn_pi'' hg) h_maps
