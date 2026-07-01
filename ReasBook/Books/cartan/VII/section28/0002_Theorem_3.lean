import cartan.VII.section28.«0001_Theorem_2»

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Topology

/- Domain sampling:
- source-facing slice owner in this chapter: `IsHolomorphicSystemSolutionOn`
- germ-level owner in this chapter: `IsHolomorphicSystemSolution`
- several-variable analyticity owners used downstream: `AnalyticOnNhd` and `AnalyticAt`
- derived product API used for the component form: `analyticAt_pi_iff`

Theorem 3 is a bridge/view statement: it assumes the canonical section-27 holomorphic-system
solution predicate for each parameter slice `x ↦ φ (x, b)` and concludes the joint analyticity of
the family `(x, b) ↦ φ (x, b)`. The primitive ODE data stay in the owner abstraction rather than
being duplicated as separate totalized-`deriv` hypotheses. -/

/-- Helper for Theorem 3: translating the state variable by the parameter preserves analyticity of
the ODE right-hand side on the shifted coefficient domain. -/
lemma analyticOnNhd_shifted_rhs
    {k : ℕ} {Ω : Set (ℂ × (Fin k → ℂ))}
    {f : ℂ → (Fin k → ℂ) → Fin k → ℂ}
    (hf : AnalyticOnNhd ℂ (fun p : ℂ × (Fin k → ℂ) ↦ f p.1 p.2) Ω) :
    AnalyticOnNhd ℂ
      (fun p : ℂ × (Fin k → ℂ) × (Fin k → ℂ) ↦ f p.1 (p.2.1 + p.2.2))
      {p : ℂ × (Fin k → ℂ) × (Fin k → ℂ) | (p.1, p.2.1 + p.2.2) ∈ Ω} := by
  -- The translation map `(x, z, b) ↦ (x, z + b)` is analytic because projections and addition are.
  intro p hp
  have hsum :
      AnalyticAt ℂ (fun q : ℂ × (Fin k → ℂ) × (Fin k → ℂ) ↦ q.2.1 + q.2.2) p := by
    have hadd :
        AnalyticAt ℂ (fun q : (Fin k → ℂ) × (Fin k → ℂ) ↦ q.1 + q.2) p.2 := by
      simpa using
        ((analyticAt_fst : AnalyticAt ℂ (fun q : (Fin k → ℂ) × (Fin k → ℂ) ↦ q.1) p.2).add
          (analyticAt_snd : AnalyticAt ℂ (fun q : (Fin k → ℂ) × (Fin k → ℂ) ↦ q.2) p.2))
    have hpair :
        AnalyticAt ℂ (fun q : ℂ × (Fin k → ℂ) × (Fin k → ℂ) ↦ q.2) p := by
      simpa using
        (analyticAt_snd : AnalyticAt ℂ (fun q : ℂ × ((Fin k → ℂ) × (Fin k → ℂ)) ↦ q.2) p)
    simpa using hadd.comp hpair
  have hshift :
      AnalyticAt ℂ (fun q : ℂ × (Fin k → ℂ) × (Fin k → ℂ) ↦ (q.1, q.2.1 + q.2.2)) p := by
    simpa using analyticAt_fst.prod hsum
  -- Composing the original analytic coefficient map with the translation gives the shifted system.
  have hbase :
      AnalyticAt ℂ (fun q : ℂ × (Fin k → ℂ) ↦ f q.1 q.2) (p.1, p.2.1 + p.2.2) :=
    hf (p.1, p.2.1 + p.2.2) hp
  simpa using hbase.comp_of_eq hshift rfl

/-- Helper for Theorem 3: subtracting the initial value turns each slice into a zero-initial
solution of the translated system. -/
lemma shifted_solution_family_isHolomorphicSystemSolutionOn
    {k : ℕ} {Ω : Set (ℂ × (Fin k → ℂ))} {U : Set ℂ} {V : Set (Fin k → ℂ)}
    {f : ℂ → (Fin k → ℂ) → Fin k → ℂ} {φ : ℂ × (Fin k → ℂ) → Fin k → ℂ}
    (hφ : ∀ b ∈ V, IsHolomorphicSystemSolutionOn Ω f 0 b U (fun x ↦ φ (x, b)))
    {b : Fin k → ℂ} (hb : b ∈ V) :
    IsHolomorphicSystemSolutionOn
      {p : ℂ × (Fin k → ℂ) | (p.1, p.2 + b) ∈ Ω}
      (fun x z ↦ f x (z + b))
      0
      0
      U
      (fun x ↦ φ (x, b) - b) := by
  -- The translated slice stays analytic on the same `x`-domain after subtracting a constant.
  refine ⟨(hφ b hb).isOpen, (hφ b hb).mem, ?_, ?_, ?_, ?_⟩
  · simpa using (hφ b hb).analytic.sub
      (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ ↦ b) U)
  · -- The shifted graph lies in the translated coefficient domain because adding `b` recovers `φ`.
    intro x hx
    have hgraph : (x, φ (x, b)) ∈ Ω := (hφ b hb).mapsTo hx
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hgraph
  · -- At `x = 0`, the translated unknown vanishes by construction.
    simpa using sub_eq_zero.mpr (hφ b hb).initial
  · intro x hx
    -- The derivative is unchanged by subtracting the constant initial parameter.
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (hφ b hb).deriv_eq hx |>.sub_const b

/-- Helper for Theorem 3: adding back the parameter coordinate preserves analyticity at the
origin. -/
lemma analyticAt_original_family_of_shifted_analytic
    {k : ℕ} {φ ψ : ℂ × (Fin k → ℂ) → Fin k → ℂ}
    (hψ : AnalyticAt ℂ ψ (0, 0))
    (hφ : φ = fun p : ℂ × (Fin k → ℂ) ↦ ψ p + p.2) :
    AnalyticAt ℂ φ (0, 0) := by
  -- The original family is the sum of the shifted family and the analytic parameter projection.
  rw [hφ]
  simpa using hψ.add (analyticAt_snd : AnalyticAt ℂ (fun p : ℂ × (Fin k → ℂ) ↦ p.2) (0, 0))

/-- Theorem 3: for a holomorphic first-order system `dφ/dx = f (x, φ)`, if the slices
`x ↦ φ (x, b)` form a family of local holomorphic solutions with initial value `b` for parameters
`b` near `0`, then `φ` is analytic in the variables `(x, b)` near `(0, 0)`. -/
theorem analyticAt_origin_of_holomorphic_ode_solution_family_with_initial_values
    {k : ℕ} {Ω : Set (ℂ × (Fin k → ℂ))} {U : Set ℂ} {V : Set (Fin k → ℂ)}
    {f : ℂ → (Fin k → ℂ) → Fin k → ℂ} {φ : ℂ × (Fin k → ℂ) → Fin k → ℂ}
    (hf : AnalyticOnNhd ℂ (fun p : ℂ × (Fin k → ℂ) ↦ f p.1 p.2) Ω)
    (hV : IsOpen V) (hV0 : (0 : Fin k → ℂ) ∈ V)
    (hφ : ∀ b ∈ V, IsHolomorphicSystemSolutionOn Ω f 0 b U (fun x ↦ φ (x, b))) :
    AnalyticAt ℂ φ (0, 0) := by
  let Ωshift : Set (ℂ × (Fin k → ℂ) × (Fin k → ℂ)) :=
    {p | (p.1, p.2.1 + p.2.2) ∈ Ω}
  let ψ : ℂ × (Fin k → ℂ) → Fin k → ℂ := fun p ↦ φ p - p.2
  let W : Set (ℂ × (Fin k → ℂ)) := U ×ˢ V
  have hU : IsOpen U := (hφ 0 hV0).isOpen
  have h0U : (0 : ℂ) ∈ U := (hφ 0 hV0).mem
  have hW : IsOpen W := hU.prod hV
  have h0W : ((0 : ℂ), (0 : Fin k → ℂ)) ∈ W := ⟨h0U, hV0⟩
  have hshifted_rhs :
      AnalyticOnNhd ℂ
        (fun p : ℂ × (Fin k → ℂ) × (Fin k → ℂ) ↦ f p.1 (p.2.1 + p.2.2))
        Ωshift := by
    -- The translated system keeps the same analytic coefficient map after the affine change.
    simpa [Ωshift] using analyticOnNhd_shifted_rhs hf
  have hshifted_sol :
      ∀ b ∈ V,
        IsHolomorphicSystemSolutionOn
          {p : ℂ × (Fin k → ℂ) | (p.1, p.2, b) ∈ Ωshift}
          (fun x z ↦ f x (z + b))
          0
          0
          {x : ℂ | (x, b) ∈ W}
          (fun x ↦ ψ (x, b)) := by
    intro b hb
    -- This is exactly the textbook substitution `z = y - b`, rewritten in the owner predicate.
    simpa [Ωshift, W, ψ, hb] using
      shifted_solution_family_isHolomorphicSystemSolutionOn hφ hb
  have hψanalytic : AnalyticAt ℂ ψ (0, 0) := by
    -- Theorem 2 applies to the translated zero-initial family on the product neighborhood `W`.
    exact analyticAt_origin_of_holomorphic_ode_solution_family
      hshifted_rhs hV hV0 hW h0W hshifted_sol
  have hφeq : φ = fun p : ℂ × (Fin k → ℂ) ↦ ψ p + p.2 := by
    -- Adding the parameter back recovers the original family pointwise.
    funext p
    simp [ψ]
  -- The original family inherits analyticity from the translated family plus the parameter map.
  exact analyticAt_original_family_of_shifted_analytic hψanalytic hφeq

/-- The parameter-indexing condition in Theorem 3 is supplied by the section-27 owner
`IsHolomorphicSystemSolutionOn`, whose `initial` field gives `φ (0, b) = b` for each
`b ∈ V`. -/
theorem analyticAt_origin_of_holomorphic_ode_solution_family_with_initial_values_initial
    {k : ℕ} {Ω : Set (ℂ × (Fin k → ℂ))} {U : Set ℂ} {V : Set (Fin k → ℂ)}
    {f : ℂ → (Fin k → ℂ) → Fin k → ℂ} {φ : ℂ × (Fin k → ℂ) → Fin k → ℂ}
    (hφ : ∀ b ∈ V, IsHolomorphicSystemSolutionOn Ω f 0 b U (fun x ↦ φ (x, b)))
    {b : Fin k → ℂ} (hb : b ∈ V) :
    φ (0, b) = b := by
  simpa using (hφ b hb).initial

/-- The component form of Theorem 3, recovered from the canonical joint analyticity owner
`AnalyticAt ℂ φ (0, 0)` via `analyticAt_pi_iff`. -/
theorem analyticAt_origin_of_holomorphic_ode_solution_family_with_initial_values_apply
    {k : ℕ} {Ω : Set (ℂ × (Fin k → ℂ))} {U : Set ℂ} {V : Set (Fin k → ℂ)}
    {f : ℂ → (Fin k → ℂ) → Fin k → ℂ} {φ : ℂ × (Fin k → ℂ) → Fin k → ℂ}
    (hf : AnalyticOnNhd ℂ (fun p : ℂ × (Fin k → ℂ) ↦ f p.1 p.2) Ω)
    (hV : IsOpen V) (hV0 : (0 : Fin k → ℂ) ∈ V)
    (hφ : ∀ b ∈ V, IsHolomorphicSystemSolutionOn Ω f 0 b U (fun x ↦ φ (x, b)))
    (i : Fin k) :
    AnalyticAt ℂ (fun z ↦ φ z i) (0, 0) := by
  have hanalytic : AnalyticAt ℂ φ (0, 0) :=
    analyticAt_origin_of_holomorphic_ode_solution_family_with_initial_values hf hV hV0 hφ
  exact analyticAt_pi_iff.mp hanalytic i
