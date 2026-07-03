import DifferentialForms_Cartan_1970.VII.section27.«0001_Theorem_I»
import Mathlib

open Filter
open Set

open scoped Topology

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: section 27 already introduces the canonical source-facing owner
-- `IsHolomorphicSystemSolutionOn` for local holomorphic first-order systems. The parameter
-- dependence theorem is stated as a bridge from that slice-wise local solution data, together
-- with an actual neighborhood in `(x, t)`-space, to joint analyticity near the origin.

/-- Helper for Theorem 2: every parameter slice in the given solution family sends the base point
`x = 0` to the zero initial value, so the corresponding graph point belongs to the coefficient
domain `Ω`. -/
lemma zero_section_mem_coeff_domain
    {k j : ℕ} {Ω : Set (ℂ × (Fin k → ℂ) × (Fin j → ℂ))}
    {F : ℂ → (Fin k → ℂ) → (Fin j → ℂ) → Fin k → ℂ}
    {V : Set (Fin j → ℂ)} {W : Set (ℂ × (Fin j → ℂ))}
    {φ : ℂ × (Fin j → ℂ) → Fin k → ℂ}
    {t : Fin j → ℂ}
    (hsol :
      ∀ t ∈ V,
        IsHolomorphicSystemSolutionOn
          {p : ℂ × (Fin k → ℂ) | (p.1, p.2, t) ∈ Ω}
          (fun x y ↦ F x y t)
          0
          0
          {x : ℂ | (x, t) ∈ W}
          (fun x ↦ φ (x, t)))
    (ht : t ∈ V) :
    ((0 : ℂ), (0 : Fin k → ℂ), t) ∈ Ω := by
  -- The graph of the slice solution passes through the prescribed initial value at `x = 0`.
  have hslice := hsol t ht
  have hgraph :
      ((0 : ℂ), φ (0, t)) ∈ {p : ℂ × (Fin k → ℂ) | (p.1, p.2, t) ∈ Ω} :=
    hslice.mapsTo hslice.mem
  simpa [hslice.initial] using hgraph

/-- Helper for Theorem 2: an open neighborhood of `((0 : ℂ), 0)` in `(x, t)`-space contains a
smaller product neighborhood around the origin. -/
lemma exists_product_neighborhood_subordinate_to_W
    {j : ℕ} {W : Set (ℂ × (Fin j → ℂ))}
    (hW : IsOpen W) (h0W : ((0 : ℂ), (0 : Fin j → ℂ)) ∈ W) :
    ∃ Ux : Set ℂ, ∃ Vx : Set (Fin j → ℂ),
      IsOpen Ux ∧ IsOpen Vx ∧
      (0 : ℂ) ∈ Ux ∧ (0 : Fin j → ℂ) ∈ Vx ∧
      Ux ×ˢ Vx ⊆ W := by
  -- First pass from the open neighborhood in the product space to neighborhood filters.
  have hW_nhds : W ∈ 𝓝 ((0 : ℂ), (0 : Fin j → ℂ)) :=
    hW.mem_nhds h0W
  rcases mem_nhds_prod_iff.mp hW_nhds with ⟨Ux, hUx, Vx, hVx, hsub⟩
  -- Then replace the filter neighborhoods by open neighborhoods of the two coordinates.
  rcases _root_.mem_nhds_iff.mp hUx with ⟨Ux', hUx'sub, hUx'open, h0Ux'⟩
  rcases _root_.mem_nhds_iff.mp hVx with ⟨Vx', hVx'sub, hVx'open, h0Vx'⟩
  refine ⟨Ux', Vx', hUx'open, hVx'open, h0Ux', h0Vx', ?_⟩
  exact Set.Subset.trans (Set.prod_mono hUx'sub hVx'sub) hsub

/-- Helper for Theorem 2: two holomorphic solution slices with the same initial value for the
same first-order system agree on any common preconnected open domain. -/
lemma eqOn_of_same_initial_holomorphic_solution
    {k : ℕ} {Ω : Set (ℂ × (Fin k → ℂ))}
    {f : ℂ → (Fin k → ℂ) → Fin k → ℂ}
    {b : Fin k → ℂ} {U : Set ℂ} {ψ₁ ψ₂ : ℂ → Fin k → ℂ}
    (hΩ : IsOpen Ω) (h0 : ((0 : ℂ), b) ∈ Ω)
    (hf : AnalyticOnNhd ℂ (fun p : ℂ × (Fin k → ℂ) ↦ f p.1 p.2) Ω)
    (hU : IsPreconnected U)
    (hψ₁ : IsHolomorphicSystemSolutionOn Ω f 0 b U ψ₁)
    (hψ₂ : IsHolomorphicSystemSolutionOn Ω f 0 b U ψ₂) :
    Set.EqOn ψ₁ ψ₂ U := by
  -- The germ-level uniqueness theorem gives a common representative near `x = 0`.
  rcases exists_eventuallyEq_unique_local_solution_holomorphic_system hΩ h0 hf with
    ⟨V, χ, hχ, huniq⟩
  have hψ₁_eq : ψ₁ =ᶠ[𝓝 (0 : ℂ)] χ :=
    huniq U ψ₁ hψ₁
  have hψ₂_eq : ψ₂ =ᶠ[𝓝 (0 : ℂ)] χ :=
    huniq U ψ₂ hψ₂
  have hψ_eq : ψ₁ =ᶠ[𝓝 (0 : ℂ)] ψ₂ :=
    hψ₁_eq.trans hψ₂_eq.symm
  -- On a preconnected open set, eventual equality at one point upgrades to equality everywhere.
  exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    hψ₁.analytic hψ₂.analytic hU hψ₁.mem hψ_eq

/-- Helper for Theorem 2: if the three-variable right-hand side is analytic at a point
`(x, y, t) ∈ Ω`, then the parameter slice `z ↦ F z _ t` is analytic at `(x, y)`. -/
lemma analyticAt_slice_rhs_of_mem
    {k j : ℕ} {Ω : Set (ℂ × (Fin k → ℂ) × (Fin j → ℂ))}
    {F : ℂ → (Fin k → ℂ) → (Fin j → ℂ) → Fin k → ℂ}
    (hF : AnalyticOnNhd ℂ (fun p : ℂ × (Fin k → ℂ) × (Fin j → ℂ) ↦ F p.1 p.2.1 p.2.2) Ω)
    {p : ℂ × (Fin k → ℂ)} {t : Fin j → ℂ}
    (hp : (p.1, p.2, t) ∈ Ω) :
    AnalyticAt ℂ (fun q : ℂ × (Fin k → ℂ) ↦ F q.1 q.2 t) p := by
  -- Freeze the parameter variable and compose the ambient analytic map with the affine inclusion.
  have htriple :
      AnalyticAt ℂ
        (fun q : ℂ × (Fin k → ℂ) × (Fin j → ℂ) ↦ F q.1 q.2.1 q.2.2)
        (p.1, p.2, t) :=
    hF (p.1, p.2, t) hp
  have hpair :
      AnalyticAt ℂ (fun q : ℂ × (Fin k → ℂ) ↦ (q.2, t)) p := by
    simpa using analyticAt_snd.prod
      (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ × (Fin k → ℂ) ↦ t) p)
  have hmap :
      AnalyticAt ℂ (fun q : ℂ × (Fin k → ℂ) ↦ (q.1, q.2, t)) p := by
    simpa using analyticAt_fst.prod hpair
  simpa using htriple.comp_of_eq hmap rfl

/-- Helper for Theorem 2: restricting a holomorphic system solution to a smaller open
independent-variable domain and a new coefficient domain containing the restricted graph preserves
the solution predicate. -/
lemma IsHolomorphicSystemSolutionOn.restrict
    {k : ℕ} {Ω Ω' : Set (ℂ × (Fin k → ℂ))}
    {f : ℂ → (Fin k → ℂ) → Fin k → ℂ}
    {b : Fin k → ℂ} {U U' : Set ℂ} {ψ : ℂ → Fin k → ℂ}
    (hψ : IsHolomorphicSystemSolutionOn Ω f 0 b U ψ)
    (hU' : IsOpen U') (h0U' : (0 : ℂ) ∈ U') (hsub : U' ⊆ U)
    (hmaps : MapsTo (fun z ↦ (z, ψ z)) U' Ω') :
    IsHolomorphicSystemSolutionOn Ω' f 0 b U' ψ := by
  refine ⟨hU', h0U', ?_, hmaps, hψ.initial, ?_⟩
  · -- Analyticity restricts from the original open solution domain to the smaller open set.
    exact hψ.analytic.mono hsub
  · intro z hz
    -- The differential equation is inherited from the original solution on the larger domain.
    exact hψ.deriv_eq (hsub hz)

/-- Helper for Theorem 2: once the majorant argument produces a jointly analytic comparison family
on a product neighborhood, slice-wise uniqueness upgrades it to analyticity of the original family
at the origin. -/
lemma analyticAt_origin_of_holomorphic_ode_solution_family_of_comparison_family
    {k j : ℕ} {Ω : Set (ℂ × (Fin k → ℂ) × (Fin j → ℂ))}
    {F : ℂ → (Fin k → ℂ) → (Fin j → ℂ) → Fin k → ℂ}
    {V : Set (Fin j → ℂ)} {W : Set (ℂ × (Fin j → ℂ))}
    {φ ψ : ℂ × (Fin j → ℂ) → Fin k → ℂ}
    {Ux : Set ℂ} {Vx : Set (Fin j → ℂ)}
    (hF : AnalyticOnNhd ℂ (fun p : ℂ × (Fin k → ℂ) × (Fin j → ℂ) ↦ F p.1 p.2.1 p.2.2) Ω)
    (hV : IsOpen V) (h0V : (0 : Fin j → ℂ) ∈ V)
    (hW : IsOpen W) (h0W : ((0 : ℂ), 0) ∈ W)
    (hsol :
      ∀ t ∈ V,
        IsHolomorphicSystemSolutionOn
          {p : ℂ × (Fin k → ℂ) | (p.1, p.2, t) ∈ Ω}
          (fun x y ↦ F x y t)
          0
          0
          {x : ℂ | (x, t) ∈ W}
          (fun x ↦ φ (x, t)))
    (hUx : IsOpen Ux) (hVx : IsOpen Vx)
    (h0Ux : (0 : ℂ) ∈ Ux) (h0Vx : (0 : Fin j → ℂ) ∈ Vx)
    (hψanalytic : AnalyticOnNhd ℂ ψ (Ux ×ˢ Vx))
    (hψsol :
      ∀ t ∈ Vx,
        IsHolomorphicSystemSolutionOn
          {p : ℂ × (Fin k → ℂ) | (p.1, p.2, t) ∈ Ω}
          (fun x y ↦ F x y t)
          0
          0
          Ux
          (fun x ↦ ψ (x, t))) :
    AnalyticAt ℂ φ ((0 : ℂ), 0) := by
  -- First shrink the given `(x, t)`-neighborhood of the original family to a product neighborhood.
  rcases exists_product_neighborhood_subordinate_to_W hW h0W with
    ⟨Uw, Vw, hUw, hVw, h0Uw, h0Vw, hUwVw⟩
  let U0 : Set ℂ := Ux ∩ Uw
  let V0 : Set (Fin j → ℂ) := Vx ∩ (V ∩ Vw)
  have hU0 : IsOpen U0 := hUx.inter hUw
  have hV0 : IsOpen V0 := hVx.inter (hV.inter hVw)
  have h0U0 : (0 : ℂ) ∈ U0 := ⟨h0Ux, h0Uw⟩
  have h0V0 : (0 : Fin j → ℂ) ∈ V0 := ⟨h0Vx, h0V, h0Vw⟩
  -- Next choose a fixed ball in the `x`-plane contained in the common slice domain.
  rcases Metric.mem_nhds_iff.mp (hU0.mem_nhds h0U0) with ⟨r, hrpos, hrsub⟩
  let B : Set ℂ := Metric.ball (0 : ℂ) r
  have hBopen : IsOpen B := Metric.isOpen_ball
  have h0B : (0 : ℂ) ∈ B := Metric.mem_ball_self hrpos
  have hBsubU0 : B ⊆ U0 := by
    simpa [B] using hrsub
  have hBsubUx : B ⊆ Ux := fun z hz ↦ (hBsubU0 hz).1
  have hBsubUw : B ⊆ Uw := fun z hz ↦ (hBsubU0 hz).2
  let N : Set (ℂ × (Fin j → ℂ)) := B ×ˢ V0
  have hNopen : IsOpen N := hBopen.prod hV0
  have h0N : ((0 : ℂ), (0 : Fin j → ℂ)) ∈ N := ⟨h0B, h0V0⟩
  have hNsub : N ⊆ Ux ×ˢ Vx := by
    intro z hz
    exact ⟨hBsubUx hz.1, hz.2.1⟩
  have hψanalyticN : AnalyticOnNhd ℂ ψ N := hψanalytic.mono hNsub
  have hEqN : Set.EqOn φ ψ N := by
    intro z hz
    rcases hz with ⟨hzB, hzV0⟩
    have htVx : z.2 ∈ Vx := hzV0.1
    have htV : z.2 ∈ V := hzV0.2.1
    have htVw : z.2 ∈ Vw := hzV0.2.2
    let Ωz : Set (ℂ × (Fin k → ℂ)) :=
      {p : ℂ × (Fin k → ℂ) | AnalyticAt ℂ (fun q : ℂ × (Fin k → ℂ) ↦ F q.1 q.2 z.2) p}
    have hΩz : IsOpen Ωz := isOpen_analyticAt ℂ (fun q : ℂ × (Fin k → ℂ) ↦ F q.1 q.2 z.2)
    have h0Ωz : ((0 : ℂ), (0 : Fin k → ℂ)) ∈ Ωz := by
      exact analyticAt_slice_rhs_of_mem hF (zero_section_mem_coeff_domain hsol htV)
    have hslice : IsHolomorphicSystemSolutionOn
        Ωz
        (fun x y ↦ F x y z.2)
        0
        0
        B
        (fun x ↦ φ (x, z.2)) := by
      have hbase := hsol z.2 htV
      refine hbase.restrict hBopen h0B ?_ ?_
      · intro x hx
        have hxUw : x ∈ Uw := hBsubUw hx
        exact hUwVw ⟨hxUw, htVw⟩
      · intro x hx
        exact analyticAt_slice_rhs_of_mem hF (hbase.mapsTo (by
          have hxUw : x ∈ Uw := hBsubUw hx
          exact hUwVw ⟨hxUw, htVw⟩))
    have hsliceψ : IsHolomorphicSystemSolutionOn
        Ωz
        (fun x y ↦ F x y z.2)
        0
        0
        B
        (fun x ↦ ψ (x, z.2)) := by
      have hbase := hψsol z.2 htVx
      refine hbase.restrict hBopen h0B hBsubUx ?_
      intro x hx
      exact analyticAt_slice_rhs_of_mem hF (hbase.mapsTo (hBsubUx hx))
    have hFΩz : AnalyticOnNhd ℂ (fun p : ℂ × (Fin k → ℂ) ↦ F p.1 p.2 z.2) Ωz := by
      intro p hp
      exact hp
    have hEqSlice :
        Set.EqOn (fun x ↦ φ (x, z.2)) (fun x ↦ ψ (x, z.2)) B :=
      eqOn_of_same_initial_holomorphic_solution hΩz h0Ωz hFΩz
        (convex_ball (0 : ℂ) r).isPreconnected hslice hsliceψ
    exact hEqSlice hzB
  -- On this common product neighborhood, the original family agrees with the analytic comparison.
  have hEventually : ψ =ᶠ[𝓝 ((0 : ℂ), (0 : Fin j → ℂ))] φ :=
    Filter.mem_of_superset (hNopen.mem_nhds h0N) fun z hz ↦ (hEqN hz).symm
  exact (hψanalyticN ((0 : ℂ), (0 : Fin j → ℂ)) h0N).congr hEventually

/-- Helper for Theorem 2: the source-faithful majorant-series construction should produce a
jointly analytic comparison family on a product neighborhood of the origin. -/
lemma exists_analytic_comparison_family_on_product_neighborhood
    {k j : ℕ} {Ω : Set (ℂ × (Fin k → ℂ) × (Fin j → ℂ))}
    {F : ℂ → (Fin k → ℂ) → (Fin j → ℂ) → Fin k → ℂ}
    {V : Set (Fin j → ℂ)} {W : Set (ℂ × (Fin j → ℂ))}
    {Ux : Set ℂ} {Vx : Set (Fin j → ℂ)}
    {φ : ℂ × (Fin j → ℂ) → Fin k → ℂ}
    (hF : AnalyticOnNhd ℂ (fun p : ℂ × (Fin k → ℂ) × (Fin j → ℂ) ↦ F p.1 p.2.1 p.2.2) Ω)
    (hUx : IsOpen Ux) (hVx : IsOpen Vx)
    (h0Ux : (0 : ℂ) ∈ Ux) (h0Vx : (0 : Fin j → ℂ) ∈ Vx)
    (hWsub : Ux ×ˢ Vx ⊆ W) (hVxsub : Vx ⊆ V)
    (hsol :
      ∀ t ∈ Vx,
        IsHolomorphicSystemSolutionOn
          {p : ℂ × (Fin k → ℂ) | (p.1, p.2, t) ∈ Ω}
          (fun x y ↦ F x y t)
          0
          0
          Ux
          (fun x ↦ φ (x, t))) :
    ∃ ψ : ℂ × (Fin j → ℂ) → Fin k → ℂ,
      AnalyticOnNhd ℂ ψ (Ux ×ˢ Vx) ∧
      (∀ t ∈ Vx,
        IsHolomorphicSystemSolutionOn
          {p : ℂ × (Fin k → ℂ) | (p.1, p.2, t) ∈ Ω}
          (fun x y ↦ F x y t)
          0
          0
          Ux
          (fun x ↦ ψ (x, t))) := by
  -- Route correction: isolate the genuine source-faithful core after shrinking to a fixed product
  -- neighborhood, so the remaining blocker is only the formal `aₙ(t)` majorant construction.
  -- TODO: implement the `x`-degree formal recursion, scalar majorant, and evaluation on `Ux ×ˢ Vx`.
  sorry

/-- Helper for Theorem 2: first shrink the given `(x, t)`-neighborhood to a product neighborhood,
then apply the source-faithful comparison-family construction on that product set. -/
lemma exists_analytic_comparison_family
    {k j : ℕ} {Ω : Set (ℂ × (Fin k → ℂ) × (Fin j → ℂ))}
    {F : ℂ → (Fin k → ℂ) → (Fin j → ℂ) → Fin k → ℂ}
    {V : Set (Fin j → ℂ)} {W : Set (ℂ × (Fin j → ℂ))}
    {φ : ℂ × (Fin j → ℂ) → Fin k → ℂ}
    (hF : AnalyticOnNhd ℂ (fun p : ℂ × (Fin k → ℂ) × (Fin j → ℂ) ↦ F p.1 p.2.1 p.2.2) Ω)
    (hV : IsOpen V) (h0V : (0 : Fin j → ℂ) ∈ V)
    (hW : IsOpen W) (h0W : ((0 : ℂ), 0) ∈ W)
    (hsol :
      ∀ t ∈ V,
        IsHolomorphicSystemSolutionOn
          {p : ℂ × (Fin k → ℂ) | (p.1, p.2, t) ∈ Ω}
          (fun x y ↦ F x y t)
          0
          0
          {x : ℂ | (x, t) ∈ W}
          (fun x ↦ φ (x, t))) :
      ∃ Ux : Set ℂ, ∃ Vx : Set (Fin j → ℂ), ∃ ψ : ℂ × (Fin j → ℂ) → Fin k → ℂ,
      IsOpen Ux ∧ IsOpen Vx ∧
      (0 : ℂ) ∈ Ux ∧ (0 : Fin j → ℂ) ∈ Vx ∧
      AnalyticOnNhd ℂ ψ (Ux ×ˢ Vx) ∧
      (∀ t ∈ Vx,
        IsHolomorphicSystemSolutionOn
          {p : ℂ × (Fin k → ℂ) | (p.1, p.2, t) ∈ Ω}
          (fun x y ↦ F x y t)
          0
          0
          Ux
          (fun x ↦ ψ (x, t))) := by
  -- First shrink the ambient `(x, t)`-neighborhood to a product neighborhood around the origin.
  rcases exists_product_neighborhood_subordinate_to_W hW h0W with
    ⟨Ux, Vw, hUx, hVw, h0Ux, h0Vw, hprodW⟩
  let Vx : Set (Fin j → ℂ) := V ∩ Vw
  have hVx : IsOpen Vx := hV.inter hVw
  have h0Vx : (0 : Fin j → ℂ) ∈ Vx := ⟨h0V, h0Vw⟩
  have hVxsub : Vx ⊆ V := fun t ht ↦ ht.1
  have hWsub : Ux ×ˢ Vx ⊆ W := by
    intro z hz
    exact hprodW ⟨hz.1, hz.2.2⟩
  have hsol' :
      ∀ t ∈ Vx,
        IsHolomorphicSystemSolutionOn
          {p : ℂ × (Fin k → ℂ) | (p.1, p.2, t) ∈ Ω}
          (fun x y ↦ F x y t)
          0
          0
          Ux
          (fun x ↦ φ (x, t)) := by
    intro t ht
    have hbase := hsol t ht.1
    refine hbase.restrict hUx h0Ux ?_ ?_
    · intro x hx
      exact hWsub ⟨hx, ht⟩
    · intro x hx
      exact hbase.mapsTo (hWsub ⟨hx, ht⟩)
  -- Then the source proof's remaining content is exactly the majorant construction on that fixed
  -- product neighborhood.
  rcases exists_analytic_comparison_family_on_product_neighborhood
      (V := V) (W := W) hF hUx hVx h0Ux h0Vx hWsub hVxsub hsol' with
    ⟨ψ, hψanalytic, hψsol⟩
  exact ⟨Ux, Vx, ψ, hUx, hVx, h0Ux, h0Vx, hψanalytic, hψsol⟩

/-- Theorem 2: let `F (x, y, t)` be holomorphic on a coefficient domain `Ω` in the sense of
`AnalyticOnNhd`, and let `φ (x, t)` be a family of local solutions with zero initial value such
that, on an open neighborhood `W` of `((0 : ℂ), 0)` in `(x, t)`-space and for each parameter
`t` near `0`, the slice `x ↦ φ (x, t)` is a local holomorphic solution of
`dφ/dx = F (x, φ, t)` in the sense of `IsHolomorphicSystemSolutionOn`. Then the solution
components `φᵢ (x, t₁, ..., tⱼ)` are analytic in the `j + 1` variables `(x, t₁, ..., tⱼ)` near
the origin. -/
theorem analyticAt_origin_of_holomorphic_ode_solution_family
    {k j : ℕ} {Ω : Set (ℂ × (Fin k → ℂ) × (Fin j → ℂ))}
    {F : ℂ → (Fin k → ℂ) → (Fin j → ℂ) → Fin k → ℂ}
    {V : Set (Fin j → ℂ)} {W : Set (ℂ × (Fin j → ℂ))}
    {φ : ℂ × (Fin j → ℂ) → Fin k → ℂ}
    (hF : AnalyticOnNhd ℂ (fun p : ℂ × (Fin k → ℂ) × (Fin j → ℂ) ↦ F p.1 p.2.1 p.2.2) Ω)
    (hV : IsOpen V) (h0V : (0 : Fin j → ℂ) ∈ V)
    (hW : IsOpen W) (h0W : ((0 : ℂ), 0) ∈ W)
    (hsol :
      ∀ t ∈ V,
        IsHolomorphicSystemSolutionOn
          {p : ℂ × (Fin k → ℂ) | (p.1, p.2, t) ∈ Ω}
          (fun x y ↦ F x y t)
          0
          0
          {x : ℂ | (x, t) ∈ W}
          (fun x ↦ φ (x, t))) :
    AnalyticAt ℂ φ ((0 : ℂ), 0) := by
  -- The source proof first constructs a jointly analytic comparison family from the
  -- parameter-valued formal ODE and a geometric majorant.
  rcases exists_analytic_comparison_family hF hV h0V hW h0W hsol with
    ⟨Ux, Vx, ψ, hUx, hVx, h0Ux, h0Vx, hψanalytic, hψsol⟩
  -- Once that comparison family exists, the already-verified uniqueness machinery transfers its
  -- analyticity back to the original solution family.
  exact analyticAt_origin_of_holomorphic_ode_solution_family_of_comparison_family
    hF hV h0V hW h0W hsol hUx hVx h0Ux h0Vx hψanalytic hψsol
