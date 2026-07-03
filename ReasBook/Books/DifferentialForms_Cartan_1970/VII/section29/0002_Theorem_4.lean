import DifferentialForms_Cartan_1970.VII.section27.«0001_Theorem_I»
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter Set
open scoped Topology

/-- The `k`-jet `(φ, φ', ..., φ^(k - 1))` of a scalar function. -/
noncomputable def higherOrderHolomorphicOdeJet (k : ℕ) (φ : ℂ → ℂ) : ℂ → Fin k → ℂ :=
  fun z i ↦ iteratedDeriv (i : ℕ) φ z

/-- The canonical first-order jet system attached to
`y^(k) = F (x, y, y', ..., y^(k - 1))`. -/
def higherOrderHolomorphicOdeSystem
    (k : ℕ) (F : ℂ × (Fin k → ℂ) → ℂ) : ℂ → (Fin k → ℂ) → Fin k → ℂ :=
  fun z y i ↦
    if h : i.1 + 1 < k then
      y ⟨i.1 + 1, h⟩
    else
      F (z, y)

/-- A local holomorphic solution on an open set of the first-order jet system associated to the
`k`th-order scalar equation. -/
abbrev IsHigherOrderHolomorphicOdeSolutionOn
    (k : ℕ) (F : ℂ × (Fin k → ℂ) → ℂ) (x₀ : ℂ) (y₀ : Fin k → ℂ)
    (U : Set ℂ) (φ : ℂ → ℂ) : Prop :=
  IsHolomorphicSystemSolutionOn
    Set.univ
    (higherOrderHolomorphicOdeSystem k F)
    x₀
    y₀
    U
    (higherOrderHolomorphicOdeJet k φ)

theorem higherOrderHolomorphicOdeJet_eventuallyEq
    {k : ℕ} {x₀ : ℂ} {φ ψ : ℂ → ℂ} (hφψ : φ =ᶠ[𝓝 x₀] ψ) :
    higherOrderHolomorphicOdeJet k φ =ᶠ[𝓝 x₀] higherOrderHolomorphicOdeJet k ψ := by
  -- Eventual equality is preserved by each iterated derivative coordinate.
  filter_upwards
    [Filter.eventually_all.mpr fun i : Fin k ↦ hφψ.iteratedDeriv (i : ℕ)] with z hz
  ext i
  exact hz i

/-- Helper for Theorem 4: analyticity of the scalar right-hand side implies analyticity of the
associated first-order jet system. -/
theorem higher_order_holomorphic_ode_system_analyticOnNhd
    {k : ℕ} {F : ℂ × (Fin k → ℂ) → ℂ} {Ω : Set (ℂ × (Fin k → ℂ))}
    (hFΩ : AnalyticOnNhd ℂ F Ω) :
    AnalyticOnNhd ℂ
      (fun p : ℂ × (Fin k → ℂ) ↦ higherOrderHolomorphicOdeSystem k F p.1 p.2) Ω := by
  -- Check analyticity componentwise, since the system takes values in a finite product.
  rw [analyticOnNhd_pi_iff]
  intro i p hp
  by_cases hi : i.1 + 1 < k
  · let j : Fin k := ⟨i.1 + 1, hi⟩
    -- On nonterminal components the system is just the next-coordinate projection.
    simpa [higherOrderHolomorphicOdeSystem, hi, j] using
      (((ContinuousLinearMap.proj (R := ℂ) j).comp
        (ContinuousLinearMap.snd ℂ ℂ (Fin k → ℂ))).analyticAt p)
  · -- On the terminal component the system reduces to the original scalar right-hand side.
    simpa [higherOrderHolomorphicOdeSystem, hi] using hFΩ p hp

/-- The induced `k`-jet map on scalar holomorphic germs. -/
noncomputable def higherOrderHolomorphicOdeJetGerm (x₀ : ℂ) (k : ℕ) :
    Germ (𝓝 x₀) ℂ → Germ (𝓝 x₀) (Fin k → ℂ) :=
  Germ.map' (higherOrderHolomorphicOdeJet k) fun _ _ hφψ ↦
    higherOrderHolomorphicOdeJet_eventuallyEq hφψ

@[simp] theorem higherOrderHolomorphicOdeJetGerm_coe
    {k : ℕ} {x₀ : ℂ} (φ : ℂ → ℂ) :
    higherOrderHolomorphicOdeJetGerm x₀ k (φ : Germ (𝓝 x₀) ℂ) =
      ((higherOrderHolomorphicOdeJet k φ) : Germ (𝓝 x₀) (Fin k → ℂ)) :=
  rfl

/-- Helper for Theorem 4: translating the scalar variable translates the entire jet
componentwise. -/
theorem higher_order_holomorphic_odeJet_comp_sub_const
    {k : ℕ} {φ : ℂ → ℂ} {a : ℂ} :
    higherOrderHolomorphicOdeJet k (fun z ↦ φ (z - a)) =
      fun z ↦ higherOrderHolomorphicOdeJet k φ (z - a) := by
  -- The shift invariance of iterated derivatives applies coordinatewise to the jet.
  ext z i
  simp [higherOrderHolomorphicOdeJet, iteratedDeriv_comp_sub_const]

/-- A local holomorphic solution germ of the `k`th-order differential equation with initial jet
`y₀` at `x₀`, expressed through the canonical first-order jet system from section 27. -/
def IsHigherOrderHolomorphicOdeSolution
    (k : ℕ) (F : ℂ × (Fin k → ℂ) → ℂ) (x₀ : ℂ) (y₀ : Fin k → ℂ)
    (φ : Germ (𝓝 x₀) ℂ) : Prop :=
  IsHolomorphicSystemSolution
    Set.univ
    (higherOrderHolomorphicOdeSystem k F)
    x₀
    y₀
    (higherOrderHolomorphicOdeJetGerm x₀ k φ)

/-- An open-set jet-system solution induces the corresponding higher-order solution germ. -/
theorem IsHigherOrderHolomorphicOdeSolutionOn.isHigherOrderHolomorphicOdeSolution
    {k : ℕ} {F : ℂ × (Fin k → ℂ) → ℂ} {x₀ : ℂ} {y₀ : Fin k → ℂ}
    {U : Set ℂ} {φ : ℂ → ℂ} (h : IsHigherOrderHolomorphicOdeSolutionOn k F x₀ y₀ U φ) :
    IsHigherOrderHolomorphicOdeSolution k F x₀ y₀ (φ : Germ (𝓝 x₀) ℂ) := by
  -- Passing from an open-set representative to the corresponding germ is built into section 27.
  simpa [IsHigherOrderHolomorphicOdeSolution] using h.isHolomorphicSystemSolution

/-- Helper for Theorem 4: replacing a representative by an equal one on the open solution domain
preserves the first-order system solution predicate. -/
theorem IsHolomorphicSystemSolutionOn.congr
    {n : ℕ} {Ω : Set (ℂ × (Fin n → ℂ))} {f : ℂ → (Fin n → ℂ) → Fin n → ℂ}
    {x₀ : ℂ} {b : Fin n → ℂ} {U : Set ℂ} {φ ψ : ℂ → Fin n → ℂ}
    (hφ : IsHolomorphicSystemSolutionOn Ω f x₀ b U φ)
    (hEq : ∀ ⦃z : ℂ⦄, z ∈ U → ψ z = φ z) :
    IsHolomorphicSystemSolutionOn Ω f x₀ b U ψ := by
  refine ⟨hφ.isOpen, hφ.mem, ?_, ?_, ?_, ?_⟩
  · -- Analyticity is local on the open domain, so pointwise equality there preserves it.
    exact AnalyticOnNhd.congr hφ.isOpen hφ.analytic fun z hz ↦ (hEq hz).symm
  · -- The graph condition is unchanged because the two representatives agree on `U`.
    intro z hz
    simpa [hEq hz] using hφ.mapsTo hz
  · -- The initial value is read off at the basepoint inside `U`.
    simpa [hEq hφ.mem] using hφ.initial
  · intro z hz
    -- Differentiate the eventual equality coming from the open neighborhood around `z`.
    have hEventually : ψ =ᶠ[𝓝 z] φ := by
      filter_upwards [hφ.isOpen.mem_nhds hz] with w hw
      exact hEq hw
    have hDeriv : HasDerivAt ψ (f z (φ z)) z :=
      (hφ.deriv_eq hz).congr_of_eventuallyEq hEventually
    simpa [hEq hz] using hDeriv

/-- Helper for Theorem 4: an unconstrained local system solution can be restricted to a smaller
open neighborhood whose graph lies in any open coefficient domain containing the initial point. -/
theorem restrict_holomorphic_system_solutionOn_to_domain
    {n : ℕ} {Ω : Set (ℂ × (Fin n → ℂ))} (hΩ : IsOpen Ω)
    {f : ℂ → (Fin n → ℂ) → Fin n → ℂ} {x₀ : ℂ} {b : Fin n → ℂ}
    {U : Set ℂ} {φ : ℂ → Fin n → ℂ}
    (hxy : (x₀, b) ∈ Ω)
    (hφ : IsHolomorphicSystemSolutionOn Set.univ f x₀ b U φ) :
    ∃ V : Set ℂ, IsHolomorphicSystemSolutionOn Ω f x₀ b V φ := by
  -- Continuity of the graph at the initial point gives a ball whose image stays inside `Ω`.
  have hcontφ : ContinuousAt φ x₀ := (hφ.analytic x₀ hφ.mem).continuousAt
  have hcontGraph : ContinuousAt (fun z ↦ (z, φ z)) x₀ := continuousAt_id.prodMk hcontφ
  have hxy' : (x₀, φ x₀) ∈ Ω := by
    simpa [hφ.initial] using hxy
  have hpre : (fun z ↦ (z, φ z)) ⁻¹' Ω ∈ 𝓝 x₀ :=
    hcontGraph.preimage_mem_nhds (hΩ.mem_nhds hxy')
  have hU : U ∈ 𝓝 x₀ := hφ.isOpen.mem_nhds hφ.mem
  rcases Metric.mem_nhds_iff.mp (Filter.inter_mem hU hpre) with ⟨r, hrpos, hrsub⟩
  let V : Set ℂ := Metric.ball x₀ r
  refine ⟨V, ?_⟩
  refine ⟨Metric.isOpen_ball, ?_, ?_, ?_, hφ.initial, ?_⟩
  · -- The chosen ball is a neighborhood of the initial point.
    simpa [V] using hrpos
  · -- Restrict analyticity from the original open solution domain.
    exact hφ.analytic.mono fun z hz ↦ (hrsub hz).1
  · -- The ball was chosen so that the graph lands in `Ω`.
    intro z hz
    exact (hrsub hz).2
  · intro z hz
    -- The differential equation is inherited from the original larger-domain solution.
    exact hφ.deriv_eq ((hrsub hz).1)

/-- Helper for Theorem 4: recentering a first-order system solution from `x₀` to `0` translates
both the domain variable and the coefficient domain. -/
theorem recenter_holomorphic_system_solutionOn
    {n : ℕ} {Ω : Set (ℂ × (Fin n → ℂ))} {f : ℂ → (Fin n → ℂ) → Fin n → ℂ}
    {x₀ : ℂ} {b : Fin n → ℂ} {V : Set ℂ} {φ : ℂ → Fin n → ℂ}
    (hφ : IsHolomorphicSystemSolutionOn Ω f x₀ b V φ) :
    IsHolomorphicSystemSolutionOn
      {p : ℂ × (Fin n → ℂ) | (p.1 + x₀, p.2) ∈ Ω}
      (fun z y ↦ f (z + x₀) y)
      0
      b
      ((fun z ↦ z + x₀) ⁻¹' V)
      (fun z ↦ φ (z + x₀)) := by
  refine ⟨hφ.isOpen.preimage (continuous_add_const x₀), ?_, ?_, ?_, ?_, ?_⟩
  · -- The translated domain still contains the recentered basepoint `0`.
    simpa using hφ.mem
  · -- Analyticity is preserved by composing with the translation `z ↦ z + x₀`.
    intro z hz
    have hshift : AnalyticAt ℂ (fun w : ℂ ↦ w + x₀) z := by
      simpa using analyticAt_id.add (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ ↦ x₀) z)
    simpa using (hφ.analytic (z + x₀) hz).comp_of_eq' hshift (by simp)
  · -- The graph condition is exactly the definition of the translated coefficient domain.
    intro z hz
    simpa using hφ.mapsTo hz
  · -- Evaluating at `0` recovers the original initial value at `x₀`.
    simpa using hφ.initial
  · intro z hz
    -- Translation in the independent variable does not change the derivative value.
    simpa using (hφ.deriv_eq hz).comp_add_const z x₀

/-- Helper for Theorem 4: translating a first-order system solution from `0` to `x₀` is the
inverse affine change of variables used in the existence step. -/
theorem translate_holomorphic_system_solutionOn_from_zero
    {n : ℕ} {f : ℂ → (Fin n → ℂ) → Fin n → ℂ}
    {x₀ : ℂ} {b : Fin n → ℂ} {U : Set ℂ} {φ : ℂ → Fin n → ℂ}
    (hφ :
      IsHolomorphicSystemSolutionOn Set.univ (fun z y ↦ f (z + x₀) y) 0 b U φ) :
    IsHolomorphicSystemSolutionOn
      Set.univ
      f
      x₀
      b
      ((fun z ↦ z - x₀) ⁻¹' U)
      (fun z ↦ φ (z - x₀)) := by
  refine ⟨hφ.isOpen.preimage (continuous_id.sub continuous_const), ?_, ?_, ?_, ?_, ?_⟩
  · -- The translated domain contains the original basepoint `x₀`.
    simpa using hφ.mem
  · -- Analyticity is preserved by composing with the inverse translation `z ↦ z - x₀`.
    intro z hz
    have hshift : AnalyticAt ℂ (fun w : ℂ ↦ w - x₀) z := by
      simpa using analyticAt_id.sub (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ ↦ x₀) z)
    simpa using (hφ.analytic (z - x₀) hz).comp_of_eq' hshift (by simp)
  · -- The target coefficient domain is `univ`, so the graph constraint is automatic.
    intro z hz
    simp
  · -- Evaluating at `x₀` lands back at the original initial value at `0`.
    simpa using hφ.initial
  · intro z hz
    -- The differential equation transports through the shift by `x₀`.
    simpa using (hφ.deriv_eq hz).comp_sub_const z x₀

/-- Helper for Theorem 4: a scalar solution of the shifted higher-order equation at `0` translates
to a scalar solution of the original equation at `x₀`. -/
theorem translated_higher_order_holomorphic_ode_solutionOn
    {k : ℕ} {F : ℂ × (Fin k → ℂ) → ℂ} {x₀ : ℂ} {y₀ : Fin k → ℂ}
    {U₀ : Set ℂ} {φ₀ : ℂ → ℂ}
    (hφ₀ :
      IsHigherOrderHolomorphicOdeSolutionOn
        k
        (fun p : ℂ × (Fin k → ℂ) ↦ F (p.1 + x₀, p.2))
        0
        y₀
        U₀
        φ₀) :
    IsHigherOrderHolomorphicOdeSolutionOn
      k
      F
      x₀
      y₀
      ((fun z ↦ z - x₀) ⁻¹' U₀)
      (fun z ↦ φ₀ (z - x₀)) := by
  have hsystem :
      IsHolomorphicSystemSolutionOn
        Set.univ
        (higherOrderHolomorphicOdeSystem k F)
        x₀
        y₀
        ((fun z ↦ z - x₀) ⁻¹' U₀)
        (fun z ↦ higherOrderHolomorphicOdeJet k φ₀ (z - x₀)) := by
    -- First translate the jet-system solution itself from `0` to `x₀`.
    have hshifted :
        IsHolomorphicSystemSolutionOn
          Set.univ
          (fun z y ↦ higherOrderHolomorphicOdeSystem k F (z + x₀) y)
          0
          y₀
          U₀
          (higherOrderHolomorphicOdeJet k φ₀) := by
      simpa [IsHigherOrderHolomorphicOdeSolutionOn, higherOrderHolomorphicOdeSystem] using hφ₀
    exact
      translate_holomorphic_system_solutionOn_from_zero
        (f := higherOrderHolomorphicOdeSystem k F)
        hshifted
  -- Then identify the translated jet with the jet of the translated scalar function.
  exact hsystem.congr fun z hz ↦ by
    simp [higher_order_holomorphic_odeJet_comp_sub_const]

/-- Helper for Theorem 4: a solution of the canonical first-order jet system is determined by its
first coordinate and equals the full jet of that coordinate. -/
theorem canonical_jet_system_solution_eq_jet_of_first_coordinate
    {k : ℕ} (hk : 0 < k) {Ω : Set (ℂ × (Fin k → ℂ))}
    {F : ℂ × (Fin k → ℂ) → ℂ} {x₀ : ℂ} {y₀ : Fin k → ℂ}
    {U : Set ℂ} {Ψ : ℂ → Fin k → ℂ}
    (hΨ : IsHolomorphicSystemSolutionOn Ω (higherOrderHolomorphicOdeSystem k F) x₀ y₀ U Ψ) :
    ∀ ⦃z : ℂ⦄, z ∈ U →
      higherOrderHolomorphicOdeJet k (fun w ↦ Ψ w ⟨0, hk⟩) z = Ψ z := by
  let i0 : Fin k := ⟨0, hk⟩
  have hcoord :
      ∀ (n : ℕ) (hn : n < k) ⦃z : ℂ⦄, z ∈ U →
        iteratedDeriv n (fun w ↦ Ψ w i0) z = Ψ z ⟨n, hn⟩ := by
    intro n
    induction n with
    | zero =>
        intro hn z hz
        -- The zeroth jet component is the function itself.
        simp [i0]
    | succ n ihn =>
        intro hn z hz
        have hn' : n < k := Nat.lt_of_succ_lt hn
        let inx : Fin k := ⟨n, hn'⟩
        let insucc : Fin k := ⟨n + 1, hn⟩
        have hEventually :
            iteratedDeriv n (fun w ↦ Ψ w i0) =ᶠ[𝓝 z] fun w ↦ Ψ w inx := by
          -- The induction hypothesis holds on the open solution domain,
          -- hence near each point of it.
          filter_upwards [hΨ.isOpen.mem_nhds hz] with w hw
          exact ihn hn' hw
        have hDerivCoord :
            deriv (fun w ↦ Ψ w inx) z = Ψ z insucc := by
          -- The system equation identifies the derivative of each coordinate with the next one.
          have hComponent :
              HasDerivAt (fun w ↦ Ψ w inx)
                ((higherOrderHolomorphicOdeSystem k F z (Ψ z)) inx) z :=
            (hasDerivAt_pi.mp (hΨ.deriv_eq hz)) inx
          calc
            deriv (fun w ↦ Ψ w inx) z =
                (higherOrderHolomorphicOdeSystem k F z (Ψ z)) inx := hComponent.deriv
            _ = Ψ z insucc := by
              simp [higherOrderHolomorphicOdeSystem, hn, inx, insucc]
        -- Differentiate the local identification of the previous jet component.
        calc
          iteratedDeriv (n + 1) (fun w ↦ Ψ w i0) z =
              deriv (iteratedDeriv n (fun w ↦ Ψ w i0)) z := by
                simp [iteratedDeriv_succ]
          _ = deriv (fun w ↦ Ψ w inx) z := hEventually.deriv_eq
          _ = Ψ z insucc := hDerivCoord
  intro z hz
  -- Assemble the componentwise identities into an equality of `Fin k`-valued functions.
  ext i
  exact hcoord i i.2 hz

/-- Helper for Theorem 4: equality of `k`-jets near `x₀` forces equality of the underlying scalar
functions near `x₀`. -/
theorem eventuallyEq_of_higherOrderHolomorphicOdeJet_eventuallyEq
    {k : ℕ} (hk : 0 < k) {x₀ : ℂ} {φ ψ : ℂ → ℂ}
    (hJet :
      higherOrderHolomorphicOdeJet k φ =ᶠ[𝓝 x₀] higherOrderHolomorphicOdeJet k ψ) :
    φ =ᶠ[𝓝 x₀] ψ := by
  let i0 : Fin k := ⟨0, hk⟩
  -- Read off the zeroth jet component, which is the original function value.
  filter_upwards [hJet] with z hz
  simpa [higherOrderHolomorphicOdeJet, i0] using congrArg (fun v : Fin k → ℂ ↦ v i0) hz

/-- Helper for Theorem 4: an eventual equality near `0` can be pulled back along the translation
`z ↦ z - x₀` to an eventual equality near `x₀`. -/
theorem eventuallyEq_comp_sub_const_of_eventuallyEq_zero
    {x₀ : ℂ} {α : Type*} {f g : ℂ → α}
    (hfg : f =ᶠ[𝓝 (0 : ℂ)] g) :
    (fun z ↦ f (z - x₀)) =ᶠ[𝓝 x₀] fun z ↦ g (z - x₀) := by
  -- The affine map `z ↦ z - x₀` sends `x₀` to `0`, so eventual equality pulls back along it.
  have hsub : Tendsto (fun z : ℂ ↦ z - x₀) (𝓝 x₀) (𝓝 (0 : ℂ)) := by
    simpa using (tendsto_id.sub tendsto_const_nhds : Tendsto
      (fun z : ℂ ↦ z - x₀) (𝓝 x₀) (𝓝 (x₀ - x₀)))
  exact hfg.comp_tendsto hsub

/-- Theorem 4: the `k`th-order holomorphic initial value problem
`y^(k) = F (x, y, y', ..., y^(k - 1))` with prescribed initial jet at `x₀`
has a unique local holomorphic solution germ. -/
theorem exists_unique_solution_germ_of_higher_order_holomorphic_ode
    {k : ℕ} (hk : 0 < k) {F : ℂ × (Fin k → ℂ) → ℂ} {x₀ : ℂ} {y₀ : Fin k → ℂ}
    (hF : AnalyticAt ℂ F (x₀, y₀)) :
    ∃! φ : Germ (𝓝 x₀) ℂ, IsHigherOrderHolomorphicOdeSolution k F x₀ y₀ φ := by
  let i0 : Fin k := ⟨0, hk⟩
  -- Route correction: the proof stays on the source-faithful first-order system route, but the
  -- key Lean step is to make the restriction and recentering interfaces explicit.
  obtain ⟨r, hrpos, hFΩball⟩ := hF.exists_ball_analyticOnNhd
  let Ω : Set (ℂ × (Fin k → ℂ)) := Metric.ball (x₀, y₀) r
  let Ω₀ : Set (ℂ × (Fin k → ℂ)) := {p | (p.1 + x₀, p.2) ∈ Ω}
  let Fshift : ℂ × (Fin k → ℂ) → ℂ := fun p ↦ F (p.1 + x₀, p.2)
  have hΩ : IsOpen Ω := Metric.isOpen_ball
  have hxyΩ : (x₀, y₀) ∈ Ω := by
    simpa [Ω] using hrpos
  have hΩ₀ : IsOpen Ω₀ := by
    -- The translated coefficient domain is the preimage of the original analytic neighborhood.
    have hcont :
        Continuous (fun p : ℂ × (Fin k → ℂ) ↦ (p.1 + x₀, p.2)) := by
      exact (continuous_fst.add continuous_const).prodMk continuous_snd
    exact hΩ.preimage hcont
  have h0Ω₀ : ((0 : ℂ), y₀) ∈ Ω₀ := by
    simpa [Ω₀] using hxyΩ
  have hFshiftΩ₀ : AnalyticOnNhd ℂ Fshift Ω₀ := by
    -- Compose the original analytic right-hand side with the affine translation on the first slot.
    refine hFΩball.comp ?_ ?_
    · intro p hp
      exact (analyticAt_fst.add analyticAt_const).prod analyticAt_snd
    · intro p hp
      simpa [Ω₀, Fshift] using hp
  have hsystemAnalytic :
      AnalyticOnNhd ℂ
        (fun p : ℂ × (Fin k → ℂ) ↦ higherOrderHolomorphicOdeSystem k Fshift p.1 p.2) Ω₀ :=
    higher_order_holomorphic_ode_system_analyticOnNhd hFshiftΩ₀
  rcases exists_eventuallyEq_unique_local_solution_holomorphic_system hΩ₀ h0Ω₀ hsystemAnalytic with
    ⟨U₀, Ψ₀, hΨ₀, huniq₀⟩
  let φ₀ : ℂ → ℂ := fun z ↦ Ψ₀ z i0
  have hjet_eq :
      ∀ ⦃z : ℂ⦄, z ∈ U₀ → higherOrderHolomorphicOdeJet k φ₀ z = Ψ₀ z :=
    canonical_jet_system_solution_eq_jet_of_first_coordinate hk hΨ₀
  have hjet_solution₀ :
      IsHigherOrderHolomorphicOdeSolutionOn k Fshift 0 y₀ U₀ φ₀ := by
    -- On the solution domain, the section-27 representative is exactly the jet of its first
    -- coordinate, so we can replace the representative by that canonical jet.
    have hjetΩ₀ :
        IsHolomorphicSystemSolutionOn
          Ω₀
          (higherOrderHolomorphicOdeSystem k Fshift)
          0
          y₀
          U₀
          (higherOrderHolomorphicOdeJet k φ₀) :=
      hΨ₀.congr fun z hz ↦ hjet_eq hz
    refine ⟨hjetΩ₀.isOpen, hjetΩ₀.mem, hjetΩ₀.analytic, ?_, hjetΩ₀.initial, ?_⟩
    · intro z hz
      simp
    · intro z hz
      exact hjetΩ₀.deriv_eq hz
  let φx : ℂ → ℂ := fun z ↦ φ₀ (z - x₀)
  have hφx_on :
      IsHigherOrderHolomorphicOdeSolutionOn k F x₀ y₀ ((fun z ↦ z - x₀) ⁻¹' U₀) φx :=
    translated_higher_order_holomorphic_ode_solutionOn hjet_solution₀
  have hφx :
      IsHigherOrderHolomorphicOdeSolution k F x₀ y₀ (φx : Germ (𝓝 x₀) ℂ) :=
    hφx_on.isHigherOrderHolomorphicOdeSolution
  refine ⟨(φx : Germ (𝓝 x₀) ℂ), hφx, ?_⟩
  intro ψ hψ
  rcases Quotient.exists_rep ψ with ⟨χ, rfl⟩
  -- Unpack the competing scalar germ into an arbitrary system representative of its jet germ.
  rcases hψ with ⟨U, Ψ, hΨ, hΨeq⟩
  have hχjet_eq_Ψ :
      higherOrderHolomorphicOdeJet k χ =ᶠ[𝓝 x₀] Ψ := by
    -- Rewrite the jet-germ identification using the canonical representative `χ`.
    change
      (Ψ : Germ (𝓝 x₀) (Fin k → ℂ)) =
        higherOrderHolomorphicOdeJetGerm x₀ k (χ : Germ (𝓝 x₀) ℂ) at hΨeq
    rw [higherOrderHolomorphicOdeJetGerm_coe] at hΨeq
    exact Germ.coe_eq.mp hΨeq.symm
  rcases restrict_holomorphic_system_solutionOn_to_domain hΩ hxyΩ hΨ with ⟨V, hV⟩
  have hV₀ :
      IsHolomorphicSystemSolutionOn
        Ω₀
        (fun z y ↦ higherOrderHolomorphicOdeSystem k F (z + x₀) y)
        0
        y₀
        ((fun z ↦ z + x₀) ⁻¹' V)
        (fun z ↦ Ψ (z + x₀)) := by
    simpa [Ω₀, Fshift, higherOrderHolomorphicOdeSystem] using
      recenter_holomorphic_system_solutionOn hV
  have hrec_eq :
      (fun z ↦ Ψ (z + x₀)) =ᶠ[𝓝 (0 : ℂ)] Ψ₀ :=
    huniq₀ _ _ hV₀
  have hΨ_eq_translated :
      Ψ =ᶠ[𝓝 x₀] fun z ↦ Ψ₀ (z - x₀) := by
    -- Pull the equality near `0` back to a neighborhood of `x₀`.
    have hpull := eventuallyEq_comp_sub_const_of_eventuallyEq_zero (x₀ := x₀) hrec_eq
    filter_upwards [hpull] with z hz
    simpa using hz
  have hjet₀_eventually :
      higherOrderHolomorphicOdeJet k φ₀ =ᶠ[𝓝 (0 : ℂ)] Ψ₀ := by
    -- The canonical jet identification holds on the open representative domain `U₀`.
    filter_upwards [hΨ₀.isOpen.mem_nhds hΨ₀.mem] with z hz
    exact hjet_eq hz
  have hjetx_eventually :
      higherOrderHolomorphicOdeJet k φx =ᶠ[𝓝 x₀] fun z ↦ Ψ₀ (z - x₀) := by
    -- Translate the canonical jet identification from `0` back to `x₀`.
    have hpull := eventuallyEq_comp_sub_const_of_eventuallyEq_zero (x₀ := x₀) hjet₀_eventually
    filter_upwards [hpull] with z hz
    simpa [φx, higher_order_holomorphic_odeJet_comp_sub_const] using hz
  have hχjet_eq_jetx :
      higherOrderHolomorphicOdeJet k χ =ᶠ[𝓝 x₀] higherOrderHolomorphicOdeJet k φx := by
    exact hχjet_eq_Ψ.trans (hΨ_eq_translated.trans hjetx_eventually.symm)
  -- Reading off the zeroth jet coordinate recovers equality of the scalar germs themselves.
  exact Germ.coe_eq.mpr (eventuallyEq_of_higherOrderHolomorphicOdeJet_eventuallyEq hk hχjet_eq_jetx)

/-- Representative-form bridge for Theorem 4. -/
theorem exists_eventuallyEq_unique_solution_of_higher_order_holomorphic_ode
    {k : ℕ} (hk : 0 < k) {F : ℂ × (Fin k → ℂ) → ℂ} {x₀ : ℂ} {y₀ : Fin k → ℂ}
    (hF : AnalyticAt ℂ F (x₀, y₀)) :
    ∃ φ : ℂ → ℂ,
      IsHigherOrderHolomorphicOdeSolution k F x₀ y₀ (φ : Germ (𝓝 x₀) ℂ) ∧
      ∀ ψ : ℂ → ℂ,
        IsHigherOrderHolomorphicOdeSolution k F x₀ y₀ (ψ : Germ (𝓝 x₀) ℂ) →
        ψ =ᶠ[𝓝 x₀] φ := by
  -- Unpack the unique germ from Theorem 4 into a representative-level eventual-equality statement.
  rcases exists_unique_solution_germ_of_higher_order_holomorphic_ode hk hF with ⟨φ, hφ, huniq⟩
  rcases Quotient.exists_rep φ with ⟨f, rfl⟩
  refine ⟨f, hφ, ?_⟩
  intro ψ hψ
  exact Germ.coe_eq.mp (huniq _ hψ)
