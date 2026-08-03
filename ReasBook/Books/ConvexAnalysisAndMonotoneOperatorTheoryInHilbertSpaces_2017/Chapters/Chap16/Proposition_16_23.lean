import Mathlib
import BauschkeLean.Chap08.Corollary_8_40
import BauschkeLean.Chap08.Definition_8_7
import BauschkeLean.Chap10.Example_10_31
import BauschkeLean.Chap10.Definition_10_27
import BauschkeLean.Chap11.Proposition_11_7
import BauschkeLean.Chap11.Definition_11_11
import BauschkeLean.Chap16.Proposition_16_17
import BauschkeLean.Chap16.Proposition_16_4

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search tool `lean_leansearch` was unavailable in this environment; local precedent was
-- checked in Proposition 11.7, Example 10.30, Example 10.31, and Definition 11.11.

universe u

namespace ERealFunction

section RadialEvenConvex

open scoped InnerProductSpace

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Strict quasiconvexity for a real-valued function, expressed through the chapter's
extended-real-valued owner. -/
def StrictlyQuasiconvexReal (f : H → ℝ) : Prop :=
  StrictlyQuasiconvex f.toEReal.asEReal

/-- Coercivity for a real-valued function, expressed through the chapter's extended-real-valued
owner. -/
def CoerciveReal (f : H → ℝ) : Prop :=
  Coercive f.toEReal.asEReal

/-- Helper for Proposition 16.23: convexity on all of `ℝ` forces every point to be in the
effective domain. -/
theorem effectiveDomain_eq_univ_of_convexOn_univ
    (φ : ℝ → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn φ Set.univ) :
    effectiveDomain φ = Set.univ := by
  ext t
  constructor
  · intro _
    simp
  · intro _
    exact hconv.subset_effectiveDomain (by simp)

/-- Helper for Proposition 16.23: the finite representative of `φ` is strictly increasing on the
range of the norm map. -/
theorem strictMono_toReal_on_norm_range_of_even_convexOn_eq_zero_iff
    (φ : ℝ → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn φ Set.univ)
    (heven : Function.Even φ)
    (hzero : ∀ t : ℝ, (φ t : EReal) = 0 ↔ t = 0) :
    StrictMono (fun s : Set.range (norm : H → ℝ) ↦ (φ s : EReal).toReal) := by
  let _ := (inferInstance : InnerProductSpace ℝ H)
  let _ := (inferInstance : CompleteSpace H)
  let hdom := effectiveDomain_eq_univ_of_convexOn_univ φ hconv
  have hconv_dom : ConvexOn φ (effectiveDomain φ) := by
    simpa [hdom] using hconv
  have hevenE : Function.Even φ.asEReal := by
    intro t
    exact congrArg (fun z : Set.Ioi (⊥ : EReal) ↦ (z : EReal)) (heven t)
  have hmono :
      StrictMonoOn φ.asEReal (Set.Ici 0) :=
    strictMonoOn_nonnegative_of_even_convexOn_eq_zero_iff φ hconv_dom hevenE hzero
  intro s t hst
  have hs0 : (s : ℝ) ∈ Set.Ici (0 : ℝ) := by
    rcases s.2 with ⟨x, hx⟩
    simp [← hx, norm_nonneg x]
  have ht0 : (t : ℝ) ∈ Set.Ici (0 : ℝ) := by
    rcases t.2 with ⟨x, hx⟩
    simp [← hx, norm_nonneg x]
  have hstE : (φ (s : ℝ) : EReal) < (φ (t : ℝ) : EReal) :=
    hmono hs0 ht0 hst
  have hs_eff : (s : ℝ) ∈ effectiveDomain φ := by
    simp [hdom]
  have ht_eff : (t : ℝ) ∈ effectiveDomain φ := by
    simp [hdom]
  have hs_top : (φ (s : ℝ) : EReal) ≠ ⊤ := by
    exact ne_of_lt ((mem_effectiveDomain_iff).1 hs_eff)
  have ht_top : (φ (t : ℝ) : EReal) ≠ ⊤ := by
    exact ne_of_lt ((mem_effectiveDomain_iff).1 ht_eff)
  have hs_bot : (φ (s : ℝ) : EReal) ≠ ⊥ := by
    exact ne_of_gt (φ s).2
  have ht_bot : (φ (t : ℝ) : EReal) ≠ ⊥ := by
    exact ne_of_gt (φ t).2
  have hst_toReal :
      (((φ (s : ℝ) : EReal).toReal : ℝ) : EReal) <
        (((φ (t : ℝ) : EReal).toReal : ℝ) : EReal) := by
    simpa [EReal.coe_toReal hs_top hs_bot, EReal.coe_toReal ht_top ht_bot] using hstE
  exact_mod_cast hst_toReal

/-- Helper for Proposition 16.23: a subgradient at `1` gives the scalar affine lower bound used in
the coercivity argument. -/
theorem subgradient_real_lower_bound_at_one
    (φ : ℝ → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn φ Set.univ)
    {ν : ℝ} (hν : ν ∈ (∂ φ) 1) :
    ∀ η : ℝ, (η - 1) * ν ≤ (φ η : EReal).toReal - (φ 1 : EReal).toReal := by
  let hdom := effectiveDomain_eq_univ_of_convexOn_univ φ hconv
  have h1_eff : (1 : ℝ) ∈ effectiveDomain φ := by
    simp [hdom]
  -- Rewrite subgradient membership through the half-space description at the finite point `1`.
  have hhalf :
      ν ∈ ⋂ y ∈ effectiveDomain φ,
        {u : ℝ | ⟪y - 1, u⟫_ℝ ≤ (φ y : EReal).toReal - (φ 1 : EReal).toReal} := by
    simpa [subdifferential_eq_iInter_affine_halfspaces φ 1 h1_eff] using hν
  intro η
  have hη_eff : η ∈ effectiveDomain φ := by
    simp [hdom]
  have hη := (Set.mem_iInter₂.mp hhalf) η hη_eff
  -- On `ℝ`, the inner product is ordinary multiplication, so the affine half-space is scalar.
  simpa [RCLike.inner_apply', mul_comm] using hη

/-- Helper for Proposition 16.23: the scalar subdifferential at `1` contains a positive slope. -/
theorem exists_positive_subgradient_at_one
    (φ : ℝ → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn φ Set.univ)
    (heven : Function.Even φ)
    (hzero : ∀ t : ℝ, (φ t : EReal) = 0 ↔ t = 0) :
    ∃ ν : ℝ, 0 < ν ∧ ν ∈ (∂ φ) 1 := by
  let hdom := effectiveDomain_eq_univ_of_convexOn_univ φ hconv
  have hconv_dom : ConvexOn φ (effectiveDomain φ) := by
    simpa [hdom] using hconv
  have hevenE : Function.Even φ.asEReal := by
    intro t
    exact congrArg (fun z : Set.Ioi (⊥ : EReal) ↦ (z : EReal)) (heven t)
  have hscalar_convex :
      _root_.ConvexOn ℝ Set.univ (fun t : ℝ ↦ (φ t : EReal).toReal) := by
    -- Replace the finite-valued convex restriction on the effective domain by its global
    -- representative once the effective domain is known to be all of `ℝ`.
    simpa [hdom] using hconv_dom.toReal_convexOn_effectiveDomain
  have hcont_one : ContinuousAtOnEffectiveDomain φ (1 : ℝ) := by
    refine ⟨?_, ?_⟩
    · simp [hdom]
    · have hcont_toReal :
          Continuous (fun t : ℝ ↦ (φ t : EReal).toReal) :=
        continuous_of_convexOn_univ (fun t : ℝ ↦ (φ t : EReal).toReal) hscalar_convex
      simpa [hdom] using hcont_toReal.continuousAt.continuousWithinAt
  have hsubdiff :
      ((∂ φ) (1 : ℝ)).Nonempty := by
    exact
      (subdifferential_nonempty_and_weaklyCompact_of_continuousAtOnEffectiveDomain
        φ hconv_dom (x := 1) hcont_one).1
  rcases hsubdiff with ⟨ν, hνsub⟩
  -- Route correction: use the source proof's global-minimizer-at-zero argument rather than
  -- re-deriving positivity of `φ 1` from strict monotonicity on `[0, +∞)`.
  have hzero_min : IsMinOn φ.asEReal Set.univ 0 :=
    isMinOn_zero_of_even_convexOn φ hconv_dom hevenE
  have hφ0_eq : (φ 0 : EReal) = 0 := (hzero 0).2 rfl
  have hφ0_le_φ1 : (φ 0 : EReal) ≤ (φ 1 : EReal) :=
    (isMinOn_univ_iff.mp hzero_min) 1
  have hφ1_ne_zero : (φ 1 : EReal) ≠ 0 := by
    intro hφ1_zero
    have h1_eq_zero : (1 : ℝ) = 0 := (hzero 1).1 hφ1_zero
    norm_num at h1_eq_zero
  have hφ1_pos_EReal : (0 : EReal) < (φ 1 : EReal) := by
    rw [← hφ0_eq]
    exact lt_of_le_of_ne hφ0_le_φ1 (by
      intro h01
      apply hφ1_ne_zero
      rw [← h01, hφ0_eq])
  have h1_eff : (1 : ℝ) ∈ effectiveDomain φ := by
    simp [hdom]
  have hφ1_top : (φ 1 : EReal) ≠ ⊤ := by
    exact ne_of_lt ((mem_effectiveDomain_iff).1 h1_eff)
  have hφ1_bot : (φ 1 : EReal) ≠ ⊥ := by
    exact ne_of_gt (φ 1).2
  have hφ1_pos :
      0 < (φ 1 : EReal).toReal := by
    have htoReal :
        (((0 : EReal).toReal : ℝ) : EReal) < (((φ 1 : EReal).toReal : ℝ) : EReal) := by
      simpa [EReal.coe_toReal hφ1_top hφ1_bot] using hφ1_pos_EReal
    exact_mod_cast htoReal
  have hlower_zero := subgradient_real_lower_bound_at_one φ hconv hνsub 0
  have hφ0 : (φ 0 : EReal).toReal = 0 := by
    rw [(hzero 0).2 rfl]
    simp
  have hφ1_le_ν : (φ 1 : EReal).toReal ≤ ν := by
    linarith
  exact ⟨ν, lt_of_lt_of_le hφ1_pos hφ1_le_ν, hνsub⟩

/-- Helper for Proposition 16.23: evaluating the scalar subgradient inequality at `‖x‖` yields
the radial affine lower bound used in the coercivity proof. -/
theorem radial_affine_lower_bound_at_norm
    (φ : ℝ → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn φ Set.univ)
    {ν : ℝ} (hν : ν ∈ (∂ φ) 1) :
    ∀ x : H, ((‖x‖ - 1) * ν + (φ 1 : EReal).toReal) ≤ (φ ‖x‖ : EReal).toReal := by
  let _ := (inferInstance : InnerProductSpace ℝ H)
  let _ := (inferInstance : CompleteSpace H)
  intro x
  -- Specialize the scalar lower bound at the radial variable `η = ‖x‖`.
  have hsub := subgradient_real_lower_bound_at_one φ hconv hν ‖x‖
  linarith

/-- Proposition 16.23 (1): let `φ : ℝ → ]-∞,+∞]` be even and convex and vanish only
at `0`. Setting `f = φ ∘ ‖·‖` and viewing the resulting extended-real values through their real
representatives, the radial function is continuous. -/
theorem proposition_16_23_continuous
    (φ : ℝ → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn φ Set.univ)
    (heven : Function.Even φ)
    (hzero : ∀ t : ℝ, (φ t : EReal) = 0 ↔ t = 0) :
    Continuous (fun x : H ↦ (φ ‖x‖ : EReal).toReal) := by
  let _ := (inferInstance : InnerProductSpace ℝ H)
  let _ := (inferInstance : CompleteSpace H)
  let _ := heven
  let _ := hzero
  let hdom := effectiveDomain_eq_univ_of_convexOn_univ φ hconv
  have hconv_dom : ConvexOn φ (effectiveDomain φ) := by
    simpa [hdom] using hconv
  have hscalar_convex :
      _root_.ConvexOn ℝ Set.univ (fun t : ℝ ↦ (φ t : EReal).toReal) := by
    -- First move to the finite representative on the effective domain, then rewrite that domain
    -- to `Set.univ`.
    simpa [hdom] using hconv_dom.toReal_convexOn_effectiveDomain
  have hscalar_cont :
      Continuous (fun t : ℝ ↦ (φ t : EReal).toReal) :=
    continuous_of_convexOn_univ (fun t : ℝ ↦ (φ t : EReal).toReal) hscalar_convex
  -- The target is the scalar continuous map composed with the continuous norm.
  simpa using hscalar_cont.comp continuous_norm

/-- Proposition 16.23 (2): under the same hypotheses, the radial function
`φ ∘ ‖·‖` is strictly quasiconvex. -/
theorem proposition_16_23_strictlyQuasiconvex
    (φ : ℝ → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn φ Set.univ)
    (heven : Function.Even φ)
    (hzero : ∀ t : ℝ, (φ t : EReal) = 0 ↔ t = 0) :
    StrictlyQuasiconvexReal (fun x : H ↦ (φ ‖x‖ : EReal).toReal) := by
  let ψ : Set.range (norm : H → ℝ) → ℝ := fun s ↦ (φ s : EReal).toReal
  have hψ :
      StrictMono ψ :=
    strictMono_toReal_on_norm_range_of_even_convexOn_eq_zero_iff φ hconv heven hzero
  have hnorm :
      StrictlyQuasiconvex ((norm : H → ℝ).toEReal.asEReal) :=
    strictlyQuasiconvex_norm
  -- Combine strict quasiconvexity of the norm with strict increase of the scalar radial profile.
  simpa [StrictlyQuasiconvexReal, ψ] using
    (strictlyQuasiconvex_comp_strictMono_range hnorm hψ)

/-- Proposition 16.23 (3): under the same hypotheses, the radial function
`φ ∘ ‖·‖` is coercive. -/
theorem proposition_16_23_coercive
    (φ : ℝ → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn φ Set.univ)
    (heven : Function.Even φ)
    (hzero : ∀ t : ℝ, (φ t : EReal) = 0 ↔ t = 0) :
    CoerciveReal (fun x : H ↦ (φ ‖x‖ : EReal).toReal) := by
  obtain ⟨ν, hν_pos, hνsub⟩ :=
    exists_positive_subgradient_at_one φ hconv heven hzero
  have hradial_lower :
      ∀ x : H,
        ((‖x‖ - 1) * ν + (φ 1 : EReal).toReal) ≤ (φ ‖x‖ : EReal).toReal := by
    -- Use the dedicated radial affine minorant helper to keep the coercive tail flat.
    exact radial_affine_lower_bound_at_norm φ hconv hνsub
  -- Turn the affine lower bound with positive slope into convergence to `+∞` along `‖x‖ → +∞`.
  rw [CoerciveReal, coercive_iff_tendsto_norm_atTop, EReal.tendsto_nhds_top_iff_real]
  intro ξ
  let c : ℝ := (φ 1 : EReal).toReal
  let R : ℝ := 1 + (ξ - c + 1) / ν
  have htail :
      ∀ᶠ x : H in Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop, R ≤ ‖x‖ := by
    exact
      (Filter.tendsto_comap :
        Filter.Tendsto (fun x : H ↦ ‖x‖)
          (Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop) Filter.atTop).eventually_ge_atTop R
  filter_upwards [htail] with x hx
  have hsub := hradial_lower x
  have hgrowth : ξ + 1 ≤ ((‖x‖ - 1) * ν + c) := by
    have hdiv : (ξ - c + 1) / ν ≤ ‖x‖ - 1 := by
      dsimp [R, c] at hx
      linarith
    have hmul : ξ - c + 1 ≤ (‖x‖ - 1) * ν := by
      exact (div_le_iff₀ hν_pos).1 hdiv
    linarith
  have hlt_real : ξ < (φ ‖x‖ : EReal).toReal := by
    linarith
  have hlt_ereal : ((ξ : ℝ) : EReal) < (((φ ‖x‖ : EReal).toReal : ℝ) : EReal) := by
    exact_mod_cast hlt_real
  simpa [Function.toEReal_apply, Function.asEReal_apply] using hlt_ereal

end RadialEvenConvex

end ERealFunction
