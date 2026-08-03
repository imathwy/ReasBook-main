import Mathlib
import BauschkeLean.Chap02.Proposition_2_58
import BauschkeLean.Chap12.Proposition_12_27
import BauschkeLean.Chap12.Proposition_12_30
import BauschkeLean.Chap12.Remark_12_24
import BauschkeLean.Chap13.Corollary_13_38
import BauschkeLean.Chap13.Proposition_13_23
import BauschkeLean.Chap13.Proposition_13_24
import BauschkeLean.Chap14.Remark_14_4
import BauschkeLean.Chap16.Proposition_16_44

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient InnerProductSpace

noncomputable section

universe u

namespace ERealFunction

section SubdifferentialRigidity

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {f g : H → Set.Ioi (⊥ : EReal)}

/- Source/core/bridge triage:
- `source-facing`: Proposition 22.19 is the uniqueness-up-to-constant statement for two
  `Γ₀(H)` potentials with the same subdifferential.
- `core/canonical`: the owner abstractions are the Chapter 9 class of proper lower
  semicontinuous convex functions `Γ₀(H)` and the Chapter 16 subdifferential owner `∂`.
- `bridge/view`: Chapter 24 reuses this theorem after converting equality of proximity operators
  to equality of subdifferentials, so this file remains the canonical owner for the
  constant-difference conclusion itself. -/

/-- Helper for Proposition 22.19: equal subdifferentials force the same proximal operator. -/
lemma eq_proximityOperator_of_subdifferential_eq_of_mem_gammaZero
    (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) (hsub : ∂ f = ∂ g) :
    Prox[f, hf] = Prox[g, hg] := by
  funext x
  -- Rewrite the chosen proximal point of `f` as a residual subgradient inclusion and transport
  -- that inclusion across the operator equality `∂ f = ∂ g`.
  apply (eq_proximityOperator_iff_sub_mem_subdifferential hg x (Prox[f, hf] x)).2
  have hmem :
      x - Prox[f, hf] x ∈ (∂ f) (Prox[f, hf] x) := by
    exact
      (eq_proximityOperator_iff_sub_mem_subdifferential hf x (Prox[f, hf] x)).1 rfl
  simpa [hsub] using hmem

/-- Helper for Proposition 22.19: the unit Moreau envelope of a `Γ₀(H)` function is finite
everywhere. -/
lemma unit_moreauEnvelope_ne_top_ne_bot_of_mem_gammaZero
    (h : H → Set.Ioi (⊥ : EReal)) (hh : h ∈ Γ₀(H)) (x : H) :
    ({}^[(1 : PosReal)] h) x ≠ ⊤ ∧ ({}^[(1 : PosReal)] h) x ≠ ⊥ := by
  let p := Prox[(1 : PosReal), h, hh] x
  have hp : p ∈ effectiveDomain h := by
    simpa [p] using
      scaledProximityOperator_mem_effectiveDomain_of_mem_gammaZero
        h hh x (1 : PosReal)
  have hp_top : (h p : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hp)
  have hvalue :
      ({}^[(1 : PosReal)] h) x =
        (h p : EReal) + ((((‖x - p‖ ^ 2) / 2 : ℝ) : EReal)) := by
    -- Evaluate the unit Moreau envelope at its proximal point.
    simpa [p] using
      moreauEnvelope_eq_proxValue_add_scaled_sqDist_of_mem_gammaZero
        h hh (1 : PosReal) x
  constructor
  · -- The proximal-value formula writes the envelope as a sum of two finite upper-bounded terms.
    rw [hvalue]
    exact EReal.add_ne_top hp_top (EReal.coe_ne_top _)
  · -- The same formula also rules out `-∞` because both summands lie strictly above `⊥`.
    rw [hvalue]
    exact EReal.add_ne_bot_iff.2 ⟨ne_of_gt (h p).2, EReal.coe_ne_bot _⟩

/-- Helper for Proposition 22.19: if the two proximal operators agree, then the unit Moreau
envelopes of the Fenchel conjugates differ by a real constant. -/
lemma unit_conjugateMoreau_toReal_eq_add_const_of_eq_proximityOperator
    (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) (hprox : Prox[f, hf] = Prox[g, hg]) :
    ∃ c : ℝ, ∀ x : H,
      (({}^[(1 : PosReal)] (gammaZeroConjugate f hf)) x).toReal =
        (({}^[(1 : PosReal)] (gammaZeroConjugate g hg)) x).toReal + c := by
  let Δ : H → ℝ := fun x : H ↦
    (({}^[(1 : PosReal)] (gammaZeroConjugate f hf)) x).toReal -
      (({}^[(1 : PosReal)] (gammaZeroConjugate g hg)) x).toReal
  have hGateaux :
      HasGateauxDerivativeOn Δ
        (fun _ : H ↦ InnerProductSpace.toDual ℝ H (0 : H)) Set.univ := by
    intro x hx
    have hf_grad :
        HasGradientAt
          (fun y : H ↦ (({}^[(1 : PosReal)] (gammaZeroConjugate f hf)) y).toReal)
          (Prox[f, hf] x) x := by
      have hf_grad_raw :=
        moreauEnvelope_toReal_hasGradientAt_of_mem_gammaZero
          (f := gammaZeroConjugate f hf)
          (γ := (1 : PosReal))
          (hf := gammaZeroConjugate_mem_gammaZero hf)
          (x := x)
      have hprox_eq_raw :=
        (congrFun
          (proximityOperator_eq_gradient_conjugateMoreauEnvelope_toReal_of_mem_gammaZero
            (f := f) (hf := hf))
          x).trans hf_grad_raw.gradient
      simpa [hprox_eq_raw] using hf_grad_raw
    have hg_grad :
        HasGradientAt
          (fun y : H ↦ (({}^[(1 : PosReal)] (gammaZeroConjugate g hg)) y).toReal)
          (Prox[g, hg] x) x := by
      have hg_grad_raw :=
        moreauEnvelope_toReal_hasGradientAt_of_mem_gammaZero
          (f := gammaZeroConjugate g hg)
          (γ := (1 : PosReal))
          (hf := gammaZeroConjugate_mem_gammaZero hg)
          (x := x)
      have hprox_eq_raw :=
        (congrFun
          (proximityOperator_eq_gradient_conjugateMoreauEnvelope_toReal_of_mem_gammaZero
            (f := g) (hf := hg))
          x).trans hg_grad_raw.gradient
      simpa [hprox_eq_raw] using hg_grad_raw
    have hg_grad' :
        HasGradientAt
          (fun y : H ↦ (({}^[(1 : PosReal)] (gammaZeroConjugate g hg)) y).toReal)
          (Prox[f, hf] x) x := by
      have hprox_x : Prox[f, hf] x = Prox[g, hg] x := congrFun hprox x
      simpa [hprox_x] using hg_grad
    have hΔ_grad :
        HasGradientAt Δ (0 : H) x := by
      -- Equal gradients force the real-valued difference to have zero gradient.
      simpa [Δ] using
        (hf_grad.hasFDerivAt.sub hg_grad'.hasFDerivAt).hasGradientAt
    simpa using hΔ_grad.hasFDerivAt.hasGateauxDerivativeAt
  have hquad :=
    gradient_eq_continuousLinearMap_eq_quadratic_form Δ (0 : H →L[ℝ] H) hGateaux
  refine ⟨Δ 0, ?_⟩
  intro x
  -- Proposition 2.58 identifies a zero-gradient real function with its constant value at `0`.
  have hx' :
      Δ x = Δ 0 := by
    simpa using congrFun hquad x
  dsimp [Δ] at hx' ⊢
  linarith

/-- Helper for Proposition 22.19: a real-constant equality between the unit conjugate Moreau
envelopes upgrades to an `EReal` equality because those envelopes are finite everywhere. -/
lemma unit_conjugateMoreau_eq_add_const_of_toReal_eq_add_const
    (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) {c : ℝ}
    (hc : ∀ x : H,
      (({}^[(1 : PosReal)] (gammaZeroConjugate f hf)) x).toReal =
        (({}^[(1 : PosReal)] (gammaZeroConjugate g hg)) x).toReal + c) :
    ∀ x : H,
      ({}^[(1 : PosReal)] (gammaZeroConjugate f hf)) x =
        ({}^[(1 : PosReal)] (gammaZeroConjugate g hg)) x + c := by
  intro x
  rcases
      unit_moreauEnvelope_ne_top_ne_bot_of_mem_gammaZero
        (h := gammaZeroConjugate f hf)
        (hh := gammaZeroConjugate_mem_gammaZero hf)
        x with
    ⟨hf_top, hf_bot⟩
  rcases
      unit_moreauEnvelope_ne_top_ne_bot_of_mem_gammaZero
        (h := gammaZeroConjugate g hg)
        (hh := gammaZeroConjugate_mem_gammaZero hg)
        x with
    ⟨hg_top, hg_bot⟩
  -- Convert the finite `EReal` values to reals, use the assumed real identity, and coerce back.
  calc
    ({}^[(1 : PosReal)] (gammaZeroConjugate f hf)) x =
        (((({}^[(1 : PosReal)] (gammaZeroConjugate f hf)) x).toReal : ℝ) : EReal) := by
          exact (EReal.coe_toReal hf_top hf_bot).symm
    _ =
        ((((({}^[(1 : PosReal)] (gammaZeroConjugate g hg)) x).toReal + c : ℝ)) : EReal) := by
          exact congrArg (fun t : ℝ ↦ (t : EReal)) (hc x)
    _ =
        ((((({}^[(1 : PosReal)] (gammaZeroConjugate g hg)) x).toReal : ℝ)) : EReal) +
          ((c : ℝ) : EReal) := by
            rw [EReal.coe_add]
    _ = ({}^[(1 : PosReal)] (gammaZeroConjugate g hg)) x + c := by
          rw [EReal.coe_toReal hg_top hg_bot]

/-- Helper for Proposition 22.19: conjugating the unit Moreau envelope of `f*` recovers
`f + (1/2)‖·‖²`. -/
lemma conjugate_unit_conjugateMoreau_eq_primal_add_halfSquaredNorm
    (hf : f ∈ Γ₀(H)) :
    (fun x : H ↦ ({}^[(1 : PosReal)] (gammaZeroConjugate f hf)) x)∗ =
      f.asEReal + halfSquaredNorm.asEReal := by
  -- First rewrite the conjugate of the unit Moreau envelope, then remove the biconjugate.
  calc
    (fun x : H ↦ ({}^[(1 : PosReal)] (gammaZeroConjugate f hf)) x)∗ =
        (gammaZeroConjugate f hf).asEReal∗ +
          (((1 : ℝ) : EReal) • halfSquaredNorm.asEReal) := by
            simpa using
              (conjugate_moreauEnvelope_eq (f := gammaZeroConjugate f hf) (γ := (1 : PosReal)))
    _ = f.asEReal∗∗ + (((1 : ℝ) : EReal) • halfSquaredNorm.asEReal) := by
          rfl
    _ = f.asEReal + (((1 : ℝ) : EReal) • halfSquaredNorm.asEReal) := by
          rw [biconjugate_eq_of_mem_gammaZero hf]
    _ = f.asEReal + halfSquaredNorm.asEReal := by
          simp

/-- Proposition 22.19: if `f, g ∈ Γ₀(ℋ)` have the same subdifferential, then they differ by a
finite real constant; equivalently, there exists `γ : ℝ` such that
`(f x : EReal) = (g x : EReal) + γ` for every `x`. -/
theorem exists_eq_add_const_of_subdifferential_eq_of_mem_gammaZero
    (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) (hsub : ∂ f = ∂ g) :
    ∃ γ : ℝ, ∀ x : H, (f x : EReal) = (g x : EReal) + γ := by
  -- Route correction: keep the source Moreau-regularization idea, but use the stable proximal
  -- and unit-Moreau API instead of the broken Chapter 17 singleton-subdifferential detour.
  have hprox :
      Prox[f, hf] = Prox[g, hg] :=
    eq_proximityOperator_of_subdifferential_eq_of_mem_gammaZero hf hg hsub
  rcases
      unit_conjugateMoreau_toReal_eq_add_const_of_eq_proximityOperator
        hf hg hprox with
    ⟨c, hc_toReal⟩
  have hc :
      ∀ x : H,
        ({}^[(1 : PosReal)] (gammaZeroConjugate f hf)) x =
          ({}^[(1 : PosReal)] (gammaZeroConjugate g hg)) x + c :=
    unit_conjugateMoreau_eq_add_const_of_toReal_eq_add_const hf hg hc_toReal
  let F : H → EReal := fun x : H ↦
    ({}^[(1 : PosReal)] (gammaZeroConjugate f hf)) x
  let G : H → EReal := fun x : H ↦
    ({}^[(1 : PosReal)] (gammaZeroConjugate g hg)) x
  have hFG : F = fun x : H ↦ G x + ((c : ℝ) : EReal) := by
    funext x
    simpa [F, G] using hc x
  have hFG_conj :
      F∗ = (fun x : H ↦ G x + ((c : ℝ) : EReal))∗ := by
    exact congrArg (fun φ : H → EReal ↦ φ∗) hFG
  have hshift :
      (fun x : H ↦ G x + ((c : ℝ) : EReal))∗ =
        G∗ + fun _ : H ↦ ((-c : ℝ) : EReal) := by
    ext u
    -- Conjugating an additive real constant flips its sign.
    simpa [G, translate_apply, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      congrFun
        (conjugate_translate_add_inner_add_const
          (f := G) (y := (0 : H)) (v := (0 : H)) (β := c))
        u
  have hprimal :
      f.asEReal + halfSquaredNorm.asEReal =
        g.asEReal + halfSquaredNorm.asEReal + fun _ : H ↦ ((-c : ℝ) : EReal) := by
    -- Conjugate the constant-shift identity and rewrite both conjugates as `f + q` and `g + q`.
    calc
      f.asEReal + halfSquaredNorm.asEReal = F∗ := by
            symm
            simpa [F] using conjugate_unit_conjugateMoreau_eq_primal_add_halfSquaredNorm hf
      _ = (fun x : H ↦ G x + ((c : ℝ) : EReal))∗ := hFG_conj
      _ = G∗ + fun _ : H ↦ ((-c : ℝ) : EReal) := hshift
      _ = g.asEReal + halfSquaredNorm.asEReal + fun _ : H ↦ ((-c : ℝ) : EReal) := by
            simpa [G] using
              congrArg
                (fun φ : H → EReal ↦ φ + fun _ : H ↦ ((-c : ℝ) : EReal))
                (conjugate_unit_conjugateMoreau_eq_primal_add_halfSquaredNorm hg)
  refine ⟨-c, ?_⟩
  intro x
  have hpoint := congrFun hprimal x
  have hpoint' :
      (f x : EReal) + halfSquaredNorm.asEReal x =
        ((g x : EReal) + ((-c : ℝ) : EReal)) +
          halfSquaredNorm.asEReal x := by
    simpa [Function.asEReal_apply, add_assoc, add_left_comm, add_comm]
      using hpoint
  rw [Function.asEReal_apply, halfSquaredNorm_apply] at hpoint'
  have hcancel :
      (f x : EReal) = (g x : EReal) + ((-c : ℝ) : EReal) := by
    apply le_antisymm
    · exact
        (EReal.addLECancellable_coe ((‖x‖ ^ 2) / 2)).add_le_add_iff_right.mp hpoint'.le
    · exact
        (EReal.addLECancellable_coe ((‖x‖ ^ 2) / 2)).add_le_add_iff_right.mp hpoint'.ge
  -- Cancel the common quadratic term to recover the desired constant-difference identity.
  simpa [sub_eq_add_neg] using hcancel

end SubdifferentialRigidity

end ERealFunction
