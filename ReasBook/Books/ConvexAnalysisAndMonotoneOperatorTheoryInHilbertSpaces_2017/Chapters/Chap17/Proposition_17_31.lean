import BauschkeLean.Chap17.Proposition_17_6
import BauschkeLean.Chap17.Theorem_17_18

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace
open scoped InnerProductSpace

universe u

namespace ERealFunction

section DifferentiabilityOfConvexFunctions

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))

/- Source/core/bridge triage:
- `source-facing`: Proposition 17.31 identifies the source directional-derivative data of `f`
  itself at `x` with the singleton shape of the source-facing subdifferential `∂ f x`.
- `core/canonical`: the owner abstractions are `HasDirectionalDerivativeAt`, `∂`,
  `directionalDerivative`, and `ContinuousAtOnEffectiveDomain`.
- `bridge/view`: Proposition 17.6 sends a source Gâteaux gradient to a subgradient, Proposition
  17.14 compares subgradients with directional derivatives, and Theorem 17.18 rewrites
  `directionalDerivative f x` as the support function of `∂ f x`.
- semantic recall: `lean_leansearch` timed out here, so the repair follows the local Chapter 17
  owners and the defect report. -/

/-- Helper for Proposition 17 31: once both endpoint values are finite, the Chapter 17
extended-real quotient is the coercion of the real quotient for `toReal`. -/
private theorem quotient_eq_coe_toReal_of_mem_effectiveDomain
    {x d : H} {α : ℝ} (hx : x ∈ effectiveDomain f) (hα : 0 < α)
    (hαdom : x + α • d ∈ effectiveDomain f) :
    ((f (x + α • d) : EReal) - (f x : EReal)) / α =
      ((((f (x + α • d) : EReal).toReal - (f x : EReal).toReal) / α : ℝ) : EReal) := by
  -- Rewrite both finite `EReal` values through `toReal`, so the quotient becomes a real one.
  have _ : α ≠ 0 := hα.ne'
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hx_bot : (f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hαdom_top : (f (x + α • d) : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hαdom)
  have hαdom_bot : (f (x + α • d) : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f (x + α • d) : EReal) from (f (x + α • d)).2)
  rw [← EReal.coe_toReal hαdom_top hαdom_bot, ← EReal.coe_toReal hx_top hx_bot,
    ← EReal.coe_sub, ← EReal.coe_div]
  simp

/-- Helper for Proposition 17 31: a linear family of source directional derivatives upgrades to
the Chapter 2 Gâteaux derivative of the finite real representative. -/
private theorem hasGateauxDerivativeAt_toReal_of_forall_hasDirectionalDerivativeAt
    {x : H} {A : H →L[ℝ] ℝ}
    (hA : ∀ y : H, HasDirectionalDerivativeAt f x y (A y : EReal)) :
    HasGateauxDerivativeAt (fun z ↦ (f z : EReal).toReal) A x := by
  rw [hasGateauxDerivativeAt_iff_tendsto_directionalDifferenceQuotient]
  intro y
  rcases hA y with ⟨hx, hA'⟩
  let q : ℝ → EReal := fun α ↦ ((f (x + α • y) : EReal) - (f x : EReal)) / α
  let r : ℝ → ℝ := fun α ↦ ((f (x + α • y) : EReal).toReal - (f x : EReal).toReal) / α
  have hfinite :
      ∀ᶠ α in nhdsWithin (0 : ℝ) (Set.Ioi 0), q α ∈ Set.Ioo (⊥ : EReal) ⊤ := by
    -- The source derivative has finite value, so nearby quotients must stay finite as well.
    refine hA' (isOpen_Ioo.mem_nhds ?_)
    simp
  have hdom :
      ∀ᶠ α in nhdsWithin (0 : ℝ) (Set.Ioi 0), x + α • y ∈ effectiveDomain f := by
    -- If a nearby point left the effective domain, the corresponding quotient would jump to `⊤`.
    filter_upwards [hfinite, self_mem_nhdsWithin] with α hαfinite hα
    rw [mem_effectiveDomain_iff]
    by_contra hαdom
    have hαtop : (f (x + α • y) : EReal) = ⊤ := by
      exact le_antisymm le_top (not_lt.mp hαdom)
    have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hqtop : q α = ⊤ := by
      dsimp [q]
      rw [hαtop, EReal.top_sub hx_top, EReal.top_div_of_pos_ne_top]
      · exact_mod_cast hα
      · exact EReal.coe_ne_top α
    exact hαfinite.2.ne hqtop
  have hEq :
      (fun α ↦ (r α : EReal)) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)] q := by
    -- Along the effective-domain branch, the source quotient is exactly the cast real quotient.
    filter_upwards [hdom, self_mem_nhdsWithin] with α hαdom hα
    dsimp [q, r]
    simpa using
      (quotient_eq_coe_toReal_of_mem_effectiveDomain f hx hα hαdom).symm
  have hEq' :
      q =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)] (fun α ↦ (r α : EReal)) :=
    hEq.symm
  have hcoe :
      Filter.Tendsto (fun α ↦ (r α : EReal)) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (A y : EReal)) :=
    Filter.Tendsto.congr' hEq' hA'
  have hreal : Filter.Tendsto r (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (A y)) :=
    EReal.tendsto_coe.mp hcoe
  simpa [r, one_div, smul_eq_mul, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hreal

-- Proof sketch: Proposition 17.6 shows that a Gâteaux gradient `gradf` at `x` is a subgradient.
-- For any other `u ∈ ∂ f(x)`, Proposition 17.14 (1) compares both `u` and `gradf` with the
-- directional derivative, and the Gâteaux derivative formula forces
-- `⟪u - gradf, u - gradf⟫ ≤ 0`, hence `u = gradf`.
/-- Proposition 17.31 (1): at an effective-domain point of a convex `]-∞,+∞]`-valued function,
if the finite real representative of `f` has Gâteaux derivative `toDualMap ℝ H gradf` at `x`,
then the subdifferential of `f` is the singleton `{gradf}`. -/
theorem subdifferential_eq_singleton_of_hasGateauxDerivativeAt
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hx : x ∈ effectiveDomain f) (gradf : H)
    (hgrad :
      HasGateauxDerivativeAt (fun z ↦ (f z : EReal).toReal) (toDualMap ℝ H gradf) x) :
    (∂ f) x = ({gradf} : Set H) := by
  -- Route correction: the source proof needs the Chapter 17 directional-derivative identity
  -- `(17.9)`, but the current header only gives a `toReal` Gâteaux derivative. This leaves a
  -- genuine statement gap: for example, the singleton indicator at `x` has constant `toReal`
  -- representative near `x`, yet its subdifferential need not be a singleton.
  sorry

variable [CompleteSpace H]

/-- Helper for Proposition 17 31: a singleton subdifferential at a continuity point forces every
directional derivative to agree with the corresponding inner product against that singleton
element. -/
private theorem forall_hasDirectionalDerivativeAt_toDualMap_of_subdifferential_eq_singleton
    (hconv : ConvexOn f (effectiveDomain f))
    {x u : H} (hxcont : x ∈ cont f) (hsub : (∂ f) x = ({u} : Set H)) :
    ∀ y : H, HasDirectionalDerivativeAt f x y ((((toDualMap ℝ H u) y : ℝ) : EReal)) := by
  intro y
  have hxeff : x ∈ effectiveDomain f := mem_effectiveDomain_of_mem_cont hxcont
  have hdir :
      HasDirectionalDerivativeAt f x y (f′(x; y)) :=
    hasDirectionalDerivativeAt_directionalDerivative f hconv hxeff y
  have hy_value : f′(x; y) = ((((toDualMap ℝ H u) y : ℝ) : EReal)) := by
    -- Theorem 17.18 turns the directional derivative into the support function of `{u}`.
    calc
      f′(x; y) = σ[(∂ f) x] y := by
        exact congrFun
          (directionalDerivative_eq_supportFunction_subdifferential_of_mem_cont
            f hconv hxcont) y
      _ = σ[{u}] y := by rw [hsub]
      _ = sSup ((fun v : H ↦ (⟪v, y⟫_ℝ : EReal)) '' ({u} : Set H)) := by
        rw [supportFunction_eq_sSup_image]
      _ = (⟪u, y⟫_ℝ : EReal) := by simp
      _ = ((((toDualMap ℝ H u) y : ℝ) : EReal)) := by
        simp [InnerProductSpace.toDualMap_apply_apply]
  -- Replace the canonical source directional derivative by the singleton formula.
  simpa [hy_value] using hdir

-- Proof sketch: Theorem 17.18 identifies the directional derivative at `x` with the support
-- function of the singleton subdifferential `{u}`, so `f'(x; y) = ⟪y, u⟫` for every direction
-- `y`. The characterization of Gâteaux differentiability by directional derivatives then gives the
-- derivative `toDualMap ℝ H u` at `x`.
/-- Proposition 17.31 (2): at a source continuity point of a convex `]-∞,+∞]`-valued function,
if the subdifferential at `x` is the singleton `{u}`, then the finite real representative of `f`
has Gâteaux derivative `toDualMap ℝ H u` at `x`. -/
theorem hasGateauxDerivativeAt_of_subdifferential_eq_singleton_of_continuousAtOnEffectiveDomain
    (hconv : ConvexOn f (effectiveDomain f))
    {x u : H} (hxcont : x ∈ cont f) (hsub : (∂ f) x = ({u} : Set H)) :
    HasGateauxDerivativeAt (fun z ↦ (f z : EReal).toReal) (toDualMap ℝ H u) x := by
  -- The singleton subdifferential gives the full directional-derivative family, which the local
  -- bridge upgrades back to the real Gâteaux derivative of the finite representative.
  exact
    hasGateauxDerivativeAt_toReal_of_forall_hasDirectionalDerivativeAt (f := f)
      (forall_hasDirectionalDerivativeAt_toDualMap_of_subdifferential_eq_singleton
        (f := f) hconv hxcont hsub)

end DifferentiabilityOfConvexFunctions

end ERealFunction
