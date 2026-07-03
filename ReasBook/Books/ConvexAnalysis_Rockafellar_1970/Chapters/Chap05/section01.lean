import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_5_1_1 (from Chap01) -/
universe u

section

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 5.1.1 says that `h(x) = e^{f(x)}` is a proper convex function whenever
  `f` is.
- `core/canonical`: the owner abstractions are `Function.IsProper.comp_extendBotTop` for
  properness and `Function.IsConvex.comp_toWithTopBot_extendBotTop_of_monotone` for
  convexity,
  both on the canonical `WithTopBot ℝ` codomain.
- `bridge/view`: the outer exponential is the finite branch `Real.exp`, seen on the extended
  codomain through `((Real.exp).toWithTopBot).extendBotTop`.

Domain-style sampling used here:
- `Function.IsProper` and `Function.IsProper.comp_extendBotTop` from `Definition_4_6`;
- `Function.IsConvex` from `Theorem_4_2`, reused through `Theorem_5_1`;
- `Function.IsConvex.comp_toWithTopBot_extendBotTop_of_monotone` from `Theorem_5_1`;
- the canonical codomain lift `Function.toWithTopBot` and boundary-preserving extension
  `Function.extendBotTop`.

Primitive data vs derived API:
- primitive data: the finite outer branch `Real.exp`;
- derived API: properness and convexity of the canonical composite.

Layer target: `source-facing`, expressed directly through the chapter owners rather than through a
parallel exponential-specific wrapper API.
-/

private theorem exp_convexOn_univ :
    ConvexOn ℝ (Set.univ : Set ℝ) Real.exp := by
  simpa using (convexOn_exp : ConvexOn ℝ Set.univ Real.exp)

variable {E : Type u}

namespace Function

section Convex

/- Properness branch for Text 5.1.1 on the canonical owner surface. -/
theorem IsProper.comp_exp {f : E → WithTopBot ℝ} (hf : f.IsProper) :
    ((((Real.exp).toWithTopBot).extendBotTop) ∘ f).IsProper := by
  simpa using hf.comp_extendBotTop Real.exp

variable [AddCommMonoid E] [MulActionWithZero ℝ E]

/-- Convexity branch for Text 5.1.1 on the canonical owner surface. -/
theorem IsConvex.comp_exp {f : E → WithTopBot ℝ} (hf : f.IsConvex ℝ) :
    ((((Real.exp).toWithTopBot).extendBotTop) ∘ f).IsConvex ℝ := by
  simpa using hf.comp_toWithTopBot_extendBotTop_of_monotone
    exp_convexOn_univ Real.exp_monotone

/-- Text 5.1.1: if `f : E → WithTopBot ℝ` is proper and convex, then the canonical exponential
composite `((Real.exp).toWithTopBot).extendBotTop ∘ f` is again a proper convex function. This is
the project-level `WithTopBot ℝ` owner form of the textbook statement `h(x) = e^{f(x)}`. -/
theorem exp_comp_isProper_and_isConvex
    {f : E → WithTopBot ℝ} (hf_proper : f.IsProper) (hf_convex : f.IsConvex ℝ) :
    ((((Real.exp).toWithTopBot).extendBotTop) ∘ f).IsProper ∧
      ((((Real.exp).toWithTopBot).extendBotTop) ∘ f).IsConvex ℝ := by
  exact ⟨hf_proper.comp_exp, hf_convex.comp_exp⟩

end Convex

end Function

end

/-! ### Theorem_5_1 (from Chap01) -/
universe u v

section

variable {𝕜 : Type*}
variable {E : Type u}
variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid E]

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 5.1 composes a convex function `f : E → (-∞, +∞]` with a convex
  nondecreasing function `φ : 𝕜 → WithTopBot β`, using the convention `φ(+∞) = +∞`. This is the
  coordinate-free refinement of the source's concrete `ℝ^n` statement.
- `core/canonical`: the chapter owner abstraction is `Function.IsConvex 𝕜` on the canonical
  `WithTopBot` lifts of `f` and `φ`, so the public API is stated directly on that primitive
  extended-order codomain layer rather than through the specialized `EReal = WithTopBot ℝ`.
- `bridge/view`: the convention `φ(+∞) = +∞` is expressed by the canonical owner
  `Function.extendBotTop`, which extends `φ : 𝕜 → WithTopBot β` to
  `WithTopBot 𝕜 → WithTopBot β`
  while preserving the two boundary points.

Domain-style sampling used here:
- `Function.IsConvex` from `Theorem_4_2`;
- `Function.extendBotTop` from `EOrder.Basic`.
-/

namespace Function

omit [IsStrictOrderedRing 𝕜] in
private theorem exists_coe_upper_of_ne_top (x : WithBotTop 𝕜) (hx : x ≠ ⊤) :
    ∃ μ : 𝕜, x ≤ (μ : WithBotTop 𝕜) := by
  cases x using WithBotTop.rec with
  | bot =>
      exact ⟨0, by simp⟩
  | top =>
      exact (hx rfl).elim
  | coe μ =>
      exact ⟨μ, by simp⟩

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
private theorem ne_top_of_extendBotTop_le_coe {β : Type v} [Preorder β]
    {φ : 𝕜 → WithBotTop β}
    {x : WithBotTop 𝕜} {α : β} (hx : φ.extendBotTop x ≤ (α : WithBotTop β)) :
    x ≠ ⊤ := by
  intro htop
  have hx' : (⊤ : WithBotTop β) ≤ (α : WithBotTop β) := by simpa [htop] using hx
  exact (not_lt_of_ge hx') (WithBotTop.coe_lt_top α)

-- Proof sketch: interpret convexity of `f` and `φ` via convexity of their scalar epigraphs.
-- The inner function `f` already lives on the chapter-facing owner layer `WithTopBot 𝕜`; the
-- outer function is first extended canonically from `WithTopBot 𝕜` to `WithTopBot β` by
-- `Function.extendBotTop`,
-- which preserves finite values and sends the two boundary points to themselves. Convexity of `f`
-- controls the inner argument at convex combinations, monotonicity of `φ` transports that
-- inequality through the outer function, and convexity of `φ` gives the final height bound for
-- the composed epigraph.
/-- If a convex `WithBotTop 𝕜`-valued function takes the value `⊥` at the left endpoint of a
convex combination with positive left weight, then the value at the combination is still `⊥`,
provided the right endpoint has some finite upper bound. -/
private theorem IsConvex.eq_bot_smul_add_of_left_eq_bot [SMul 𝕜 E] {f : E → WithBotTop 𝕜}
    (hf : f.IsConvex 𝕜) {x y : E} {a b : 𝕜} (hfx : f x = ⊥) (ha : 0 < a) (hb : 0 ≤ b)
    (hab : a + b = 1) (hy : ∃ μ : 𝕜, f y ≤ (μ : WithBotTop 𝕜)) :
    f (a • x + b • y) = ⊥ := by
  refine (WithBotTop.eq_bot_iff_forall_lt _).2 ?_
  intro m
  rcases hy with ⟨μ, hyμ⟩
  let t : 𝕜 := (m - b * μ - a) / a
  have hx_epi : (x, t) ∈ {p : E × 𝕜 | f p.1 ≤ (p.2 : WithBotTop 𝕜)} := by
    simp [t, hfx]
  have hy_epi : (y, μ) ∈ {p : E × 𝕜 | f p.1 ≤ (p.2 : WithBotTop 𝕜)} := by
    exact hyμ
  have hxy_epi :=
    hf.convex_epigraph hx_epi hy_epi (le_of_lt ha) hb <| by
      simpa [smul_eq_mul, mul_add, add_comm, add_left_comm, add_assoc] using hab
  have hz_le : f (a • x + b • y) ≤ ((a * t + b * μ : 𝕜) : WithBotTop 𝕜) := by
    simpa [smul_eq_mul, mul_add, add_comm, add_left_comm, add_assoc] using hxy_epi
  have hat : a * t + b * μ = m - a := by
    have ha0 : a ≠ 0 := ne_of_gt ha
    dsimp [t]
    field_simp [ha0]
    ring
  have hma : m - a < m := by
    nlinarith [ha]
  have ht_lt : ((a * t + b * μ : 𝕜) : WithBotTop 𝕜) < (m : WithBotTop 𝕜) := by
    simpa [hat] using (WithBotTop.coe_lt_coe_iff.2 hma)
  exact lt_of_le_of_lt hz_le ht_lt

/-- Right-endpoint version of `IsConvex.eq_bot_smul_add_of_left_eq_bot`. -/
private theorem IsConvex.eq_bot_smul_add_of_right_eq_bot [SMul 𝕜 E] {f : E → WithBotTop 𝕜}
    (hf : f.IsConvex 𝕜) {x y : E} {a b : 𝕜} (hfy : f y = ⊥) (ha : 0 ≤ a) (hb : 0 < b)
    (hab : a + b = 1) (hx : ∃ μ : 𝕜, f x ≤ (μ : WithBotTop 𝕜)) :
    f (a • x + b • y) = ⊥ := by
  have hswap : f (b • y + a • x) = ⊥ :=
    hf.eq_bot_smul_add_of_left_eq_bot hfy hb ha (by simpa [add_comm] using hab) hx
  simpa [add_comm] using hswap

/-- Theorem 5.1 in owner form: if `f : E → (-∞, +∞]` and `φ : 𝕜 → WithTopBot β` are convex, and
`φ` is nondecreasing, then the canonical extension of `φ` composed with `f` is convex on `E`. -/
theorem IsConvex.comp_extendBotTop_of_monotone {β : Type v} [SMul 𝕜 E]
    [AddCommMonoid β] [SMul 𝕜 β] [Preorder β]
    {f : E → WithTopBot 𝕜} (hf : f.IsConvex 𝕜) {φ : 𝕜 → WithTopBot β}
    (hφ_conv : φ.IsConvex 𝕜) (hφ_mono : Monotone φ) :
    (φ.extendBotTop ∘ f).IsConvex 𝕜 := by
  let ψ : WithTopBot 𝕜 → WithTopBot β := φ.extendBotTop
  have hψ_mono : Monotone ψ := Function.Monotone.extendBotTop (φ := φ) hφ_mono
  let ef : Set (E × 𝕜) := {p : E × 𝕜 | f p.1 ≤ (p.2 : WithBotTop 𝕜)}
  let eφ : Set (𝕜 × β) := {p : 𝕜 × β | φ p.1 ≤ (p.2 : WithBotTop β)}
  have hf_epi : Convex 𝕜 ef := by
    simpa [ef] using hf.convex_epigraph
  have hφ_epi : Convex 𝕜 eφ := by
    simpa [eφ] using hφ_conv.convex_epigraph
  refine (Function.isConvex_iff_convex_epigraph (ψ ∘ f)).2 ?_
  intro p hp q hq a b ha hb hab
  rcases p with ⟨x, η⟩
  rcases q with ⟨y, θ⟩
  have hp_val : ψ (f x) ≤ (η : WithBotTop β) := by
    simpa [ef, ψ] using hp
  have hq_val : ψ (f y) ≤ (θ : WithBotTop β) := by
    simpa [ef, ψ] using hq
  change
    ψ (f (a • x + b • y)) ≤ ((a • η + b • θ : β) : WithBotTop β)
  cases hfx : f x using WithBotTop.rec with
  | bot =>
      by_cases ha0 : a = 0
      · have hb1 : b = 1 := by
          rw [ha0, zero_add] at hab
          exact hab
        simpa [ψ, ha0, hb1] using hq
      · have ha_pos : 0 < a := by
          exact lt_of_le_of_ne ha (by simpa [eq_comm] using ha0)
        have hy : ∃ μ : 𝕜, f y ≤ (μ : WithBotTop 𝕜) := by
          exact exists_coe_upper_of_ne_top (f y) <|
            ne_top_of_extendBotTop_le_coe hq_val
        have hfz : f (a • x + b • y) = ⊥ :=
          hf.eq_bot_smul_add_of_left_eq_bot hfx ha_pos hb hab hy
        simp [ψ, hfz]
  | top =>
      exfalso
      have hp_top := hp_val
      have hp_top' : (⊤ : WithBotTop β) ≤ (η : WithBotTop β) := by simpa [ψ, hfx] using hp_top
      exact (not_lt_of_ge hp_top') (WithBotTop.coe_lt_top η)
  | coe rx =>
      cases hfy : f y using WithBotTop.rec with
      | bot =>
          by_cases hb0 : b = 0
          · have ha1 : a = 1 := by
              rw [hb0, add_zero] at hab
              exact hab
            simpa [ψ, hb0, ha1] using hp
          · have hb_pos : 0 < b := by
              exact lt_of_le_of_ne hb (by simpa [eq_comm] using hb0)
            have hx : ∃ μ : 𝕜, f x ≤ (μ : WithBotTop 𝕜) := by
              exact exists_coe_upper_of_ne_top (f x) <|
                ne_top_of_extendBotTop_le_coe hp_val
            have hfz : f (a • x + b • y) = ⊥ :=
              hf.eq_bot_smul_add_of_right_eq_bot hfy ha hb_pos hab hx
            simp [ψ, hfz]
      | top =>
          exfalso
          have hq_top := hq_val
          have hq_top' : (⊤ : WithBotTop β) ≤ (θ : WithBotTop β) := by
            simpa [ψ, hfy] using hq_top
          exact (not_lt_of_ge hq_top') (WithBotTop.coe_lt_top θ)
      | coe ry =>
          have hx_epi : (x, rx) ∈ ef := by
            simp [ef, hfx]
          have hy_epi : (y, ry) ∈ ef := by
            simp [ef, hfy]
          have hxy_epi :=
            hf_epi hx_epi hy_epi ha hb <| by
              simpa [smul_eq_mul, mul_add, add_comm, add_left_comm, add_assoc] using hab
          have hf_le : f (a • x + b • y) ≤ ((a * rx + b * ry : 𝕜) : WithBotTop 𝕜) := by
            simpa [ef, smul_eq_mul, mul_add, add_comm, add_left_comm, add_assoc] using hxy_epi
          cases hfz : f (a • x + b • y) using WithBotTop.rec with
          | bot =>
              simp [ψ]
          | top =>
              exfalso
              have hf_top : (⊤ : WithBotTop 𝕜) ≤ ((a * rx + b * ry : 𝕜) : WithBotTop 𝕜) := by
                simpa [hfz] using hf_le
              exact (not_lt_of_ge hf_top) (WithBotTop.coe_lt_top (a * rx + b * ry))
          | coe rz =>
              have hrz_le :
                  (rz : WithBotTop 𝕜) ≤ ((a * rx + b * ry : 𝕜) : WithBotTop 𝕜) := by
                simpa [hfz] using hf_le
              have hxφ_epi : (rx, η) ∈ eφ := by
                simpa [eφ, ψ, hfx] using hp_val
              have hyφ_epi : (ry, θ) ∈ eφ := by
                simpa [eφ, ψ, hfy] using hq_val
              have hφxy_epi :=
                hφ_epi hxφ_epi hyφ_epi ha hb <| by
                  simpa [smul_eq_mul, mul_add, add_comm, add_left_comm, add_assoc] using hab
              have hφ_le' : φ (a • rx + b • ry) ≤ ((a • η + b • θ : β) : WithBotTop β) := by
                simpa [eφ] using hφxy_epi
              have hφ_le : φ (a * rx + b * ry) ≤ ((a • η + b • θ : β) : WithBotTop β) := by
                simpa [smul_eq_mul] using hφ_le'
              have hmono : ψ (rz : WithBotTop 𝕜) ≤ ψ ((a * rx + b * ry : 𝕜) : WithBotTop 𝕜) :=
                hψ_mono hrz_le
              have hφ_leψ :
                  ψ ((a * rx + b * ry : 𝕜) : WithBotTop 𝕜) ≤
                    ((a • η + b • θ : β) : WithBotTop β) := by
                simpa [ψ] using hφ_le
              simpa [ψ, hfz] using hmono.trans hφ_leψ

/-- Finite-branch companion of `IsConvex.comp_extendBotTop_of_monotone`: if
`φ : 𝕜 → β` is convex on `Set.univ` and monotone, then
`((φ.toWithTopBot).extendBotTop) ∘ f` is convex. -/
theorem IsConvex.comp_toWithTopBot_extendBotTop_of_monotone {β : Type v}
    [SMul 𝕜 E] [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β]
    [Module 𝕜 β] [PosSMulMono 𝕜 β]
    {f : E → WithTopBot 𝕜} (hf : f.IsConvex 𝕜) {φ : 𝕜 → β}
    (hφ_conv : ConvexOn 𝕜 (Set.univ : Set 𝕜) φ) (hφ_mono : Monotone φ) :
    (((φ.toWithTopBot).extendBotTop) ∘ f).IsConvex 𝕜 := by
  refine hf.comp_extendBotTop_of_monotone
    (Function.isConvex_coe_of_convexOn_univ (f := φ) hφ_conv) ?_
  intro x y hxy
  exact (WithBotTop.coe_le_coe_iff).2 (hφ_mono hxy)

end Function

end

/-! ### Text_5_1_2 (from Chap01) -/
universe u

section

variable {E : Type u}
variable [AddCommMonoid E] [SMul ℝ E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 5.1.2 says that the pointwise power `h(x) = f(x)^p` is convex when `f` is
  convex, nonnegative, and `p > 1`.
- `core/canonical`: the owner abstraction for finite real-valued convex functions is mathlib's
  `ConvexOn ℝ s f`; at this owner layer the primitive exponent bound is `1 ≤ p`, and the proof
  uses the Jensen field of `ConvexOn` together with the canonical outer-map owners
  `convexOn_rpow` and `Real.monotoneOn_rpow_Ici_of_exponent_nonneg`.
- `bridge/view`: the companion theorem `ConvexOn.rpow_of_one_lt` recovers the source wording
  `p > 1` from the canonical owner theorem `ConvexOn.rpow`.

Domain-style sampling used here:
- `ConvexOn` from `Mathlib/Analysis/Convex/Function.lean`;
- `convexOn_rpow` from `Mathlib/Analysis/Convex/SpecificFunctions/Basic.lean`;
- `Real.monotoneOn_rpow_Ici_of_exponent_nonneg` from
  `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean`.

Primitive data vs derived API:
- primitive inputs: a convex real-valued branch `f : E → ℝ` on `s`, pointwise nonnegativity on
  `s` as `∀ x ∈ s, 0 ≤ f x`, and an exponent `p`;
- derived output: convexity of the pointwise power `fun x ↦ f x ^ p`.

Layer target: `core/canonical`, with the owner theorem stated directly on `ConvexOn` at the
primitive exponent threshold `1 ≤ p`; the strict source inequality `p > 1` is kept as a thin
companion bridge.
-/

namespace ConvexOn

-- Proof sketch: use the outer map `x ↦ x ^ p` on `Ici 0`. For `p ≥ 1`, mathlib gives convexity
-- of this outer map on `Ici 0`, and it is monotone there for every nonnegative exponent.
-- Convexity of `f` gives
-- `f (a • x + b • y) ≤ a * f x + b * f y`; monotonicity of `x ↦ x ^ p` on `Ici 0` transports
-- this inequality, and convexity of `x ↦ x ^ p` yields the final Jensen inequality.
/-- Canonical owner form behind Text 5.1.2: on `ConvexOn`, the same argument extends to the
endpoint `p = 1`, so nonnegative convex functions remain convex after taking the pointwise
`p`-power for every exponent `p ≥ 1`. -/
theorem rpow {s : Set E} {f : E → ℝ} {p : ℝ}
    (hf : ConvexOn ℝ s f) (hfs : Set.MapsTo f s (Set.Ici 0)) (hp : 1 ≤ p) :
    ConvexOn ℝ s (fun x ↦ f x ^ p) := by
  have hp_nonneg : 0 ≤ p := le_trans (by norm_num : (0 : ℝ) ≤ 1) hp
  have hpow : ConvexOn ℝ (Set.Ici 0) (fun t : ℝ ↦ t ^ p) := convexOn_rpow hp
  have hmono : MonotoneOn (fun t : ℝ ↦ t ^ p) (Set.Ici 0) :=
    Real.monotoneOn_rpow_Ici_of_exponent_nonneg hp_nonneg
  refine ⟨hf.1, ?_⟩
  intro x hx y hy a b ha hb hab
  have hx_nonneg : 0 ≤ f x := hfs hx
  have hy_nonneg : 0 ≤ f y := hfs hy
  have hxy_nonneg : 0 ≤ f (a • x + b • y) := hfs (hf.1 hx hy ha hb hab)
  have hcomb_nonneg : 0 ≤ a * f x + b * f y :=
    add_nonneg (mul_nonneg ha hx_nonneg) (mul_nonneg hb hy_nonneg)
  have hxy_le : f (a • x + b • y) ≤ a * f x + b * f y := by
    simpa [smul_eq_mul] using hf.2 hx hy ha hb hab
  calc
    f (a • x + b • y) ^ p ≤ (a * f x + b * f y) ^ p :=
      hmono hxy_nonneg hcomb_nonneg hxy_le
    _ ≤ a * (f x ^ p) + b * (f y ^ p) := by
      simpa [smul_eq_mul] using hpow.2 hx_nonneg hy_nonneg ha hb hab

/-- Text 5.1.2: if a real-valued function is convex and nonnegative on a convex set, then its
pointwise `p`-power is convex for every exponent `p > 1`. -/
theorem rpow_of_one_lt {s : Set E} {f : E → ℝ} {p : ℝ}
    (hf : ConvexOn ℝ s f) (hf₀ : ∀ x ∈ s, 0 ≤ f x) (hp : 1 < p) :
    ConvexOn ℝ s (fun x ↦ f x ^ p) :=
  hf.rpow (fun x hx ↦ hf₀ x hx) hp.le

end ConvexOn

end

/-! ### Text_5_1_3 (from Chap01) -/
universe u

section

variable {E : Type u} [SeminormedAddCommGroup E] [SMul ℝ E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 5.1.3 says that norm powers `x ↦ ‖x‖ ^ p` are convex for `p ≥ 1`.
- `core/canonical`: the natural owner layer is the real-valued convex-function predicate
  `ConvexOn ℝ s f`; the primitive theorem here is `ConvexOn.norm_rpow`, while
  `convexOn_norm` is the bridge that supplies the norm branch from set convexity.
- `bridge/view`: this file keeps the abstract real normed-space form; concrete coordinate
  specializations are downstream views. The case `p = 1` is norm convexity, and `p > 1` is the
  strict-exponent corollary of `ConvexOn.rpow` from Text 5.1.2.

Domain-style sampling used here:
- `convexOn_norm`;
- `ConvexOn.rpow`;
- `ConvexOn.norm_rpow` (introduced here as the owner-level API).
-/

namespace ConvexOn

-- Proof sketch: apply Text 5.1.2 (`ConvexOn.rpow`) to the norm branch; the nonnegativity side
-- condition is immediate from `norm_nonneg`.
/-- Canonical owner form behind Text 5.1.3: if the norm map is convex on `s`, then every real
power `x ↦ ‖x‖ ^ p` with `p ≥ 1` is convex on `s`. -/
theorem norm_rpow {s : Set E} (hnorm : ConvexOn ℝ s (fun x : E ↦ ‖x‖)) {p : ℝ} (hp : 1 ≤ p) :
    ConvexOn ℝ s (fun x ↦ ‖x‖ ^ p) := by
  refine hnorm.rpow ?_ hp
  intro x _
  exact norm_nonneg x

end ConvexOn

end

section

variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

-- Proof sketch: feed `convexOn_norm hs` into the canonical owner theorem
-- `ConvexOn.norm_rpow`.
/-- Text 5.1.3: on every convex set, `x ↦ ‖x‖ ^ p` is convex for every exponent `p ≥ 1`. -/
theorem convexOn_norm_rpow {s : Set E} (hs : Convex ℝ s) {p : ℝ} (hp : 1 ≤ p) :
    ConvexOn ℝ s (fun x ↦ ‖x‖ ^ p) :=
  (convexOn_norm hs).norm_rpow hp

-- Proof sketch: specialize `convexOn_norm_rpow` to `Set.univ`.
/-- Text 5.1.3: for every exponent `p ≥ 1`, the map `x ↦ ‖x‖ ^ p` is convex on the whole space. -/
theorem convexOn_univ_norm_rpow {p : ℝ} (hp : 1 ≤ p) :
    ConvexOn ℝ Set.univ (fun x : E ↦ ‖x‖ ^ p) := by
  simpa using (convexOn_norm_rpow (s := Set.univ) convex_univ hp :
    ConvexOn ℝ Set.univ (fun x : E ↦ ‖x‖ ^ p))

end

/-! ### Text_5_1_4 (from Chap01) -/
universe u v

section

variable {𝕜 : Type v} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: the example states that the reciprocal of a concave scalar-valued function is
  convex on the region where the function is positive.
- `core/canonical`: the natural owner layer is mathlib's set-based pair `ConcaveOn` / `ConvexOn`;
  no project-local wrapper is needed.
- `bridge/view`: the reciprocal map is the scalar convex outer function on `(0, +∞)`, and the
  source domain `C = {x ∈ s | g(x) > 0}` is recorded literally as the positive locus of `g`
  inside the ambient set `s`.

Domain-style sampling used here:
- `ConcaveOn` and `ConvexOn` from mathlib's convex-function API;
- `convexOn_zpow (-1)` for convexity of the reciprocal on `(0, +∞)`;
- `one_div_strictAntiOn` for monotonicity of the reciprocal on positive scalars.
-/

-- Proof sketch: on `(0, +∞)` the reciprocal map is convex and antitone. On
-- `{x ∈ s | 0 < g x}`, concavity of `g` gives
-- `a • g x + b • g y ≤ g (a • x + b • y)`, so antitonicity gives the first reciprocal inequality,
-- and convexity of the reciprocal gives the second inequality.
namespace ConcaveOn

/-- Text 5.1.4 (set-parametric form): if `g` is concave on `s`, then `x ↦ 1 / g x` is convex on
the positive locus `s ∩ {x | 0 < g x}`. -/
theorem one_div {s : Set E} {g : E → 𝕜} (hg : ConcaveOn 𝕜 s g) :
    ConvexOn 𝕜 (s ∩ {x | 0 < g x}) (fun x ↦ 1 / g x) := by
  let t : Set E := s ∩ {x | 0 < g x}
  have hconv_one_div : ConvexOn 𝕜 (Set.Ioi (0 : 𝕜)) (fun t : 𝕜 ↦ 1 / t) := by
    simpa [one_div, zpow_neg_one] using
      (convexOn_zpow (-1 : ℤ) :
        ConvexOn 𝕜 (Set.Ioi (0 : 𝕜)) (fun t : 𝕜 ↦ t ^ (-1 : ℤ)))
  have hanti_one_div : AntitoneOn (fun t : 𝕜 ↦ 1 / t) (Set.Ioi (0 : 𝕜)) :=
    one_div_strictAntiOn.antitoneOn
  have ht_subset : t ⊆ s := by
    intro x hx
    exact hx.1
  have ht_convex : Convex 𝕜 t := by
    intro x hx y hy a b ha hb hab
    refine ⟨hg.1 hx.1 hy.1 ha hb hab, ?_⟩
    have hcombo_pos : 0 < a • g x + b • g y := by
      exact (convex_Ioi (0 : 𝕜)) hx.2 hy.2 ha hb hab
    have hconc : a • g x + b • g y ≤ g (a • x + b • y) := hg.2 hx.1 hy.1 ha hb hab
    exact lt_of_lt_of_le hcombo_pos hconc
  have hg_t : ConcaveOn 𝕜 t g := hg.subset ht_subset ht_convex
  refine ⟨ht_convex, ?_⟩
  intro x hx y hy a b ha hb hab
  have hx_pos : 0 < g x := hx.2
  have hy_pos : 0 < g y := hy.2
  have hcombo_pos : 0 < a • g x + b • g y :=
    (convex_Ioi (0 : 𝕜)) hx_pos hy_pos ha hb hab
  have hz_pos : 0 < g (a • x + b • y) := (ht_convex hx hy ha hb hab).2
  have hconc : a • g x + b • g y ≤ g (a • x + b • y) := hg_t.2 hx hy ha hb hab
  have hrecip_le :
      1 / g (a • x + b • y) ≤ 1 / (a • g x + b • g y) :=
    hanti_one_div hcombo_pos hz_pos hconc
  calc
    1 / g (a • x + b • y) ≤ 1 / (a • g x + b • g y) := hrecip_le
    _ ≤ a • (1 / g x) + b • (1 / g y) := hconv_one_div.2 hx_pos hy_pos ha hb hab

end ConcaveOn

end

/-! ### Text_5_1_5 (from Chap01) -/
universe u v

section

/-
Source/core/bridge triage for this item.

- `source-facing`: Text 5.1.5 says that the affine value transform `(λ f + α)` of a proper convex
  function is again proper convex when `0 ≤ λ`.
- `core/canonical`: the owner predicates are `Function.IsProper` and `Function.IsConvex`, and the
  boundary-preserving affine value transform is expressed directly by the canonical owners
  `Function.toWithTopBot` and `Function.extendBotTop`, applied to the finite affine branch
  `t ↦ λ • t + α`.
- `bridge/view`: `extendBotTop` is essential here because the textbook convention at `+∞` is not
  the raw `WithTopBot` scalar-multiplication convention when `λ = 0`.

Domain-style sampling used here:
- `Function.IsProper` and `Function.IsProper.bot_lt` from `Definition_4_6`;
- `Function.IsConvex` from `Theorem_4_2`, imported through `Theorem_5_1`;
- `Function.IsConvex.comp_toWithTopBot_extendBotTop_of_monotone` from `Theorem_5_1`;
- `Function.toWithTopBot` and `Function.extendBotTop` from `EOrder.Basic`.

Primitive data vs derived API:
- primitive data: the finite affine branch `t ↦ λ • t + α`;
- core/canonical realization: the canonical codomain lift `.toWithTopBot` of the finite affine
  branch together with its boundary-preserving extension `extendBotTop`;
- derived API: the properness/convexity preservation theorem below, stated directly on that
  canonical composite rather than through a local wrapper owner.
-/

variable {𝕜 : Type v} {E : Type u}

namespace Function

private theorem affineBranch_convexOn_univ_of_nonneg
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (lam α : 𝕜) (hlam : 0 ≤ lam) :
    ConvexOn 𝕜 (Set.univ : Set 𝕜) (fun t : 𝕜 ↦ lam • t + α) := by
  have hAffineConvexOn : ConvexOn 𝕜 (Set.univ : Set 𝕜) (fun t : 𝕜 ↦ lam • t + α) := by
    have hId : ConvexOn 𝕜 (Set.univ : Set 𝕜) (fun t : 𝕜 ↦ t) := convexOn_id convex_univ
    have hSmul : ConvexOn 𝕜 (Set.univ : Set 𝕜) (fun t : 𝕜 ↦ lam • t) := hId.smul hlam
    simpa using hSmul.add_const α
  exact hAffineConvexOn

private theorem monotone_affineBranch_of_nonneg
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (lam α : 𝕜) (hlam : 0 ≤ lam) :
    Monotone (fun t : 𝕜 ↦ lam • t + α) := by
  intro x y hxy
  simpa [smul_eq_mul, add_comm, add_left_comm, add_assoc] using
    (add_le_add_right (mul_le_mul_of_nonneg_left hxy hlam) α)

/- Properness branch for Text 5.1.5 on the canonical owner surface. -/
theorem IsProper.comp_affineValueTransform
    {β : Type*} [SMul 𝕜 β] [Add β] [Preorder β]
    {f : E → WithTopBot β} (hf : f.IsProper) (lam : 𝕜) (a : β) :
    ((((fun t : β ↦ lam • t + a).toWithTopBot).extendBotTop) ∘ f).IsProper := by
  simpa using hf.comp_extendBotTop (fun t : β ↦ lam • t + a)

/-- Convexity branch for Text 5.1.5 on the canonical owner surface. -/
theorem IsConvex.comp_affineValueTransform_of_nonneg
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [AddCommMonoid E] [MulActionWithZero 𝕜 E]
    {f : E → WithTopBot 𝕜} (hf : f.IsConvex 𝕜)
    (lam α : 𝕜) (hlam : 0 ≤ lam) :
    ((((fun t : 𝕜 ↦ lam • t + α).toWithTopBot).extendBotTop) ∘ f).IsConvex 𝕜 := by
  simpa using hf.comp_toWithTopBot_extendBotTop_of_monotone
    (affineBranch_convexOn_univ_of_nonneg lam α hlam)
    (monotone_affineBranch_of_nonneg lam α hlam)

/-- Text 5.1.5: if `f` is proper convex and `0 ≤ λ`, then the canonical affine value composite
`((fun t ↦ λ • t + α).toWithTopBot).extendBotTop ∘ f` preserves both owners `IsProper` and
`IsConvex`. -/
theorem affineValueTransform_comp_isProper_and_isConvex_of_nonneg
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [AddCommMonoid E] [MulActionWithZero 𝕜 E]
    {f : E → WithTopBot 𝕜} (hf_proper : f.IsProper) (hf_convex : f.IsConvex 𝕜)
    (lam α : 𝕜) (hlam : 0 ≤ lam) :
    ((((fun t : 𝕜 ↦ lam • t + α).toWithTopBot).extendBotTop) ∘ f).IsProper ∧
      ((((fun t : 𝕜 ↦ lam • t + α).toWithTopBot).extendBotTop) ∘ f).IsConvex 𝕜 := by
  exact ⟨hf_proper.comp_affineValueTransform lam α,
    hf_convex.comp_affineValueTransform_of_nonneg lam α hlam⟩

end Function

end
