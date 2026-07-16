import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Basic
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {𝕜 : Type*}
variable {E : Type u}
variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid E]

namespace WithTopBot

/-- Three-branch recursor for the canonical `WithTop (WithBot α)` owner. -/
protected def rec {α : Type*} {motive : WithTopBot α → Sort*}
    (bot : motive ⊥) (top : motive ⊤) (coe : ∀ a : α, motive (a : WithTopBot α)) :
    ∀ x, motive x :=
  fun x ↦ WithTop.recTopCoe top (fun y ↦ WithBot.recBotCoe bot coe y) x

end WithTopBot

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
private theorem exists_coe_upper_of_ne_top (x : WithTopBot 𝕜) (hx : x ≠ ⊤) :
    ∃ μ : 𝕜, x ≤ (μ : WithTopBot 𝕜) := by
  induction x using WithTop.recTopCoe with
  | top => exact (hx rfl).elim
  | coe x =>
      induction x using WithBot.recBotCoe with
      | bot => exact ⟨0, bot_le⟩
      | coe μ => exact ⟨μ, le_rfl⟩

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
private theorem ne_top_of_extendBotTop_le_coe {β : Type v} [Preorder β]
    {φ : 𝕜 → WithTopBot β}
    {x : WithTopBot 𝕜} {α : β} (hx : φ.extendBotTop x ≤ (α : WithTopBot β)) :
    x ≠ ⊤ := by
  intro htop
  have hx' : (⊤ : WithTopBot β) ≤ (α : WithTopBot β) := by simpa [htop] using hx
  exact (WithTop.not_top_le_coe _ hx').elim

-- Proof sketch: interpret convexity of `f` and `φ` via convexity of their scalar epigraphs.
-- The inner function `f` already lives on the chapter-facing owner layer `WithTopBot 𝕜`; the
-- outer function is first extended canonically from `WithTopBot 𝕜` to `WithTopBot β` by
-- `Function.extendBotTop`,
-- which preserves finite values and sends the two boundary points to themselves. Convexity of `f`
-- controls the inner argument at convex combinations, monotonicity of `φ` transports that
-- inequality through the outer function, and convexity of `φ` gives the final height bound for
-- the composed epigraph.
/-- If a convex `WithTopBot 𝕜`-valued function takes the value `⊥` at the left endpoint of a
convex combination with positive left weight, then the value at the combination is still `⊥`,
provided the right endpoint has some finite upper bound. -/
private theorem IsConvex.eq_bot_smul_add_of_left_eq_bot [SMul 𝕜 E] {f : E → WithTopBot 𝕜}
    (hf : f.IsConvex 𝕜) {x y : E} {a b : 𝕜} (hfx : f x = ⊥) (ha : 0 < a) (hb : 0 ≤ b)
    (hab : a + b = 1) (hy : ∃ μ : 𝕜, f y ≤ (μ : WithTopBot 𝕜)) :
    f (a • x + b • y) = ⊥ := by
  have hlt : ∀ m : 𝕜, f (a • x + b • y) < (m : WithTopBot 𝕜) := by
    intro m
    rcases hy with ⟨μ, hyμ⟩
    let t : 𝕜 := (m - b * μ - a) / a
    have hx_epi : (x, t) ∈ {p : E × 𝕜 | f p.1 ≤ (p.2 : WithTopBot 𝕜)} := by
      simp [t, hfx]
    have hy_epi : (y, μ) ∈ {p : E × 𝕜 | f p.1 ≤ (p.2 : WithTopBot 𝕜)} := hyμ
    have hxy_epi := hf.convex_epigraph hx_epi hy_epi (le_of_lt ha) hb <| by
      simpa [smul_eq_mul, mul_add, add_comm, add_left_comm, add_assoc] using hab
    have hz_le : f (a • x + b • y) ≤ ((a * t + b * μ : 𝕜) : WithTopBot 𝕜) := by
      simpa [smul_eq_mul, mul_add, add_comm, add_left_comm, add_assoc] using hxy_epi
    have hat : a * t + b * μ = m - a := by
      have ha0 : a ≠ 0 := ne_of_gt ha
      dsimp [t]
      field_simp [ha0]
      ring
    have hma : m - a < m := by nlinarith [ha]
    exact lt_of_le_of_lt hz_le <| by
      exact_mod_cast (show a * t + b * μ < m by simpa [hat] using hma)
  cases hz : f (a • x + b • y) using WithTopBot.rec with
  | bot => rfl
  | top =>
      have h := hlt 0
      rw [hz] at h
      exact False.elim ((WithTop.not_top_le_coe _ (le_of_lt h)))
  | coe r =>
      have h := hlt r
      rw [hz] at h
      exact False.elim (lt_irrefl _ h)

/-- Right-endpoint version of `IsConvex.eq_bot_smul_add_of_left_eq_bot`. -/
private theorem IsConvex.eq_bot_smul_add_of_right_eq_bot [SMul 𝕜 E] {f : E → WithTopBot 𝕜}
    (hf : f.IsConvex 𝕜) {x y : E} {a b : 𝕜} (hfy : f y = ⊥) (ha : 0 ≤ a) (hb : 0 < b)
    (hab : a + b = 1) (hx : ∃ μ : 𝕜, f x ≤ (μ : WithTopBot 𝕜)) :
    f (a • x + b • y) = ⊥ := by
  have hswap : f (b • y + a • x) = ⊥ :=
    hf.eq_bot_smul_add_of_left_eq_bot hfy hb ha (by simpa [add_comm] using hab) hx
  simpa [add_comm] using hswap

/-- Extending a monotone finite map by the two boundary values remains monotone. -/
private theorem Monotone.extendBotTop {δ ε : Type*} [Preorder δ] [Preorder ε]
    {φ : δ → WithTopBot ε} (hφ : Monotone φ) :
    Monotone φ.extendBotTop := by
  intro x y hxy
  induction y using WithTop.recTopCoe with
  | top => exact le_top
  | coe y =>
      induction x using WithTop.recTopCoe with
      | top => exact False.elim ((WithTop.not_top_le_coe _ hxy))
      | coe x =>
          have hxy' : x ≤ y := WithTop.coe_le_coe.mp hxy
          induction x using WithBot.recBotCoe with
          | bot => exact bot_le
          | coe x =>
              induction y using WithBot.recBotCoe with
              | bot => exact False.elim ((WithBot.not_coe_le_bot x hxy'))
              | coe y =>
                  simpa using hφ (WithBot.coe_le_coe.mp hxy')

/-- Theorem 5.1 in owner form: if `f : E → (-∞, +∞]` and `φ : 𝕜 → WithTopBot β` are convex, and
`φ` is nondecreasing, then the canonical extension of `φ` composed with `f` is convex on `E`. -/
theorem IsConvex.comp_extendBotTop_of_monotone {β : Type v} [Module 𝕜 E]
    [AddCommMonoid β] [Module 𝕜 β] [PartialOrder β]
    {f : E → WithTopBot 𝕜} (hf : f.IsConvex 𝕜) {φ : 𝕜 → WithTopBot β}
    (hφ_conv : φ.IsConvex 𝕜) (hφ_mono : Monotone φ) :
    (φ.extendBotTop ∘ f).IsConvex 𝕜 := by
  let ψ : WithTopBot 𝕜 → WithTopBot β := φ.extendBotTop
  have hψ_mono : Monotone ψ := Monotone.extendBotTop hφ_mono
  let ef : Set (E × 𝕜) := {p : E × 𝕜 | f p.1 ≤ (p.2 : WithTopBot 𝕜)}
  let eφ : Set (𝕜 × β) := {p : 𝕜 × β | φ p.1 ≤ (p.2 : WithTopBot β)}
  have hf_epi : Convex 𝕜 ef := by
    simpa [ef] using hf.convex_epigraph
  have hφ_epi : Convex 𝕜 eφ := by
    simpa [eφ] using hφ_conv.convex_epigraph
  refine Function.isConvex_iff_convex_epigraph.2 ?_
  intro p hp q hq a b ha hb hab
  rcases p with ⟨x, η⟩
  rcases q with ⟨y, θ⟩
  have hp_val : ψ (f x) ≤ (η : WithTopBot β) := by
    simpa [ef, ψ] using hp
  have hq_val : ψ (f y) ≤ (θ : WithTopBot β) := by
    simpa [ef, ψ] using hq
  change
    ψ (f (a • x + b • y)) ≤ ((a • η + b • θ : β) : WithTopBot β)
  cases hfx : f x using WithTopBot.rec with
  | bot =>
      by_cases ha0 : a = 0
      · have hb1 : b = 1 := by
          rw [ha0, zero_add] at hab
          exact hab
        simpa [ψ, ha0, hb1] using hq_val
      · have ha_pos : 0 < a := by
          exact lt_of_le_of_ne ha (by simpa [eq_comm] using ha0)
        have hy : ∃ μ : 𝕜, f y ≤ (μ : WithTopBot 𝕜) := by
          exact exists_coe_upper_of_ne_top (f y) <|
            ne_top_of_extendBotTop_le_coe hq_val
        have hfz : f (a • x + b • y) = ⊥ :=
          hf.eq_bot_smul_add_of_left_eq_bot hfx ha_pos hb hab hy
        simp [ψ, hfz]
  | top =>
      exfalso
      have hp_top := hp_val
      have hp_top' : (⊤ : WithTopBot β) ≤ (η : WithTopBot β) := by simpa [ψ, hfx] using hp_top
      exact (not_lt_of_ge hp_top') (WithTop.coe_lt_top _)
  | coe rx =>
      cases hfy : f y using WithTopBot.rec with
      | bot =>
          by_cases hb0 : b = 0
          · have ha1 : a = 1 := by
              rw [hb0, add_zero] at hab
              exact hab
            simpa [ψ, hb0, ha1] using hp_val
          · have hb_pos : 0 < b := by
              exact lt_of_le_of_ne hb (by simpa [eq_comm] using hb0)
            have hx : ∃ μ : 𝕜, f x ≤ (μ : WithTopBot 𝕜) := by
              exact exists_coe_upper_of_ne_top (f x) <|
                ne_top_of_extendBotTop_le_coe hp_val
            have hfz : f (a • x + b • y) = ⊥ :=
              hf.eq_bot_smul_add_of_right_eq_bot hfy ha hb_pos hab hx
            simp [ψ, hfz]
      | top =>
          exfalso
          have hq_top := hq_val
          have hq_top' : (⊤ : WithTopBot β) ≤ (θ : WithTopBot β) := by
            simpa [ψ, hfy] using hq_top
          exact (not_lt_of_ge hq_top') (WithTop.coe_lt_top _)
      | coe ry =>
          have hx_epi : (x, rx) ∈ ef := by
            simp [ef, hfx]
          have hy_epi : (y, ry) ∈ ef := by
            simp [ef, hfy]
          have hxy_epi :=
            hf_epi hx_epi hy_epi ha hb <| by
              simpa [smul_eq_mul, mul_add, add_comm, add_left_comm, add_assoc] using hab
          have hf_le : f (a • x + b • y) ≤ ((a * rx + b * ry : 𝕜) : WithTopBot 𝕜) := by
            simpa [ef, smul_eq_mul, mul_add, add_comm, add_left_comm, add_assoc] using hxy_epi
          cases hfz : f (a • x + b • y) using WithTopBot.rec with
          | bot =>
              simp [ψ]
          | top =>
              exfalso
              have hf_top : (⊤ : WithTopBot 𝕜) ≤ ((a * rx + b * ry : 𝕜) : WithTopBot 𝕜) := by
                simpa [hfz] using hf_le
              exact (not_lt_of_ge hf_top) (WithTop.coe_lt_top _)
          | coe rz =>
              have hrz_le :
                  (rz : WithTopBot 𝕜) ≤ ((a * rx + b * ry : 𝕜) : WithTopBot 𝕜) := by
                simpa [hfz] using hf_le
              have hxφ_epi : (rx, η) ∈ eφ := by
                simpa [eφ, ψ, hfx] using hp_val
              have hyφ_epi : (ry, θ) ∈ eφ := by
                simpa [eφ, ψ, hfy] using hq_val
              have hφxy_epi :=
                hφ_epi hxφ_epi hyφ_epi ha hb <| by
                  simpa [smul_eq_mul, mul_add, add_comm, add_left_comm, add_assoc] using hab
              have hφ_le' : φ (a • rx + b • ry) ≤ ((a • η + b • θ : β) : WithTopBot β) := by
                simpa [eφ] using hφxy_epi
              have hφ_le : φ (a * rx + b * ry) ≤ ((a • η + b • θ : β) : WithTopBot β) := by
                simpa [smul_eq_mul] using hφ_le'
              have hmono : ψ (rz : WithTopBot 𝕜) ≤ ψ ((a * rx + b * ry : 𝕜) : WithTopBot 𝕜) :=
                hψ_mono hrz_le
              have hφ_leψ :
                  ψ ((a * rx + b * ry : 𝕜) : WithTopBot 𝕜) ≤
                    ((a • η + b • θ : β) : WithTopBot β) := by
                simpa [ψ] using hφ_le
              simpa [ψ, hfz] using hmono.trans hφ_leψ

/-- Finite-branch companion of `IsConvex.comp_extendBotTop_of_monotone`: if
`φ : 𝕜 → β` is convex on `Set.univ` and monotone, then
`((φ.toWithTopBot).extendBotTop) ∘ f` is convex. -/
theorem IsConvex.comp_toWithTopBot_extendBotTop_of_monotone {β : Type v}
    [Module 𝕜 E] [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β]
    [Module 𝕜 β] [PosSMulMono 𝕜 β]
    {f : E → WithTopBot 𝕜} (hf : f.IsConvex 𝕜) {φ : 𝕜 → β}
    (hφ_conv : ConvexOn 𝕜 (Set.univ : Set 𝕜) φ) (hφ_mono : Monotone φ) :
    (((φ.toWithTopBot).extendBotTop) ∘ f).IsConvex 𝕜 := by
  refine hf.comp_extendBotTop_of_monotone
    (Function.isConvex_coe_of_convexOn_univ (f := φ) hφ_conv) ?_
  intro x y hxy
  exact WithTop.coe_le_coe.mpr (WithBot.coe_le_coe.mpr (hφ_mono hxy))

end Function

end
