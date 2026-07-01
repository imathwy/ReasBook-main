import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Coe
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_2
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_5_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped BigOperators

section

variable {𝕜 : Type v} {E : Type u}
variable [Ring 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid E] [SMul 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 5.2 says that the pointwise sum of two proper convex functions is
  convex; the textbook states this in concrete coordinates, but the proof uses only the ambient
  ordered module structure already carried by the convexity owner.
- `core/canonical`: the chapter owner abstractions are `Function.IsProper` from Definition
  4.6 and the set-level convexity owner `ConvexOn` (with global `Function.IsConvex` as the
  `Set.univ` specialization).
- `bridge/view`: the proof route is the intrinsic epigraph owner bridge
  `convexOn_iff_convex_epigraph` together with order arithmetic on `WithTopBot 𝕜`; the
  owner-minimal bridge theorem `ConvexOn.add_of_bot_lt` isolates the only extra input actually
  used in the argument, namely pointwise exclusion of `⊥`, and the global numbered theorem is
  recovered as `Function.IsConvex.add_of_proper`.

- Primitive data vs derived API: the source-facing theorem uses the chapter owner predicates
  `Function.IsConvex` and `Function.IsProper`; the set-level bridge
  `ConvexOn.add_of_bot_lt` replaces properness by the derived pointwise lower-bound condition
  `∀ x ∈ S, ⊥ < f x`; the finite-sum / nonnegative-scaling lemmas are further derived
  owner API used by nearby downstream files.

Domain-style sampling used here:
- the chapter owner declaration `Function.IsProper` and its order-theoretic reformulation
  `Function.isProper_iff` from Definition 4.6;
- the chapter owner declaration `Function.IsConvex` from Theorem 4.2;
- `convexOn_iff_convex_epigraph` from the same owner file;
- the chapter `WithTopBot` owner arithmetic from `EOrder`.
-/

-- Proof sketch: if `a + b` is bounded above by a finite scalar and both summands are strictly
-- above `⊥`, then both summands are finite scalar values. Lift them to `𝕜`, keep one summand
-- unchanged, and recover the other by subtraction.
/-- A `WithTopBot 𝕜` sum bounded above by a finite scalar admits finite scalar upper bounds on the
summands whose sum is exactly that scalar. -/
private theorem exists_add_bounds_of_le
    {a b : WithTopBot 𝕜} {r : 𝕜}
    (ha_bot : ⊥ < a) (hb_bot : ⊥ < b) (h : a + b ≤ r) :
    ∃ r₁ r₂ : 𝕜, a ≤ r₁ ∧ b ≤ r₂ ∧ r₁ + r₂ = r := by
  have ha_top : a ≠ ⊤ := by
    intro ha
    have htop : (⊤ : WithTopBot 𝕜) ≤ (r : WithTopBot 𝕜) := by
      have hsum : (⊤ : WithTopBot 𝕜) + b ≤ (r : WithTopBot 𝕜) := by
        simpa [ha] using h
      have htop := hsum
      simp [WithTopBot.top_add_of_ne_bot hb_bot.ne'] at htop
    exact (not_le_of_gt (WithTopBot.coe_lt_top r)) htop
  have hb_top : b ≠ ⊤ := by
    intro hb
    have htop : (⊤ : WithTopBot 𝕜) ≤ (r : WithTopBot 𝕜) := by
      have hsum : a + (⊤ : WithTopBot 𝕜) ≤ (r : WithTopBot 𝕜) := by
        simpa [hb] using h
      have htop := hsum
      simp [WithTopBot.add_top_of_ne_bot ha_bot.ne'] at htop
    exact (not_le_of_gt (WithTopBot.coe_lt_top r)) htop
  rcases (WithTopBot.canLift_iff_ne_top_ne_bot).2 ⟨ha_top, ha_bot.ne'⟩ with ⟨a', ha'⟩
  rcases (WithTopBot.canLift_iff_ne_top_ne_bot).2 ⟨hb_top, hb_bot.ne'⟩ with ⟨b', hb'⟩
  have h' : a' + b' ≤ r := by
    exact WithTopBot.coe_le_coe.mp <| by
      simpa [ha', hb', WithTopBot.coe_add] using h
  refine ⟨a', r - a', ?_, ?_, by abel⟩
  · simpa [ha'] using
      (show ((a' : WithTopBot 𝕜) ≤ (a' : WithTopBot 𝕜)) from le_rfl)
  · have hb_le : b' ≤ r - a' := by
      exact (le_sub_iff_add_le).2 <| by simpa [add_comm] using h'
    simpa [hb'] using
      (WithTopBot.coe_le_coe_iff.2 hb_le :
        ((b' : WithTopBot 𝕜) ≤ ((r - a' : 𝕜) : WithTopBot 𝕜)))

namespace ConvexOn

/-- Set-level owner form of Theorem 5.2: if two `WithTopBot`-valued functions are convex on `S`
and everywhere strictly above `⊥` on `S`, then their pointwise sum is convex on `S`. -/
theorem add_of_bot_lt
    {S : Set E} {f₁ f₂ : E → WithTopBot 𝕜}
    (hf₁ : ConvexOn 𝕜 S f₁)
    (hf₂ : ConvexOn 𝕜 S f₂)
    (hf₁_bot : ∀ x ∈ S, ⊥ < f₁ x)
    (hf₂_bot : ∀ x ∈ S, ⊥ < f₂ x) :
    ConvexOn 𝕜 S (f₁ + f₂) := by
  rw [convexOn_iff_convex_epigraph] at hf₁ hf₂ ⊢
  intro p hp q hq a b ha hb hab
  rcases p with ⟨x, α⟩
  rcases q with ⟨y, β⟩
  have hxS : x ∈ S := hp.1
  have hyS : y ∈ S := hq.1
  have hx : f₁ x + f₂ x ≤ (α : WithTopBot 𝕜) := by
    simpa [Pi.add_apply] using hp.2
  have hy : f₁ y + f₂ y ≤ (β : WithTopBot 𝕜) := by
    simpa [Pi.add_apply] using hq.2
  rcases exists_add_bounds_of_le (hf₁_bot x hxS) (hf₂_bot x hxS) hx with
    ⟨α₁, α₂, hx₁, hx₂, hα⟩
  rcases exists_add_bounds_of_le (hf₁_bot y hyS) (hf₂_bot y hyS) hy with
    ⟨β₁, β₂, hy₁, hy₂, hβ⟩
  have hx₁_epi : (x, α₁) ∈ {p : E × 𝕜 | p.1 ∈ S ∧ f₁ p.1 ≤ p.2} := by
    exact ⟨hxS, hx₁⟩
  have hy₁_epi : (y, β₁) ∈ {p : E × 𝕜 | p.1 ∈ S ∧ f₁ p.1 ≤ p.2} := by
    exact ⟨hyS, hy₁⟩
  have hx₂_epi : (x, α₂) ∈ {p : E × 𝕜 | p.1 ∈ S ∧ f₂ p.1 ≤ p.2} := by
    exact ⟨hxS, hx₂⟩
  have hy₂_epi : (y, β₂) ∈ {p : E × 𝕜 | p.1 ∈ S ∧ f₂ p.1 ≤ p.2} := by
    exact ⟨hyS, hy₂⟩
  have h₁_epi := hf₁ hx₁_epi hy₁_epi ha hb hab
  have h₂_epi := hf₂ hx₂_epi hy₂_epi ha hb hab
  have h₁ :
      f₁ (a • x + b • y) ≤ (((a * α₁ + b * β₁ : 𝕜) : WithTopBot 𝕜)) := by
    simpa [smul_eq_mul, mul_add, add_comm, add_left_comm, add_assoc] using h₁_epi.2
  have h₂ :
      f₂ (a • x + b • y) ≤ (((a * α₂ + b * β₂ : 𝕜) : WithTopBot 𝕜)) := by
    simpa [smul_eq_mul, mul_add, add_comm, add_left_comm, add_assoc] using h₂_epi.2
  have hsum :
      f₁ (a • x + b • y) + f₂ (a • x + b • y) ≤
        (((a * α₁ + b * β₁ : 𝕜) : WithTopBot 𝕜) +
          (((a * α₂ + b * β₂ : 𝕜) : WithTopBot 𝕜))) :=
    add_le_add h₁ h₂
  have hbound :
      (((a * α₁ + b * β₁ : 𝕜) : WithTopBot 𝕜) +
          (((a * α₂ + b * β₂ : 𝕜) : WithTopBot 𝕜))) =
        (((a * α + b * β : 𝕜) : WithTopBot 𝕜)) := by
    calc
      (((a * α₁ + b * β₁ : 𝕜) : WithTopBot 𝕜) +
          (((a * α₂ + b * β₂ : 𝕜) : WithTopBot 𝕜))) =
          ((((a * α₁ + b * β₁) + (a * α₂ + b * β₂) : 𝕜) : WithTopBot 𝕜)) := by
              rw [← WithTopBot.coe_add]
      _ = ((((a * α₁ + a * α₂) + (b * β₁ + b * β₂) : 𝕜) : WithTopBot 𝕜)) := by
            congr 1
            abel
      _ = (((a * (α₁ + α₂) + b * (β₁ + β₂) : 𝕜) : WithTopBot 𝕜)) := by
            congr 1
            rw [← mul_add, ← mul_add]
      _ = (((a * α + b * β : 𝕜) : WithTopBot 𝕜)) := by
            simp [hα, hβ]
  have hsum' :
      f₁ (a • x + b • y) + f₂ (a • x + b • y) ≤
        (((a * α + b * β : 𝕜) : WithTopBot 𝕜)) := hbound ▸ hsum
  exact ⟨h₁_epi.1, by
    simpa [Pi.add_apply, smul_eq_mul, mul_add, add_comm, add_left_comm, add_assoc] using hsum'⟩

/-- Set-level properness companion of `ConvexOn.add_of_bot_lt`: properness is used only through
pointwise `⊥`-exclusion. -/
theorem add_of_proper
    {S : Set E} {f₁ f₂ : E → WithTopBot 𝕜}
    (hf₁ : ConvexOn 𝕜 S f₁)
    (hf₂ : ConvexOn 𝕜 S f₂)
    (hf₁_proper : f₁.IsProper)
    (hf₂_proper : f₂.IsProper) :
    ConvexOn 𝕜 S (f₁ + f₂) := by
  exact hf₁.add_of_bot_lt hf₂
    (fun x _ ↦ hf₁_proper.bot_lt x)
    (fun x _ ↦ hf₂_proper.bot_lt x)

end ConvexOn

namespace Function

/-- If two convex `WithTopBot`-valued functions are everywhere strictly above `⊥`, then their
pointwise sum is convex. This is Theorem 5.2 in global owner form, derived from the set-level
owner theorem `ConvexOn.add_of_bot_lt` on `Set.univ`. -/
theorem IsConvex.add_of_bot_lt
    {f₁ f₂ : E → WithTopBot 𝕜}
    (hf₁ : IsConvex 𝕜 f₁)
    (hf₂ : IsConvex 𝕜 f₂)
    (hf₁_bot : ∀ x : E, ⊥ < f₁ x)
    (hf₂_bot : ∀ x : E, ⊥ < f₂ x) :
    IsConvex 𝕜 (f₁ + f₂) := by
  simpa [Function.IsConvex] using
    (ConvexOn.add_of_bot_lt (S := Set.univ)
      (hf₁ := by simpa [Function.IsConvex] using hf₁)
      (hf₂ := by simpa [Function.IsConvex] using hf₂)
      (hf₁_bot := fun x _ ↦ hf₁_bot x)
      (hf₂_bot := fun x _ ↦ hf₂_bot x))

/-- Properness-form restatement of Theorem 5.2. This companion adds no new mathematics: it uses
`Function.IsProper` only to recover the pointwise `⊥`-exclusion required by the main owner
theorem `Function.IsConvex.add_of_bot_lt`. -/
theorem IsConvex.add_of_proper
    {f₁ f₂ : E → WithTopBot 𝕜}
    (hf₁ : IsConvex 𝕜 f₁)
    (hf₂ : IsConvex 𝕜 f₂)
    (hf₁_proper : f₁.IsProper)
    (hf₂_proper : f₂.IsProper) :
    IsConvex 𝕜 (f₁ + f₂) := by
  simpa [Function.IsConvex] using
    (ConvexOn.add_of_proper (S := Set.univ)
      (hf₁ := by simpa [Function.IsConvex] using hf₁)
      (hf₂ := by simpa [Function.IsConvex] using hf₂)
      hf₁_proper hf₂_proper)

/-- A finite sum of convex `WithTopBot`-valued functions is convex when every summand is
everywhere strictly above `⊥`. -/
theorem isConvex_sum_of_bot_lt
    {ι : Type*} (s : Finset ι) (g : ι → E → WithTopBot 𝕜)
    (hg_bot : ∀ i ∈ s, ∀ x : E, ⊥ < g i x)
    (hg_convex : ∀ i ∈ s, IsConvex 𝕜 (g i)) :
    IsConvex 𝕜 (s.sum g) := by
  classical
  revert hg_bot hg_convex
  refine Finset.induction_on s ?_ ?_
  · intro hg_bot hg_convex
    simpa using isConvex_zero
  · intro i s hi hs hg_bot hg_convex
    have hs_bot : ∀ j ∈ s, ∀ x : E, ⊥ < g j x := by
      intro j hj x
      exact hg_bot j (by simp [hj]) x
    have hs_convex : ∀ j ∈ s, IsConvex 𝕜 (g j) := by
      intro j hj
      exact hg_convex j (by simp [hj])
    have hsum_bot' : ∀ x : E, ⊥ < s.sum (fun j ↦ g j x) := by
      intro x
      simpa using
        (WithBot.bot_lt_sum_iff.2 (fun j hj ↦ hs_bot j hj x) :
          (⊥ : WithTopBot 𝕜) < s.sum (fun j ↦ g j x))
    have hsum_bot : ∀ x : E, ⊥ < (s.sum g) x := by
      intro x
      simpa [Finset.sum_apply] using hsum_bot' x
    have hsum_convex : IsConvex 𝕜 (s.sum g) :=
      hs hs_bot hs_convex
    simpa [Finset.sum_insert, hi] using
      (hg_convex i (by simp)).add_of_bot_lt hsum_convex (hg_bot i (by simp)) hsum_bot

end Function

end

section

variable {𝕜 : Type v} {E : Type u}
variable [Ring 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid E] [MulActionWithZero 𝕜 E]

namespace Function

/-- Multiplying a convex `WithTopBot 𝕜`-valued function by a nonnegative scalar preserves
convexity. -/
theorem IsConvex.smul_nonneg
    {f : E → WithTopBot 𝕜} (hf : IsConvex 𝕜 f) {a : 𝕜} (ha : 0 ≤ a) :
    IsConvex 𝕜 (a • f) := by
  rcases eq_or_lt_of_le ha with rfl | ha_pos
  · have h0 : (0 : 𝕜) • f = (fun _ : E ↦ (0 : WithTopBot 𝕜)) := by
      funext x
      cases hfx : f x using WithTopBot.rec with
      | bot =>
          simp [WithTopBot.smul_def, hfx]
      | top =>
          simp [WithTopBot.smul_def, hfx]
      | coe t =>
          simp [WithTopBot.smul_def, hfx]
    simpa [h0] using (Function.isConvex_zero (𝕜 := 𝕜) (E := E) (β := 𝕜))
  · let φ : 𝕜 → WithTopBot 𝕜 := fun t ↦ (a * t : 𝕜)
    have hφ_conv : φ.IsConvex 𝕜 := by
      have hId : ConvexOn 𝕜 (Set.univ : Set 𝕜) (fun t : 𝕜 ↦ t) := convexOn_id convex_univ
      have hSmul : ConvexOn 𝕜 (Set.univ : Set 𝕜) (fun t : 𝕜 ↦ a • t) := hId.smul ha
      exact Function.isConvex_coe_of_convexOn_univ (f := fun t : 𝕜 ↦ a * t) <| by
        simpa [smul_eq_mul] using hSmul
    have hφ_mono : Monotone φ := by
      intro x y hxy
      exact (WithTopBot.coe_le_coe_iff).2 <| mul_le_mul_of_nonneg_left hxy ha
    have hcomp : (φ.extendBotTop ∘ f).IsConvex 𝕜 :=
      hf.comp_extendBotTop_of_monotone hφ_conv hφ_mono
    have hEq : (φ.extendBotTop ∘ f) = a • f := by
      funext x
      cases hfx : f x using WithTopBot.rec with
      | bot =>
          simp [φ, hfx, WithTopBot.smul_def,
            WithTopBot.coe_mul_bot_of_pos (α := 𝕜) ha_pos]
      | top =>
          simp [φ, hfx, WithTopBot.smul_def,
            WithTopBot.coe_mul_top_of_pos (α := 𝕜) ha_pos]
      | coe t =>
          simp [φ, hfx, WithTopBot.smul_def, WithTopBot.coe_mul]
    simpa [hEq] using hcomp

end Function

end

section

variable {β : Type v}
variable [LT β] [AddCommMonoid β]

namespace Function

/-- If a finite pointwise sum of proper `WithTopBot`-valued functions is finite somewhere, then
that sum is proper. This clause belongs to the owner predicate `Function.IsProper`, so it is kept
with the finite-sum owner API rather than in a later source-facing Chapter 2 theorem file. -/
-- Proof sketch: a finite point of the sum gives nonemptiness of its effective domain. Each proper
-- summand is everywhere strictly above `⊥`, hence so is their finite sum by
-- `WithBot.bot_lt_sum_iff`; this yields pointwise `≠ ⊥`, and the chapter characterization
-- `isProper_iff` then gives properness.
theorem isProper_sum_of_exists_lt_top
    {X : Type*} {ι : Type*}
    (s : Finset ι)
    (f : ι → X → WithTopBot β)
    (hf_proper : ∀ i ∈ s, IsProper (f i))
    (hsum_finite : ∃ x : X, s.sum (fun i ↦ f i x) < (⊤ : WithTopBot β)) :
    IsProper (s.sum f) := by
  rcases hsum_finite with ⟨x, hx⟩
  refine (isProper_iff _).2 ?_
  refine ⟨⟨x, by simpa [mem_effectiveDomain] using hx⟩, ?_⟩
  intro y
  have hsum_bot' : (⊥ : WithTopBot β) < s.sum (fun i ↦ f i y) := by
    exact (WithBot.bot_lt_sum_iff.2
      (fun i hi ↦ Function.IsProper.bot_lt (hf_proper i hi) y) :
        (⊥ : WithTopBot β) < s.sum (fun i ↦ f i y))
  have hsum_bot : (⊥ : WithTopBot β) < (s.sum f) y := by
    simpa [Finset.sum_apply] using hsum_bot'
  exact (WithBot.bot_lt_iff_ne_bot).1 hsum_bot

end Function

end
