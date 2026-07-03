import Mathlib
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_3_1_16 (from Chap03) -/
open Set
open scoped BigOperators Gradient SupportFunction WithTopConvexAnalysis EuclideanOrthant

noncomputable section

universe u

variable {m : ℕ} {E : Type u}

local notation "Eₘ" => EuclideanSpace ℝ (Fin m)

/- Lemma 3.1.16 lies in the chapter's support-function composition / subdifferential-calculus
domain on real inner-product spaces with finite-coordinate multipliers.

Primary domain:
- support functions `ξ[Λ]` composed with the canonical coordinate package
  `x ↦ (f₁(x), …, f_m(x))`.

Sampled owner declarations:
- `EuclideanSpace.nonnegativeOrthant` and `LagrangianProblem.constraintVector` in
  `Definition_1_10_2`
- `supportFunction` and the notation `ξ[Λ]` in `Definition_3_9`
- `pointwiseSupremumOn` in `Theorem_3_1_8`
- `activePointwiseSupremumOnIndices` in `Lemma_3_1_14`
- `subdifferential` in `Definition_3_1_5`
- `HasGradientAt` and `HasGradientAt.gradient` from mathlib's gradient owner API

Best owner abstractions:
- `LagrangianProblem.constraintVector` for the canonical packaging of a finite scalar family into
  an `ℝ^m`-valued map
- the source-facing support-function composition `x ↦ ξ[Λ] (vectorMap fs x)`
- the source-facing active-multiplier face `activeSupportFunctionMultipliers Λ fs x`
- `subdifferential` from `Definition_3_1_5`, with `supportFunctionCompWithTop Λ fs` kept only as
  the thin `WithTop ℝ` bridge needed for that owner

Primitive data:
- a weight set `Λ : Set Eₘ`
- a coordinate family `fs : Fin m → E → ℝ`

Derived API kept here:
- `vectorMap fs` as the source-facing shorthand for the owner coordinate package
- `supportFunctionCompWithTop Λ fs` as the thin `WithTop ℝ` bridge of `ξ[Λ] ∘ vectorMap fs`
- `activeSupportFunctionMultipliers Λ fs x` as the active face of `ξ[Λ]` at `vectorMap fs x`
- `weightedGradientCombination fs x` as the weighted sum of the component gradients

Source/core/bridge triage:
- source-facing: the support-function composition `x ↦ ξ[Λ] (vectorMap fs x)` and its active
  multipliers
- core/canonical: `EuclideanSpace.nonnegativeOrthant`, `LagrangianProblem.constraintVector`,
  `supportFunction`, `pointwiseSupremumOn`, `activePointwiseSupremumOnIndices`, `subdifferential`
- bridge/view: `supportFunctionCompWithTop Λ fs`, together with `vectorMap` and
  `weightedGradientCombination`

This file therefore keeps the public theorem surface on `ξ[Λ] ∘ vectorMap` and uses the generic
pointwise-supremum machinery only as a thin bridge for the chapter's `WithTop` subdifferential
owner.
-/

/-- The source-facing coordinate package `x ↦ (f₁(x), …, f_m(x))`, derived from the chapter owner
`LagrangianProblem.constraintVector`. -/
abbrev vectorMap (fs : Fin m → E → ℝ) : E → Eₘ :=
  (LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector

/-- Evaluating `vectorMap fs x` at coordinate `i` recovers `f_i x`. -/
@[simp] theorem vectorMap_apply (fs : Fin m → E → ℝ) (x : E) (i : Fin m) :
    vectorMap fs x i = fs i x :=
  rfl

/-- The `WithTop`-valued bridge of the support-function composition `x ↦ ξ[Λ] (vectorMap fs x)`,
used only where the chapter owner `subdifferential` requires codomain `WithTop ℝ`. -/
abbrev supportFunctionCompWithTop
    (Λ : Set Eₘ) (fs : Fin m → E → ℝ) : E → WithTop ℝ :=
  pointwiseSupremumOn Λ (fun x lam ↦ (inner ℝ lam (vectorMap fs x) : WithTop ℝ))

/-- The active multiplier face of the support-function bridge at the point `vectorMap fs x`,
reused from the generic active-index owner `activePointwiseSupremumOnIndices`. -/
abbrev activeSupportFunctionMultipliers
    (Λ : Set Eₘ) (fs : Fin m → E → ℝ) (x : E) : Set Eₘ :=
  activePointwiseSupremumOnIndices
    Λ
    (fun y lam ↦ (inner ℝ lam (vectorMap fs y) : WithTop ℝ))
    x

/-- Membership in `activeSupportFunctionMultipliers Λ fs x` means that `lam ∈ Λ` attains the
support-function bridge value at `vectorMap fs x`. -/
@[simp] theorem mem_activeSupportFunctionMultipliers_iff
    {Λ : Set Eₘ} {fs : Fin m → E → ℝ} {x : E} {lam : Eₘ} :
    lam ∈ activeSupportFunctionMultipliers Λ fs x ↔
      lam ∈ Λ ∧
        (inner ℝ lam (vectorMap fs x) : WithTop ℝ) = supportFunctionCompWithTop Λ fs x :=
  Iff.rfl

section Convexity

variable [AddCommMonoid E] [Module ℝ E]

/-- Lemma 3.1.16 (1): if `Λ ⊆ ℝ_+^m` and each component `f_i` is convex, then the
finite real part of the support-function composition `x ↦ ξ[Λ] (vectorMap fs x)` is convex on its
effective domain. -/
-- Proof sketch: for each fixed `lam ∈ Λ`, nonnegativity of its coordinates makes
-- `x ↦ ⟪lam, vectorMap fs x⟫ = ∑ i, lam i * f_i x` a nonnegative linear combination of convex
-- functions, hence convex. The support function `ξ[Λ] (vectorMap fs x)` is the supremum of these
-- convex slices over `Λ`, so its finite real part is convex on the intrinsic finite-value domain.
-- When `Λ` is also bounded and nonempty, Proposition 3.11 upgrades that domain to `Set.univ`.
theorem convexOn_supportFunction_comp_vectorMap
    {Λ : Set Eₘ} {fs : Fin m → E → ℝ}
    (hΛ_nonneg : Λ ⊆ ℝ₊^m)
    (hfs_convex : ∀ i, ConvexOn ℝ Set.univ (fs i)) :
    ConvexOn ℝ (extendedRealEffectiveDomain (ξ[Λ] ∘ vectorMap fs))
      (extendedRealRealPart (ξ[Λ] ∘ vectorMap fs)) :=
  by
    let f : E → EReal := ξ[Λ] ∘ vectorMap fs
    -- Route correction: follow the textbook directly by proving the support-function Jensen bound
    -- for `f`, and then reuse that same bound both for domain convexity and for the real-part
    -- convexity inequality.
    have hsupport_jensen :
        ∀ {x y : E} (hx : x ∈ extendedRealEffectiveDomain f)
          (hy : y ∈ extendedRealEffectiveDomain f)
          {a b : ℝ}, 0 ≤ a → 0 ≤ b → a + b = 1 →
          f (a • x + b • y) ≤
            ((a * extendedRealRealPart f x + b * extendedRealRealPart f y : ℝ) : EReal) := by
      intro x y hx hy a b ha hb hab
      -- Compare each active slice with the convex combination of the support values at `x` and `y`.
      rw [show f (a • x + b • y) = ξ[Λ] (vectorMap fs (a • x + b • y)) by rfl, supportFunction_apply]
      refine sSup_le ?_
      rintro _ ⟨lam, hlamΛ, rfl⟩
      have hlam_nonneg : ∀ i, 0 ≤ lam i := by
        intro i
        have horth : lam ∈ ℝ₊^m := hΛ_nonneg hlamΛ
        simpa [EuclideanSpace.mem_nonnegativeOrthant_iff] using horth i
      have hx_slice :
          inner ℝ lam (vectorMap fs x) ≤ extendedRealRealPart f x := by
        have hx_slice_ereal :
            ((inner ℝ lam (vectorMap fs x) : ℝ) : EReal) ≤ f x := by
          rw [show f x = ξ[Λ] (vectorMap fs x) by rfl, supportFunction_apply]
          exact le_sSup ⟨lam, hlamΛ, rfl⟩
        exact (le_extendedRealRealPart_iff hx).2 hx_slice_ereal
      have hy_slice :
          inner ℝ lam (vectorMap fs y) ≤ extendedRealRealPart f y := by
        have hy_slice_ereal :
            ((inner ℝ lam (vectorMap fs y) : ℝ) : EReal) ≤ f y := by
          rw [show f y = ξ[Λ] (vectorMap fs y) by rfl, supportFunction_apply]
          exact le_sSup ⟨lam, hlamΛ, rfl⟩
        exact (le_extendedRealRealPart_iff hy).2 hy_slice_ereal
      have hslice_convex :
          inner ℝ lam (vectorMap fs (a • x + b • y)) ≤
            a * inner ℝ lam (vectorMap fs x) + b * inner ℝ lam (vectorMap fs y) := by
        have hinner_eq :
            ∀ z : E, inner ℝ lam (vectorMap fs z) = ∑ i, lam i * fs i z := by
          intro z
          rw [PiLp.inner_apply]
          refine Finset.sum_congr rfl ?_
          intro i hi
          change (vectorMap fs z i) * lam i = lam i * fs i z
          simp
          ring
        have hsum :
            ∑ i, lam i * fs i (a • x + b • y) ≤
              ∑ i, lam i * (a * fs i x + b * fs i y) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          exact
            mul_le_mul_of_nonneg_left
              ((hfs_convex i).2 (by simp) (by simp) ha hb hab) (hlam_nonneg i)
        calc
          inner ℝ lam (vectorMap fs (a • x + b • y))
              = ∑ i, lam i * fs i (a • x + b • y) := hinner_eq _
          _ ≤ ∑ i, lam i * (a * fs i x + b * fs i y) := hsum
          _ = a * inner ℝ lam (vectorMap fs x) + b * inner ℝ lam (vectorMap fs y) := by
            calc
              ∑ i, lam i * (a * fs i x + b * fs i y)
                  = ∑ i, (a * (lam i * fs i x) + b * (lam i * fs i y)) := by
                      refine Finset.sum_congr rfl ?_
                      intro i hi
                      ring
              _ = ∑ i, a * (lam i * fs i x) + ∑ i, b * (lam i * fs i y) := by
                    rw [Finset.sum_add_distrib]
              _ = a * ∑ i, lam i * fs i x + b * ∑ i, lam i * fs i y := by
                    rw [← Finset.mul_sum, ← Finset.mul_sum]
              _ = a * inner ℝ lam (vectorMap fs x) + b * inner ℝ lam (vectorMap fs y) := by
                    rw [hinner_eq, hinner_eq]
      have hslice_bound :
          inner ℝ lam (vectorMap fs (a • x + b • y)) ≤
            a * extendedRealRealPart f x + b * extendedRealRealPart f y := by
        have hx_scaled :
            a * inner ℝ lam (vectorMap fs x) ≤ a * extendedRealRealPart f x :=
          mul_le_mul_of_nonneg_left hx_slice ha
        have hy_scaled :
            b * inner ℝ lam (vectorMap fs y) ≤ b * extendedRealRealPart f y :=
          mul_le_mul_of_nonneg_left hy_slice hb
        linarith
      change (((inner ℝ lam (vectorMap fs (a • x + b • y)) : ℝ) : EReal) ≤
        ((a * extendedRealRealPart f x + b * extendedRealRealPart f y : ℝ) : EReal))
      exact_mod_cast hslice_bound
    have hdom_convex : Convex ℝ (extendedRealEffectiveDomain f) := by
      rw [convex_iff_add_mem]
      intro x hx y hy a b ha hb hab
      have hΛ_nonempty : Λ.Nonempty := by
        by_contra hΛ_empty
        have hΛ_eq : Λ = ∅ := Set.not_nonempty_iff_eq_empty.mp hΛ_empty
        have hx_bot : f x = ⊥ := by
          simp [f, supportFunction_apply, hΛ_eq]
        exact hx.2 hx_bot
      obtain ⟨lam, hlamΛ⟩ := hΛ_nonempty
      have hupper :
          f (a • x + b • y) ≤
            ((a * extendedRealRealPart f x + b * extendedRealRealPart f y : ℝ) : EReal) :=
        hsupport_jensen hx hy ha hb hab
      have hlower :
          (((inner ℝ lam (vectorMap fs (a • x + b • y)) : ℝ)) : EReal) ≤
            f (a • x + b • y) := by
        rw [show f (a • x + b • y) = ξ[Λ] (vectorMap fs (a • x + b • y)) by rfl, supportFunction_apply]
        exact le_sSup ⟨lam, hlamΛ, rfl⟩
      refine ⟨?_, ?_⟩
      · exact ne_top_of_le_ne_top (EReal.coe_ne_top _) hupper
      · intro hz_bot
        have : (((inner ℝ lam (vectorMap fs (a • x + b • y)) : ℝ)) : EReal) ≤ (⊥ : EReal) := by
          simpa [hz_bot] using hlower
        exact (not_le_of_gt (EReal.bot_lt_coe _)) this
    refine ⟨hdom_convex, ?_⟩
    · intro x hx y hy a b ha hb hab
      have hz :
          a • x + b • y ∈ extendedRealEffectiveDomain f :=
        hdom_convex hx hy ha hb hab
      exact (extendedRealRealPart_le_iff hz).2 (hsupport_jensen hx hy ha hb hab)

end Convexity

section Gradient

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [CompleteSpace E]

/-- The weighted sum of the gradients `∇ f_i(x)` with weights given by the coordinates of
`lam ∈ ℝ^m`. -/
def weightedGradientCombination (fs : Fin m → E → ℝ) (x : E) (lam : Eₘ) : E :=
  ∑ i, (lam i) • ∇ (fs i) x

/-- Helper for Lemma 3.1.16: the nonnegative orthant in `ℝ^m` is closed. -/
private theorem nonnegativeOrthant_isClosed : IsClosed (ℝ₊^m : Set Eₘ) := by
  let e : Eₘ ≃ₜ (Fin m → ℝ) := (EuclideanSpace.equiv (Fin m) ℝ).toHomeomorph
  have horthant :
      (ℝ₊^m : Set Eₘ) =
        e ⁻¹' Set.pi Set.univ (fun _ : Fin m ↦ Set.Ici (0 : ℝ)) := by
    ext x
    simp [EuclideanSpace.mem_nonnegativeOrthant_iff, Pi.le_def, e]
  -- Transport the coordinatewise closed halfspaces through the Euclidean homeomorphism.
  rw [horthant]
  exact (isClosed_set_pi fun _ _ ↦ isClosed_Ici).preimage e.continuous

/-- Helper for Lemma 3.1.16: the support slice against `vectorMap fs x` is the coordinatewise
weighted sum `∑ᵢ λᵢ fᵢ(x)`. -/
private theorem inner_vectorMap_eq_sum
    (fs : Fin m → E → ℝ) (x : E) (lam : Eₘ) :
    inner ℝ lam (vectorMap fs x) = ∑ i, lam i * fs i x := by
  -- Expand the Euclidean inner product coordinatewise.
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl ?_
  intro i hi
  change (vectorMap fs x i) * lam i = lam i * fs i x
  simp
  ring

/-- Helper for Lemma 3.1.16: pairing the weighted gradient combination with a direction expands
coordinatewise. -/
private theorem inner_weightedGradientCombination
    (fs : Fin m → E → ℝ) (x h : E) (lam : Eₘ) :
    inner ℝ (weightedGradientCombination fs x lam) h =
      ∑ i, lam i * inner ℝ (∇ (fs i) x) h := by
  -- Expand the inner product of the finite sum term by term.
  rw [weightedGradientCombination, real_inner_comm, inner_sum]
  simp [real_inner_smul_right, real_inner_comm]

/-- Helper for Lemma 3.1.16: under compactness, the `WithTop` support-function bridge is finite
at every point. -/
private theorem supportFunctionCompWithTop_mem_dom_of_nonempty_compact
    {Λ : Set Eₘ} {fs : Fin m → E → ℝ}
    (hΛ_nonempty : Λ.Nonempty) (hΛ_compact : IsCompact Λ) (x : E) :
    x ∈ dom (supportFunctionCompWithTop Λ fs) := by
  -- Compactness bounds all multipliers uniformly, so the support slice stays below a finite real.
  rw [mem_withTopEffectiveDomain_iff, supportFunctionCompWithTop, pointwiseSupremumOn_apply]
  obtain ⟨R, hR⟩ := hΛ_compact.isBounded.exists_norm_le
  refine lt_top_iff_ne_top.mpr ?_
  apply ne_top_of_le_ne_top (b := ((R * ‖vectorMap fs x‖ : ℝ) : WithTop ℝ))
  · exact WithTop.coe_ne_top
  · refine csSup_le ?_ ?_
    · rcases hΛ_nonempty with ⟨lam, hlam⟩
      exact ⟨((inner ℝ lam (vectorMap fs x) : ℝ) : WithTop ℝ), ⟨lam, hlam, rfl⟩⟩
    rintro _ ⟨lam, hlam, rfl⟩
    have hle :
        inner ℝ lam (vectorMap fs x) ≤ R * ‖vectorMap fs x‖ :=
      (real_inner_le_norm lam (vectorMap fs x)).trans <|
        mul_le_mul_of_nonneg_right (hR lam hlam) (norm_nonneg (vectorMap fs x))
    have hle' :
        ((inner ℝ lam (vectorMap fs x) : ℝ) : WithTop ℝ) ≤
          ((R * ‖vectorMap fs x‖ : ℝ) : WithTop ℝ) := by
      exact_mod_cast hle
    simpa using hle'

/-- Helper for Lemma 3.1.16: compactness makes the `WithTop` support-function composition finite
everywhere, so its finite real part is convex on its whole effective domain. -/
private theorem convexOn_supportFunctionCompWithTop_of_nonempty_compact
    {Λ : Set Eₘ} {fs : Fin m → E → ℝ}
    (hΛ_nonempty : Λ.Nonempty) (hΛ_compact : IsCompact Λ) (hΛ_nonneg : Λ ⊆ ℝ₊^m)
    (hfs_convex : ∀ i, ConvexOn ℝ Set.univ (fs i)) :
    ConvexOn ℝ (dom (supportFunctionCompWithTop Λ fs))
      (withTopRealPart (supportFunctionCompWithTop Λ fs)) := by
  let f : E → WithTop ℝ := supportFunctionCompWithTop Λ fs
  have hdom : dom f = Set.univ := by
    refine Set.eq_univ_iff_forall.mpr ?_
    intro z
    simpa [f] using
      supportFunctionCompWithTop_mem_dom_of_nonempty_compact
        (Λ := Λ) (fs := fs) hΛ_nonempty hΛ_compact z
  refine ⟨by simpa [f, hdom] using (convex_univ : Convex ℝ (Set.univ : Set E)), ?_⟩
  intro x hx y hy a b ha hb hab
  have hxdom : x ∈ dom f := by simpa [hdom] using hx
  have hydom : y ∈ dom f := by simpa [hdom] using hy
  have hzdom : a • x + b • y ∈ dom f := by simpa [hdom]
  -- Compare each support slice with the convex combination of the two endpoint support values.
  have hsupport_jensen :
      f (a • x + b • y) ≤
        ((a * withTopRealPart f x + b * withTopRealPart f y : ℝ) : WithTop ℝ) := by
    rw [show f (a • x + b • y) = supportFunctionCompWithTop Λ fs (a • x + b • y) by rfl,
      supportFunctionCompWithTop, pointwiseSupremumOn_apply]
    refine csSup_le ?_ ?_
    · rcases hΛ_nonempty with ⟨lam, hlamΛ⟩
      exact ⟨((inner ℝ lam (vectorMap fs (a • x + b • y)) : ℝ) : WithTop ℝ), ⟨lam, hlamΛ, rfl⟩⟩
    · rintro _ ⟨lam, hlamΛ, rfl⟩
      have hlam_nonneg : ∀ i, 0 ≤ lam i := by
        intro i
        have horth : lam ∈ ℝ₊^m := hΛ_nonneg hlamΛ
        simpa [EuclideanSpace.mem_nonnegativeOrthant_iff] using horth i
      have hx_slice :
          inner ℝ lam (vectorMap fs x) ≤ withTopRealPart f x := by
        have hx_slice_top :
            ((inner ℝ lam (vectorMap fs x) : ℝ) : WithTop ℝ) ≤ f x := by
          rw [show f x = supportFunctionCompWithTop Λ fs x by rfl, supportFunctionCompWithTop,
            pointwiseSupremumOn_apply]
          exact le_csSup (by exact ⟨⊤, fun _ _ ↦ le_top⟩) ⟨lam, hlamΛ, rfl⟩
        exact (le_withTopRealPart_iff (f := f) (x := x) hxdom).mpr hx_slice_top
      have hy_slice :
          inner ℝ lam (vectorMap fs y) ≤ withTopRealPart f y := by
        have hy_slice_top :
            ((inner ℝ lam (vectorMap fs y) : ℝ) : WithTop ℝ) ≤ f y := by
          rw [show f y = supportFunctionCompWithTop Λ fs y by rfl, supportFunctionCompWithTop,
            pointwiseSupremumOn_apply]
          exact le_csSup (by exact ⟨⊤, fun _ _ ↦ le_top⟩) ⟨lam, hlamΛ, rfl⟩
        exact (le_withTopRealPart_iff (f := f) (x := y) hydom).mpr hy_slice_top
      have hslice_convex :
          inner ℝ lam (vectorMap fs (a • x + b • y)) ≤
            a * inner ℝ lam (vectorMap fs x) + b * inner ℝ lam (vectorMap fs y) := by
        have hinner_eq :
            ∀ z : E, inner ℝ lam (vectorMap fs z) = ∑ i, lam i * fs i z := by
          intro z
          rw [PiLp.inner_apply]
          refine Finset.sum_congr rfl ?_
          intro i hi
          change (vectorMap fs z i) * lam i = lam i * fs i z
          simp
          ring
        have hsum :
            ∑ i, lam i * fs i (a • x + b • y) ≤
              ∑ i, lam i * (a * fs i x + b * fs i y) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          exact
            mul_le_mul_of_nonneg_left
              ((hfs_convex i).2 (by simp) (by simp) ha hb hab) (hlam_nonneg i)
        calc
          inner ℝ lam (vectorMap fs (a • x + b • y))
              = ∑ i, lam i * fs i (a • x + b • y) := hinner_eq _
          _ ≤ ∑ i, lam i * (a * fs i x + b * fs i y) := hsum
          _ = a * inner ℝ lam (vectorMap fs x) + b * inner ℝ lam (vectorMap fs y) := by
            calc
              ∑ i, lam i * (a * fs i x + b * fs i y)
                  = ∑ i, (a * (lam i * fs i x) + b * (lam i * fs i y)) := by
                      refine Finset.sum_congr rfl ?_
                      intro i hi
                      ring
              _ = ∑ i, a * (lam i * fs i x) + ∑ i, b * (lam i * fs i y) := by
                    rw [Finset.sum_add_distrib]
              _ = a * ∑ i, lam i * fs i x + b * ∑ i, lam i * fs i y := by
                    rw [← Finset.mul_sum, ← Finset.mul_sum]
              _ = a * inner ℝ lam (vectorMap fs x) + b * inner ℝ lam (vectorMap fs y) := by
                    rw [hinner_eq, hinner_eq]
      have hslice_bound :
          inner ℝ lam (vectorMap fs (a • x + b • y)) ≤
            a * withTopRealPart f x + b * withTopRealPart f y := by
        have hx_scaled :
            a * inner ℝ lam (vectorMap fs x) ≤ a * withTopRealPart f x :=
          mul_le_mul_of_nonneg_left hx_slice ha
        have hy_scaled :
            b * inner ℝ lam (vectorMap fs y) ≤ b * withTopRealPart f y :=
          mul_le_mul_of_nonneg_left hy_slice hb
        linarith
      change
        ((inner ℝ lam (vectorMap fs (a • x + b • y)) : ℝ) : WithTop ℝ) ≤
          ((a * withTopRealPart f x + b * withTopRealPart f y : ℝ) : WithTop ℝ)
      exact_mod_cast hslice_bound
  exact (withTopRealPart_le_iff (f := f) (x := a • x + b • y) hzdom).mpr hsupport_jensen

/-- Helper for Lemma 3.1.16: the active multiplier face is nonempty because a compact support
slice attains its maximum. -/
private theorem activeSupportFunctionMultipliers_nonempty
    {Λ : Set Eₘ} {fs : Fin m → E → ℝ}
    (hΛ_nonempty : Λ.Nonempty) (hΛ_compact : IsCompact Λ) (x : E) :
    (activeSupportFunctionMultipliers Λ fs x).Nonempty := by
  let φ : Eₘ → ℝ := fun lam ↦ inner ℝ lam (vectorMap fs x)
  -- A continuous linear slice attains its maximum on the compact multiplier set.
  obtain ⟨lam, hlam, hlammax⟩ :=
    hΛ_compact.exists_isMaxOn hΛ_nonempty <| by
      change ContinuousOn φ Λ
      simpa [φ] using ((continuous_id).inner continuous_const).continuousOn
  refine ⟨lam, ?_⟩
  rw [mem_activeSupportFunctionMultipliers_iff]
  refine ⟨hlam, ?_⟩
  -- The attained maximum is exactly the supremum value defining the support bridge.
  have hgreat :
      IsGreatest
        ((fun lam ↦ (φ lam : WithTop ℝ)) '' Λ)
        ((φ lam : ℝ) : WithTop ℝ) := by
    refine ⟨?_, ?_⟩
    · exact ⟨lam, hlam, rfl⟩
    · rintro _ ⟨mu, hmu, rfl⟩
      have hle : φ mu ≤ φ lam := (isMaxOn_iff.mp hlammax) mu hmu
      have hle' : (φ mu : WithTop ℝ) ≤ (φ lam : WithTop ℝ) := by
        exact_mod_cast hle
      simpa [φ] using hle'
  simpa [supportFunctionCompWithTop, pointwiseSupremumOn_apply, φ] using
    (IsGreatest.csSup_eq hgreat).symm

/-- Helper for Lemma 3.1.16: the active multiplier face is compact as the intersection of the
compact multiplier set with a closed level set of the support slice. -/
private theorem activeSupportFunctionMultipliers_isCompact
    {Λ : Set Eₘ} {fs : Fin m → E → ℝ}
    (hΛ_nonempty : Λ.Nonempty) (hΛ_compact : IsCompact Λ) (x : E) :
    IsCompact (activeSupportFunctionMultipliers Λ fs x) := by
  let c : ℝ := withTopRealPart (supportFunctionCompWithTop Λ fs) x
  have hxdom :
      x ∈ dom (supportFunctionCompWithTop Λ fs) :=
    supportFunctionCompWithTop_mem_dom_of_nonempty_compact hΛ_nonempty hΛ_compact x
  have hrewrite :
      activeSupportFunctionMultipliers Λ fs x =
        Λ ∩ {lam | inner ℝ lam (vectorMap fs x) = c} := by
    ext lam
    constructor
    · intro hlam
      rcases hlam with ⟨hlamΛ, hlamEq⟩
      refine ⟨hlamΛ, ?_⟩
      have hlamEq' :
          ((inner ℝ lam (vectorMap fs x) : ℝ) : WithTop ℝ) = ((c : ℝ) : WithTop ℝ) := by
        simpa [c] using hlamEq.trans (coe_withTopRealPart (f := supportFunctionCompWithTop Λ fs) hxdom).symm
      exact WithTop.coe_injective hlamEq'
    · intro hlam
      rcases hlam with ⟨hlamΛ, hlamEq⟩
      refine ⟨hlamΛ, ?_⟩
      have hlamEq' :
          ((inner ℝ lam (vectorMap fs x) : ℝ) : WithTop ℝ) = ((c : ℝ) : WithTop ℝ) := by
        exact_mod_cast hlamEq
      calc
        ((inner ℝ lam (vectorMap fs x) : ℝ) : WithTop ℝ) = ((c : ℝ) : WithTop ℝ) := hlamEq'
        _ = supportFunctionCompWithTop Λ fs x := by
          calc
            ((c : ℝ) : WithTop ℝ) =
                ((withTopRealPart (supportFunctionCompWithTop Λ fs) x : ℝ) : WithTop ℝ) := by
                  simp [c]
            _ = supportFunctionCompWithTop Λ fs x :=
              coe_withTopRealPart (f := supportFunctionCompWithTop Λ fs) hxdom
  rw [hrewrite]
  -- The active face is the compact multiplier set intersected with a closed affine level set.
  refine hΛ_compact.inter_right ?_
  exact isClosed_eq
    (by
      simpa [c] using
        (((continuous_id).inner continuous_const) : Continuous fun lam : Eₘ ↦ inner ℝ lam (vectorMap fs x)))
    continuous_const

/-- Helper for Lemma 3.1.16: the active multiplier face is convex because it is a level face of
the linear support slice. -/
private theorem activeSupportFunctionMultipliers_convex
    {Λ : Set Eₘ} {fs : Fin m → E → ℝ}
    (hΛ_convex : Convex ℝ Λ) (x : E) :
    Convex ℝ (activeSupportFunctionMultipliers Λ fs x) := by
  rw [convex_iff_add_mem]
  intro lam hlam mu hmu a b ha hb hab
  rw [mem_activeSupportFunctionMultipliers_iff] at hlam hmu ⊢
  refine ⟨(convex_iff_add_mem.mp hΛ_convex) hlam.1 hmu.1 ha hb hab, ?_⟩
  have hinner_eq : inner ℝ lam (vectorMap fs x) = inner ℝ mu (vectorMap fs x) := by
    simpa using (hlam.2.trans hmu.2.symm)
  -- Two active multipliers share the same support value, so every convex combination stays active.
  calc
    (inner ℝ (a • lam + b • mu) (vectorMap fs x) : WithTop ℝ)
        = (((a + b) * inner ℝ lam (vectorMap fs x) : ℝ) : WithTop ℝ) := by
            simp [inner_add_left, inner_smul_left, hinner_eq, add_mul]
    _ = (inner ℝ lam (vectorMap fs x) : WithTop ℝ) := by
      simp [hab]
    _ = supportFunctionCompWithTop Λ fs x := hlam.2

/-- Helper for Lemma 3.1.16: the weighted-gradient map is linear in the multiplier variable. -/
private theorem weightedGradientCombination_isLinear
    (fs : Fin m → E → ℝ) (x : E) :
    IsLinearMap ℝ (weightedGradientCombination fs x) := by
  refine ⟨?_, ?_⟩
  · intro a b
    -- Expand the defining sum coordinatewise to expose additivity.
    unfold weightedGradientCombination
    change ∑ i, (((a i + b i) : ℝ) • ∇ (fs i) x) = _
    simp [Finset.sum_add_distrib, add_smul]
  · intro c a
    -- Scalar multiplication also acts coordinatewise on the multiplier variable.
    unfold weightedGradientCombination
    change ∑ i, ((c * a i : ℝ) • ∇ (fs i) x) = _
    simp [Finset.smul_sum, mul_smul]

/-- Helper for Lemma 3.1.16: every active multiplier yields a subgradient of the support-function
composition. -/
private theorem weightedGradientCombination_mem_subdifferential_of_mem_activeSupportFunctionMultipliers
    {Λ : Set Eₘ} {fs : Fin m → E → ℝ}
    (hΛ_nonneg : Λ ⊆ ℝ₊^m)
    (hfs_convex : ∀ i, ConvexOn ℝ Set.univ (fs i))
    {x : E} (hfs_grad : ∀ i, HasGradientAt (fs i) (∇ (fs i) x) x)
    {lam : Eₘ}
    (hlam : lam ∈ activeSupportFunctionMultipliers Λ fs x) :
    weightedGradientCombination fs x lam ∈
      ∂ (supportFunctionCompWithTop Λ fs)(x) := by
  rcases mem_activeSupportFunctionMultipliers_iff.mp hlam with ⟨hlamΛ, hlamActive⟩
  refine mem_subdifferential_iff.mpr ?_
  constructor
  · -- Activity identifies the base-point value with a finite real support slice.
    rw [mem_withTopEffectiveDomain_iff, ← hlamActive]
    simp
  · intro y hy
    have hlam_nonneg : ∀ i, 0 ≤ lam i := by
      intro i
      have horth : lam ∈ ℝ₊^m := hΛ_nonneg hlamΛ
      simpa [EuclideanSpace.mem_nonnegativeOrthant_iff] using horth i
    have hcomponent :
        ∀ i, fs i y ≥ fs i x + inner ℝ (∇ (fs i) x) (y - x) := by
      intro i
      have hdom_i :
          dom (fun z ↦ (fs i z : WithTop ℝ)) = Set.univ := by
        ext z
        simp [withTopEffectiveDomain]
      have hconv_i :
          ConvexOn ℝ (dom (fun z ↦ (fs i z : WithTop ℝ)))
            (withTopRealPart (fun z ↦ (fs i z : WithTop ℝ))) := by
        simpa [hdom_i, withTopRealPart] using (hfs_convex i)
      have hxint :
          x ∈ interior (dom (fun z ↦ (fs i z : WithTop ℝ))) := by
        simp [hdom_i]
      have hydom :
          y ∈ dom (fun z ↦ (fs i z : WithTop ℝ)) := by
        simp [hdom_i]
      simpa [withTopRealPart] using
        gradient_support_inequality_of_hasGradientAt
          (f := fun z ↦ (fs i z : WithTop ℝ))
          hconv_i hxint (g := ∇ (fs i) x) (hfs_grad i) hydom
    have hsum :
        ∑ i, lam i * (fs i x + inner ℝ (∇ (fs i) x) (y - x)) ≤
          ∑ i, lam i * fs i y := by
      refine Finset.sum_le_sum ?_
      intro i hi
      exact mul_le_mul_of_nonneg_left (hcomponent i) (hlam_nonneg i)
    have hsum' :
        (((∑ i, lam i * (fs i x + inner ℝ (∇ (fs i) x) (y - x)) : ℝ)) : WithTop ℝ) ≤
          (((∑ i, lam i * fs i y : ℝ)) : WithTop ℝ) := by
      exact_mod_cast hsum
    have hySlice :
        ((inner ℝ lam (vectorMap fs y) : ℝ) : WithTop ℝ) ≤
          supportFunctionCompWithTop Λ fs y := by
      rw [supportFunctionCompWithTop, pointwiseSupremumOn_apply]
      refine le_csSup ?_ ?_
      · exact ⟨⊤, fun _ _ ↦ le_top⟩
      · exact ⟨lam, hlamΛ, rfl⟩
    have hsumEq :
        ∑ i, lam i * (fs i x + inner ℝ (∇ (fs i) x) (y - x)) =
          inner ℝ lam (vectorMap fs x) +
            inner ℝ (weightedGradientCombination fs x lam) (y - x) := by
      rw [inner_vectorMap_eq_sum, inner_weightedGradientCombination]
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
    -- Compare the support value at `y` with the active slice at `x` plus the summed
    -- first-order lower bound of the components.
    calc
      supportFunctionCompWithTop Λ fs y
          ≥ ((inner ℝ lam (vectorMap fs y) : ℝ) : WithTop ℝ) := hySlice
      _ = (((∑ i, lam i * fs i y : ℝ)) : WithTop ℝ) := by
        rw [inner_vectorMap_eq_sum]
      _ ≥ (((∑ i, lam i * (fs i x + inner ℝ (∇ (fs i) x) (y - x)) : ℝ)) : WithTop ℝ) := hsum'
      _ =
          (((inner ℝ lam (vectorMap fs x) +
            inner ℝ (weightedGradientCombination fs x lam) (y - x) : ℝ)) : WithTop ℝ) := by
              rw [hsumEq]
      _ =
          supportFunctionCompWithTop Λ fs x +
            (inner ℝ (weightedGradientCombination fs x lam) (y - x) : WithTop ℝ) := by
              rw [← hlamActive, WithTop.coe_add]

/-- Helper for Lemma 3.1.16: activity at `x + α • h` turns the support-function secant quotient
into an upper bound by the corresponding weighted sum of the component secant quotients. -/
private theorem active_multiplier_secant_quotient_le_weighted_component_secant
    {Λ : Set Eₘ} {fs : Fin m → E → ℝ}
    (hΛ_nonempty : Λ.Nonempty) (hΛ_compact : IsCompact Λ)
    {x h : E} {α : ℝ} (hα : 0 < α) {lam : Eₘ}
    (hlam : lam ∈ activeSupportFunctionMultipliers Λ fs (x + α • h)) :
    (withTopRealPart (supportFunctionCompWithTop Λ fs) (x + α • h) -
        withTopRealPart (supportFunctionCompWithTop Λ fs) x) / α ≤
      ∑ i, lam i * ((fs i (x + α • h) - fs i x) / α) := by
  let f : E → WithTop ℝ := supportFunctionCompWithTop Λ fs
  have hxdom : x ∈ dom f := by
    simpa [f] using
      supportFunctionCompWithTop_mem_dom_of_nonempty_compact
        (Λ := Λ) (fs := fs) hΛ_nonempty hΛ_compact x
  have hxαdom : x + α • h ∈ dom f := by
    simpa [f] using
      supportFunctionCompWithTop_mem_dom_of_nonempty_compact
        (Λ := Λ) (fs := fs) hΛ_nonempty hΛ_compact (x + α • h)
  rcases mem_activeSupportFunctionMultipliers_iff.mp hlam with ⟨hlamΛ, hlamActive⟩
  have hx_slice :
      inner ℝ lam (vectorMap fs x) ≤ withTopRealPart f x := by
    have hx_slice_top :
        ((inner ℝ lam (vectorMap fs x) : ℝ) : WithTop ℝ) ≤ f x := by
      rw [show f x = supportFunctionCompWithTop Λ fs x by rfl, supportFunctionCompWithTop,
        pointwiseSupremumOn_apply]
      exact le_csSup (by exact ⟨⊤, fun _ _ ↦ le_top⟩)
        ⟨lam, hlamΛ, rfl⟩
    exact (le_withTopRealPart_iff (f := f) (x := x) hxdom).mpr hx_slice_top
  have hxα_eq :
      withTopRealPart f (x + α • h) = inner ℝ lam (vectorMap fs (x + α • h)) := by
    have hxα_eq_top :
        ((withTopRealPart f (x + α • h) : ℝ) : WithTop ℝ) =
          ((inner ℝ lam (vectorMap fs (x + α • h)) : ℝ) : WithTop ℝ) := by
      calc
        ((withTopRealPart f (x + α • h) : ℝ) : WithTop ℝ)
            = f (x + α • h) := coe_withTopRealPart (f := f) hxαdom
        _ = supportFunctionCompWithTop Λ fs (x + α • h) := by rfl
        _ = ((inner ℝ lam (vectorMap fs (x + α • h)) : ℝ) : WithTop ℝ) := hlamActive.symm
    exact WithTop.coe_injective hxα_eq_top
  have hsecant :
      withTopRealPart f (x + α • h) - withTopRealPart f x ≤
        ∑ i, lam i * (fs i (x + α • h) - fs i x) := by
    calc
      withTopRealPart f (x + α • h) - withTopRealPart f x
          = inner ℝ lam (vectorMap fs (x + α • h)) - withTopRealPart f x := by
              rw [hxα_eq]
      _ ≤ inner ℝ lam (vectorMap fs (x + α • h)) - inner ℝ lam (vectorMap fs x) := by
            linarith
      _ = ∑ i, lam i * (fs i (x + α • h) - fs i x) := by
            rw [inner_vectorMap_eq_sum, inner_vectorMap_eq_sum, ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
  apply (div_le_iff₀ hα).2
  have hscaled :
      withTopRealPart f (x + α • h) - withTopRealPart f x ≤
        α * ∑ i, lam i * ((fs i (x + α • h) - fs i x) / α) := by
    calc
      withTopRealPart f (x + α • h) - withTopRealPart f x
          ≤ ∑ i, lam i * (fs i (x + α • h) - fs i x) := hsecant
      _ = α * ∑ i, lam i * ((fs i (x + α • h) - fs i x) / α) := by
            calc
              ∑ i, lam i * (fs i (x + α • h) - fs i x)
                  = ∑ i, α * (lam i * ((fs i (x + α • h) - fs i x) / α)) := by
                      refine Finset.sum_congr rfl ?_
                      intro i hi
                      field_simp [hα.ne']
              _ = α * ∑ i, lam i * ((fs i (x + α • h) - fs i x) / α) := by
                    exact
                      (Finset.mul_sum Finset.univ
                        (fun i : Fin m ↦ lam i * ((fs i (x + α • h) - fs i x) / α)) α).symm
  simpa [mul_comm] using hscaled

-- The remaining work is the reverse inclusion `∂f(x) ⊆ image(active multipliers)`.
 /-- Helper for Lemma 3.1.16: a limit of multipliers that stay active along a convergent point
 sequence remains active at the limit point. -/
private theorem mem_activeSupportFunctionMultipliers_of_tendsto
    {Λ : Set Eₘ} {fs : Fin m → E → ℝ} {x : E}
    (hΛ_compact : IsCompact Λ)
    {xSeq : ℕ → E} {lamSeq : ℕ → Eₘ} {lamStar : Eₘ}
    (hxSeq : Filter.Tendsto xSeq Filter.atTop (nhds x))
    (hlamSeq : Filter.Tendsto lamSeq Filter.atTop (nhds lamStar))
    (hactive : ∀ n, lamSeq n ∈ activeSupportFunctionMultipliers Λ fs (xSeq n))
    (hfs_cont : ∀ i, ContinuousAt (fs i) x) :
    lamStar ∈ activeSupportFunctionMultipliers Λ fs x := by
  let e : Eₘ ≃ₜ (Fin m → ℝ) := (EuclideanSpace.equiv (Fin m) ℝ).toHomeomorph
  have hlamStar_mem : lamStar ∈ Λ := by
    refine hΛ_compact.isClosed.mem_of_tendsto hlamSeq ?_
    exact Filter.Eventually.of_forall fun n ↦
      (mem_activeSupportFunctionMultipliers_iff.mp (hactive n)).1
  have hvector_tendsto :
      Filter.Tendsto (fun n ↦ vectorMap fs (xSeq n)) Filter.atTop (nhds (vectorMap fs x)) := by
    have hpi :
        Filter.Tendsto
          (fun n ↦ e (vectorMap fs (xSeq n)))
          Filter.atTop
          (nhds (e (vectorMap fs x))) := by
      simpa [e, vectorMap_apply] using
        (tendsto_pi_nhds.mpr fun i ↦ (hfs_cont i).tendsto.comp hxSeq)
    simpa [e] using e.symm.continuous.tendsto (e (vectorMap fs x)) |>.comp hpi
  have hactive_value_tendsto :
      Filter.Tendsto
        (fun n ↦ inner ℝ (lamSeq n) (vectorMap fs (xSeq n)))
        Filter.atTop
        (nhds (inner ℝ lamStar (vectorMap fs x))) :=
    hlamSeq.inner hvector_tendsto
  rw [mem_activeSupportFunctionMultipliers_iff]
  refine ⟨hlamStar_mem, ?_⟩
  -- Compare every fixed multiplier slice with the active slice along the sequence and pass to the
  -- limit to recover maximality at `x`.
  have hmax :
      ∀ μ ∈ Λ, inner ℝ μ (vectorMap fs x) ≤ inner ℝ lamStar (vectorMap fs x) := by
    intro μ hμΛ
    have hμ_tendsto :
        Filter.Tendsto
          (fun n ↦ inner ℝ μ (vectorMap fs (xSeq n)))
          Filter.atTop
          (nhds (inner ℝ μ (vectorMap fs x))) :=
      Filter.Tendsto.inner tendsto_const_nhds hvector_tendsto
    have hμ_le :
        ∀ᶠ n : ℕ in Filter.atTop,
          inner ℝ μ (vectorMap fs (xSeq n)) ≤
            inner ℝ (lamSeq n) (vectorMap fs (xSeq n)) := by
      refine Filter.Eventually.of_forall ?_
      intro n
      rcases mem_activeSupportFunctionMultipliers_iff.mp (hactive n) with ⟨_, hEq⟩
      have hslice :
          ((inner ℝ μ (vectorMap fs (xSeq n)) : ℝ) : WithTop ℝ) ≤
            supportFunctionCompWithTop Λ fs (xSeq n) := by
        rw [supportFunctionCompWithTop, pointwiseSupremumOn_apply]
        exact le_csSup (by exact ⟨⊤, fun _ _ ↦ le_top⟩) ⟨μ, hμΛ, rfl⟩
      rw [← hEq] at hslice
      exact_mod_cast hslice
    exact le_of_tendsto_of_tendsto hμ_tendsto hactive_value_tendsto hμ_le
  have hslice_le :
      ((inner ℝ lamStar (vectorMap fs x) : ℝ) : WithTop ℝ) ≤
        supportFunctionCompWithTop Λ fs x := by
    rw [supportFunctionCompWithTop, pointwiseSupremumOn_apply]
    exact le_csSup (by exact ⟨⊤, fun _ _ ↦ le_top⟩) ⟨lamStar, hlamStar_mem, rfl⟩
  have hsupp_le :
      supportFunctionCompWithTop Λ fs x ≤
        ((inner ℝ lamStar (vectorMap fs x) : ℝ) : WithTop ℝ) := by
    rw [supportFunctionCompWithTop, pointwiseSupremumOn_apply]
    refine csSup_le ?_ ?_
    · exact ⟨_, ⟨lamStar, hlamStar_mem, rfl⟩⟩
    rintro _ ⟨μ, hμΛ, rfl⟩
    change ((inner ℝ μ (vectorMap fs x) : ℝ) : WithTop ℝ) ≤
      ((inner ℝ lamStar (vectorMap fs x) : ℝ) : WithTop ℝ)
    exact_mod_cast hmax μ hμΛ
  exact le_antisymm hslice_le hsupp_le

/-- Helper for Lemma 3.1.16: every subgradient pairing is bounded by the support function of the
active weighted-gradient image. -/
private theorem subgradient_pairing_le_supportFunction_activeImage
    {Λ : Set Eₘ} {fs : Fin m → E → ℝ}
    (hΛ_nonempty : Λ.Nonempty) (hΛ_compact : IsCompact Λ)
    {x : E} (hfs_grad : ∀ i, HasGradientAt (fs i) (∇ (fs i) x) x)
    {g : E}
    (hg : g ∈ ∂ (supportFunctionCompWithTop Λ fs)(x))
    (h : E) :
    (((inner ℝ g h : ℝ)) : EReal) ≤
      ξ[(weightedGradientCombination fs x) '' activeSupportFunctionMultipliers Λ fs x] h := by
  classical
  let a : ℕ → ℝ := fun n ↦ ((n : ℝ) + 1)⁻¹
  have ha_pos : ∀ n, 0 < a n := by
    intro n
    dsimp [a]
    apply inv_pos.mpr
    have hsucc : 0 < n + 1 := Nat.succ_pos n
    exact_mod_cast hsucc
  have ha_tendsto : Filter.Tendsto a Filter.atTop (nhds (0 : ℝ)) := by
    simpa [a] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  let xSeq : ℕ → E := fun n ↦ x + a n • h
  have hxSeq_tendsto : Filter.Tendsto xSeq Filter.atTop (nhds x) := by
    have hsmul :
        Filter.Tendsto (fun n ↦ a n • h) Filter.atTop (nhds ((0 : ℝ) • h)) :=
      Filter.Tendsto.smul_const ha_tendsto h
    simpa [xSeq] using Filter.Tendsto.add tendsto_const_nhds hsmul
  have hface_nonempty :
      ∀ n, (activeSupportFunctionMultipliers Λ fs (xSeq n)).Nonempty :=
    fun n ↦ activeSupportFunctionMultipliers_nonempty
      (Λ := Λ) (fs := fs) hΛ_nonempty hΛ_compact (xSeq n)
  choose lam hlam using hface_nonempty
  have hlam_mem : ∀ n, lam n ∈ Λ := by
    intro n
    exact (mem_activeSupportFunctionMultipliers_iff.mp (hlam n)).1
  obtain ⟨lamStar, hlamStar_mem, φ, hφmono, hlam_tendsto⟩ :=
    hΛ_compact.tendsto_subseq hlam_mem
  have hxSeq_sub_tendsto :
      Filter.Tendsto (xSeq ∘ φ) Filter.atTop (nhds x) :=
    hxSeq_tendsto.comp hφmono.tendsto_atTop
  have hlamStar_active :
      lamStar ∈ activeSupportFunctionMultipliers Λ fs x :=
    mem_activeSupportFunctionMultipliers_of_tendsto
      (Λ := Λ) (fs := fs) (x := x) hΛ_compact
      hxSeq_sub_tendsto hlam_tendsto
      (fun n ↦ hlam (φ n))
      (fun i ↦ (hfs_grad i).continuousAt)
  let f : E → WithTop ℝ := supportFunctionCompWithTop Λ fs
  have hsub := mem_subdifferential_iff.mp hg
  have hxdom : x ∈ dom f := by
    simpa [f] using hsub.1
  have hlower :
      ∀ n,
        inner ℝ g h ≤
          (withTopRealPart f (xSeq (φ n)) - withTopRealPart f x) / a (φ n) := by
    intro n
    have hdom_n : xSeq (φ n) ∈ dom f := by
      simpa [f, xSeq] using
        supportFunctionCompWithTop_mem_dom_of_nonempty_compact
          (Λ := Λ) (fs := fs) hΛ_nonempty hΛ_compact (xSeq (φ n))
    have hineq :
        f (xSeq (φ n)) ≥ f x + (inner ℝ g (xSeq (φ n) - x) : WithTop ℝ) :=
      hsub.2 hdom_n
    rw [← coe_withTopRealPart (f := f) hdom_n, ← coe_withTopRealPart (f := f) hxdom] at hineq
    have hreal :
        withTopRealPart f (xSeq (φ n)) ≥
          withTopRealPart f x + a (φ n) * inner ℝ g h := by
      have hreal' :
          withTopRealPart f x + inner ℝ g (xSeq (φ n) - x) ≤
            withTopRealPart f (xSeq (φ n)) := by
        exact_mod_cast hineq
      have hsubeq : xSeq (φ n) - x = a (φ n) • h := by
        simp [xSeq]
      simpa [hsubeq, real_inner_smul_right] using hreal'
    exact (le_div_iff₀ (ha_pos (φ n))).2 (by linarith)
  have hupper :
      ∀ n,
        (withTopRealPart f (xSeq (φ n)) - withTopRealPart f x) / a (φ n) ≤
          ∑ i, lam (φ n) i * ((fs i (xSeq (φ n)) - fs i x) / a (φ n)) := by
    intro n
    simpa [f, xSeq] using
      active_multiplier_secant_quotient_le_weighted_component_secant
        (Λ := Λ) (fs := fs) hΛ_nonempty hΛ_compact
        (x := x) (h := h) (α := a (φ n)) (ha_pos (φ n)) (hlam (φ n))
  have hpair_seq :
      ∀ n,
        inner ℝ g h ≤
          ∑ i, lam (φ n) i * ((fs i (xSeq (φ n)) - fs i x) / a (φ n)) := by
    intro n
    exact (hlower n).trans (hupper n)
  have hlam_coord :
      ∀ i, Filter.Tendsto (fun n ↦ lam (φ n) i) Filter.atTop (nhds (lamStar i)) := by
    intro i
    let e : Eₘ ≃ₜ (Fin m → ℝ) := (EuclideanSpace.equiv (Fin m) ℝ).toHomeomorph
    have hlamPi :
        Filter.Tendsto (fun n ↦ e (lam (φ n))) Filter.atTop (nhds (e lamStar)) :=
      (e.continuous.tendsto lamStar).comp hlam_tendsto
    simpa [e] using (tendsto_pi_nhds.mp hlamPi i)
  have hsecant_coord :
      ∀ i,
        Filter.Tendsto
          (fun n ↦ ((fs i (xSeq (φ n)) - fs i x) / a (φ n)))
          Filter.atTop
          (nhds (inner ℝ (∇ (fs i) x) h)) := by
    intro i
    let fi : ℝ → ℝ := fun t ↦ fs i (x + t • h)
    have hline :
        HasDerivAt fi (inner ℝ (∇ (fs i) x) h) 0 := by
      have hlineMap :
          HasFDerivAt (fun t : ℝ ↦ x + t • h)
            ((1 : ℝ →L[ℝ] ℝ).smulRight h) 0 := by
        simpa using
          (HasFDerivAt.const_add x
            (HasFDerivAt.smul_const (hasFDerivAt_id (𝕜 := ℝ) (E := ℝ) 0) h))
      have hcompBase :
          HasFDerivAt (fs i)
            ((InnerProductSpace.toDual ℝ E) (∇ (fs i) x))
            (x + (0 : ℝ) • h) := by
        simpa using (hfs_grad i).hasFDerivAt
      have hcomp :
          HasFDerivAt fi
            (((InnerProductSpace.toDual ℝ E) (∇ (fs i) x)).comp
              ((1 : ℝ →L[ℝ] ℝ).smulRight h))
            0 := by
        exact HasFDerivAt.comp 0 hcompBase hlineMap
      simpa [fi, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply] using
        hcomp.hasDerivAt
    have hslope :
        Filter.Tendsto
          (fun t : ℝ ↦ (fi (0 + t) - fi 0) / t)
          (nhdsWithin 0 ({0}ᶜ))
          (nhds (inner ℝ (∇ (fs i) x) h)) := by
      simpa [fi, zero_add, div_eq_inv_mul, mul_comm, mul_left_comm, mul_assoc] using
        hline.tendsto_slope_zero
    have ha_subseq_within :
        Filter.Tendsto (fun n ↦ a (φ n)) Filter.atTop (nhdsWithin 0 ({0}ᶜ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        (fun n ↦ a (φ n))
        (ha_tendsto.comp hφmono.tendsto_atTop)
        ?_
      exact Filter.Eventually.of_forall fun n ↦ by
        have hne : a (φ n) ≠ 0 := (ha_pos (φ n)).ne'
        simpa using hne
    simpa [fi, xSeq, div_eq_inv_mul, mul_comm, mul_left_comm, mul_assoc] using
      hslope.comp ha_subseq_within
  have hsum_tendsto :
        Filter.Tendsto
          (fun n ↦ ∑ i, lam (φ n) i * ((fs i (xSeq (φ n)) - fs i x) / a (φ n)))
        Filter.atTop
        (nhds (∑ i, lamStar i * inner ℝ (∇ (fs i) x) h)) := by
    classical
    refine Finset.induction_on Finset.univ ?base ?step
    · simp
    · intro i s hi hs
      simpa [Finset.sum_insert hi] using
        (hlam_coord i).mul (hsecant_coord i) |>.add hs
  have hlimit_pair :
      inner ℝ g h ≤
        ∑ i, lamStar i * inner ℝ (∇ (fs i) x) h :=
    ge_of_tendsto hsum_tendsto (Filter.Eventually.of_forall hpair_seq)
  let Q : Set E :=
    (weightedGradientCombination fs x) '' activeSupportFunctionMultipliers Λ fs x
  have hQ_mem : weightedGradientCombination fs x lamStar ∈ Q := by
    exact ⟨lamStar, hlamStar_active, rfl⟩
  have hQ_support :
      (((inner ℝ (weightedGradientCombination fs x lamStar) h : ℝ)) : EReal) ≤ ξ[Q] h := by
    rw [supportFunction_apply]
    exact le_sSup ⟨weightedGradientCombination fs x lamStar, hQ_mem, rfl⟩
  have hpair_real :
      inner ℝ g h ≤ inner ℝ (weightedGradientCombination fs x lamStar) h := by
    simpa [inner_weightedGradientCombination] using hlimit_pair
  exact le_trans (by exact_mod_cast hpair_real) hQ_support

private theorem subdifferential_supportFunctionCompWithTop_subset_image_activeMultipliers
    {Λ : Set Eₘ} {fs : Fin m → E → ℝ}
    (hΛ_nonempty : Λ.Nonempty) (hΛ_compact : IsCompact Λ) (hΛ_convex : Convex ℝ Λ)
    (hΛ_nonneg : Λ ⊆ ℝ₊^m)
    (hfs_convex : ∀ i, ConvexOn ℝ Set.univ (fs i))
    (x : E) (hfs_grad : ∀ i, HasGradientAt (fs i) (∇ (fs i) x) x) :
    ∂ (supportFunctionCompWithTop Λ fs)(x) ⊆
      (weightedGradientCombination fs x) '' activeSupportFunctionMultipliers Λ fs x := by
  -- Route correction: the forward inclusion is already proved directly, so the remaining task is
  -- the source-faithful reverse inclusion by support-function comparison.
  have _hf_convex :
      ConvexOn ℝ (dom (supportFunctionCompWithTop Λ fs))
        (withTopRealPart (supportFunctionCompWithTop Λ fs)) :=
    convexOn_supportFunctionCompWithTop_of_nonempty_compact
      (Λ := Λ) (fs := fs) hΛ_nonempty hΛ_compact hΛ_nonneg hfs_convex
  have _hsecant :
      ∀ {h : E} {α : ℝ} (hα : 0 < α) {lam : Eₘ},
        lam ∈ activeSupportFunctionMultipliers Λ fs (x + α • h) →
          (withTopRealPart (supportFunctionCompWithTop Λ fs) (x + α • h) -
              withTopRealPart (supportFunctionCompWithTop Λ fs) x) / α ≤
            ∑ i, lam i * ((fs i (x + α • h) - fs i x) / α) :=
    fun {h} {α} hα {lam} hlam ↦
      active_multiplier_secant_quotient_le_weighted_component_secant
        (Λ := Λ) (fs := fs) hΛ_nonempty hΛ_compact hα hlam
  have _hface_nonempty :
      (activeSupportFunctionMultipliers Λ fs x).Nonempty :=
    activeSupportFunctionMultipliers_nonempty
      (Λ := Λ) (fs := fs) hΛ_nonempty hΛ_compact x
  have _hface_compact :
      IsCompact (activeSupportFunctionMultipliers Λ fs x) :=
    activeSupportFunctionMultipliers_isCompact
      (Λ := Λ) (fs := fs) hΛ_nonempty hΛ_compact x
  let Q : Set E :=
    (weightedGradientCombination fs x) '' activeSupportFunctionMultipliers Λ fs x
  have hQ_nonempty : Q.Nonempty := by
    rcases _hface_nonempty with ⟨lam, hlam⟩
    exact ⟨weightedGradientCombination fs x lam, ⟨lam, hlam, rfl⟩⟩
  have hmap_cont : Continuous (weightedGradientCombination fs x) := by
    -- The weighted-gradient map is linear in the multiplier variable, hence continuous on the
    -- finite-dimensional Euclidean multiplier space.
    let L : Eₘ →ₗ[ℝ] E :=
      { toFun := weightedGradientCombination fs x
        map_add' := (weightedGradientCombination_isLinear fs x).map_add
        map_smul' := (weightedGradientCombination_isLinear fs x).map_smul }
    exact L.continuous_of_finiteDimensional
  have hQ_compact : IsCompact Q :=
    _hface_compact.image hmap_cont
  have hQ_convex : Convex ℝ Q :=
    (activeSupportFunctionMultipliers_convex (Λ := Λ) (fs := fs) hΛ_convex x).is_linear_image
      (weightedGradientCombination_isLinear fs x)
  intro g hg
  have hsingleton_subset : ({g} : Set E) ⊆ Q := by
    apply subset_of_supportFunction_le_on_domain ({g}) Q
      hQ_nonempty hQ_compact.isClosed hQ_convex
    intro y hy
    -- Route correction: compare the singleton support function with the active-image support
    -- function through the nearby-active-multiplier pairing bound.
    have hpair :
        (((inner ℝ g y : ℝ)) : EReal) ≤ ξ[Q] y :=
      subgradient_pairing_le_supportFunction_activeImage
        (Λ := Λ) (fs := fs) hΛ_nonempty hΛ_compact hfs_grad hg y
    simpa using hpair
  exact hsingleton_subset (by simp)

/-- Lemma 3.1.16 (2): when the support maxima over `Λ ⊆ ℝ_+^m` are attained, the subdifferential
of the thin `WithTop` bridge of the support-function composition `x ↦ ξ[Λ] (vectorMap fs x)` at
`x` is exactly the image of the active multiplier face under
`λ ↦ ∑ᵢ λ_i ∇ f_i(x)`. The support-function composition stays the source-facing owner, and
`supportFunctionCompWithTop Λ fs` is only the codomain bridge required by `∂`. -/
-- Proof sketch: view `supportFunctionCompWithTop Λ fs` as the generic pointwise supremum over the
-- linear slices `lam ↦ (inner ℝ lam (vectorMap fs x) : WithTop ℝ)`. Compactness and convexity of
-- `Λ` identify the subdifferential of that bridge with the active multiplier face, and the chain
-- rule for the coordinate map at the chosen point `x`, expressed through the owner witnesses
-- `HasGradientAt (fs i) (∇ (fs i) x) x`, sends each active `lam` to
-- `∑ i, lam i • ∇ (fs i) x`.
theorem subdifferential_supportFunction_comp_vectorMap_eq_image_activeMultipliers
    {Λ : Set Eₘ} {fs : Fin m → E → ℝ}
    (hΛ_nonempty : Λ.Nonempty) (hΛ_compact : IsCompact Λ) (hΛ_convex : Convex ℝ Λ)
    (hΛ_nonneg : Λ ⊆ ℝ₊^m)
    (hfs_convex : ∀ i, ConvexOn ℝ Set.univ (fs i))
    (x : E) (hfs_grad : ∀ i, HasGradientAt (fs i) (∇ (fs i) x) x) :
    ∂ (supportFunctionCompWithTop Λ fs)(x) =
      (weightedGradientCombination fs x) '' activeSupportFunctionMultipliers Λ fs x := by
  have hface_convex :
      Convex ℝ (activeSupportFunctionMultipliers Λ fs x) :=
    activeSupportFunctionMultipliers_convex (Λ := Λ) (fs := fs) hΛ_convex x
  have hmap_linear :
      IsLinearMap ℝ (weightedGradientCombination fs x) :=
    weightedGradientCombination_isLinear fs x
  have himage_subset :
      (weightedGradientCombination fs x) '' activeSupportFunctionMultipliers Λ fs x ⊆
        ∂ (supportFunctionCompWithTop Λ fs)(x) := by
    intro g hg
    rcases hg with ⟨lam, hlam, rfl⟩
    exact
      weightedGradientCombination_mem_subdifferential_of_mem_activeSupportFunctionMultipliers
        (Λ := Λ) (fs := fs) hΛ_nonneg hfs_convex hfs_grad hlam
  have hsubset :
      ∂ (supportFunctionCompWithTop Λ fs)(x) ⊆
        (weightedGradientCombination fs x) '' activeSupportFunctionMultipliers Λ fs x :=
    subdifferential_supportFunctionCompWithTop_subset_image_activeMultipliers
      (Λ := Λ) (fs := fs) hΛ_nonempty hΛ_compact hΛ_convex hΛ_nonneg hfs_convex x hfs_grad
  -- The theorem is now reduced to the two set inclusions.
  exact Set.Subset.antisymm hsubset himage_subset

end Gradient

end

/-! ### Theorem_3_1_16 (from Chap03) -/
noncomputable section

open scoped ConvexAnalysis WithTopConvexAnalysis

/- Theorem 3.1.16 is a recall-only Euclidean specialization in the chapter's
Fenchel-biconjugacy domain.

Primary domain:
- Fenchel conjugates, biduals, and subdifferentials of `ℝ ∪ {+∞}`-valued
  functions on `ℝⁿ`.

Relevant sampled declarations in this domain:
- `dom` and `withTopToEReal` in `Definition_3_3`, the chapter owners for the
  effective-domain / `EReal` bridge;
- `subdifferential` and the notation `∂ f(x)` in `Definition_3_1_5`, the
  chapter owner for extended-valued subgradients;
- `fenchelDual` and the notation `f⋆` in `Definition_3_1_2_1`, the
  source-facing Fenchel-dual owner;
- `fenchelBidual`, `fenchelBidual_le_of_mem_dom`,
  `subdifferential_subset_dom_fenchelDual`, and
  `fenchelBidual_eq_of_subdifferential_nonempty` in `Theorem_3_1_5_2`, the
  owner-level bidual surface.

Best owner abstraction:
- the existing source-facing owner surface `f⋆`, `f⋆⋆`, `dom f`, and `∂ f(x)`.

Primitive data:
- none in this file; the primitive domain, subdifferential, Fenchel-dual, and
  Fenchel-bidual data already live upstream.

Derived API:
- only the Euclidean `ℝⁿ` specialization of the three theorem clauses.

Source/core/bridge triage:
- source-facing: Theorem 3.1.16 as the textbook Euclidean specialization;
- core/canonical: `dom`, `subdifferential`, `fenchelDual`, and `fenchelBidual`;
- bridge/view: this recall-only specialization from the intrinsic owner layer
  to `EuclideanSpace ℝ (Fin n)`.

The previous file rebuilt local copies of the effective domain, finite real
part, subgradient predicate, subdifferential, Fenchel dual, and Fenchel bidual.
All of those notions are already owned upstream in the chapter. This refinement
deletes the duplicate wheels and recalls only the Euclidean specialization of
the canonical owner-level theorem surface.
-/

section

variable {n : ℕ}
variable {f : EuclideanSpace ℝ (Fin n) → WithTop ℝ}
variable {x : EuclideanSpace ℝ (Fin n)}

/- Theorem 3.1.16 (1): in the Euclidean specialization `E = EuclideanSpace ℝ (Fin n)`, the
Fenchel bidual is bounded above by the original value at every point of `dom f`. -/
#check
  (fenchelBidual_le_of_mem_dom :
    x ∈ dom f → (f⋆⋆) x ≤ withTopToEReal (f x))

/- Theorem 3.1.16 (2): in the Euclidean specialization `E = EuclideanSpace ℝ (Fin n)`, every
subgradient belongs to the effective domain of the Fenchel dual. -/
#check
  (subdifferential_subset_dom_fenchelDual :
    ∂ f(x) ⊆ dom (f⋆))

/- Theorem 3.1.16 (3): in the Euclidean specialization `E = EuclideanSpace ℝ (Fin n)`, nonempty
subdifferential implies Fenchel-bidual equality at `x`. -/
#check
  (fenchelBidual_eq_of_subdifferential_nonempty :
    (∂ f(x)).Nonempty → (f⋆⋆) x = withTopToEReal (f x))

end

end

/-! ### Lemma_3_1_17 (from Chap03) -/
noncomputable section

open scoped BigOperators Gradient Pointwise WithTopConvexAnalysis

universe u

variable {m : ℕ}

local notation "Y" => EuclideanSpace ℝ (Fin m)

/- Lemma 3.1.17 lies in the chapter's local convex-composition / constrained-subdifferential
chain-rule domain.

Sampled owner-style declarations:
- `vectorMap` in `Lemma_3_1_16`, the chapter's existing owner for the coordinate vector
  `x ↦ (f₁(x), ..., fₘ(x))`;
- `constrainedSubdifferential` in `Definition_3_1_5`, the earlier chapter owner for local
  subgradient inequalities on a feasible set;
- `subdifferentialWithin` in `Theorem_3_44`, the later real-valued bridge/view of the same local
  notion at feasible points;
- mathlib `Monotone` and `HasGradientAt` on the coordinatewise ordered product `Fin m → ℝ`;
- the canonical finite weighted set sum `∑ i, a i • S i`.

Best owner abstractions:
- source-facing: Lemma 3.1.17's convex-composition and subdifferential chain rule;
- core/canonical: `constrainedSubdifferential`, `vectorMap`, and the full-domain coordinatewise
  monotonicity owner `Monotone (F ∘ (EuclideanSpace.equiv (Fin m) ℝ).symm)` on `Fin m → ℝ`;
- bridge/view: the later `subdifferentialWithin` view.

Primitive data:
- the convex set `Q` in a real inner-product space `E`;
- the outer function `F : Y → ℝ`;
- the coordinate family `f : Fin m → E → ℝ`.

Derived API:
- convexity of `F ∘ vectorMap f`;
- the weighted constrained-subdifferential identity at interior points of `Q`.

This file therefore deletes the duplicate global subgradient formulation and keeps the statement at
the correct local owner layer. The public API now uses the earlier chapter owner
`constrainedSubdifferential`, the existing coordinate-vector owner `vectorMap`, and the canonical
full-domain coordinatewise monotonicity hypothesis
`Monotone (F ∘ (EuclideanSpace.equiv (Fin m) ℝ).symm)` on the product space `Fin m → ℝ`. The
textbook input model `ℝⁿ` is not essential for these owner statements, and neither is
finite-dimensionality of the input space `E`, so the file now grows from the intrinsic
inner-product-space layer already used by `constrainedSubdifferential` and `vectorMap`. The later
`subdifferentialWithin` view should be derived from this owner statement at feasible points rather
than maintained as a parallel root theorem here.
-/

section Convexity

variable {E : Type u} [AddCommMonoid E] [Module ℝ E]

/-- Lemma 3.1.17 (convexity part): if `F` is convex and coordinatewise monotone on `ℝ^m`, and
each component function `f i` is convex on the convex set `Q`, then the composition
`x ↦ F (f₁(x), ..., fₘ(x))` is convex on `Q`; coordinatewise monotonicity is recorded by the
canonical full-domain product-order hypothesis
`Monotone (F ∘ (EuclideanSpace.equiv (Fin m) ℝ).symm)` on `Fin m → ℝ`. -/
-- Proof sketch: combine convexity of each `f i` with coordinatewise monotonicity and convexity
-- of `F`.
theorem convexOn_comp_coordinatewiseMonotone
    {Q : Set E} (hQ_convex : Convex ℝ Q)
    {F : Y → ℝ} (hF_conv : ConvexOn ℝ Set.univ F)
    {f : Fin m → E → ℝ} (hf_conv : ∀ i, ConvexOn ℝ Q (f i))
    (hF_mono : Monotone (F ∘ (EuclideanSpace.equiv (Fin m) ℝ).symm)) :
    ConvexOn ℝ Q (F ∘ vectorMap f) := by
  refine ⟨hQ_convex, ?_⟩
  intro x hx y hy a b ha hb hab
  -- First compare the coordinate vector at the convex combination point componentwise.
  have hcoord :
      (EuclideanSpace.equiv (Fin m) ℝ) (vectorMap f (a • x + b • y)) ≤
        (EuclideanSpace.equiv (Fin m) ℝ) (a • vectorMap f x + b • vectorMap f y) := by
    intro i
    simpa [vectorMap_apply] using (hf_conv i).2 hx hy ha hb hab
  have hmono :
      F (vectorMap f (a • x + b • y)) ≤ F (a • vectorMap f x + b • vectorMap f y) :=
    by simpa using hF_mono hcoord
  -- Then use the convexity inequality for `F` at the two endpoint coordinate vectors.
  have houter :
      F (a • vectorMap f x + b • vectorMap f y) ≤
        a * F (vectorMap f x) + b * F (vectorMap f y) := by
    simpa [Function.comp] using hF_conv.2 (by simp) (by simp) ha hb hab
  exact hmono.trans houter

end Convexity

section Gradient

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Lemma 3.1.17 (subdifferential part): if `F` is convex and coordinatewise monotone on `ℝ^m`,
and each component function `f i` is convex on the convex set `Q`, then at every interior
feasible point `x ∈ interior Q` and for every gradient witness
`g = ∇F (f₁(x), ..., fₘ(x))`, the constrained subdifferential
`∂[Q] (fun y ↦ ((F ∘ vectorMap f) y : WithTop ℝ))(x)` equals the weighted sum
`∑ᵢ gᵢ • ∂[Q] (fun y ↦ (f i y : WithTop ℝ))(x)`. This keeps the owner notation `∂[Q]` on the
public theorem surface instead of unpacking it back to the raw set builder. -/
-- Proof sketch: compute the directional derivative of the composition using the pointwise
-- gradient witness `HasGradientAt F g (vectorMap f x)`, identify each directional
-- derivative of `f i` with its support function on
-- `∂[Q] (fun y ↦ (f i y : WithTop ℝ))(x)`, and then apply the
-- support-function characterization of convex sets from Corollary 3.1.5 inside the feasible set
-- `Q`.
theorem constrainedSubdifferential_comp_coordinatewiseMonotone_eq_weighted_sum
    {Q : Set E} (hQ_convex : Convex ℝ Q)
    {F : Y → ℝ} (hF_conv : ConvexOn ℝ Set.univ F)
    {f : Fin m → E → ℝ} (hf_conv : ∀ i, ConvexOn ℝ Q (f i))
    (hF_mono : Monotone (F ∘ (EuclideanSpace.equiv (Fin m) ℝ).symm))
    {x : E} (hx : x ∈ interior Q) {g : Y}
    (hF_grad : HasGradientAt F g (vectorMap f x)) :
    ∂[Q] (fun y ↦ ((F ∘ vectorMap f) y : WithTop ℝ))(x) =
      ∑ i : Fin m,
        (g i) • ∂[Q] (fun y ↦ (f i y : WithTop ℝ))(x) := by
  -- Route correction: the source proof finishes by identifying both sides through their support
  -- functions, but this file still lacks the owner-level bridge from constrained
  -- subdifferentials on `Q` to the corresponding within-set directional derivatives.
  --
  -- TODO: prove the constrained support-function bridge in this ambient owner language, then use
  -- the textbook chain-rule identity for directional derivatives together with Corollary 3.1.5.
  sorry

end Gradient

end

/-! ### Theorem_3_1_17 (from Chap03) -/
noncomputable section

open scoped WithTopConvexAnalysis

open scoped Topology

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Theorem 3.1.17 is a `bridge/view` Euclidean specialization in the chapter's convex
directional-derivative domain.

Primary domain:
- convex directional derivatives and subdifferentials of `ℝ ∪ {+∞}`-valued functions on `ℝⁿ`.

Relevant owner-style declarations sampled before refinement:
- `convexDirectionalDerivative` in `Theorem_3_21`, the chapter owner for the extended-valued
  directional derivative;
- `subdifferential_convexDirectionalDerivativeReal_at_zero_eq_subdifferential` in
  `Theorem_3_21`, the canonical subdifferential comparison theorem;
- `convexDirectionalDerivativeReal_isGreatest_subgradientPairing_of_mem_interior` in
  `Theorem_3_21`, the canonical max-formula theorem;
- `dom`, `withTopRealPart`, and `subdifferential` from `Definition_3_3` and `Definition_3_1_5`,
  which already own the effective-domain and subgradient vocabulary used here.

Best owner abstraction:
- the chapter owner `convexDirectionalDerivative`, together with the canonical finite
  theorem-level `toReal` view used under interior hypotheses, and the
  subdifferential owner `∂ f(x)`.

Primitive data:
- none in this file; the directional-derivative construction and subdifferential owners are
  already defined upstream.

Derived API:
- this Euclidean recall surface for the subdifferential identity and max formula.

Source/core/bridge triage:
- source-facing: the Euclidean specialization of the directional-derivative subdifferential
  identity and max formula;
- core/canonical: `convexDirectionalDerivative` and `subdifferential`;
- bridge/view: this recall file.

The previous version redefined the effective domain, finite real part, subdifferential, and
directional derivative locally on `ℝⁿ`. Those were duplicate wheels once `Theorem_3_21`,
`Definition_3_3`, and `Definition_3_1_5` became the chapter owners. This file now reuses the
canonical owner vocabulary directly and keeps only the Euclidean specialization layer. -/

section Subdifferential

variable {f : E → WithTop ℝ} {x0 : E}

/-- Theorem 3.1.17: for a convex `ℝ ∪ {+∞}`-valued function on `ℝⁿ`, the
subdifferential with respect to the direction variable of `p ↦ f'(x₀; p)` at
`0` coincides with the subdifferential of `f` at `x₀`. The companion
directional-derivative max formula is recalled immediately below in the
canonical `IsGreatest` owner form. -/
-- This Euclidean bridge theorem restates the owner-level subdifferential
-- identity already proved upstream in `Theorem_3_21`.
theorem convexDirectionalDerivativeReal_subdifferential_eq_at_zero
    (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    (hx0 : x0 ∈ interior (dom f)) :
    ∂[Set.univ] f′[hx0](0) = ∂ f(x0) :=
  subdifferential_convexDirectionalDerivativeReal_at_zero_eq_subdifferential
    hf hx0

/-- The companion max formula is recorded in the canonical greatest-element
form for the image of the subdifferential under `g ↦ ⟪g, p⟫`. -/
-- The recalled `IsGreatest` formulation is the chapter-owner form of the textbook maximum claim.
recall convexDirectionalDerivativeReal_isGreatest_subgradientPairing_of_mem_interior

end Subdifferential

end

/-! ### Lemma_3_1_18 (from Chap03) -/
noncomputable section

open scoped Pointwise

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-
Lemma 3.1.18 is a source-facing item in the chapter's tangent-cone domain.

Primary domain:
- tangent cones of convex subsets of real normed spaces.

Relevant owner-style declarations sampled before refinement:
- `posTangentConeAt`
- `mem_posTangentConeAt_of_segment_subset`
- `PointedCone.hull`
- `Set.vsub_singleton`

Best owner abstraction:
- `posTangentConeAt Q xBar`

Primitive data:
- the feasible set `Q`
- the base point `xBar`

Derived API:
- the displacement set `Q -ᵥ ({xBar} : Set E)`
- the pointed conical hull `PointedCone.hull ℝ (Q -ᵥ ({xBar} : Set E))`

Source/core/bridge triage:
- source-facing: the textbook feasible-direction cone at `xBar`
- core/canonical: `posTangentConeAt Q xBar`
- bridge/view: the displacement-set realization and its pointed cone hull

Mathlib's field-valued `tangentConeAt ℝ Q xBar` is a different owner abstraction from the textbook
positive cone of feasible directions; at boundary points it can be strictly larger. This source
item therefore uses the chapter's canonical owner `posTangentConeAt`. The textbook `ℝⁿ` statement
is a specialization of this real normed-space theorem.
-/

/-- Lemma 3.1.18, owner-level equality form: for a convex set `Q` in a real normed space and a
point `xBar ∈ Q`, the positive tangent cone at `xBar` is the closure of the canonical pointed cone
hull of the feasible displacements `Q - xBar`. The textbook `ℝⁿ` closed boundary-point case is the
specialization `IsClosed Q` and `xBar ∈ frontier Q`. -/
-- Proof sketch: the tangent cone is the positive-direction owner `posTangentConeAt Q xBar`, while
-- the feasible-direction model is `PointedCone.hull ℝ (Q -ᵥ ({xBar} : Set E))`. Convexity turns
-- small feasible increments into segments from `xBar`, and the tangent-cone closure description
-- identifies the resulting cone with the closure of this pointed hull.
theorem posTangentConeAt_eq_closure_pointedConeHull_vsub_singleton
    (Q : Set E) (hQ_convex : Convex ℝ Q) (xBar : E) (hxBar : xBar ∈ Q) :
    posTangentConeAt Q xBar =
      closure (PointedCone.hull ℝ (Q -ᵥ ({xBar} : Set E))) := by
  let S : Set E := Q -ᵥ ({xBar} : Set E)
  -- The displacement set remains convex after translating `Q` by `-xBar`.
  have hS_convex : Convex ℝ S := by
    simpa [S, Set.vsub_singleton, vsub_eq_sub] using hQ_convex.sub (convex_singleton xBar)
  have hxBar_mem_singleton : xBar ∈ ({xBar} : Set E) := by
    simp
  have hxBar_vsub_self : xBar -ᵥ xBar = (0 : E) := by
    simp [vsub_eq_sub]
  -- The zero displacement is feasible because the base point itself lies in `Q`.
  have hS_zero : (0 : E) ∈ S := by
    exact ⟨xBar, hxBar, xBar, hxBar_mem_singleton, hxBar_vsub_self⟩
  -- Every feasible displacement comes from a segment starting at `xBar`, so it is tangent.
  have hS_subset : S ⊆ posTangentConeAt Q xBar := by
    intro v hv
    have hv' : v ∈ (· -ᵥ xBar) '' Q := by
      simpa [S, Set.vsub_singleton] using hv
    rcases hv' with ⟨x, hx, rfl⟩
    simpa [vsub_eq_sub] using
      sub_mem_posTangentConeAt_of_segment_subset (hQ_convex.segment_subset hxBar hx)
  have hsmul_mem :
      ∀ {r : ℝ} {v : E}, 0 ≤ r → v ∈ posTangentConeAt Q xBar → r • v ∈ posTangentConeAt Q xBar := by
    intro r v hr hv
    rcases exists_fun_of_mem_tangentConeAt hv with ⟨α, l, hl, c, d, hd₀, hds, hcd⟩
    let rr : NNReal := ⟨r, hr⟩
    refine mem_tangentConeAt_of_seq l (fun n ↦ rr * c n) d hd₀ hds ?_
    simpa [rr, mul_smul] using (tendsto_const_nhds.smul hcd)
  have hconvexHull_pointed : (ConvexCone.hull ℝ S).Pointed :=
    ConvexCone.subset_hull hS_zero
  have hpointedHull_eq_convexHull : (PointedCone.hull ℝ S : Set E) = ConvexCone.hull ℝ S := by
    ext v
    constructor
    · intro hv
      let C : PointedCone ℝ E := (ConvexCone.hull ℝ S).toPointedCone hconvexHull_pointed
      have hspan : PointedCone.hull ℝ S ≤ C := by
        refine Submodule.span_le.2 ?_
        intro x hx
        exact ConvexCone.subset_hull hx
      exact hspan hv
    · intro hv
      have hconvexHull_le : ConvexCone.hull ℝ S ≤ (PointedCone.hull ℝ S : ConvexCone ℝ E) := by
        exact ConvexCone.hull_min (fun x hx ↦ PointedCone.subset_hull hx)
      exact hconvexHull_le hv
  have hmem_pointedHull {v : E} :
      v ∈ (PointedCone.hull ℝ S : Set E) ↔ ∃ r : ℝ, 0 < r ∧ v ∈ r • S := by
    rw [hpointedHull_eq_convexHull]
    simpa using (ConvexCone.mem_hull_of_convex hS_convex : v ∈ ConvexCone.hull ℝ S ↔ _)
  have hpointedHull_subset : (PointedCone.hull ℝ S : Set E) ⊆ posTangentConeAt Q xBar := by
    intro v hv
    rcases hmem_pointedHull.mp hv with ⟨r, hr, y, hy, rfl⟩
    exact hsmul_mem hr.le (hS_subset hy)
  have hclosed : IsClosed (posTangentConeAt Q xBar) := by
    rw [posTangentConeAt, tangentConeAt_def]
    exact isClosed_setOf_clusterPt
  apply Set.Subset.antisymm
  · intro v hv
    -- Tangent-cone witnesses provide scaled feasible increments converging to `v`.
    rcases exists_fun_of_mem_tangentConeAt hv with ⟨α, l, hl, c, d, hd₀, hds, hcd⟩
    have hdS : ∀ᶠ n in l, d n ∈ S := by
      filter_upwards [hds] with n hn
      have hn' : d n ∈ (· -ᵥ xBar) '' Q := by
        refine ⟨xBar + d n, hn, ?_⟩
        simp [vsub_eq_sub]
      simpa [S, Set.vsub_singleton] using hn'
    have hcdHull : ∀ᶠ n in l, c n • d n ∈ (PointedCone.hull ℝ S : Set E) := by
      filter_upwards [hdS] with n hn
      simpa [NNReal.smul_def] using
        (PointedCone.hull ℝ S).smul_mem (show 0 ≤ (c n : ℝ) from (c n).2)
          (PointedCone.subset_hull hn)
    exact mem_closure_of_tendsto hcd hcdHull
  -- Closedness upgrades the pointed-hull inclusion to an inclusion of its closure.
  · exact hclosed.closure_subset_iff.2 hpointedHull_subset

end
