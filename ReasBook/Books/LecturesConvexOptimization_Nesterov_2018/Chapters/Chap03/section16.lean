import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_16 (from Chap03) -/
open scoped WithTopConvexAnalysis

universe u

/- Definition 3.16 is a recall-only item in the chapter's common-subdifferential domain.

Primary domain:
- convex analysis of extended-real-valued functions on real inner-product spaces.

Relevant owner-style declarations sampled before refinement:
- `subdifferential`, the pointwise owner for subgradients;
- `commonRegularSubdifferential`, the canonical owner for the intersection of pointwise
  subdifferentials over a set;
- `mem_commonRegularSubdifferential_iff`, the membership bridge for that owner.

Best owner abstraction:
- `commonRegularSubdifferential`

Primitive data:
- an extended-real-valued function `f`;
- a set `X`.

Derived API:
- the textbook notation `∂̂ f(X)`;
- the membership expansion `g ∈ ∂̂ f(X) ↔ ∀ x ∈ X, g ∈ ∂ f(x)`.

Source/core/bridge triage:
- source-facing: the epigraph facet of `X` with respect to `f`;
- core/canonical: `commonRegularSubdifferential f X`;
- bridge/view: `mem_commonRegularSubdifferential_iff`.

The textbook defines the epigraph facet for a nonempty closed convex set `X ⊆ dom f`, but those
extra hypotheses are not primitive data for the underlying owner. This file therefore reuses the
existing common-subdifferential owner directly rather than introducing a new synonym or keeping a
Euclidean-coordinate wrapper.
-/

section

/- Definition 3.16: for a nonempty closed convex set `X ⊆ dom f`, the epigraph facet of `X` with
respect to `f` is the common regular subdifferential `∂̂ f(X) = ⋂ x ∈ X, ∂ f(x)`. -/
recall commonRegularSubdifferential
    {V : Type u} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]
    (f : V → WithTop ℝ) (X : Set V) : Set V

/- Membership in the recalled epigraph facet means belonging to every pointwise subdifferential
`∂ f(x)` for `x ∈ X`. -/
recall mem_commonRegularSubdifferential_iff
    {V : Type u} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]
    {f : V → WithTop ℝ} {X : Set V} {g : V} :
    g ∈ ∂̂ f(X) ↔ ∀ x ∈ X, g ∈ ∂ f(x)

end

/-! ### Lemma_3_16 (from Chap03) -/
noncomputable section

open Set
open scoped Gradient SupportFunction WithTopConvexAnalysis EuclideanOrthant

universe u

variable {m : ℕ} {E : Type u}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "Eₘ" => EuclideanSpace ℝ (Fin m)

/- Lemma 3.16 is a source-facing bounded-to-compact bridge in the chapter's
support-function-composition domain.

Primary domain:
- support-function compositions and their active-multiplier subdifferentials.

Sampled owner and bridge declarations:
- `activeSupportFunctionMultipliers`
- `subdifferential_supportFunction_comp_vectorMap_eq_image_activeMultipliers`
- `Bornology.IsBounded.isCompact_closure`
- `subset_convexHull`

Best owner abstraction:
- the owner theorem
  `subdifferential_supportFunction_comp_vectorMap_eq_image_activeMultipliers`
  over the support-function composition `x ↦ ξ[Λ] (vectorMap fs x)`, its active multipliers
  `activeSupportFunctionMultipliers Λ fs x`, its thin `WithTop` bridge
  `supportFunctionCompWithTop Λ fs`, and `weightedGradientCombination`

Primitive data:
- a weight set `Λ : Set Eₘ`
- a coordinate family `fs : Fin m → E → ℝ`
- a pointwise gradient witness `HasGradientAt (fs i) (∇ (fs i) x) x` at the base point

Derived API kept here:
- the source-facing orthant hypothesis `Λ ⊆ nonnegativeOrthant m`
- the bounded-to-compact passage `Bornology.IsBounded.isCompact_closure`
- the closure active multiplier face `activeSupportFunctionMultipliers (closure Λ) fs x`
- the convex-hull enclosure `subset_convexHull`
- the direct image `(weightedGradientCombination fs x) ''
    activeSupportFunctionMultipliers (closure Λ) fs x`

Source/core/bridge triage:
- source-facing: Lemma 3.16's bounded-to-compact subdifferential description
- core/canonical: `EuclideanSpace.nonnegativeOrthant`, `supportFunction`, `pointwiseSupremumOn`,
  `weightedGradientCombination`, `subdifferential`,
  `subdifferential_supportFunction_comp_vectorMap_eq_image_activeMultipliers`
- bridge/view: `Bornology.IsBounded.isCompact_closure`, the closure specialization, and the
  `WithTop` bridge `supportFunctionCompWithTop Λ fs` on the left-hand side of the theorem
  statements

This file therefore refines part (1) to direct canonical recall of the exact owner theorem
`convexOn_supportFunction_comp_vectorMap` and keeps only parts (2) and (3) as the genuine
bounded-to-compact bridge layer on top of that owner API.
-/

/- Lemma 3.16 (1): for a nonnegative weight set, the finite real part of the
support-function composition `x ↦ ξ[Λ] (vectorMap fs x)` is convex on its effective domain.

This is exactly the upstream owner theorem `convexOn_supportFunction_comp_vectorMap` from
`Lemma_3_1_16`. In the bounded case considered here, Proposition 3.11 can additionally identify
that effective domain with `Set.univ`. Keeping a renamed local theorem here would duplicate the
owner's exact interface, so this file records that fact only in prose. -/

/-- Helper for Lemma 3.16: if `s ⊆ t ⊆ closure s`, `s` is nonempty, and `t` is bounded above,
then the two `sSup` values in `WithTop ℝ` agree. -/
private theorem sSup_eq_of_subset_of_subset_closure
    {s t : Set (WithTop ℝ)} (hs : s.Nonempty) (ht_bdd : BddAbove t)
    (hst : s ⊆ t) (hts : t ⊆ closure s) :
    sSup t = sSup s := by
  -- The closure hypothesis identifies the upper-bound predicates of `s` and `t`.
  refine (isLUB_csSup (hs.mono hst) ht_bdd).unique ?_
  exact
    ((isLUB_iff_of_subset_of_subset_closure hst hts).1
      (isLUB_csSup hs (ht_bdd.mono hst)))

/-- Helper for Lemma 3.16: the nonnegative orthant in `ℝ^m` is closed. -/
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

/-- Helper for Lemma 3.16: closing a bounded nonempty multiplier set does not change the
`WithTop` support-function composition. -/
private theorem supportFunctionCompWithTop_closure_eq
    {Λ : Set Eₘ} {fs : Fin m → E → ℝ}
    (hΛ_bounded : Bornology.IsBounded Λ) (hΛ_nonempty : Λ.Nonempty) :
    supportFunctionCompWithTop (closure Λ) fs = supportFunctionCompWithTop Λ fs := by
  ext x
  let φ : Eₘ → WithTop ℝ := fun lam ↦ (inner ℝ lam (vectorMap fs x) : WithTop ℝ)
  have hφ_cont : Continuous φ := by
    -- The support slice is the inner product followed by the `WithTop` coercion.
    simpa [φ] using
      (WithTop.continuous_coe.comp (continuous_id.inner continuous_const))
  rw [supportFunctionCompWithTop, supportFunctionCompWithTop, pointwiseSupremumOn_apply,
    pointwiseSupremumOn_apply]
  change sSup (φ '' closure Λ) = sSup (φ '' Λ)
  -- The closure image sits between the original image and its closure.
  exact sSup_eq_of_subset_of_subset_closure
    (hΛ_nonempty.image φ)
    ((hΛ_bounded.isCompact_closure.image hφ_cont).bddAbove)
    (by
      rintro _ ⟨lam, hlam, rfl⟩
      exact ⟨lam, subset_closure hlam, rfl⟩)
    (hφ_cont.continuousOn.image_closure)

/-- Helper for Lemma 3.16: the active multiplier face over `closure Λ` is convex. -/
private theorem activeSupportFunctionMultipliers_convex_closure
    {Λ : Set Eₘ} {fs : Fin m → E → ℝ}
    (hΛ_convex : Convex ℝ Λ) (x : E) :
    Convex ℝ (activeSupportFunctionMultipliers (closure Λ) fs x) := by
  rw [convex_iff_add_mem]
  intro lam hlam mu hmu a b ha hb hab
  rw [mem_activeSupportFunctionMultipliers_iff] at hlam hmu ⊢
  have hclosure_convex : Convex ℝ (closure Λ) := hΛ_convex.closure
  refine ⟨(convex_iff_add_mem.mp hclosure_convex) hlam.1 hmu.1 ha hb hab, ?_⟩
  have hinner_eq : inner ℝ lam (vectorMap fs x) = inner ℝ mu (vectorMap fs x) := by
    simpa using (hlam.2.trans hmu.2.symm)
  -- Both active multipliers expose the same support value, so every convex combination stays
  -- on that active face.
  calc
    (inner ℝ (a • lam + b • mu) (vectorMap fs x) : WithTop ℝ)
        = (((a + b) * inner ℝ lam (vectorMap fs x) : ℝ) : WithTop ℝ) := by
            simp [inner_add_left, inner_smul_left, hinner_eq, add_mul]
    _ = (inner ℝ lam (vectorMap fs x) : WithTop ℝ) := by
      simp [hab]
    _ = supportFunctionCompWithTop (closure Λ) fs x := hlam.2

/-- Helper for Lemma 3.16: the weighted-gradient combination depends linearly on the multiplier
vector. -/
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

/-- Helper for Lemma 3.16: an active multiplier for `Λ` remains active after passing to
`closure Λ`. -/
private theorem activeSupportFunctionMultipliers_subset_closure
    {Λ : Set Eₘ} {fs : Fin m → E → ℝ}
    (hΛ_bounded : Bornology.IsBounded Λ) (hΛ_nonempty : Λ.Nonempty) {x : E} :
    activeSupportFunctionMultipliers Λ fs x ⊆
      activeSupportFunctionMultipliers (closure Λ) fs x := by
  intro w hw
  rw [mem_activeSupportFunctionMultipliers_iff] at hw ⊢
  refine ⟨subset_closure hw.1, ?_⟩
  -- Closure does not change the support value, so the same touching equality remains valid.
  have hclosure_eq :
      supportFunctionCompWithTop Λ fs x =
        supportFunctionCompWithTop (closure Λ) fs x := by
    exact
      (congrFun
        (supportFunctionCompWithTop_closure_eq
          (Λ := Λ)
          (fs := fs)
          hΛ_bounded
          hΛ_nonempty)
        x).symm
  exact hw.2.trans hclosure_eq

/-- Lemma 3.16 (2): for a bounded convex nonnegative weight set, the subdifferential of the
`WithTop` bridge of the support-function composition `x ↦ ξ[Λ] (vectorMap fs x)` is the convex
hull of the image of the closure active-multiplier face under the owner weighted-gradient map. -/
-- Proof sketch: pass from `Λ` to `closure Λ`; boundedness makes the closure compact without
-- changing the support-function value. The bounded source-facing formulation is then the convex
-- hull of the weighted-gradient image of the closure active-multiplier face.
theorem
    subdifferential_supportFunction_comp_vectorMap_eq_convexHull_image_activeMultipliers_of_bounded
    {Λ : Set Eₘ} {fs : Fin m → E → ℝ}
    (hΛ_bounded : Bornology.IsBounded Λ) (hΛ_nonempty : Λ.Nonempty)
    (hΛ_nonneg : Λ ⊆ ℝ₊^m) (hΛ_convex : Convex ℝ Λ)
    (hfs_convex : ∀ i, ConvexOn ℝ Set.univ (fs i)) (x : E)
    (hfs_grad : ∀ i, HasGradientAt (fs i) (∇ (fs i) x) x) :
    ∂ (supportFunctionCompWithTop Λ fs)(x) =
      convexHull ℝ
        ((weightedGradientCombination fs x) ''
          activeSupportFunctionMultipliers (closure Λ) fs x) := by
  have hclosure_nonneg : closure Λ ⊆ ℝ₊^m := by
    -- The nonnegative orthant is closed, so closing `Λ` preserves nonnegativity.
    exact nonnegativeOrthant_isClosed.closure_subset_iff.2 hΛ_nonneg
  have hsub_eq :
      ∂ (supportFunctionCompWithTop (closure Λ) fs)(x) =
        (weightedGradientCombination fs x) ''
          activeSupportFunctionMultipliers (closure Λ) fs x := by
    -- Apply the compact owner theorem to the closed bounded multiplier set.
    exact subdifferential_supportFunction_comp_vectorMap_eq_image_activeMultipliers
      (hΛ_nonempty.mono subset_closure)
      hΛ_bounded.isCompact_closure
      hΛ_convex.closure
      hclosure_nonneg
      hfs_convex
      x
      hfs_grad
  have himage_convex :
      Convex ℝ
        ((weightedGradientCombination fs x) ''
          activeSupportFunctionMultipliers (closure Λ) fs x) := by
    -- The active face is convex and the weighted-gradient map is linear in the multiplier.
    exact
      (activeSupportFunctionMultipliers_convex_closure
        (Λ := Λ) (fs := fs) hΛ_convex x).is_linear_image
        (weightedGradientCombination_isLinear fs x)
  -- Replace `Λ` by `closure Λ`, invoke the owner theorem, and collapse the convex hull of a
  -- convex image.
  calc
    ∂ (supportFunctionCompWithTop Λ fs)(x)
        = ∂ (supportFunctionCompWithTop (closure Λ) fs)(x) := by
            simp [supportFunctionCompWithTop_closure_eq
              (Λ := Λ) (fs := fs) hΛ_bounded hΛ_nonempty]
    _ = (weightedGradientCombination fs x) ''
          activeSupportFunctionMultipliers (closure Λ) fs x := hsub_eq
    _ = convexHull ℝ
          ((weightedGradientCombination fs x) ''
            activeSupportFunctionMultipliers (closure Λ) fs x) := by
            symm
            exact himage_convex.convexHull_eq

/-- Lemma 3.16 (3): every active multiplier in a bounded convex nonnegative weight set `Λ`
produces a subgradient of the support-function composition under the weighted-gradient map. -/
-- Proof sketch: the weighted gradient combination belongs to the image
-- `(weightedGradientCombination fs x) '' activeSupportFunctionMultipliers (closure Λ) fs x`
-- after passing from `Λ` to `closure Λ`. Then apply Lemma 3.16 (2) and the inclusion of a set
-- into its convex hull.
theorem weightedGradientCombination_mem_subdifferential_of_mem_activeMultipliers_of_bounded
    {Λ : Set Eₘ} {fs : Fin m → E → ℝ}
    (hΛ_bounded : Bornology.IsBounded Λ) (hΛ_nonneg : Λ ⊆ ℝ₊^m)
    (hΛ_convex : Convex ℝ Λ) (hfs_convex : ∀ i, ConvexOn ℝ Set.univ (fs i))
    {x : E}
    (hfs_grad : ∀ i, HasGradientAt (fs i) (∇ (fs i) x) x) {w : Eₘ}
    (hw : w ∈ activeSupportFunctionMultipliers Λ fs x) :
    weightedGradientCombination fs x w ∈
      ∂ (supportFunctionCompWithTop Λ fs)(x) := by
  have hw' := hw
  have hΛ_nonempty : Λ.Nonempty := by
    -- Any active multiplier is, in particular, a point of `Λ`.
    rw [mem_activeSupportFunctionMultipliers_iff] at hw'
    exact ⟨w, hw'.1⟩
  have hw_closure :
      w ∈ activeSupportFunctionMultipliers (closure Λ) fs x := by
    -- Activity persists after passing from `Λ` to its closure.
    exact
      activeSupportFunctionMultipliers_subset_closure
        (Λ := Λ)
        (fs := fs)
        hΛ_bounded
        hΛ_nonempty
        hw
  have hw_image :
      weightedGradientCombination fs x w ∈
        (weightedGradientCombination fs x) ''
          activeSupportFunctionMultipliers (closure Λ) fs x := by
    exact ⟨w, hw_closure, rfl⟩
  have hw_hull :
      weightedGradientCombination fs x w ∈
        convexHull ℝ
          ((weightedGradientCombination fs x) ''
            activeSupportFunctionMultipliers (closure Λ) fs x) := by
    -- Every point of the image lies in its convex hull.
    exact subset_convexHull ℝ _ hw_image
  -- Substitute the bounded subdifferential formula from Lemma 3.16 (2).
  simpa
    [subdifferential_supportFunction_comp_vectorMap_eq_convexHull_image_activeMultipliers_of_bounded
      (Λ := Λ)
      (fs := fs)
      hΛ_bounded
      hΛ_nonempty
      hΛ_nonneg
      hΛ_convex
      hfs_convex
      x
      hfs_grad]
    using hw_hull

end

/-! ### Proposition_3_16 (from Chap03) -/
noncomputable section

open scoped WithTopConvexAnalysis

/- Proposition 3.16 lies in the chapter's real subdifferential / norm domain.

Primary domain:
- subdifferentials of the norm on a real inner-product space.

Sampled owner-style declarations:
- `subdifferential` in `Definition_3_1_5`, the chapter owner for unconstrained subgradients;
- `mem_subdifferential_iff` in `Definition_3_1_5`, the atomic membership view of that owner;
- `subdifferential_seminorm_at_zero_eq_inner_le` in `Proposition_3_20`, the nearby intrinsic
  origin-subdifferential theorem for seminorms;
- mathlib `real_inner_le_norm`, the canonical Cauchy--Schwarz inequality in the real
  inner-product-space owner language.

Best owner abstraction:
- `subdifferential`.

Primitive data:
- the norm function `fun x : E ↦ ‖x‖`.

Derived API:
- the origin formula `∂ ‖·‖ (0) = closedBall 0 1`;
- the nonzero singleton formula `∂ ‖·‖ (x) = {‖x‖⁻¹ • x}`;
- the combined piecewise statement of Proposition 3.16.

Source/core/bridge triage:
- source-facing: Proposition 3.16's zero/nonzero description of the norm subdifferential;
- core/canonical: the chapter owner `subdifferential`;
- bridge/view: the direct membership inequality characterization for
  `∂ (fun y ↦ ‖y‖) (x)`.

The previous version rebuilt a real-valued subgradient predicate and subdifferential local to this
file, even though Chapter 3 already owns those notions in `Definition_3_1_5`. The proposition also
does not genuinely use coordinates, so the public statement is refined to the intrinsic real
inner-product-space level while preserving the same Euclidean specialization.
-/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Membership in the norm subdifferential is exactly the affine lower-support inequality for the
norm. -/
theorem mem_subdifferential_norm_iff {x g : E} :
    g ∈ ∂ (fun y : E ↦ ‖y‖)(x) ↔ ∀ y : E, ‖x‖ + inner ℝ g (y - x) ≤ ‖y‖ := by
  constructor
  · intro hg y
    rw [mem_subdifferential_iff, IsSubgradientAt] at hg
    have hy := hg.2 (by simp : y ∈ dom fun z : E ↦ ((‖z‖ : ℝ) : WithTop ℝ))
    exact_mod_cast hy
  · intro h
    rw [mem_subdifferential_iff, IsSubgradientAt]
    refine ⟨by simp, ?_⟩
    intro y hy
    exact_mod_cast h y

/-- The norm has closed unit-ball subdifferential at the origin. -/
-- Proof sketch: rewrite membership in `∂ (fun x ↦ ‖x‖) (0)` via
-- `mem_subdifferential_norm_iff`. The resulting inequality `⟪g, y⟫ ≤ ‖y‖` for all `y` is
-- equivalent to `‖g‖ ≤ 1` by Cauchy--Schwarz and the test point `y = g`.
theorem subdifferential_norm_zero :
    ∂ (fun x : E ↦ ‖x‖)(0) = Metric.closedBall 0 1 := by
  ext g
  constructor
  · intro hg
    have hg' := mem_subdifferential_norm_iff.mp hg
    have hgg : inner ℝ g g ≤ ‖g‖ := by
      simpa using hg' g
    rw [real_inner_self_eq_norm_mul_norm] at hgg
    have hnorm : ‖g‖ ≤ 1 := by
      nlinarith [norm_nonneg g]
    simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm
  · intro hg
    have hg' : ‖g‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hg
    rw [mem_subdifferential_norm_iff]
    intro y
    calc
      ‖(0 : E)‖ + inner ℝ g (y - 0) = inner ℝ g y := by simp
      _ ≤ ‖g‖ * ‖y‖ := real_inner_le_norm _ _
      _ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right hg' (norm_nonneg y)
      _ = ‖y‖ := by ring

/-- Away from the origin, the norm has singleton subdifferential generated by the normalized
vector `‖x‖⁻¹ • x`. -/
-- Proof sketch: rewrite membership via `mem_subdifferential_norm_iff`. The normalized vector
-- `‖x‖⁻¹ • x` satisfies the support inequality by Cauchy--Schwarz. Conversely, any subgradient
-- `g` satisfies `⟪g, z⟫ ≤ ‖z‖` for all `z`, hence `‖g‖ ≤ 1`; testing at `y = 0` gives
-- `‖x‖ ≤ ⟪g, x⟫`, so equality holds in Cauchy--Schwarz and forces `g = ‖x‖⁻¹ • x`.
theorem subdifferential_norm_nonzero
    (x : E) (hx : x ≠ 0) :
    ∂ (fun y : E ↦ ‖y‖)(x) = {‖x‖⁻¹ • x} := by
  ext g
  constructor
  · intro hg
    have hsub := mem_subdifferential_norm_iff.mp hg
    have hgx : ‖x‖ ≤ inner ℝ g x := by
      have h0 := hsub 0
      have h0' : ‖x‖ - inner ℝ g x ≤ 0 := by simpa using h0
      linarith
    have hall : ∀ z : E, inner ℝ g z ≤ ‖z‖ := by
      intro z
      have hz := hsub (x + z)
      have hz' : ‖x‖ + inner ℝ g z ≤ ‖x + z‖ := by
        simpa using hz
      have htri : ‖x + z‖ ≤ ‖x‖ + ‖z‖ := norm_add_le x z
      linarith
    have hgle : ‖g‖ ≤ 1 := by
      have hgg : inner ℝ g g ≤ ‖g‖ := hall g
      rw [real_inner_self_eq_norm_mul_norm] at hgg
      nlinarith [norm_nonneg g]
    have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hcs : inner ℝ g x = ‖g‖ * ‖x‖ := by
      apply le_antisymm
      · exact real_inner_le_norm _ _
      · nlinarith [hgx, hgle, hxnorm]
    have hgnorm : ‖g‖ = 1 := by
      nlinarith [hgx, hgle, hcs, hxnorm]
    have hsmul : ‖x‖ • g = x := by
      have hsmul' : ‖x‖ • g = ‖g‖ • x := (inner_eq_norm_mul_iff_real).mp hcs
      simpa [hgnorm] using hsmul'
    have hg_eq : g = ‖x‖⁻¹ • x := (eq_inv_smul_iff₀ (norm_ne_zero_iff.mpr hx)).2 hsmul
    simp [hg_eq]
  · intro hg
    rcases Set.mem_singleton_iff.mp hg with rfl
    rw [mem_subdifferential_norm_iff]
    intro y
    have hself : inner ℝ (‖x‖⁻¹ • x) x = ‖x‖ := by
      calc
        inner ℝ (‖x‖⁻¹ • x) x = ‖x‖⁻¹ * inner ℝ x x := by
          simp [inner_smul_left]
        _ = ‖x‖⁻¹ * (‖x‖ * ‖x‖) := by rw [real_inner_self_eq_norm_mul_norm]
        _ = ‖x‖ := by field_simp [norm_ne_zero_iff.mpr hx]
    calc
      ‖x‖ + inner ℝ (‖x‖⁻¹ • x) (y - x)
          = ‖x‖ + (inner ℝ (‖x‖⁻¹ • x) y - inner ℝ (‖x‖⁻¹ • x) x) := by
              rw [inner_sub_right]
      _ = inner ℝ (‖x‖⁻¹ • x) y := by rw [hself]; ring
      _ ≤ ‖‖x‖⁻¹ • x‖ * ‖y‖ := real_inner_le_norm _ _
      _ = ‖y‖ := by
          have hunit : ‖‖x‖⁻¹ • x‖ = 1 := by
            rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg x))]
            field_simp [norm_ne_zero_iff.mpr hx]
          rw [hunit, one_mul]

attribute [local instance] Classical.propDecidable

/-- Proposition 3.16: the subdifferential of the norm is the closed unit ball at the origin and
the singleton `{‖x‖⁻¹ • x}` at every nonzero point. -/
-- Proof sketch: split on `x = 0` and apply the previous two formulas.
theorem subdifferential_norm_eq_closedBall_or_singleton
    (x : E) :
    ∂ (fun y : E ↦ ‖y‖)(x) =
      if x = 0 then
        Metric.closedBall 0 1
      else
        {‖x‖⁻¹ • x} := by
  by_cases hx : x = 0
  · simpa [hx] using subdifferential_norm_zero
  · simpa [hx] using subdifferential_norm_nonzero x hx

end

/-! ### Theorem_3_16 (from Chap03) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Helper for Theorem 3.16: the displacement from a point outside `Q` to its Euclidean
projection on `Q` is nonzero. -/
lemma projection_displacement_ne_zero
    (Q : Set E) (hQ_nonempty : Q.Nonempty) {x : E} (hQ_closed : IsClosed Q)
    (hQ_convex : Convex ℝ Q) (hx : x ∉ Q) :
    x - euclideanProjection Q hQ_nonempty hQ_closed hQ_convex x ≠ 0 := by
  -- The projection point belongs to `Q`, so a zero displacement would force `x ∈ Q`.
  let p := euclideanProjection Q hQ_nonempty hQ_closed hQ_convex x
  have hp : IsProjectionPointOn Q x p := by
    simpa [p] using
      euclideanProjection_isProjectionPointOn Q hQ_nonempty hQ_closed hQ_convex x
  intro hzero
  have hxp : x = p := sub_eq_zero.mp hzero
  exact hx (hxp.symm ▸ hp.1)

/-- Helper for Theorem 3.16: the projection variational inequality bounds every feasible inner
product by the projection value against the projection displacement. -/
lemma projection_inner_le_projection_value
    (Q : Set E) (hQ_nonempty : Q.Nonempty) {x y : E} (hQ_closed : IsClosed Q)
    (hQ_convex : Convex ℝ Q) (hy : y ∈ Q) :
    inner ℝ (x - euclideanProjection Q hQ_nonempty hQ_closed hQ_convex x) y ≤
      inner ℝ (x - euclideanProjection Q hQ_nonempty hQ_closed hQ_convex x)
        (euclideanProjection Q hQ_nonempty hQ_closed hQ_convex x) := by
  -- Rewrite the projection variational inequality into the source-facing support inequality.
  let p := euclideanProjection Q hQ_nonempty hQ_closed hQ_convex x
  have hp : IsProjectionPointOn Q x p := by
    simpa [p] using
      euclideanProjection_isProjectionPointOn Q hQ_nonempty hQ_closed hQ_convex x
  have hinner : inner ℝ (x - p) (y - p) ≤ 0 := by
    have hproj : 0 ≤ inner ℝ (p - x) (y - p) :=
      hp.inner_sub_nonneg hQ_convex hy
    have hproj' : 0 ≤ -inner ℝ (x - p) (y - p) := by
      rw [← inner_neg_left]
      simpa [sub_eq_add_neg] using hproj
    exact neg_nonneg.mp hproj'
  -- Expand `y` around the projection point to isolate the controlled displacement term.
  calc
    inner ℝ (x - p) y = inner ℝ (x - p) ((y - p) + p) := by abel_nf
    _ = inner ℝ (x - p) (y - p) + inner ℝ (x - p) p := by
      rw [inner_add_right]
    _ ≤ 0 + inner ℝ (x - p) p := by
      linarith
    _ = inner ℝ (x - p) p := by
      simp

/-- Helper for Theorem 3.16: the projection point lies strictly below the exterior point along the
projection displacement functional. -/
lemma projection_value_lt_point_value
    (Q : Set E) (hQ_nonempty : Q.Nonempty) {x : E} (hQ_closed : IsClosed Q)
    (hQ_convex : Convex ℝ Q) (hx : x ∉ Q) :
    inner ℝ (x - euclideanProjection Q hQ_nonempty hQ_closed hQ_convex x)
        (euclideanProjection Q hQ_nonempty hQ_closed hQ_convex x) <
      inner ℝ (x - euclideanProjection Q hQ_nonempty hQ_closed hQ_convex x) x := by
  -- The gap equals `‖x - p‖²`, which is positive because `x` lies outside `Q`.
  let p := euclideanProjection Q hQ_nonempty hQ_closed hQ_convex x
  have hne : x - p ≠ 0 := by
    simpa [p] using
      projection_displacement_ne_zero Q hQ_nonempty hQ_closed hQ_convex hx
  have hrewrite :
      inner ℝ (x - p) x =
        inner ℝ (x - p) p + ‖x - p‖ ^ (2 : ℕ) := by
    calc
      inner ℝ (x - p) x = inner ℝ (x - p) (p + (x - p)) := by
        congr 1
        abel_nf
      _ = inner ℝ (x - p) p + inner ℝ (x - p) (x - p) := by
        rw [inner_add_right]
      _ = inner ℝ (x - p) p + ‖x - p‖ ^ (2 : ℕ) := by
        rw [real_inner_self_eq_norm_sq]
  have hpos : 0 < ‖x - p‖ ^ (2 : ℕ) := by
    exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hne)
  linarith

/-- Theorem 3.16: if `Q` is a nonempty closed convex subset of a real inner-product space and
`x ∉ Q`, then there exist `a ≠ 0` and `b : ℝ` with `⟪a, x⟫ > b ≥ sup_{y ∈ Q} ⟪a, y⟫`;
equivalently, in the local Chapter 3 API, `Q` and the singleton `{x}` are strongly separable by a
hyperplane. -/
-- Proof sketch: follow the source proof via the Euclidean projection `p` of `x` onto `Q`; the
-- normal `a = x - p` supports `Q` at `p`, and the midpoint between `⟪a, p⟫` and `⟪a, x⟫` gives a
-- strict offset.
theorem areStronglySeparable_singleton_of_nonmem_closed_convex
    (Q : Set E) (hQ_nonempty : Q.Nonempty) {x : E} (hQ_closed : IsClosed Q)
    (hQ_convex : Convex ℝ Q) (hx : x ∉ Q) :
    AreStronglySeparable Q ({x} : Set E) := by
  -- Route correction: replace the Hahn--Banach shortcut with the textbook projection argument.
  rw [areStronglySeparable_iff]
  let p := euclideanProjection Q hQ_nonempty hQ_closed hQ_convex x
  let a := x - p
  let γ := (inner ℝ a p + inner ℝ a x) / 2
  refine ⟨a, ?_, γ, ?_⟩
  · -- The projection point cannot coincide with `x` because `x ∉ Q`.
    simpa [a, p] using
      projection_displacement_ne_zero Q hQ_nonempty hQ_closed hQ_convex hx
  · constructor
    · intro y hy
      -- The projection point gives a non-strict support bound, and the midpoint makes it strict.
      have hle : inner ℝ a y ≤ inner ℝ a p := by
        simpa [a, p] using
          projection_inner_le_projection_value Q hQ_nonempty hQ_closed hQ_convex hy
      have hgap : inner ℝ a p < inner ℝ a x := by
        simpa [a, p] using
          projection_value_lt_point_value Q hQ_nonempty hQ_closed hQ_convex hx
      have hpγ : inner ℝ a p < γ := by
        dsimp [γ]
        linarith
      linarith
    · intro y hy
      -- The singleton side is exactly the strict upper half-space inequality for `x`.
      have hgap : inner ℝ a p < inner ℝ a x := by
        simpa [a, p] using
          projection_value_lt_point_value Q hQ_nonempty hQ_closed hQ_convex hx
      rcases Set.mem_singleton_iff.mp hy with rfl
      dsimp [γ]
      linarith

end
