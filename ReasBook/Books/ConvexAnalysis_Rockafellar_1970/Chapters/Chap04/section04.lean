import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_4_4_1 (from Chap01) -/
noncomputable section

attribute [local instance] Classical.propDecidable
open scoped Rockafellar
open scoped Topology

/-!
Source/core/bridge triage for this item.

- `source-facing`: the example lists six explicit extended-real-valued functions on `ℝ`, with
  `+∞` outside the natural interval where the real formula is intended.
- `core/canonical`: the owner abstractions are the chapter predicate `Function.IsConvex`, the
  codomain lift `Function.toWithBotTop`, and the canonical extension owner
  `Function.toWithBotTopOn`.
- `bridge/view`: the source extension formula `f.toWithBotTop + δ[ℝ](· | C)` remains available
  via `Function.toWithBotTopOn_eq_add_indicator`; the convexity clauses below use the canonical
  owner bridge `isConvex_toWithBotTopOn_iff`.

Domain-style sampling used here:
- the chapter owner `Function.IsConvex` from `Theorem_4_2`;
- the codomain-lift bridge `Function.toWithBotTop` from `Definition_4_4`;
- the canonical extension owner `Function.toWithBotTopOn` from `Remark_4_4_5`;
- the chapter indicator owner `indicator` from `Defintion_4_8_1`;
- mathlib's epigraph owner theorem `convexOn_iff_convex_epigraph`;
- mathlib's canonical convexity declarations `convexOn_exp` and `convexOn_rpow`;
- mathlib's canonical concavity declaration `Real.concaveOn_rpow`;
- mathlib's concavity declaration `strictConcaveOn_log_Ioi`, whose negation yields convexity of
  `x ↦ -log x` on `(0, ∞)`.

Primitive data vs derived API:
- primitive source-facing data: the six displayed formulas themselves;
- derived API: the six owner-level convexity theorems below.

Layer target: `core/canonical`; extension examples are stated with
`Function.toWithBotTopOn`, while formulas remain textbook-visible in the branch functions.
-/

section

private theorem convexOn_rpow_Ioi_of_nonpos {p : ℝ} (hp : p ≤ 0) :
    ConvexOn ℝ (Set.Ioi (0 : ℝ)) fun x : ℝ ↦ Real.rpow x p := by
  refine convexOn_of_deriv2_nonneg' (convex_Ioi (0 : ℝ)) ?_ ?_ ?_
  · intro x hx
    exact (Real.differentiableAt_rpow_const_of_ne p hx.ne').differentiableWithinAt
  · have hdiff : DifferentiableOn ℝ (fun x : ℝ ↦ x ^ (p - 1)) (Set.Ioi (0 : ℝ)) := by
        intro x hx
        exact
          (Real.differentiableAt_rpow_const_of_ne (p - 1) hx.ne').differentiableWithinAt
    simpa [Real.deriv_rpow_const'] using hdiff.const_mul p
  · intro x hx
    have hderiv2 :
        deriv^[2] (fun y : ℝ ↦ Real.rpow y p) x = p * (p - 1) * x ^ (p - 2) := by
      simpa [descPochhammer] using (Real.iter_deriv_rpow_const p x 2)
    rw [hderiv2]
    have hpp : 0 ≤ p * (p - 1) := by
      nlinarith
    exact mul_nonneg hpp (Real.rpow_nonneg hx.le _)

private theorem quadraticGap_image_Ioo (α : ℝ) (hα : 0 < α) :
    (fun x : ℝ ↦ α ^ 2 - x ^ 2) '' Set.Ioo (-α) α = Set.Ioc (0 : ℝ) (α ^ 2) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    constructor
    · nlinarith [hx.1, hx.2, hα]
    · nlinarith [sq_nonneg x]
  · intro hy
    have hnonneg : 0 ≤ α ^ 2 - y := by
      nlinarith [hy.2]
    refine ⟨Real.sqrt (α ^ 2 - y), ?_, ?_⟩
    · constructor
      · exact lt_of_lt_of_le (by linarith [hα]) (Real.sqrt_nonneg _)
      · rw [Real.sqrt_lt' hα]
        nlinarith [hy.1]
    · have hsquare : Real.sqrt (α ^ 2 - y) ^ 2 = α ^ 2 - y := Real.sq_sqrt hnonneg
      nlinarith

private theorem convexOn_inverseSqrtGap (α : ℝ) (hα : 0 < α) :
    ConvexOn ℝ (Set.Ioo (-α) α)
      (fun x : ℝ ↦ Real.rpow (α ^ 2 - x ^ 2) (-(1 / 2 : ℝ))) := by
  let g : ℝ → ℝ := fun y ↦ Real.rpow y (-(1 / 2 : ℝ))
  let q : ℝ → ℝ := fun x ↦ α ^ 2 - x ^ 2
  have hq_univ : ConcaveOn ℝ Set.univ q := by
    have hconst : ConcaveOn ℝ Set.univ (fun _ : ℝ ↦ α ^ 2) :=
      concaveOn_const (α ^ 2) (convex_univ : Convex ℝ (Set.univ : Set ℝ))
    have hsq : ConvexOn ℝ Set.univ (fun x : ℝ ↦ x ^ (2 : ℕ)) := by
      simpa using
        (show StrictConvexOn ℝ Set.univ (fun x : ℝ ↦ x ^ (2 : ℕ)) from
          Even.strictConvexOn_pow (by decide) (by decide)).convexOn
    simpa [q] using hconst.sub hsq
  have hq : ConcaveOn ℝ (Set.Ioo (-α) α) q :=
    hq_univ.subset (by intro x hx; simp) (convex_Ioo (-α) α)
  have hg_Ioi' : ConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ Real.rpow x (-(1 / 2 : ℝ))) :=
    convexOn_rpow_Ioi_of_nonpos (by norm_num)
  have hg_Ioi : ConvexOn ℝ (Set.Ioi (0 : ℝ)) g := by
    simpa [g] using hg_Ioi'
  have hg : ConvexOn ℝ (q '' Set.Ioo (-α) α) g := by
    rw [quadraticGap_image_Ioo α hα]
    exact hg_Ioi.subset (by intro y hy; exact hy.1) (convex_Ioc 0 (α ^ 2))
  have hg_anti : AntitoneOn g (q '' Set.Ioo (-α) α) := by
    rw [quadraticGap_image_Ioo α hα]
    have hg_anti_Ioi :
        AntitoneOn (fun y : ℝ ↦ Real.rpow y (-(1 / 2 : ℝ))) (Set.Ioi (0 : ℝ)) := by
      simpa using Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by norm_num)
    exact
      hg_anti_Ioi.mono (by intro y hy; exact hy.1)
  simpa [g, q, Function.comp] using hg.comp_concaveOn hq hg_anti

-- Proof sketch: use mathlib's owner theorem `convexOn_exp` on `univ`, precompose with an
-- arbitrary affine map `g`, and then pass to the chapter owner `Function.IsConvex`
-- through the canonical codomain lift `.toWithBotTop`.
/-- Affine-map owner form for Example 4.4.1 (1): for any affine map `g : E →ᵃ[ℝ] ℝ`, the
function `x ↦ exp (g x)` is convex. -/
theorem expAffineMap_isConvex {E : Type*} [AddCommGroup E] [Module ℝ E]
    (g : E →ᵃ[ℝ] ℝ) :
    ((fun x : E ↦ Real.exp (g x)).toWithBotTop).IsConvex ℝ := by
  refine Function.isConvex_coe_of_convexOn_univ ?_
  simpa using convexOn_exp.comp_affineMap g

/-- Intrinsic owner form of Example 4.4.1 (1): for any linear functional `L : E →ₗ[ℝ] ℝ`, the
function `x ↦ exp (L x)` is convex. -/
theorem expLinear_isConvex {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (L : E →ₗ[ℝ] ℝ) :
    ((fun x : E ↦ Real.exp (L x)).toWithBotTop).IsConvex ℝ := by
  refine Function.isConvex_coe_of_convexOn_univ ?_
  simpa using convexOn_exp.comp_linearMap L

-- Proof sketch: specialize `expLinear_isConvex` to `E = ℝ` and the linear map
-- `x ↦ α * x`.
/-- Example 4.4.1 (1): the function `x ↦ exp (α x)` is convex on `ℝ`. -/
theorem expAffine_isConvex (α : ℝ) :
    ((fun x : ℝ ↦ Real.exp (α * x)).toWithBotTop).IsConvex ℝ := by
  simpa [mul_comm] using expLinear_isConvex (L := LinearMap.mul ℝ ℝ α)

-- Proof sketch: reduce the extension statement to convexity of the finite branch on
-- `[0, ∞)` using `isConvex_toWithBotTopOn_iff`, then reuse mathlib's canonical
-- owner theorem `convexOn_rpow`.
/-- Example 4.4.1 (2): for `1 ≤ p`, the function `x ↦ x^p` on `[0, ∞)` extended by `+∞` to
`(-∞, 0)` is convex. -/
theorem nonnegativePowerExtension_isConvex {p : ℝ} (hp : 1 ≤ p) :
    ((fun x : ℝ ↦ Real.rpow x p).toWithBotTopOn (Set.Ici (0 : ℝ))).IsConvex ℝ := by
  exact (isConvex_toWithBotTopOn_iff).2 (by simpa using convexOn_rpow hp)

-- Proof sketch: rewrite the global extension statement through
-- `isConvex_toWithBotTopOn_iff`, then use the canonical concavity owner
-- `Real.concaveOn_rpow` on `[0, ∞)` and negate it.
/-- Example 4.4.1 (3): for `0 ≤ p ≤ 1`, the function `x ↦ -x^p` on `[0, ∞)` extended by `+∞` to
`(-∞, 0)` is convex. -/
theorem nonnegativeNegPowerExtension_isConvex {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    ((fun x : ℝ ↦ -Real.rpow x p).toWithBotTopOn (Set.Ici (0 : ℝ))).IsConvex ℝ := by
  have hconv :
      ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x : ℝ ↦ -Real.rpow x p) := by
    convert (Real.concaveOn_rpow hp₀ hp₁).neg using 1
  exact (isConvex_toWithBotTopOn_iff).2 hconv

-- Proof sketch: on `(0, ∞)`, the real-valued function `x ↦ x^p` has nonnegative second
-- derivative when `p ≤ 0`. Apply the second-derivative criterion on `(0, ∞)` and then extend by
-- `+∞` to `(-∞, 0]` via `isConvex_toWithBotTopOn_iff`.
/-- Example 4.4.1 (4): for `p ≤ 0`, the function `x ↦ x^p` on `(0, ∞)` extended by `+∞` to
`(-∞, 0]` is convex. -/
theorem positivePowerExtension_isConvex {p : ℝ} (hp : p ≤ 0) :
    ((fun x : ℝ ↦ Real.rpow x p).toWithBotTopOn (Set.Ioi (0 : ℝ))).IsConvex ℝ := by
  exact (isConvex_toWithBotTopOn_iff).2 (convexOn_rpow_Ioi_of_nonpos hp)

-- Proof sketch: if `α ≤ 0`, then `Ioo (-α) α` is empty, so `Function.toWithBotTopOn` is
-- identically `⊤`, which is convex. If `α > 0`, then on `(-α, α)` the
-- real-valued function `x ↦ (α^2 - x^2)^(-1/2)` has nonnegative second derivative; apply
-- `Theorem_4_4` on that open interval and then extend with
-- `isConvex_toWithBotTopOn_iff`.
/-- Example 4.4.1 (5): for every `α`, the function `x ↦ (α^2 - x^2)^(-1/2)` on `(-α, α)`
extended by `+∞` outside is convex. -/
theorem inverseSqrtGapExtension_isConvex (α : ℝ) :
    ((fun x : ℝ ↦ Real.rpow (α ^ 2 - x ^ 2) (-(1 / 2 : ℝ))).toWithBotTopOn
      (Set.Ioo (-α) α)).IsConvex ℝ := by
  by_cases hα : 0 < α
  · exact (isConvex_toWithBotTopOn_iff).2 (convexOn_inverseSqrtGap α hα)
  · have hempty : Set.Ioo (-α) α = ∅ := by
      ext x
      constructor
      · intro hx
        have : 0 < α := by linarith [hx.1, hx.2]
        exact (hα this).elim
      · intro hx
        exact False.elim hx
    have hconvEmpty :
        ConvexOn ℝ (Set.Ioo (-α) α)
          (fun x : ℝ ↦ Real.rpow (α ^ 2 - x ^ 2) (-(1 / 2 : ℝ))) := by
      refine ⟨?_, ?_⟩
      · simpa [hempty] using (convex_empty : Convex ℝ (∅ : Set ℝ))
      · intro x hx
        simp [hempty] at hx
    exact (isConvex_toWithBotTopOn_iff).2 hconvEmpty

-- Proof sketch: `strictConcaveOn_log_Ioi` gives concavity of `Real.log` on `(0, ∞)`, so negating
-- it yields convexity of `x ↦ -log x` there; then use
-- `isConvex_toWithBotTopOn_iff` for the extension by `+∞`.
/-- Example 4.4.1 (6): the function `x ↦ -log x` on `(0, ∞)` extended by `+∞` to `(-∞, 0]` is
convex. -/
theorem negLogExtension_isConvex :
    ((fun x : ℝ ↦ -Real.log x).toWithBotTopOn (Set.Ioi (0 : ℝ))).IsConvex ℝ := by
  have hconv : ConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ -Real.log x) := by
    convert strictConcaveOn_log_Ioi.concaveOn.neg using 1
  exact (isConvex_toWithBotTopOn_iff).2 hconv

end

/-! ### Definition_4_4 (from Chap01) -/
noncomputable section

universe u v

section

variable {E : Type u}
variable {α : Type v}
variable {β : Type v}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Definition 4.4 introduces the effective domain via epigraph projection.
- `core/canonical`: for any ordered codomain with top, the effective domain is
  intrinsically `{x | f x < ⊤}`.
- `bridge/view`: `effectiveDomain_eq_image_fst_epi` recovers the textbook projection
  description for `WithTopBot α` codomain, while the canonical codomain-lift owners
  `Function.toWithTopBot` and `Bifunction.toWithTopBot` now live in `Chap01.EOrder.Basic`
  (with backward-compatible aliases).

Domain-style sampling used here:
- the chapter epigraph owner `epi`;
- codomain ordered-top structure;
- `WithTop α` and its canonical coercion into `WithTopBot α`;
- the order-theoretic predicate `f x < ⊤`.

Primitive data vs derived API:
- primitive object: for a ordered codomain with top, the effective-domain set
  `{x | f x < ⊤}`;
- derived API: the epigraph-projection characterization through `epi` for `WithTopBot α`, the
  value-level bridge from `WithTop α` into `WithTopBot α`, the function-level bridges
  `Function.toWithTopBot` and `Bifunction.toWithTopBot`, and the
  `dom(·)` notation used downstream for that owner set.
-/

/-- Definition 4.4: the effective domain of a function into a codomain with `(<)` and top
is the
set of points where the function is strictly below `⊤`. -/
def effectiveDomain [LT β] [Top β] (f : E → β) : Set E :=
  {x | f x < ⊤}

/-- Rockafellar's notation for the effective domain of a function with `(<)` and top codomain
data. -/
notation "dom(" f ")" => effectiveDomain f

/-- Scalar-parameterized notation for the relative interior of the effective domain. -/
scoped[Rockafellar] notation "riDom[" 𝕜 "](" f ")" => intrinsicInterior 𝕜 dom(f)

/-- Rockafellar's notation for the relative interior of the effective domain. -/
scoped[Rockafellar] notation "riDom(" f ")" => intrinsicInterior ℝ dom(f)

open scoped Rockafellar

/-- The scalar-parameterized notation `riDom[𝕜](f)` unfolds to intrinsic interior of `dom(f)`. -/
@[simp] theorem riDom_eq_intrinsicInterior_dom [LT β] [Top β] {𝕜 : Type*} [Ring 𝕜]
    {V : Type*} {P : Type*} [AddCommGroup V] [Module 𝕜 V]
    [TopologicalSpace P] [AddTorsor V P] (f : P → β) :
    riDom[𝕜](f) = intrinsicInterior 𝕜 dom(f) :=
  rfl

/-- Membership in `riDom[𝕜](f)` is exactly membership in the intrinsic interior of `dom(f)`. -/
@[simp] theorem mem_riDom_iff [LT β] [Top β] {𝕜 : Type*} [Ring 𝕜]
    {V : Type*} {P : Type*}
    [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace P] [AddTorsor V P]
    {f : P → β} {x : P} :
    x ∈ riDom[𝕜](f) ↔ x ∈ intrinsicInterior 𝕜 dom(f) :=
  Iff.rfl

/-- Real-scalar notation `riDom(f)` is the `𝕜 = ℝ` specialization of `riDom[𝕜](f)`. -/
@[simp] theorem riDom_real_eq_intrinsicInterior_dom [LT β] [Top β]
    {V : Type*} {P : Type*}
    [AddCommGroup V] [Module ℝ V] [TopologicalSpace P] [AddTorsor V P]
    (f : P → β) :
    riDom(f) = intrinsicInterior ℝ dom(f) :=
  rfl

/-- Relative projection bridge: over a subset `S`, points of `S` in the effective domain are
exactly first coordinates of points in the restricted epigraph `epi[S] f`. -/
theorem effectiveDomain_inter_eq_image_fst_epi
    [Preorder α] [Nonempty α] (f : E → WithTopBot α)
    (S : Set E) :
    S ∩ dom(f) = Prod.fst '' (epi[S] f) := by
  ext x
  constructor
  · rintro ⟨hxS, hxdom⟩
    have hne_top : f x ≠ ⊤ := ne_of_lt hxdom
    by_cases hne_bot : f x = ⊥
    · rcases ‹Nonempty α› with ⟨μ⟩
      refine ⟨(x, μ), ?_, rfl⟩
      simp [hxS, hne_bot]
    · cases hfx : f x with
      | none => exact (hne_top hfx).elim
      | some y =>
          cases y with
          | bot => exact (hne_bot hfx).elim
          | coe a =>
              refine ⟨(x, a), ?_, rfl⟩
              refine (mem_epi_restrict_iff).2 ?_
              refine ⟨hxS, ?_⟩
              have hfx' : f x = (a : WithTopBot α) := by
                simpa using hfx
              exact hfx'.le
  · rintro ⟨⟨x', μ⟩, hμ, rfl⟩
    rcases (mem_epi_restrict_iff).1 hμ with ⟨hxS, hle⟩
    refine ⟨hxS, lt_of_le_of_lt hle ?_⟩
    simp

/-- The effective domain is the projection of the chapter epigraph owner onto the ambient space. -/
theorem effectiveDomain_eq_image_fst_epi
    [Preorder α] [Nonempty α] (f : E → WithTopBot α) :
    dom(f) = Prod.fst '' epi f := by
  simpa [Set.inter_comm] using
    (effectiveDomain_inter_eq_image_fst_epi (f := f) (S := Set.univ))

/-- A point belongs to the effective domain exactly when the function value is strictly below
`+∞`. -/
@[simp] theorem mem_effectiveDomain [LT β] [Top β] {f : E → β} {x : E} :
    x ∈ dom(f) ↔ f x < ⊤ :=
  Iff.rfl

/-- Helper for Definition 4.4: boundary-swapping negation on `WithTopBot α` lets the domain
statements for `-g` stay local to this item without importing the broken chapter wrapper. -/
local instance instNegWithTopBot [Neg α] : Neg (WithTopBot α) :=
  ⟨fun x =>
    match x with
    | ⊥ => ⊤
    | ⊤ => ⊥
    | (a : α) => (-a : α)⟩

/-- For `WithTopBot` codomain with negation, membership in `dom(-g)` is exactly strict
positivity of `g` above `-∞`. -/
@[simp] theorem mem_dom_neg_iff [Preorder α] [Neg α]
    {g : E → WithTopBot α} {x : E} :
    x ∈ dom(-g) ↔ ⊥ < g x := by
  change (-g x) < ⊤ ↔ ⊥ < g x
  by_cases htop : g x = ⊤
  · rw [htop]
    constructor
    · intro _
      change ((⊥ : WithBot α) : WithTop (WithBot α)) < (⊤ : WithTop (WithBot α))
      exact WithTop.coe_lt_top (⊥ : WithBot α)
    · intro _
      change ((⊥ : WithBot α) : WithTop (WithBot α)) < (⊤ : WithTop (WithBot α))
      exact WithTop.coe_lt_top (⊥ : WithBot α)
  · by_cases hbot : g x = ⊥
    · rw [hbot]
      constructor
      · intro hlt
        change (⊤ : WithTop (WithBot α)) < (⊤ : WithTop (WithBot α)) at hlt
        exact False.elim ((lt_irrefl (⊤ : WithTop (WithBot α))) hlt)
      · intro hlt
        change
          ((⊥ : WithBot α) : WithTop (WithBot α)) <
            ((⊥ : WithBot α) : WithTop (WithBot α)) at hlt
        exact False.elim ((lt_irrefl (((⊥ : WithBot α) : WithTop (WithBot α)))) hlt)
    · cases hgx : g x using WithBotTop.rec with
      | bot => exact (htop (by simpa using hgx)).elim
      | top => exact (hbot (by simpa using hgx)).elim
      | coe a =>
          constructor
          · intro _
            change
              ((⊥ : WithBot α) : WithTop (WithBot α)) <
                (((a : α) : WithBot α) : WithTop (WithBot α))
            exact WithTop.coe_lt_coe.2 (WithBot.bot_lt_coe a)
          · intro _
            change ((((-a : α) : WithBot α) : WithTop (WithBot α)) < (⊤ : WithTop (WithBot α)))
            exact WithTop.coe_lt_top (((-a : α) : WithBot α))

/-- Set form of `mem_dom_neg_iff`: the effective domain of `-g` is where `g` is strictly above
`-∞`. -/
theorem dom_neg_eq_setOf_bot_lt [Preorder α] [Neg α]
    (g : E → WithTopBot α) :
    dom(-g) = {x : E | ⊥ < g x} := by
  ext x
  exact mem_dom_neg_iff

/-- Relative epigraph bridge: restricting to `S ∩ dom(f)` is equivalent to restricting to `S`. -/
@[simp] theorem epigraph_inter_effectiveDomain_eq [Preorder α]
    (f : E → WithTopBot α)
    (S : Set E) :
    (epi[S ∩ dom(f)] f) = (epi[S] f) := by
  ext ⟨x, μ⟩
  constructor
  · intro h
    rw [mem_epi_restrict_iff] at h
    rw [mem_epi_restrict_iff]
    exact ⟨h.1.1, h.2⟩
  · intro hμ
    rw [mem_epi_restrict_iff] at hμ
    rw [mem_epi_restrict_iff]
    exact ⟨⟨hμ.1, (mem_effectiveDomain).2 (lt_of_le_of_lt hμ.2 (by simp))⟩, hμ.2⟩

/-- Restricting the epigraph of `f` to its effective domain does not change the epigraph. -/
@[simp] theorem epigraph_effectiveDomain_eq [Preorder α] (f : E → WithTopBot α) :
    (epi[dom(f)] f) = (epi f) := by
  simpa [Set.inter_comm] using
    (epigraph_inter_effectiveDomain_eq (f := f) (S := Set.univ))

end

/-! ### Theorem_4_4 (from Chap01) -/
section

open Set
open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-
Source/core/bridge triage:
- `source-facing`: Theorem 4.4 identifies convexity of a scalar-valued function on an open
  interval `(α, β)` with pointwise nonnegativity of its second derivative on that interval.
- `core/canonical`: the owner abstraction is first stated on an arbitrary open convex set
  `s : Set 𝕜`; the primary theorem surface is intrinsic/relative via
  `derivWithin (derivWithin f s) s`, with ambient `deriv^[2]` as an open-set bridge.
- `bridge/view`: the forward implication uses the owner-side monotonicity theorem
  `ConvexOn.monotoneOn_deriv`; the scalar-generic reverse implication uses
  `ConvexAnalysis.convexOn_of_deriv2_nonneg'`.
- Primitive data vs derived API: the primitive inputs are the interval endpoints `α, β` and the
  function `f : 𝕜 → 𝕜` together with differentiability of `f` and `deriv f` on `Ioo α β`;
  convexity on `Ioo α β` and the pointwise sign condition on
  `derivWithin (derivWithin f (Ioo α β)) (Ioo α β)` are the canonical equivalent views.
- Domain-style sampling: this item is aligned with
  `ConvexAnalysis.convexOn_of_deriv2_nonneg'`,
  `ConvexOn.monotoneOn_deriv`, `MonotoneOn.derivWithin_nonneg`, and
  `DifferentiableOn`.
- Layer target: mixed `core/canonical` plus `source-facing`; the theorem surface is scalar-general
  over ordered normed fields with the order completeness needed for the mean value theorem.
-/

/- Primitive local bridge: if `s` is a neighborhood of `x`, the intrinsic second derivative
agrees at `x` with ambient `deriv^[2]`. -/
theorem derivWithin2_eq_deriv2_of_mem_nhds {s : Set 𝕜} {f : 𝕜 → 𝕜} {x : 𝕜}
    (hs_nhds : s ∈ 𝓝 x) :
    derivWithin (derivWithin f s) s x = deriv^[2] f x := by
  rcases mem_nhds_iff.mp hs_nhds with ⟨t, ht_sub, ht_open, hxt⟩
  have ht_nhds : t ∈ 𝓝 x := ht_open.mem_nhds hxt
  have hderivWithin_eq_deriv : derivWithin f s =ᶠ[𝓝 x] deriv f := by
    filter_upwards [ht_nhds] with y hy
    exact derivWithin_of_mem_nhds <|
      Filter.mem_of_superset (ht_open.mem_nhds hy) ht_sub
  calc
    derivWithin (derivWithin f s) s x = deriv (derivWithin f s) x :=
      derivWithin_of_mem_nhds hs_nhds
    _ = deriv (deriv f) x := hderivWithin_eq_deriv.deriv_eq
    _ = deriv^[2] f x := by simp [Function.iterate_succ_apply']

/- Open-set pointwise bridge, derived from the primitive local neighborhood form. -/
theorem IsOpen.derivWithin2_eq_deriv2 {s : Set 𝕜} {f : 𝕜 → 𝕜}
    (hs_open : IsOpen s) {x : 𝕜} (hx : x ∈ s) :
    derivWithin (derivWithin f s) s x = deriv^[2] f x :=
  derivWithin2_eq_deriv2_of_mem_nhds (hs_open.mem_nhds hx)

section OrderedDiff

variable [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜]

private lemma convexOn_derivWithin_le_slope_generic {s : Set 𝕜} {f : 𝕜 → 𝕜} {x y f' : 𝕜}
    (hconv : ConvexOn 𝕜 s f) (hx : x ∈ s) (hy : y ∈ s) (hxy : x < y)
    (hf' : HasDerivWithinAt f f' s x) :
    f' ≤ slope f x y := by
  apply le_of_tendsto <| (hasDerivWithinAt_iff_tendsto_slope' (show x ∉ Ioi x by simp)).mp <|
    hf'.mono_of_mem_nhdsWithin <| hconv.1.ordConnected.mem_nhdsGT hx hy hxy
  simp_rw [eventually_nhdsWithin_iff, slope_def_field]
  filter_upwards [eventually_lt_nhds hxy] with t ht ht'
  refine hconv.secant_mono hx (?_ : t ∈ s) hy ht'.ne' hxy.ne' ht.le
  exact hconv.1.ordConnected.out hx hy ⟨ht'.le, ht.le⟩

private lemma convexOn_slope_le_derivWithin_generic {s : Set 𝕜} {f : 𝕜 → 𝕜} {x y f' : 𝕜}
    (hconv : ConvexOn 𝕜 s f) (hx : x ∈ s) (hy : y ∈ s) (hxy : x < y)
    (hf' : HasDerivWithinAt f f' s y) :
    slope f x y ≤ f' := by
  apply ge_of_tendsto <| (hasDerivWithinAt_iff_tendsto_slope' (show y ∉ Iio y by simp)).mp <|
    hf'.mono_of_mem_nhdsWithin <| hconv.1.ordConnected.mem_nhdsLT hx hy hxy
  simp_rw [eventually_nhdsWithin_iff, slope_comm f x y, slope_def_field]
  filter_upwards [eventually_gt_nhds hxy] with t ht ht'
  refine hconv.secant_mono hy hx (?_ : t ∈ s) hxy.ne ht'.ne ht.le
  exact hconv.1.ordConnected.out hx hy ⟨ht.le, ht'.le⟩

private lemma convexOn_monotoneOn_derivWithin_generic {s : Set 𝕜} {f : 𝕜 → 𝕜}
    (hconv : ConvexOn 𝕜 s f) (hfd : DifferentiableOn 𝕜 f s) :
    MonotoneOn (derivWithin f s) s := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with rfl | hxy'
  · rfl
  exact (convexOn_derivWithin_le_slope_generic hconv hx hy hxy' (hfd x hx).hasDerivWithinAt).trans
    (convexOn_slope_le_derivWithin_generic hconv hx hy hxy' (hfd y hy).hasDerivWithinAt)

/-- Intrinsic second-derivative monotonicity on a convex set: if `f` is convex and differentiable
on `s`, then the relative second derivative `derivWithin (derivWithin f s) s` is pointwise
nonnegative on `s`. -/
theorem ConvexOn.nonneg_derivWithin2 {s : Set 𝕜} {f : 𝕜 → 𝕜}
    (hconv : ConvexOn 𝕜 s f) (hfd : DifferentiableOn 𝕜 f s) :
    ∀ x ∈ s, 0 ≤ derivWithin (derivWithin f s) s x := by
  have hmono : MonotoneOn (derivWithin f s) s := convexOn_monotoneOn_derivWithin_generic hconv hfd
  intro x hx
  exact hmono.derivWithin_nonneg

/-- On an open set, the intrinsic second-derivative condition from
`ConvexOn.nonneg_derivWithin2` specializes to the ambient second derivative `deriv^[2]`. -/
theorem ConvexOn.nonneg_deriv2_of_isOpen {s : Set 𝕜} {f : 𝕜 → 𝕜}
    (hconv : ConvexOn 𝕜 s f) (hs_open : IsOpen s) (hfd : DifferentiableOn 𝕜 f s) :
    ∀ x ∈ s, 0 ≤ deriv^[2] f x := by
  have hmonoWithin : MonotoneOn (derivWithin f s) s :=
    convexOn_monotoneOn_derivWithin_generic hconv hfd
  have hmono : MonotoneOn (deriv f) s := by
    intro x hx y hy hxy
    rw [← derivWithin_of_isOpen hs_open hx, ← derivWithin_of_isOpen hs_open hy]
    exact hmonoWithin hx hy hxy
  intro x hx
  have hnonneg : 0 ≤ derivWithin (deriv f) s x := hmono.derivWithin_nonneg
  simpa [derivWithin_of_isOpen hs_open hx, Function.iterate_succ_apply'] using hnonneg

/-
On an open set, nonnegativity of the intrinsic second derivative is equivalent to
nonnegativity of the ambient second derivative.
-/
omit [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜] in
theorem IsOpen.nonneg_derivWithin2_iff_nonneg_deriv2 {s : Set 𝕜} {f : 𝕜 → 𝕜}
    (hs_open : IsOpen s) :
    (∀ x ∈ s, 0 ≤ derivWithin (derivWithin f s) s x) ↔ ∀ x ∈ s, 0 ≤ deriv^[2] f x := by
  constructor <;> intro h x hx
  · simpa [derivWithin2_eq_deriv2_of_mem_nhds (f := f) (hs_open.mem_nhds hx)] using h x hx
  · simpa [derivWithin2_eq_deriv2_of_mem_nhds (f := f) (hs_open.mem_nhds hx)] using h x hx

end OrderedDiff

section OrderedConvex

variable [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜]
  [DenselyOrdered 𝕜]

/-- Open-set owner criterion at the intrinsic/relative layer: on an open convex set, a function
with `DifferentiableOn` hypotheses for both `f` and `deriv f` is convex iff
`derivWithin (derivWithin f s) s` is pointwise nonnegative. -/
theorem IsOpen.convexOn_iff_nonneg_derivWithin2 {s : Set 𝕜} {f : 𝕜 → 𝕜}
    (hs_open : IsOpen s) (hs_convex : Convex 𝕜 s)
    (hfd : DifferentiableOn 𝕜 f s) (hderiv : DifferentiableOn 𝕜 (deriv f) s) :
    ConvexOn 𝕜 s f ↔ ∀ x ∈ s, 0 ≤ derivWithin (derivWithin f s) s x := by
  constructor
  · intro hconv
    exact hconv.nonneg_derivWithin2 hfd
  · intro hnonneg
    have hnonneg_deriv2 : ∀ x ∈ s, 0 ≤ deriv^[2] f x := by
      simpa [hs_open.nonneg_derivWithin2_iff_nonneg_deriv2] using hnonneg
    exact ConvexAnalysis.convexOn_of_deriv2_nonneg'
      hs_convex hfd hderiv hnonneg_deriv2

/-- Open-set ambient bridge: the intrinsic owner criterion
`IsOpen.convexOn_iff_nonneg_derivWithin2` specializes to ambient `deriv^[2]`. -/
theorem IsOpen.convexOn_iff_nonneg_deriv2 {s : Set 𝕜} {f : 𝕜 → 𝕜}
    (hs_open : IsOpen s) (hs_convex : Convex 𝕜 s)
    (hfd : DifferentiableOn 𝕜 f s) (hderiv : DifferentiableOn 𝕜 (deriv f) s) :
    ConvexOn 𝕜 s f ↔ ∀ x ∈ s, 0 ≤ deriv^[2] f x := by
  simpa [hs_open.nonneg_derivWithin2_iff_nonneg_deriv2] using
    (hs_open.convexOn_iff_nonneg_derivWithin2 hs_convex hfd hderiv)

-- Proof sketch: apply the owner-level open-convex-set intrinsic criterion with `s = Ioo α β`.
/-- Theorem 4.4 at the intrinsic/relative owner layer: a twice differentiable scalar-valued
function on `(α, β)` is convex on that interval iff
`derivWithin (derivWithin f (Ioo α β)) (Ioo α β)` is pointwise nonnegative. -/
theorem convexOn_Ioo_iff_nonneg_derivWithin2 {α β : 𝕜} {f : 𝕜 → 𝕜}
    (hfd : DifferentiableOn 𝕜 f (Ioo α β))
    (hderiv : DifferentiableOn 𝕜 (deriv f) (Ioo α β)) :
    ConvexOn 𝕜 (Ioo α β) f ↔
      ∀ x ∈ Ioo α β, 0 ≤ derivWithin (derivWithin f (Ioo α β)) (Ioo α β) x := by
  simpa using
    (isOpen_Ioo.convexOn_iff_nonneg_derivWithin2 (convex_Ioo α β) hfd hderiv)

/-- Theorem 4.4 ambient bridge: on the open interval `(α, β)`, the intrinsic second-derivative
criterion is equivalent to pointwise nonnegativity of `deriv^[2]`. -/
theorem convexOn_Ioo_iff_nonneg_deriv2 {α β : 𝕜} {f : 𝕜 → 𝕜}
    (hfd : DifferentiableOn 𝕜 f (Ioo α β))
    (hderiv : DifferentiableOn 𝕜 (deriv f) (Ioo α β)) :
    ConvexOn 𝕜 (Ioo α β) f ↔ ∀ x ∈ Ioo α β, 0 ≤ deriv^[2] f x := by
  simpa using
    (isOpen_Ioo.convexOn_iff_nonneg_deriv2 (convex_Ioo α β) hfd hderiv)

end OrderedConvex

end

/-! ### Remark_4_4_5 (from Chap01) -/
noncomputable section

attribute [local instance] Classical.propDecidable

open scoped Rockafellar
open scoped Pointwise
open Function

universe u v w

/-!
Source/core/bridge triage for this item.

- `source-facing`: Remark 4.4.5 identifies a convex function on a set `C` with the globally
  defined `WithTopBot α`-valued function obtained by adjoining `+∞` outside `C`.
- `core/canonical`: the owner abstractions are the chapter predicate `Function.IsConvex` for the
  ambient `WithTopBot α`-valued function, mathlib's `ConvexOn` for the finite branch on `C`, and
  `Set.piecewise` as the intrinsic two-branch extension owner.
- `bridge/view`: the source-facing bridge is `f.toWithTopBot + δ(· | C)`, and the chapter helper
  owner `Function.toWithTopBotOn f C` is a thin alias to the canonical
  `C.piecewise f.toWithTopBot ⊤` surface.

Domain-style sampling used here:
- `Function.IsConvex` and `Function.isConvex_iff_convex_epigraph` from `Theorem_4_2`;
- `Function.toWithTopBot` from `Chap01.EOrder.Basic`;
- `indicator` and the notation `δ(· | C)` from `Defintion_4_8_1`;
- `Set.piecewise` as the canonical owner for total two-branch functions;
- mathlib's `ConvexOn` and `convexOn_iff_convex_epigraph`.

Primitive data vs derived API:
- primitive data: a set `C : Set E` and an `α`-valued function `f : E → α`;
- derived API: the source-facing bridge `f.toWithTopBot + δ(· | C)`, the helper owner
  `Function.toWithTopBotOn f C`, and the equivalence between global-owner convexity and convexity
  of `f` on `C`.

Layer target: `core/canonical` with `source-facing` bridge; the primary theorem below uses the
canonical `Set.piecewise` owner, while `Function.toWithTopBotOn` and the source formula
`f.toWithTopBot + δ(· | C)` are kept as thin bridges.
-/

section

variable {E : Type u}
variable {α : Type v}

namespace Function

/-- Helper for Remark 4.4.5: the canonical codomain lift views a finite-valued map as
`WithTopBot`-valued. -/
abbrev toWithTopBot (f : E → α) : E → WithTopBot α :=
  fun x ↦ (f x : WithTopBot α)

/-- Canonical owner for extension by `+∞` outside `C`. -/
def toWithTopBotOn (f : E → α) (C : Set E) : E → WithTopBot α :=
  C.piecewise f.toWithTopBot ⊤

/-- Backward-compatible alias for `Function.toWithTopBotOn`. -/
abbrev toWithBotTopOn (f : E → α) (C : Set E) : E → WithTopBot α :=
  f.toWithTopBotOn C

@[simp] theorem toWithTopBotOn_of_mem (f : E → α) (C : Set E) {x : E} (hx : x ∈ C) :
    f.toWithTopBotOn C x = f x := by
  simp [toWithTopBotOn, hx, Function.toWithTopBot]

@[simp] theorem toWithTopBotOn_of_notMem (f : E → α) (C : Set E) {x : E} (hx : x ∉ C) :
    f.toWithTopBotOn C x = (⊤ : WithTopBot α) := by
  simp [toWithTopBotOn, hx]

/-- Backward-compatible `WithBotTop`-spelled bridge for `toWithTopBotOn_of_mem`. -/
@[simp] theorem toWithBotTopOn_of_mem (f : E → α) (C : Set E) {x : E} (hx : x ∈ C) :
    f.toWithBotTopOn C x = f x := by
  simpa using (toWithTopBotOn_of_mem (f := f) (C := C) hx)

/-- Backward-compatible `WithBotTop`-spelled bridge for `toWithTopBotOn_of_notMem`. -/
@[simp] theorem toWithBotTopOn_of_notMem (f : E → α) (C : Set E) {x : E} (hx : x ∉ C) :
    f.toWithBotTopOn C x = (⊤ : WithTopBot α) := by
  simpa using (toWithTopBotOn_of_notMem (f := f) (C := C) hx)

end Function

section

variable [AddZeroClass α]

namespace Function

-- Proof sketch: unfold `δ(x | C)` and `C.piecewise`, then split on `x ∈ C`. On `C`, the
-- indicator contributes `0`, so the sum reduces to the finite branch `f x`; outside `C`, the
-- indicator contributes `⊤`, so the whole function is `⊤`.
/-- Adding the indicator of `C` to an `α`-valued branch `f` gives the canonical two-branch
function that agrees with `f` on `C` and is `+∞` outside `C`. -/
theorem toWithTopBot_add_indicator_eq_piecewise (f : E → α) (C : Set E) :
    f.toWithTopBot + (δ[α](· | C)) = C.piecewise f.toWithTopBot ⊤ := by
  -- Split on membership in `C`; on-set the indicator is `0`, off-set it is `⊤`.
  funext x
  by_cases hx : x ∈ C <;> simp [hx, Function.toWithTopBot]

/-- Backward-compatible `WithBotTop`-spelled bridge for
`toWithTopBot_add_indicator_eq_piecewise`. -/
theorem toWithBotTop_add_indicator_eq_piecewise (f : E → α) (C : Set E) :
    f.toWithTopBot + (δ[α](· | C)) = C.piecewise f.toWithTopBot ⊤ := by
  simpa using (toWithTopBot_add_indicator_eq_piecewise (f := f) (C := C))

end Function

end

section

variable [AddZeroClass α]

/-- The source-facing `f + δ(· | C)` expression is the canonical extension by `+∞` outside
`C`. -/
theorem Function.toWithTopBotOn_eq_add_indicator (f : E → α) (C : Set E) :
    f.toWithTopBotOn C = f.toWithTopBot + (δ[α](· | C)) := by
  simpa [Function.toWithTopBotOn] using
    (Function.toWithTopBot_add_indicator_eq_piecewise (f := f) (C := C)).symm

/-- Backward-compatible `WithBotTop`-spelled bridge for
`Function.toWithTopBotOn_eq_add_indicator`. -/
theorem Function.toWithBotTopOn_eq_add_indicator (f : E → α) (C : Set E) :
    f.toWithBotTopOn C = f.toWithTopBot + (δ[α](· | C)) := by
  simpa using (Function.toWithTopBotOn_eq_add_indicator (f := f) (C := C))

end

section

variable {𝕜 : Type w} [Semiring 𝕜] [PartialOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]
variable {α : Type v} [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α]
variable [SMul 𝕜 α] [PosSMulMono 𝕜 α]

/-- Helper for Remark 4.4.5: the finite-height epigraph of the canonical extension by `+∞`
outside `C` is exactly the ordinary epigraph of `f` restricted to `C`. -/
theorem piecewise_toWithTopBot_epigraph_eq {C : Set E} {f : E → α} :
    {p : E × α | (C.piecewise f.toWithTopBot ⊤) p.1 ≤ (p.2 : WithTopBot α)} =
      {p : E × α | p.1 ∈ C ∧ f p.1 ≤ p.2} := by
  -- Split on whether the base point lies in `C`; off-set the left inequality is impossible.
  ext p
  by_cases hp : p.1 ∈ C <;> simp [hp, Function.toWithTopBot]

/-- Helper for Remark 4.4.5: under the ordered scalar-action hypotheses used here, a convex
finite-height epigraph yields `ConvexOn` for the underlying finite-valued function. -/
theorem convexOn_of_convex_epigraph_of_pos_smul {C : Set E} {f : E → α}
    (h : Convex 𝕜 {p : E × α | p.1 ∈ C ∧ f p.1 ≤ p.2}) :
    ConvexOn 𝕜 C f := by
  -- Read convexity of the epigraph on the two canonical points `(x, f x)` and `(y, f y)`.
  refine ⟨?_, ?_⟩
  · intro x hx y hy a b ha hb hab
    exact (@h (x, f x) ⟨hx, le_rfl⟩ (y, f y) ⟨hy, le_rfl⟩ a b ha hb hab).1
  · intro x hx y hy a b ha hb hab
    exact (@h (x, f x) ⟨hx, le_rfl⟩ (y, f y) ⟨hy, le_rfl⟩ a b ha hb hab).2

/-- Helper for Remark 4.4.5: under the ordered scalar-action hypotheses used here, `ConvexOn`
forces convexity of the finite-height epigraph. -/
theorem ConvexOn.convex_epigraph_of_pos_smul {C : Set E} {f : E → α}
    (hf : ConvexOn 𝕜 C f) :
    Convex 𝕜 {p : E × α | p.1 ∈ C ∧ f p.1 ≤ p.2} := by
  -- Convex combinations in the epigraph stay above the convex combination of the function values.
  rintro ⟨x, r⟩ ⟨hx, hr⟩ ⟨y, t⟩ ⟨hy, ht⟩ a b ha hb hab
  refine ⟨hf.1 hx hy ha hb hab, ?_⟩
  calc
    f (a • x + b • y) ≤ a • f x + b • f y := hf.2 hx hy ha hb hab
    _ ≤ a • r + b • t := by
      gcongr

-- Proof sketch: rewrite both convexity statements to convexity of the same epigraph set via the
-- canonical piecewise owner.
/-- Canonical `Set.piecewise` extension bridge: convexity of the global extension by `+∞` outside
`C` is exactly convexity of the finite branch on `C`. -/
theorem isConvex_piecewise_toWithTopBot_iff {C : Set E} {f : E → α} :
    (C.piecewise f.toWithTopBot ⊤).IsConvex 𝕜 ↔ ConvexOn 𝕜 C f := by
  -- Route correction: pass each direction through the common finite-height epigraph set instead
  -- of trying to rewrite both sides of the equivalence at once.
  constructor
  · intro hpiecewise
    -- Convert global-owner convexity of the extension into convexity of its epigraph.
    have hepigraph :
        Convex 𝕜 {p : E × α | p.1 ∈ C ∧ f p.1 ≤ p.2} := by
      simpa [piecewise_toWithTopBot_epigraph_eq (C := C) (f := f)] using
        (Function.isConvex_iff_convex_epigraph
          (𝕜 := 𝕜) (f := C.piecewise f.toWithTopBot ⊤)).1 hpiecewise
    -- Repackage that same epigraph set as the standard `ConvexOn` owner on `C`.
    exact convexOn_of_convex_epigraph_of_pos_smul (𝕜 := 𝕜) (C := C) (f := f) hepigraph
  · intro hf
    -- Start from the ordinary epigraph of `f` on `C`.
    have hepigraph :
        Convex 𝕜 {p : E × α | (C.piecewise f.toWithTopBot ⊤) p.1 ≤ (p.2 : WithTopBot α)} := by
      simpa [piecewise_toWithTopBot_epigraph_eq (C := C) (f := f)] using
        (ConvexOn.convex_epigraph_of_pos_smul (𝕜 := 𝕜) (C := C) (f := f) hf)
    -- Package the rewritten epigraph back into the global-owner convexity statement.
    exact (Function.isConvex_iff_convex_epigraph
      (𝕜 := 𝕜) (f := C.piecewise f.toWithTopBot ⊤)).2 hepigraph

/-- Backward-compatible `WithBotTop`-spelled bridge for
`isConvex_piecewise_toWithTopBot_iff`. -/
theorem isConvex_piecewise_toWithBotTop_iff {C : Set E} {f : E → α} :
    (C.piecewise f.toWithTopBot ⊤).IsConvex 𝕜 ↔ ConvexOn 𝕜 C f := by
  simpa using (isConvex_piecewise_toWithTopBot_iff (𝕜 := 𝕜) (C := C) (f := f))

/-- Bridge form using the canonical owner `Function.toWithTopBotOn`. -/
theorem isConvex_toWithTopBotOn_iff {C : Set E} {f : E → α} :
    (f.toWithTopBotOn C).IsConvex 𝕜 ↔ ConvexOn 𝕜 C f := by
  simpa [Function.toWithTopBotOn] using
    (isConvex_piecewise_toWithTopBot_iff (C := C) (f := f))

/-- Backward-compatible `WithBotTop`-spelled bridge for
`isConvex_toWithTopBotOn_iff`. -/
theorem isConvex_toWithBotTopOn_iff {C : Set E} {f : E → α} :
    (f.toWithBotTopOn C).IsConvex 𝕜 ↔ ConvexOn 𝕜 C f := by
  simpa using (isConvex_toWithTopBotOn_iff (𝕜 := 𝕜) (C := C) (f := f))

/-- Remark 4.4.5: viewing an `α`-valued function on `C` as the globally defined
`WithTopBot α`-valued function `f.toWithTopBot + δ(· | C)` preserves convexity exactly. This is
the owner-level identification between convexity on a fixed set and convexity of the canonical
extension by `+∞` outside that set. -/
theorem isConvex_toWithTopBot_add_indicator_iff {C : Set E} {f : E → α} :
    (f.toWithTopBot + (δ[α](· | C))).IsConvex 𝕜 ↔ ConvexOn 𝕜 C f := by
  -- Rewrite the source-facing formula to the canonical piecewise owner.
  rw [Function.toWithTopBot_add_indicator_eq_piecewise (f := f) (C := C)]
  exact isConvex_piecewise_toWithTopBot_iff (𝕜 := 𝕜) (C := C) (f := f)

/-- Backward-compatible `WithBotTop`-spelled bridge for
`isConvex_toWithTopBot_add_indicator_iff`. -/
theorem isConvex_toWithBotTop_add_indicator_iff {C : Set E} {f : E → α} :
    (f.toWithTopBot + (δ[α](· | C))).IsConvex 𝕜 ↔ ConvexOn 𝕜 C f := by
  simpa using (isConvex_toWithTopBot_add_indicator_iff (𝕜 := 𝕜) (C := C) (f := f))

end

/-! ### Remark_4_4_7 (from Chap01) -/
/- 
Source/core/bridge triage:
- `source-facing`: Remark 4.4.7 fixes the book-wide convention that a "convex function" is
  globally defined on the ambient space (the source `R^n` wording is a specialization).
- `core/canonical`: the owner predicate for this global convention is
  `ConvexOn 𝕜 (Set.univ : Set E) f`; the chapter owner for the implicit domain convention is
  `effectiveDomain` with membership theorem `mem_effectiveDomain`.
- `bridge/view`: the remark's comment that the effective domain is implicit from the formula for
  `f` is mediated by the chapter's canonical domain owner `dom(f)`, rather than by introducing a
  second local wrapper around finiteness.
- Primitive data vs derived API: the primitive object is a total function
  `f : E → WithTopBot α`; the convention "convex function" is represented by
  `ConvexOn 𝕜 Set.univ f`, and the
  implicit-domain observation is derived from `dom(f) = {x | f x < ⊤}` (with `EReal` recovered by
  specialization).
- Domain-style sampling used here: `ConvexOn`,
  `convexOn_iff_convex_epigraph`, `convexOn_withTopBot_iff_convex_epigraph`,
  `effectiveDomain`, and `mem_effectiveDomain`.
-/

/- Remark 4.4.7: throughout the book, a "convex function" means a globally defined convex
function (with source `R^n` / `EReal` language recovered by specialization); in this chapter the
source-facing owner predicate for that convention is `ConvexOn 𝕜 Set.univ`, with epigraph
convexity used as a bridge. -/
recall ConvexOn

/- The canonical bridge for the owner is convexity of the ordinary epigraph set. -/
recall convexOn_iff_convex_epigraph

/- Chapter bridge theorem specialized to the `WithTopBot` codomain owner layer. -/
recall convexOn_withTopBot_iff_convex_epigraph

/- The effective domain itself is the chapter's canonical owner for the implicit finiteness domain
of a globally defined function into an ordered codomain with top (including the source
`WithTopBot α` / `EReal` case). -/
recall effectiveDomain

/- The effective domain is read directly from the defining formula as the finiteness set
`dom(f) = {x | f x < ⊤}`. -/
recall mem_effectiveDomain

section

universe u v

variable {E : Type u}
variable {β : Type v} [LT β] [Top β]

/-- Set-level bridge form of the defining formula for the effective domain owner `dom(f)`. -/
@[simp] theorem dom_eq_setOf_lt_top (f : E → β) :
    dom(f) = {x | f x < ⊤} :=
  rfl

end

section

universe u v w

variable {𝕜 : Type w}
variable {E : Type u}
variable {α : Type v}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [SMul 𝕜 E]
variable [AddCommMonoid (WithTopBot α)] [PartialOrder (WithTopBot α)]
variable [IsOrderedAddMonoid (WithTopBot α)]
variable [Module 𝕜 (WithTopBot α)] [PosSMulMono 𝕜 (WithTopBot α)]

/-- Global-owner specialization for Remark 4.4.7: saying "`f` is convex" on the ambient space is
exactly the `Set.univ` instance of the canonical `ConvexOn` owner. -/
theorem convexOn_univ_withTopBot_iff_convex_epigraph (f : E → WithTopBot α) :
    ConvexOn 𝕜 (Set.univ : Set E) f ↔
      Convex 𝕜 {p : E × WithTopBot α | f p.1 ≤ p.2} := by
  simpa using
    (convexOn_withTopBot_iff_convex_epigraph (𝕜 := 𝕜) (C := (Set.univ : Set E)) (f := f))

end
