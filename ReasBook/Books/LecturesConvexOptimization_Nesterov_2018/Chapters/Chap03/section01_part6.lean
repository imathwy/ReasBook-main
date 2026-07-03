import Mathlib
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_3_1_5 (from Chap03) -/
noncomputable section

universe u

variable {X : Type u} [TopologicalSpace X] [AddCommMonoid X] [Module ℝ X]

/- Theorem 3.1.5 is the owner closure-calculus file for closed convex `WithTop ℝ`-valued
functions on feasible sets.

Primary domain:
- closed-convex extended-real-valued functions on real topological modules.

Sampled owner-style declarations in this domain:
- `ClosedConvexOn` from `Definition_3_1_1_5`
- mathlib `ConvexOn.smul`
- mathlib `ConvexOn.add`
- mathlib `ConvexOn.sup`

Best owner abstraction:
- source-facing owner: `ClosedConvexOn Q f`
- core/canonical supporting layer: `ConvexOn ℝ Q (withTopRealPart f)` together with the pointwise
  function operations `•`, `+`, and `⊔`

Primitive data:
- the owner witnesses `hf`, `hf₁`, `hf₂`
- the scalar `β` together with the nonnegativity hypothesis `0 ≤ β`

Derived API:
- the three closure theorems below

Source/core/bridge triage:
- source-facing: the scalar-multiple, sum, and pointwise-maximum closure rules recorded under
  Theorem 3.1.5
- core/canonical: `ClosedConvexOn` and the corresponding `ConvexOn` function operations
- bridge/view: `ClosedConvexOn.convexOn_withTopRealPart`, which transports the owner statement to
  the canonical convex-function surface

The public API therefore stays at the `ClosedConvexOn` owner level, but it uses the canonical
pointwise function owners where available instead of longer theorem-local lambda spellings.
-/

namespace ClosedConvexOn

/-- Theorem 3.1.5 (1): multiplying a closed convex function by a nonnegative scalar preserves
closedness and convexity on the same feasible set; the canonical pointwise owner is
`(β : WithTop ℝ) • f`. -/
-- Proof sketch: identify the constrained epigraph of `x ↦ β • f₁ x` with the epigraph of `f₁`
-- under the height rescaling by `β`; convexity is preserved by nonnegative scalar multiplication,
-- and closedness follows from continuity of the rescaling map.
theorem nonneg_smul
    {Q : Set X} {f : X → WithTop ℝ} {β : ℝ}
    (hf : ClosedConvexOn Q f) (hβ : 0 ≤ β) :
    ClosedConvexOn Q ((β : WithTop ℝ) • f) := sorry

/-- Theorem 3.1.5 (2): the sum of two closed convex functions is closed and convex on the
intersection of their feasible sets. -/
-- Proof sketch: restrict both functions to `Q₁ ∩ Q₂`; convexity is preserved by pointwise
-- addition, and closedness follows from the standard epigraph or lower-semicontinuity argument for
-- sums on a common feasible domain.
theorem add_inter
    {Q₁ Q₂ : Set X} {f₁ f₂ : X → WithTop ℝ}
    (hf₁ : ClosedConvexOn Q₁ f₁) (hf₂ : ClosedConvexOn Q₂ f₂) :
    ClosedConvexOn (Q₁ ∩ Q₂) (f₁ + f₂) := sorry

/-- Theorem 3.1.5 (3): the pointwise maximum of two closed convex functions is closed and convex
on the intersection of their feasible sets; the canonical pointwise owner is `f₁ ⊔ f₂`. -/
-- Proof sketch: the constrained epigraph of `f₁ ⊔ f₂` over `Q₁ ∩ Q₂` is the intersection of the
-- constrained epigraphs of `f₁` and `f₂`, and intersections preserve both closedness and
-- convexity.
theorem max_inter
    {Q₁ Q₂ : Set X} {f₁ f₂ : X → WithTop ℝ}
    (hf₁ : ClosedConvexOn Q₁ f₁) (hf₂ : ClosedConvexOn Q₂ f₂) :
    ClosedConvexOn (Q₁ ∩ Q₂) (f₁ ⊔ f₂) := sorry

end ClosedConvexOn

end

/-! ### Theorem_3_1_5_1 (from Chap03) -/
/- Theorem 3.1.5.1 is a recall-only surface in the chapter's extended-valued convex-
subdifferential domain.

Primary domain:
- convex analysis of `ℝ ∪ {+∞}`-valued functions on Euclidean space.

Sampled owner-style declarations:
- `dom` and `withTopRealPart` in `Definition_3_3`, the chapter owners for the effective domain
  and finite-value representative;
- `subdifferential` in `Definition_3_1_5`, the chapter owner for extended-valued subgradient
  sets;
- `subdifferential_nonempty_and_isBounded_of_convexOn_effectiveDomain_of_mem_interior` in
  `Theorem_3_1_15`, the canonical chapter theorem on this owner surface.

Best owner abstraction:
- `subdifferential_nonempty_and_isBounded_of_convexOn_effectiveDomain_of_mem_interior`.

Primitive data:
- none in this file; the theorem and its owner-level hypotheses already live upstream.

Derived API:
- this recall-only source-facing entry point.

Source/core/bridge triage:
- source-facing: Theorem 3.1.5.1's nonempty-and-bounded subdifferential statement;
- core/canonical: the upstream theorem in `Theorem_3_1_15` on the chapter owners
  `dom`, `withTopRealPart`, and `subdifferential`;
- bridge/view: this recall surface.

The previous file kept a second theorem stub with the same statement as the canonical upstream
theorem. This file now reuses that theorem directly instead of maintaining a parallel copy.
-/

recall subdifferential_nonempty_and_isBounded_of_convexOn_effectiveDomain_of_mem_interior

/-! ### Theorem_3_1_5_2 (from Chap03) -/
noncomputable section

open scoped ConvexAnalysis WithTopConvexAnalysis

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Theorem 3.1.5.2 lies in the chapter's Fenchel-biconjugacy domain.

Primary domain:
- Fenchel conjugates, biduals, and subdifferentials of `ℝ ∪ {+∞}`-valued functions on real
  inner-product spaces.

Sampled owner-style declarations:
- `fenchelConjugate` and `fenchelConjugate_apply` in `Chap06/Definition_6_1`, the core
  extended-real Fenchel-conjugate owner and its evaluation theorem;
- `fenchelDual` and `fenchelDual_apply` in `Definition_3_1_2_1`, the source-facing Fenchel-dual
  bridge owner and its supremum formula;
- `subdifferential` and the notation `∂ f(x)` in `Definition_3_1_5`, the chapter owner for
  extended-valued subgradients;
- `dom` in `Definition_3_1_1_2`, the effective-domain owner for `EReal`-valued functions.

Best owner abstraction:
- source-facing: `fenchelBidual`, written `f⋆⋆`;
- core/canonical: `fenchelConjugate`;
- bridge/view: evaluate `fenchelConjugate (f⋆)` along the Riesz map `innerₗ E`.

Primitive data:
- `f : E → WithTop ℝ`;
- the source-facing dual owner `f⋆`;
- the subdifferential owner `∂ f(x)`.

Derived API:
- the source-facing notation `f⋆⋆`;
- the unrestricted conjugate expansion of `(f⋆⋆) x`;
- the bridge theorem restricting that supremum to `dom (f⋆)` when `(dom f).Nonempty`;
- the three textbook theorem declarations on that notation surface.

Source/core/bridge triage:
- source-facing: Theorem 3.1.5.2's Fenchel-biconjugacy statements;
- core/canonical: `fenchelConjugate`;
- bridge/view: the bidual owner `fenchelBidual`, which packages the second Fenchel conjugate on
  the same source-facing inner-product-space surface.
-/

/-- The Fenchel bidual of an `ℝ ∪ {+∞}`-valued function on a real inner-product space. -/
abbrev fenchelBidual (f : E → WithTop ℝ) : E → EReal :=
  fenchelConjugate (f⋆) ∘ innerₗ E

/- Lean spelling `f⋆⋆` for the source-facing Fenchel bidual `fenchelBidual f`. -/
scoped[ConvexAnalysis] postfix:max "⋆⋆" => fenchelBidual

/-- Evaluating `fenchelBidual f` gives the unrestricted Fenchel-conjugate supremum formula. -/
theorem fenchelBidual_apply (f : E → WithTop ℝ) (x : E) :
    (f⋆⋆) x = ⨆ s : E, (inner ℝ s x : EReal) - (f⋆) s := by
  simpa [fenchelBidual, innerₗ_apply_apply, real_inner_comm] using
    fenchelConjugate_apply (f⋆) (innerₗ E x)

section

variable {f : E → WithTop ℝ}

/-- Helper for Theorem 3.1.5.2: on the effective domain of `f`, the `EReal` image of `f` is the
corresponding finite real value. -/
lemma withTopToEReal_eq_coe_withTopRealPart_of_mem_dom {y : E} (hy : y ∈ dom f) :
    withTopToEReal (f y) = (withTopRealPart f y : EReal) := by
  -- On `dom f`, coercing the finite real part back to `EReal` recovers the original value.
  simpa [withTopToEReal] using (congrArg withTopToEReal (coe_withTopRealPart hy)).symm

/-- Helper for Theorem 3.1.5.2: at a finite primal point, the `EReal` image of `f` is not
`⊤`. -/
lemma withTopToEReal_ne_top_of_mem_dom {y : E} (hy : y ∈ dom f) :
    withTopToEReal (f y) ≠ ⊤ := by
  rw [withTopToEReal_eq_coe_withTopRealPart_of_mem_dom (f := f) hy]
  exact EReal.coe_ne_top _

/-- Helper for Theorem 3.1.5.2: at a finite primal point, the `EReal` image of `f` is not
`⊥`. -/
lemma withTopToEReal_ne_bot_of_mem_dom {y : E} (hy : y ∈ dom f) :
    withTopToEReal (f y) ≠ ⊥ := by
  rw [withTopToEReal_eq_coe_withTopRealPart_of_mem_dom (f := f) hy]
  exact EReal.coe_ne_bot _

/-- Helper for Theorem 3.1.5.2: testing the Fenchel-dual supremum at a finite primal point gives
the canonical affine lower bound. -/
lemma fenchelDual_lower_bound_of_mem_dom {s y : E} (hy : y ∈ dom f) :
    (inner ℝ s y : EReal) - withTopToEReal (f y) ≤ (f⋆) s := by
  -- The point `y` is one admissible index in the domain-restricted supremum formula for `f⋆`.
  rw [fenchelDual_apply_eq_sSup_image_dom]
  exact le_sSup ⟨y, hy, rfl⟩

/-- Helper for Theorem 3.1.5.2: a finite primal point prevents the Fenchel dual from taking the
value `⊥`. -/
lemma fenchelDual_ne_bot_of_mem_dom {s y : E} (hy : y ∈ dom f) :
    (f⋆) s ≠ ⊥ := by
  -- Compare `f⋆ s` with the finite affine term contributed by `y`.
  have hlower := fenchelDual_lower_bound_of_mem_dom (f := f) (s := s) hy
  have hfinite : (⊥ : EReal) < (inner ℝ s y : EReal) - withTopToEReal (f y) := by
    rw [withTopToEReal_eq_coe_withTopRealPart_of_mem_dom (f := f) hy, ← EReal.coe_sub]
    exact EReal.bot_lt_coe _
  intro hbot
  rw [hbot] at hlower
  exact (not_lt_of_ge hlower) hfinite

/-- Helper for Theorem 3.1.5.2: once `dom f` is nonempty, any point outside `dom (f⋆)` contributes
`⊥` to the bidual maximand. -/
lemma fenchelBidual_maximand_eq_bot_of_not_mem_dom
    (hdom : (dom f).Nonempty) {s x : E} (hs : s ∉ dom (f⋆)) :
    ((inner ℝ s x : EReal) - (f⋆) s) = ⊥ := by
  -- A finite primal witness rules out `(f⋆) s = ⊥`, so outside `dom (f⋆)` the only remaining
  -- possibility is `(f⋆) s = ⊤`.
  rcases hdom with ⟨y, hy⟩
  have hdual_ne_bot : (f⋆) s ≠ ⊥ := fenchelDual_ne_bot_of_mem_dom (f := f) (s := s) hy
  have hs_top : (f⋆) s = ⊤ := by
    by_contra hs_ne_top
    exact hs ((mem_extendedRealEffectiveDomain_iff).2 ⟨hs_ne_top, hdual_ne_bot⟩)
  rw [hs_top, EReal.sub_top]

/-- Helper for Theorem 3.1.5.2: after discarding the `⊥` terms, the bidual supremum is indexed by
`dom (f⋆)`. -/
lemma iSup_fenchelBidual_maximand_eq_iSup_dom
    (hdom : (dom f).Nonempty) (x : E) :
    (⨆ s : E, (inner ℝ s x : EReal) - (f⋆) s) =
      ⨆ s : dom (f⋆), (inner ℝ s.1 x : EReal) - (f⋆) s.1 := by
  refine le_antisymm ?_ ?_
  · -- Every unrestricted term either comes from `dom (f⋆)` or is `⊥` outside that domain.
    refine iSup_le ?_
    intro s
    by_cases hs : s ∈ dom (f⋆)
    · exact le_iSup (fun t : dom (f⋆) ↦ (inner ℝ t.1 x : EReal) - (f⋆) t.1) ⟨s, hs⟩
    · rw [fenchelBidual_maximand_eq_bot_of_not_mem_dom (f := f) hdom hs]
      exact bot_le
  · -- Any point of `dom (f⋆)` is also an index in the unrestricted supremum.
    refine iSup_le ?_
    intro s
    exact le_iSup (fun t : E ↦ (inner ℝ t x : EReal) - (f⋆) t) s.1

-- Proof sketch: expand `fenchelBidual_apply`. If `dom f` is nonempty, then for every `s` the
-- term `(f⋆) s` is bounded below by one finite affine value, so `(f⋆) s ≠ ⊥`; points outside
-- `dom (f⋆)` therefore contribute only `⊥`, and the supremum may be restricted to `dom (f⋆)`.
/-- If `f` has a finite value somewhere, then the Fenchel-bidual supremum may be restricted to the
effective domain of the Fenchel dual. -/
theorem fenchelBidual_apply_eq_sSup_image_dom_of_dom_nonempty
    (hdom : (dom f).Nonempty) (x : E) :
    (f⋆⋆) x =
      sSup ((fun s : E ↦ (inner ℝ s x : EReal) - (f⋆) s) '' dom (f⋆)) := by
  calc
    (f⋆⋆) x = ⨆ s : E, (inner ℝ s x : EReal) - (f⋆) s := by
      -- Start from the unrestricted Fenchel-conjugate formula for the bidual.
      rw [fenchelBidual_apply]
    _ = ⨆ s : dom (f⋆), (inner ℝ s.1 x : EReal) - (f⋆) s.1 := by
      -- Restrict to `dom (f⋆)` because the complementary terms are `⊥`.
      rw [iSup_fenchelBidual_maximand_eq_iSup_dom (f := f) hdom x]
    _ = sSup (Set.range fun s : dom (f⋆) ↦ (inner ℝ s.1 x : EReal) - (f⋆) s.1) := by
      -- Convert the subtype-indexed supremum into the supremum over its range.
      rw [sSup_range]
    _ = sSup ((fun s : E ↦ (inner ℝ s x : EReal) - (f⋆) s) '' dom (f⋆)) := by
      -- Identify the subtype range with the image of the maximand on `dom (f⋆)`.
      congr 1
      ext z
      constructor
      · rintro ⟨s, rfl⟩
        exact ⟨s.1, s.2, rfl⟩
      · rintro ⟨s, hs, rfl⟩
        exact ⟨⟨s, hs⟩, rfl⟩

section

variable {x : E}

-- Proof sketch: use `fenchelBidual_apply_eq_sSup_image_dom_of_dom_nonempty ⟨x, hx⟩` to rewrite
-- `(f⋆⋆) x` as the supremum over `dom (f⋆)` of the affine terms `⟪s, x⟫ - f⋆(s)`, then expand
-- `f⋆(s)` as a supremum over `dom f` and test the defining supremum at `y = x`.
/-- Theorem 3.1.5.2 (1): for every `x ∈ dom f`, the Fenchel bidual is bounded above by the
original value `f x`. -/
theorem fenchelBidual_le_of_mem_dom
    (hx : x ∈ dom f) :
    (f⋆⋆) x ≤ withTopToEReal (f x) := by
  -- Rewrite the bidual as the supremum of the dual support terms over `dom (f⋆)`.
  rw [fenchelBidual_apply_eq_sSup_image_dom_of_dom_nonempty (f := f) ⟨x, hx⟩ x]
  refine sSup_le ?_
  rintro z ⟨s, hs, rfl⟩
  have hs_mem := mem_extendedRealEffectiveDomain_iff.mp hs
  have hsum : (inner ℝ s x : EReal) ≤ (f⋆) s + withTopToEReal (f x) := by
    -- Test the defining supremum of `f⋆ s` at the concrete primal point `x`.
    have hlower := fenchelDual_lower_bound_of_mem_dom (f := f) (s := s) hx
    exact (EReal.sub_le_iff_le_add (.inl (withTopToEReal_ne_bot_of_mem_dom (f := f) hx))
      (.inl (withTopToEReal_ne_top_of_mem_dom (f := f) hx))).1 hlower
  -- Rearranging that bound yields the desired estimate for this support term.
  exact EReal.sub_le_of_le_add' hsum

/-- Helper for Theorem 3.1.5.2: the subgradient inequality gives the standard upper bound on the
Fenchel dual at the subgradient. -/
lemma fenchelDual_le_subgradient_support_value {x g : E}
    (hg : g ∈ ∂ f(x)) :
    (f⋆) g ≤ (inner ℝ g x : EReal) - withTopToEReal (f x) := by
  have hsub : IsSubgradientAt f x g := mem_subdifferential_iff.mp hg
  have hx : x ∈ dom f := hsub.mem_dom
  rw [fenchelDual_apply_eq_sSup_image_dom]
  refine sSup_le ?_
  rintro z ⟨y, hy, rfl⟩
  have hineq : f y ≥ f x + (inner ℝ g (y - x) : WithTop ℝ) := hsub.2 hy
  have hineq_real : withTopRealPart f y ≥ withTopRealPart f x + inner ℝ g (y - x) := by
    -- On `dom f`, the `WithTop` inequality is an ordinary real inequality.
    have hineq' :
        (((withTopRealPart f y : ℝ) : WithTop ℝ) ≥
          ((withTopRealPart f x + inner ℝ g (y - x) : ℝ) : WithTop ℝ)) := by
      rw [WithTop.coe_add, coe_withTopRealPart hy, coe_withTopRealPart hx]
      simpa [ge_iff_le] using hineq
    exact_mod_cast hineq'
  have hinner : inner ℝ g y = inner ℝ g x + inner ℝ g (y - x) := by
    -- Expand `⟪g, y⟫` along the decomposition `y = x + (y - x)`.
    calc
      inner ℝ g y = inner ℝ g (x + (y - x)) := by simp
      _ = inner ℝ g x + inner ℝ g (y - x) := by rw [inner_add_right]
  have hreal : inner ℝ g y - withTopRealPart f y ≤ inner ℝ g x - withTopRealPart f x := by
    -- After moving to real coordinates, the subgradient inequality is exactly the desired bound.
    linarith
  -- Re-express both finite function values as real coefficients in `EReal`.
  simpa only [withTopToEReal_eq_coe_withTopRealPart_of_mem_dom (f := f) hx,
    withTopToEReal_eq_coe_withTopRealPart_of_mem_dom (f := f) hy,
    ← EReal.coe_sub] using (show
      ((inner ℝ g y - withTopRealPart f y : ℝ) : EReal) ≤
        ((inner ℝ g x - withTopRealPart f x : ℝ) : EReal) from by
      exact_mod_cast hreal)

-- Proof sketch: for any `g ∈ ∂ f(x)`, the subgradient inequality bounds every term
-- `⟪g, y⟫ - f y` by `⟪g, x⟫ - f x`, so the supremum defining `(f⋆) g` is finite and therefore
-- `g ∈ dom (f⋆)`.
/-- Theorem 3.1.5.2 (2): every subgradient at `x` belongs to the effective domain of the
Fenchel dual. -/
theorem subdifferential_subset_dom_fenchelDual :
    ∂ f(x) ⊆ dom (f⋆) := by
  intro g hg
  have hsub : IsSubgradientAt f x g := mem_subdifferential_iff.mp hg
  have hx : x ∈ dom f := hsub.mem_dom
  have hdual_ne_bot : (f⋆) g ≠ ⊥ := fenchelDual_ne_bot_of_mem_dom (f := f) (s := g) hx
  have hdual_le := fenchelDual_le_subgradient_support_value (f := f) (x := x) hg
  have hsupport_ne_top : ((inner ℝ g x : EReal) - withTopToEReal (f x)) ≠ ⊤ := by
    -- The support value is finite because `x ∈ dom f`.
    rw [withTopToEReal_eq_coe_withTopRealPart_of_mem_dom (f := f) hx, ← EReal.coe_sub]
    exact EReal.coe_ne_top _
  have hdual_ne_top : (f⋆) g ≠ ⊤ := by
    -- A value bounded above by a finite support term cannot be `⊤`.
    exact ne_of_lt (lt_of_le_of_lt hdual_le (lt_top_iff_ne_top.mpr hsupport_ne_top))
  exact (mem_extendedRealEffectiveDomain_iff).2 ⟨hdual_ne_top, hdual_ne_bot⟩

/-- Helper for Theorem 3.1.5.2: a subgradient witness gives the reverse support inequality needed
for the bidual equality. -/
lemma subgradient_support_term_ge_value {x g : E}
    (hg : g ∈ ∂ f(x)) :
    withTopToEReal (f x) ≤ (inner ℝ g x : EReal) - (f⋆) g := by
  have hsub : IsSubgradientAt f x g := mem_subdifferential_iff.mp hg
  have hx : x ∈ dom f := hsub.mem_dom
  have hg_dom : g ∈ dom (f⋆) := subdifferential_subset_dom_fenchelDual (f := f) (x := x) hg
  have hg_mem := mem_extendedRealEffectiveDomain_iff.mp hg_dom
  have hsupport := fenchelDual_le_subgradient_support_value (f := f) (x := x) hg
  -- Convert the upper bound on `f⋆ g` into the corresponding lower bound on the support term.
  rw [EReal.le_sub_iff_add_le (.inl hg_mem.2) (.inr (EReal.coe_ne_top _))]
  rw [EReal.le_sub_iff_add_le (.inl (withTopToEReal_ne_bot_of_mem_dom (f := f) hx))
    (.inl (withTopToEReal_ne_top_of_mem_dom (f := f) hx))] at hsupport
  simpa [add_comm] using hsupport

-- Proof sketch: part (1) gives `(f⋆⋆) x ≤ f x`. For any `g ∈ ∂ f(x)`, part (2) shows
-- `g ∈ dom (f⋆)`, and the subgradient inequality yields the reverse bound
-- `withTopToEReal (f x) ≤ (inner ℝ g x : EReal) - (f⋆) g ≤ (f⋆⋆) x`.
/-- Theorem 3.1.5.2 (3): if the subdifferential at `x` is nonempty, then the Fenchel bidual
agrees with the original value at `x`. -/
theorem fenchelBidual_eq_of_subdifferential_nonempty
    (hsub : (∂ f(x)).Nonempty) :
    (f⋆⋆) x = withTopToEReal (f x) := by
  rcases hsub with ⟨g, hg⟩
  have hx : x ∈ dom f := (mem_subdifferential_iff.mp hg).mem_dom
  have hupper : (f⋆⋆) x ≤ withTopToEReal (f x) := fenchelBidual_le_of_mem_dom (f := f) hx
  have hg_dom : g ∈ dom (f⋆) := subdifferential_subset_dom_fenchelDual (f := f) (x := x) hg
  have hsupport : withTopToEReal (f x) ≤ (inner ℝ g x : EReal) - (f⋆) g :=
    subgradient_support_term_ge_value (f := f) (x := x) hg
  have hterm : (inner ℝ g x : EReal) - (f⋆) g ≤ (f⋆⋆) x := by
    -- The subgradient witness contributes one admissible term to the bidual supremum.
    rw [fenchelBidual_apply_eq_sSup_image_dom_of_dom_nonempty (f := f) ⟨x, hx⟩ x]
    exact le_sSup ⟨g, hg_dom, rfl⟩
  exact le_antisymm hupper (hsupport.trans hterm)

end

end

end

/-! ### Theorem_3_1_5_3 (from Chap03) -/
/- Theorem 3.1.5.3 is a recall-only surface in the chapter's convex directional-derivative /
subdifferential domain.

Primary domain:
- finite directional derivatives of convex `ℝ ∪ {+∞}`-valued functions at interior points of
  their effective domains.

Relevant owner-style declarations sampled before refinement:
- `convexDirectionalDerivative` in `Theorem_3_21`, the chapter owner for the extended-valued
  directional derivative;
- the inline coercion
  `fun p ↦ ((((convexDirectionalDerivative f x0 p).toReal : ℝ) : WithTop ℝ))` used in
  `Theorem_3_21` for the subdifferential-at-the-origin comparison;
- `subdifferential` in `Definition_3_1_5`, the chapter owner for subgradients of
  `WithTop ℝ`-valued functions;
- `convexDirectionalDerivativeReal_isGreatest_subgradientPairing_of_mem_interior` in
  `Theorem_3_21`, the canonical max-formula theorem on that owner surface.

Best owner abstraction:
- `convexDirectionalDerivativeReal_isGreatest_subgradientPairing_of_mem_interior`.

Primitive data:
- none in this file; the directional-derivative construction and the supporting subdifferential
  API already live upstream in `Theorem_3_21`.

Derived API:
- this recall-only source-facing entry point for the textbook max formula.

Source/core/bridge triage:
- source-facing: Theorem 3.1.5.3's statement that `f'(x₀; p)` is the maximum of
  `⟪g, p⟫` over `g ∈ ∂f(x₀)`;
- core/canonical: `convexDirectionalDerivative` together with the owner theorem
  `convexDirectionalDerivativeReal_isGreatest_subgradientPairing_of_mem_interior`;
- bridge/view: this file's numbered recall surface.

The previous file duplicated the secant-slope construction, the finite directional derivative, its
`WithTop ℝ` lift, and two owner theorems that already exist in `Theorem_3_21`. The refined file
reuses the chapter owner theorem directly and deletes the parallel local API.
-/

/- Theorem 3.1.5.3: at an interior point of the effective domain of a convex
`ℝ ∪ {+∞}`-valued function, the finite directional derivative in direction `p` is the maximum of
the pairings `⟪g, p⟫` over all subgradients `g ∈ ∂f(x₀)`. -/
recall convexDirectionalDerivativeReal_isGreatest_subgradientPairing_of_mem_interior

/-! ### Theorem_3_1_5_4 (from Chap03) -/
open scoped WithTopConvexAnalysis

universe u

/- Theorem 3.1.5.4 is a recall-only surface in the chapter's convex directional-derivative and
subdifferential domain.

Primary domain:
- directional derivatives and subdifferentials of convex `ℝ ∪ {+∞}`-valued functions on real
  normed and inner-product spaces.

Relevant owner-style declarations sampled before refinement:
- `convexDirectionalDerivative` in `Theorem_3_21`, the chapter owner for the extended-valued
  directional derivative at a finite base point;
- `convexDirectionalDerivativeReal_convexOn_univ_of_mem_interior` in `Theorem_3_21`, the convexity
  theorem for the finite interior-point directional derivative;
- `subdifferential` in `Definition_3_1_5`, the chapter owner for subgradients, with notation
  `∂ f(x)`;
- `subdifferential_convexDirectionalDerivativeReal_at_zero_eq_subdifferential` and
  `convexDirectionalDerivativeReal_isGreatest_subgradientPairing_of_mem_interior` in
  `Theorem_3_21`, the canonical comparison and max-formula theorems for that owner surface.

Best owner abstraction:
- the finite directional-derivative owner `f′[hx0]`, derived in `Theorem_3_21` from the
  extended-valued owner `convexDirectionalDerivative`.

Primitive data:
- none in this file; the directional-derivative and subdifferential owners already live upstream.

Derived API:
- the convexity of `f′[hx0]` on all directions;
- the identity `∂₂ f′(x₀; 0) = ∂ f(x₀)`;
- the max formula for `f′(x₀; p)` over the subdifferential.

Source/core/bridge triage:
- source-facing: the three textbook clauses of Theorem 3.1.5.4;
- core/canonical: `convexDirectionalDerivative`, `f′[hx0]`, and `∂ f(x0)`;
- bridge/view: this recall-only item file.

The textbook states the theorem for proper convex functions on `ℝⁿ`. In the chapter API, the
properness content is absorbed by the effective-domain owner `dom f` and the interior hypothesis
`x0 ∈ interior (dom f)`, while the ambient space is generalized to the natural real normed or
inner-product setting. This file therefore recalls the exact upstream owner theorems rather than
introducing a second parallel theorem vocabulary.
-/

section DirectionalDerivative

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Theorem 3.1.5.4 (1): if `f` is convex on its effective domain and `x₀` lies in the interior of
that domain, then the directional derivative `p ↦ f′(x₀; p)` is a finite convex function on all
directions. The finiteness is built into the recalled owner surface `f′[hx0] : E → ℝ`. -/
recall convexDirectionalDerivativeReal_convexOn_univ_of_mem_interior

end DirectionalDerivative

section Subdifferential

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Theorem 3.1.5.4 (2): the subdifferential with respect to the direction variable of
`p ↦ f′(x₀; p)` at `0` equals the subdifferential of `f` at `x₀`. -/
recall subdifferential_convexDirectionalDerivativeReal_at_zero_eq_subdifferential

/- Theorem 3.1.5.4 (3): for every direction `p`, the directional derivative `f′(x₀; p)` is the
maximum of the pairings `⟪g, p⟫` over `g ∈ ∂ f(x₀)`, recorded in the owner API as an
`IsGreatest` statement. -/
recall convexDirectionalDerivativeReal_isGreatest_subgradientPairing_of_mem_interior

end Subdifferential

/-! ### Theorem_3_1_5_5 (from Chap03) -/
/- Theorem 3.1.5.5 is a recall-only item in the chapter's extended-valued convex-analysis /
subgradient / supporting-hyperplane domain.

Primary domain:
- subgradients of `ℝ ∪ {+∞}`-valued functions on real inner-product spaces and their
  supporting-hyperplane consequences for sublevel sets.

Relevant owner-style declarations sampled before refinement:
- `IsSubgradientAt` and `subdifferential` in `Definition_3_1_5`
- `IsSupportingHyperplane` in `Definition_3_1_4_1`
- `subgradient_nonpos_on_sublevelSet_of_mem_subdifferential`
- `subgradient_isSupportingHyperplane_sublevelSet_of_mem_subdifferential`

Best owner abstraction:
- the subdifferential owner API `g ∈ subdifferential f x0`, with supporting-hyperplane data derived
  through `IsSupportingHyperplane`.

Primitive data:
- an extended-valued function `f`, a base point `x0`, and a subgradient vector `g`
- the owner membership hypothesis `g ∈ subdifferential f x0`
- the nonvanishing hypothesis `g ≠ 0` for the supporting-hyperplane conclusion

Derived API:
- the sublevel-set inequality `⟪g, x - x0⟫ ≤ 0`
- the supporting-hyperplane conclusion for `{x | f x ≤ f x0}`

Source/core/bridge triage:
- source-facing: the sublevel-set support consequence of a subgradient at `x0`
- core/canonical: the owner subdifferential API and the hyperplane-support owner
  `IsSupportingHyperplane`
- bridge/view: none needed here beyond direct recall of the existing owner-based theorems

This file previously duplicated the subgradient inequality and supporting-hyperplane conclusion by
storing the owner predicate data in unpacked form (`hx0` together with the affine lower-support
family `hg`). The chapter already has the canonical owner-based statements in `Theorem_3_22`, and
the duplicate local theorem names had no downstream users. With `Theorem_3_22` now lifted from the
Euclidean model layer to the intrinsic real-inner-product-space owner layer, this file recalls the
canonical theorems directly instead of keeping a parallel wrapper API around `subdifferential`. -/

/- Theorem 3.1.5.5: every subgradient `g ∈ ∂f(x₀)` is a supporting vector to the sublevel set
`{x | f x ≤ f x₀}`, equivalently `⟪g, x - x₀⟫ ≤ 0` for every point of that set. -/
recall subgradient_nonpos_on_sublevelSet_of_mem_subdifferential

/- A nonzero subgradient at `x₀` yields a supporting hyperplane to the sublevel set
`{x | f x ≤ f x₀}`. -/
recall subgradient_isSupportingHyperplane_sublevelSet_of_mem_subdifferential

/-! ### Theorem_3_1_5_6 (from Chap03) -/
noncomputable section

open scoped WithTopConvexAnalysis

universe u

/- Theorem 3.1.5.6 lies in the chapter's extended-valued convex-analysis / subdifferential domain.

Relevant owner-style declarations sampled before refinement:
- `IsSubgradientAt`
- `subdifferential`
- `mem_subdifferential_iff`
- `isMinOn_iff`

Best owner abstraction:
- the subdifferential owner `subdifferential`, derived from `IsSubgradientAt`
- the minimizer owner `IsMinOn`

Primitive data:
- a feasible set `Q`, an extended-real objective `f`, points `x0`, `xStar`, `g`
- the feasibility hypothesis `hx0 : x0 ∈ Q`
- the minimizing hypothesis `hxStar : IsMinOn f Q xStar`
- the owner-membership hypothesis `hg : g ∈ ∂ f(x0)`

Derived API:
- `x0 ∈ dom f`, extracted from `hg`
- `xStar ∈ dom f`, extracted from `hxStar` and `hg`
- the real inequality obtained by comparing the subgradient lower-support bound with the minimizer
  inequality

Source/core/bridge triage:
- source-facing: the minimizer-pairing theorem stated in the textbook
- core/canonical: `subdifferential` / `IsSubgradientAt` and `IsMinOn`
- bridge/view: the passage from `IsMinOn f Q xStar` to the sublevel inequality `f xStar ≤ f x0`

The textbook states the result on `ℝⁿ`, but the theorem itself only uses the inner-product-space
owner abstractions. This file therefore removes the unnecessary Euclidean wrapper and proves the
source-facing statement directly from the canonical owner data. -/

variable {V : Type u} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Theorem 3.1.5.6: if `xStar` minimizes `f` on `Q` and `x0 ∈ Q`, then every subgradient
`g ∈ ∂f(x0)` has nonnegative pairing with the displacement `x0 - xStar`. -/
-- Proof sketch: extract the owner subgradient inequality from `hg` and evaluate it at `xStar`.
-- Since `xStar` minimizes `f` on `Q` and `x0 ∈ Q`, we have `f xStar ≤ f x0`, so the owner
-- sublevel-set inequality applies directly at `xStar`.
theorem subgradient_inner_sub_nonneg_of_isMinOn
    {Q : Set V} {f : V → WithTop ℝ} {x0 xStar g : V}
    (hx0 : x0 ∈ Q) (hxStar : IsMinOn f Q xStar) (hg : g ∈ ∂ f(x0)) :
    0 ≤ inner ℝ g (x0 - xStar) := by
  exact
    subgradient_nonneg_on_sublevelSet_of_mem_subdifferential hg
      ((isMinOn_iff.mp hxStar) x0 hx0)

end

/-! ### Theorem_3_1_5_7 (from Chap03) -/
/- Theorem 3.1.5.7 is a recall-only surface in the chapter's extended-valued convex-analysis /
common-subdifferential domain.

Relevant owner-style declarations sampled before refinement:
- `commonRegularSubdifferential` and `mem_commonRegularSubdifferential_iff` in
  `Definition_3_1_5_4`
- `eq_add_inner_of_mem_commonRegularSubdifferential` in `Theorem_3_1_19`
- `map_segment_eq_of_commonRegularSubdifferential_nonempty` in `Theorem_3_1_19`

Best owner abstraction:
- the intrinsic common-regular-subdifferential owner theorems in `Theorem_3_1_19`,
  now stated on arbitrary real inner-product spaces rather than only on the Euclidean model

Primitive data:
- none in this file; the common-subgradient owner objects and both source-facing consequences
  already live upstream

Derived API:
- this numbered recall surface for the affine-increment identity and the affine-on-segments
  consequence

Source/core/bridge triage:
- source-facing: the textbook consequences of a nonempty common regular subdifferential
- core/canonical: `commonRegularSubdifferential` together with the owner theorems
  `eq_add_inner_of_mem_commonRegularSubdifferential` and
  `map_segment_eq_of_commonRegularSubdifferential_nonempty`
- bridge/view: this numbered recall surface

The previous version duplicated the affine-increment theorem with the same public name as the
upstream owner theorem and added a second renamed segment-affinity theorem carrying extra unused
hypotheses. The owner theorems also used to be fixed to `EuclideanSpace ℝ (Fin n)`, even though
their owner notion `commonRegularSubdifferential` is already intrinsic. Since there are no
downstream users of the duplicate local names, this file now reuses the generalized canonical
owner theorems directly instead of maintaining either a parallel wrapper API or a Euclidean-only
recall surface. -/

/- Theorem 3.1.5.7: every common subgradient `g ∈ ∂̂ f(X)` gives the affine increment formula
`f x₁ = f x₀ + ⟪g, x₁ - x₀⟫` on `X`. -/
recall eq_add_inner_of_mem_commonRegularSubdifferential

/- If the common regular subdifferential of a convex function on `X` is nonempty, then the
function is affine on every segment contained in `X`. -/
recall map_segment_eq_of_commonRegularSubdifferential_nonempty

/-! ### Theorem_3_1_5_8 (from Chap03) -/
open scoped ConstrainedArgmin WithTopConvexAnalysis

/- This item is a recall-only surface in the chapter's extended-valued
convex-analysis minimizer/common-subdifferential domain.

Primary domain:
- effective-domain minimizers of `WithTop ℝ`-valued convex functions and their
  common-subdifferential optimality criterion.

Relevant owner-style declarations sampled before refinement:
- `IsMinOn` and `isMinOn_iff` in mathlib, the canonical minimizer predicate on a set;
- `subdifferential` in `Definition_3_1_5`, the chapter owner for extended-valued subgradients;
- `commonRegularSubdifferential` in `Definition_3_1_5_4`, the chapter owner for common
  subdifferentials;
- `constrainedArgmin` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the canonical
  minimizer-set owner on a feasible set;
- `subset_constrainedArgmin_effectiveDomain_iff_zero_mem_commonRegularSubdifferential` in
  `Theorem_3_1_20`, the upstream chapter theorem for this exact source-facing optimality
  statement.

Best owner abstraction:
- `argmin[dom f] f` together with
  `subset_constrainedArgmin_effectiveDomain_iff_zero_mem_commonRegularSubdifferential`.

Primitive data:
- an extended-valued function `f`;
- a set `XStar`.

Derived API:
- the minimizer-set owner `argmin[dom f] f`;
- its atomic membership theorem `mem_constrainedArgmin_iff`;
- the zero-common-subgradient optimality criterion.

Source/core/bridge triage:
- source-facing: the textbook optimality criterion for a set of global minimizers;
- core/canonical: `argmin[dom f] f` together with the theorem in `Theorem_3_1_20`;
- bridge/view: this numbered recall surface.

The previous file duplicated a local owner `globalMinimizers` for the canonical minimizer set
`argmin[dom f] f`, together with a parallel membership theorem and the same
zero-common-subgradient criterion. Chapter 3 already has the canonical theorem surface in
`Theorem_3_1_20`, so this file now reuses that owner directly instead of maintaining a parallel
Euclidean-only wrapper API. -/

universe u

section MinimizersRecall

variable {V : Type u} (f : V → WithTop ℝ) (x : V)

/- The set `arg min_{x ∈ dom f} f(x)` is the canonical owner `argmin[dom f] f`. -/
set_option linter.hashCommand false in
#check (argmin[dom f] f : Set V)

/- Membership in `argmin[dom f] f` is exactly effective-domain membership together
with minimizing on that domain. -/
set_option linter.hashCommand false in
#check (show x ∈ argmin[dom f] f ↔ x ∈ dom f ∧ IsMinOn f (dom f) x from
  mem_constrainedArgmin_iff)

end MinimizersRecall

section CommonSubdifferentialRecall

variable {V : Type u}
variable [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]

/- Theorem 3.1.5.8: if `X^* := argmin[dom f] f`, then `XStar ⊆ X^*` if and only if the zero
vector lies in the common regular subdifferential `∂̂ f(XStar)`. The source-side assumptions that
`XStar` is nonempty, closed, convex, and contained in `dom f` are redundant for this equivalence,
so the canonical recall surface states the exact owner theorem without them. -/
recall subset_constrainedArgmin_effectiveDomain_iff_zero_mem_commonRegularSubdifferential
    {f : V → WithTop ℝ} {XStar : Set V} :
    XStar ⊆ argmin[dom f] f ↔ (0 : V) ∈ ∂̂ f(XStar)

end CommonSubdifferentialRecall

/-! ### Corollary_3_1_6 (from Chap03) -/
/- Corollary 3.1.6 is a recall-only item in the chapter's convex-analysis/subdifferential domain.

Sampled owner-style declarations:
- `subdifferential`
- `mem_subdifferential_iff`
- `subgradient_nonneg_on_sublevelSet_of_mem_subdifferential`
- `subgradient_inner_sub_nonneg_of_isMinOn`

Best owner abstraction:
- the canonical subdifferential owner API together with the owner theorem
  `subgradient_nonneg_on_sublevelSet_of_mem_subdifferential`

Primitive data:
- a set `Q`, a function `f`, points `x0`, `xStar`, `g`
- the membership hypothesis `x0 ∈ Q`
- the minimizer hypothesis `IsMinOn f Q xStar`
- the subdifferential-membership hypothesis `g ∈ subdifferential f x0`

Derived API:
- the pairing inequality `0 ≤ inner ℝ g (x0 - xStar)`

Source/core/bridge triage:
- source-facing: the corollary that every subgradient at a feasible point has nonnegative pairing
  with the displacement to a minimizer
- core/canonical: the subdifferential owner API and the owner theorem
  `subgradient_nonneg_on_sublevelSet_of_mem_subdifferential`
- bridge/view: the existing chapter theorem `subgradient_inner_sub_nonneg_of_isMinOn`, which
  already has the exact corollary interface

This item therefore keeps only the direct recall of that source-facing bridge theorem instead of
introducing a second local wrapper around the owner abstraction. -/

recall subgradient_inner_sub_nonneg_of_isMinOn

/-! ### Definition_3_1_6 (from Chap03) -/
open scoped WithTopConvexAnalysis

universe u

/- Definition 3.1.6 is a recall-only item in the chapter's common-subdifferential domain.

Primary domain:
- convex analysis of extended-real-valued functions on real inner-product spaces.

Sampled owner-style declarations:
- `subdifferential`, the pointwise owner for subgradients
- `commonRegularSubdifferential`, the canonical owner for the intersection of pointwise
  subdifferentials over a set
- `mem_commonRegularSubdifferential_iff`, the membership bridge for that owner

Best owner abstraction:
- `commonRegularSubdifferential`

Primitive data inside the owner abstraction:
- an extended-real-valued function `f`
- a set `X`

Derived API:
- the textbook notation `∂̂ f(X)`
- the membership expansion `g ∈ ∂̂ f(X) ↔ ∀ x ∈ X, g ∈ ∂ f(x)`

Source/core/bridge triage:
- source-facing: the epigraph facet of `X` with respect to `f`
- core/canonical: `commonRegularSubdifferential f X`
- bridge/view: `mem_commonRegularSubdifferential_iff`

The textbook defines the epigraph facet for a closed convex set `X ⊆ dom f`, but those extra
hypotheses are not primitive data for the underlying owner. This file therefore reuses the
existing common-subdifferential owner directly rather than introducing a new synonym or keeping a
Euclidean-coordinate wrapper. -/

section

/- Definition 3.1.6: for a closed convex set `X ⊆ dom f`, the epigraph facet of `X` with respect
to `f` is the common regular subdifferential `∂̂ f(X) = ⋂ x ∈ X, ∂ f(x)`. -/
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

/-! ### Theorem_3_1_6 (from Chap03) -/
noncomputable section

variable {m n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Eₘ" => EuclideanSpace ℝ (Fin m)

namespace ClosedConvexOn

/- Theorem 3.1.6 lies in the chapter's closed-convex affine-pullback calculus.

Primary domain:
- closed convex `WithTop ℝ`-valued functions on Euclidean spaces and affine pullbacks.

Sampled owner-style declarations in this domain:
- `ClosedConvexOn` from `Definition_3_1_1_5`
- `ClosedConvexOn.comp_continuousAffineMap` from `Theorem_3_1_2_2`
- `ClosedConvexOn.comp_affineMap` from `Theorem_3_1_2_2`
- mathlib `ConvexOn.comp_affineMap`

Best owner abstraction:
- `ClosedConvexOn.comp_affineMap`

Primitive data:
- the owner witness `hφ : ClosedConvexOn S φ`
- the linear part `A`
- the translation vector `b`

Derived API:
- the affine map `A.toAffineMap +ᵥ AffineMap.const ℝ Eₙ b`
- the source-facing bridge theorem `ClosedConvexOn.comp_linearMap_add`

Source/core/bridge triage:
- source-facing: the textbook `x ↦ A x + b` specialization
- core/canonical: `ClosedConvexOn.comp_affineMap`
- bridge/view: the affine-map package of `A` and `b`

The boundedness hypothesis from the textbook statement is mathematically redundant for closed
convexity under affine precomposition, so the refined theorem reuses the earlier owner theorem
directly and keeps only the linear-plus-translation source surface.
-/

/-- Theorem 3.1.6: if `φ` is closed and convex on `S ⊆ ℝᵐ`, then the composition
`x ↦ φ (A x + b)` is closed and convex on the inverse image
`{x ∈ ℝⁿ | A x + b ∈ S}`. -/
-- Proof sketch: package `x ↦ A x + b` as an affine map and apply the owner theorem
-- `ClosedConvexOn.comp_affineMap`.
theorem comp_linearMap_add
    {S : Set Eₘ} {φ : Eₘ → WithTop ℝ}
    (hφ : ClosedConvexOn S φ)
    (A : Eₙ →ₗ[ℝ] Eₘ) (b : Eₘ) :
    ClosedConvexOn {x : Eₙ | A x + b ∈ S} (fun x ↦ φ (A x + b)) := by
  simpa using hφ.comp_affineMap (A.toAffineMap +ᵥ AffineMap.const ℝ Eₙ b)

end ClosedConvexOn

end

/-! ### Corollary_3_1_7 (from Chap03) -/
open scoped BigOperators

universe u v

/- Corollary 3.1.7 lies in finite-family whole-space convex analysis.

Primary domain:
- finite log-sum-exp convexity on a real module.

Sampled owner-style declarations:
- mathlib `ConvexOn`, the canonical owner for convexity on a set;
- mathlib `convex_univ`, the canonical whole-space convex-domain theorem;
- mathlib `LinearMap.convexOn`, a standard source of whole-space convex examples;
- project `convexOn_log_sum_exp_of_convexOn`, the chapter owner theorem on a common domain.

Best owner abstraction:
- source-facing: the whole-space finite log-sum-exp convexity statement;
- core/canonical: `convexOn_log_sum_exp_of_convexOn`;
- bridge/view: specialization of the common-domain owner theorem to `Set.univ`.

Primitive data:
- a finite index set `t : Finset ι`;
- a family `f : ι → E → ℝ`;
- whole-space convexity of each member `f i`.

Derived API:
- convexity of `x ↦ log (∑ i ∈ t, exp (f i x))` on `Set.univ`.

The previous file-level theorem was only the `Set.univ` specialization of the owner theorem, with
no extra mathematical content. This file therefore keeps only the direct owner-level specialization
check instead of a parallel local theorem name.
-/

variable {ι : Type u} {E : Type v} [AddCommMonoid E] [Module ℝ E]

/- Corollary 3.1.7 is the whole-space specialization of the chapter owner theorem
`convexOn_log_sum_exp_of_convexOn`. -/
#check
  (show ∀ {t : Finset ι} {f : ι → E → ℝ},
      t.Nonempty →
      (∀ i ∈ t, ConvexOn ℝ Set.univ (f i)) →
      ConvexOn ℝ Set.univ (fun x ↦ Real.log (∑ i ∈ t, Real.exp (f i x))) from
    convexOn_log_sum_exp_of_convexOn Set.univ)

/-! ### Definition_3_1_7 (from Chap03) -/
noncomputable section

universe u v

variable {E : Type u} {F : Type v} [SMul NNReal E] [SMul ℝ F]

/-
Definition 3.1.7 is source-facing in the chapter's positive-homogeneity API.

Primary domain:
- positively homogeneous functions on a cone.

Relevant owner-style declarations sampled before refinement:
- `SubMulAction NNReal E`
- `SMulMemClass.smul_mem`
- `Real.rpow`
- `IsPositivelyHomogeneousOn p (dom f) (withTopRealPart f)` in `Theorem_3_1_21`

Best owner abstraction for the cone data:
- `SubMulAction NNReal E`

Primitive data:
- a cone-shaped domain `s : Set E`
- a real degree `p`
- a map `f : E → F`

Derived API:
- the closure field `IsPositivelyHomogeneousOn.smul_mem`
- the scaling law `IsPositivelyHomogeneousOn.map_smul`

Source/core/bridge triage:
- source-facing: `IsPositivelyHomogeneousOn p s f`
- core/canonical: `SubMulAction NNReal E`
- bridge/view: the specialization `IsPositivelyHomogeneousOn p (dom f) (withTopRealPart f)` in
  `Theorem_3_1_21`
-/
/-- Definition 3.1.7: a function on a cone is positively homogeneous of degree `p` when its
domain is closed under nonnegative scalar multiplication and scaling the input by a bundled
nonnegative scalar `τ : NNReal` scales the value by `τ ^ p`. -/
class IsPositivelyHomogeneousOn (p : ℝ) (s : Set E) (f : E → F) : Prop where
  /-- A positively homogeneous function has a domain closed under nonnegative scalar
  multiplication. -/
  smul_mem {x : E} (hx : x ∈ s) (τ : NNReal) : τ • x ∈ s
  /-- A positively homogeneous function satisfies the prescribed nonnegative scaling identity on
  its domain. -/
  map_smul {x : E} (hx : x ∈ s) (τ : NNReal) :
    f (τ • x) = Real.rpow (τ : ℝ) p • f x

end

/-! ### Lemma_3_1_7 (from Chap03) -/
open scoped Gradient Topology
open Filter

noncomputable section

universe u

open scoped WithTopConvexAnalysis

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-
Lemma 3.1.7 lies in the chapter's extended-valued convex-analysis / subdifferential-calculus
domain on real inner-product spaces.

Sampled owner-style declarations:
- `withTopEffectiveDomain` in `Definition_3_3`, the chapter owner for the finite-value domain;
- `withTopRealPart` in `Definition_3_3`, the canonical real-valued representative on that domain;
- `ConvexOn ℝ (dom f) (withTopRealPart f)` in `Definition_3_3`, the owner convexity surface;
- `subdifferential` in `Definition_3_1_5`, the owner set-valued subgradient API.

Best owner abstraction:
- source-facing: the singleton-subdifferential theorem below;
- core/canonical: `withTopEffectiveDomain`, `withTopRealPart`,
  `ConvexOn ℝ (dom f) (withTopRealPart f)`, and
  `subdifferential`;
- bridge/view: none beyond the theorem statement itself.

Primitive data:
- the ambient `WithTop ℝ`-valued function `f`;
- the base point `x`;
- convexity on the canonical owner surface;
- interior-point membership in the effective domain;
- the primitive gradient witness `HasGradientAt (withTopRealPart f) g x`.

Derived API:
- `subdifferential_eq_singleton_of_hasGradientAt`;
- `subdifferential_eq_singleton_gradient`.

The previous version duplicated the effective-domain, finite-real-part, convexity, and
subdifferential definitions locally. Those notions already have chapter owners upstream, so this
file states the source-facing theorem directly on that owner API instead of maintaining a
parallel wrapper layer. The textbook writes the result on `ℝⁿ`, but the owner declarations used
here only need a complete real inner-product space, and the scalar cannot be weakened away from
`ℝ` because both `gradient` and the chapter subgradient API are formulated through the real inner
product pairing.
-/

/-- Helper for Lemma 3.1.7: convexity along the line segment from `x` to `y` turns the gradient at
`x` into the expected affine support inequality at every point of the effective domain. -/
lemma gradient_support_inequality_of_hasGradientAt
    {f : E → WithTop ℝ} (hf : ConvexOn ℝ (dom f) (withTopRealPart f)) {x : E}
    (hx : x ∈ interior (dom f)) {g : E}
    (hgrad : HasGradientAt (withTopRealPart f) g x) :
    ∀ ⦃y : E⦄, y ∈ dom f →
      withTopRealPart f y ≥ withTopRealPart f x + inner ℝ g (y - x) := by
  intro y hy
  let line : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x y
  let S : Set ℝ := line ⁻¹' dom f
  let φ : ℝ → ℝ := fun α ↦ withTopRealPart f (x + α • (y - x))
  have hline_apply (α : ℝ) : line α = x + α • (y - x) := by
    simpa [line, sub_eq_add_neg, add_smul, smul_add, add_assoc, add_left_comm, add_comm] using
      (AffineMap.lineMap_apply_module x y α)
  have hconv : ConvexOn ℝ S φ := by
    -- Restrict the ambient convex function to the affine line through `x` and `y`.
    have hconvLine : ConvexOn ℝ S (withTopRealPart f ∘ line) := by
      simpa [S, Function.comp] using hf.comp_affineMap line
    convert hconvLine using 1
    ext α
    simp [φ, Function.comp, hline_apply]
  have hzero_mem : (0 : ℝ) ∈ S := by
    simpa [S, hline_apply] using interior_subset hx
  have hone_mem : (1 : ℝ) ∈ S := by
    simpa [S, hline_apply] using hy
  have hline :
      HasLineDerivAt ℝ (withTopRealPart f) (inner ℝ g (y - x)) x (y - x) := by
    -- The gradient witness identifies the derivative of the scalar slice at the left endpoint.
    simpa [hgrad.fderiv_apply] using hgrad.hasFDerivAt.hasLineDerivAt (y - x)
  have hderiv :
      HasDerivWithinAt φ (inner ℝ g (y - x)) (Set.Ioi (0 : ℝ)) 0 := by
    have hderivLineAt :
        HasDerivAt
          (fun α : ℝ ↦ withTopRealPart f (x + α • (y - x)))
          (inner ℝ g (y - x)) 0 := by
      simpa using hline
    have hderivLine :
        HasDerivWithinAt
          (fun α : ℝ ↦ withTopRealPart f (x + α • (y - x)))
          (inner ℝ g (y - x)) (Set.Ioi (0 : ℝ)) 0 :=
      hderivLineAt.hasDerivWithinAt
    simpa [φ] using hderivLine
  have hslope :
      inner ℝ g (y - x) ≤ withTopRealPart f y - withTopRealPart f x := by
    -- A convex scalar slice stays above every secant line issued from the right derivative.
    simpa [φ, slope_def_field] using
      hconv.le_slope_of_hasDerivWithinAt_Ioi hzero_mem hone_mem zero_lt_one hderiv
  linarith

/-- Helper for Lemma 3.1.7: the displayed gradient belongs to the subdifferential at the interior
point because its affine support inequality holds on the effective domain. -/
lemma gradient_mem_subdifferential_of_hasGradientAt
    {f : E → WithTop ℝ} (hf : ConvexOn ℝ (dom f) (withTopRealPart f)) {x : E}
    (hx : x ∈ interior (dom f)) {g : E}
    (hgrad : HasGradientAt (withTopRealPart f) g x) :
    g ∈ ∂ f(x) := by
  -- Convert the real supporting inequality into the owner-level `WithTop` subgradient condition.
  refine mem_subdifferential_iff.mpr ?_
  constructor
  · exact interior_subset hx
  · intro y hy
    have hsupport :=
      gradient_support_inequality_of_hasGradientAt hf hx hgrad hy
    rw [← coe_withTopRealPart hy, ← coe_withTopRealPart (interior_subset hx)]
    exact_mod_cast hsupport

/-- Helper for Lemma 3.1.7: any subgradient at the interior point has pairing at most the pairing
of the true gradient against every direction. -/
lemma inner_le_inner_gradient_of_mem_subdifferential_of_hasGradientAt
    {f : E → WithTop ℝ} {x g h : E}
    (hx : x ∈ interior (dom f))
    (hgrad : HasGradientAt (withTopRealPart f) g x)
    (hh : h ∈ ∂ f(x)) :
    ∀ p : E, inner ℝ h p ≤ inner ℝ g p := by
  intro p
  have hx_dom : x ∈ dom f := interior_subset hx
  have hhsub := mem_subdifferential_iff.mp hh
  have hline_grad : HasLineDerivAt ℝ (withTopRealPart f) (inner ℝ g p) x p := by
    -- Read the Fréchet gradient as the derivative of the one-dimensional slice in direction `p`.
    simpa [hgrad.fderiv_apply] using hgrad.hasFDerivAt.hasLineDerivAt p
  have hpath : Tendsto (fun α : ℝ ↦ x + α • p) (𝓝[>] (0 : ℝ)) (𝓝 x) := by
    have hcont : ContinuousAt (fun α : ℝ ↦ x + α • p) (0 : ℝ) := by
      fun_prop
    simpa [nhdsWithin, zero_smul] using hcont.tendsto.mono_left inf_le_left
  have hdom : ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), x + α • p ∈ dom f := by
    -- Interior points keep the whole ray inside the effective domain for small positive times.
    exact (hpath.eventually (IsOpen.mem_nhds isOpen_interior hx)).mono fun α hα ↦
      interior_subset hα
  have hlim :
      Tendsto (fun α : ℝ ↦ (withTopRealPart f (x + α • p) - withTopRealPart f x) / α)
        (𝓝[>] (0 : ℝ)) (𝓝 (inner ℝ g p)) := by
    simpa [div_eq_mul_inv, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
      hline_grad.tendsto_slope_zero_right
  have hineq :
      ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ),
        inner ℝ h p ≤ (withTopRealPart f (x + α • p) - withTopRealPart f x) / α := by
    filter_upwards [hdom, self_mem_nhdsWithin] with α hαdom hαpos
    have hsubineq :
        f (x + α • p) ≥ f x + (inner ℝ h (x + α • p - x) : WithTop ℝ) :=
      hhsub.2 hαdom
    have hreal :
        withTopRealPart f (x + α • p) ≥ withTopRealPart f x + α * inner ℝ h p := by
      rw [← coe_withTopRealPart hαdom, ← coe_withTopRealPart hx_dom] at hsubineq
      have hinner : inner ℝ h (x + α • p - x) = α * inner ℝ h p := by
        simp [inner_smul_right]
      rw [hinner] at hsubineq
      exact_mod_cast hsubineq
    have hdiff : α * inner ℝ h p ≤ withTopRealPart f (x + α • p) - withTopRealPart f x := by
      linarith
    rw [div_eq_mul_inv]
    exact (le_div_iff₀ hαpos).2 (by simpa [mul_comm] using hdiff)
  exact tendsto_le_of_eventuallyLE tendsto_const_nhds hlim hineq

/-- Helper for Lemma 3.1.7: every subgradient at the interior point agrees with the true
gradient, obtained by comparing the support inequality in directions `p` and `-p`. -/
lemma eq_gradient_of_mem_subdifferential_of_hasGradientAt
    {f : E → WithTop ℝ} {x g h : E}
    (hx : x ∈ interior (dom f))
    (hgrad : HasGradientAt (withTopRealPart f) g x)
    (hh : h ∈ ∂ f(x)) :
    h = g := by
  -- Equality of all inner products forces equality in the ambient real inner-product space.
  apply ext_inner_right ℝ
  intro p
  have hpos :
      inner ℝ h p ≤ inner ℝ g p :=
    inner_le_inner_gradient_of_mem_subdifferential_of_hasGradientAt hx hgrad hh p
  have hneg : inner ℝ h p ≥ inner ℝ g p := by
    -- Apply the same one-sided comparison to `-p` and use linearity of the inner product.
    have hneg' :
        inner ℝ h (-p) ≤ inner ℝ g (-p) :=
      inner_le_inner_gradient_of_mem_subdifferential_of_hasGradientAt hx hgrad hh (-p)
    simpa using hneg'
  linarith

/-- Core owner form of Lemma 3.1.7: if a convex extended-real-valued function on a complete real
inner-product space has gradient `g` at an interior point of its effective domain, then its
subdifferential there is the singleton `{g}`. -/
-- Proof sketch: convexity and the explicit gradient witness at `x` give the supporting-plane
-- inequality with slope `g`, so `g` lies in the subdifferential. For the reverse inclusion,
-- compare the subgradient inequality for an arbitrary `h ∈ ∂f(x)` along directions `p` and `-p`;
-- differentiability identifies the corresponding directional increments with the same linear
-- functional `p ↦ ⟪g, p⟫`, forcing `h = g`.
theorem subdifferential_eq_singleton_of_hasGradientAt
    {f : E → WithTop ℝ} (hf : ConvexOn ℝ (dom f) (withTopRealPart f)) {x : E}
    (hx : x ∈ interior (dom f)) {g : E}
    (hgrad : HasGradientAt (withTopRealPart f) g x) :
    ∂ f(x) = {g} := by
  -- First show that the displayed gradient is a subgradient, then prove every subgradient
  -- coincides with it.
  ext h
  constructor
  · intro hh
    have hEq : h = g :=
      eq_gradient_of_mem_subdifferential_of_hasGradientAt hx hgrad hh
    simp [hEq]
  · intro hh
    rcases Set.mem_singleton_iff.mp hh with rfl
    exact gradient_mem_subdifferential_of_hasGradientAt hf hx hgrad

/-- Lemma 3.1.7, derived owner form: if a convex extended-real-valued function on a complete real
inner-product space is differentiable at an interior point of its effective domain, then its
subdifferential there is the singleton containing the gradient of its finite real part. -/
-- Proof sketch: convexity and differentiability at `x` give the supporting-plane inequality with
-- slope `∇ (withTopRealPart f) x`, so the gradient lies in the subdifferential. For the reverse
-- inclusion, compare the subgradient inequality for an arbitrary `g ∈ ∂f(x)` along directions
-- `p` and `-p`; differentiability identifies the directional derivatives with pairings against
-- `∇ (withTopRealPart f) x`, forcing `g = ∇ (withTopRealPart f) x`.
theorem subdifferential_eq_singleton_gradient
    {f : E → WithTop ℝ} (hf : ConvexOn ℝ (dom f) (withTopRealPart f)) {x : E}
    (hx : x ∈ interior (dom f))
    (hfd : DifferentiableAt ℝ (withTopRealPart f) x) :
    ∂ f(x) = {∇ (withTopRealPart f) x} := by
  exact subdifferential_eq_singleton_of_hasGradientAt hf hx hfd.hasGradientAt

end

/-! ### Theorem_3_1_7 (from Chap03) -/
/- Theorem 3.1.7 is a recall-only surface in the chapter's constrained partial-infimum /
extended-real convex-analysis domain.

Primary mathematical domain:
- constrained fiberwise infima of real-valued convex functions, viewed through the chapter's
  `EReal` finite-value bridge.

Relevant owner-style declarations sampled before refinement:
- `partialInfProjection` in `Theorem_3_1_2_3`, the source-facing owner for constrained fiberwise
  infima;
- `extendedRealRealPart` in `Definition_3_1_1_3`, the chapter bridge from `EReal` values to their
  real part on the finite-value domain;
- `partialInfProjection_convexOn` in `Theorem_3_1_2_3`, the canonical convexity theorem for that
  owner surface;
- `partialInfProjection_convexOn_of_convexWithTop` in `Theorem_3_8`, the later `WithTop` analogue
  that reuses the same owner abstraction.

Best owner abstraction:
- `partialInfProjection_convexOn`.

Primitive data:
- none in this file; the owner object and its convexity theorem already live upstream.

Derived API:
- this recall-only numbered entry point.

Source/core/bridge triage:
- source-facing: Theorem 3.1.7's statement that the constrained partial infimum of a real-valued
  convex function is convex;
- core/canonical: `partialInfProjection_convexOn` on the chapter owner `partialInfProjection`;
- bridge/view: the chapter `EReal` convexity surface
  `ConvexOn ℝ (dom ψ) (extendedRealRealPart ψ)`.

The previous file introduced a second theorem name with exactly the same statement as
`partialInfProjection_convexOn`. Since the upstream theorem already lives on the correct owner
abstraction and is reused elsewhere in the chapter, this file now recalls that canonical theorem
directly instead of maintaining a duplicate wrapper.
-/

recall partialInfProjection_convexOn

/-! ### Corollary_3_1_8 (from Chap03) -/
/- Corollary 3.1.8 is a recall-only item in the chapter's extended-valued
constrained-subdifferential domain.

Primary domain:
- convexity and lower-semicontinuity consequences of nonempty constrained subdifferentials for
  `WithTop ℝ`-valued functions on Euclidean space.

Sampled owner-style declarations:
- `withTopRealPart`
- `constrainedSubdifferential`
- `convexOn_of_constrainedSubdifferential_nonempty`
- `lowerSemicontinuousOn_of_constrainedSubdifferential_nonempty`

Best owner abstraction:
- the owner theorem pair
  `convexOn_of_constrainedSubdifferential_nonempty` and
  `lowerSemicontinuousOn_of_constrainedSubdifferential_nonempty`,
  built from the chapter owner objects `withTopRealPart` and
  `constrainedSubdifferential`

Primitive data:
- a convex feasible set `Q`
- a `WithTop ℝ`-valued objective `f`
- pointwise nonemptiness of `constrainedSubdifferential Q f x` on `Q`

Derived API:
- convexity of `withTopRealPart f` on `Q`
- lower semicontinuity of `withTopRealPart f` on `Q`

Source/core/bridge triage:
- source-facing: the textbook corollary collecting the convexity and lower-semicontinuity
  consequences
- core/canonical: `withTopRealPart` and `constrainedSubdifferential`
- bridge/view: none; both consequences already exist upstream with the exact public interfaces
  needed here

The previous file-level conjunction theorem was a redundant wrapper around those two owner
consequences, and it had no downstream users. This file therefore keeps only direct recalls of the
upstream owner theorems instead of a parallel local packaging layer. -/

recall convexOn_of_constrainedSubdifferential_nonempty

recall lowerSemicontinuousOn_of_constrainedSubdifferential_nonempty

/-! ### Lemma_3_1_8 (from Chap03) -/
universe u

open scoped WithTopConvexAnalysis

/- Lemma 3.1.8 is a recall-only bridge in the chapter's extended-valued
convex-composition/subdifferential-calculus domain.

Sampled owner-style declarations:
- `withTopEffectiveDomain` in `Definition_3_3`, the chapter owner for the finite-value domain
- `withTopRealPart` in `Definition_3_3`, the owner finite-value representative
- `subdifferential` in `Definition_3_1_5`, the owner subgradient-set API
- `monotoneConvexComp_convexOn` and `subdifferential_monotoneConvexComp_eq_convexHull` in
  `Lemma_3_8`, the source owner clauses for this monotone composition lemma on real inner-product
  spaces

Best owner abstraction:
- the source-facing composition object `monotoneConvexComp` together with its convexity and
  subdifferential owner clauses in `Lemma_3_8`
- the ambient effective-domain / finite-part / subdifferential notions remain owned upstream by
  `Definition_3_3` and `Definition_3_1_5`

Primitive data:
- none in this recall file

Derived API:
- `monotoneConvexComp`
- `monotoneConvexComp_apply_of_mem_effectiveDomain`
- `monotoneConvexComp_convexOn`
- `subdifferential_monotoneConvexComp_eq_convexHull`

Source/core/bridge triage:
- source-facing: the monotone composition object and its two textbook clauses recalled below
- core/canonical: `withTopEffectiveDomain`, `withTopRealPart`,
  `ConvexOn ℝ (dom f) (withTopRealPart f)`,
  `subdifferential`
- bridge/view: this recall-only file

The previous version redefined the ambient effective-domain, finite-real-part, convexity, and
subdifferential API locally, then split the owner theorem into two wrapper consequences. Those
parallel wrappers had no downstream users. This file now recalls the owner composition surface
directly instead of maintaining a second root API. The owner surface in `Lemma_3_8` is now itself
split into the two atomic textbook clauses, so this recall file follows that same canonical
surface and drops the redundant properness hypotheses that were only artifacts of the earlier
coordinate-specialized statement. -/

recall monotoneConvexComp {V : Type u} (φ : ℝ → WithTop ℝ) (ψ : V → WithTop ℝ) :
    V → WithTop ℝ

recall monotoneConvexComp_apply_of_mem_effectiveDomain
    {V : Type u} {φ : ℝ → WithTop ℝ} {ψ : V → WithTop ℝ} {x : V}
    (hx : x ∈ dom ψ) :
    monotoneConvexComp φ ψ x = φ (withTopRealPart ψ x)

recall monotoneConvexComp_convexOn

recall subdifferential_monotoneConvexComp_eq_convexHull

/-! ### Theorem_3_1_8 (from Chap03) -/
noncomputable section

universe u v

open scoped WithTopConvexAnalysis

variable {ι : Type u} {X : Type v}

/- Theorem 3.1.8 lies in the chapter's `WithTop ℝ`-valued closed-convex pointwise-supremum
domain.

Sampled owner-style declarations in this domain:
- `pointwiseSupremumOn` and `pointwiseSupremumOn_apply` from `PointwiseSupremumOn`
- `dom` and `constrainedEpigraph` from `Definition_3_3`
- `ClosedConvexOn` from `Definition_3_1_1_5`
- `ConvexOn ℝ (dom f) (withTopRealPart f)` as the canonical convexity view behind
  `ClosedConvexOn`

Best owner abstraction:
- core/canonical owners reused from earlier chapter files:
  `pointwiseSupremumOn`, `dom`, and `ClosedConvexOn`
- bridge/view layer: the feasible-domain restriction
  `pointwiseSupremumOnEffectiveDomain Q Δ φ = Q ∩ dom (pointwiseSupremumOn Δ φ)`

Primitive data:
- the parameter subset `Δ : Set ι`
- the slice family `φ : X → ι → WithTop ℝ`
- the owner function `pointwiseSupremumOn Δ φ`

Derived API:
- `pointwiseSupremumOn_apply`
- `pointwiseSupremumOnEffectiveDomain`
- `mem_pointwiseSupremumOnEffectiveDomain_iff`
- `mem_pointwiseSupremumOnEffectiveDomain_iff_lt_top`
- `ClosedConvexOn.pointwise_sSup`

Source/core/bridge triage:
- source-facing: Theorem 3.1.8 itself, namely the closed-convexity theorem below
- core/canonical: `pointwiseSupremumOn`, `dom`, `ClosedConvexOn`
- bridge/view: `pointwiseSupremumOnEffectiveDomain`

This file reuses the generic owner `pointwiseSupremumOn`, and it does not keep a parallel
primitive notion of “finite-value domain”: that domain is derived canonically from the upstream
owner `dom` applied to `pointwiseSupremumOn Δ φ`, then intersected with the ambient feasible set
`Q`. -/

/-- The finite-value domain of the pointwise supremum over `Δ` inside `Q`, expressed through the
chapter owner `dom`. -/
abbrev pointwiseSupremumOnEffectiveDomain
    (Q : Set X) (Δ : Set ι) (φ : X → ι → WithTop ℝ) : Set X :=
  Q ∩ dom (pointwiseSupremumOn Δ φ)

/-- Membership in `pointwiseSupremumOnEffectiveDomain Q Δ φ` means lying in `Q` and in the
canonical effective domain of `pointwiseSupremumOn Δ φ`. -/
@[simp]
theorem mem_pointwiseSupremumOnEffectiveDomain_iff
    {Q : Set X} {Δ : Set ι} {φ : X → ι → WithTop ℝ} {x : X} :
    x ∈ pointwiseSupremumOnEffectiveDomain Q Δ φ ↔
      x ∈ Q ∧ x ∈ dom (pointwiseSupremumOn Δ φ) :=
  Iff.rfl

/-- Membership in `pointwiseSupremumOnEffectiveDomain Q Δ φ` can be read as a finiteness
condition on the pointwise supremum. -/
theorem mem_pointwiseSupremumOnEffectiveDomain_iff_lt_top
    {Q : Set X} {Δ : Set ι} {φ : X → ι → WithTop ℝ} {x : X} :
    x ∈ pointwiseSupremumOnEffectiveDomain Q Δ φ ↔
      x ∈ Q ∧ pointwiseSupremumOn Δ φ x < ⊤ := by
  rw [mem_pointwiseSupremumOnEffectiveDomain_iff, mem_withTopEffectiveDomain_iff]

section

variable [TopologicalSpace X] [AddCommMonoid X] [Module ℝ X]

namespace ClosedConvexOn

/-- Theorem 3.1.8: if every slice `x ↦ φ(x, y)` with `y ∈ Δ` is closed and convex on `Q`, then
the pointwise supremum `x ↦ sup_{y ∈ Δ} φ(x, y)` is closed and convex on the finite-value domain
`{x ∈ Q | sup_{y ∈ Δ} φ(x, y) < +∞}`. -/
-- Proof sketch: the constrained epigraph of `pointwiseSupremumOn Δ φ` over
-- `pointwiseSupremumOnEffectiveDomain Q Δ φ` is the intersection over `y ∈ Δ` of the constrained
-- epigraphs of the slices `x ↦ φ x y`. Intersections preserve closedness and convexity, and the
-- finiteness-on-domain clause is built into `pointwiseSupremumOnEffectiveDomain`.
theorem pointwise_sSup
    {Q : Set X} {Δ : Set ι} {φ : X → ι → WithTop ℝ}
    (hΔ : Δ.Nonempty)
    (hφ : ∀ y ∈ Δ, ClosedConvexOn Q (fun x ↦ φ x y)) :
    ClosedConvexOn (pointwiseSupremumOnEffectiveDomain Q Δ φ) (pointwiseSupremumOn Δ φ) := sorry

end ClosedConvexOn

end

end
