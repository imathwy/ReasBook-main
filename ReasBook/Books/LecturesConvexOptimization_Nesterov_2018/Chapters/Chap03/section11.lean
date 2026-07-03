import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_11 (from Chap03) -/
/-
Definition 3.11 is a source-facing recall in the chapter's one-sided directional-derivative
domain.

Primary mathematical domain:
- one-sided directional derivatives of `EReal`-valued functions on real modules.

Sampled owner-style declarations:
- `HasDerivWithinAt`
- `HasDirectionalDerivAt`
- `DirectionallyDifferentiableAt`
- `directionallyDifferentiableAt_iff_exists_hasDirectionalDerivAt`

Best owner abstraction:
- `HasDirectionalDerivAt`

Primitive data:
- none in this file; the owner predicate lives upstream in `Definition_3_1_3_1`, and the earlier
  chapter recall surface already lives in `Definition_3_1_3`.

Derived API:
- the source-facing owner predicate `HasDirectionalDerivAt`
- its existential wrapper `DirectionallyDifferentiableAt`
- the thin specification theorem `directionallyDifferentiableAt_iff_exists_hasDirectionalDerivAt`

Source/core/bridge triage:
- source-facing: `HasDirectionalDerivAt`, `DirectionallyDifferentiableAt`
- core/canonical: the earlier chapter recall `Definition_3_1_3`, backed by `HasDerivWithinAt` on
  the scalar slice
- bridge/view: `directionallyDifferentiableAt_iff_exists_hasDirectionalDerivAt`

Definition 3.11 adds no new mathematical data beyond the earlier chapter recall surface in
`Definition_3_1_3`. This file therefore reuses that surface directly instead of restating the full
signatures a second time.
-/

recall HasDirectionalDerivAt

recall DirectionallyDifferentiableAt

recall directionallyDifferentiableAt_iff_exists_hasDirectionalDerivAt

/-! ### Lemma_3_11 (from Chap03) -/
noncomputable section

open scoped WithTopConvexAnalysis

/- Lemma 3.11 lies in the chapter's extended-valued convex-analysis / affine subdifferential
calculus on Euclidean spaces.

Sampled owner declarations:
- mathlib `ConvexOn.comp_affineMap`
- `ClosedConvexOn.comp_affineMap`
- `IsSubgradientAt.comp_affineMap`
- `subdifferential`
- `mem_subdifferential_iff`

Best owner abstractions:
- `ClosedConvexOn` for the closed-convex affine-pullback statement
- `IsSubgradientAt` and `subdifferential` from `Definition_3_1_5` for the affine subgradient
  calculus statement

Primitive data:
- the affine map `g : Eₙ →ᵃ[ℝ] Eₘ`
- the ambient closed-convex hypothesis `ClosedConvexOn S φ`
- the owner-level subgradient predicate `IsSubgradientAt f (g x) h`

Derived API:
- the recalled owner theorem `ClosedConvexOn.comp_affineMap`
- the Euclidean bridge theorem `subdifferential_comp_affineMap_image_adjoint_subset`

Source/core/bridge triage:
- source-facing: Lemma 3.11's two affine-pullback consequences, namely closed convexity on
  `g ⁻¹' S` and the adjoint-image inclusion for the subdifferential
- core/canonical: `ClosedConvexOn`, `IsSubgradientAt`, and `subdifferential`
- bridge/view: `ConvexOn.comp_affineMap`, which underlies the closed-convex owner theorem, and
  the finite-dimensional set-level subdifferential inclusion derived from
  `IsSubgradientAt.comp_affineMap`

This file therefore recalls the assumption-free closed-convex owner theorem directly and keeps
only the thin affine subdifferential bridge theorem that specializes
`IsSubgradientAt.comp_affineMap` to the
source-facing subdifferential statement. -/

recall ClosedConvexOn.comp_affineMap
    {m n : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin m))}
    {φ : EuclideanSpace ℝ (Fin m) → WithTop ℝ}
    (hφ : ClosedConvexOn S φ)
    (g : EuclideanSpace ℝ (Fin n) →ᵃ[ℝ] EuclideanSpace ℝ (Fin m)) :
    ClosedConvexOn (g ⁻¹' S) (φ ∘ g)

universe u v

/-- Lemma 3.11, subdifferential part: every subgradient of `f` at `g x` pulls back along the
adjoint of the linear part of `g`. In set form, the adjoint image of `∂ f((g x))` is contained in
`∂ (f ∘ g)(x)`. In Euclidean coordinates, when `g y = A y + b`, the pullback is under `Aᵀ`. -/
-- Proof sketch: unpack membership in `subdifferential f (g x)` into the owner predicate
-- `IsSubgradientAt f (g x)`. The owner theorem `IsSubgradientAt.comp_affineMap` pulls that
-- subgradient back along `g.linear.adjoint`, and `mem_subdifferential_iff` repackages the result
-- into the set-valued statement.
theorem subdifferential_comp_affineMap_image_adjoint_subset
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {f : F → WithTop ℝ} {g : E →ᵃ[ℝ] F} {x : E} :
    g.linear.adjoint '' (∂ f((g x))) ⊆ ∂ (f ∘ g)(x) := by
  rintro _ ⟨h, hh, rfl⟩
  simpa [mem_subdifferential_iff] using (mem_subdifferential_iff.mp hh).comp_affineMap

end

/-! ### Proposition_3_11 (from Chap03) -/
universe u

noncomputable section

variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

open scoped ConvexAnalysis SupportFunction

recall mem_extendedRealEffectiveDomain_iff

recall supportFunction_apply

/- Proposition 3.11 lies in the chapter's support-function / effective-domain domain.

Relevant sampled owner declarations:
- `supportFunction` / `supportFunction_apply` in `Definition_3_9`, the source-facing owner for
  `ξ[Q]`
- `extendedRealEffectiveDomain` / notation `dom` in `Definition_3_1_1_2`, the chapter owner for
  finite `EReal` values
- downstream recall `Proposition_3_1_2_3`, which already treats this file as the owner theorem
  family for bounded support-function finiteness

Best owner abstraction:
- source-facing: Proposition 3.11's bounded-set finiteness statement for `ξ[Q]`
- core/canonical: the pair `ξ[Q]` and `dom ξ[Q]`
- bridge/view: the pointwise membership theorem below, derived from the owner language rather than
  from any local wrapper

Primitive data:
- a set `Q : Set E`
- the assumptions `Q.Nonempty` and `Bornology.IsBounded Q`

Derived API:
- `supportFunction_mem_extendedRealEffectiveDomain_of_nonempty_bounded`
- `supportFunction_dom_eq_univ_of_nonempty_bounded`

No smaller upstream project or mathlib theorem with the same support-function / effective-domain
interface was found in the sampled domain, so this file remains the owner theorem family and keeps
the chapter owners `ξ[Q]` and `dom` directly on the public surface. The textbook `ℝⁿ` statement is
the specialization `E = EuclideanSpace ℝ (Fin n)`.
-/

/-- The support function of a nonempty bounded set takes finite extended-real values at every
point of a real inner-product space. The textbook `ℝⁿ` statement is the specialization
`E = EuclideanSpace ℝ (Fin n)`. -/
-- Proof sketch: boundedness gives a uniform upper bound on the inner products `⟪u, x⟫` for
-- `x ∈ Q`, so the defining supremum is not `⊤`; nonemptiness gives one attained lower bound, so
-- the supremum is not `⊥`.
theorem supportFunction_mem_extendedRealEffectiveDomain_of_nonempty_bounded
    (Q : Set E) (hQ_nonempty : Q.Nonempty) (hQ_bounded : Bornology.IsBounded Q) (u : E) :
    u ∈ dom ξ[Q] := by
  rw [mem_extendedRealEffectiveDomain_iff, supportFunction_apply]
  constructor
  · obtain ⟨R, hR⟩ := hQ_bounded.exists_norm_le
    have hsSup_le :
        sSup ((fun x ↦ ((inner ℝ x u : ℝ) : EReal)) '' Q) ≤ ((R * ‖u‖ : ℝ) : EReal) := by
      refine sSup_le ?_
      rintro _ ⟨x, hx, rfl⟩
      change ((inner ℝ x u : ℝ) : EReal) ≤ ((R * ‖u‖ : ℝ) : EReal)
      exact_mod_cast (real_inner_le_norm x u).trans <|
        mul_le_mul_of_nonneg_right (hR x hx) (norm_nonneg u)
    exact ne_top_of_le_ne_top (EReal.coe_ne_top (R * ‖u‖)) hsSup_le
  · rcases hQ_nonempty with ⟨x, hxQ⟩
    intro hbot
    have hx_le : ((inner ℝ x u : ℝ) : EReal) ≤ sSup ((fun x ↦ ((inner ℝ x u : ℝ) : EReal)) '' Q) :=
      le_sSup ⟨x, hxQ, rfl⟩
    have : ((inner ℝ x u : ℝ) : EReal) ≤ (⊥ : EReal) := by
      rw [hbot] at hx_le
      exact hx_le
    exact (not_le_of_gt (EReal.bot_lt_coe _)) this

/-- Proposition 3.11: if `Q` is a nonempty bounded subset of a real inner-product space `E`,
then the domain `dom ξ_Q` of its support function is all of `E`; equivalently, `ξ_Q(u)` is finite
for every `u ∈ E`. The textbook `ℝⁿ` statement is the specialization
`E = EuclideanSpace ℝ (Fin n)`. -/
-- Proof sketch: use
-- `supportFunction_mem_extendedRealEffectiveDomain_of_nonempty_bounded` pointwise to show every
-- `u` belongs to the finite-value domain of `supportFunction Q`, then conclude by extensionality
-- that this domain is `Set.univ`.
theorem supportFunction_dom_eq_univ_of_nonempty_bounded
    (Q : Set E) (hQ_nonempty : Q.Nonempty) (hQ_bounded : Bornology.IsBounded Q) :
    dom ξ[Q] = Set.univ := by
  refine Set.eq_univ_iff_forall.mpr fun u ↦ ?_
  exact supportFunction_mem_extendedRealEffectiveDomain_of_nonempty_bounded
    Q hQ_nonempty hQ_bounded u

end

/-! ### Theorem_3_11 (from Chap03) -/
/- Theorem 3.11 lies in the chapter's two-function closed-convex minimax domain.

Sampled owner-style declarations in this domain:
- `ClosedConvexOn` from `Definition_3_1_1_5`, the chapter owner for closed convexity on a feasible
  set
- `constrainedSublevelSet` from `Definition_3_3`, the owner constrained sublevel-set construction
- `IsMinimaxLinearizationParameter` from `Definition_3_1_2_3`, the source-facing owner predicate
  for two-function minimax linearization
- `exists_minimax_parameter_of_bounded_constrainedSublevelSets` from `Theorem_3_1_2_6`, the
  earlier chapter owner theorem with the exact canonical conclusion

Best owner abstraction:
- source-facing: the existence of a minimax linearization parameter for the maximum of two closed
  convex functions
- core/canonical: `exists_minimax_parameter_of_bounded_constrainedSublevelSets`
- bridge/view: this file only, which recalls the earlier owner theorem as the numbered textbook
  item without exporting a second theorem name

Primitive data:
- the feasible set `Q`
- two real-valued objectives `f₁`, `f₂ : E → ℝ`
- closed convexity of the canonical `WithTop` lifts of `f₁` and `f₂` on `Q`
- boundedness of the constrained sublevel sets of the pointwise maximum
  `x ↦ max (f₁ x) (f₂ x)` on `Q`

Derived API:
- a weight `lam : unitInterval`
- the owner conclusion
  `IsMinimaxLinearizationParameter (fun x : Q ↦ f₁ x) (fun x : Q ↦ f₂ x) lam`

Source/core/bridge triage:
- source-facing: Theorem 3.11 as the chapter's two-function minimax statement for the maximum of
  two closed convex functions
- core/canonical: `IsMinimaxLinearizationParameter` and
  `exists_minimax_parameter_of_bounded_constrainedSublevelSets`
- bridge/view: the `WithTop` lift in the hypotheses, used only to express the chapter's
  closed-convex owner assumptions

The previous version replaced the minimax-parameter conclusion by the weaker existence of an
attained weighted objective, and it added redundant hypotheses `Q.Nonempty` and `IsClosed Q`
instead of reusing the chapter owner theorem. This refinement removes that parallel wrapper and
keeps Theorem 3.11 as a direct recall of the canonical minimax-parameter owner. -/

/- Theorem 3.11: if `f₁` and `f₂` are real-valued functions whose canonical `WithTop` lifts are
closed and convex on a feasible set `Q`, and every constrained sublevel set of the pointwise
maximum `x ↦ max (f₁ x) (f₂ x)` on `Q` is bounded, then there exists a parameter `λ* ∈ [0, 1]`
for which the constrained minimum value of `x ↦ max (f₁ x) (f₂ x)` on `Q` equals that of the
convex combination `x ↦ λ* f₁ x + (1 - λ*) f₂ x`; Lean records this conclusion by the owner
predicate `IsMinimaxLinearizationParameter` on the subtype `Q`. -/
recall exists_minimax_parameter_of_bounded_constrainedSublevelSets
