

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_5_20 (from Chap05) -/
universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Lemma 5.20 is `source-facing` for the strong-convexity owner
`is_strongly_convex_function`. For the perturbation `g`, the cleanest faithful interface is the
canonical/library-facing one: convexity of the finite-valued restriction `x ↦ (g x).toReal` on
`effective_domain g`, together with the explicit source codomain condition `g : E → (-∞, ∞]`,
encoded by `hg_ne_bot`. This avoids the duplicate `effective_domain` owner conflict between the
Chapter 2 and Chapter 5 item files while preserving the textbook mathematics. -/

-- Proof sketch: use `hf.ne_bot` together with `hg_ne_bot` to rule out `-∞` for `f + g`, read
-- convexity of `effective_domain g` from the set component of `hg`, combine it with
-- `hf.convex_effective_domain` to control the domain of `f + g`, and then add the strong-convex
-- Jensen inequality for `f` to the convex Jensen inequality for the real-valued restriction of
-- `g`, coercing back to `EReal`.
/-- Lemma 5.20: if `f` is `σ`-strongly convex and `g` is convex, then `f + g` is
`σ`-strongly convex. Here the textbook convexity of `g : E → (-∞, ∞]` is expressed by convexity of
the finite-valued restriction `x ↦ (g x).toReal` on `effective_domain g`, together with the
explicit hypothesis that `g` never takes the value `-∞`. -/
theorem is_strongly_convex_function_add_of_convexOn_toReal
    {f g : E → EReal} {σ : ℝ} (hf : is_strongly_convex_function f σ)
    (hg_ne_bot : ∀ x, g x ≠ ⊥)
    (hg : ConvexOn ℝ (effective_domain g) (fun x ↦ (g x).toReal)) :
    is_strongly_convex_function (fun x ↦ f x + g x) σ := sorry

end
