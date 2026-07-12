import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Topology

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

-- Proof sketch: choose `α > 0` with the lower directional derivative at `x` along `d` bounded
-- above by `-2 α`. The liminf hypothesis then yields `ε₁ > 0` such that
-- `(f (x + t • d) - f x) / t ≤ -α` for all `t ∈ (0, ε₁]`, hence
-- `f (x + t • d) ≤ f x - α t < f x`. Since `x ∈ interior (effective_domain f)`, some ball around
-- `x` lies in `effective_domain f`; because `d ≠ 0`, choosing `ε₂` so that `t • d` stays in that
-- ball for `t ∈ (0, ε₂]` gives the domain membership. Taking `ε = min ε₁ ε₂` yields the claim.
/-- Lemma 8.2: if `f : E → (-∞, ∞]` is represented by an `EReal`-valued function with no `⊥`
values, `x` lies in the interior of `dom(f)`, and the lower directional derivative of `f` at `x`
along a nonzero direction `d` is negative, then `f` strictly decreases along the ray
`x + t • d` for all sufficiently small `t > 0`, and those nearby points remain in `dom(f)`. -/
theorem exists_strict_decrease_along_descent_direction
    (f : E → EReal) (x d : E) (h_ne_bot : ∀ y, f y ≠ ⊥)
    (hx : x ∈ interior (effective_domain f)) (hd : d ≠ 0)
    (hdescent :
      Filter.liminf
          (fun t : ℝ ↦ (f (x + t • d) - f x) / (t : EReal))
          (𝓝[>] (0 : ℝ)) < 0) :
    ∃ ε > 0, ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) ε →
      x + t • d ∈ effective_domain f ∧ f (x + t • d) < f x := sorry

end
