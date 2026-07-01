import ConvexAnalysis_Rockafellar_1970.Chap02.Corollary_7_2_1

-- Declarations for this item will be appended below by the statement pipeline.

section

variable {𝕜 E : Type*}
variable [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
variable [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 7.0.7 isolates the endpoint-valued behavior of closed improper convex
  functions.
- `core/canonical`: the owner predicates already fixed in Chapter 2 are `Function.IsConvex 𝕜`,
  `Function.IsProper`, and `LowerSemicontinuous`; the canonical endpoint functions are the
  endpoint values `⊥` and `⊤` in `WithBotTop 𝕜`.
- `bridge/view`: Corollary 7.2.1 already supplies the key owner-side bridge
  `Function.IsConvex.eq_bot_of_mem_dom_of_lowerSemicontinuous`, which identifies the
  effective-domain branch with value `⊥`. The complementary branch is value `⊤` by the owner
  `dom(·)`.

Domain-style sampling used here:
- `Function.IsProper`;
- `LowerSemicontinuous`;
- `Function.IsConvex.eq_bot_of_mem_dom_of_lowerSemicontinuous`;
- the primitive bridge `Function.eq_bot_or_eq_top_of_eq_bot_on_dom`;
- the endpoint values `⊥` and `⊤` in `WithBotTop 𝕜`.

Primitive data vs derived API:
- primitive source inputs: `f : E → WithBotTop 𝕜` with `f.IsConvex 𝕜`,
  `LowerSemicontinuous f`, and
  `¬ f.IsProper`;
- derived source-facing output: the pointwise endpoint dichotomy
  `∀ x, f x = ⊥ ∨ f x = ⊤`.

Layer target: `source-facing`; this remark remains a theorem about the existing closedness,
convexity, and properness owners. The `dom` case split is factored through the primitive endpoint
bridge `Function.eq_bot_or_eq_top_of_eq_bot_on_dom` rather than inlined in the convex theorem.
-/

namespace Function

variable {β X : Type*} [PartialOrder β] [OrderTop β] [Bot β]
variable {f : X → β}

/-- Primitive endpoint bridge: if a function equals `⊥` at each point of its effective domain,
then every value is an endpoint `⊥` or `⊤`. -/
theorem eq_bot_or_eq_top_of_eq_bot_on_dom
    (hbot : ∀ ⦃x : X⦄, x ∈ dom(f) → f x = ⊥) (x : X) :
    f x = ⊥ ∨ f x = ⊤ := by
  by_cases hx : x ∈ dom(f)
  · exact .inl (hbot hx)
  · exact .inr <| by
      by_contra hxtop
      exact hx <| by
        simpa [mem_effectiveDomain] using (lt_of_le_of_ne le_top hxtop)

end Function

namespace Function.IsConvex

variable {f : E → WithBotTop 𝕜}

-- Proof sketch: Corollary 7.2.1 provides the primitive input `f = ⊥` on `dom(f)`. The endpoint
-- dichotomy then follows from `Function.eq_bot_or_eq_top_of_eq_bot_on_dom`.
/-- Text 7.0.7 (owner form): a lower semicontinuous improper convex `WithBotTop 𝕜`-valued function
on a finite-dimensional normed space over an ordered scalar field is pointwise endpoint-valued:
for every `x`, one has `f x = ⊥` or `f x = ⊤`. -/
theorem eq_bot_or_eq_top_of_lowerSemicontinuous_of_not_isProper
    (hf : f.IsConvex 𝕜) (hf_lsc : LowerSemicontinuous f)
    (hf_not_proper : ¬ f.IsProper) :
    ∀ x : E, f x = ⊥ ∨ f x = ⊤ := by
  intro x
  exact Function.eq_bot_or_eq_top_of_eq_bot_on_dom
    (f := f)
    (hbot := fun {x} hx ↦
      hf.eq_bot_of_mem_dom_of_lowerSemicontinuous hf_lsc hf_not_proper hx) x

end Function.IsConvex

end
