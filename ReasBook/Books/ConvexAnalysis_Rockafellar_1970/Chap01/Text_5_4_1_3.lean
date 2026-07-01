import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Eorder.Add
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_4_0

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise
open Function

section

variable {E : Type*} {𝕜 : Type*}
variable [AddCommMonoid 𝕜] [ConditionallyCompleteLattice 𝕜] [IsOrderedAddMonoid 𝕜]
variable [Add E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: the proposition identifies the effective domain of the infimal convolution
  `f □ g` with the Minkowski sum of the effective domains of `f` and `g`.
- `core/canonical`: the owner abstraction is the chapter declaration `infimal_convolution` from
  `Text_5_4_0`, together with the chapter properness owner `Function.IsProper` from
  `Definition_4_6`.
- `bridge/view`: for `WithBotTop`-valued functions, the textbook domain statement is recovered
  directly from the decomposition owner
  `infimal_convolution_eq_sInf_decompositions`. In this codomain one must stay in the no-`⊥`
  regime: otherwise `⊥ + ⊤ = ⊥`, so finiteness of a decomposition term `f x₁ + g x₂` no longer
  forces finiteness of the summands.
- Domain-style sampling used here: the chapter owner declaration `infimal_convolution`, the domain
  notation `dom(f)`, the properness owner `Function.IsProper`, the companion
  `Function.IsProper.ne_bot`, the owner bridge `infimal_convolution_eq_sInf_decompositions`, the
  additive boundary lemma `WithBotTop.add_ne_top_iff_ne_top₂`, and the canonical Minkowski-sum
  notation on sets.
- Primitive data vs derived API: the owner-level domain identity needs only the pointwise no-`⊥`
  hypotheses `hf_ne_bot` and `hg_ne_bot`; the textbook properness wording is therefore a derived
  companion obtained from `Function.IsProper`.
- Ambient minimization: the statement and proof use only additive structure on
  the domain, together with the ordered-additive codomain structure already required by the owner
  epigraph bridge, so the theorem remains at an abstract additive/order layer.
- Layer targets:
  - `bridge/view`: `infimal_convolution_dom_eq_add` records the exact owner-level
    `WithBotTop` domain formula under the no-`⊥` guard needed to avoid the mixed-infinite
    pathology;
  - `source-facing`: `infimal_convolution_dom_eq_add_of_isProper` recovers the
    textbook properness phrasing from the chapter owner `Function.IsProper`.
-/

-- Route correction: the old epigraph/vertical-infimum proof used the chapter `WithTopBot`
-- projection API, while this item lives in the `WithBotTop` codomain. The proof below stays on
-- `WithBotTop` and follows the textbook decomposition witnesses directly.
/-- Helper for Text 5.4.1.3: a decomposition whose two coordinates lie in the effective domains of
`f` and `g` has finite total value. -/
lemma decomposition_value_lt_top_of_mem_dom
    (f g : E → WithBotTop 𝕜)
    (hf_ne_bot : ∀ x : E, f x ≠ ⊥)
    (hg_ne_bot : ∀ x : E, g x ≠ ⊥)
    {u v : E} (hu : u ∈ dom(f)) (hv : v ∈ dom(g)) :
    f u + g v < (⊤ : WithBotTop 𝕜) := by
  -- Translate domain membership into non-`⊤` facts and combine them through the additive boundary
  -- lemma for `WithBotTop`.
  rw [lt_top_iff_ne_top]
  exact
    (WithBotTop.add_ne_top_iff_ne_top₂ (hf_ne_bot u) (hg_ne_bot v)).2
      ⟨(lt_top_iff_ne_top.mp hu), (lt_top_iff_ne_top.mp hv)⟩

/-- Helper for Text 5.4.1.3: if `x` is outside `dom(f) + dom(g)`, then every decomposition
`x = u + v` has value `f u + g v = ⊤`. -/
lemma decomposition_value_eq_top_of_not_mem_dom_add
    (f g : E → WithBotTop 𝕜)
    (hf_ne_bot : ∀ x : E, f x ≠ ⊥)
    (hg_ne_bot : ∀ x : E, g x ≠ ⊥)
    {x u v : E} (huv : u + v = x) (hx : x ∉ dom(f) + dom(g)) :
    f u + g v = (⊤ : WithBotTop 𝕜) := by
  classical
  by_cases hsum : f u + g v = (⊤ : WithBotTop 𝕜)
  · exact hsum
  · -- If the decomposition value were finite, both summands would lie in their own domains and
    -- would therefore produce a forbidden representation of `x`.
    have hparts :=
      (WithBotTop.add_ne_top_iff_ne_top₂ (hf_ne_bot u) (hg_ne_bot v)).1 hsum
    have hu_dom : u ∈ dom(f) := by
      exact (lt_top_iff_ne_top).2 hparts.1
    have hv_dom : v ∈ dom(g) := by
      exact (lt_top_iff_ne_top).2 hparts.2
    exact False.elim (hx (Set.mem_add.2 ⟨u, hu_dom, v, hv_dom, huv⟩))

/-- Helper for Text 5.4.1.3: every sum of points from `dom(f)` and `dom(g)` lies in
`dom(f □ g)`. -/
lemma add_subset_infimal_convolution_dom
    (f g : E → WithBotTop 𝕜)
    (hf_ne_bot : ∀ x : E, f x ≠ ⊥)
    (hg_ne_bot : ∀ x : E, g x ≠ ⊥) :
    dom(f) + dom(g) ⊆ dom(f □ g) := by
  intro x hx
  rcases Set.mem_add.1 hx with ⟨u, hu, v, hv, rfl⟩
  -- Use the textbook witness decomposition `u + v = x` inside the defining infimum.
  rw [mem_effectiveDomain, infimal_convolution_eq_sInf_decompositions]
  refine lt_of_le_of_lt ?_ (decomposition_value_lt_top_of_mem_dom f g hf_ne_bot hg_ne_bot hu hv)
  apply sInf_le
  exact ⟨(u, v), by simp, rfl⟩

/-- Helper for Text 5.4.1.3: every point of `dom(f □ g)` admits a decomposition with first
coordinate in `dom(f)` and second coordinate in `dom(g)`. -/
lemma infimal_convolution_dom_subset_add
    (f g : E → WithBotTop 𝕜)
    (hf_ne_bot : ∀ x : E, f x ≠ ⊥)
    (hg_ne_bot : ∀ x : E, g x ≠ ⊥) :
    dom(f □ g) ⊆ dom(f) + dom(g) := by
  classical
  intro x hx
  by_contra hx_add
  -- Contrapositively, if `x` is outside the Minkowski sum of the domains, then every
  -- decomposition value in the defining image set is `⊤`, so the infimum itself is `⊤`.
  have hx_value : (f □ g) x < (⊤ : WithBotTop 𝕜) := mem_effectiveDomain.mp hx
  have hsInf_eq_top :
      sInf ((fun p : E × E ↦ f p.1 + g p.2) '' {p : E × E | p.1 + p.2 = x}) =
        (⊤ : WithBotTop 𝕜) := by
    apply le_antisymm le_top
    refine le_sInf ?_
    intro y hy
    rcases hy with ⟨⟨u, v⟩, huv, rfl⟩
    simpa using
      (show (⊤ : WithBotTop 𝕜) ≤ f u + g v by
        rw [decomposition_value_eq_top_of_not_mem_dom_add f g hf_ne_bot hg_ne_bot huv hx_add])
  have hx_top : (f □ g) x = (⊤ : WithBotTop 𝕜) := by
    -- Rewrite the infimal convolution into its decomposition infimum and substitute the forced
    -- `⊤` value of that infimum.
    rw [infimal_convolution_eq_sInf_decompositions, hsInf_eq_top]
  exact (lt_top_iff_ne_top.mp hx_value) hx_top

/-- Text 5.4.1.3: the effective domain of the infimal convolution of `f` and `g` is the Minkowski
sum of the effective domains of `f` and `g`. For `WithBotTop`-valued functions this domain formula
is valid under the natural pointwise `⊥`-exclusion hypotheses `f x ≠ ⊥` and `g x ≠ ⊥`. -/
theorem infimal_convolution_dom_eq_add
    (f g : E → WithBotTop 𝕜)
    (hf_ne_bot : ∀ x : E, f x ≠ ⊥)
    (hg_ne_bot : ∀ x : E, g x ≠ ⊥) :
    dom(f □ g) = dom(f) + dom(g) := by
  -- The two textbook inclusions are proved separately so the main theorem stays at the set level.
  exact Set.Subset.antisymm
    (infimal_convolution_dom_subset_add f g hf_ne_bot hg_ne_bot)
    (add_subset_infimal_convolution_dom f g hf_ne_bot hg_ne_bot)

/-- Properness-form restatement of Text 5.4.1.3. This companion uses the chapter owner
`Function.IsProper` only to recover the pointwise no-`⊥` hypotheses needed by the main theorem
`infimal_convolution_dom_eq_add`. -/
theorem infimal_convolution_dom_eq_add_of_isProper
    (f g : E → WithBotTop 𝕜) (hf : f.IsProper) (hg : g.IsProper) :
    dom(f □ g) = dom(f) + dom(g) := by
  -- Properness is used only to recover the pointwise `≠ ⊥` hypotheses needed above.
  simpa using infimal_convolution_dom_eq_add f g hf.ne_bot hg.ne_bot

end
