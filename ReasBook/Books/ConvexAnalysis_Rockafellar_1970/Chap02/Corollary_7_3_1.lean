import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Corollary_6_3_2
import ConvexAnalysis_Rockafellar_1970.Chap02.Lemma_7_3

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Rockafellar

variable
    {𝕜 E : Type*}
    [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
    [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

local instance : SMul 𝕜 (WithTopBot 𝕜) where
  smul r x := (r : WithTopBot 𝕜) * x

omit [NontriviallyNormedField 𝕜] [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜] in
private theorem withTopBot_bot_lt_coe (a : 𝕜) :
    (⊥ : WithTopBot 𝕜) < (a : WithTopBot 𝕜) := by
  change (((⊥ : WithBot 𝕜) : WithTop (WithBot 𝕜)) <
    (((a : WithBot 𝕜) : WithTop (WithBot 𝕜))))
  exact WithTop.coe_lt_coe.mpr (WithBot.bot_lt_coe a)

omit [NontriviallyNormedField 𝕜] [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜] in
private theorem withTopBot_coe_lt_top (a : 𝕜) :
    (a : WithTopBot 𝕜) < (⊤ : WithTopBot 𝕜) := by
  change (((a : WithBot 𝕜) : WithTop (WithBot 𝕜)) < (⊤ : WithTop (WithBot 𝕜)))
  exact WithTop.coe_lt_top _

omit [NontriviallyNormedField 𝕜] [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜] in
private theorem withTopBot_coe_lt_coe_iff {a b : 𝕜} :
    (a : WithTopBot 𝕜) < (b : WithTopBot 𝕜) ↔ a < b := by
  constructor
  · intro h
    change (((a : WithBot 𝕜) : WithTop (WithBot 𝕜)) <
      (((b : WithBot 𝕜) : WithTop (WithBot 𝕜)))) at h
    exact WithBot.coe_lt_coe.mp (WithTop.coe_lt_coe.mp h)
  · intro h
    change (((a : WithBot 𝕜) : WithTop (WithBot 𝕜)) <
      (((b : WithBot 𝕜) : WithTop (WithBot 𝕜))))
    exact WithTop.coe_lt_coe.mpr (WithBot.coe_lt_coe.mpr h)

omit [NontriviallyNormedField 𝕜] [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜] in
private theorem withTopBot_coe_lt_coe {a b : 𝕜} (h : a < b) :
    (a : WithTopBot 𝕜) < (b : WithTopBot 𝕜) :=
  withTopBot_coe_lt_coe_iff.mpr h

omit [OrderTopology 𝕜] [CompleteSpace 𝕜] in
private theorem exists_between_coe_of_lt [DenselyOrdered 𝕜]
    {x y : WithTopBot 𝕜} (h : x < y) :
    ∃ a : 𝕜, x < (a : WithTopBot 𝕜) ∧ (a : WithTopBot 𝕜) < y := by
  cases x with
  | none =>
      have hyle : y ≤ (⊤ : WithTopBot 𝕜) := le_top
      exact (not_lt_of_ge hyle h).elim
  | some x' =>
      cases x' with
      | bot =>
          cases y with
          | none =>
              exact ⟨0, withTopBot_bot_lt_coe 0, withTopBot_coe_lt_top 0⟩
          | some y' =>
              cases y' with
              | bot =>
                  exact (lt_irrefl _ h).elim
              | coe b =>
                  obtain ⟨a, ha⟩ := exists_lt b
                  exact ⟨a, withTopBot_bot_lt_coe a, withTopBot_coe_lt_coe ha⟩
      | coe x =>
          cases y with
          | none =>
              obtain ⟨a, hxa⟩ := exists_gt x
              exact ⟨a, withTopBot_coe_lt_coe hxa, withTopBot_coe_lt_top a⟩
          | some y' =>
              cases y' with
              | bot =>
                  exact (not_lt_of_ge (bot_le : (⊥ : WithTopBot 𝕜) ≤ (x : WithTopBot 𝕜)) h).elim
              | coe y =>
                  have hxy : x < y := withTopBot_coe_lt_coe_iff.mp h
                  obtain ⟨a, hxa, hay⟩ := exists_between hxy
                  exact ⟨a, withTopBot_coe_lt_coe hxa, withTopBot_coe_lt_coe hay⟩

namespace Function.IsConvex

variable {f : E → WithTopBot 𝕜}

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 7.3.1 says that if a convex function on a finite-dimensional
  ordered-normed-field ambient has a strict sublevel point below an extended level `α`, then that
  strict sublevel
  set already meets the relative
  interior of `dom f`.
- `core/canonical`: the owner abstraction is `ConvexOn 𝕜 (Set.univ : Set E) f`, together with the
  chapter effective-domain owner `dom(·)` and mathlib's
  `intrinsicInterior 𝕜`.
- `bridge/view`: the proof route factors through the canonical epigraph theorem `Lemma_7_3` and
  the convex-set owner theorem
  `Convex.inter_ri_nonempty_of_isOpen_of_inter_intrinsicClosure_nonempty`; no parallel local
  finiteness-set wrapper is needed because `dom(f)` already owns that notion upstream.
- Domain-style sampling used here: the owner predicate `ConvexOn 𝕜 (Set.univ : Set E) f`, the nearby
  epigraph-relative-interior bridge
  `Function.IsConvex.mem_ri_epi_iff`
  from `Lemma_7_3`, and the owner-style relative-interior open-set bridge
  `Convex.inter_ri_nonempty_of_isOpen_of_inter_intrinsicClosure_nonempty` from
  `Corollary_6_3_2`.
- Primitive data vs derived API: the primitive data are the convex function `f`, the level
  `α : WithTopBot 𝕜`, and a strict sublevel witness. The conclusion is the derived existence
  of a strict sublevel point on the relative interior of the effective domain.
- Layer target: this item remains `source-facing`, but its convexity input is now expressed through
  the chapter owner predicate, and its domain conclusion through the owner `dom(f)` instead of a
  duplicate raw set expression.
- Ambient-space refinement: the textbook `R^n` presentation is only a coordinate model for this
  argument, so the public theorem is stated at the owner level of finite-dimensional ordered
  normed-field spaces.
-/

/-- Corollary 7.3.1, existential owner form: if a convex function on a finite-dimensional ordered
normed-field ambient has a strict sublevel point below `α`, then one can choose such a point in
`riDom[𝕜](f)`. Specializing to `𝕜 = ℝ` recovers the textbook `R^n` statement. -/
-- Proof sketch: apply Corollary 6.3.2 to the open half-space
-- `{p : E × 𝕜 | p.2 < β}` (with `β : 𝕜`, `β < α`) and the epigraph `epi f`.
-- A relative-interior point `(x, μ)` of the epigraph with `μ < β` projects to
-- `x ∈ riDom[𝕜](f)`, and `f x ≤ μ < α` gives the desired strict inequality.
theorem exists_lt_on_riDom_of_exists_lt
    (hf : f.IsConvex 𝕜) (α : WithTopBot 𝕜)
    (hα : ∃ x : E, f x < α) :
    ∃ x, x ∈ riDom[𝕜](f) ∧ f x < α := by
  have hEpi : Convex 𝕜 (epi f) := by
    exact hf
  rcases hα with ⟨x, hxlt⟩
  rcases exists_between_coe_of_lt hxlt with ⟨β, hxβ, hβα⟩
  rcases exists_between_coe_of_lt hxβ with ⟨γ, hxγ, hγβ⟩
  let U : Set (E × 𝕜) := {p | p.2 < β}
  have hU : IsOpen U := isOpen_lt continuous_snd continuous_const
  have hclosure :
      (intrinsicClosure 𝕜 (epi f) ∩ U).Nonempty := by
    refine ⟨(x, γ), ?_⟩
    refine ⟨subset_intrinsicClosure ?_, ?_⟩
    · simpa [epi] using hxγ.le
    · simpa [U] using hγβ
  obtain ⟨⟨y, μ⟩, hyi, hyμlt⟩ :=
    Convex.inter_ri_nonempty_of_isOpen_of_inter_intrinsicClosure_nonempty
      hEpi hU hclosure
  have hyμβ : (μ : WithTopBot 𝕜) < β := by
    simpa [U] using hyμlt
  have hyμα : (μ : WithTopBot 𝕜) < α := lt_trans hyμβ hβα
  rcases (Function.IsConvex.mem_ri_epi_iff (f := f) hf).1 hyi with ⟨hy_dom, hfyμ⟩
  exact ⟨y, hy_dom, lt_trans hfyμ hyμα⟩

/-- Corollary 7.3.1, set-nonempty bridge form:
if the strict `α`-sublevel set is nonempty, it meets `riDom[𝕜](f)`. -/
theorem riDom_inter_nonempty_of_sublevel_nonempty
    (hf : f.IsConvex 𝕜) (α : WithTopBot 𝕜)
    (hα : ({x : E | f x < α} : Set E).Nonempty) :
    (riDom[𝕜](f) ∩ {x : E | f x < α}).Nonempty := by
  rcases hα with ⟨x, hxlt⟩
  rcases Function.IsConvex.exists_lt_on_riDom_of_exists_lt (f := f) hf α ⟨x, hxlt⟩ with
    ⟨y, hyri, hylt⟩
  exact ⟨y, hyri, hylt⟩

end Function.IsConvex

end
