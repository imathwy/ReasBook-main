import Mathlib.Tactic.Recall
import BauschkeLean.Chap20.Proposition_20_22
import BauschkeLean.Chap21.Proposition_21_12

open scoped InnerProductSpace SetValuedOperator

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/- Source/core/bridge triage:
- `source-facing`: Corollary 21.14 records the closure, interior, and convexity consequences for
  the domain and range of a maximally monotone operator.
- `core/canonical`: the owner surface is `Maximal IsMonotone A` together with the Chapter 21
  Fitzpatrick-domain bridges `A.fstImageDomFitzpatrick` and `A.sndImageDomFitzpatrick`.
- `bridge/view`: the inverse-domain identification
  `A.sndImageDomFitzpatrick = (A⁻¹).fstImageDomFitzpatrick` is used only internally.

Primitive data: `A` and `hA : Maximal IsMonotone A`.
Derived API: the closure/interior projection identities and the convexity consequences for
`A.dom` and `A.range`, with the domain identities recalled directly from Proposition 21.12 and
the range identities routed through the second projection `A.sndImageDomFitzpatrick`. -/

/- Corollary 21.14 (1): the closure-domain identity is already the Chapter 21 owner theorem
`closure_dom_eq_closure_fst_image_dom_fitzpatrick`. -/
recall closure_dom_eq_closure_fst_image_dom_fitzpatrick

/- Corollary 21.14 (2): the interior-domain identity is already the Chapter 21 owner theorem
`interior_dom_eq_interior_fst_image_dom_fitzpatrick`. -/
recall interior_dom_eq_interior_fst_image_dom_fitzpatrick

/-- For a maximally monotone operator, the closure of the range agrees with
the closure of the second-coordinate projection `Q₂ (dom F_A)`, formalized by
`A.sndImageDomFitzpatrick`. -/
theorem closure_range_eq_closure_snd_image_dom_fitzpatrick_of_maximal
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) :
    closure A.range = closure A.sndImageDomFitzpatrick := by
  calc
    closure A.range = closure (A⁻¹).fstImageDomFitzpatrick := by
      simpa using
        closure_dom_eq_closure_fst_image_dom_fitzpatrick (A⁻¹) (Maximal.inverse hA)
    _ = closure A.sndImageDomFitzpatrick := by
      rw [← sndImageDomFitzpatrick_eq_fstImageDomFitzpatrick_inverse A]

/-- For a maximally monotone operator, the interior of the range agrees with
the interior of the second-coordinate projection `Q₂ (dom F_A)`, formalized by
`A.sndImageDomFitzpatrick`. -/
theorem interior_range_eq_interior_snd_image_dom_fitzpatrick_of_maximal
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) :
    interior A.range = interior A.sndImageDomFitzpatrick := by
  calc
    interior A.range = interior (A⁻¹).fstImageDomFitzpatrick := by
      simpa using
        interior_dom_eq_interior_fst_image_dom_fitzpatrick (A⁻¹) (Maximal.inverse hA)
    _ = interior A.sndImageDomFitzpatrick := by
      rw [← sndImageDomFitzpatrick_eq_fstImageDomFitzpatrick_inverse A]

omit [CompleteSpace H] in
/-- Helper for Corollary 21.14: maximal monotonicity gives a nonempty graph, which is the setup
needed to package the Fitzpatrick function into `Γ₀(H × H)`. -/
private theorem graphNonemptyOfMaximalForFitzpatrick
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) :
    (gra A).Nonempty := by
  by_contra hgraph
  have hnone : ∀ x u : H, u ∉ A x := by
    intro x u hxu
    exact hgraph ⟨(x, u), hxu⟩
  have hzero : (0 : H) ∈ A (0 : H) := by
    -- If the graph were empty, the Minty test would be vacuous at `(0, 0)`.
    refine (Maximal.mem_iff hA 0 0).2 ?_
    intro y v hv
    exact False.elim (hnone y v hv)
  exact hnone 0 0 hzero

omit [CompleteSpace H] in
/-- Helper for Corollary 21.14: the first-coordinate projection `Q₁ (dom F_A)` is convex for a
maximally monotone operator. -/
private theorem convexFstImageDomFitzpatrickOfMaximal
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) :
    Convex ℝ A.fstImageDomFitzpatrick := by
  let FA : H × H → Set.Ioi (⊥ : EReal) :=
    ERealFunction.properIoi (F[A])
      (fitzpatrickFunction_isProper_of_graph_nonempty_of_monotone
        A (graphNonemptyOfMaximalForFitzpatrick A hA) (Maximal.isMonotone hA))
  have hFA : FA ∈ Γ₀(H × H) := by
    -- Package the Fitzpatrick owner through the canonical `Γ₀(H × H)` interface.
    simpa [FA] using
      fitzpatrickFunction_mem_gammaZero
        A (graphNonemptyOfMaximalForFitzpatrick A hA) (Maximal.isMonotone hA)
  -- Project the convex effective domain to the first coordinate.
  simpa [fstImageDomFitzpatrick, FA, ERealFunction.effectiveDomain, ERealFunction.dom] using
    hFA.2.convex_effectiveDomain.linear_image (ContinuousLinearMap.fst ℝ H H).toLinearMap

omit [CompleteSpace H] in
/-- Helper for Corollary 21.14: the second-coordinate projection `Q₂ (dom F_A)` is convex for a
maximally monotone operator, via the inverse-domain bridge. -/
private theorem convexSndImageDomFitzpatrickOfMaximal
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) :
    Convex ℝ A.sndImageDomFitzpatrick := by
  -- Route correction: use the inverse-projection identity instead of unfolding `Prod.snd`.
  rw [sndImageDomFitzpatrick_eq_fstImageDomFitzpatrick_inverse A]
  exact convexFstImageDomFitzpatrickOfMaximal (A⁻¹) (Maximal.inverse hA)

/-- Corollary 21.14: for a maximally monotone operator, the closure of the domain is convex.
-/
theorem convex_closure_dom_of_maximal
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) :
    Convex ℝ (closure A.dom) := by
  -- Rewrite the target to the Fitzpatrick-domain projection, then close by convexity of closure.
  rw [closure_dom_eq_closure_fst_image_dom_fitzpatrick A hA]
  exact convex_closure_of_convex (convexFstImageDomFitzpatrickOfMaximal A hA)

/-- For a maximally monotone operator, the interior of the domain is convex.
-/
theorem convex_interior_dom_of_maximal
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) :
    Convex ℝ (interior A.dom) := by
  -- The interior identity reduces the claim to convexity of `Q₁ (dom F_A)`.
  rw [interior_dom_eq_interior_fst_image_dom_fitzpatrick A hA]
  exact convex_interior_of_convex (convexFstImageDomFitzpatrickOfMaximal A hA)

/-- For a maximally monotone operator, the closure of the range is convex.
-/
theorem convex_closure_range_of_maximal
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) :
    Convex ℝ (closure A.range) := by
  -- Rewrite through the range-side projection identity and preserve convexity under closure.
  rw [closure_range_eq_closure_snd_image_dom_fitzpatrick_of_maximal A hA]
  exact convex_closure_of_convex (convexSndImageDomFitzpatrickOfMaximal A hA)

/-- For a maximally monotone operator, the interior of the range is convex.
-/
theorem convex_interior_range_of_maximal
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) :
    Convex ℝ (interior A.range) := by
  -- The interior range identity reduces to convexity of `Q₂ (dom F_A)`.
  rw [interior_range_eq_interior_snd_image_dom_fitzpatrick_of_maximal A hA]
  exact convex_interior_of_convex (convexSndImageDomFitzpatrickOfMaximal A hA)

end SetValuedOperator
