import BauschkeLean.Chap18.Corollary_18_11
import BauschkeLean.Chap16.Remark_16_2

-- Declarations for this item will be appended below by the statement pipeline.

open SetValuedOperator

universe u

namespace ERealFunction

section DifferentiabilityAndStrictConvexity

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {f : H → Set.Ioi (⊥ : EReal)}

-- Semantic recall: `lean_leansearch` returned only generic convex-analysis lemmas, so the local
-- chapter owner `Corollary_18_11` remains the verified canonical source for this item.
/- Source/core/bridge triage:
- `source-facing`: Corollary 18.12 specializes the strict-convexity side of Corollary 18.11 from
  arbitrary nonempty convex subsets of `dom (∂ f*)` to the source-facing set
  `interior (effectiveDomain f*)`, then reapplies the same owner statement to `f*`.
- `core/canonical`: Corollary 18.11 is the chapter owner abstraction for the
  Gâteaux-differentiability/strict-convexity equivalence.
- `bridge/view`: the extra hypothesis `hdom_conj` is exactly the bridge from the canonical owner
  domain `dom (∂ (f∗[hf]))` to the source-facing interior-effective-domain presentation.

This file therefore keeps only the two source-facing corollaries and does not introduce a parallel
wrapper around the Corollary 18.11 owner statement. -/

/-! Corollary 18.12 is formalized below as the two source clauses `(1)` and `(2)`, so each
equivalence remains a separate labeled theorem. -/

/-- Helper for Corollary 18.12: if the subdifferential domain of `f*`, represented by `f∗[hf]`,
agrees with `interior (effectiveDomain (f∗[hf]))`, then that interior effective domain is
nonempty. -/
lemma interiorEffectiveDomain_gammaZeroConjugate_nonempty_of_domEq
    (hf : f ∈ Γ₀(H))
    (hdom_conj :
      SetValuedOperator.dom (∂ (f∗[hf])) = interior (effectiveDomain (f∗[hf]))) :
    (interior (effectiveDomain (f∗[hf]))).Nonempty := by
  have hfstar : f∗[hf] ∈ Γ₀(H) := gammaZeroConjugate_mem_gammaZero hf
  have hnonempty_dom : (SetValuedOperator.dom (∂ (f∗[hf]))).Nonempty := by
    -- Remark 16.2 supplies a point of the conjugate subdifferential domain.
    simpa using subdifferential_dom_nonempty_of_mem_gammaZero (f := f∗[hf]) hfstar
  -- The domain-identification hypothesis transports that nonemptiness to the source-facing set.
  rwa [hdom_conj] at hnonempty_dom

omit [CompleteSpace H] in
/-- Helper for Corollary 18.12: strict convexity on `interior (effectiveDomain (f∗[hf]))`
restricts to every nonempty subset of `dom (∂ (f∗[hf]))` once `hdom_conj` identifies these two
sets. -/
lemma strictlyConvexOn_conjugateSubdiffDom_of_strictlyConvexOn_interiorEffectiveDomain
    (hf : f ∈ Γ₀(H))
    (hdom_conj :
      SetValuedOperator.dom (∂ (f∗[hf])) = interior (effectiveDomain (f∗[hf])))
    (hstrict : StrictlyConvexOn (f∗[hf]) (interior (effectiveDomain (f∗[hf]))))
    {C : Set H} (hC_nonempty : C.Nonempty)
    (hC_subset : C ⊆ SetValuedOperator.dom (∂ (f∗[hf]))) :
    StrictlyConvexOn (f∗[hf]) C := by
  -- Restrict the source-facing strict-convexity hypothesis along the domain identification.
  refine StrictlyConvexOn.mono hstrict hC_nonempty ?_
  simpa [hdom_conj] using hC_subset

/-- Helper for Corollary 18.12: the packaged double Fenchel conjugate of a `Γ₀(H)` function is
the original function. -/
lemma doubleGammaZeroConjugate_eq
    (hf : f ∈ Γ₀(H)) :
    (f∗[hf])∗[gammaZeroConjugate_mem_gammaZero hf] = f := by
  -- Corollary 13.38 gives the pointwise biconjugate identity on the `EReal`-valued coercions.
  funext x
  apply Subtype.ext
  simpa using congrFun (biconjugate_eq_of_mem_gammaZero hf) x

-- Proof sketch: `Remark 16.2` makes `dom (∂ (f∗[hf]))` nonempty, so `hdom_conj` upgrades the
-- source-facing set `interior (effectiveDomain (f∗[hf]))` to a nonempty convex subset of the
-- owner domain `dom (∂ (f∗[hf]))`. Apply Corollary 18.11 to that subset for the forward
-- implication, and restrict a strict-convexity hypothesis on the whole interior effective domain
-- along `hdom_conj` for the reverse implication.
/-- Clause (1) of Corollary 18.12: if `f ∈ Γ₀(H)` and both `f` and its Fenchel conjugate `f*`,
represented by `f∗[hf]`, satisfy `dom (∂ ·) = interior (effectiveDomain ·)`, then the
finite-valued representative of `f` is Gâteaux differentiable on
`interior (effectiveDomain f)` if and only if `f*` is strictly convex on
`interior (effectiveDomain f*)`. -/
theorem
    gateauxDifferentiableOn_interior_iff_strictlyConvexOn_conjugateInterior
    (hf : f ∈ Γ₀(H))
    (hdom : SetValuedOperator.dom (∂ f) = interior (effectiveDomain f))
    (hdom_conj :
      SetValuedOperator.dom (∂ (f∗[hf])) = interior (effectiveDomain (f∗[hf]))) :
    GateauxDifferentiableOn (fun x ↦ (f x : EReal).toReal) (interior (effectiveDomain f)) ↔
      StrictlyConvexOn (f∗[hf]) (interior (effectiveDomain (f∗[hf]))) := by
  constructor
  · intro hdiff
    have hstrict :=
      (gateauxDifferentiableOn_interior_effectiveDomain_iff_strictlyConvexOn_conjugateSubdiffDom
        (f := f) hf hdom).1 hdiff
    have hinter_nonempty :
        (interior (effectiveDomain (f∗[hf]))).Nonempty :=
      interiorEffectiveDomain_gammaZeroConjugate_nonempty_of_domEq
        (f := f) hf hdom_conj
    have hinter_convex : Convex ℝ (interior (effectiveDomain (f∗[hf]))) := by
      have hfstar : f∗[hf] ∈ Γ₀(H) := gammaZeroConjugate_mem_gammaZero hf
      -- The conjugate effective domain is convex, and convexity passes to the interior.
      simpa using hfstar.2.convex_effectiveDomain.interior
    have hinter_subset :
        interior (effectiveDomain (f∗[hf])) ⊆ SetValuedOperator.dom (∂ (f∗[hf])) := by
      -- The source-facing set is exactly the owner-domain set under `hdom_conj`.
      simp [hdom_conj]
    -- Specialize Corollary 18.11 to the source-facing set `interior (effectiveDomain (f∗[hf]))`.
    exact hstrict hinter_nonempty hinter_convex hinter_subset
  · intro hstrict
    -- Route correction: feed Corollary 18.11 the restricted strict-convexity family instead of
    -- unfolding the conjugate-side owner domain inside the main proof.
    refine
      (gateauxDifferentiableOn_interior_effectiveDomain_iff_strictlyConvexOn_conjugateSubdiffDom
        (f := f) hf hdom).2 ?_
    intro C hC_nonempty _ hC_subset
    exact
      strictlyConvexOn_conjugateSubdiffDom_of_strictlyConvexOn_interiorEffectiveDomain
        (f := f) hf hdom_conj hstrict hC_nonempty hC_subset

-- Proof sketch: apply clause (1) to the canonical conjugate `f∗[hf]`. The owner theorem
-- `gammaZeroConjugate_mem_gammaZero` supplies the new `Γ₀(H)` hypothesis, `hdom_conj` is now the
-- first domain-identification assumption, and `hdom` becomes the second after rewriting the double
-- conjugate back to `f` via `gammaZeroConjugate_gammaZeroConjugate`.
/-- Clause (2) of Corollary 18.12: if `f ∈ Γ₀(H)` and both `f` and its Fenchel conjugate `f*`,
represented by `f∗[hf]`, satisfy `dom (∂ ·) = interior (effectiveDomain ·)`, then `f` is
strictly convex on `interior (effectiveDomain f)` if and only if `f*` is Gâteaux differentiable
on `interior (effectiveDomain f*)`. -/
theorem
    strictlyConvexOn_interior_iff_gateauxDifferentiableOn_conjugateInterior
    (hf : f ∈ Γ₀(H))
    (hdom : SetValuedOperator.dom (∂ f) = interior (effectiveDomain f))
    (hdom_conj :
      SetValuedOperator.dom (∂ (f∗[hf])) = interior (effectiveDomain (f∗[hf]))) :
    StrictlyConvexOn f (interior (effectiveDomain f)) ↔
      GateauxDifferentiableOn (fun x ↦ (f∗[hf] x : EReal).toReal)
        (interior (effectiveDomain (f∗[hf]))) := by
  have hfstar : f∗[hf] ∈ Γ₀(H) := gammaZeroConjugate_mem_gammaZero hf
  have hdom_double :
      SetValuedOperator.dom (∂ ((f∗[hf])∗[hfstar])) =
        interior (effectiveDomain ((f∗[hf])∗[hfstar])) := by
    -- Rewrite the double conjugate back to `f` before reusing the first clause.
    simpa [doubleGammaZeroConjugate_eq (f := f) hf] using hdom
  have hmain :=
    gateauxDifferentiableOn_interior_iff_strictlyConvexOn_conjugateInterior
      (f := f∗[hf]) hfstar hdom_conj
        hdom_double
  -- Turn the first clause around after transporting the double conjugate back to `f`.
  simpa [doubleGammaZeroConjugate_eq (f := f) hf] using hmain.symm

/-- Corollary 18.12: if `f ∈ Γ₀(H)` and both `f` and its Fenchel conjugate `f*`, represented by
`f∗[hf]`, satisfy `dom (∂ ·) = interior (effectiveDomain ·)`, then Gâteaux differentiability of
`f` on `interior (effectiveDomain f)` is equivalent to strict convexity of `f*` on
`interior (effectiveDomain f*)`, and strict convexity of `f` on `interior (effectiveDomain f)` is
equivalent to Gâteaux differentiability of `f*` on `interior (effectiveDomain f*)`. -/
theorem gateauxDifferentiableOn_interior_effectiveDomain_iff_strictlyConvexOn_interior_effectiveDomain_gammaZeroConjugate
    (hf : f ∈ Γ₀(H))
    (hdom : SetValuedOperator.dom (∂ f) = interior (effectiveDomain f))
    (hdom_conj :
      SetValuedOperator.dom (∂ (f∗[hf])) = interior (effectiveDomain (f∗[hf]))) :
    (GateauxDifferentiableOn (fun x ↦ (f x : EReal).toReal) (interior (effectiveDomain f)) ↔
        StrictlyConvexOn (f∗[hf]) (interior (effectiveDomain (f∗[hf])))) ∧
      (StrictlyConvexOn f (interior (effectiveDomain f)) ↔
        GateauxDifferentiableOn (fun x ↦ (f∗[hf] x : EReal).toReal)
          (interior (effectiveDomain (f∗[hf])))) := by
  -- Package the two clause theorems into the single source-facing corollary entry.
  constructor
  · exact gateauxDifferentiableOn_interior_iff_strictlyConvexOn_conjugateInterior
      (f := f) hf hdom hdom_conj
  · exact strictlyConvexOn_interior_iff_gateauxDifferentiableOn_conjugateInterior
      (f := f) hf hdom hdom_conj

end DifferentiabilityAndStrictConvexity

end ERealFunction
