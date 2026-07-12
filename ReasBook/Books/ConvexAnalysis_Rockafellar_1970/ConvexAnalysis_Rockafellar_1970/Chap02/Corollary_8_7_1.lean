import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_6
import ConvexAnalysis_Rockafellar_1970.Chap02.Corollary_7_2_1
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_8_4
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_8_7

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Bornology
open scoped Rockafellar

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 8.7.1 says that for a closed convex function, boundedness of one
  nonempty real sublevel set forces boundedness of every real sublevel set.
- `core/canonical`: the owner predicates are the chapter notions `Function.IsConvex` and
  mathlib's `LowerSemicontinuous` together with
  `Bornology.IsBounded` for subsets of `E`.
- `bridge/view`: Theorem 8.7 identifies the recession cone of every nonempty real sublevel set
  with the common owner `Function.recessionCone ((f)₀⁺)` in the proper branch, Corollary 7.2.1
  identifies every real sublevel set with `dom(f)` in the improper branch, and Theorem 8.4
  converts boundedness of a nonempty closed convex set into triviality of its recession cone.
- Primitive data vs derived API: the primitive inputs are the function `f`, one real level
  `lambda0`, the closed/convex hypotheses on `f`, and the nonemptiness and boundedness of one
  sublevel set; boundedness of every real sublevel set is the derived conclusion.

Domain-style sampling used here:
- the chapter owner theorem `Function.IsConvex.convex_le` from Theorem 4.6;
- `Function.IsConvex.eq_bot_of_mem_dom_of_lowerSemicontinuous` from
  Corollary 7.2.1;
- `recessionCone_sublevelSet_eq_functionRecessionCone` from Theorem 8.7;
- `Convex.isBounded_iff_recessionCone_eq_singleton_zero` from Theorem 8.4.

Layer target: `source-facing`; the corollary remains a statement about bounded sublevel sets, but
its proof and ambient API are refined to the existing owner declarations instead of reaching back
to the lower-level translate-profile API from Theorem 8.6.
- Ambient-space refinement: although the source states the corollary on `R^n`, the surrounding
  owner API in Chapter 8 already lives on arbitrary finite-dimensional real normed spaces, so the
  corollary is stated at that intrinsic level and `EuclideanSpace ℝ (Fin n)` is treated only as a
  specialization.
- Scalar refinement boundary: this item stays over `ℝ` because the boundedness/recession bridge
  used here (`Convex.isBounded_iff_recessionCone_eq_singleton_zero`) is currently available only
  on the real asymptotic-cone layer.
-/

namespace Function.IsConvex

variable {f : E → WithBotTop ℝ}

/-- Corollary 8.7.1: if a closed convex function on a finite-dimensional real normed space has one
nonempty bounded real sublevel set, then every real sublevel set is bounded. -/
-- Proof sketch: closedness and convexity of every sublevel set come from lower semicontinuity and
-- the chapter owner theorem `Function.IsConvex.convex_le`. Theorem 8.4 turns boundedness of the
-- nonempty `lambda0`-sublevel set into the triviality of its recession cone. In the proper case,
-- if the `lambda`-sublevel set is nonempty, Theorem 8.7 identifies its recession cone with that
-- same common cone, so Theorem 8.4 gives boundedness again. In the improper case, Corollary 7.2.1
-- forces every finite sublevel set to equal `dom(f)`, so all real sublevel sets are already the
-- same bounded set. Empty sublevel sets are bounded automatically.
theorem isBounded_sublevel_of_nonempty_bounded_sublevel
    (hf_convex : Function.IsConvex ℝ f) (hf_closed : LowerSemicontinuous f)
    (lambda0 : ℝ)
    (hlambda0_nonempty : ({x : E | f x ≤ lambda0}).Nonempty)
    (hlambda0_bounded : IsBounded {x : E | f x ≤ lambda0}) :
    ∀ lambda : ℝ, IsBounded {x : E | f x ≤ lambda} := by
  let sublevel : ℝ → Set E := fun μ ↦ f ⁻¹' Set.Iic (μ : WithBotTop ℝ)
  have hsublevel_closed (μ : ℝ) : IsClosed (sublevel μ) := by
    simpa [sublevel] using hf_closed.isClosed_preimage (μ : WithBotTop ℝ)
  have hsublevel_convex (μ : ℝ) : Convex ℝ (sublevel μ) := by
    simpa [sublevel] using hf_convex.convex_le (μ : WithBotTop ℝ)
  intro lambda
  by_cases hf_proper : Function.IsProper f
  · have hlambda0_recession : 0⁺[ℝ] (sublevel lambda0) = ({0} : Set E) :=
      ((hsublevel_convex lambda0).isBounded_iff_recessionCone_eq_singleton_zero
        (hsublevel_closed lambda0)
        (by simpa [sublevel] using hlambda0_nonempty)).mp <|
        by simpa [sublevel] using hlambda0_bounded
    by_cases hlambda_nonempty : (sublevel lambda).Nonempty
    · have hlambda_recession :
          0⁺[ℝ] (sublevel lambda) = Function.recessionCone ((f)₀⁺) := by
        simpa [sublevel, Set.mem_preimage, Set.mem_Iic] using
          hf_convex.recessionCone_sublevelSet_eq_functionRecessionCone
            hf_proper hf_closed lambda hlambda_nonempty
      have hlambda0_recession' :
          0⁺[ℝ] (sublevel lambda0) = Function.recessionCone ((f)₀⁺) := by
        simpa [sublevel, Set.mem_preimage, Set.mem_Iic] using
          hf_convex.recessionCone_sublevelSet_eq_functionRecessionCone
            hf_proper hf_closed lambda0 hlambda0_nonempty
      have hlambda_recession_zero : 0⁺[ℝ] (sublevel lambda) = ({0} : Set E) := by
        calc
          0⁺[ℝ] (sublevel lambda) = Function.recessionCone ((f)₀⁺) := hlambda_recession
          _ = 0⁺[ℝ] (sublevel lambda0) := hlambda0_recession'.symm
          _ = ({0} : Set E) := hlambda0_recession
      simpa [sublevel] using
        ((hsublevel_convex lambda).isBounded_iff_recessionCone_eq_singleton_zero
          (hsublevel_closed lambda) hlambda_nonempty).mpr
          hlambda_recession_zero
    · have hlambda_empty : sublevel lambda = ∅ := Set.not_nonempty_iff_eq_empty.mp hlambda_nonempty
      have hbounded_sublevel : IsBounded (sublevel lambda) := by simp [hlambda_empty]
      simpa [sublevel, Set.mem_preimage, Set.mem_Iic] using hbounded_sublevel
  · have hsublevel_eq_dom :
        ∀ μ : ℝ, sublevel μ = dom(f) := by
      intro μ
      ext x
      constructor
      · intro hx
        exact lt_of_le_of_lt hx (WithBotTop.coe_lt_top μ)
      · intro hx
        have hbot :
            f x = ⊥ :=
          hf_convex.eq_bot_of_mem_dom_of_lowerSemicontinuous hf_closed hf_proper hx
        simp [sublevel, hbot]
    have hlambda0_bounded' : IsBounded (sublevel lambda0) := by
      simpa [sublevel, Set.mem_preimage, Set.mem_Iic] using hlambda0_bounded
    have hbounded_dom : IsBounded (dom(f)) := by
      simpa [hsublevel_eq_dom lambda0] using hlambda0_bounded'
    have hbounded_sublevel : IsBounded (sublevel lambda) := by
      simpa [hsublevel_eq_dom lambda] using hbounded_dom
    simpa [sublevel, Set.mem_preimage, Set.mem_Iic] using hbounded_sublevel

end Function.IsConvex

end
