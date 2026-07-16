import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_2
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_2
import ConvexAnalysis_Rockafellar_1970.Chap08.Definition_38_5_2

noncomputable section

open scoped RealInnerProductSpace Rockafellar

universe u

namespace Function

section

variable {E : Type u}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {f g : E → EReal}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Proposition 38.5.6 records that the two Chapter 38 formulas defining the
  function inner product still make sense for improper convex/concave functions, and that the two
  relative-interior hypotheses from Proposition 38.5.3 still suffice in that improper setting.
- `core/canonical`: the existing owner layer is `Function.innerProduct` together with the
  existence predicate `Function.HasInnerProduct`.
- `bridge/view`: the source's displayed formulas are already the canonical `iSup`/`iInf`
  expressions from `Definition_38_5_2`, so the first clause is a thin source-facing bridge to
  `HasInnerProduct`, while the remaining clauses are improper-case variants of the two
  relative-interior existence criteria from `Proposition_38_5_3`.

Domain-style sampling used here:
- `Function.innerProduct`, `Function.HasInnerProduct`, and `Function.hasInnerProduct_iff` from
  `Definition_38_5_2`;
- the proper-case relative-interior criteria from `Proposition_38_5_3`;
- the Chapter 3/Chapter 6 owners `f⋆` and `concaveConjugate g`.

Layer target: `source-facing`, stated directly on the existing Chapter 38 owner API rather than
through a new improperness wrapper.
-/

-- Proof sketch: unfold `HasInnerProduct` using `hasInnerProduct_iff`, then rewrite the left-hand
-- side with `innerProduct_eq_iSup_concaveConjugate_sub`. This shows that the textbook supremum and
-- infimum formulas remain the defining comparison even without properness hypotheses.
/-- Proposition 38.5.6 (1): the two formulas
`sup_x (g^* x - f x)` and `inf_y (f^* y - g y)` defining the Chapter 38 function inner product are
still meaningful for arbitrary extended-real-valued `f` and `g`; equivalently, `HasInnerProduct`
is exactly equality between those two extrema without any properness assumption. -/
theorem hasInnerProduct_iff_iSup_concaveConjugate_sub_eq_iInf_convexConjugate_sub
    (f : E → EReal) (g : E → EReal) :
    HasInnerProduct f g ↔
      (⨆ x : E, concaveConjugate g x - f x) = ⨅ y : E, f⋆ y - g y := sorry

-- Proof sketch: apply the same closed-case Fenchel duality argument as in Proposition 38.5.3,
-- but observe that Definition 38.5.2 already phrases the Chapter 38 pairing purely in terms of
-- the two conjugate extrema, which remain meaningful for improper functions. The relative-interior
-- qualification on `riDom(f)` and `riDom(-concaveConjugate g)` therefore still yields existence of
-- `HasInnerProduct f g` without properness assumptions.
/-- Proposition 38.5.6 (2): if `f` is convex, `g` is concave, `-g` is lower semicontinuous, and
`ri (dom f)` meets `ri (dom g^*)`, rendered by
`riDom(f)` meeting `riDom(-concaveConjugate g)`, then the Chapter 38 inner product of `f` and `g`
exists even when one of the two functions is improper. -/
theorem hasInnerProduct_of_g_closed_and_nonempty_inter_riDom_f_concaveConjugate_improper
    (hf_convex : f.IsConvex ℝ)
    (hg_concave : g.IsConcave ℝ)
    (hg_closed : LowerSemicontinuous (-g))
    (hri : (riDom(f) ∩ riDom(-(concaveConjugate g : E → EReal))).Nonempty) :
    HasInnerProduct f g := sorry

-- Proof sketch: this is the symmetric improper-case variant of Proposition 38.5.3. The closed
-- convex side `f` identifies the primal objective with its conjugate-side formulation, and the
-- relative-interior qualification `riDom(-g) ∩ riDom(f⋆) ≠ ∅` gives the same zero-duality-gap
-- conclusion even when properness is dropped.
/-- Proposition 38.5.6 (3): if `f` is convex and lower semicontinuous, `g` is concave, and
`ri (dom g)` meets `ri (dom f^*)`, rendered by `riDom(-g)` meeting `riDom(f⋆)`, then the Chapter
38 inner product of `f` and `g` exists even when one of the two functions is improper. -/
theorem hasInnerProduct_of_f_closed_and_nonempty_inter_riDom_g_convexConjugate_improper
    (hf_convex : f.IsConvex ℝ)
    (hf_closed : LowerSemicontinuous f)
    (hg_concave : g.IsConcave ℝ)
    (hri : (riDom(-g) ∩ riDom(f⋆)).Nonempty) :
    HasInnerProduct f g := sorry

end

end Function
