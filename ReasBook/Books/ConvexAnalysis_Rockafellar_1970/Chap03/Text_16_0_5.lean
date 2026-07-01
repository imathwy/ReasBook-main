import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_5_7
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u u' v v' w'

section

open scoped Rockafellar

variable {E : Type u} {EStar : Type u'} {F : Type v} {FStar : Type v'} {L : Type w'}
variable [SupSet L] [InfSet L] [Sub L]
variable [HasPairing E EStar L] [HasPairing F FStar L]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 16.0.5 rewrites the closure-free instance of the dual precomposition
  formula `(gA)^* = A^* g^*` as an explicit supremum-infimum identity at a fixed `x*`.
- `core/canonical`: the project owners are `convexConjugate` for Fenchel conjugation and
  `Function.linearImage` for the infimum over a fiber.
- `bridge/view`: the displayed left-hand side is the pointwise formula
  `convexConjugate_eq_iSup_pairing_sub` for `g ∘ A`, while the right-hand side is the pointwise
  formula `Function.linearImage_eq_sInf_image` for the dual-side map applied to
  `convexConjugate g`.

Domain-style sampling used here:
- `convexConjugate` and `convexConjugate_eq_iSup_pairing_sub` from Defn 12.2;
- `Function.linearImage`, its notation `◁`, and `Function.linearImage_eq_sInf_image` from
  Theorem 5.7;
- map-fiber owners via `Function.linearImage`.

Primitive data vs derived API:
- primitive inputs: a primal map `A`, a dual-side map `AStar`, a function `g`, a
  closure-free duality hypothesis `hdual : (g ∘ A)⋆ = AStar ◁ g⋆`, and the evaluation point
  `xStar`;
- derived API: the owner-level pointwise equality
  `(g ∘ A)⋆ xStar = (AStar ◁ g⋆) xStar` and its displayed supremum-infimum expansion.

Layer target: `bridge/view`; the source sentence is a pointwise unpacking of the closure-free dual
formula, so the theorem is stated directly in that supremum-infimum form.

Ambient note: the theorem itself only uses the owner declarations `convexConjugate` and
`Function.linearImage` plus maps `A` and `AStar`, so the API stays at the primitive
pairing-and-inf/sup layer. The adjoint-based Euclidean wording is a downstream specialization.
-/

-- Proof sketch: evaluate the owner-level equality `hdual` at `xStar`.
/-- Evaluating the closure-free dual formula at `xStar` gives the pointwise owner equality
`(g ∘ A)⋆ xStar = (AStar ◁ g⋆) xStar`. -/
theorem
    convexConjugate_comp_map_apply_eq_linearImage_apply_of_closureFreeDualFormula
    (A : E → F) (AStar : FStar → EStar) (g : F → L)
    (hdual : (g ∘ A)⋆ = AStar ◁ g⋆)
    (xStar : EStar) :
    (g ∘ A)⋆ xStar = (AStar ◁ g⋆) xStar := by
  simpa using congrFun hdual xStar

/-- Text 16.0.5: when the closure operation is unnecessary in the dual formula
`(g ∘ A)^* = AStar ◁ g^*`, evaluating at `x*` identifies the Fenchel supremum of
`x ↦ g (A x)` with the infimum of `g*` over the dual fiber `AStar y* = x*`. The source's adjoint
Euclidean statement is a specialization. -/
theorem convexConjugate_comp_map_apply_eq_sInf_image_conjugate_of_closureFreeDualFormula
    (A : E → F) (AStar : FStar → EStar) (g : F → L)
    (hdual : (g ∘ A)⋆ = AStar ◁ g⋆)
    (xStar : EStar) :
    (g ∘ A)⋆ xStar =
      sInf (g⋆ '' {yStar : FStar | AStar yStar = xStar}) := by
  simpa [Function.linearImage_eq_sInf_image] using
    convexConjugate_comp_map_apply_eq_linearImage_apply_of_closureFreeDualFormula
      A AStar g hdual xStar

-- Proof sketch: rewrite the left-hand side by `convexConjugate_eq_iSup_pairing_sub`.
/-- Source-view supremum-infimum restatement of Text 16.0.5 at fixed `xStar`. -/
theorem iSup_pairing_sub_comp_map_eq_sInf_image_conjugate_of_closureFreeDualFormula
    (A : E → F) (AStar : FStar → EStar) (g : F → L)
    (hdual : (g ∘ A)⋆ = AStar ◁ g⋆)
    (xStar : EStar) :
    (⨆ x : E, (⟪x, xStar⟫ₚ - g (A x))) =
      sInf (g⋆ '' {yStar : FStar | AStar yStar = xStar}) := by
  simpa [convexConjugate_eq_iSup_pairing_sub] using
    convexConjugate_comp_map_apply_eq_sInf_image_conjugate_of_closureFreeDualFormula
      A AStar g hdual xStar

end
