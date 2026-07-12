import ConvexAnalysis_Rockafellar_1970.Chap03.Text_13_0_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_13_1_4
import ConvexAnalysis_Rockafellar_1970.Chap06.Theorem_6_30_4

noncomputable section

open scoped Rockafellar

universe u

section PairingSwap

variable {X : Type u} {XStar : Type*} {α : Type*}
variable [Neg XStar]
variable [AddCommGroup α] [ConditionallyCompleteLattice α] [IsOrderedAddMonoid α]
variable [HasPairing X XStar α] [HasPairing XStar X α]
variable [HasPairingSwap X XStar α] [HasPairingNegRight X XStar α]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Definition 39.0.12 distinguishes the two readings of the same convex-set
  pairing, through the convex indicator `δ[α](· | C)` on the supremum side and the concave
  function `-δ[α](· | C)` on the infimum side.
- `core/canonical`: the chapter already owns those two readings as the support-function owner
  `supportFunction C`, written `δᵛ[WithBotTop α](· | C)`, together with the concave conjugate
  `concaveConjugate (-(δ[α](· | C) : X → WithBotTop α))`.
- `bridge/view`: this file is therefore a pure bridge file. It does not introduce a separate
  orientation owner, because the mathematics already lives on those canonical function owners.
  The public surface is direct recall of the supremum-side equality plus the infimum-side bridge
  to `-δᵛ[WithBotTop α](-xStar | C)` and its `sInf` formula.

Primary mathematical domain:
- support-function and infimum-pairing views of a convex set at the pairing level.

Domain-style sampling used here:
- `convexConjugate_indicatorFunction_eq_supportFunction` from `Chap03.Text_13_1_4`;
- `concaveConjugate` from `Chap06.Definition_6_30_4`;
- `supportFunction` and `supportFunction_def` from `Chap01.Defintion_4_8_2`;
- `neg_supportFunction_neg_eq_sInf_image_pairing` from `Chap03.Text_13_0_2`.

Primitive data vs derived API:
- primitive data introduced here: none beyond the ambient set `C`;
- derived API: the supremum-side direct recall
  `convexConjugate_indicatorFunction_eq_supportFunction`, together with the
  infimum-side bridge from `concaveConjugate (-(δ[α](· | C) : X → WithBotTop α))` to the sign-dual support
  function formula and its pointwise `sInf` specialization.

Abstraction-layer choice:
- the canonical owner is the generic pairing bridge on `(X, XStar)`;
- this file intentionally avoids extra self-pairing wrapper declarations, since they are strict
  specializations of the generic owner and do not add new mathematical structure.

Layer target: `bridge/view`.

Notation evaluation:
- the source writes the same bracket notation `⟨C, x⋆⟩` for both readings, with the choice of
  branch supplied by context;
- because this file deliberately avoids introducing a second owner object for that contextual
  choice, no new notation is added here;
- the public surface remains the explicit owner formulas already used elsewhere in the chapter.
-/

/-- In the infimum orientation, the concave conjugate of the negative indicator is the sign-dual
support-function pairing `xStar ↦ -δᵛ[WithBotTop α](-xStar | C)`. -/
@[simp]
theorem concaveConjugate_neg_indicatorFunction_eq_neg_supportFunction_neg (C : Set X) :
    concaveConjugate (-(δ(· | C) : X → WithBotTop α)) =
      fun xStar : XStar ↦ -δᵛ(-xStar | C) := by
  have hnegfun : (-(-(δ(· | C) : X → WithBotTop α))) = (δ(· | C)) := by
    funext x
    simp
  ext xStar
  calc
    concaveConjugate (-(δ(· | C) : X → WithBotTop α)) xStar
        = -((-(-(δ(· | C) : X → WithBotTop α)))⋆ (-xStar)) := by
          simpa using
            concaveConjugate_eq_neg_convexConjugate_neg_apply
              (-(δ(· | C) : X → WithBotTop α)) xStar
    _ = -((δ(· | C))⋆ (-xStar : XStar)) := by
          congr 1
          exact
            congrArg
              (fun f : X → WithBotTop α ↦ (f⋆ : XStar → WithBotTop α) (-xStar))
              hnegfun
    _ = -δᵛ(-xStar | C) := by
          congr 1
          simpa using
            (convexConjugate_indicatorFunction_eq_supportFunction_pointwise
              (C := C) (xStar := -xStar))

@[simp]
theorem concaveConjugate_neg_indicatorFunction_eq_neg_supportFunction_neg_pointwise
    (C : Set X) (xStar : XStar) :
    concaveConjugate (-(δ(· | C) : X → WithBotTop α)) xStar =
      -δᵛ(-xStar | C) := by
  simpa using
    congrFun
      (concaveConjugate_neg_indicatorFunction_eq_neg_supportFunction_neg
        C) xStar

/-- In the infimum orientation, the oriented-set pairing is exactly the infimum of the pairings
`⟪xStar, x⟫ₚ` over `x ∈ C`. -/
theorem concaveConjugate_neg_indicatorFunction_eq_sInf_image_pairing
    (C : Set X) (xStar : XStar) :
    concaveConjugate (-(δ(· | C) : X → WithBotTop α)) xStar =
      sInf ((fun x ↦ (⟪xStar, x⟫ₚ : WithBotTop α)) '' C) := by
  rw [concaveConjugate_neg_indicatorFunction_eq_neg_supportFunction_neg_pointwise (C := C)]
  simpa using
    neg_supportFunction_neg_eq_sInf_image_pairing (C := C) (xStar := xStar)

end PairingSwap

end
