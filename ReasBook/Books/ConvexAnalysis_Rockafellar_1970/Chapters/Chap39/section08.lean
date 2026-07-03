import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_39_8_1 (from Chap08) -/
noncomputable section

open scoped Rockafellar

universe u v w

namespace Set

section

attribute [local instance] Classical.propDecidable

variable {X : Type u} {Y : Type v} {α : Type w}
variable [AddGroup α] [ConditionallyCompleteLattice α]
variable [HasPairing X Y α]

/-- Definition 39.8.1: the pairing inner product of a supremum-oriented set `C` and an
infimum-oriented set `D`, when it exists, is the Chapter 38 function inner product of the
indicator of `C` with the concave indicator of `D`. -/
abbrev innerProduct (C : Set X) (D : Set Y) : WithBotTop α :=
  Function.innerProduct (δ[α](· | C)) (fun y ↦ -(δ[α](y | D)))

/-- Definition 39.8.1: the set inner product of `C` and `D` over `α` exists exactly when the two
textbook extrema agree:
`sup_{x ∈ C} inf_{y ∈ D} ⟪x, y⟫ = inf_{y ∈ D} sup_{x ∈ C} ⟪x, y⟫`. -/
def HasInnerProduct (C : Set X) (D : Set Y) : Prop :=
  C.innerProduct D = ⨅ y ∈ D, ⨆ x ∈ C, (⟪x, y⟫ₚ : WithBotTop α)

/-- The source-facing owner `C.innerProduct D` is the Chapter 36 maximin value
`sup_{x ∈ C} inf_{y ∈ D} ⟪x, y⟫`. -/
@[simp] theorem innerProduct_eq_iSup_iInf_pairing
    (C : Set X) (D : Set Y) :
    C.innerProduct D = ⨆ x ∈ C, ⨅ y ∈ D, (⟪x, y⟫ₚ : WithBotTop α) := by
  sorry

private theorem function_hasInnerProduct_iff
    (C : Set X) (D : Set Y) (hCD : C.Nonempty ∨ D.Nonempty) :
    Function.HasInnerProduct (δ[α](· | C)) (fun y ↦ -(δ[α](y | D))) ↔
      C.innerProduct D = ⨅ y ∈ D, ⨆ x ∈ C, (⟪x, y⟫ₚ : WithBotTop α) := by
  sorry

/-- The existence of the set inner product is exactly equality between the two textbook extrema
from Definition 39.8.1. -/
@[simp] theorem hasInnerProduct_iff
    (C : Set X) (D : Set Y) :
    HasInnerProduct (α := α) C D ↔
      C.innerProduct D = ⨅ y ∈ D, ⨆ x ∈ C, (⟪x, y⟫ₚ : WithBotTop α) := by
  rfl

/-- Bridge to the Chapter 38 owner layer: the set-level existence predicate from Definition 39.8.1
is equivalent to saying at least one set is nonempty and the corresponding indicator-function
pairing has a Chapter 38 inner product. -/
theorem hasInnerProduct_iff_nonempty_or_and_functionHasInnerProduct
    (C : Set X) (D : Set Y) :
    HasInnerProduct (α := α) C D ↔
      (C.Nonempty ∨ D.Nonempty) ∧
        Function.HasInnerProduct (δ[α](· | C)) (fun y ↦ -(δ[α](y | D))) := by
  constructor
  · intro hpair
    have hCD : C.Nonempty ∨ D.Nonempty := by
      by_contra hCD
      have hC_empty : C = ∅ := Set.not_nonempty_iff_eq_empty.mp (fun hC ↦ hCD (Or.inl hC))
      have hD_empty : D = ∅ := Set.not_nonempty_iff_eq_empty.mp (fun hD ↦ hCD (Or.inr hD))
      subst C D
      simp at hpair
    exact ⟨hCD, (function_hasInnerProduct_iff C D hCD).2 hpair⟩
  · rintro ⟨hCD, hfun⟩
    exact (function_hasInnerProduct_iff C D hCD).1 hfun

/-- When the set inner product exists, the source maximin value also equals the companion minimax
value `inf_{y ∈ D} sup_{x ∈ C} ⟪x, y⟫`. -/
theorem innerProduct_eq_iInf_iSup_pairing
    {C : Set X} {D : Set Y} (h : HasInnerProduct (α := α) C D) :
    C.innerProduct D = ⨅ y ∈ D, ⨆ x ∈ C, (⟪x, y⟫ₚ : WithBotTop α) := h

end

end Set

/-! ### Definition_39_8_2 (from Chap08) -/
noncomputable section

open scoped Rockafellar

universe u v w

section SetFunctionBridge

variable {X : Type u} {Y : Type v} {α : Type w}
variable [AddGroup α] [ConditionallyCompleteLattice α]
variable [HasPairing X Y α]

local instance : HasPairing Y X α := HasPairing.swap (X := X) (Y := Y) (L := α)

/-!
Source/core/bridge triage for this item.

- `source-facing`: the second definitional paragraph of §39.8 extends the Chapter 38 pairing to
  pair a supremum-oriented convex set `C` with a proper concave function `h`, and dually a proper
  convex function `h` with an infimum-oriented convex set `D`.
- `core/canonical`: the owner abstraction is already `Function.innerProduct` /
  `Function.HasInnerProduct` from Definition 38.5.2, together with the chapter set owners
  `indicatorFunction`, `supportFunction`, and the support/conjugacy bridges
  `convexConjugate_indicatorFunction_eq_supportFunction` and
  `concaveConjugate_eq_neg_convexConjugate_neg`.
- `bridge/view`: the set/function and function/set pairings here are thin bridges obtained by
  plugging the appropriate indicator representatives into the Chapter 38 owner, not new root
  owners.

Primary mathematical domain:
- Fenchel-style inner products involving convex sets, convex functions, and concave functions.

Domain-style sampling used here:
- `Function.innerProduct` and `Function.HasInnerProduct` from
  `Chap08.Definition_38_5_2`;
- `indicatorFunction` from `Chap01.Defintion_4_8_1`;
- `supportFunction` from `Chap01.Defintion_4_8_2`;
- `convexConjugate_indicatorFunction_eq_supportFunction` from
  `Chap03.Text_13_1_4`;
- `concaveConjugate_eq_neg_convexConjugate_neg` from `Chap06.Theorem_6_30_4`.

Primitive data vs derived API:
- primitive bridge inputs: a set `C` or `D` and a function `h`;
- primitive bridge owners introduced here: `Set.innerProduct`, `Set.HasInnerProduct`,
  `Function.innerProductSet`, and `Function.HasInnerProductSet`;
- derived API: the textbook `sup` / `inf` formulas obtained from the Chapter 38 owner and the
  existing support-function bridge theorems.

Layer target: `bridge/view`. The public declarations expose the source-facing pairings, but their
  bodies remain direct canonical reuse of `Function.innerProduct` rather than parallel wheel
  definitions.

Notation decision:
- no new notation is introduced. As in Definition 38.5.2, the textbook bracket notation would
  collide with the ambient vector inner-product notation, so the file keeps short owner names in
  `Set` and `Function`.
-/

namespace Set

/-- Definition 39.8.2, left-set clause: the inner product of a supremum-oriented convex set `C`
and a function `h` is the Chapter 38 owner `Function.innerProduct` specialized to the indicator of
`C`. -/
abbrev innerProduct (C : Set X) (h : Y → WithBotTop α) : WithBotTop α :=
  Function.innerProduct (δ[α](· | C)) h

/-- The pairing of a set `C` with a function `h` exists exactly when the corresponding Chapter 38
function-level inner product for the indicator of `C` exists. -/
def HasInnerProduct (C : Set X) (h : Y → WithBotTop α) : Prop :=
  Function.HasInnerProduct (δ[α](· | C)) h

/-- The set/function pairing `innerProduct C h` is the source supremum of
`x ↦ inf_y (⟪x, y⟫ - h y)` over `C`. -/
theorem innerProduct_eq_iSup_iInf_pairing_sub
    (C : Set X) (h : Y → WithBotTop α) :
    innerProduct C h =
      ⨆ x ∈ C, (⨅ y : Y, (((⟪x, y⟫ₚ : α) : WithBotTop α) - h y)) := by
  classical
  rw [innerProduct, Function.innerProduct_eq_iSup_concaveConjugate_sub]
  change (⨆ x : X, (⨅ y : Y, (((⟪x, y⟫ₚ : α) : WithBotTop α) - h y)) - δ[α](x | C)) =
    ⨆ x ∈ C, (⨅ y : Y, (((⟪x, y⟫ₚ : α) : WithBotTop α) - h y))
  calc
    (⨆ x : X, (⨅ y : Y, (((⟪x, y⟫ₚ : α) : WithBotTop α) - h y)) - δ[α](x | C))
        = ⨆ x : X, if x ∈ C then (⨅ y : Y, (((⟪x, y⟫ₚ : α) : WithBotTop α) - h y)) else ⊥ := by
            apply iSup_congr
            intro x
            by_cases hx : x ∈ C
            · rw [indicator_def, if_pos hx, if_pos hx]
              calc
                (⨅ y : Y, (((⟪x, y⟫ₚ : α) : WithBotTop α) - h y)) - (0 : WithBotTop α)
                    =
                      (⨅ y : Y, (((⟪x, y⟫ₚ : α) : WithBotTop α) - h y)) +
                        (-(0 : WithBotTop α)) := by
                        rfl
                _ = (⨅ y : Y, (((⟪x, y⟫ₚ : α) : WithBotTop α) - h y)) + 0 := by
                      rw [WithBotTop.neg_zero]
                _ = (⨅ y : Y, (((⟪x, y⟫ₚ : α) : WithBotTop α) - h y)) := by
                      rw [add_zero]
            · rw [indicator_def, if_neg hx, if_neg hx, WithBotTop.sub_top]
    _ = ⨆ x ∈ C, (⨅ y : Y, (((⟪x, y⟫ₚ : α) : WithBotTop α) - h y)) := by
          refine le_antisymm ?_ ?_
          · refine iSup_le fun x ↦ ?_
            by_cases hx : x ∈ C
            · exact le_iSup_of_le x <| le_iSup_of_le hx <| by rw [if_pos hx]
            · rw [if_neg hx]
              exact bot_le
          · refine iSup₂_le fun x hx ↦ ?_
            exact le_iSup_of_le x <| by rw [if_pos hx]

/-- The set/function pairing exists exactly when the Chapter 38 owner value equals the textbook
primal expression `inf_y (δᵛ(y | C) - h y)`. -/
theorem hasInnerProduct_iff
    (C : Set X) (h : Y → WithBotTop α) :
    HasInnerProduct C h ↔ innerProduct C h = ⨅ y : Y, δᵛ(y | C) - h y := by
  letI : HasPairingSwap X Y α := ⟨fun _ _ ↦ rfl⟩
  rw [HasInnerProduct, innerProduct, Function.hasInnerProduct_iff]
  have hsup : ∀ y : Y, (δ[α](· | C))⋆ y = δᵛ(y | C) := by
    intro y
    simpa using
      (convexConjugate_indicatorFunction_eq_supportFunction_pointwise
        (C := C) (xStar := y))
  constructor <;> intro hpair
  · calc
      Function.innerProduct (δ[α](· | C)) h = ⨅ y : Y, (δ[α](· | C))⋆ y - h y := hpair
      _ = ⨅ y : Y, δᵛ(y | C) - h y := by
            refine iInf_congr ?_
            intro y
            rw [hsup y]
  · calc
      Function.innerProduct (δ[α](· | C)) h = ⨅ y : Y, δᵛ(y | C) - h y := hpair
      _ = ⨅ y : Y, (δ[α](· | C))⋆ y - h y := by
            refine iInf_congr ?_
            intro y
            rw [hsup y]

/-- When the set/function pairing exists, it equals the textbook primal expression
`inf_y (δᵛ(y | C) - h y)`. -/
theorem innerProduct_eq_iInf_supportFunction_sub
    {C : Set X} {h : Y → WithBotTop α} (hpair : HasInnerProduct C h) :
    innerProduct C h = ⨅ y : Y, δᵛ(y | C) - h y :=
  (hasInnerProduct_iff C h).1 hpair

end Set

end SetFunctionBridge

section FunctionSetBridge

variable {X : Type u} {Y : Type v} {α : Type w}
variable [HasPairing X Y α]

local instance : HasPairing Y X α := HasPairing.swap (X := X) (Y := Y) (L := α)

namespace Function

/-- Definition 39.8.2, right-set clause: the inner product of a function `h` and an
infimum-oriented convex set `D` is the Chapter 38 owner specialized to the concave indicator view
`-indicatorFunction D`. -/
abbrev innerProductSet [AddGroup α] [ConditionallyCompleteLattice α]
    (h : X → WithBotTop α) (D : Set Y) : WithBotTop α :=
  innerProduct h (fun y ↦ -(δ[α](y | D)))

/-- The pairing of a function `h` with a set `D` exists exactly when the corresponding Chapter 38
function-level inner product with `-indicatorFunction D` exists. -/
def HasInnerProductSet [AddGroup α] [ConditionallyCompleteLattice α]
    (h : X → WithBotTop α) (D : Set Y) : Prop :=
  HasInnerProduct h (fun y ↦ -(δ[α](y | D)))

/-- The function/set pairing `innerProductSet h D` is the source supremum
`sup_x (-δᵛ(-x | D) - h x)`, i.e. `sup_x ((x, D) - h x)` in the textbook notation. -/
theorem innerProductSet_eq_iSup_neg_supportFunction_neg_sub
    [AddCommGroup α] [ConditionallyCompleteLinearOrder α]
    [Neg X] [IsOrderedAddMonoid α]
    [HasPairingNegRight Y X α]
    (h : X → WithBotTop α) (D : Set Y) :
    innerProductSet h D = ⨆ x : X, -δᵛ((-x : X) | D) - h x := by
  letI : HasPairingSwap X Y α := ⟨fun _ _ ↦ rfl⟩
  rw [innerProductSet, innerProduct_eq_iSup_concaveConjugate_sub]
  apply iSup_congr
  intro x
  have hswap :
      @concaveConjugate Y X (WithBotTop α) _ _ Function.instHasPairing
          (fun y ↦ -(δ[α](y | D))) x =
        concaveConjugate (fun y ↦ -(δ[α](y | D))) x := by
    change
      (⨅ y : Y, (((⟪x, y⟫ₚ : α) : WithBotTop α) - (-(δ[α](y | D))))) =
        (⨅ y : Y, (((⟪y, x⟫ₚ : α) : WithBotTop α) - (-(δ[α](y | D)))))
    apply iInf_congr
    intro y
    exact congrArg (fun t : WithBotTop α ↦ t - (-(δ[α](y | D))))
      (congrArg ((↑) : α → WithBotTop α)
        (HasPairingSwap.pairing_swap (X := X) (Y := Y) (𝕜 := α) (x := x) (y := y))
      )
  have hconj :
      concaveConjugate (fun y ↦ -(δ[α](y | D))) x =
        -δᵛ((-x : X) | D) := by
    have hnegfun : (-fun y ↦ -(δ[α](y | D))) = (δ[α](· | D)) := by
      funext y
      simp
    have hneg :
        concaveConjugate (fun y ↦ -(δ[α](y | D))) x =
          -((-fun y ↦ -(δ[α](y | D)))⋆ (-x : X)) := by
      simpa using
        concaveConjugate_eq_neg_convexConjugate_neg_apply
          (fun y ↦ -(δ[α](y | D))) x
    letI : HasPairingSwap Y X α := ⟨fun y x =>
      (HasPairingSwap.pairing_swap (x := x) (y := y)).symm⟩
    have hsup' :
        (δ[α](· | D))⋆ (-x : X) = δᵛ((-x : X) | D) := by
      simpa using
        congrFun
          (convexConjugate_indicatorFunction_eq_supportFunction
            (C := D))
          (-x : X)
    have hsup :
        (-fun y ↦ -(δ[α](y | D)))⋆ (-x : X) = δᵛ((-x : X) | D) := by
      calc
        (-fun y ↦ -(δ[α](y | D)))⋆ (-x : X) = (δ[α](· | D))⋆ (-x : X) := by
          simpa using
            congrArg (fun f : Y → WithBotTop α ↦ (f⋆ : X → WithBotTop α) (-x : X)) hnegfun
        _ = δᵛ((-x : X) | D) := hsup'
    rw [hneg, hsup]
  rw [hswap]
  simpa [sub_eq_add_neg] using congrArg (fun t : WithBotTop α ↦ t - h x) hconj

/-- If the conjugate `h⋆` never takes the value `⊥` outside `D`, then the function/set pairing
exists exactly when the Chapter 38 owner value equals the textbook dual expression
`inf_{y ∈ D} h⋆ y`. -/
theorem hasInnerProductSet_iff
    [AddGroup α] [ConditionallyCompleteLattice α]
    (h : X → WithBotTop α) (D : Set Y) (hconj_ne_bot : ∀ ⦃y⦄, y ∉ D → h⋆ y ≠ ⊥) :
    HasInnerProductSet h D ↔ innerProductSet h D = ⨅ y ∈ D, h⋆ y := by
  classical
  have hD :
      (⨅ y : Y, h⋆ y - (-(δ[α](y | D)))) =
        ⨅ y ∈ D, h⋆ y := by
    calc
      (⨅ y : Y, h⋆ y - (-(δ[α](y | D))))
          = ⨅ y : Y, if y ∈ D then h⋆ y else ⊤ := by
              apply iInf_congr
              intro y
              by_cases hy : y ∈ D
              · rw [indicator_of_mem D hy]
                simp [hy]
              · rw [indicator_of_notMem D hy]
                simpa [hy] using
                  (WithBotTop.sub_bot (x := h⋆ y) (hx := hconj_ne_bot hy))
      _ = ⨅ y ∈ D, h⋆ y := by
            rw [iInf_ite]
            simp
  rw [HasInnerProductSet, Function.hasInnerProduct_iff]
  constructor
  · intro hpair
    simpa [innerProductSet] using hpair.trans hD
  · intro hpair
    simpa [innerProductSet] using hpair.trans hD.symm

/-- If the conjugate `h⋆` never takes the value `⊥` outside `D`, then an existing function/set
pairing equals the textbook value `inf_{y ∈ D} h⋆ y`. -/
theorem innerProductSet_eq_iInf_convexConjugate
    [AddGroup α] [ConditionallyCompleteLattice α]
    {h : X → WithBotTop α} {D : Set Y} (hconj_ne_bot : ∀ ⦃y⦄, y ∉ D → h⋆ y ≠ ⊥)
    (hpair : HasInnerProductSet h D) :
    innerProductSet h D = ⨅ y ∈ D, h⋆ y :=
  (hasInnerProductSet_iff h D hconj_ne_bot).1 hpair

end Function

end FunctionSetBridge

/-! ### Proposition_39_8_3 (from Chap08) -/
noncomputable section

open scoped Pointwise Rockafellar

universe u v

namespace Set

/-!
Source/core/bridge triage for this item.

- `source-facing`: Proposition 39.8.3 records the homogeneity and additivity inequalities for the
  set inner product from Definition 39.8.1, together with the point specializations obtained when
  one side is a singleton.
- `core/canonical`: the owner abstraction is already the unconditional set pairing
  `Set.innerProduct`; `Set.HasInnerProduct` is only the companion maximin-minimax recognition
  predicate from Definition 39.8.1. The set operations are the canonical pointwise scalar action
  and Minkowski sum on sets, while the singleton clauses are already owned upstream by the support
  function `δᵛ(· | C)` and the sign-dual support-function bridge
  `x ↦ -δᵛ(-x | D)`.
- `bridge/view`: the two point clauses should therefore reuse those existing owner bridges rather
  than keep a parallel local singleton-pairing API.

Domain-style sampling used here:
- `Set.innerProduct` and `Set.HasInnerProduct` from `Definition_39_8_1`;
- `Function.innerProduct_neg_indicator_singleton_eq_convexPairing` from
  `Proposition_38_5_5`;
- `supportFunction_set_add_apply` from `Chap03.Text_13_1_3`;
- `neg_supportFunction_neg_eq_sInf_image_pairing_swap` from `Chap03.Text_13_0_2`.

Primitive data vs derived API:
- primitive owner data: `Set.innerProduct C D`;
- derived recognition data: `Set.HasInnerProduct C D`;
- derived API: the homogeneity/superadditivity inequalities, plus the singleton bridge views
  `C.innerProduct {y} = δᵛ[WithBotTop α](y | C)` and
  `({x} : Set E).innerProduct D = -δᵛ[WithBotTop α](-x | D)`,
  which make the point clauses immediate corollaries of the support-function owner theorems.
-/

section PositiveHomogeneity

variable {𝕜 : Type v} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E] [HasLinearPairing E E 𝕜]

-- Proof sketch: unfold `Set.innerProduct` to the maximin formula from Definition 39.8.1 and
-- pull the positive scalar `λ` through the ambient inner product on the left variable. The
-- positivity assumption keeps the infimum/supremum order unchanged, so the owner-level scaling
-- identity holds directly for the unconditional set inner product.
/-- Proposition 39.8.3 (1): positive dilations of the left set scale the set inner product by the
same scalar. -/
theorem innerProduct_smul_left_of_pos
    (C D : Set E) {lam : 𝕜} (hlam : 0 < lam) :
    ((lam • C).innerProduct D : WithBotTop 𝕜) =
      (lam : WithBotTop 𝕜) * (C.innerProduct D : WithBotTop 𝕜) := sorry

-- Proof sketch: rewrite the right-set pairing through the maximin/minimax description of
-- `Set.innerProduct`, pull the positive scalar through the inner product in the right variable,
-- and use the same positivity argument to preserve the infimum order. This is again an
-- owner-level identity for the unconditional set inner product.
/-- Proposition 39.8.3 (2): positive dilations of the right set scale the set inner product by the
same scalar. -/
theorem innerProduct_smul_right_of_pos
    (C D : Set E) {lam : 𝕜} (hlam : 0 < lam) :
    (C.innerProduct (lam • D) : WithBotTop 𝕜) =
      (lam : WithBotTop 𝕜) * (C.innerProduct D : WithBotTop 𝕜) := sorry

end PositiveHomogeneity

section AdditivityInequalities

variable {𝕜 : Type v} [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [IsOrderedAddMonoid 𝕜] [DenselyOrdered 𝕜]
variable {E : Type u} [AddCommMonoid E] [Module 𝕜 E] [HasLinearPairing E E 𝕜]

-- Proof sketch: expand the left-hand side as `sup_{x ∈ C + C'} inf_{y ∈ D} ⟪x, y⟫`, then use the
-- Minkowski-sum decomposition `x = x₁ + x₂` and additivity of the ambient inner product in the
-- left variable to compare with the separate suprema over `C` and `C'`. This superadditivity is
-- intrinsic to the unconditional owner `Set.innerProduct`.
/-- Proposition 39.8.3 (3): the set inner product is superadditive in the left set variable,
with no extra existence hypotheses. -/
theorem innerProduct_add_left_ge
    (C C' D : Set E) :
    ((C + C').innerProduct D : WithBotTop 𝕜) ≥
      (C.innerProduct D : WithBotTop 𝕜) + (C'.innerProduct D : WithBotTop 𝕜) := sorry

-- Proof sketch: rewrite the right-hand side through the minimax formula for `Set.innerProduct`
-- and compare `inf_{y ∈ D + D'} sup_{x ∈ C} ⟪x, y⟫` with the sum of the separate infima using
-- additivity of the ambient inner product in the right variable. This subadditivity also lives at
-- the unconditional owner level.
/-- Proposition 39.8.3 (4): the set inner product is subadditive in the right set variable,
with no extra existence hypotheses. -/
theorem innerProduct_add_right_le
    (C D D' : Set E) :
    (C.innerProduct (D + D') : WithBotTop 𝕜) ≤
      (C.innerProduct D : WithBotTop 𝕜) + (C.innerProduct D' : WithBotTop 𝕜) := sorry

end AdditivityInequalities

section SingletonRight

variable {α : Type v} [AddCommGroup α] [ConditionallyCompleteLinearOrder α]
variable {E : Type u} [HasPairing E E α] [HasPairingSwap E E α]

-- Proof sketch: Proposition 38.5.5 rewrites `C.innerProduct {y}` as the convex pairing of the
-- indicator of `C` with `y`, and Text 13.1.4 identifies that convex pairing with the support
-- value `δᵛ[WithBotTop ℝ](y | C)`.
/-- Owner bridge: pairing a set with the singleton right set `{y}` is exactly the support value of
`C` at `y`. -/
theorem innerProduct_singleton_right_eq_supportFunction
    (C : Set E) (y : E) :
    C.innerProduct ({y} : Set E) = δᵛ[WithBotTop α](y | C) := by
  rw [innerProduct]
  rw [Function.innerProduct_neg_indicator_singleton_eq_convexPairing]
  simpa using
    convexConjugate_indicatorFunction_eq_supportFunction_pointwise C y

end SingletonRight

section SingletonRightAdd

variable {𝕜 : Type v} [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [IsOrderedAddMonoid 𝕜] [DenselyOrdered 𝕜]
variable {E : Type u} [AddCommMonoid E] [Module 𝕜 E]
variable [HasLinearPairing E E 𝕜] [HasPairingSwap E E 𝕜]

-- Proof sketch: rewrite each singleton-right pairing by
-- `innerProduct_singleton_right_eq_supportFunction`, then apply the owner theorem
-- `supportFunction_set_add_apply`.
/-- Proposition 39.8.3 (5): pairing a Minkowski sum on the left with a point `y`, viewed as the
singleton right set `{y}`, is additive in the left-set argument. -/
theorem innerProduct_add_singleton_right
    (C C' : Set E) (y : E) :
    ((C + C').innerProduct ({y} : Set E) : WithBotTop 𝕜) =
      (C.innerProduct ({y} : Set E) : WithBotTop 𝕜) +
        (C'.innerProduct ({y} : Set E) : WithBotTop 𝕜) := by
  rw [innerProduct_singleton_right_eq_supportFunction,
    innerProduct_singleton_right_eq_supportFunction,
    innerProduct_singleton_right_eq_supportFunction]
  simpa using supportFunction_set_add_apply C C' y

end SingletonRightAdd

section SingletonLeft

variable {𝕜 : Type v} [AddCommGroup 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [IsOrderedAddMonoid 𝕜]
variable {E : Type u} [AddCommGroup E]
variable [HasPairing E E 𝕜] [HasPairingSwap E E 𝕜] [HasPairingNegRight E E 𝕜]

local instance : Neg (WithBotTop 𝕜) := WithBotTop.instNeg

-- Proof sketch: collapse the outer supremum in `innerProduct_eq_iSup_iInf_pairing` against the
-- singleton `{x}`. The resulting infimum of the pairing values over `D` is exactly the sign-dual
-- support-function formula from `neg_supportFunction_neg_eq_sInf_image_pairing_swap`.
/-- Owner bridge: pairing the singleton left set `{x}` with `D` is the sign-dual support value
`-δᵛ[WithBotTop 𝕜](-x | D)`. -/
theorem innerProduct_singleton_left_eq_neg_supportFunction_neg
    (x : E) (D : Set E) :
    ({x} : Set E).innerProduct D = -δᵛ[WithBotTop 𝕜](-x | D) := by
  rw [innerProduct_eq_iSup_iInf_pairing]
  calc
    (⨆ z ∈ ({x} : Set E), ⨅ y ∈ D, (⟪z, y⟫ₚ : WithBotTop 𝕜))
        = (⨅ y ∈ D, (⟪x, y⟫ₚ : WithBotTop 𝕜)) := by
            simp
    _ = (⨅ y ∈ D, (⟪y, x⟫ₚ : WithBotTop 𝕜)) := by
          refine iInf_congr fun y ↦ ?_
          refine iInf_congr fun _ ↦ ?_
          exact
            congrArg ((↑) : 𝕜 → WithBotTop 𝕜) (HasPairingSwap.pairing_swap x y)
    _ = sInf ((fun y ↦ (⟪y, x⟫ₚ : WithBotTop 𝕜)) '' D) := by
          rw [sInf_image]
    _ = -δᵛ[WithBotTop 𝕜](-x | D) := by
          simpa using
            (neg_supportFunction_neg_eq_sInf_image_pairing_swap
              (C := D) (xStar := x)).symm

end SingletonLeft

section SingletonLeftAdd

variable {𝕜 : Type v} [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [IsOrderedAddMonoid 𝕜] [DenselyOrdered 𝕜]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E]
variable [HasLinearPairing E E 𝕜] [HasPairingSwap E E 𝕜]

local instance : Neg (WithBotTop 𝕜) := WithBotTop.instNeg

-- Proof sketch: rewrite each singleton-left pairing by
-- `innerProduct_singleton_left_eq_neg_supportFunction_neg`, then apply `Neg.neg` to the owner
-- theorem `supportFunction_set_add_apply`.
/-- Proposition 39.8.3 (6): pairing a point `x`, viewed as the singleton left set `{x}`, with a
Minkowski sum on the right is additive in the right-set argument. -/
theorem innerProduct_singleton_left_add
    (x : E) (D D' : Set E) :
    (({x} : Set E).innerProduct (D + D') : WithBotTop 𝕜) =
      (({x} : Set E).innerProduct D : WithBotTop 𝕜) +
        (({x} : Set E).innerProduct D' : WithBotTop 𝕜) := sorry

end SingletonLeftAdd

end Set

/-! ### Definition_39_8_4 (from Chap08) -/
open scoped Pointwise

universe u v

namespace SetRel

/-!
Source/core/bridge triage:

- `source-facing`: Definition 39.8.4 introduces eigensets by the image equation `AC = λ C`.
- `core/canonical`: the process/image owner already present in the chapter is `SetRel.image`, and
  the textbook dilate `λ C` is the canonical pointwise scalar action on sets.
- `bridge/view`: the textbook notation `AC` is rendered directly as `A.image C`, so no extra
  action notation or wrapper owner is introduced here.

Primary mathematical domain:
- convex processes acting on sets through relation image.

Domain-style sampling used here:
- `SetRel.image` from `Mathlib.Data.Rel` for the image of a set under a relation;
- the canonical pointwise set scalar action `lam • C`.

Primitive data vs derived API:
- primitive owner data: a self-relation `A : SetRel U U`, a scalar `lam : R`, and a set `C`;
- primitive source-facing owner introduced here: `A.IsEigenset lam C`;
- derived API: the direct rewriting lemma exposing the defining image equation.

Layer target: `source-facing`, stated directly on the canonical relation-image owner.
-/

section

variable {R : Type u} {U : Type v} [SMul R U]

/-- Definition 39.8.4: a set `C` is an eigenset of a self-relation `A` with eigenvalue `lam`
when its image under `A`, written in the text as `AC`, is exactly the dilate `lam • C`. -/
def IsEigenset (A : SetRel U U) (lam : R) (C : Set U) : Prop :=
  A.image C = lam • C

-- Proof sketch: unfold `SetRel.IsEigenset`; this is the definitional equation of the owner,
-- restated in a rewrite-friendly `..._def` form.
/-- An eigenset is exactly a set whose image under `A` equals its `lam`-dilate. -/
@[simp] theorem isEigenset_def
    (A : SetRel U U) (lam : R) (C : Set U) :
    A.IsEigenset lam C ↔ A.image C = lam • C := sorry

-- Proof sketch: this is the same defining equivalence as `isEigenset_def`, recorded under the
-- standard `..._iff` companion name for rewriting and search.
/-- An eigenset is exactly a set whose image under `A` equals its `lam`-dilate. -/
@[simp] theorem isEigenset_iff
    (A : SetRel U U) (lam : R) (C : Set U) :
    A.IsEigenset lam C ↔ A.image C = lam • C := sorry

-- Proof sketch: unfold `SetRel.IsEigenset`; an eigenset hypothesis is exactly the defining image
-- equation `A.image C = lam • C`.
/-- An eigenset hypothesis directly yields the defining image equation `A.image C = lam • C`. -/
@[simp] theorem isEigenset_image_eq
    {A : SetRel U U} {lam : R} {C : Set U} (hC : A.IsEigenset lam C) :
    A.image C = lam • C := sorry

namespace IsEigenset

-- Proof sketch: unfold `SetRel.IsEigenset`; the hypothesis already is the defining image
-- equation `A.image C = lam • C`.
/-- An eigenset hypothesis directly yields the defining image equation. -/
theorem image_eq {A : SetRel U U} {lam : R} {C : Set U} (hC : A.IsEigenset lam C) :
    A.image C = lam • C := sorry

end IsEigenset

end

end SetRel

/-! ### Theorem_39_8 (from Chap08) -/
noncomputable section

open scoped Rockafellar SetRel

universe u v w

namespace SetRel

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 39.8 is the process-level composition theorem for convex processes,
  together with its closed-case companion and the adjoint-side closure formula.
- `core/canonical`: the chapter already owns convex processes on `A : SetRel U X` via
  `A.IsConvexProcess 𝕜`, relation composition via the canonical `SetRel.comp` notation `A ○ B`,
  graph closure via `cl(·)` / `A.IsClosed`, and process adjoints via `A∗[...]`.
- `bridge/view`: this item is a direct process-side specialization of the Chapter 38 composition
  theorems for bifunctions, using the Chapter 39 indicator-fiber and process-adjoint bridges. No
  new packaged
  “composition data” or “adjoint composition data” owner should appear here.

Primary mathematical domain:
- composition of convex processes in the finite-dimensional real continuous-pairing setting used
  by Chapter 38.

Domain-style sampling used here:
- `SetRel.comp` and `SetRel.IsConvexProcess.comp` from `Chap08.Proposition_39_0_10`;
- `SetRel.closure` / `cl(·)` and `SetRel.IsClosed` from `Chap08.Definition_39_0_5`;
- `SetRel.adjoint` / `A∗[...]` from `Chap08.Definition_39_0_14`;
- `Bifunction.comp` together with the Chapter 38 composition theorems
  `Bifunction.adjointFunction_comp_eq_comp_adjointFunction_of_common_riDom` and
  `Bifunction.isClosedConvex_comp_of_common_riDom_adjoint_inverse` from
  `Chap08.Theorem_38_5` and `Chap08.Proposition_38_5_1`;
- `indicatorFibers`, `dom_indicatorFibers_eq_dom`, and
  `lowerSemicontinuous_uncurry_indicatorFibers_iff_isClosed` from
  `Chap08.Proposition_39_0_13`.

Primitive data vs derived API:
- primitive source data: convex processes `A : SetRel U X` and `B : SetRel X Y`;
- primitive reused owners: `A ○ B`, `(A∗[...]).dom`, `B.dom`, `(B∗[...]).cod`, `cl(·)`, and
  `IsClosed`;
- derived API here: the source adjoint-of-composition identity, the closedness theorem for
  `A ○ B` under the dual qualification, and the adjoint-side closure identity.

Layer target: `source-facing`, stated directly on the canonical `SetRel` owners.
-/

section

variable {U : Type u}
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [_root_.FiniteDimensional ℝ U]
variable {X : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [_root_.FiniteDimensional ℝ X]
variable {Y : Type w}
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y] [_root_.FiniteDimensional ℝ Y]
variable [HasLinearPairing U U ℝ] [HasContinuousPairing U U ℝ]
variable [HasLinearPairing X X ℝ] [HasContinuousPairing X X ℝ]
variable [HasLinearPairing Y Y ℝ] [HasContinuousPairing Y Y ℝ]

local notation "ri(" C ")" => intrinsicInterior ℝ C

local notation:100 A "∗ᵣ" => (A∗[X, U; ℝ])
local notation:100 A "∗ₛ" => (A∗[Y, X; ℝ])
local notation:100 A "∗ₜ" => (A∗[Y, U; ℝ])

-- Proof sketch: specialize the Chapter 38 product-adjoint theorem to the indicator bifunctions of
-- `A` and `B`, using the Chapter 39 bridge that identifies relation composition with the product
-- of the corresponding indicator bifunctions. The Chapter 38 qualification
-- `ri(dom (adjoint (indicatorFibers ℝ A))) ∩ ri(dom (indicatorFibers ℝ B)) ≠ ∅`
-- reads process-side as `ri((A∗ᵣ).dom) ∩ ri(B.dom) ≠ ∅`.
/-- Theorem 39.8 (1): if convex processes `A` and `B` have the same orientation and
`ri (dom A*)` meets `ri (dom B)`, then the adjoint of the product `(BA)` is the product of the
adjoints, rendered on the canonical `SetRel` owners as
`(A ○ B)∗ₜ = B∗ₛ ○ A∗ᵣ`. -/
theorem adjoint_comp_eq_comp_adjoint_of_common_ri_dom_adjoint_dom
    {aRel : SetRel U X} {bRel : SetRel X Y}
    (hA : aRel.IsConvexProcess ℝ) (hB : bRel.IsConvexProcess ℝ)
    (hri : (ri((aRel∗ᵣ).dom) ∩ ri(bRel.dom)).Nonempty) :
    (aRel ○ bRel)∗ₜ = bRel∗ₛ ○ aRel∗ᵣ := sorry

-- Proof sketch: specialize the closed-case Chapter 38 composition theorem to the indicator
-- bifunctions of `A` and `B`. The dual regularity hypothesis in Corollary 38.5.1 is
-- `ri(dom (adjoint (indicatorFibers ℝ A))) ∩
--   ri(dom ((adjoint (indicatorFibers ℝ B)) _*)) ≠ ∅`.
-- On the process surface this is `ri((A∗ᵣ).dom) ∩ ri(((B∗ₛ)⁻¹).dom)`, equivalently
-- `ri((A∗ᵣ).dom) ∩ ri((B∗ₛ).cod)` by `SetRel.dom_inv`.
/-- Theorem 39.8 (2): if `A` and `B` are closed convex processes and
`ri (range B*)` meets `ri (dom A*)`, then the product process `(BA)` is closed. -/
theorem isClosed_comp_of_isClosed_of_common_ri_cod_adjoint_dom_adjoint
    {aRel : SetRel U X} {bRel : SetRel X Y}
    (hA : aRel.IsConvexProcess ℝ) (hB : bRel.IsConvexProcess ℝ)
    (hA_closed : aRel.IsClosed) (hB_closed : bRel.IsClosed)
    (hri : (ri((bRel∗ₛ).cod) ∩ ri((aRel∗ᵣ).dom)).Nonempty) :
    (aRel ○ bRel).IsClosed := sorry

-- Proof sketch: under the same closedness and dual relative-interior hypothesis, apply the
-- Chapter 38 adjoint-side closure formula to the indicator bifunctions of `A` and `B`, then
-- translate back through the Chapter 39 adjoint-process and graph-closure owners.
/-- Theorem 39.8 (3): if `A` and `B` are closed convex processes and
`ri (range B*)` meets `ri (dom A*)`, then the adjoint of the product `(BA)` is the graph closure
of the product of the adjoints. -/
theorem adjoint_comp_eq_closure_comp_adjoint_of_isClosed_of_common_ri_cod_adjoint_dom_adjoint
    {aRel : SetRel U X} {bRel : SetRel X Y}
    (hA : aRel.IsConvexProcess ℝ) (hB : bRel.IsConvexProcess ℝ)
    (hA_closed : aRel.IsClosed) (hB_closed : bRel.IsClosed)
    (hri : (ri((bRel∗ₛ).cod) ∩ ri((aRel∗ᵣ).dom)).Nonempty) :
    (aRel ○ bRel)∗ₜ = cl(bRel∗ₛ ○ aRel∗ᵣ) := sorry

end

end SetRel
