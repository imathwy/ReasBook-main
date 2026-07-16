import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_13_1_4
import ConvexAnalysis_Rockafellar_1970.Chap06.Theorem_6_30_4
import ConvexAnalysis_Rockafellar_1970.Chap08.Definition_38_5_2

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
