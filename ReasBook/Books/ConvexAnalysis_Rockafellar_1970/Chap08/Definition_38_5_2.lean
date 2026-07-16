import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_4
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition_36_0_1

noncomputable section

open scoped Rockafellar

universe u v w

namespace Function

section Core

variable {X : Type u} {Y : Type v} {L : Type w}
variable [SupSet L] [InfSet L] [Sub L]
variable [HasPairing X Y L]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Definition 38.5.2 introduces the inner product of a convex function `f` and a
  concave function `g` as the common value of the dual expression `sup_x (g* x - f x)` and the
  primal expression `inf_y (f* y - g y)` when those two values agree.
- `core/canonical`: the owner declarations already present in the project are the Chapter 12
  convex conjugate `f⋆` and the Chapter 6 concave conjugate `concaveConjugate g`, both already
  phrased on the primitive pairing layer.
- `bridge/view`: the equivalent saddle-value reading belongs to the Chapter 7 minimax owner layer,
  so this file keeps the source-facing pairing itself but exposes the bridge to
  `Bifunction.maximinValueOn`, `Bifunction.minimaxValueOn`, and `Bifunction.HasSaddleValueOn`
  instead of introducing a second local saddle-value wrapper.

Primary mathematical domain:
- Fenchel-duality pairings between convex-side and concave-side functions on a primitive dual
  pairing.

Domain-style sampling used here:
- `convexConjugate` and the notation `f⋆` from `Chap03.Defn_12_2`;
- `concaveConjugate` and `concaveConjugate_eq_iInf_pairing_sub` from
  `Chap06.Definition_6_30_4`;
- `Bifunction.maximinValueOn`, `Bifunction.minimaxValueOn`, and `Bifunction.HasSaddleValueOn`
  from `Chap07.Definition_36_0_1`, identifying the existing core owner for the equivalent
  saddle-value formulation.

Primitive data vs derived API:
- primitive data: two functions `f : X → L` and `g : Y → L`;
- primitive source-facing owner introduced here: `Function.innerProduct f g`;
- derived API: the defining dual-objective formula and the existence predicate
  `Function.HasInnerProduct f g`; in the chapter-facing `WithBotTop α` specialization, this file
  additionally provides bridge theorems identifying these source-side formulas with the Chapter 36
  saddle-value owners on the canonical Fenchel pairing kernel under the natural bridge-side
  hypotheses excluding the bad translation value `⊥`. The reversed pairing needed to read `g*` on
  `X` is only the canonical swapped view of the given pairing, so it is kept internal rather than
  exposed as a second public owner input.

Layer target: `source-facing`, implemented directly through the existing conjugate owners instead
of through a parallel package of maximin/minimax data.

Notation evaluation:
- the textbook notation `⟨f, g⟩` conflicts with the ambient vector inner-product notation
  `⟪x, y⟫`, already used pervasively across the project, so this file keeps the short raw owner
  names `Function.innerProduct` and `Function.HasInnerProduct`.
-/

local instance : HasPairing Y X L where
  pairing y x := ⟪x, y⟫ₚ

/-- Definition 38.5.2: the inner product of `f` and `g`, when it exists, is their common duality
value. The canonical owner is the dual-objective side `sup_x (g* x - f x)`, with existence
recorded separately by `HasInnerProduct`. -/
abbrev innerProduct (f : X → L) (g : Y → L) : L :=
  ⨆ x : X, concaveConjugate g x - f x

/-- Definition 38.5.2: the inner product of `f` and `g` exists exactly when the dual-objective
value `innerProduct f g` agrees with the companion primal-objective value
`inf_y (f* y - g y)`. -/
def HasInnerProduct (f : X → L) (g : Y → L) : Prop :=
  innerProduct f g = ⨅ y : Y, f⋆ y - g y

/-- The source-facing owner `innerProduct f g` is the dual objective `sup_x (g* x - f x)`. -/
@[simp] theorem innerProduct_eq_iSup_concaveConjugate_sub
    (f : X → L) (g : Y → L) :
    innerProduct f g = ⨆ x : X, concaveConjugate g x - f x :=
  rfl

/-- The existence of the inner product is exactly equality between the dual and primal objective
formulas from Definition 38.5.2. -/
@[simp] theorem hasInnerProduct_iff
    (f : X → L) (g : Y → L) :
    HasInnerProduct f g ↔ innerProduct f g = ⨅ y : Y, f⋆ y - g y :=
  Iff.rfl

/-- When the inner product exists, the defining owner value also equals the primal objective
`inf_y (f* y - g y)`. -/
theorem innerProduct_eq_iInf_convexConjugate_sub
    {f : X → L} {g : Y → L} (h : HasInnerProduct f g) :
    innerProduct f g = ⨅ y : Y, f⋆ y - g y :=
  h

end Core

section WithBotTopBridge

variable {X : Type u} {Y : Type v} {α : Type w}
variable [AddCommGroup α] [ConditionallyCompleteLinearOrder α] [IsOrderedAddMonoid α]
variable [HasPairing X Y α]

local instance : HasPairing Y X α where
  pairing y x := ⟪x, y⟫ₚ

private def subRightOrderIso (r : α) : WithBotTop α ≃o WithBotTop α where
  toFun := fun t ↦ t - r
  invFun := fun t ↦ t + r
  left_inv := fun _ ↦ WithBotTop.sub_add_cancel
  right_inv := fun _ ↦ WithBotTop.add_sub_cancel_right
  map_rel_iff' := fun {s t} ↦ by
    simpa [sub_eq_add_neg] using
      (WithBotTop.addLECancellable_coe (-r)).add_le_add_iff_right

/-- The source dual objective for `innerProduct f g` is the Chapter 36 maximin value on
`univ × univ` of the Fenchel pairing kernel `(x, y) ↦ ⟪x, y⟫ₚ - f x - g y`, provided `f` never
takes the bad translation value `⊥` and the minimizing side is nonempty. -/
theorem innerProduct_eq_maximinValueOn_univ_univ
    [Nonempty Y]
    (f : X → WithBotTop α) (g : Y → WithBotTop α) (hf : ∀ x, f x ≠ ⊥) :
    innerProduct f g =
      Bifunction.maximinValueOn (Set.univ : Set X) Set.univ
        (fun x y ↦ ⟪x, y⟫ₚ - f x - g y) := by
  rw [Bifunction.maximinValueOn, innerProduct_eq_iSup_concaveConjugate_sub]
  simp only [concaveConjugate_eq_iInf_pairing_sub, WithBotTop.sub_eq_add_neg, Set.mem_univ,
    iInf_pos, iSup_pos]
  apply iSup_congr
  intro x
  rcases eq_or_ne (f x) ⊤ with hfx_top | hfx_top
  · rw [hfx_top]
    simp only [WithBotTop.neg_top, WithBotTop.add_bot, WithBotTop.bot_add, iInf_const]
  lift f x to α using ⟨hfx_top, hf x⟩ with fx hfx
  calc
    (⨅ y : Y, (⟪x, y⟫ₚ - g y)) - fx
        = subRightOrderIso fx (⨅ y : Y, (⟪x, y⟫ₚ - g y)) := by
            rfl
    _ = ⨅ y : Y, subRightOrderIso fx (⟪x, y⟫ₚ - g y) := by
          exact (subRightOrderIso fx).map_iInf _
    _ = ⨅ y : Y, ((⟪x, y⟫ₚ - g y) - fx) := by
          rfl
    _ = ⨅ y : Y, ⟪x, y⟫ₚ - fx - g y := by
          refine iInf_congr fun y ↦ ?_
          simp only [WithBotTop.sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- The companion primal objective for `HasInnerProduct f g` is the Chapter 36 minimax value on
`univ × univ` of the same Fenchel pairing kernel, provided `g` never takes the bad translation
value `⊥` and the maximizing side is nonempty. -/
theorem iInf_convexConjugate_sub_eq_minimaxValueOn_univ_univ
    [Nonempty X]
    (f : X → WithBotTop α) (g : Y → WithBotTop α) (hg : ∀ y, g y ≠ ⊥) :
    (⨅ y : Y, f⋆ y - g y) =
      Bifunction.minimaxValueOn (Set.univ : Set X) Set.univ
        (fun x y ↦ ⟪x, y⟫ₚ - f x - g y) := by
  rw [Bifunction.minimaxValueOn]
  simp only [convexConjugate_eq_iSup_pairing_sub, WithBotTop.sub_eq_add_neg, Set.mem_univ,
    iSup_pos, iInf_pos]
  apply iInf_congr
  intro y
  rcases eq_or_ne (g y) ⊤ with hgy_top | hgy_top
  · rw [hgy_top]
    simp only [WithBotTop.neg_top, WithBotTop.add_bot, iSup_const]
  lift g y to α using ⟨hgy_top, hg y⟩ with gy hgy
  calc
    (⨆ x : X, (⟪x, y⟫ₚ - f x)) - gy
        = subRightOrderIso gy (⨆ x : X, (⟪x, y⟫ₚ - f x)) := by
            rfl
    _ = ⨆ x : X, subRightOrderIso gy (⟪x, y⟫ₚ - f x) := by
          exact (subRightOrderIso gy).map_iSup _
    _ = ⨆ x : X, ((⟪x, y⟫ₚ - f x) - gy) := by
          rfl
    _ = ⨆ x : X, ⟪x, y⟫ₚ - f x - gy := by
          refine iSup_congr fun x ↦ ?_
          simp only [WithBotTop.sub_eq_add_neg, add_assoc]

/-- The inner product of `f` and `g` exists exactly when the canonical Fenchel pairing kernel has
a saddle value on `univ × univ`, provided neither outer translation term ever equals `⊥` and both
sides are nonempty. This is the Chapter 36 bridge for Definition 38.5.2 on the chapter-facing
codomain. -/
theorem hasInnerProduct_iff_hasSaddleValueOn_univ_univ
    [Nonempty X] [Nonempty Y]
    (f : X → WithBotTop α) (g : Y → WithBotTop α)
    (hf : ∀ x, f x ≠ ⊥) (hg : ∀ y, g y ≠ ⊥) :
    HasInnerProduct f g ↔
      Bifunction.HasSaddleValueOn (Set.univ : Set X) Set.univ
        (fun x y ↦ ⟪x, y⟫ₚ - f x - g y) := by
  rw [HasInnerProduct, Bifunction.HasSaddleValueOn,
    innerProduct_eq_maximinValueOn_univ_univ f g hf,
    ← iInf_convexConjugate_sub_eq_minimaxValueOn_univ_univ f g hg]

end WithBotTopBridge

end Function
