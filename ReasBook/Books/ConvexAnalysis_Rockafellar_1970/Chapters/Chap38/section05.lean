import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_38_5_1 (from Chap08) -/
open Bifunction

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 38.5.1 is the closed-case companion to Theorem 38.5 for the product
  `GF`, asserting closedness of `GF`, pointwise attainment of the defining infimum, and the
  adjoint-side closure identity `(GF)^* = cl(F^* G^*)`.
- `core/canonical`: the owner declarations already present in the chapter are the product owner
  `Bifunction.comp`, `Bifunction.adjoint`, `Bifunction.inverse`, `Bifunction.dom`,
  `Bifunction.IsProper`, `Bifunction.IsClosedConvex`, `Bifunction.closure`, and the canonical
  Corollary 38.5.1 theorem family already recorded in `Items/Chap08/Proposition_38_5_1.lean`.
- `bridge/view`: this file contributes no new mathematics beyond those existing source-facing
  owner theorems, so it should reuse them directly instead of maintaining a second wrapper API.

Primary mathematical domain:
- composition of closed proper convex bifunctions and the adjoint-side closure formula.

Domain-style sampling used here:
- `Bifunction.comp` from `Theorem_38_5`;
- `Bifunction.adjoint` from the Chapter 6 duality owner layer;
- `Bifunction.closure` from `Definition_6_29_24`;
- the canonical Corollary 38.5.1 theorem family in `Proposition_38_5_1`.

Primitive data vs derived API:
- primitive source data: closed proper convex bifunctions `F : U → X → EReal` and
  `G : X → Y → EReal`;
- primitive owner layer: the existing chapter owners `comp G F`, `adjoint`, `inverse`,
  `dom`, and `closure`;
- derived API: closedness of `comp G F`, pointwise attainment of its defining infimum, and the
  adjoint-side closure identity.

Layer target: `bridge/view`. This file reuses the existing source-facing owner theorems directly
instead of maintaining renamed local copies.
-/

/- Corollary 38.5.1 is already recorded upstream on the canonical `Bifunction` owners. -/
recall isClosedConvex_comp_of_common_riDom_adjoint_inverse

recall exists_eq_comp_of_common_riDom_adjoint_inverse
recall adjointFunction_comp_eq_closure_comp_adjointFunction_of_common_riDom_adjoint_inverse

/-! ### Proposition_38_5_1 (from Chap08) -/
noncomputable section

open scoped Rockafellar

namespace Bifunction

section

universe u v w

variable {U : Type u} {X : Type v} {Y : Type w}
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
variable [HasLinearPairing U U ℝ] [HasContinuousPairing U U ℝ]
variable [HasLinearPairing X X ℝ] [HasContinuousPairing X X ℝ]
variable [HasLinearPairing Y Y ℝ] [HasContinuousPairing Y Y ℝ]

/-!
Source/core/bridge triage for this item.

- `source-facing`: despite the legacy file name, this item is Rockafellar's Corollary 38.5.1 on
  the product `GF` of closed proper convex bifunctions, asserting closedness of `GF`, pointwise
  attainment of the defining infimum, and the adjoint-side closure identity.
- `core/canonical`: the owner declarations in the chapter are the product owner `Bifunction.comp`
  used as `comp G F`,
  `Bifunction.adjoint`, `Bifunction.inverse`,
  `Bifunction.dom`, `Bifunction.IsProper`, `Bifunction.IsClosedConvex`, and the bifunction-closure
  owner `Bifunction.closure`.
- `bridge/view`: the source right-hand side `cl(F^* G^*)` is rendered by the closure owner
  applied to `comp (adjoint F) (adjoint G)`.

Primary mathematical domain:
- composition of convex bifunctions and adjoint-side closure formulas.

Domain-style sampling used here:
- `Bifunction.comp` and `Bifunction.comp_apply_eq_iInf` from `Theorem_38_5`;
- `Bifunction.adjoint` from `Chap06.Lemma_31_0_8`;
- `Bifunction.closure` from `Chap06.Definition_6_29_24`;
- `Bifunction.inverse` from `Chap07.Definition_36_4_1`;
- `Bifunction.IsClosedConvex`, `Bifunction.dom`, and `Bifunction.IsProper` from
  `Chap07.Defn_34_2` and `Chap08.Theorem_38_1`.

Primitive data vs derived API:
- primitive source data: closed proper convex bifunctions `F : U → X → EReal` and
  `G : X → Y → EReal`;
- primitive owner layer: the source-facing product `comp G F`;
- derived API: closedness of `comp G F`, pointwise attainment of its defining infimum, and the
  adjoint-side closure identity.

Layer target: `source-facing`, stated directly on the Chapter 38 product owner and existing
adjoint/inverse/domain owners rather than through a parallel “closed composition” package.
-/

variable (F : U → X → EReal) (G : X → Y → EReal)

local notation "ri(" C ")" => intrinsicInterior ℝ C
local notation "F⋆" => (adjoint X U F : X → U → EReal)
local notation "G⋆" => (adjoint Y X G : Y → X → EReal)
local notation "(GF)⋆" => (adjoint Y U (comp G F) : Y → U → EReal)

-- Proof sketch: this is the closed-case companion to Theorem 38.5. The common-relative-interior
-- hypothesis is already expressed through the chapter owners `dom`, `adjoint`, and
-- `inverse`, so the closedness conclusion should stay on the product owner `comp G F`.
/-- Corollary 38.5.1, closedness clause: if `F` and `G` are closed proper convex bifunctions and
`ri (dom F^*)` meets `ri (dom (G^*)_*)`, rendered here by `ri(dom (adjoint F))` and
`ri(dom (inverse (adjoint G)))`, then the product `comp G F` is closed convex. -/
theorem isClosedConvex_comp_of_common_riDom_adjoint_inverse
    (hF : IsClosedConvex F) (hF_proper : IsProper F)
    (hG : IsClosedConvex G) (hG_proper : IsProper G)
    (hri :
      (ri(dom (F⋆)) ∩ ri(dom ((G⋆) _*))).Nonempty)
    : IsClosedConvex (comp G F) := by
  sorry

-- Proof sketch: the same regularity hypothesis yields attainment of the source infimum
-- `inf_x (F u x + G x y)` for every `(u, y)`. The theorem keeps that source-facing equality
-- surface instead of packaging attainment as auxiliary data.
/-- Corollary 38.5.1, attainment clause: under the same hypotheses, the infimum in the definition
of `comp G F` is attained at every pair `(u, y)`. -/
theorem exists_eq_comp_of_common_riDom_adjoint_inverse
    (hF : IsClosedConvex F) (hF_proper : IsProper F)
    (hG : IsClosedConvex G) (hG_proper : IsProper G)
    (hri :
      (ri(dom (F⋆)) ∩ ri(dom ((G⋆) _*))).Nonempty)
    (u : U) (y : Y) :
    ∃ x : X, comp G F u y = F u x + G x y := by
  sorry

-- Proof sketch: the adjoint of the product is identified with the closure of the product of the
-- adjoints. The right-hand side is stated directly with the source-facing closure owner.
/-- Corollary 38.5.1, adjoint clause:
`(GF)^* = cl(F^* G^*)`, rendered by `adjoint`, `comp`, and `closure`. -/
theorem
    adjointFunction_comp_eq_closure_comp_adjointFunction_of_common_riDom_adjoint_inverse
    (hF : IsClosedConvex F) (hF_proper : IsProper F)
    (hG : IsClosedConvex G) (hG_proper : IsProper G)
    (hri :
      (ri(dom (F⋆)) ∩ ri(dom ((G⋆) _*))).Nonempty)
    :
    (GF)⋆ = cl (comp F⋆ G⋆) := by
  sorry

end

end Bifunction

/-! ### Definition_38_5_2 (from Chap08) -/
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

/-! ### Proposition_38_5_3 (from Chap08) -/
open Bornology

noncomputable section

open scoped RealInnerProductSpace Rockafellar

universe u

namespace Function

section

variable {E : Type u}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {f g : E → EReal}

local notation "IsClosedProperConvex[ℝ]" => @Function.IsClosedProperConvex ℝ
local notation "IsClosedProperConcave[ℝ]" => @Function.IsClosedProperConcave ℝ

/-!
Source/core/bridge triage for this item.

- `source-facing`: Proposition 38.5.3 gives three sufficient conditions for existence of the
  Chapter 38 function inner product.
- `core/canonical`: the owner abstractions already present are `Function.HasInnerProduct`,
  `convexConjugate` with notation `f⋆`, `concaveConjugate`, and the domain-relative-interior
  notation `riDom(·)`.
- `bridge/view`: the source phrases `dom g` and `dom g^*` for a concave function are rendered in
  the chapter orientation by `dom(-g)` and `dom(-concaveConjugate g)`, since the project's
  effective-domain owner is phrased on the convex side of the sign-duality.

Primary mathematical domain:
- Fenchel duality and existence of the Chapter 38 inner product.

Domain-style sampling used here:
- `Function.HasInnerProduct` from `Definition_38_5_2`;
- `riDom(·)` from `Chap01.Definition_4_4`;
- `convexConjugate` / `concaveConjugate` from Chapters 3 and 6.

Primitive data vs derived API:
- primitive inputs: a convex function `f` and a concave function `g` on a finite-dimensional real
  inner-product space;
- primitive owner layer already upstream: `HasInnerProduct f g`;
- derived API here: three source-facing sufficient conditions for that owner.

Layer target: `source-facing`, stated directly on `HasInnerProduct f g` rather than through a
parallel strong-duality package.
-/

-- Proof sketch: interpret `HasInnerProduct f g` as the zero-duality-gap statement
-- `sup_x (g* x - f x) = inf_y (f* y - g y)`. Apply the identity-map Fenchel theorem in the
-- orientation where the primal side is `f` and the dual side is `g*`; the closed proper concave
-- owner on `g` identifies `g**` with `g`, and the source condition
-- `ri(dom f) ∩ ri(dom g^*) ≠ ∅` is rendered by `riDom(f) ∩ riDom(-g∗)`.
/-- Proposition 38.5.3 (1): if `f` is convex proper, `g` is closed proper concave, and
`ri (dom f)` meets `ri (dom g^*)`, rendered by `riDom(f)` meeting `riDom(-g∗)`, then the
Chapter 38 inner product of `f` and `g` exists. -/
theorem hasInnerProduct_of_g_closed_and_nonempty_inter_riDom_f_concaveConjugate
    (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper)
    (hg : IsClosedProperConcave[ℝ] g)
    (hri : (riDom(f) ∩ riDom(-(g∗ : E → EReal))).Nonempty) :
    HasInnerProduct f g := sorry

-- Proof sketch: apply the same identity-map Fenchel theorem to the primal objective
-- `y ↦ f⋆ y - g y`. Closedness of `f` identifies `(f⋆)⋆` with `f`, and the source condition
-- `ri(dom g) ∩ ri(dom f^*) ≠ ∅` is represented by the chapter owners
-- `riDom(-g) ∩ riDom(f⋆)`.
/-- Proposition 38.5.3 (2): if `g` is concave proper, `f` is closed proper convex, and
`ri (dom g)` meets `ri (dom f^*)`, rendered by `riDom(-g)` meeting `riDom(f⋆)`, then the
Chapter 38 inner product of `f` and `g` exists. -/
theorem hasInnerProduct_of_f_closed_and_nonempty_inter_riDom_g_convexConjugate
    (hf : IsClosedProperConvex[ℝ] f)
    (hg_concave : g.IsConcave ℝ) (hg_proper : (-g).IsProper)
    (hri : (riDom(-g) ∩ riDom(f⋆)).Nonempty) :
    HasInnerProduct f g := sorry

-- Proof sketch: if `dom(f)` is bounded, Chapter 13 makes `f⋆` finite everywhere, so
-- `riDom(f⋆) = Set.univ`; similarly, boundedness of the concave-side effective domain `dom(-g)`
-- makes `-concaveConjugate g` finite everywhere. Hence one of the two previous relative-interior
-- qualifications becomes automatic, and `HasInnerProduct f g` follows.
/-- Proposition 38.5.3 (3): a simple sufficient condition is that `f` be closed proper convex,
`g` be closed proper concave, and that either `dom(f)` or the concave-side effective domain
`dom(-g)` corresponding to the source `dom g` be bounded. -/
theorem hasInnerProduct_of_closed_and_bounded_effectiveDomain
    (hf : IsClosedProperConvex[ℝ] f)
    (hg : IsClosedProperConcave[ℝ] g)
    (hdom_bounded : IsBounded dom(f) ∨ IsBounded dom(-g)) :
    HasInnerProduct f g := sorry

end

end Function

/-! ### Proposition_38_5_4 (from Chap08) -/
noncomputable section

open scoped Rockafellar

universe u v w

namespace Function

section IndicatorOfPoint

variable {X : Type u} {Y : Type v} {α : Type w}
variable [AddGroup α] [ConditionallyCompleteLattice α] [HasPairing X Y α]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Proposition 38.5.4 evaluates the Chapter 38 inner product of the convex
  indicator of the point `a` and the concave indicator of the point `b`.
- `core/canonical`: the owner already introduced upstream is `Function.innerProduct`; the point
  indicators are already owned by the Chapter 1 notation `δ[α](· | C)`.
- `bridge/view`: the self-inner-product reading from the source is a specialization of the
  canonical pairing statement, so this file should reuse the Chapter 33 singleton-pairing bridge
  theorems instead of rebuilding conjugate/support calculations locally.

Primary mathematical domain:
- Fenchel-style function pairings on the primitive pairing layer.

Domain-style sampling used here:
- `Function.innerProduct` from `Definition_38_5_2`;
- `convexConjugate_eq_iSup_pairing_sub` from `Chap03.Defn_12_2`;
- `Function.concaveConjugate_negIndicator_singleton` from `Chap07.Lemma33_0_9`;
- `Function.convexPairing_indicator_singleton` from `Chap07.Lemma33_0_9`.

Primitive data vs derived API:
- primitive data: a left point `a : X`, a right point `b : Y`, and the ambient pairing;
- derived API: the Chapter 38 inner-product value of the corresponding singleton indicators.

Layer target: `source-facing`, stated directly on the Chapter 38 function owner at the canonical
pairing level.
-/

local instance indicatorSingletonHasPairing : HasPairing Y X α :=
  HasPairing.swap

-- Proof sketch: rewrite the Chapter 38 owner `innerProduct` as the outer supremum formula and
-- collapse the concave singleton indicator there by the Chapter 33 singleton-pairing theorem.
-- The remaining supremum is exactly the convex pairing of the singleton indicator at `a`, which
-- the companion Chapter 33 theorem evaluates to the ambient pairing value `⟪a, b⟫ₚ`.
/-- Proposition 38.5.4: the Chapter 38 inner product of the convex indicator of the point `a`
and the concave indicator of the point `b` is the ambient pairing value `⟪a, b⟫ₚ`. In the source
self-pairing case, this specializes to the ordinary inner product. -/
theorem innerProduct_indicator_singleton_eq_pairing
    (a : X) (b : Y) :
    innerProduct (δ[α](· | ({a} : Set X))) (fun y ↦ -(δ[α](y | ({b} : Set Y)))) =
      (⟪a, b⟫ₚ : WithBotTop α) := by
  calc
    innerProduct (δ[α](· | ({a} : Set X))) (fun y ↦ -(δ[α](y | ({b} : Set Y)))) =
        ⟪(δ[α](· | ({a} : Set X))), b⟫ᶠ := by
          rw [innerProduct_eq_iSup_concaveConjugate_sub, convexConjugate_eq_iSup_pairing_sub]
          refine iSup_congr fun x ↦ ?_
          exact
            congrArg (fun t : WithBotTop α ↦ t - δ[α](x | ({a} : Set X)))
              (concaveConjugate_negIndicator_singleton b x)
    _ = (⟪a, b⟫ₚ : WithBotTop α) := by
          exact convexPairing_indicator_singleton a b

end IndicatorOfPoint

end Function

/-! ### Proposition_38_5_5 (from Chap08) -/
noncomputable section

universe u v w

open scoped Rockafellar

namespace Function

section

variable {X : Type u} {Y : Type v} {α : Type w}
variable [AddGroup α] [ConditionallyCompleteLattice α]
variable [HasPairing X Y α]

local instance : HasPairing Y X α :=
  HasPairing.swap

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 38.5.5 identifies the Chapter 38 inner product of `f` with the
  concave singleton indicator at `xStar`.
- `core/canonical`: the owner expressions are already `innerProduct` from Definition 38.5.2 and
  the Chapter 33 convex-pairing notation `⟪f, xStar⟫ᶠ = f⋆ xStar`.
- `bridge/view`: this item is therefore only a bridge between those existing owners. The actual
  singleton-indicator conjugate evaluation is already owned upstream by
  `concaveConjugate_negIndicator_singleton`, so this file should reuse that theorem
  directly rather than keeping a parallel local proof route.

Primary mathematical domain:
- Fenchel duality pairings for convex and concave conjugates.

Domain-style sampling used here:
- `innerProduct` and `innerProduct_eq_iSup_concaveConjugate_sub` from `Definition_38_5_2`;
- `convexConjugate_eq_iSup_pairing_sub` from the Chapter 12 owner API;
- `concaveConjugate_negIndicator_singleton` from `Lemma33_0_9`.
-/

-- Proof sketch: unfold `innerProduct` as `sup_x (g⋆ x - f x)` for
-- `g y = -δ[α](y | ({xStar} : Set Y))`. The concave conjugate of this negative singleton
-- indicator is the pairing function `x ↦ ⟪x, xStar⟫ₚ`, so the supremum becomes the Chapter 33
-- convex conjugate formula for `⟪f, xStar⟫ᶠ`.
/-- Proposition 38.5.5: the Section 38 inner product of `f` with the concave singleton indicator
`y ↦ -δ[α](y | ({xStar} : Set Y))` agrees with the Chapter 33 convex-pairing notation
`⟪f, xStar⟫ᶠ` for the conjugate value `f⋆ xStar`. -/
theorem innerProduct_neg_indicator_singleton_eq_convexPairing
    (f : X → WithBotTop α) (xStar : Y) :
    innerProduct f (-(δ[α](· | ({xStar} : Set Y)))) = ⟪f, xStar⟫ᶠ := by
  rw [innerProduct_eq_iSup_concaveConjugate_sub, convexConjugate_eq_iSup_pairing_sub]
  refine iSup_congr fun x ↦ ?_
  rw [concaveConjugate_negIndicator_singleton xStar x]

end

end Function

/-! ### Theorem_38_5 (from Chap08) -/
noncomputable section

open scoped Rockafellar

universe u v w

namespace Bifunction

section Owner

variable {U : Type u} {X : Type v} {Y : Type w}
variable {α : Type*}
variable [ConditionallyCompleteLattice α] [Add α]

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 38.5 studies the product `GF` of two convex bifunctions, defined by
  `((GF) u) y = inf_x (F u x + G x y)`.
- `core/canonical`: the owner abstractions already present upstream are `Bifunction.image` for the
  one-step elimination of an intermediate variable, `Bifunction.adjoint`, and the
  slice-domain owner `Bifunction.dom`.
- `bridge/view`: the Chapter 38 product is therefore the thin source-facing bridge
  `fun u ↦ image G (F u)` rather than a second pointwise-infimum wheel.

Primary mathematical domain:
- composition of proper convex bifunctions and the adjoint-duality formula `(GF)* = F*G*`.

Domain-style sampling used here:
- `Bifunction.image` and `Bifunction.image_apply` from `Definition_38_0_4`;
- `Bifunction.adjoint` from `Chap06.Lemma_31_0_8`;
- `Bifunction.dom` and `Bifunction.IsProper` from `Chap08.Theorem_38_1`.

Primitive data vs derived API:
- primitive source data: bifunctions `F : U → X → WithBotTop α` and
  `G : X → Y → WithBotTop α`;
- primitive source-facing owner introduced here: `Bifunction.comp`, used in the raw owner form
  `comp G F` because dot notation would collide with ordinary `Function.comp`;
- derived API: the pointwise image formula, the indexed-infimum formula, graph convexity of
  `Function.uncurry`, the adjoint identity, and the attainment clause for the dual-side product.

Layer target: `source-facing`. The product `GF` is genuine source-facing content for §38.5, but it
should be owned by a thin bridge over the existing image operator.

Notation decision:
- no new notation is introduced. The source juxtaposition `GF` is not a stable Lean surface form,
  and a symbolic surrogate would be decorative rather than canonical. The short owner name `comp`
  keeps the mathematical meaning explicit without introducing parser noise.
-/

/-- Theorem 38.5 owner: the product of bifunctions, obtained by taking for each `u` the image of
the slice `F u` under `G`. -/
abbrev comp
    (G : X → Y → WithBotTop α) (F : U → X → WithBotTop α) :
    U → Y → WithBotTop α :=
  fun u ↦ image G (F u)

/-- Evaluating the product `comp G F` at `(u, y)` is the image formula for the slice `F u`
under `G`. -/
@[simp] theorem comp_apply
    (G : X → Y → WithBotTop α) (F : U → X → WithBotTop α) (u : U) (y : Y) :
    comp G F u y = image G (F u) y :=
  rfl

/-- Evaluating `comp G F` at `(u, y)` gives the indexed infimum
`inf_x (F u x + G x y)`. -/
@[simp] theorem comp_apply_eq_iInf
    (G : X → Y → WithBotTop α) (F : U → X → WithBotTop α) (u : U) (y : Y) :
    comp G F u y = ⨅ x : X, F u x + G x y := by
  simpa [comp] using image_apply G (F u) y

end Owner

section Theorem

variable {U : Type u} {X : Type v} {Y : Type w}

local notation "ri(" C ")" => intrinsicInterior ℝ C

section Convexity

variable {𝕜 : Type*} {α : Type*}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid U] [SMul 𝕜 U]
variable [AddCommMonoid X] [SMul 𝕜 X]
variable [AddCommMonoid Y] [SMul 𝕜 Y]
variable [AddCommMonoid α] [SMul 𝕜 α] [LE α]
variable [ConditionallyCompleteLattice α] [Add α]

/-- Theorem 38.5, convexity clause: the product `comp G F` of convex bifunctions is again convex,
expressed canonically as convexity of the uncurried graph function. -/
theorem uncurry_comp_isConvex
    {F : U → X → WithBotTop α} {G : X → Y → WithBotTop α}
    (hF : Function.IsConvex 𝕜 (Function.uncurry F))
    (hG : Function.IsConvex 𝕜 (Function.uncurry G)) :
    Function.IsConvex 𝕜 (Function.uncurry (comp G F)) := by
  sorry

end Convexity

section Adjoint

variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
variable [HasLinearPairing U U ℝ] [HasContinuousPairing U U ℝ]
variable [HasLinearPairing X X ℝ] [HasContinuousPairing X X ℝ]
variable [HasLinearPairing Y Y ℝ] [HasContinuousPairing Y Y ℝ]
variable {F : U → X → EReal} {G : X → Y → EReal}

/-- Theorem 38.5, adjoint clause: if the relative interiors of `dom F*` and `dom G` meet, then
the adjoint of the product is the product of the adjoints, rendered by the owners
`adjoint`, `dom`, and `comp`. -/
theorem adjointFunction_comp_eq_comp_adjointFunction_of_common_riDom
    (hF_convex : Function.IsConvex ℝ (Function.uncurry F)) (hF_proper : IsProper F)
    (hG_convex : Function.IsConvex ℝ (Function.uncurry G)) (hG_proper : IsProper G)
    (hri :
      (ri(dom (adjoint X U F)) ∩ ri(dom G)).Nonempty)
    :
    adjoint Y U (comp G F) =
      comp (adjoint X U F) (adjoint Y X G) := by
  sorry

/-- Pointwise form of the adjoint identity in Theorem 38.5. -/
@[simp] theorem adjointFunction_comp_apply_of_common_riDom
    (hF_convex : Function.IsConvex ℝ (Function.uncurry F)) (hF_proper : IsProper F)
    (hG_convex : Function.IsConvex ℝ (Function.uncurry G)) (hG_proper : IsProper G)
    (hri :
      (ri(dom (adjoint X U F)) ∩ ri(dom G)).Nonempty)
    (yStar : Y) (uStar : U) :
    adjoint Y U (comp G F) yStar uStar =
      comp (adjoint X U F) (adjoint Y X G) yStar uStar := by
  simpa using
    congrFun
      (congrFun
        (adjointFunction_comp_eq_comp_adjointFunction_of_common_riDom
          hF_convex hF_proper hG_convex hG_proper hri)
        yStar)
      uStar

/-- Theorem 38.5, attainment clause in owner form: under the same common-relative-interior
hypothesis, the dual-side product `F*G*` is attained at every pair `(u*, y*)`. Because the
chapter owner `comp` is defined by an infimum, this is stated as existence of an intermediate
`x*` realizing the value of `comp (adjoint F) (adjoint G) y* u*`. -/
theorem exists_eq_comp_adjointFunction_of_common_riDom
    (hF_convex : Function.IsConvex ℝ (Function.uncurry F)) (hF_proper : IsProper F)
    (hG_convex : Function.IsConvex ℝ (Function.uncurry G)) (hG_proper : IsProper G)
    (hri :
      (ri(dom (adjoint X U F)) ∩ ri(dom G)).Nonempty)
    (yStar : Y) (uStar : U) :
    ∃ xStar : X,
      comp (adjoint X U F) (adjoint Y X G) yStar uStar =
        adjoint Y X G yStar xStar + adjoint X U F xStar uStar := by
  sorry

end Adjoint

end Theorem

end Bifunction

/-! ### Proposition_38_5_6 (from Chap08) -/
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
