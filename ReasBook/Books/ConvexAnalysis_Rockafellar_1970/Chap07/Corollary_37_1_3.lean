import ConvexAnalysis_Rockafellar_1970.Chap01.HasPairing
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_8
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_2
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_3
import ConvexAnalysis_Rockafellar_1970.Chap07.Corollary_37_1_2
import ConvexAnalysis_Rockafellar_1970.Chap07.Proposition_37_1_3

noncomputable section

universe u u' v v'

open scoped Rockafellar

namespace SaddleFunction

section

open Bifunction

variable {R : Type*} {α : Type*}
variable {U : Type u} {UStar : Type u'} {X : Type v} {XStar : Type v'}
variable [Ring R] [PartialOrder R]
variable [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [AddCommGroup α]
variable [IsOrderedAddMonoid α]
variable [TopologicalSpace U] [AddCommGroup U] [Module R U]
variable [TopologicalSpace UStar] [AddCommGroup UStar] [Module R UStar]
variable [TopologicalSpace X] [AddCommGroup X] [Module R X]
variable [TopologicalSpace XStar] [AddCommGroup XStar] [Module R XStar]
variable [HasPairing U UStar (WithBotTop α)] [HasPairing X XStar (WithBotTop α)]
variable [HasPairingZeroRight U UStar (WithBotTop α)]
variable [HasPairingZeroLeft X XStar (WithBotTop α)]
variable [SMul R (WithBotTop α)]

local notation "lowerConjugate" =>
  (Bifunction.lowerConjugate : (U → XStar → WithBotTop α) → UStar → X → WithBotTop α)

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 37.1.3 turns origin relative-interior hypotheses on the two
  conjugate-domain factors into existence and finiteness of the ambient saddle value of `K`.
- `core/canonical`: the owner layer already present in the chapter is `HasSaddleValue`,
  `maximinValue`, `lowerConjugate`, `dom₁`, `dom₂`, and `ri[R](·)`.
- `bridge/view`: the source domain symbols `C*` and `D*` are written through the Chapter 37 owner
  `lowerConjugate K` and the Chapter 34 coordinate-domain owners `dom₁` and `dom₂`.

Primary mathematical domain:
- minimax theory for closed concave-convex saddle-functions via conjugate-domain geometry.

Domain-style sampling used here:
- `Bifunction.HasSaddleValue` and `Bifunction.maximinValue` from `Definition_36_0_1`;
- `Bifunction.lowerConjugate` from `Definition_37_1_1`;
- `SaddleFunction.dom₁` and `SaddleFunction.dom₂` from `Defn_34_3`;
- `ri[R](·)` from `Chap02.Text_6_8`;
- `Bifunction.lowerConjugate_eq_upperConjugate_of_isConcaveConvex_of_isClosed_of_mem_ri_dom₁_or_mem_ri_dom₂`
  from
  `Corollary_37_1_2`;
- `Bifunction.minimaxValue_eq_neg_lowerConjugate_zero_zero` and
  `Bifunction.maximinValue_eq_neg_upperConjugate_zero_zero` from `Proposition_37_1_3`.

Primitive data vs derived API:
- primitive data: a saddle kernel `K : U → XStar → WithBotTop α` with hypotheses `IsClosed K`,
  `IsConcaveConvex R K`, together with the canonical zero-pairing owners
  `HasPairingZeroRight U UStar (WithBotTop α)` and
  `HasPairingZeroLeft X XStar (WithBotTop α)` needed to identify the Chapter 36 ambient values
  with the Chapter 37 conjugates at the base point `(0, 0)`;
- derived API: the owner-level saddle-value conclusion `HasSaddleValue K` and the finiteness of
  the resulting ambient saddle value.

Redundant source assumptions:
- the source also lists properness, but these two corollary clauses only use the origin-relative
  interior hypotheses on the conjugate-domain owners themselves, so `IsProper K` is redundant and
  removed from the public API.

Layer target: `source-facing`, but the first conclusion is expressed on the canonical Chapter 36
owner `HasSaddleValue K` rather than by restating its defining equality.
-/

-- Proof sketch: combine Proposition 37.1.3 with the standard minimax qualification coming from
-- the origin lying in the relative interior of one conjugate-domain factor, then rewrite the
-- source domain symbols `C*` and `D*` through the canonical Chapter 37 owner
-- `dom₁ (lowerConjugate K)` and `dom₂ (lowerConjugate K)`.
/-- Corollary 37.1.3 (1): if the origin belongs to the relative interior of either conjugate-domain
factor of a closed concave-convex saddle-function `K`, then the ambient maximin and
minimax values of `K` coincide. Here the common conjugate-domain factors `C*` and `D*` are
written as `dom₁ (lowerConjugate K)` and `dom₂ (lowerConjugate K)`. -/
theorem hasSaddleValue_of_zero_mem_ri_conjugateDom₁_or_zero_mem_ri_conjugateDom₂
    {K : U → XStar → WithBotTop α}
    (hK_closed : IsClosed K)
    (hK_concaveConvex : IsConcaveConvex R K)
    (hri :
      (0 : UStar) ∈ ri[R](dom₁ (lowerConjugate K)) ∨
        (0 : X) ∈ ri[R](dom₂ (lowerConjugate K))) :
    HasSaddleValue K := by
  rw [HasSaddleValue, HasSaddleValueOn]
  calc
    maximinValue K = -(K ^*((0 : UStar), (0 : X))) :=
      maximinValue_eq_neg_upperConjugate_zero_zero K
    _ = -(K _*((0 : UStar), (0 : X))) := by
      rw [← lowerConjugate_eq_upperConjugate_of_isConcaveConvex_of_isClosed_of_mem_ri_dom₁_or_mem_ri_dom₂
        hK_concaveConvex hK_closed hri]
    _ = minimaxValue K := by
      symm
      exact minimaxValue_eq_neg_lowerConjugate_zero_zero K

-- Proof sketch: apply the first clause to obtain the common saddle value, then use Proposition
-- 37.1.3 at the zero base point. When the origin lies in the relative interiors of both
-- conjugate-domain factors, the conjugate value at `(0, 0)` is finite, so the common saddle
-- value is finite as well.
/-- Corollary 37.1.3 (2): if the origin belongs to the relative interiors of both conjugate-domain
factors of `K`, equivalently `((0, 0) : UStar × X)` lies in the relative interior of the effective
domain `dom (lowerConjugate K)`, then the common saddle value of `K` is finite. -/
theorem finite_saddleValue_of_zero_mem_ri_conjugateDom₁_and_zero_mem_ri_conjugateDom₂
    {K : U → XStar → WithBotTop α}
    (hK_closed : IsClosed K)
    (hK_concaveConvex : IsConcaveConvex R K)
    (hri : ((0 : UStar), (0 : X)) ∈ ri[R](dom (lowerConjugate K))) :
    ⊥ < maximinValue K ∧ maximinValue K < ⊤ := by
  have hri_dom :
      (0 : UStar) ∈ ri[R](dom₁ (lowerConjugate K)) ∧
        (0 : X) ∈ ri[R](dom₂ (lowerConjugate K)) := by
    simpa [SaddleFunction.dom, ri_prod_eq, Set.mem_prod] using hri
  have hri_dom₁ : (0 : UStar) ∈ ri[R](dom₁ (lowerConjugate K)) := hri_dom.1
  have hri_dom₂ : (0 : X) ∈ ri[R](dom₂ (lowerConjugate K)) := hri_dom.2
  have hmax :
      maximinValue K = -(K _*((0 : UStar), (0 : X))) := by
    calc
      maximinValue K = -(K ^*((0 : UStar), (0 : X))) :=
        maximinValue_eq_neg_upperConjugate_zero_zero K
      _ = -(K _*((0 : UStar), (0 : X))) := by
        rw [← lowerConjugate_eq_upperConjugate_of_isConcaveConvex_of_isClosed_of_mem_ri_dom₁_or_mem_ri_dom₂
          hK_concaveConvex hK_closed (Or.inl hri_dom₁)]
  have hdom₁_zero : (0 : UStar) ∈ dom₁ (lowerConjugate K) :=
    intrinsicInterior_subset hri_dom₁
  have hdom₂_zero : (0 : X) ∈ dom₂ (lowerConjugate K) :=
    intrinsicInterior_subset hri_dom₂
  have hbot_lower : ⊥ < K _*((0 : UStar), (0 : X)) :=
    (mem_dom₁.mp hdom₁_zero) 0
  have htop_lower : K _*((0 : UStar), (0 : X)) < ⊤ :=
    (mem_dom₂.mp hdom₂_zero) 0
  constructor
  · rw [hmax]
    simpa using (WithBotTop.neg_lt_neg_iff).2 htop_lower
  · rw [hmax]
    simpa using (WithBotTop.neg_lt_neg_iff).2 hbot_lower

end

end SaddleFunction
