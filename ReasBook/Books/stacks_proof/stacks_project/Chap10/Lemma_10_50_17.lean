import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Valuation

section

variable (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]

local notation "K" => FractionRing A
local notation "v" => ValuationRing.valuation A K
local notation "O" => Valuation.integer v
local notation "Γ" => ValuationRing.ValueGroup A K
local notation "Γ≤1" => { γ : Γ // γ ≤ (1 : Γ) }

/- Domain triage:
* primary domain: commutative algebra of ideals in valuation rings via the canonical value group;
* source-facing layer: the textbook correspondence between ideals of a valuation ring and initial
  segments of the integral cone of its value group, together with the prime-ideal compatibility;
* core/canonical owner abstraction for this item: the order isomorphism
  `Ideal O ≃o Order.Ideal Γ≤1`, built from the owner declarations
  `ValuationRing.equivInteger`, `leIdeal`, `leIdeal_mono`, `leIdeal_v_le_of_mem`, and
  `RingEquiv.idealComapOrderIso`;
* bridge/view layer: the public `valuationRing_ideal_correspondence` transports the integer-ring
  owner isomorphism back to ideals of `A`.
* primitive data vs. derived API: the primitive input is only the valuation ring `A` and its
  canonical valuation `v`; the order-ideal correspondence and valuation-prime condition are
  derived from the `leIdeal` family and the canonical ring equivalence `A ≃+* O`.
-/

private theorem valuation_surjective : Function.Surjective v := by
  intro γ
  refine Quotient.inductionOn γ ?_
  intro x
  exact ⟨x, rfl⟩

private theorem leIdeal_one : leIdeal v (1 : Γ) = ⊤ := by
  ext x
  constructor
  · intro _
    trivial
  · intro _
    exact x.2

private noncomputable def valuationRingIdealToOrderIdeal
    (I : Ideal O) : Order.Ideal Γ≤1 where
  carrier := { γ | leIdeal v γ.1 ≤ I }
  lower' := by
    intro γ δ hδγ hγ
    exact (leIdeal_mono v hδγ).trans hγ
  nonempty' := by
    refine ⟨⟨0, zero_le'⟩, ?_⟩
    change leIdeal v (0 : Γ) ≤ I
    rw [leIdeal_zero]
    exact bot_le
  directed' := by
    intro γ₁ hγ₁ γ₂ hγ₂
    by_cases h : γ₁ ≤ γ₂
    · exact ⟨γ₂, hγ₂, h, le_rfl⟩
    · exact ⟨γ₁, hγ₁, le_rfl, le_of_not_ge h⟩

private noncomputable def valuationRingOrderIdealToIdeal
    (J : Order.Ideal Γ≤1) : Ideal O where
  carrier := { x | ⟨v x, x.2⟩ ∈ J }
  zero_mem' := by
    obtain ⟨γ, hγ⟩ := J.nonempty
    refine J.lower ?_ hγ
    change (0 : Γ) ≤ γ.1
    exact zero_le'
  add_mem' := by
    intro x y hx hy
    by_cases hxy : v x ≤ v y
    · exact J.lower
        (show (⟨v (x + y), (x + y).2⟩ : Γ≤1) ≤ ⟨v y, y.2⟩ from
          by simpa [max_eq_right hxy] using Valuation.map_add v x y)
        hy
    · exact J.lower
        (show (⟨v (x + y), (x + y).2⟩ : Γ≤1) ≤ ⟨v x, x.2⟩ from
          by simpa [max_eq_left <| le_of_not_ge hxy] using Valuation.map_add v x y)
        hx
  smul_mem' := by
    intro a x hx
    refine J.lower (show (⟨v ((a : O) * x), ((a : O) * x).2⟩ : Γ≤1) ≤ ⟨v x, x.2⟩ from ?_) hx
    change v ((a : O) * x) ≤ v x
    simpa [Subring.smul_def, map_mul] using mul_le_of_le_one_left zero_le' a.2

private noncomputable def valuationRingIntegerIdealOrderIso :
    Ideal O ≃o Order.Ideal Γ≤1 where
  toFun := valuationRingIdealToOrderIdeal A
  invFun := valuationRingOrderIdealToIdeal A
  left_inv := by
    intro I
    ext x
    constructor
    · intro hx
      exact hx <| by simp [mem_leIdeal_iff]
    · intro hx
      simpa [valuationRingOrderIdealToIdeal, valuationRingIdealToOrderIdeal] using
        (leIdeal_v_le_of_mem v hx)
  right_inv := by
    intro J
    ext γ
    constructor
    · intro hγ
      obtain ⟨x, hx⟩ := valuation_surjective A γ.1
      let x' : (ValuationRing.valuation A K).integer := ⟨x, by
        simpa [Valuation.mem_integer_iff, hx] using γ.2⟩
      have hx' : x' ∈ leIdeal v γ.1 := by
        simp [mem_leIdeal_iff, x', hx]
      simpa [valuationRingOrderIdealToIdeal, hx, x'] using hγ hx'
    · intro hγ x hx
      exact J.lower hx hγ
  map_rel_iff' := by
    intro I J
    change valuationRingIdealToOrderIdeal A I ≤ valuationRingIdealToOrderIdeal A J ↔ I ≤ J
    constructor
    · intro h x hx
      have hx' : (⟨v x, x.2⟩ : Γ≤1) ∈ valuationRingIdealToOrderIdeal A I :=
        leIdeal_v_le_of_mem v hx
      exact (h hx') <| by simp [mem_leIdeal_iff]
    · intro h γ hγ
      exact hγ.trans h

namespace Order.Ideal

/-- The source-facing prime condition on an ideal of the integral value-group cone. In additive
normalization, this is exactly the textbook condition `γ + δ ∈ I → γ ∈ I ∨ δ ∈ I`. -/
def IsValuationPrime (J : Order.Ideal Γ≤1) : Prop :=
  (⟨1, le_rfl⟩ : Γ≤1) ∉ J ∧
    ∀ ⦃γ δ : Γ⦄, ∀ hγ : γ ≤ 1, ∀ hδ : δ ≤ 1,
      (⟨γ * δ, mul_le_one' hγ hδ⟩ : Γ≤1) ∈ J →
        (⟨γ, hγ⟩ : Γ≤1) ∈ J ∨ (⟨δ, hδ⟩ : Γ≤1) ∈ J

end Order.Ideal

private theorem valuationRingIntegerIdealOrderIso_isValuationPrime_iff (I : Ideal O) :
    I.IsPrime ↔ Order.Ideal.IsValuationPrime A (valuationRingIntegerIdealOrderIso A I) := by
  constructor
  · intro hI
    refine ⟨?_, ?_⟩
    · intro hOne
      have htop : (⊤ : Ideal O) ≤ I := by
        change leIdeal v (1 : Γ) ≤ I at hOne
        simpa [leIdeal_one A] using hOne
      exact hI.ne_top <| eq_top_iff.mpr htop
    · intro γ δ hγ hδ hγδ
      obtain ⟨x, hx⟩ := valuation_surjective A γ
      obtain ⟨y, hy⟩ := valuation_surjective A δ
      let x' : O := ⟨x, by simpa [Valuation.mem_integer_iff, hx] using hγ⟩
      let y' : O := ⟨y, by simpa [Valuation.mem_integer_iff, hy] using hδ⟩
      have hxy : x' * y' ∈ I := by
        apply hγδ
        simp [mem_leIdeal_iff, x', y', hx, hy, map_mul]
      rcases hI.mem_or_mem hxy with hxI | hyI
      · left
        simpa [valuationRingIdealToOrderIdeal, x', hx] using leIdeal_v_le_of_mem v hxI
      · right
        simpa [valuationRingIdealToOrderIdeal, y', hy] using leIdeal_v_le_of_mem v hyI
  · intro hI
    refine Ideal.isPrime_iff.mpr ⟨?_, ?_⟩
    · intro htop
      subst htop
      have hOne : (⟨1, le_rfl⟩ : Γ≤1) ∈ valuationRingIntegerIdealOrderIso A (⊤ : Ideal O) := by
        change leIdeal v (1 : Γ) ≤ (⊤ : Ideal O)
        simp [leIdeal_one A]
      exact hI.1 hOne
    · intro x y hxy
      have hxy' : (⟨v x * v y, mul_le_one' x.2 y.2⟩ : Γ≤1) ∈ valuationRingIntegerIdealOrderIso A I := by
        simpa [valuationRingIdealToOrderIdeal, map_mul] using leIdeal_v_le_of_mem v hxy
      rcases hI.2 x.2 y.2 hxy' with hx | hy
      · left
        exact hx <| by simp [mem_leIdeal_iff]
      · right
        exact hy <| by simp [mem_leIdeal_iff]

-- Proof sketch: identify an ideal of `A` with the initial segment of valuation values of its
-- elements in the canonical value group, restricted to the integral part `γ ≤ 1`; this gives the
-- inclusion-preserving bijection. Prime ideals correspond to the multiplicatively prime initial
-- segments, which in additive normalization are the textbook prime ideals of the nonnegative cone.
/-- Lemma 10.50.17: ideals of a valuation ring correspond bijectively, in an
inclusion-preserving way, to order ideals of the integral part of its canonical value group, and
this correspondence sends prime ideals to valuation-prime order ideals. -/
@[stacks 00IH]
noncomputable def valuationRing_ideal_correspondence :
    Ideal A ≃o Order.Ideal Γ≤1 :=
  (ValuationRing.equivInteger A K).idealComapOrderIso.symm.trans
    (valuationRingIntegerIdealOrderIso A)

/-- Prime ideals correspond to multiplicatively prime ideals of the integral value-group cone under
`valuationRing_ideal_correspondence`; in additive normalization this is the textbook prime-ideal
condition on `Γ_{\ge 0}`. -/
theorem valuationRing_ideal_correspondence_isPrime_iff (I : Ideal A) :
    I.IsPrime ↔ Order.Ideal.IsValuationPrime A (valuationRing_ideal_correspondence A I) := by
  let e : A ≃+* O := ValuationRing.equivInteger A K
  simpa [valuationRing_ideal_correspondence, e] using
    (show I.IsPrime ↔ Order.Ideal.IsValuationPrime A (valuationRingIntegerIdealOrderIso A (I.map e)) from by
      constructor
      · intro hI
        letI : I.IsPrime := hI
        have hmap : (I.map e).IsPrime := Ideal.map_isPrime_of_equiv e
        exact (valuationRingIntegerIdealOrderIso_isValuationPrime_iff A (I.map e)).mp hmap
      · intro hI
        have hmap : (I.map e).IsPrime :=
          (valuationRingIntegerIdealOrderIso_isValuationPrime_iff A (I.map e)).mpr hI
        letI : (I.map e).IsPrime := hmap
        have hcomap : (Ideal.comap e (I.map e)).IsPrime := Ideal.comap_isPrime e (I.map e)
        rw [Ideal.comap_map_of_surjective e e.surjective] at hcomap
        have hs : I ⊔ Ideal.comap e ⊥ = I := by
          rw [Ideal.comap_bot_of_injective e e.injective, sup_of_le_left bot_le]
        exact hs ▸ hcomap)

end
