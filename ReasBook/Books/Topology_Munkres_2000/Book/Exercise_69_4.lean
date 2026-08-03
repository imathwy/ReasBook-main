module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

public section

-- The hint is the canonical criterion for a product of additive groups to be cyclic.
#check AddGroup.isAddCyclic_prod_iff

/-- The Chinese remainder equivalences for `30 = 2 * 15 = 3 * 10` identify two
direct products whose cyclic factor orders are different. -/
def cyclicFactorEquiv : (ZMod 2 × ZMod 15) ≃+ (ZMod 3 × ZMod 10) :=
  ((ZMod.chineseRemainder (by decide : Nat.Coprime 2 15)).symm.trans
    ((ZMod.ringEquivCongr (by decide : 2 * 15 = 3 * 10)).trans
      (ZMod.chineseRemainder (by decide : Nat.Coprime 3 10)))).toAddEquiv

/-- Exercise 69.4: The orders of two cyclic direct-sum factors are not uniquely
determined by the resulting group, even up to reordering, as witnessed by the
equivalence `cyclicFactorEquiv` and the factorizations `30 = 2 * 15 = 3 * 10`. -/
theorem cyclicFactorOrders_not_unique :
    ({Nat.card (ZMod 2), Nat.card (ZMod 15)} : Finset ℕ) ≠
      {Nat.card (ZMod 3), Nat.card (ZMod 10)} := by
  simp only [Nat.card_eq_fintype_card, ZMod.card]
  decide
