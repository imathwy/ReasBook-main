module

public import Topology_Munkres_2000.Book.Exercise_69_1.Abelianization
public import Topology_Munkres_2000.Book.Exercise_68_2
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

public section

open scoped Monoid.Coprod

universe u₁ u₂ v₁ v₂

namespace Monoid.Coprod

/-- Companion for Exercise 69.3 (a): The abelianization of a free product of two finite
cyclic groups has cardinality equal to the product of the cardinalities of the factors. -/
theorem natCard_abelianization_eq_mul {G₁ : Type u₁} {G₂ : Type u₂}
    [Group G₁] [Group G₂] [Finite G₁] [Finite G₂] [IsCyclic G₁] [IsCyclic G₂] :
    Nat.card (Abelianization (G₁ ∗ G₂)) = Nat.card G₁ * Nat.card G₂ := by
  -- Cyclicity identifies each factor with its abelianization.
  letI : CommGroup G₁ := IsCyclic.commGroup
  letI : CommGroup G₂ := IsCyclic.commGroup
  -- The binary free-product equivalence then reduces cardinality to a product.
  calc
    Nat.card (Abelianization (G₁ ∗ G₂)) =
        Nat.card (Abelianization G₁ × Abelianization G₂) :=
      Nat.card_congr (Abelianization.coprodMulEquivProd G₁ G₂).toEquiv
    _ = Nat.card (Abelianization G₁) * Nat.card (Abelianization G₂) :=
      Nat.card_prod _ _
    _ = Nat.card G₁ * Nat.card G₂ :=
      congrArg₂ (fun a b : ℕ ↦ a * b)
        (Nat.card_congr (Abelianization.equivOfComm (H := G₁)).toEquiv).symm
        (Nat.card_congr (Abelianization.equivOfComm (H := G₂)).toEquiv).symm

/-- Companion for Exercise 69.3 (b): The order of every finite-order element of a free
product of two finite cyclic groups is at most the larger factor cardinality. -/
theorem orderOf_le_max_factor_card {G₁ : Type u₁} {G₂ : Type u₂}
    [Group G₁] [Group G₂] [Finite G₁] [Finite G₂] [IsCyclic G₁] [IsCyclic G₂]
    (x : G₁ ∗ G₂) (h_x : IsOfFinOrder x) :
    orderOf x ≤ max (Nat.card G₁) (Nat.card G₂) := by
  -- Exercise 68.2 conjugates every torsion element into one of the factors.
  rcases (isOfFinOrder_iff_isConj_factor x).mp h_x with
    ⟨g, _, hconj⟩ | ⟨g, _, hconj⟩
  · obtain ⟨c, hc⟩ := hconj
    -- Conjugacy and the injective inclusion preserve order, after which finiteness bounds it.
    calc
      orderOf x = orderOf (inl g) := SemiconjBy.orderOf_eq (↑c) hc
      _ = orderOf g :=
        orderOf_injective (inl : G₁ →* G₁ ∗ G₂) inl_injective g
      _ ≤ Nat.card G₁ := orderOf_le_card
      _ ≤ max (Nat.card G₁) (Nat.card G₂) := le_max_left _ _
  · obtain ⟨c, hc⟩ := hconj
    -- The same argument applies to the right factor.
    calc
      orderOf x = orderOf (inr g) := SemiconjBy.orderOf_eq (↑c) hc
      _ = orderOf g :=
        orderOf_injective (inr : G₂ →* G₁ ∗ G₂) inr_injective g
      _ ≤ Nat.card G₂ := orderOf_le_card
      _ ≤ max (Nat.card G₁) (Nat.card G₂) := le_max_right _ _

/-- Companion for Exercise 69.3 (b): The larger factor cardinality occurs as the order of
an element of the free product. -/
theorem exists_orderOf_eq_max_factor_card {G₁ : Type u₁} {G₂ : Type u₂}
    [Group G₁] [Group G₂] [Finite G₁] [Finite G₂] [IsCyclic G₁] [IsCyclic G₂] :
    ∃ x : G₁ ∗ G₂, orderOf x = max (Nat.card G₁) (Nat.card G₂) := by
  -- Choose a full-order cyclic generator from whichever factor has larger cardinality.
  by_cases hcard : Nat.card G₁ ≤ Nat.card G₂
  · obtain ⟨g : G₂, hg⟩ :=
      (isCyclic_iff_exists_orderOf_eq_natCard (α := G₂)).mp inferInstance
    refine ⟨inr g, ?_⟩
    -- Injecting the generator preserves its order and realizes the maximum.
    calc
      orderOf (inr g) = orderOf g :=
        orderOf_injective (inr : G₂ →* G₁ ∗ G₂) inr_injective g
      _ = Nat.card G₂ := hg
      _ = max (Nat.card G₁) (Nat.card G₂) := (max_eq_right hcard).symm
  · have hcard' : Nat.card G₂ ≤ Nat.card G₁ :=
      Nat.le_of_lt (Nat.lt_of_not_ge hcard)
    obtain ⟨g : G₁, hg⟩ :=
      (isCyclic_iff_exists_orderOf_eq_natCard (α := G₁)).mp inferInstance
    refine ⟨inl g, ?_⟩
    -- The left inclusion gives the symmetric realization when the left factor is larger.
    calc
      orderOf (inl g) = orderOf g :=
        orderOf_injective (inl : G₁ →* G₁ ∗ G₂) inl_injective g
      _ = Nat.card G₁ := hg
      _ = max (Nat.card G₁) (Nat.card G₂) := (max_eq_left hcard').symm

/-- Helper for Exercise 69.3: positive natural pairs with equal products and equal maxima
agree either directly or after swapping their entries. -/
private lemma positiveNatPairEqOrEqSwap {a b c d : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hprod : a * b = c * d) (hmax : max a b = max c d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  -- Split according to which entry realizes each maximum.
  by_cases hba : b ≤ a
  · by_cases hdc : d ≤ c
    · have hac : a = c := by
        calc
          a = max a b := (max_eq_left hba).symm
          _ = max c d := hmax
          _ = c := max_eq_left hdc
      subst c
      -- Equal products now cancel the common positive maximum.
      have hbd : b = d := Nat.eq_of_mul_eq_mul_left ha hprod
      exact Or.inl ⟨rfl, hbd⟩
    · have hcd : c ≤ d := Nat.le_of_lt (Nat.lt_of_not_ge hdc)
      have had : a = d := by
        calc
          a = max a b := (max_eq_left hba).symm
          _ = max c d := hmax
          _ = d := max_eq_right hcd
      subst d
      -- Commute the second product to expose the shared positive factor.
      have hprod' : a * b = a * c := by
        simpa [Nat.mul_comm] using hprod
      have hbc : b = c := Nat.eq_of_mul_eq_mul_left ha hprod'
      exact Or.inr ⟨rfl, hbc⟩
  · have hab : a ≤ b := Nat.le_of_lt (Nat.lt_of_not_ge hba)
    by_cases hdc : d ≤ c
    · have hbc : b = c := by
        calc
          b = max a b := (max_eq_right hab).symm
          _ = max c d := hmax
          _ = c := max_eq_left hdc
      subst c
      -- Put the common maximum on the left before cancellation.
      have hprod' : b * a = b * d := by
        simpa [Nat.mul_comm] using hprod
      have had : a = d := Nat.eq_of_mul_eq_mul_left hb hprod'
      exact Or.inr ⟨had, rfl⟩
    · have hcd : c ≤ d := Nat.le_of_lt (Nat.lt_of_not_ge hdc)
      have hbd : b = d := by
        calc
          b = max a b := (max_eq_right hab).symm
          _ = max c d := hmax
          _ = d := max_eq_right hcd
      subst d
      -- Cancellation of the positive right maximum recovers the remaining entry.
      have hac : a = c := Nat.eq_of_mul_eq_mul_right hb hprod
      exact Or.inl ⟨hac, rfl⟩

/-- Exercise 69.3 (c): If two free products of finite cyclic groups are isomorphic, then
the cardinalities of their factors agree, possibly after interchanging the factors. -/
theorem cyclicFactorCards_eq_or_eq_swap
    {G₁ : Type u₁} {G₂ : Type u₂} {H₁ : Type v₁} {H₂ : Type v₂}
    [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    [Finite G₁] [Finite G₂] [Finite H₁] [Finite H₂]
    [IsCyclic G₁] [IsCyclic G₂] [IsCyclic H₁] [IsCyclic H₂]
    (e : G₁ ∗ G₂ ≃* H₁ ∗ H₂) :
    (Nat.card G₁ = Nat.card H₁ ∧ Nat.card G₂ = Nat.card H₂) ∨
      (Nat.card G₁ = Nat.card H₂ ∧ Nat.card G₂ = Nat.card H₁) := by
  -- Abelianization transports the product of the two factor cardinalities across `e`.
  have hprod : Nat.card G₁ * Nat.card G₂ = Nat.card H₁ * Nat.card H₂ := by
    calc
      Nat.card G₁ * Nat.card G₂ = Nat.card (Abelianization (G₁ ∗ G₂)) :=
        natCard_abelianization_eq_mul.symm
      _ = Nat.card (Abelianization (H₁ ∗ H₂)) :=
        Nat.card_congr e.abelianizationCongr.toEquiv
      _ = Nat.card H₁ * Nat.card H₂ := natCard_abelianization_eq_mul
  -- A maximal-order witness from the source gives one inequality between the maxima.
  obtain ⟨x, hx⟩ := exists_orderOf_eq_max_factor_card (G₁ := G₁) (G₂ := G₂)
  have hfin_x : IsOfFinOrder x := by
    rw [← orderOf_pos_iff, hx]
    exact (Nat.card_pos (α := G₁)).trans_le (le_max_left _ _)
  have hfin_ex : IsOfFinOrder (e x) := e.toMonoidHom.isOfFinOrder hfin_x
  have hmax_le : max (Nat.card G₁) (Nat.card G₂) ≤
      max (Nat.card H₁) (Nat.card H₂) := by
    calc
      max (Nat.card G₁) (Nat.card G₂) = orderOf x := hx.symm
      _ = orderOf (e x) := (e.orderOf_eq x).symm
      _ ≤ max (Nat.card H₁) (Nat.card H₂) :=
        orderOf_le_max_factor_card (e x) hfin_ex
  -- Applying the same witness argument to `e.symm` gives the reverse inequality.
  obtain ⟨y, hy⟩ := exists_orderOf_eq_max_factor_card (G₁ := H₁) (G₂ := H₂)
  have hfin_y : IsOfFinOrder y := by
    rw [← orderOf_pos_iff, hy]
    exact (Nat.card_pos (α := H₁)).trans_le (le_max_left _ _)
  have hfin_ey : IsOfFinOrder (e.symm y) := e.symm.toMonoidHom.isOfFinOrder hfin_y
  have hmax_ge : max (Nat.card H₁) (Nat.card H₂) ≤
      max (Nat.card G₁) (Nat.card G₂) := by
    calc
      max (Nat.card H₁) (Nat.card H₂) = orderOf y := hy.symm
      _ = orderOf (e.symm y) := (e.symm.orderOf_eq y).symm
      _ ≤ max (Nat.card G₁) (Nat.card G₂) :=
        orderOf_le_max_factor_card (e.symm y) hfin_ey
  have hmax : max (Nat.card G₁) (Nat.card G₂) =
      max (Nat.card H₁) (Nat.card H₂) := le_antisymm hmax_le hmax_ge
  -- Product and maximum determine a positive pair up to swapping.
  exact positiveNatPairEqOrEqSwap (Nat.card_pos (α := G₁)) (Nat.card_pos (α := G₂))
    (Nat.card_pos (α := H₁)) (Nat.card_pos (α := H₂)) hprod hmax

end Monoid.Coprod
