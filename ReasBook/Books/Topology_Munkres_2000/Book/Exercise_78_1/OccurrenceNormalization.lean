module

public import Topology_Munkres_2000.Book.Exercise_78_1.TriangularRegions

public section

namespace FourTrianglePasting

open LabellingScheme

/-- Helper for Exercise 78.1: the first occurrence in a four-word scheme. -/
noncomputable def fourConsOccurrenceZero {α : Type u}
    (w₀ w₁ w₂ w₃ : PolygonWord α) :
    Occurrence (w₀ ::ₘ w₁ ::ₘ w₂ ::ₘ w₃ ::ₘ 0) :=
  (consOccurrenceEquiv w₀ (w₁ ::ₘ w₂ ::ₘ w₃ ::ₘ 0)).symm none

/-- Helper for Exercise 78.1: the second occurrence in a four-word scheme. -/
noncomputable def fourConsOccurrenceOne {α : Type u}
    (w₀ w₁ w₂ w₃ : PolygonWord α) :
    Occurrence (w₀ ::ₘ w₁ ::ₘ w₂ ::ₘ w₃ ::ₘ 0) :=
  (consOccurrenceEquiv w₀ (w₁ ::ₘ w₂ ::ₘ w₃ ::ₘ 0)).symm
    (some ((consOccurrenceEquiv w₁ (w₂ ::ₘ w₃ ::ₘ 0)).symm none))

/-- Helper for Exercise 78.1: the third occurrence in a four-word scheme. -/
noncomputable def fourConsOccurrenceTwo {α : Type u}
    (w₀ w₁ w₂ w₃ : PolygonWord α) :
    Occurrence (w₀ ::ₘ w₁ ::ₘ w₂ ::ₘ w₃ ::ₘ 0) :=
  (consOccurrenceEquiv w₀ (w₁ ::ₘ w₂ ::ₘ w₃ ::ₘ 0)).symm
    (some ((consOccurrenceEquiv w₁ (w₂ ::ₘ w₃ ::ₘ 0)).symm
      (some ((consOccurrenceEquiv w₂ (w₃ ::ₘ 0)).symm none))))

/-- Helper for Exercise 78.1: the fourth occurrence in a four-word scheme. -/
noncomputable def fourConsOccurrenceThree {α : Type u}
    (w₀ w₁ w₂ w₃ : PolygonWord α) :
    Occurrence (w₀ ::ₘ w₁ ::ₘ w₂ ::ₘ w₃ ::ₘ 0) :=
  (consOccurrenceEquiv w₀ (w₁ ::ₘ w₂ ::ₘ w₃ ::ₘ 0)).symm
    (some ((consOccurrenceEquiv w₁ (w₂ ::ₘ w₃ ::ₘ 0)).symm
      (some ((consOccurrenceEquiv w₂ (w₃ ::ₘ 0)).symm
        (some ((consOccurrenceEquiv w₃ 0).symm none))))))

/-- Helper for Exercise 78.1: the four displayed occurrences exhaust a four-word scheme. -/
theorem fourConsOccurrence_cases {α : Type u} (w₀ w₁ w₂ w₃ : PolygonWord α)
    (region : Occurrence (w₀ ::ₘ w₁ ::ₘ w₂ ::ₘ w₃ ::ₘ 0)) :
    region = fourConsOccurrenceZero w₀ w₁ w₂ w₃ ∨
      region = fourConsOccurrenceOne w₀ w₁ w₂ w₃ ∨
      region = fourConsOccurrenceTwo w₀ w₁ w₂ w₃ ∨
      region = fourConsOccurrenceThree w₀ w₁ w₂ w₃ := by
  -- Peel off the four multiset cons cells, ruling out an occurrence of the empty remainder.
  cases h₀ : consOccurrenceEquiv w₀ (w₁ ::ₘ w₂ ::ₘ w₃ ::ₘ 0) region with
  | none =>
      left
      apply (consOccurrenceEquiv w₀ _).injective
      simpa [fourConsOccurrenceZero] using h₀
  | some region₁ =>
      cases h₁ : consOccurrenceEquiv w₁ (w₂ ::ₘ w₃ ::ₘ 0) region₁ with
      | none =>
          right
          left
          apply (consOccurrenceEquiv w₀ _).injective
          rw [h₀, fourConsOccurrenceOne, Equiv.apply_symm_apply]
          apply congrArg some
          calc
            region₁ = (consOccurrenceEquiv w₁ (w₂ ::ₘ w₃ ::ₘ 0)).symm
                ((consOccurrenceEquiv w₁ (w₂ ::ₘ w₃ ::ₘ 0)) region₁) :=
              ((consOccurrenceEquiv w₁ (w₂ ::ₘ w₃ ::ₘ 0)).symm_apply_apply region₁).symm
            _ = (consOccurrenceEquiv w₁ (w₂ ::ₘ w₃ ::ₘ 0)).symm none := congrArg _ h₁
      | some region₂ =>
          cases h₂ : consOccurrenceEquiv w₂ (w₃ ::ₘ 0) region₂ with
          | none =>
              right
              right
              left
              apply (consOccurrenceEquiv w₀ _).injective
              rw [h₀, fourConsOccurrenceTwo, Equiv.apply_symm_apply]
              apply congrArg some
              calc
                region₁ = (consOccurrenceEquiv w₁ (w₂ ::ₘ w₃ ::ₘ 0)).symm
                    ((consOccurrenceEquiv w₁ (w₂ ::ₘ w₃ ::ₘ 0)) region₁) :=
                  ((consOccurrenceEquiv w₁
                    (w₂ ::ₘ w₃ ::ₘ 0)).symm_apply_apply region₁).symm
                _ = (consOccurrenceEquiv w₁ (w₂ ::ₘ w₃ ::ₘ 0)).symm
                    (some region₂) := congrArg _ h₁
                _ = _ := by
                  apply congrArg (fun r ↦
                    (consOccurrenceEquiv w₁ (w₂ ::ₘ w₃ ::ₘ 0)).symm (some r))
                  calc
                    region₂ = (consOccurrenceEquiv w₂ (w₃ ::ₘ 0)).symm
                        ((consOccurrenceEquiv w₂ (w₃ ::ₘ 0)) region₂) :=
                      ((consOccurrenceEquiv w₂ (w₃ ::ₘ 0)).symm_apply_apply region₂).symm
                    _ = (consOccurrenceEquiv w₂ (w₃ ::ₘ 0)).symm none := congrArg _ h₂
          | some region₃ =>
              cases h₃ : consOccurrenceEquiv w₃ 0 region₃ with
              | none =>
                  right
                  right
                  right
                  apply (consOccurrenceEquiv w₀ _).injective
                  rw [h₀, fourConsOccurrenceThree, Equiv.apply_symm_apply]
                  apply congrArg some
                  calc
                    region₁ = (consOccurrenceEquiv w₁ (w₂ ::ₘ w₃ ::ₘ 0)).symm
                        ((consOccurrenceEquiv w₁ (w₂ ::ₘ w₃ ::ₘ 0)) region₁) :=
                      ((consOccurrenceEquiv w₁
                        (w₂ ::ₘ w₃ ::ₘ 0)).symm_apply_apply region₁).symm
                    _ = (consOccurrenceEquiv w₁ (w₂ ::ₘ w₃ ::ₘ 0)).symm
                        (some region₂) := congrArg _ h₁
                    _ = _ := by
                      apply congrArg (fun r ↦
                        (consOccurrenceEquiv w₁ (w₂ ::ₘ w₃ ::ₘ 0)).symm (some r))
                      calc
                        region₂ = (consOccurrenceEquiv w₂ (w₃ ::ₘ 0)).symm
                            ((consOccurrenceEquiv w₂ (w₃ ::ₘ 0)) region₂) :=
                          ((consOccurrenceEquiv w₂
                            (w₃ ::ₘ 0)).symm_apply_apply region₂).symm
                        _ = (consOccurrenceEquiv w₂ (w₃ ::ₘ 0)).symm
                            (some region₃) := congrArg _ h₂
                        _ = _ := by
                          apply congrArg (fun r ↦
                            (consOccurrenceEquiv w₂ (w₃ ::ₘ 0)).symm (some r))
                          calc
                            region₃ = (consOccurrenceEquiv w₃ 0).symm
                                ((consOccurrenceEquiv w₃ 0) region₃) :=
                              ((consOccurrenceEquiv w₃ 0).symm_apply_apply region₃).symm
                            _ = (consOccurrenceEquiv w₃ 0).symm none := congrArg _ h₃
              | some emptyRegion =>
                  exact (Nat.not_lt_zero emptyRegion.2 emptyRegion.2.isLt).elim

/-- Helper for Exercise 78.1: the first normalized occurrence carries the first word. -/
theorem fourConsOccurrenceZero_fst {α : Type u} (w₀ w₁ w₂ w₃ : PolygonWord α) :
    (fourConsOccurrenceZero w₀ w₁ w₂ w₃).1 = w₀ := by
  -- Compute the distinguished inverse image of the outer cons equivalence.
  unfold fourConsOccurrenceZero consOccurrenceEquiv Occurrence
  exact congrArg Sigma.fst
    (@Multiset.consEquiv_symm_none (PolygonWord α) (Classical.decEq _)
      (w₁ ::ₘ w₂ ::ₘ w₃ ::ₘ 0) w₀)

/-- Helper for Exercise 78.1: the second normalized occurrence carries the second word. -/
theorem fourConsOccurrenceOne_fst {α : Type u} (w₀ w₁ w₂ w₃ : PolygonWord α) :
    (fourConsOccurrenceOne w₀ w₁ w₂ w₃).1 = w₁ := by
  -- Pass through the outer cons and compute the distinguished point of the next cons.
  unfold fourConsOccurrenceOne consOccurrenceEquiv Occurrence
  rw [@Multiset.consEquiv_symm_some (PolygonWord α) (Classical.decEq _)
    (w₁ ::ₘ w₂ ::ₘ w₃ ::ₘ 0) w₀]
  exact congrArg Sigma.fst
    (@Multiset.consEquiv_symm_none (PolygonWord α) (Classical.decEq _)
      (w₂ ::ₘ w₃ ::ₘ 0) w₁)

/-- Helper for Exercise 78.1: the third normalized occurrence carries the third word. -/
theorem fourConsOccurrenceTwo_fst {α : Type u} (w₀ w₁ w₂ w₃ : PolygonWord α) :
    (fourConsOccurrenceTwo w₀ w₁ w₂ w₃).1 = w₂ := by
  -- Pass through two outer cons cells and compute the next distinguished point.
  unfold fourConsOccurrenceTwo consOccurrenceEquiv Occurrence
  rw [@Multiset.consEquiv_symm_some (PolygonWord α) (Classical.decEq _)
      (w₁ ::ₘ w₂ ::ₘ w₃ ::ₘ 0) w₀,
    @Multiset.consEquiv_symm_some (PolygonWord α) (Classical.decEq _)
      (w₂ ::ₘ w₃ ::ₘ 0) w₁]
  exact congrArg Sigma.fst
    (@Multiset.consEquiv_symm_none (PolygonWord α) (Classical.decEq _) (w₃ ::ₘ 0) w₂)

/-- Helper for Exercise 78.1: the fourth normalized occurrence carries the fourth word. -/
theorem fourConsOccurrenceThree_fst {α : Type u} (w₀ w₁ w₂ w₃ : PolygonWord α) :
    (fourConsOccurrenceThree w₀ w₁ w₂ w₃).1 = w₃ := by
  -- Pass through three outer cons cells and compute the final distinguished point.
  unfold fourConsOccurrenceThree consOccurrenceEquiv Occurrence
  rw [@Multiset.consEquiv_symm_some (PolygonWord α) (Classical.decEq _)
      (w₁ ::ₘ w₂ ::ₘ w₃ ::ₘ 0) w₀,
    @Multiset.consEquiv_symm_some (PolygonWord α) (Classical.decEq _)
      (w₂ ::ₘ w₃ ::ₘ 0) w₁,
    @Multiset.consEquiv_symm_some (PolygonWord α) (Classical.decEq _)
      (w₃ ::ₘ 0) w₂]
  exact congrArg Sigma.fst
    (@Multiset.consEquiv_symm_none (PolygonWord α) (Classical.decEq _) 0 w₃)

end FourTrianglePasting
