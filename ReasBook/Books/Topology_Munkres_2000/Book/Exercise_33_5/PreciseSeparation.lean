module

public import Topology_Munkres_2000.Book.Definition_33_4.ZeroSet

public section

open Set

universe u

namespace ContinuousMap

variable {X : Type u} [TopologicalSpace X]

/-- A continuous map to the closed unit interval separates `A` and `B` precisely when
its zero fiber is `A` and its one fiber is `B`. -/
def SeparatesPrecisely (f : C(X, Icc (0 : ℝ) 1)) (A B : Set X) : Prop :=
  f.VanishesPreciselyOn A ∧ ∀ x, (f x : ℝ) = 1 ↔ x ∈ B

namespace SeparatesPrecisely

variable {f : C(X, Icc (0 : ℝ) 1)} {A B : Set X}

/-- Precise separation is equivalent to the endpoint and strict-interior conditions
appearing in the strong Urysohn lemma. -/
theorem iff_eqOn_and_mem_Ioo :
    f.SeparatesPrecisely A B ↔
      EqOn (fun x ↦ (f x : ℝ)) (fun _ ↦ 0) A ∧
        EqOn (fun x ↦ (f x : ℝ)) (fun _ ↦ 1) B ∧
          ∀ x, x ∉ A → x ∉ B → (f x : ℝ) ∈ Ioo 0 1 := by
  constructor
  · rintro ⟨hZero, hOne⟩
    have hZeroIff := (ContinuousMap.vanishesPreciselyOn_iff f A).1 hZero
    refine ⟨fun x hxA ↦ (hZeroIff x).2 hxA, fun x hxB ↦ (hOne x).2 hxB, ?_⟩
    intro x hxA hxB
    -- Exact endpoint fibers make both interval bounds strict away from `A` and `B`.
    have hPositive : 0 < (f x : ℝ) := (hZero.positive_iff_notMem x).2 hxA
    have hNeOne : (f x : ℝ) ≠ 1 := fun hfx ↦ hxB ((hOne x).1 hfx)
    exact ⟨hPositive, lt_of_le_of_ne (f x).property.2 hNeOne⟩
  · rintro ⟨hZero, hOne, hInterior⟩
    constructor
    · refine (ContinuousMap.vanishesPreciselyOn_iff f A).2 fun x ↦ ?_
      constructor
      · intro hfx
        by_contra hxA
        have hxB : x ∉ B := by
          intro hxB
          have hfxOne : (f x : ℝ) = 1 := hOne hxB
          linarith
        exact (ne_of_gt (hInterior x hxA hxB).1) hfx
      · intro hxA
        exact hZero hxA
    · intro x
      constructor
      · intro hfx
        by_contra hxB
        have hxA : x ∉ A := by
          intro hxA
          have hfxZero : (f x : ℝ) = 0 := hZero hxA
          linarith
        exact (ne_of_lt (hInterior x hxA hxB).2) hfx
      · intro hxB
        exact hOne hxB

/-- A map that separates `A` and `B` precisely vanishes precisely on `A`. -/
theorem vanishesPreciselyOn (h : f.SeparatesPrecisely A B) :
    f.VanishesPreciselyOn A := h.1

/-- The one fiber of a map that separates `A` and `B` precisely is `B`. -/
theorem oneSet_eq (h : f.SeparatesPrecisely A B) :
    {x | (f x : ℝ) = 1} = B := Set.ext fun x ↦ h.2 x

end SeparatesPrecisely

end ContinuousMap
