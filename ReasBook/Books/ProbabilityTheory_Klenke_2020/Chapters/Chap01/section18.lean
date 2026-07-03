import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_1_18 (from Items/Chap01) -/
open Set MeasureTheory

universe u

variable {Ω : Type u}

-- Proof sketch: If `d` comes from a measurable space, its measurable sets are closed under binary
-- intersections. Conversely, binary intersection closure lets one form the measurable space
-- `d.toMeasurableSpace`, and `ofMeasurableSpace_toMeasurableSpace` identifies the resulting
-- Dynkin system with `d`.
/-- Theorem 1.18: A Dynkin system on `Ω` is a `π`-system in the textbook sense, i.e. it is closed
under binary intersections, if and only if it is the family of measurable sets of some measurable
space on `Ω`. -/
theorem dynkinSystem_interClosed_iff_exists_measurableSpace
    (d : MeasurableSpace.DynkinSystem Ω) :
    (∀ s : Set Ω, d.Has s → ∀ t : Set Ω, d.Has t → d.Has (s ∩ t)) ↔
      ∃ m : MeasurableSpace Ω, d = MeasurableSpace.DynkinSystem.ofMeasurableSpace m := by
  constructor
  · intro h_inter
    -- Repackage the hypothesis into the binder order used by `DynkinSystem.toMeasurableSpace`.
    have h_inter' : ∀ s t : Set Ω, d.Has s → d.Has t → d.Has (s ∩ t) :=
      fun s t hs ht => h_inter s hs t ht
    -- Use the binary-intersection closure to bundle `d` into a measurable space.
    refine ⟨d.toMeasurableSpace h_inter', ?_⟩
    -- The associated Dynkin system recovers exactly the original one.
    symm
    exact MeasurableSpace.DynkinSystem.ofMeasurableSpace_toMeasurableSpace (d := d) h_inter'
  · rintro ⟨m, rfl⟩ s hs t ht
    -- After rewriting to measurable sets of `m`, closure under intersection is standard.
    simpa using MeasurableSet.inter hs ht
