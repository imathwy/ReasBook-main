import Mathlib

noncomputable section

section Exercise131317JenningsObstruction

variable {p : ℕ}
variable {A B : Type*} [Ring A] [Ring B]
variable [Algebra (ZMod p) A] [Algebra (ZMod p) B]

/-- Helper for Exercise 13-13.1-17: an algebra equivalence preserves membership in the Jacobson
radical. This isolates the first transport step needed for the later Jennings-layer obstruction. -/
theorem mem_jacobson_iff_of_algEquiv
    (e : A ≃ₐ[ZMod p] B) {x : A} :
    x ∈ Ring.jacobson A ↔ e x ∈ Ring.jacobson B := by
  letI : RingHomSurjective (e : A →+* B) := ⟨e.surjective⟩
  letI : RingHomSurjective (e.symm : B →+* A) := ⟨e.symm.surjective⟩
  constructor
  · intro hx
    -- Map the source Jacobson class forward, then use the general `map_jacobson_le` inclusion.
    have hxmap : e x ∈ Submodule.map (e : A →+* B).toSemilinearMap (Ring.jacobson A) :=
      ⟨x, hx, rfl⟩
    exact (Ring.map_jacobson_le (f := (e : A →+* B))) hxmap
  · intro hx
    -- Apply the same argument to the inverse equivalence to pull the class back.
    have hxmap : x ∈ Submodule.map (e.symm : B →+* A).toSemilinearMap (Ring.jacobson B) := by
      refine ⟨e x, hx, ?_⟩
      simp
    exact (Ring.map_jacobson_le (f := (e.symm : B →+* A))) hxmap

/-- Helper for Exercise 13-13.1-17: an algebra equivalence preserves the basic `p`-th-power
Jacobian test `x^p ∈ J`. This is the transport-stable core of the later Jennings obstruction. -/
theorem jennings_pth_power_class_preserved_of_algEquiv
    (e : A ≃ₐ[ZMod p] B) (x : A) :
    x ^ p ∈ Ring.jacobson A ↔ e x ^ p ∈ Ring.jacobson B := by
  -- Route correction: isolate the first Jacobson-transport step before introducing the higher
  -- quotient layers `J / J²` and `J^p / J^(p+1)`.
  simpa [map_pow] using
    (mem_jacobson_iff_of_algEquiv (p := p) e (x := x ^ p))

end Exercise131317JenningsObstruction
