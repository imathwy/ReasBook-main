import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_6_3.Index

open scoped MatrixGroups

noncomputable section

universe u v

open Representation

local notation "A5" => alternatingGroup (Fin 5)
local notation "𝔽₄" => FiniteField.Extension (ZMod 2) 2 2

/-- Exercise 18-18.6-3: the rank-one `SL₂(𝔽₄)` realizability frontier that drives
the characteristic-`2` descent for the alternating group. -/
theorem Representation.sl2F4_irreducible_degreeTwo_realizableOver_f4 :
    ∀ {K : Type u} [Field K] [Algebra 𝔽₄ K]
      {V : Type v} [AddCommGroup V] [Module K V]
      (σ : Representation K (SL(2, 𝔽₄)) V) [σ.IsIrreducible],
      Module.finrank K V = 2 → Representation.IsRealizableOver 𝔽₄ σ := by
  -- The target file owns the textbook declaration; the long rank-one proof lives in the local
  -- support module under a core helper name to keep imports acyclic.
  exact Representation.sl2F4_irreducible_degreeTwo_realizableOver_f4_core

/-- Every irreducible two-dimensional representation of `A₅` in characteristic `2` over an
extension field of `𝔽₄` is realizable over `𝔽₄`. -/
theorem alternatingGroup_fin5_irreducible_degree_two_mod_two_realizable_over_f4
    {K : Type u} [Field K] [Algebra 𝔽₄ K]
    {V : Type v} [AddCommGroup V] [Module K V]
    (ρ : Representation K A5 V) [ρ.IsIrreducible] (hV : Module.finrank K V = 2) :
    IsRealizableOver 𝔽₄ ρ := by
  -- The textbook realizability clause is exactly the second half of the local source package.
  exact Representation.a5_irreducible_degree_two_realizable_over_f4 ρ hV

/-- The alternating group `A₅` is isomorphic to the special linear group `SL(2, 𝔽₄)`. -/
theorem alternatingGroup_fin5_isomorphic_to_sl2_f4 :
    Nonempty (A5 ≃* SL(2, 𝔽₄)) := by
  -- Once one irreducible degree-`2` source model over `𝔽₄` is available, the remaining argument
  -- is the kernel-and-order comparison already isolated above.
  exact alternatingGroup_fin5_mulEquiv_sl2_f4_of_source_witness
    Representation.a5_degree_two_source_slot_exists_over_f4
