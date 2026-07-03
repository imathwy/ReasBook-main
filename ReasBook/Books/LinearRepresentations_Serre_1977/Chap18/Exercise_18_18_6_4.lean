import Mathlib
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_6_4.ProjectiveLinearGroupCardinality
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_6_4.ExplicitGeneratorsAndRegularClasses
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_6_4.ExplicitWordTransportData
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_6_4.ExplicitWordTransportHom
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_6_4.ExplicitExceptionalIsomorphism

noncomputable section

open CategoryTheory
open Representation
open scoped MatrixGroups

local notation "A5" => alternatingGroup (Fin 5)

/-- Exercise 18-18.6-4 (1): the alternating group `A₅` is isomorphic to LinearRepresentations_Serre_1977's quotient
`SL₂(𝔽₅) / {±1}`, expressed canonically as the projective special linear group
`PSL(2, ZMod 5)`. -/
theorem alternatingGroup_fin5_isomorphic_to_PSL_two_zmod_five :
    Nonempty (A5 ≃* PSL(2, ZMod 5)) := by
  -- The explicit finite transport table already encodes a multiplicative bijection.
  exact
    ⟨MulEquiv.ofBijective
      alternating_group_fin5_to_psl_hom
      alternating_group_fin5_to_psl_lookup_bijective⟩

/-- Exercise 18-18.6-4 (2): over an algebraically closed field of characteristic `5`, the
finite-dimensional irreducible representations of `A₅` are exhausted, up to isomorphism, by a
`Fin 3`-indexed complete irreducible family whose members have dimensions `1`, `3`, and `5`. -/
theorem exists_alternatingGroup_fin5_modFive_irreducible_family
    {k : Type} [Field k] [IsAlgClosed k] [CharP k 5] :
    ∃ π : Fin 3 → FDRep k A5,
      IsCompleteIrreducibleFamily π ∧
        Module.finrank k (π 0).V = 1 ∧
        Module.finrank k (π 1).V = 3 ∧
        Module.finrank k (π 2).V = 5 := by
  admit
