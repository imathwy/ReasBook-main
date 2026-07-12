import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_6_3.DirectSL2F4
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_6_3.Shared

noncomputable section

universe u

open CategoryTheory

namespace Representation

local notation "A5" => alternatingGroup (Fin 5)
local notation "𝔽₄" => FiniteField.Extension (ZMod 2) 2 2

/-- Helper for Exercise 18-18.6-3: theorem-local support package for the `χ₃,φ,ψ` branch. It
returns the descended simple degree-`2` slot.  The older character-row fields are intentionally
kept out of this owner because their stale import path currently collides with an earlier
Corollary 18.2.3 API copy. -/
theorem a5_source_degree_three_phi_owner_over_f4_support :
    ∃ E2 : FDRep 𝔽₄ A5,
      Simple E2 ∧ Module.finrank 𝔽₄ E2.V = 2 := by
  -- Route correction: the previous support statement mixed the source slot with Brauer-character
  -- row bookkeeping through a stale duplicated API.  The target-facing owner only needs the
  -- simple degree-`2` source constituent; the direct `A₅ ≃ SL₂(𝔽₄)` projective-line model now
  -- supplies that constituent without the stale character-row route.
  exact a5_natural_sl2_f4_source_slot

/-- Helper for Exercise 18-18.6-3: theorem-local support package for the `χ₃,ψ,φ` branch. After
the boundary is narrowed to existence of a simple degree-`2` slot, the same source slot witnesses
the companion branch as well. -/
theorem a5_source_degree_three_psi_owner_over_f4_support :
    ∃ E2 : FDRep 𝔽₄ A5,
      Simple E2 ∧ Module.finrank 𝔽₄ E2.V = 2 := by
  -- Route correction: the old wide statement tracked branch-specific Brauer-character rows.
  -- The narrowed target-facing statement only asks for one simple degree-`2` source slot, so the
  -- first branch supplies the same existential witness here.
  exact a5_source_degree_three_phi_owner_over_f4_support

end Representation
