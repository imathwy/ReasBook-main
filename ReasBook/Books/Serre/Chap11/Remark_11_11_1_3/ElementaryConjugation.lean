import Mathlib
import Serre.Chap10.Definition_10_10_1_3
import Serre.Chap10.Exercise_10_10_5_5
import Serre.Chap12.Proposition_12_12_1_1

-- Stable elementary-subgroup conjugation infrastructure extracted from Remark 11-11.1-3.

noncomputable section

namespace Representation

section CharacterizationOfCharacters

open scoped Pointwise Representation TensorProduct

variable {G : Type} [Group G] [Finite G]

local notation:max s " •ᶜ " H => (MulAut.conj s • H : Subgroup G)

/-- Helper for Remark 11-11.1-3: the family of elementary subgroups is stable under conjugation.
-/
theorem elementary_mem_of_conj
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    {H : Subgroup G} (hH : H ∈ X) (s : G) :
    (s •ᶜ H) ∈ X := by
  rw [hXelem]
  exact isElementary_of_mulEquiv ((MulAut.conj s).subgroupMap H) ((hXelem H).1 hH)

end CharacterizationOfCharacters

end Representation
