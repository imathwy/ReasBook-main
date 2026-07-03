import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_6_3.Shared
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_6_3.SourceCharacters

noncomputable section

universe u

namespace Representation

local notation "A5" => alternatingGroup (Fin 5)
local notation "𝔽₄" => FiniteField.Extension (ZMod 2) 2 2

/-
This support file is reserved for the long source-faithful owner lemmas that must construct the
two actual degree-`3` `𝔽₄[A₅]` reductions of LinearRepresentations_Serre_1977's ordinary `χ₃` rows. Rescue mode keeps those
lemmas out of the target file so the main theorem can import them later without reintroducing the
stale duplicate theorem from `Chi3Reduction.lean`.
-/

end Representation
