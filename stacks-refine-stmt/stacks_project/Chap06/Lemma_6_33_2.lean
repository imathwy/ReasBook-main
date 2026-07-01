import stacks_project.Chap06.Glueing_data_for_sheaves_on_an_open_cover

open TopCat TopologicalSpace
open TopologicalSpace.Opens

noncomputable section

universe u v

section

variable {X : TopCat.{u}} {ι : Type v} {U : ι → Opens X}

-- Proof sketch: define sections on an open `W ⊆ X` as compatible families of local sections on
-- the intersections `W ∩ U i`; the sheaf condition and the cocycle condition on the local gluing
-- datum show that these sections form a sheaf whose restriction to each `U i` recovers the given
-- local sheaf.
/-- Lemma 6.33.2: every gluing datum of sheaves of sets on an open cover is realized by a sheaf on
the ambient space. -/
theorem exists_sheaf_realizing_open_cover_glueing
    (data : SheafOpenCoverGlueing U) :
    ∃ F : X.Sheaf (Type u), data.Realizes F := by
  sorry

end
