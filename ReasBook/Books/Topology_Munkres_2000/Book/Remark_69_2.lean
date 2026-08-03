module

public import Mathlib.GroupTheory.FreeGroup.«Reduce»

public section

universe u

namespace FreeGroup

/-- Remark 69.2. Every element of a free group has a unique reduced-word
representative. For a generator map `a : J → G`, an element of
`(FreeGroup.lift a).ker` may therefore be called a relation either as a kernel
element or as its reduced word. -/
theorem existsUnique_reducedWord {J : Type u} (x : FreeGroup J) :
    ∃! w : List (J × Bool), IsReduced w ∧ mk w = x := by
  classical
  refine ⟨x.toWord, ⟨isReduced_toWord, mk_toWord⟩, ?_⟩
  rintro w ⟨hw, rfl⟩
  calc
    w = reduce w := hw.reduce_eq.symm
    _ = (mk w).toWord := toWord_mk.symm

end FreeGroup
