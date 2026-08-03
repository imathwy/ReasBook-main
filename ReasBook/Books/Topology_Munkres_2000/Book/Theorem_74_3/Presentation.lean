module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.PresentedGroup

public section

open scoped commutatorElement

namespace OrientableSurfaceGroup

/-- The ordered product of the commutators of the paired generators indexed by
`Fin n × Bool`, where `(i, false)` represents `αᵢ` and `(i, true)` represents `βᵢ`. -/
@[expose] def relator (n : ℕ) : FreeGroup (Fin n × Bool) :=
  (List.ofFn fun i : Fin n ↦
    ⁅FreeGroup.of (i, false), FreeGroup.of (i, true)⁆).prod

/-- The genus-`n` surface group presented by the single relation `relator n = 1`. -/
abbrev Presentation (n : ℕ) : Type :=
  PresentedGroup ({relator n} : Set (FreeGroup (Fin n × Bool)))

/-- The generator `αᵢ` of the genus-`n` surface group. -/
@[expose] def alpha (n : ℕ) (i : Fin n) : Presentation n :=
  PresentedGroup.of (i, false)

/-- The generator `βᵢ` of the genus-`n` surface group. -/
@[expose] def beta (n : ℕ) (i : Fin n) : Presentation n :=
  PresentedGroup.of (i, true)

/-- The relator is the ordered product of the commutators of the paired generators. -/
theorem relator_def (n : ℕ) :
    relator n = (List.ofFn fun i : Fin n ↦
      ⁅FreeGroup.of (i, false), FreeGroup.of (i, true)⁆).prod := rfl

/-- The generator `αᵢ` is the canonical image of `(i, false)`. -/
theorem alpha_def (n : ℕ) (i : Fin n) :
    alpha n i = PresentedGroup.of (i, false) := rfl

/-- The generator `βᵢ` is the canonical image of `(i, true)`. -/
theorem beta_def (n : ℕ) (i : Fin n) :
    beta n i = PresentedGroup.of (i, true) := rfl

/-- The canonical generators satisfy the ordered product-of-commutators relation. -/
theorem relation (n : ℕ) :
    (List.ofFn fun i : Fin n ↦ ⁅alpha n i, beta n i⁆).prod = 1 := sorry

end OrientableSurfaceGroup
