module

public import Topology_Munkres_2000.Book.Exercise_9_2.Selection
import Mathlib.Data.Rat.Encodable
import Mathlib.SetTheory.Cardinal.Order

public section

/-- Object-level answer for Exercise 9.2 (1): a choice function for all nonempty subsets of the
positive integers, obtained by selecting an element with least encoding. This declaration
does not express the source's proof-theoretic requirement that the choice axiom not be used. -/
noncomputable def positiveNatSetChoice : SetChoice ℕ+ :=
  SetChoice.ofEncodable

/-- Membership property for Exercise 9.2 (1): the positive-integer choice function selects
an element of the supplied nonempty set. -/
theorem positiveNatSetChoice_mem (s : Set ℕ+) (hs : s.Nonempty) :
    positiveNatSetChoice s hs ∈ s :=
  SetChoice.mem positiveNatSetChoice s hs

/-- Object-level answer for Exercise 9.2 (2): a choice function for all nonempty subsets of the
integers, obtained by selecting an element with least encoding. This declaration does not
express the source's proof-theoretic requirement that the choice axiom not be used. -/
noncomputable def intSetChoice : SetChoice ℤ :=
  SetChoice.ofEncodable

/-- Membership property for Exercise 9.2 (2): the integer choice function selects an element
of the supplied nonempty set. -/
theorem intSetChoice_mem (s : Set ℤ) (hs : s.Nonempty) : intSetChoice s hs ∈ s :=
  SetChoice.mem intSetChoice s hs

/-- Object-level answer for Exercise 9.2 (3): a choice function for all nonempty subsets of the
rational numbers, obtained by selecting an element with least encoding. This declaration
does not express the source's proof-theoretic requirement that the choice axiom not be used. -/
noncomputable def ratSetChoice : SetChoice ℚ :=
  SetChoice.ofEncodable

/-- Membership property for Exercise 9.2 (3): the rational choice function selects an element
of the supplied nonempty set. -/
theorem ratSetChoice_mem (s : Set ℚ) (hs : s.Nonempty) : ratSetChoice s hs ∈ s :=
  SetChoice.mem ratSetChoice s hs

/-- Exercise 9.2 (4): The existence of a choice function for all nonempty subsets of
binary sequences is equivalent to the well-orderability of the type of binary sequences.
This characterizes the extra principle needed for this clause rather than presenting the
conditional well-order construction below as a choice-free answer. -/
theorem binarySequenceSetChoice_nonempty_iff_wellOrderable :
    Nonempty (SetChoice (ℕ → Fin 2)) ↔
      ∃ r : (ℕ → Fin 2) → (ℕ → Fin 2) → Prop, IsWellOrder (ℕ → Fin 2) r := by
  constructor
  · intro _
    -- The canonical relation witnesses well-orderability independently of the selector.
    refine ⟨WellOrderingRel, ?_⟩
    infer_instance
  · intro h
    obtain ⟨r, hr⟩ := h
    -- Regard the supplied well-order as an instance, then select the least member of each set.
    letI : IsWellOrder (ℕ → Fin 2) r := hr
    exact ⟨SetChoice.ofWellFounded r⟩

/-- Conditional bridge for Exercise 9.2 (4): an explicitly supplied well-order of `ℕ → Fin 2`
yields a choice function on its nonempty subsets. This does not determine whether such a choice
function can be constructed without the set-theoretic axiom of choice. -/
noncomputable def binarySequenceSetChoiceFromWellOrder
    (r : (ℕ → Fin 2) → (ℕ → Fin 2) → Prop) [IsWellOrder (ℕ → Fin 2) r] :
    SetChoice (ℕ → Fin 2) :=
  SetChoice.ofWellFounded r

/-- Membership property for Exercise 9.2 (4): the conditional binary-sequence choice function
selects an element of the supplied nonempty set. -/
theorem binarySequenceSetChoiceFromWellOrder_mem
    (r : (ℕ → Fin 2) → (ℕ → Fin 2) → Prop) [IsWellOrder (ℕ → Fin 2) r]
    (s : Set (ℕ → Fin 2)) (hs : s.Nonempty) :
    binarySequenceSetChoiceFromWellOrder r s hs ∈ s :=
  SetChoice.mem (binarySequenceSetChoiceFromWellOrder r) s hs
