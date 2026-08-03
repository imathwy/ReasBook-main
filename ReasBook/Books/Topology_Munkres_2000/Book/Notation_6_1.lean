module

public import Topology_Munkres_2000.Book.Notation_4_2.Sections

public section

/- Notation 6.1. For a positive integer `n : ℕ+`, the section `Sₙ` of the
positive integers is the set of positive integers less than `n`; these sections
are the prototypes for finite sets. -/
#check fun n : ℕ+ ↦ (S_{n} : Set ℕ+)

end
