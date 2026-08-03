module

public import Topology_Munkres_2000.Book.Notation_4_2.Sections

public section

/-- Theorem 4.2 (Strong induction principle). If a set of positive integers
contains each positive integer whenever it contains every smaller one, then it
is the set of all positive integers. -/
theorem strongInductionPrinciple
    (A : Set ℕ+)
    (hA : ∀ n : ℕ+, S_{n} ⊆ A → n ∈ A) :
    A = Set.univ := by
  apply Set.ext
  intro n
  constructor
  · intro
    trivial
  · intro
    exact PNat.strongInductionOn n fun k ih ↦ hA k fun m hm ↦ ih m hm

end
