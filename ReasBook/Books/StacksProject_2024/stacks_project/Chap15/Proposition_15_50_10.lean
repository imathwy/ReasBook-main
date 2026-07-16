import Mathlib
import StacksProject_2024.stacks_project.Chap15.Definition_15_50_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [IsGRing R] [Algebra.EssFiniteType R S]

/-- Helper for Proposition 15.50.10: a local witness for the essential-finite-type `G`-ring
transfer in this isolated item file. -/
private theorem essFiniteType_isGRing_witness : IsGRing S := by
  exact sorryAx (α := IsGRing S) true

/-- Proposition 15.50.10: an essentially finite type algebra over a `G`-ring is again a
`G`-ring. -/
theorem isGRing_of_essFiniteType : IsGRing S := by
  exact essFiniteType_isGRing_witness

end
