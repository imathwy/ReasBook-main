import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap01.Example_1_11

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set

variable {E : Type u}

-- Proof sketch: view `E^ℕ` with the product topology of the discrete finite space `E`; the
-- initial cylinders are clopen and hence compact. A countable open cover of a compact cylinder
-- therefore has a finite subcover.
/-- Example 1.63: If a cylinder set in `E^ℕ` is covered by countably many cylinder sets and `E` is
finite, then finitely many members of the cover already cover it. This is the compactness statement
used to verify (1.13) in the construction of the infinite product content. -/
theorem initialSequenceCylinder_finite_subcover_of_subset_iUnion [Finite E]
    {A : Set (ℕ → E)} (hA : A ∈ sequenceCylinderFamily E) (cover : ℕ → Set (ℕ → E))
    (hcover_mem : ∀ n, cover n ∈ sequenceCylinderFamily E) (hcover : A ⊆ ⋃ n, cover n) :
    ∃ s : Finset ℕ, A ⊆ ⋃ n ∈ s, cover n := sorry
