import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open PrimeSpectrum
open Topology

section

variable {R : Type u} [CommSemiring R]

/- Lemma 10.29.3: a subset of `Spec(R)` is constructible if and only if it is a finite union of
subsets of the form `D(f) ∩ V(g₁, …, gₘ)`.

The canonical mathlib formulation is `PrimeSpectrum.exists_constructibleSetData_iff`: a
constructible subset is exactly a set represented by `PrimeSpectrum.ConstructibleSetData R`, where
each basic piece is packaged as `V(g₁, …, gₘ) \ V(f) = D(f) ∩ V(g₁, …, gₘ)`. -/
recall PrimeSpectrum.exists_constructibleSetData_iff

private noncomputable def pairToBasicConstructibleSetData (a : R × Finset R) :
    BasicConstructibleSetData R where
  f := a.1
  n := a.2.card
  g := fun i ↦ ((Finset.equivFin a.2).symm i).1

omit [CommSemiring R] in
private theorem range_pairToBasicConstructibleSetData
    (a : R × Finset R) :
    Set.range (pairToBasicConstructibleSetData a).g = (a.2 : Set R) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ((Finset.equivFin a.2).symm i).2
  · intro hx
    refine ⟨Finset.equivFin a.2 ⟨x, hx⟩, ?_⟩
    simp [pairToBasicConstructibleSetData]

private theorem pairToBasicConstructibleSetData_toSet
    (a : R × Finset R) :
    (pairToBasicConstructibleSetData a).toSet =
      ((basicOpen a.1 : Set (PrimeSpectrum R)) ∩ zeroLocus (a.2 : Set R)) := by
  rw [BasicConstructibleSetData.toSet, range_pairToBasicConstructibleSetData,
    Set.diff_eq_compl_inter, basicOpen_eq_zeroLocus_compl]
  simp [pairToBasicConstructibleSetData, Set.inter_comm]

/-- Textbook finset reformulation of Lemma 10.29.3: a subset of `Spec(R)` is constructible if and
only if it is a finite union of subsets of the form `D(f) ∩ V(G)` with `f ∈ R` and `G ⊆ R`
finite. This is the finite-set form of the textbook description `D(f) ∩ V(g₁, …, gₘ)`. -/
-- Proof sketch: unpack `PrimeSpectrum.exists_constructibleSetData_iff`, convert between a finite
-- family `g : Fin n → R` and the corresponding finite set of generators, and use
-- `PrimeSpectrum.basicOpen_eq_zeroLocus_compl` to identify `V(G) \ V(f)` with `D(f) ∩ V(G)`.
theorem isConstructible_iff_exists_finset_union_basicOpen_inter_zeroLocus
    {T : Set (PrimeSpectrum R)} :
    IsConstructible T ↔
      ∃ s : Finset (R × Finset R),
        T = ⋃ a ∈ s,
          ((basicOpen a.1 : Set (PrimeSpectrum R)) ∩ zeroLocus (a.2 : Set R)) := by
  classical
  constructor
  · intro hT
    obtain ⟨S, rfl⟩ := exists_constructibleSetData_iff.mpr hT
    refine ⟨S.image fun C ↦ (C.f, (Set.finite_range C.g).toFinset), ?_⟩
    rw [ConstructibleSetData.toSet, Finset.set_biUnion_finset_image]
    congr! with C hC
    rw [BasicConstructibleSetData.toSet, Set.diff_eq_compl_inter, basicOpen_eq_zeroLocus_compl,
      Set.Finite.coe_toFinset (Set.finite_range C.g)]
  · rintro ⟨s, rfl⟩
    apply exists_constructibleSetData_iff.mp
    refine ⟨s.image pairToBasicConstructibleSetData, ?_⟩
    rw [ConstructibleSetData.toSet, Finset.set_biUnion_finset_image]
    congr! with a ha
    exact pairToBasicConstructibleSetData_toSet a

end
