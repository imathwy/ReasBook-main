import Mathlib
import StacksProject_2024.Chap10.Lemma_10_17_2

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial PrimeSpectrum

universe u

section

variable {R : Type u} [CommRing R]

/-- Canonical complement-of-zero-locus form of Lemma 10.29.9: if `f, g : R[X]` and the leading
coefficient of `g` is a unit, then the image of `D(f) ∩ V(g)` in `Spec(R)` under the structure
morphism `Spec(R[X]) → Spec(R)` is a compact open of the canonical form `(V(t))ᶜ`. This is the
`isUnit`-leading-coefficient variant of `Polynomial.exists_image_comap_of_monic`. -/
theorem exists_image_basicOpen_inter_zeroLocus_eq_zeroLocus_compl_of_isUnit_leadingCoeff
    (f g : R[X]) (hg : IsUnit g.leadingCoeff) :
    ∃ t : Finset R,
      comap C '' ((basicOpen f : Set (PrimeSpectrum R[X])) ∩ zeroLocus ({g} : Set R[X])) =
        (zeroLocus t : Set (PrimeSpectrum R))ᶜ := by
  let g' : R[X] := hg.unit⁻¹ • g
  have hg' : g'.Monic := by
    simpa [g'] using monic_of_isUnit_leadingCoeff_inv_smul hg
  have hg'_eq : g' = C (↑(hg.unit⁻¹) : R) * g := by
    ext i
    simp [g', coeff_C_mul, Units.smul_def]
  have hzero :
      (zeroLocus ({g'} : Set R[X]) : Set (PrimeSpectrum R[X])) = zeroLocus ({g} : Set R[X]) := by
    rw [hg'_eq, ← zeroLocus_span ({C (↑(hg.unit⁻¹) : R) * g} : Set R[X]),
      ← zeroLocus_span ({g} : Set R[X]),
      Ideal.span_singleton_mul_left_unit (isUnit_C.mpr (Units.isUnit _))]
  obtain ⟨t, ht⟩ := exists_image_comap_of_monic f g' hg'
  refine ⟨t, ?_⟩
  calc
    comap C '' ((basicOpen f : Set (PrimeSpectrum R[X])) ∩ zeroLocus ({g} : Set R[X]))
        = comap C '' (zeroLocus ({g'} : Set R[X]) \ zeroLocus ({f} : Set R[X])) := by
            congr 1
            ext x
            rw [hzero]
            constructor <;> intro h <;>
              simpa [basicOpen_eq_zeroLocus_compl, Set.diff_eq, and_comm] using h
    _ = (zeroLocus t : Set (PrimeSpectrum R))ᶜ := ht

/-- If `f, g : R[X]` and the leading coefficient of `g` is a unit, then the image of
`D(f) ∩ V(g)` in `Spec(R)` under the structure morphism `Spec(R[X]) → Spec(R)` is compact open. -/
theorem isCompact_isOpen_image_basicOpen_inter_zeroLocus_of_isUnit_leadingCoeff
    (f g : R[X]) (hg : IsUnit g.leadingCoeff) :
    IsCompact (comap C '' ((basicOpen f : Set (PrimeSpectrum R[X])) ∩ zeroLocus ({g} : Set R[X]))) ∧
      IsOpen (comap C '' ((basicOpen f : Set (PrimeSpectrum R[X])) ∩ zeroLocus ({g} : Set R[X]))) := by
  let U : Set (PrimeSpectrum R) :=
    comap C '' ((basicOpen f : Set (PrimeSpectrum R[X])) ∩ zeroLocus ({g} : Set R[X]))
  obtain ⟨t, ht⟩ := exists_image_basicOpen_inter_zeroLocus_eq_zeroLocus_compl_of_isUnit_leadingCoeff
    f g hg
  change IsCompact U ∧ IsOpen U
  exact
    (PrimeSpectrum.isCompact_isOpen_iff :
      IsCompact U ∧ IsOpen U ↔
        ∃ s : Finset R, (zeroLocus s : Set (PrimeSpectrum R))ᶜ = U).mpr
      ⟨t, by simpa [U] using ht.symm⟩

/-- Lemma 10.29.9: if `f, g : R[X]` and the leading coefficient of `g` is a unit, then the image
of `D(f) ∩ V(g)` in `Spec(R)` under the structure morphism `Spec(R[X]) → Spec(R)` is a finite
union of basic opens. -/
@[stacks 00FD]
theorem exists_finite_basicOpen_cover_image_basicOpen_inter_zeroLocus_of_isUnit_leadingCoeff
    (f g : R[X]) (hg : IsUnit g.leadingCoeff) :
    ∃ t : Finset R,
      comap C '' ((basicOpen f : Set (PrimeSpectrum R[X])) ∩ zeroLocus ({g} : Set R[X])) =
        ⋃ r ∈ t, (basicOpen r : Set (PrimeSpectrum R)) := by
  obtain ⟨t, ht⟩ := exists_image_basicOpen_inter_zeroLocus_eq_zeroLocus_compl_of_isUnit_leadingCoeff
    f g hg
  refine ⟨t, ht.trans ?_⟩
  ext p
  simp [basicOpen_eq_zeroLocus_compl, Set.not_subset]

end
