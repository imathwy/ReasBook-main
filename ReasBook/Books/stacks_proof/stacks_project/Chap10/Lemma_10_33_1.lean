import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

open PrimeSpectrum

variable {R : Type u} [CommRing R] (S : Submonoid R)

-- Semantic search tool unavailable in this environment; local API checks used
-- `PrimeSpectrum.comap`, `PrimeSpectrum.localization_comap_range`, and nearby quotient/localization
-- precedent in `Lemma_10_33_2` and `Definition_10_54_1`.

/-- Helper for Lemma 10.33.1: the closed image hypothesis identifies the image of
`Spec(S⁻¹R) → Spec(R)` with the zero locus of the kernel of the localization map. -/
lemma range_comap_eq_zeroLocus_kernel_of_isClosed
    (hclosed : IsClosed (Set.range (PrimeSpectrum.comap (algebraMap R (Localization S))))) :
    Set.range (PrimeSpectrum.comap (algebraMap R (Localization S))) =
      PrimeSpectrum.zeroLocus (RingHom.ker (algebraMap R (Localization S))) := by
  -- The closed image already equals its closure, and the closure is the zero locus of the kernel.
  simpa [hclosed.closure_eq] using
    (PrimeSpectrum.closure_range_comap (f := algebraMap R (Localization S)))

/-- Helper for Lemma 10.33.1: every element of the multiplicative set becomes a unit in the
quotient by the kernel of the localization map. -/
lemma isUnit_quotient_mk_of_mem_submonoid
    (hzero : Set.range (PrimeSpectrum.comap (algebraMap R (Localization S))) =
      PrimeSpectrum.zeroLocus (RingHom.ker (algebraMap R (Localization S)))) (s : S) :
    IsUnit (Ideal.Quotient.mk (RingHom.ker (algebraMap R (Localization S))) s) := by
  let I : Ideal R := RingHom.ker (algebraMap R (Localization S))
  let q : R →+* R ⧸ I := Ideal.Quotient.mk I
  by_contra hs
  -- A nonunit in the quotient lies in some maximal ideal of the quotient ring.
  have hs_nonunit : q s ∈ nonunits (R ⧸ I) := by
    exact mem_nonunits_iff.mpr hs
  obtain ⟨J, hJmax, hsJ⟩ := exists_max_ideal_of_mem_nonunits hs_nonunit
  let x : PrimeSpectrum (R ⧸ I) := ⟨J, hJmax.isPrime⟩
  have hx_zero : PrimeSpectrum.comap q x ∈ PrimeSpectrum.zeroLocus I := by
    rw [PrimeSpectrum.mem_zeroLocus]
    simpa [I, q] using (Ideal.ker_le_comap q : RingHom.ker q ≤ Ideal.comap q x.asIdeal)
  have hx_range :
      PrimeSpectrum.comap q x ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization S))) := by
    rw [hzero]
    simpa [I] using hx_zero
  have hrange :
      Set.range (PrimeSpectrum.comap (algebraMap R (Localization S))) =
        { p : PrimeSpectrum R | Disjoint (S : Set R) p.asIdeal } :=
    PrimeSpectrum.localization_comap_range (S := Localization S) (M := S)
  have hdisjoint :
      Disjoint (S : Set R) (PrimeSpectrum.comap q x).asIdeal := by
    rw [hrange] at hx_range
    exact hx_range
  have hs_mem : (s : R) ∈ (PrimeSpectrum.comap q x).asIdeal := by
    change q s ∈ x.asIdeal
    exact hsJ
  exact hdisjoint.le_bot ⟨s.2, hs_mem⟩

/-- Helper for Lemma 10.33.1: the quotient by the kernel of the localization map surjects onto
the localization. -/
lemma kernel_quotient_kerLift_surjective_of_isClosed_range_comap
    (hclosed : IsClosed (Set.range (PrimeSpectrum.comap (algebraMap R (Localization S))))) :
    Function.Surjective
      (RingHom.kerLift (algebraMap R (Localization S)) :
        R ⧸ RingHom.ker (algebraMap R (Localization S)) →+* Localization S) := by
  let I : Ideal R := RingHom.ker (algebraMap R (Localization S))
  let q : R →+* R ⧸ I := Ideal.Quotient.mk I
  let g : R ⧸ I →+* Localization S := RingHom.kerLift (algebraMap R (Localization S))
  have hzero := range_comap_eq_zeroLocus_kernel_of_isClosed (R := R) (S := S) hclosed
  let h : Localization S →+* R ⧸ I :=
    IsLocalization.lift
      (M := S)
      (S := Localization S)
      (g := q)
      (fun s ↦ isUnit_quotient_mk_of_mem_submonoid (R := R) (S := S) hzero s)
  have hcomp : h.comp (algebraMap R (Localization S)) = q := by
    -- The lift is the unique map extending the quotient map on the base ring.
    simpa [h] using
      (IsLocalization.lift_comp
        (M := S)
        (S := Localization S)
        (g := q)
        (hg := fun s ↦ isUnit_quotient_mk_of_mem_submonoid (R := R) (S := S) hzero s))
  have hright : g.comp h = RingHom.id (Localization S) := by
    -- It suffices to check the composite on the image of `R`.
    apply IsLocalization.ringHom_ext (M := S)
    ext r
    have hcomp_apply := congrArg (fun k : R →+* R ⧸ I => k r) hcomp
    calc
      g (h (algebraMap R (Localization S) r))
          = g (q r) := by
              exact congrArg g hcomp_apply
      _ = algebraMap R (Localization S) r := by
            exact RingHom.kerLift_mk (f := algebraMap R (Localization S)) r
  intro z
  -- The right inverse produced by the localization lift gives surjectivity.
  refine ⟨h z, ?_⟩
  simpa [RingHom.comp_apply] using congrArg (fun k : Localization S →+* Localization S => k z) hright

/-- Helper for Lemma 10.33.1: the quotient by the kernel of the localization map is isomorphic to
the localization. -/
theorem kernel_quotient_ringEquiv_localization_of_isClosed_range_comap
    (hclosed : IsClosed (Set.range (PrimeSpectrum.comap (algebraMap R (Localization S))))) :
    Nonempty ((R ⧸ RingHom.ker (algebraMap R (Localization S))) ≃+* Localization S) := by
  -- The kernel lift is injective in general and surjective under the closed-image hypothesis.
  exact ⟨RingEquiv.ofBijective
    (RingHom.kerLift (algebraMap R (Localization S)))
    ⟨RingHom.kerLift_injective (f := algebraMap R (Localization S)),
      kernel_quotient_kerLift_surjective_of_isClosed_range_comap (R := R) (S := S) hclosed⟩⟩

/-- Lemma 10.33.1: if the image of `Spec(S⁻¹R) → Spec(R)` is closed, then `S⁻¹R` is isomorphic to
the quotient `R / I` for some ideal `I ⊆ R`. -/
@[stacks 02JH]
theorem exists_ideal_ringEquiv_quotient_of_isClosed_range_comap
    (hclosed : IsClosed (Set.range (PrimeSpectrum.comap (algebraMap R (Localization S))))) :
    ∃ I : Ideal R, Nonempty (Localization S ≃+* R ⧸ I) := by
  -- Use the kernel of the localization map as the quotient ideal.
  refine ⟨RingHom.ker (algebraMap R (Localization S)), ?_⟩
  obtain ⟨e⟩ :=
    kernel_quotient_ringEquiv_localization_of_isClosed_range_comap (R := R) (S := S) hclosed
  exact ⟨e.symm⟩

/-- Closed image of `Spec(S⁻¹R) → Spec(R)` forces the localization map `R → S⁻¹R` to be
surjective. -/
theorem algebraMap_surjective_of_isClosed_range_comap
    (hclosed : IsClosed (Set.range (PrimeSpectrum.comap (algebraMap R (Localization S))))) :
    Function.Surjective (algebraMap R (Localization S)) := by
  let I : Ideal R := RingHom.ker (algebraMap R (Localization S))
  have hsurj :
      Function.Surjective
        (RingHom.kerLift (algebraMap R (Localization S)) : R ⧸ I →+* Localization S) :=
    kernel_quotient_kerLift_surjective_of_isClosed_range_comap (R := R) (S := S) hclosed
  intro z
  -- First lift `z` to the kernel quotient, then choose a representative in `R`.
  obtain ⟨y, hy⟩ := hsurj z
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨r, ?_⟩
  simpa [I] using hy

end
