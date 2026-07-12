import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

open PrimeSpectrum

variable {R : Type u} [CommRing R] (M : Submonoid R)

/- Lemma 10.33.1: if the image of `Spec(Localization M) → Spec(R)` is closed, then the
localization map `R → Localization M` is surjective. -/
-- Proof sketch: since the image is closed, it is a zero locus `V(I)` for some ideal `I`. For a
-- localization, `PrimeSpectrum.localization_comap_range` identifies the image with the primes of
-- `R` disjoint from `M`. Hence a prime contains `I` exactly when it is disjoint from `M`, so every
-- element of `M` becomes invertible modulo `I`. Taking `I = ker(R → Localization M)`, the induced
-- map `R ⧸ I → Localization M` is surjective, and the first isomorphism theorem identifies the
-- localization with this quotient.
theorem algebraMap_surjective_of_isClosed_range_comap
    (hclosed : IsClosed (Set.range (PrimeSpectrum.comap (algebraMap R (Localization M))))) :
    Function.Surjective (algebraMap R (Localization M)) := by
  let I : Ideal R := RingHom.ker (algebraMap R (Localization M))
  let q : R →+* R ⧸ I := Ideal.Quotient.mk I
  have hrange :
      Set.range (PrimeSpectrum.comap (algebraMap R (Localization M))) = zeroLocus I := by
    simpa [I, hclosed.closure_eq] using
      (PrimeSpectrum.closure_range_comap (algebraMap R (Localization M)))
  have hunit :
      ∀ m : M, IsUnit (q m) := by
    intro m
    by_contra hm
    obtain ⟨J, hJmax, hmJ⟩ :=
      exists_max_ideal_of_mem_nonunits
        ((mem_nonunits_iff : q m ∈ nonunits (R ⧸ I) ↔ ¬ IsUnit (q m)).2 hm)
    let p : PrimeSpectrum (R ⧸ I) := ⟨J, hJmax.isPrime⟩
    have hqrange :
        PrimeSpectrum.comap q p ∈
          Set.range (PrimeSpectrum.comap (algebraMap R (Localization M))) := by
      have hqzero : PrimeSpectrum.comap q p ∈ zeroLocus I := by
        rw [PrimeSpectrum.mem_zeroLocus]
        simpa [I, q, Ideal.mk_ker] using Ideal.ker_le_comap q
      rwa [← hrange] at hqzero
    have hdisj :
        Disjoint (M : Set R) (PrimeSpectrum.comap q p).asIdeal := by
      rwa [PrimeSpectrum.localization_comap_range (Localization M) M] at hqrange
    have hmq : (m : R) ∈ (PrimeSpectrum.comap q p).asIdeal := by
      simpa [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] using hmJ
    exact Set.disjoint_left.mp hdisj m.2 hmq
  letI :
      IsLocalization (M.map q) (R ⧸ I) :=
    IsLocalization.self <| by
      rintro _ ⟨m, hm, rfl⟩
      exact hunit ⟨m, hm⟩
  let lift : R ⧸ I →+* Localization M :=
    Ideal.Quotient.lift I (algebraMap R (Localization M))
      (fun x hx ↦ by simpa only [RingHom.mem_ker] using hx)
  letI : Algebra (R ⧸ I) (Localization M) :=
    lift.toAlgebra
  have hcomp :
      (RingHom.id (Localization M)).comp (algebraMap R (Localization M)) =
        (algebraMap (R ⧸ I) (Localization M)).comp q := by
    simpa [q, lift] using
      (Ideal.Quotient.lift_comp_mk I (algebraMap R (Localization M))
        (fun x hx ↦ by simpa only [RingHom.mem_ker] using hx)).symm
  letI :
      IsLocalization (M.map q) (Localization M) :=
    IsLocalization.of_surjective M (Localization M) q Ideal.Quotient.mk_surjective
      (RingHom.id _) (fun z ↦ ⟨z, rfl⟩) hcomp bot_le
  let e :
      (R ⧸ I) ≃ₐ[R ⧸ I] Localization M :=
    IsLocalization.algEquiv (M.map q) (R ⧸ I) (Localization M)
  have hsurjQuot : Function.Surjective (algebraMap (R ⧸ I) (Localization M)) := by
    intro z
    obtain ⟨y, rfl⟩ := e.surjective z
    exact ⟨y, (e.commutes y).symm⟩
  intro z
  obtain ⟨y, hy⟩ := hsurjQuot z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨x, by simpa [q] using hy⟩

end
