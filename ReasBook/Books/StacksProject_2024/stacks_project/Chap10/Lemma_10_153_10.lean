import Mathlib
import Mathlib.Data.List.TFAE
import StacksProject_2024.stacks_project.Chap10.Lemma_10_53_5
import StacksProject_2024.stacks_project.Chap10.Lemma_10_153_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing

section

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-
Domain-style sampling:
- primary domain: henselian local rings and zero-dimensional finite algebras over a local base;
- sampled owner declarations in this domain:
  `HenselianLocalRing`,
  `henselian_local_ring_tfae`,
  `Ring.KrullDimLE.eq_maximalIdeal_of_isPrime`,
  `maximalSpectrum_toPiLocalizationEquiv_of_finite_of_jacobson_locallyNilpotent`;
- best owner abstraction:
  the canonical owner is `HenselianLocalRing R`, and the decisive bridge clause is
  `finite_algebra_finite_local_product_property R` from `henselian_local_ring_tfae`;
- primitive data:
  the local-ring structure on `R` together with the canonical zero-dimensional owner
  `Ring.KrullDimLE 0 R`;
- derived API:
  zero-dimensionality of finite `R`-algebras, locally nilpotent Jacobson radicals, and the
  canonical product decomposition indexed by `MaximalSpectrum`.

Source/core/bridge triage:
- `source-facing`: `localRing_henselian_of_krullDimLE_zero`;
- `core/canonical`: `HenselianLocalRing R`;
- `bridge/view`: `localRing_henselian_of_ringKrullDim_eq_zero`, together with the finite-algebra
  product criterion from `henselian_local_ring_tfae` and the canonical product decomposition
  `maximalSpectrum_toPiLocalizationEquiv_of_finite_of_jacobson_locallyNilpotent`.
-/

-- Proof sketch: by Lemma `10.153.3`, it is enough to show that every finite `R`-algebra is a
-- product of local rings. For a finite `R`-algebra `S`, all primes of `S` lie over the maximal
-- ideal of `R`; because `R` has Krull dimension at most `0`, these primes admit no strict
-- inclusions, so they are all maximal. The intersection of the finitely many maximal ideals is
-- nilpotent, and Lemma `10.53.5` then yields the required product decomposition.
/-- Lemma 10.153.10, owner-level form: a zero-dimensional local ring is henselian, stated using
the canonical zero-dimensional owner hypothesis `[Ring.KrullDimLE 0 R]`. -/
theorem localRing_henselian_of_krullDimLE_zero [Ring.KrullDimLE 0 R] :
    HenselianLocalRing R := by
  let l : List Prop := [
    HenselianLocalRing R,
    @simple_root_lift_property.{u} R _ _,
    @monic_coprime_factorization_lift_property.{u} R _ _,
    @monic_coprime_factorization_lift_with_degree_property.{u} R _ _,
    @coprime_factorization_lift_property.{u} R _ _,
    @coprime_factorization_lift_with_degree_property.{u} R _ _,
    @etale_retraction_exists_property.{u, u} R _ _,
    @etale_retraction_unique_property.{u, u} R _ _,
    @finite_algebra_local_product_property.{u, u} R _,
    @finite_algebra_finite_local_product_property.{u, u} R _,
    @finite_type_algebra_split_finite_nonQuasiFinite_property.{u, u} R _ _,
    @finite_type_algebra_split_finite_positive_dimensional_fiber_property.{u, u} R _ _,
    @quasi_finite_algebra_split_finite_zero_special_fiber_property.{u, u} R _ _
  ]
  have htfae : List.TFAE l := by
    simpa [l] using (@henselian_local_ring_tfae.{u, u} R _ _)
  have hfinite (S : Type u) [CommRing S] [Algebra R S] [Module.Finite R S] :
      has_finite_local_ring_product_decomposition S := by
    have hdimS : Ring.KrullDimLE 0 S := Ring.KrullDimLE.mk₀ fun J hJ ↦ by
      letI : J.IsPrime := hJ
      letI : (Ideal.comap (algebraMap R S) J).IsMaximal := by
        rw [Ring.KrullDimLE.eq_maximalIdeal_of_isPrime
          (Ideal.comap (algebraMap R S) J)]
        exact maximalIdeal.isMaximal R
      have hcomap : (Ideal.comap (algebraMap R S) J).IsMaximal := inferInstance
      exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap J hcomap
    letI : Algebra.QuasiFinite R S :=
      (RingHom.quasiFinite_algebraMap : (algebraMap R S).QuasiFinite ↔ Algebra.QuasiFinite R S).mp <|
        RingHom.QuasiFinite.of_finite
          <| RingHom.finite_algebraMap.mpr inferInstance
    have hfin : Finite (MaximalSpectrum S) := by
      have hprimesOver : ((maximalIdeal R).primesOver S).Finite :=
        Algebra.QuasiFinite.finite_primesOver (maximalIdeal R)
      have hmax : { J : Ideal S | J.IsMaximal }.Finite := hprimesOver.subset fun J hJ ↦ by
        letI : J.IsMaximal := hJ
        letI : J.IsPrime := hJ.isPrime
        refine ⟨hJ.isPrime, ⟨?_⟩⟩
        simpa [Ideal.under_def] using
          (Ring.KrullDimLE.eq_maximalIdeal_of_isPrime
            (Ideal.comap (algebraMap R S) J)).symm
      exact (MaximalSpectrum.equivSubtype S).finite_iff.mpr hmax
    have hjac : (Ring.jacobson S).IsLocallyNilpotent := by
      rw [Ideal.isLocallyNilpotent_iff]
      intro x hx
      rw [Ring.jacobson_eq_nilradical_of_krullDimLE_zero S] at hx
      exact mem_nilradical.mp hx
    let _ : Fintype (MaximalSpectrum S) := Fintype.ofFinite (MaximalSpectrum S)
    refine ⟨MaximalSpectrum S, inferInstance, fun J ↦ Localization.AtPrime J.asIdeal,
      fun _ ↦ inferInstance, fun _ ↦ inferInstance, ?_⟩
    exact ⟨maximalSpectrum_toPiLocalizationEquiv_of_finite_of_jacobson_locallyNilpotent hfin hjac⟩
  exact (htfae.out 0 9 rfl rfl).mpr hfinite

/-- Lemma 10.153.10, textbook wording: if `ringKrullDim R = 0`, then the local ring `R` is
henselian. This is the thin bridge from the source equality form to the owner theorem
`localRing_henselian_of_krullDimLE_zero`. -/
theorem localRing_henselian_of_ringKrullDim_eq_zero
    (hdim : ringKrullDim R = 0) :
    HenselianLocalRing R := by
  let _ : Ring.KrullDimLE 0 R := ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr hdim
  exact localRing_henselian_of_krullDimLE_zero R

end
