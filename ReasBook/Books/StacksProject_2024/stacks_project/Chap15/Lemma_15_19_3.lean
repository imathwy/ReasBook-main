import Mathlib
import StacksProject_2024.stacks_project.Chap15.Lemma_15_18_2

-- Declarations for this item will be appended below by the statement pipeline.

open PrimeSpectrum
open scoped TensorProduct

universe u v w x

section

variable {R' : Type u} {S' : Type v} {M' : Type w} {R'' : Type x}
variable [CommRing R'] [CommRing S'] [CommRing R'']
variable [Algebra R' S'] [Algebra R' R'']
variable [AddCommGroup M'] [Module S' M'] [Module R' M'] [IsScalarTower R' S' M']
variable {I' : Ideal R'} {I'' : Ideal R''} {J' : Ideal S'}

attribute [local instance] Algebra.TensorProduct.rightAlgebra

local notation "S''" => S' ⊗[R'] R''
local notation "M''" => S'' ⊗[S'] M'

/-- Helper for Lemma 15.19.3: if a prime of `S'` contains `I'S' + J'`, then its contraction to
`R'` contains `I'`. -/
lemma mem_zeroLocus_comap_left_of_mem_zeroLocus_add
    {q' : PrimeSpectrum S'}
    (hq' : q' ∈ zeroLocus ((Ideal.map (algebraMap R' S') I' + J' : Ideal S') : Set S')) :
    PrimeSpectrum.comap (algebraMap R' S') q' ∈ zeroLocus (I' : Set R') := by
  -- Rewrite closed-subset membership as containment of the sum ideal in `q'`.
  have hsum_le : Ideal.map (algebraMap R' S') I' + J' ≤ q'.asIdeal :=
    (mem_zeroLocus q' ((Ideal.map (algebraMap R' S') I' + J' : Ideal S') : Set S')).1 hq'
  rw [Ideal.add_eq_sup] at hsum_le
  -- Contract the `I'S'` summand back to `R'`.
  have hmap_le : Ideal.map (algebraMap R' S') I' ≤ q'.asIdeal :=
    le_trans le_sup_left hsum_le
  have hcomap_le : I' ≤ (PrimeSpectrum.comap (algebraMap R' S') q').asIdeal := by
    simpa using (Ideal.map_le_iff_le_comap.mp hmap_le)
  exact (mem_zeroLocus (PrimeSpectrum.comap (algebraMap R' S') q') (I' : Set R')).2 hcomap_le

/-- Helper for Lemma 15.19.3: a prime of `S' ⊗[R'] R''` lying over compatible primes in
`V(I'S' + J')` and `V(I'')` belongs to the upstairs closed subset
`V(I''(S' ⊗[R'] R'') + J'(S' ⊗[R'] R''))`. -/
lemma mem_zeroLocus_add_of_tensor_compatible_primes
    {q'' : PrimeSpectrum S''} {q' : PrimeSpectrum S'} {p'' : PrimeSpectrum R''}
    (hq' : q' ∈ zeroLocus ((Ideal.map (algebraMap R' S') I' + J' : Ideal S') : Set S'))
    (hp'' : p'' ∈ zeroLocus (I'' : Set R''))
    (hq''S' : PrimeSpectrum.comap (algebraMap S' S'') q'' = q')
    (hq''R'' : PrimeSpectrum.comap (algebraMap R'' S'') q'' = p'') :
    q'' ∈ zeroLocus
      ((Ideal.map (algebraMap R'' S'') I'' + Ideal.map (algebraMap S' S'') J' : Ideal S'') :
        Set S'') := by
  -- Split the downstairs sum-ideal condition into its two summands.
  have hsum_le : Ideal.map (algebraMap R' S') I' + J' ≤ q'.asIdeal :=
    (mem_zeroLocus q' ((Ideal.map (algebraMap R' S') I' + J' : Ideal S') : Set S')).1 hq'
  rw [Ideal.add_eq_sup] at hsum_le
  have hp''_le : I'' ≤ p''.asIdeal := (mem_zeroLocus p'' (I'' : Set R'')).1 hp''
  have hq''S'_ideal : Ideal.comap (algebraMap S' S'') q''.asIdeal = q'.asIdeal := by
    simpa [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hq''S'
  have hq''R''_ideal : Ideal.comap (algebraMap R'' S'') q''.asIdeal = p''.asIdeal := by
    simpa [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hq''R''
  -- The `I''` summand ascends from the contraction to `R''`.
  have hI_map_le : Ideal.map (algebraMap R'' S'') I'' ≤ q''.asIdeal := by
    apply Ideal.map_le_iff_le_comap.mpr
    simpa [hq''R''_ideal] using hp''_le
  -- The `J'` summand ascends from the contraction to `S'`.
  have hJ_le : J' ≤ q'.asIdeal := le_trans le_sup_right hsum_le
  have hJ_map_le : Ideal.map (algebraMap S' S'') J' ≤ q''.asIdeal := by
    apply Ideal.map_le_iff_le_comap.mpr
    simpa [hq''S'_ideal] using hJ_le
  -- Reassemble the two summands into the desired upstairs zero-locus condition.
  have hadd_le :
      Ideal.map (algebraMap R'' S'') I'' + Ideal.map (algebraMap S' S'') J' ≤ q''.asIdeal := by
    rw [Ideal.add_eq_sup]
    exact sup_le hI_map_le hJ_map_le
  exact
    (mem_zeroLocus q''
      ((Ideal.map (algebraMap R'' S'') I'' + Ideal.map (algebraMap S' S'') J' : Ideal S'') :
        Set S'')).2 hadd_le

/-- Helper for Lemma 15.19.3: flatness of the localized tensor-base-changed module at a prime
`q''` descends to flatness at the compatible prime `q'` of `S'`. -/
lemma flat_localizedModule_of_flat_tensor_prime
    {q'' : PrimeSpectrum S''} {q' : PrimeSpectrum S'} {p'' : PrimeSpectrum R''}
    (hq''S' : PrimeSpectrum.comap (algebraMap S' S'') q'' = q')
    (hq''R'' : PrimeSpectrum.comap (algebraMap R'' S'') q'' = p'')
    (hflat_q'' : Module.Flat R'' (LocalizedModule.AtPrime q''.asIdeal M''))
    (hflat_p'' : Module.Flat R' (LocalizedModule.AtPrime p''.asIdeal R'')) :
    Module.Flat R' (LocalizedModule.AtPrime q'.asIdeal M') := by
  -- Route correction: reuse Lemma `15.18.2` for the tensor-square descent and only perform the
  -- two prime rewrites that identify its contracted primes with `p''` and `q'`.
  have hflat_q''R'' :
      Module.Flat R'
        (LocalizedModule.AtPrime (PrimeSpectrum.comap (algebraMap R'' S'') q'').asIdeal R'') := by
    cases hq''R''
    simpa using hflat_p''
  have hflat_down :
      Module.Flat R'
        (LocalizedModule.AtPrime (PrimeSpectrum.comap (algebraMap S' S'') q'').asIdeal M') :=
    flat_localizedModule_of_flat_tensor_base_change
      (R := R') (S := S') (M := M') (R' := R'') q'' hflat_q'' hflat_q''R''
  cases hq''S'
  simpa using hflat_down

/-- Lemma 15.19.3: if the canonical closed-subset inclusion
`V(I''(S' ⊗[R'] R'') + J'(S' ⊗[R'] R'')) ⊆ Module.flatOverBaseLocus R'' (S' ⊗[R'] R'')
((S' ⊗[R'] R'') ⊗[S'] M')` holds after base change from `R'` to `R''`, then the corresponding
inclusion for `V(I'S' + J')` already holds over `R'`, provided `I'R'' ≤ I''`, the induced map
`V(I'') → V(I')` is surjective, and `I''` has flat-over-`R'` zero locus on `Spec R''`. -/
theorem zeroLocus_add_subset_flatOverBaseLocus_of_surjOn_zeroLocus_descends
    (hI'' : Ideal.map (algebraMap R' R'') I' ≤ I'')
    (hsurj : Set.SurjOn (PrimeSpectrum.comap (algebraMap R' R''))
      (zeroLocus (I'' : Set R'')) (zeroLocus (I' : Set R')))
    (hlocFlat : zeroLocus (I'' : Set R'') ⊆ Module.flatOverBaseLocus R' R'' R'')
    (hbase : zeroLocus
      ((Ideal.map (algebraMap R'' S'') I'' + Ideal.map (algebraMap S' S'') J' : Ideal S'') :
        Set S'') ⊆
        Module.flatOverBaseLocus R'' S'' M'') :
    zeroLocus ((Ideal.map (algebraMap R' S') I' + J' : Ideal S') : Set S') ⊆
      Module.flatOverBaseLocus R' S' M' := by
  let _ := hI''
  -- Follow the source proof primewise via contraction to `R'`, lifting to `R''`, and then lifting
  -- once more to the tensor-product base change.
  refine
    (Ideal.zeroLocus_subset_flatOverBaseLocus_iff
      (R := R') (S := S') (M := M') (Ideal.map (algebraMap R' S') I' + J')).2 ?_
  intro q' hq'
  let p' : PrimeSpectrum R' := PrimeSpectrum.comap (algebraMap R' S') q'
  -- The downstairs closed-subset condition gives the required base prime in `V(I')`.
  have hp' : p' ∈ zeroLocus (I' : Set R') := by
    simpa [p'] using
      mem_zeroLocus_comap_left_of_mem_zeroLocus_add (I' := I') (J' := J') hq'
  obtain ⟨p'', hp'', hp''comap⟩ := hsurj hp'
  have hcompat :
      PrimeSpectrum.comap (algebraMap R' R'') p'' =
        PrimeSpectrum.comap (algebraMap R' S') q' := by
    simpa [p'] using hp''comap
  -- Lift the compatible pair `(q', p'')` to a prime upstairs in `Spec (S' ⊗[R'] R'')`.
  obtain ⟨q'', hq''S', hq''R''⟩ :=
    exists_prime_over_tensor_base_change (R := R') (S := S') (R' := R'') q' p'' hcompat
  have hq'' :
      q'' ∈ zeroLocus
        ((Ideal.map (algebraMap R'' S'') I'' + Ideal.map (algebraMap S' S'') J' : Ideal S'') :
          Set S'') :=
    mem_zeroLocus_add_of_tensor_compatible_primes
      (I' := I') (I'' := I'') (J' := J') hq' hp'' hq''S' hq''R''
  -- The upstairs hypothesis gives flatness after localizing the base-changed module at `q''`.
  have hflat_q'' : Module.Flat R'' (LocalizedModule.AtPrime q''.asIdeal M'') :=
    (Module.mem_flatOverBaseLocus R'' S'' M'' q'').1 (hbase hq'')
  -- The local flatness of `R''` over `R'` at `p''` is the second input for descent.
  have hflat_p'' : Module.Flat R' (LocalizedModule.AtPrime p''.asIdeal R'') :=
    (Module.mem_flatOverBaseLocus R' R'' R'' p'').1 (hlocFlat hp'')
  -- Descend flatness from `q''` back to the original prime `q'`.
  have hflat_q' : Module.Flat R' (LocalizedModule.AtPrime q'.asIdeal M') :=
    flat_localizedModule_of_flat_tensor_prime
      (q'' := q'') (q' := q') (p'' := p'') hq''S' hq''R'' hflat_q'' hflat_p''
  exact (Module.mem_flatOverBaseLocus R' S' M' q').2 hflat_q'

/-- The `J' = 0` specialization of Lemma 15.19.3, phrased directly as the canonical closed-subset
inclusion `V(I'S') ⊆ Module.flatOverBaseLocus R' S' M'`. -/
theorem zeroLocus_subset_flatOverBaseLocus_of_surjOn_zeroLocus_descends
    (hI'' : Ideal.map (algebraMap R' R'') I' ≤ I'')
    (hsurj : Set.SurjOn (PrimeSpectrum.comap (algebraMap R' R''))
      (zeroLocus (I'' : Set R'')) (zeroLocus (I' : Set R')))
    (hlocFlat : zeroLocus (I'' : Set R'') ⊆ Module.flatOverBaseLocus R' R'' R'')
    (hbase :
      zeroLocus (Ideal.map (algebraMap R'' S'') I'' : Set S'') ⊆
        Module.flatOverBaseLocus R'' S'' M'') :
    zeroLocus (Ideal.map (algebraMap R' S') I' : Set S') ⊆
      Module.flatOverBaseLocus R' S' M' := by
  -- Specialize the main theorem to `J' = 0` and simplify the two sum ideals.
  have hbase' :
      zeroLocus
          ((Ideal.map (algebraMap R'' S'') I'' + Ideal.map (algebraMap S' S'') (⊥ : Ideal S') :
              Ideal S'') : Set S'') ⊆
        Module.flatOverBaseLocus R'' S'' M'' := by
    simpa [Ideal.map_bot, Ideal.add_eq_sup, sup_bot_eq] using hbase
  intro q hq
  -- Rewrite the downstairs hypothesis into the `J' = ⊥` form required by the main theorem.
  have hq' :
      q ∈ zeroLocus
        ((Ideal.map (algebraMap R' S') I' + (⊥ : Ideal S') : Ideal S') : Set S') := by
    simpa [Ideal.add_eq_sup, sup_bot_eq] using hq
  exact
    zeroLocus_add_subset_flatOverBaseLocus_of_surjOn_zeroLocus_descends
      (I' := I') (I'' := I'') (J' := (⊥ : Ideal S')) hI'' hsurj hlocFlat hbase' hq'

end
