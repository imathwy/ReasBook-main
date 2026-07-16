import DifferentialForms_Cartan_1970.cartan.III.section12.«0038_Exercise_25».PiCotKernel

noncomputable section

open Filter Bornology
open scoped Topology

/-- Helper for Cartan section12 0038_Exercise_25: the kernel `z ↦ π cot (π z)` is meromorphic on
the whole complex plane. -/
theorem exercise25_piCot_isMeromorphic :
    Meromorphic exercise25PiCot := by
  rw [exercise25_piCot_as_logDeriv_sinPi]
  let hsinPi : Meromorphic (fun w : ℂ ↦ Complex.sin ((Real.pi : ℂ) * w)) := by
    intro z
    fun_prop
  simpa using hsinPi.logDeriv

/-- Helper for Cartan section12 0038_Exercise_25: the cotangent kernel has a simple pole at each
integer. -/
theorem exercise25_piCot_integer_simplePole (n : ℤ) :
    meromorphicOrderAt exercise25PiCot (n : ℂ) = (-1 : WithTop ℤ) := by
  have hmer : MeromorphicAt exercise25PiCot (n : ℂ) := exercise25_piCot_isMeromorphic (n : ℂ)
  have hsub_mer : MeromorphicAt (fun z : ℂ ↦ z - (n : ℂ)) (n : ℂ) := by
    fun_prop
  have hprod_mer : MeromorphicAt (fun z ↦ (z - (n : ℂ)) * exercise25PiCot z) (n : ℂ) :=
    hsub_mer.mul hmer
  have hprod_order :
      meromorphicOrderAt (fun z ↦ (z - (n : ℂ)) * exercise25PiCot z) (n : ℂ) = 0 := by
    exact (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero hprod_mer).1
      ⟨1, one_ne_zero, exercise25_tendsto_sub_integer_mul_piCot n⟩
  have hmul_order :
      meromorphicOrderAt (fun z ↦ (z - (n : ℂ)) * exercise25PiCot z) (n : ℂ) =
        meromorphicOrderAt (fun z : ℂ ↦ z - (n : ℂ)) (n : ℂ) +
          meromorphicOrderAt exercise25PiCot (n : ℂ) :=
    meromorphicOrderAt_mul hsub_mer hmer
  rw [hmul_order] at hprod_order
  have hsum_zero : meromorphicOrderAt exercise25PiCot (n : ℂ) + (1 : WithTop ℤ) = 0 := by
    simpa [add_comm] using hprod_order
  have hsub := congrArg (fun t : WithTop ℤ ↦ t - (1 : WithTop ℤ)) hsum_zero
  simpa [sub_eq_add_neg, add_assoc] using hsub

/-- Helper for Cartan section12 0038_Exercise_25: the residue of the cotangent kernel at each
integer is `1`. -/
theorem exercise25_piCot_integer_trailingCoeff (n : ℤ) :
    meromorphicTrailingCoeffAt exercise25PiCot (n : ℂ) = 1 := by
  have hmer : MeromorphicAt exercise25PiCot (n : ℂ) := exercise25_piCot_isMeromorphic (n : ℂ)
  have hsub_mer : MeromorphicAt (fun z : ℂ ↦ z - (n : ℂ)) (n : ℂ) := by
    fun_prop
  have hprod_mer : MeromorphicAt (fun z ↦ (z - (n : ℂ)) * exercise25PiCot z) (n : ℂ) :=
    hsub_mer.mul hmer
  have hprod_order :
      meromorphicOrderAt (fun z ↦ (z - (n : ℂ)) * exercise25PiCot z) (n : ℂ) = 0 := by
    exact (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero hprod_mer).1
      ⟨1, one_ne_zero, exercise25_tendsto_sub_integer_mul_piCot n⟩
  have hprod_coeff_tendsto := hprod_mer.tendsto_nhds_meromorphicTrailingCoeffAt
  have hprod_coeff_tendsto' :
      Tendsto (fun z ↦ (z - (n : ℂ)) * exercise25PiCot z) (𝓝[≠] (n : ℂ))
        (𝓝 (meromorphicTrailingCoeffAt
          (fun z ↦ (z - (n : ℂ)) * exercise25PiCot z) (n : ℂ))) := by
    simpa [hprod_order, Pi.smul_apply, Pi.pow_apply, smul_eq_mul] using hprod_coeff_tendsto
  have hprod_coeff :
      meromorphicTrailingCoeffAt (fun z ↦ (z - (n : ℂ)) * exercise25PiCot z) (n : ℂ) = 1 :=
    tendsto_nhds_unique hprod_coeff_tendsto' (exercise25_tendsto_sub_integer_mul_piCot n)
  have hprod_coeff' :
      meromorphicTrailingCoeffAt ((fun z : ℂ ↦ z - (n : ℂ)) * exercise25PiCot) (n : ℂ) = 1 := by
    simpa using hprod_coeff
  have hmul_coeff := hsub_mer.meromorphicTrailingCoeffAt_mul hmer
  rw [meromorphicTrailingCoeffAt_id_sub_const, hprod_coeff'] at hmul_coeff
  simpa using hmul_coeff.symm
