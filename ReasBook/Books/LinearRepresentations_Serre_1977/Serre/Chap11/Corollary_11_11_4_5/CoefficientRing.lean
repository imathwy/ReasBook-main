import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.IntegralRestrictionSplitting

/-!
# Chain-independent helpers for Corollary 11-11.4-5

* `connectedSpace_primeSpectrum_of_tensor` — connectedness descends along the integral extension
  `B → A ⊗[ℤ] B`;
* `Representation.characterRing_flat_int` — `R(G)` is flat over `ℤ`.
-/

open scoped TensorProduct Representation NumberField

namespace Corollary_11_11_4_5

/-- Connectedness descent along the integral extension `B → A ⊗[ℤ] B`: if `A` is an integral,
free, faithful `ℤ`-algebra and `B` is flat over `ℤ`, then connectedness of `Spec (A ⊗[ℤ] B)`
forces connectedness of `Spec B`. -/
theorem connectedSpace_primeSpectrum_of_tensor
    {A B : Type*} [CommRing A] [CommRing B]
    [Algebra.IsIntegral ℤ A] [Module.Free ℤ A] [Nontrivial A] [FaithfulSMul ℤ A]
    [Module.Flat ℤ B]
    (h : ConnectedSpace (PrimeSpectrum (A ⊗[ℤ] B))) :
    ConnectedSpace (PrimeSpectrum B) := by
  let e : (A ⊗[ℤ] B) ≃ₐ[ℤ] (B ⊗[ℤ] A) := Algebra.TensorProduct.comm ℤ A B
  haveI : ConnectedSpace (PrimeSpectrum (B ⊗[ℤ] A)) :=
    (PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv).connectedSpace_iff.mp h
  haveI : Algebra.IsIntegral B (B ⊗[ℤ] A) := Algebra.IsIntegral.tensorProduct ℤ B A
  have hinj : Function.Injective (algebraMap B (B ⊗[ℤ] A)) :=
    Algebra.TensorProduct.includeLeft_injective (R := ℤ) (S := ℤ) (A := B) (B := A)
      ((faithfulSMul_iff_algebraMap_injective ℤ A).mp inferInstance)
  haveI : FaithfulSMul B (B ⊗[ℤ] A) := (faithfulSMul_iff_algebraMap_injective B _).mpr hinj
  exact (Algebra.IsIntegral.comap_surjective (R := B) (S := B ⊗[ℤ] A)).connectedSpace
    (PrimeSpectrum.continuous_comap _)

end Corollary_11_11_4_5

namespace Representation

/-- The character ring `R(G)` is flat over `ℤ` (finitely generated and torsion-free over the
PID `ℤ`, hence free). -/
theorem characterRing_flat_int {G : Type} [Group G] [Finite G] : Module.Flat ℤ (R(G)) := by
  haveI : Module.Finite ℤ (R(G)) := Representation.characterRing_moduleFinite
  haveI : Module.IsTorsionFree ℤ (R(G)) := by
    refine Module.IsTorsionFree.of_smul_eq_zero ?_
    intro n χ hχ
    by_cases hn : n = 0
    · exact Or.inl hn
    · right
      apply Subtype.ext
      ext g
      have hvalue := congrArg (fun z : R(G) ↦ ((z : G → ℂ) g)) hχ
      simpa [smul_eq_mul, hn] using hvalue
  haveI : Module.Free ℤ (R(G)) := Module.free_of_finite_type_torsion_free'
  infer_instance

end Representation

namespace Corollary_11_11_4_5

/-- A complex embedding of the `n`-th cyclotomic number field. -/
noncomputable def cyclotomicEmbedding (n : ℕ) [NeZero n] : CyclotomicField n ℚ →ₐ[ℚ] ℂ :=
  IsAlgClosed.lift (R := ℚ) (S := CyclotomicField n ℚ) (M := ℂ)

/-- The coefficient ring `A = 𝓞 (ℚ(ζ_n))` as a `ℂ`-algebra, via `𝓞 L → L → ℂ`. -/
noncomputable def cyclotomicAlgebra (n : ℕ) [NeZero n] : Algebra (𝓞 (CyclotomicField n ℚ)) ℂ :=
  (((cyclotomicEmbedding n).toRingHom).comp
    (algebraMap (𝓞 (CyclotomicField n ℚ)) (CyclotomicField n ℚ))).toAlgebra

/-- `𝓞 (ℚ(ζ_n)) ↪ ℂ` is faithful. -/
theorem cyclotomicAlgebra_faithfulSMul (n : ℕ) [NeZero n] :
    @FaithfulSMul (𝓞 (CyclotomicField n ℚ)) ℂ (cyclotomicAlgebra n).toSMul := by
  letI := cyclotomicAlgebra n
  rw [faithfulSMul_iff_algebraMap_injective]
  show Function.Injective ((cyclotomicEmbedding n).toRingHom.comp
    (algebraMap (𝓞 (CyclotomicField n ℚ)) _))
  exact (cyclotomicEmbedding n).injective.comp (FaithfulSMul.algebraMap_injective _ _)

/-- Every `n`-th root of unity in `ℂ` lies in the image of `A = 𝓞 (ℚ(ζ_n))`. -/
theorem cyclotomicAlgebra_hroots (n : ℕ) [NeZero n] (z : ℂˣ) (hz : z ^ n = 1) :
    (z : ℂ) ∈ Set.range (@algebraMap (𝓞 (CyclotomicField n ℚ)) ℂ _ _ (cyclotomicAlgebra n)) := by
  letI := cyclotomicAlgebra n
  haveI : IsCyclotomicExtension {n} ℚ (CyclotomicField n ℚ) :=
    CyclotomicField.isCyclotomicExtension n ℚ
  have hpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hζspec : IsPrimitiveRoot (IsCyclotomicExtension.zeta n ℚ (CyclotomicField n ℚ)) n :=
    IsCyclotomicExtension.zeta_spec n ℚ (CyclotomicField n ℚ)
  have hζint : IsIntegral ℤ (IsCyclotomicExtension.zeta n ℚ (CyclotomicField n ℚ)) :=
    hζspec.isIntegral hpos
  set ζA : 𝓞 (CyclotomicField n ℚ) := ⟨_, hζint⟩ with hζA
  have hμ : IsPrimitiveRoot (algebraMap (𝓞 (CyclotomicField n ℚ)) ℂ ζA) n := by
    have hmap : algebraMap (𝓞 (CyclotomicField n ℚ)) ℂ ζA
        = cyclotomicEmbedding n (IsCyclotomicExtension.zeta n ℚ (CyclotomicField n ℚ)) := rfl
    rw [hmap]; exact hζspec.map_of_injective (cyclotomicEmbedding n).injective
  have hzc : (z : ℂ) ^ n = 1 := by
    have := congrArg Units.val hz; simpa [Units.val_pow_eq_pow_val] using this
  obtain ⟨i, _, hi⟩ := hμ.eq_pow_of_pow_eq_one hzc
  exact ⟨ζA ^ i, by rw [map_pow, hi]⟩

end Corollary_11_11_4_5
