import StacksProject_2024.Chap10.Lemma_10_64_3.SemilocalPrime

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]

open scoped TensorProduct

namespace Ideal

variable (𝔭 : Ideal R) [𝔭.IsPrime]
variable [(𝔭.map (algebraMap R S)).IsPrime]

local notation "𝔭S" => 𝔭.map (algebraMap R S)
local notation "Rₚ" => Localization.AtPrime 𝔭
local notation "Sₚ" => Localization (Algebra.algebraMapSubmonoid S (Ideal.primeCompl 𝔭))
local notation "S𝔮" => Localization.AtPrime 𝔭S

attribute [local instance] semilocal_map_prime_isPrime
attribute [local instance] semilocalToLocalAlgebra

/-- Helper for Lemma 10.64.3: the tensor-side inclusion of the localized base ring `Rₚ` into
`S ⊗[R] Rₚ`. -/
noncomputable abbrev tensorLocalizedBaseIncludeRight : Rₚ →+* (S ⊗[R] Rₚ) :=
  (Algebra.TensorProduct.includeRight : Rₚ →ₐ[R] S ⊗[R] Rₚ).toRingHom

/-- Helper for Lemma 10.64.3: under the tensor-localization equivalence
`S ⊗[R] Rₚ ≃ Sₚ`, the tensor-side image of the `n`th power of the localized prime ideal is the
`n`th power of the semilocalized prime. -/
lemma localized_prime_map_eq_semilocalized_prime :
    map (algebraMap Rₚ Sₚ) (map (algebraMap R Rₚ) 𝔭) =
      map (algebraMap S Sₚ) 𝔭S := by
  -- Compare the two ideal maps by identifying the underlying composite ring homomorphisms.
  have hbase :
      (algebraMap Rₚ Sₚ).comp (algebraMap R Rₚ) =
        (algebraMap S Sₚ).comp (algebraMap R S) := by
    calc
      (algebraMap Rₚ Sₚ).comp (algebraMap R Rₚ) = algebraMap R Sₚ := by
        symm
        exact IsScalarTower.algebraMap_eq R Rₚ Sₚ
      _ = (algebraMap S Sₚ).comp (algebraMap R S) := by
        exact IsScalarTower.algebraMap_eq R S Sₚ
  calc
    map (algebraMap Rₚ Sₚ) (map (algebraMap R Rₚ) 𝔭)
        = map (((algebraMap Rₚ Sₚ).comp (algebraMap R Rₚ))) 𝔭 := by
            rw [Ideal.map_map]
    _ = map (((algebraMap S Sₚ).comp (algebraMap R S))) 𝔭 := by
          rw [hbase]
    _ = map (algebraMap S Sₚ) 𝔭S := by
          rw [← Ideal.map_map]

/-- Helper for Lemma 10.64.3: under the tensor-localization equivalence
`S ⊗[R] Rₚ ≃ Sₚ`, the tensor-side image of the `n`th power of the localized prime ideal is the
`n`th power of the semilocalized prime. -/
lemma tensorLeftAlgEquiv_map_localized_prime_pow (n : ℕ) :
    map (Localization.tensorLeftAlgEquiv (Ideal.primeCompl 𝔭) S).toRingHom
        (((map (algebraMap R Rₚ) 𝔭) ^ n).map (tensorLocalizedBaseIncludeRight (R := R) (S := S)
          (𝔭 := 𝔭))) =
      (map (algebraMap S Sₚ) 𝔭S) ^ n := by
  -- The base-change equivalence sends the tensor-side copy `1 ⊗ x` of `Rₚ` to its image in `Sₚ`.
  have hcomp :
      ((Localization.tensorLeftAlgEquiv (Ideal.primeCompl 𝔭) S).toRingHom).comp
          (tensorLocalizedBaseIncludeRight (R := R) (S := S) (𝔭 := 𝔭)) =
        algebraMap Rₚ Sₚ := by
    ext x
    simpa using
      (Localization.tensorLeftAlgEquiv_apply_one_tmul (M := Ideal.primeCompl 𝔭) (S := S) x)
  -- Then the ideal transport is just functoriality of `Ideal.map`, together with `Ideal.map_pow`.
  calc
    map (Localization.tensorLeftAlgEquiv (Ideal.primeCompl 𝔭) S).toRingHom
        (((map (algebraMap R Rₚ) 𝔭) ^ n).map (tensorLocalizedBaseIncludeRight (R := R) (S := S)
          (𝔭 := 𝔭)))
        = map (algebraMap Rₚ Sₚ) ((map (algebraMap R Rₚ) 𝔭) ^ n) := by
            rw [Ideal.map_map]
            rw [hcomp]
    _ = (map (algebraMap Rₚ Sₚ) (map (algebraMap R Rₚ) 𝔭)) ^ n := by
          rw [Ideal.map_pow]
    _ = (map (algebraMap S Sₚ) 𝔭S) ^ n := by
          exact congrArg (fun K : Ideal Sₚ ↦ K ^ n)
            (localized_prime_map_eq_semilocalized_prime
              (R := R) (S := S) (𝔭 := 𝔭))

/-- Helper for Lemma 10.64.3: the right-unit tensor equivalence sends the tensor-side copy of the
base ring back to the original `R → S` algebra map. -/
lemma tensor_rid_comp_includeRight :
    (Algebra.TensorProduct.rid R S S).toRingHom.comp
        (Algebra.TensorProduct.includeRight : R →ₐ[R] S ⊗[R] R).toRingHom =
      algebraMap R S := by
  -- The right tensor unit identifies `1 ⊗ r` with the scalar action of `r` on `S`.
  ext x
  simpa [Algebra.smul_def]

/-- Helper for Lemma 10.64.3: extending an ideal to `S ⊗[R] R` along `includeRight` and then
pushing it across the right-unit equivalence recovers the usual extension to `S`. -/
lemma tensor_rid_map_includeRight_eq_map (I : Ideal R) :
    map (Algebra.TensorProduct.rid R S S).toRingHom
        (map (Algebra.TensorProduct.includeRight : R →ₐ[R] S ⊗[R] R) I) =
      map (algebraMap R S) I := by
  -- Functoriality of `Ideal.map` along the composite `rid ∘ includeRight = algebraMap`.
  calc
    map (Algebra.TensorProduct.rid R S S).toRingHom
        (map (Algebra.TensorProduct.includeRight : R →ₐ[R] S ⊗[R] R) I)
        =
          map ((Algebra.TensorProduct.rid R S S).toRingHom.comp
            (Algebra.TensorProduct.includeRight : R →ₐ[R] S ⊗[R] R).toRingHom) I := by
            simpa using
              (Ideal.map_map
                (I := I)
                ((Algebra.TensorProduct.includeRight : R →ₐ[R] S ⊗[R] R).toRingHom)
                ((Algebra.TensorProduct.rid R S S).toRingHom))
    _ = map (algebraMap R S) I := by
          rw [tensor_rid_comp_includeRight (R := R) (S := S)]

/-- Helper for Lemma 10.64.3: after precomposing with the right-unit tensor equivalence
`S ⊗[R] R ≃ S`, the map `includeLeft : S → S ⊗[R] (Rₚ / 𝔭ₚ^n)` becomes the tensorization of the
canonical algebra map `R → Rₚ / 𝔭ₚ^n`. -/
lemma tensor_map_eq_includeLeft_comp_rid (n : ℕ) :
    ((Algebra.TensorProduct.map (AlgHom.id R S)
        (Algebra.ofId R (Rₚ ⧸ (map (algebraMap R Rₚ) 𝔭) ^ n))).toRingHom) =
      (((show S →ₐ[S] S ⊗[R] (Rₚ ⧸ (map (algebraMap R Rₚ) 𝔭) ^ n) from
          Algebra.TensorProduct.includeLeft).toRingHom).comp
        (Algebra.TensorProduct.rid R S S).toRingHom) := by
  -- This is exactly the right-unit identity used in mathlib's `includeLeft_bijective` proof.
  -- Reprove it locally so the later kernel transport can cite a named lemma in this file.
  have h :
      ((show S →ₐ[S] S ⊗[R] (Rₚ ⧸ (map (algebraMap R Rₚ) 𝔭) ^ n) from
          Algebra.TensorProduct.includeLeft).comp
        (Algebra.TensorProduct.rid R S S).toAlgHom) =
        Algebra.TensorProduct.map (.id S S)
          (Algebra.ofId R (Rₚ ⧸ (map (algebraMap R Rₚ) 𝔭) ^ n)) := by
    ext <;> simp
  simpa using congrArg AlgHom.toRingHom h.symm

/-- Helper for Lemma 10.64.3: transporting the tensorized quotient kernel across the right-unit
equivalence identifies it with the image of the kernel of `includeLeft`. -/
lemma ker_tensor_map_eq_map_rid_symm_ker_includeLeft (n : ℕ) :
    RingHom.ker
        ((Algebra.TensorProduct.map (AlgHom.id R S)
          (Algebra.ofId R (Rₚ ⧸ (map (algebraMap R Rₚ) 𝔭) ^ n))).toRingHom) =
      Ideal.map (Algebra.TensorProduct.rid R S S).symm.toRingHom
        (RingHom.ker
          ((show S →ₐ[S] S ⊗[R] (Rₚ ⧸ (map (algebraMap R Rₚ) 𝔭) ^ n) from
            Algebra.TensorProduct.includeLeft).toRingHom)) := by
  -- Rewrite the tensorized quotient map through `rid`, then convert the resulting kernel-comap
  -- into an ideal map along the inverse equivalence.
  rw [tensor_map_eq_includeLeft_comp_rid (R := R) (S := S) (𝔭 := 𝔭) n]
  rw [RingHom.ker_eq_comap_bot, RingHom.ker_eq_comap_bot, ← Ideal.comap_comap]
  let J : Ideal S :=
    RingHom.ker
      ((show S →ₐ[S] S ⊗[R] (Rₚ ⧸ (map (algebraMap R Rₚ) 𝔭) ^ n) from
        Algebra.TensorProduct.includeLeft).toRingHom)
  change Ideal.comap (Algebra.TensorProduct.rid R S S).toRingHom J =
    Ideal.map (Algebra.TensorProduct.rid R S S).symm.toRingHom J
  exact (Ideal.map_symm (f := (Algebra.TensorProduct.rid R S S).toRingEquiv) (I := J)).symm

/-- Helper for Lemma 10.64.3: flat base change turns the defining kernel of `𝔭^(n)` into the
kernel of the tensor-side quotient map before localization transport. -/
lemma tensor_quotient_kernel_eq_map_symbolicPower (n : ℕ) :
    RingHom.ker
      ((Algebra.TensorProduct.includeLeft :
          S →ₐ[R] S ⊗[R] (Rₚ ⧸ (map (algebraMap R Rₚ) 𝔭) ^ n)).toRingHom) =
      map (algebraMap R S) (𝔭.symbolicPower n) := by
  let g : R →ₐ[R] (Rₚ ⧸ (map (algebraMap R Rₚ) 𝔭) ^ n) :=
    Algebra.ofId R (Rₚ ⧸ (map (algebraMap R Rₚ) 𝔭) ^ n)
  have hkernel_tensor :
      RingHom.ker ((Algebra.TensorProduct.map (AlgHom.id R S) g).toRingHom) =
        Ideal.map (Algebra.TensorProduct.includeRight : R →ₐ[R] S ⊗[R] R)
          (RingHom.ker g.toRingHom) := by
    -- Flatness computes the tensor kernel as the range of tensoring the defining kernel subtype.
    rw [← Submodule.restrictScalars_inj R]
    change
      (TensorProduct.AlgebraTensorModule.lTensor R S g.toLinearMap).ker =
        Submodule.restrictScalars R
          (Ideal.map (Algebra.TensorProduct.includeRight : R →ₐ[R] S ⊗[R] R)
            (RingHom.ker g.toRingHom))
    rw [Module.Flat.ker_lTensor_eq (S := R) (M := S) (f := g.toLinearMap)]
    -- Then the tensor range is exactly the ideal generated by the tensor-side copy of the kernel.
    simpa using
      (TensorProduct.AlgebraTensorModule.range_lTensor_idealMap
        (R := R) (A := S) (B := R) (S := R) (I := RingHom.ker g.toRingHom))
  have hkernel_source : RingHom.ker g.toRingHom = 𝔭.symbolicPower n := by
    -- The source kernel is the defining kernel of the `n`th symbolic power.
    change
      RingHom.ker
          (((Ideal.Quotient.mk ((map (algebraMap R Rₚ) 𝔭) ^ n))).comp
            (algebraMap R Rₚ)) =
        𝔭.symbolicPower n
    exact (Ideal.symbolicPower_eq_ker_quotient_map_pow (𝔭 := 𝔭) n).symm
  have htransport :
      RingHom.ker
          ((Algebra.TensorProduct.includeLeft :
              S →ₐ[R] S ⊗[R] (Rₚ ⧸ (map (algebraMap R Rₚ) 𝔭) ^ n)).toRingHom) =
        Ideal.map (Algebra.TensorProduct.rid R S S).toRingHom
          (RingHom.ker ((Algebra.TensorProduct.map (AlgHom.id R S) g).toRingHom)) := by
    have hbridge :=
      ker_tensor_map_eq_map_rid_symm_ker_includeLeft (R := R) (S := S) (𝔭 := 𝔭) n
    have hrid_comp :
        (Algebra.TensorProduct.rid R S S).toRingHom.comp
            (Algebra.TensorProduct.rid R S S).symm.toRingHom =
          RingHom.id S := by
      ext x
      exact (Algebra.TensorProduct.rid R S S).apply_symm_apply x
    -- Mapping across `rid` cancels the earlier transport through `rid.symm`.
    calc
      RingHom.ker
          ((Algebra.TensorProduct.includeLeft :
              S →ₐ[R] S ⊗[R] (Rₚ ⧸ (map (algebraMap R Rₚ) 𝔭) ^ n)).toRingHom)
          =
            Ideal.map (Algebra.TensorProduct.rid R S S).toRingHom
              (Ideal.map (Algebra.TensorProduct.rid R S S).symm.toRingHom
                (RingHom.ker
                  ((Algebra.TensorProduct.includeLeft :
                      S →ₐ[R] S ⊗[R] (Rₚ ⧸ (map (algebraMap R Rₚ) 𝔭) ^ n)).toRingHom))) := by
              symm
              rw [Ideal.map_map, hrid_comp, Ideal.map_id]
      _ = Ideal.map (Algebra.TensorProduct.rid R S S).toRingHom
            (RingHom.ker ((Algebra.TensorProduct.map (AlgHom.id R S) g).toRingHom)) := by
              simpa [g] using congrArg
                (Ideal.map (Algebra.TensorProduct.rid R S S).toRingHom) hbridge.symm
  -- The existing `rid` transport turns the tensor-side kernel computation into the public kernel.
  calc
    RingHom.ker
        ((Algebra.TensorProduct.includeLeft :
            S →ₐ[R] S ⊗[R] (Rₚ ⧸ (map (algebraMap R Rₚ) 𝔭) ^ n)).toRingHom)
        =
          Ideal.map (Algebra.TensorProduct.rid R S S).toRingHom
            (RingHom.ker ((Algebra.TensorProduct.map (AlgHom.id R S) g).toRingHom)) := by
              exact htransport
    _ = Ideal.map (Algebra.TensorProduct.rid R S S).toRingHom
          (Ideal.map (Algebra.TensorProduct.includeRight : R →ₐ[R] S ⊗[R] R)
            (RingHom.ker g.toRingHom)) := by
            rw [hkernel_tensor]
    _ = Ideal.map (Algebra.TensorProduct.rid R S S).toRingHom
          (Ideal.map (Algebra.TensorProduct.includeRight : R →ₐ[R] S ⊗[R] R)
            (𝔭.symbolicPower n)) := by
            rw [hkernel_source]
    _ = map (algebraMap R S) (𝔭.symbolicPower n) := by
          simpa using tensor_rid_map_includeRight_eq_map
            (R := R) (S := S) (I := 𝔭.symbolicPower n)

/-- Helper for Lemma 10.64.3: the tensor quotient `S ⊗[R] (Rₚ / 𝔭ₚ^n)` identifies with the
semilocal quotient `Sₚ / J^n`, where `J = map (algebraMap S Sₚ) 𝔭S`. -/
noncomputable def tensorQuotientToSemilocalPowQuotientAlgEquiv (n : ℕ) :
    S ⊗[R] (Rₚ ⧸ (map (algebraMap R Rₚ) 𝔭) ^ n) ≃ₐ[S]
      Sₚ ⧸ (map (algebraMap S Sₚ) 𝔭S) ^ n := by
  -- First rewrite the tensor quotient as a quotient of `S ⊗[R] Rₚ`.
  let e₁ :=
    Algebra.TensorProduct.tensorQuotientEquiv (R := R) S Rₚ S
      ((map (algebraMap R Rₚ) 𝔭) ^ n)
  -- Then transport that quotient across the tensor-localization equivalence.
  let e₂ :
      ((S ⊗[R] Rₚ) ⧸
          (((map (algebraMap R Rₚ) 𝔭) ^ n).map
            (tensorLocalizedBaseIncludeRight (R := R) (S := S) (𝔭 := 𝔭)))) ≃ₐ[S]
        (Sₚ ⧸ ((map (algebraMap S Sₚ) 𝔭S) ^ n)) :=
    Ideal.quotientEquivAlg
      ((((map (algebraMap R Rₚ) 𝔭) ^ n).map
        (tensorLocalizedBaseIncludeRight (R := R) (S := S) (𝔭 := 𝔭))))
      (((map (algebraMap S Sₚ) 𝔭S) ^ n))
      (Localization.tensorLeftAlgEquiv (Ideal.primeCompl 𝔭) S)
      (tensorLeftAlgEquiv_map_localized_prime_pow (R := R) (S := S) (𝔭 := 𝔭) n).symm
  exact e₁.trans e₂

/-- Helper for Lemma 10.64.3: the tensor-to-semilocal quotient equivalence sends `includeLeft s`
to the class of `algebraMap S Sₚ s`. -/
@[simp] lemma tensorQuotientToSemilocalPowQuotientAlgEquiv_apply_includeLeft
    (n : ℕ) (s : S) :
    tensorQuotientToSemilocalPowQuotientAlgEquiv (R := R) (S := S) (𝔭 := 𝔭) n
      ((Algebra.TensorProduct.includeLeft : S →ₐ[R]
          S ⊗[R] (Rₚ ⧸ (map (algebraMap R Rₚ) 𝔭) ^ n)) s) =
      Ideal.Quotient.mk ((map (algebraMap S Sₚ) 𝔭S) ^ n) (algebraMap S Sₚ s) := by
  -- The tensor quotient equivalence sends `includeLeft s = s ⊗ 1` to the quotient class of
  -- `s ⊗ 1`, and the tensor-localization equivalence identifies that tensor with `algebraMap s`.
  change
    Ideal.quotientEquivAlg _ _ (Localization.tensorLeftAlgEquiv (Ideal.primeCompl 𝔭) S)
        (tensorLeftAlgEquiv_map_localized_prime_pow (R := R) (S := S) (𝔭 := 𝔭) n).symm
      ((Algebra.TensorProduct.tensorQuotientEquiv (R := R) S Rₚ S
        ((map (algebraMap R Rₚ) 𝔭) ^ n))
        (s ⊗ₜ[R] (Ideal.Quotient.mk ((map (algebraMap R Rₚ) 𝔭) ^ n) (1 : Rₚ)))) =
    Ideal.Quotient.mk ((map (algebraMap S Sₚ) 𝔭S) ^ n) (algebraMap S Sₚ s)
  rw [Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul]
  calc
    Ideal.quotientEquivAlg _ _ (Localization.tensorLeftAlgEquiv (Ideal.primeCompl 𝔭) S)
        (tensorLeftAlgEquiv_map_localized_prime_pow (R := R) (S := S) (𝔭 := 𝔭) n).symm
          (Ideal.Quotient.mk
            (((map (algebraMap R Rₚ) 𝔭) ^ n).map
              (tensorLocalizedBaseIncludeRight (R := R) (S := S) (𝔭 := 𝔭)))
            (s ⊗ₜ[R] (1 : Rₚ)))
        =
          Ideal.Quotient.mk ((map (algebraMap S Sₚ) 𝔭S) ^ n)
            ((Localization.tensorLeftAlgEquiv (Ideal.primeCompl 𝔭) S) (s ⊗ₜ[R] (1 : Rₚ))) := by
              simpa using
                (Ideal.quotientEquivAlg_mk
                  (I := (((map (algebraMap R Rₚ) 𝔭) ^ n).map
                    (tensorLocalizedBaseIncludeRight (R := R) (S := S) (𝔭 := 𝔭))))
                  (J := ((map (algebraMap S Sₚ) 𝔭S) ^ n))
                  (f := Localization.tensorLeftAlgEquiv (Ideal.primeCompl 𝔭) S)
                  (tensorLeftAlgEquiv_map_localized_prime_pow
                    (R := R) (S := S) (𝔭 := 𝔭) n).symm
                  (s ⊗ₜ[R] (1 : Rₚ)))
    _ = Ideal.Quotient.mk ((map (algebraMap S Sₚ) 𝔭S) ^ n) (algebraMap S Sₚ s) := by
          exact congrArg (Ideal.Quotient.mk ((map (algebraMap S Sₚ) 𝔭S) ^ n))
            (Localization.tensorLeftAlgEquiv_apply_tmul_one
              (M := Ideal.primeCompl 𝔭) (S := S) s)

/-- Helper for Lemma 10.64.3: after transporting the tensor quotient to the semilocal quotient,
the source map `includeLeft : S → S ⊗[R] (Rₚ / 𝔭ₚ^n)` becomes the semilocal quotient map. -/
lemma tensorQuotientToSemilocalPowQuotientAlgEquiv_comp_includeLeft (n : ℕ) :
    ((tensorQuotientToSemilocalPowQuotientAlgEquiv (R := R) (S := S) (𝔭 := 𝔭) n).toRingHom).comp
        ((Algebra.TensorProduct.includeLeft : S →ₐ[R]
          S ⊗[R] (Rₚ ⧸ (map (algebraMap R Rₚ) 𝔭) ^ n)).toRingHom) =
      (((Ideal.Quotient.mk ((map (algebraMap S Sₚ) 𝔭S) ^ n))).comp
        (algebraMap S Sₚ)) := by
  -- Equality of ring maps is checked on the source ring `S`.
  ext s
  simpa using
    (tensorQuotientToSemilocalPowQuotientAlgEquiv_apply_includeLeft
      (R := R) (S := S) (𝔭 := 𝔭) n s)

/-- Helper for Lemma 10.64.3: flat base change turns the defining kernel of `𝔭^(n)` into the
kernel of the semilocal quotient map. -/
lemma map_symbolicPower_eq_ker_semilocal_pow_quotient (n : ℕ) :
    map (algebraMap R S) (𝔭.symbolicPower n) =
      RingHom.ker
        (((Ideal.Quotient.mk ((map (algebraMap S Sₚ) 𝔭S) ^ n))).comp
          (algebraMap S Sₚ)) := by
  -- Rewrite the semilocal quotient map as the tensor quotient map followed by the explicit
  -- quotient equivalence constructed above.
  calc
    map (algebraMap R S) (𝔭.symbolicPower n)
        = RingHom.ker
            ((Algebra.TensorProduct.includeLeft : S →ₐ[R]
              S ⊗[R] (Rₚ ⧸ (map (algebraMap R Rₚ) 𝔭) ^ n)).toRingHom) := by
            symm
            exact tensor_quotient_kernel_eq_map_symbolicPower (R := R) (S := S) (𝔭 := 𝔭) n
    _ = RingHom.ker
          (((tensorQuotientToSemilocalPowQuotientAlgEquiv (R := R) (S := S) (𝔭 := 𝔭) n).toRingHom).comp
            ((Algebra.TensorProduct.includeLeft : S →ₐ[R]
              S ⊗[R] (Rₚ ⧸ (map (algebraMap R Rₚ) 𝔭) ^ n)).toRingHom)) := by
            ext s
            constructor
            · intro hs
              change
                tensorQuotientToSemilocalPowQuotientAlgEquiv (R := R) (S := S) (𝔭 := 𝔭) n
                  ((Algebra.TensorProduct.includeLeft : S →ₐ[R]
                    S ⊗[R] (Rₚ ⧸ (map (algebraMap R Rₚ) 𝔭) ^ n)) s) = 0
              simpa [hs]
            · intro hs
              change
                tensorQuotientToSemilocalPowQuotientAlgEquiv (R := R) (S := S) (𝔭 := 𝔭) n
                  ((Algebra.TensorProduct.includeLeft : S →ₐ[R]
                    S ⊗[R] (Rₚ ⧸ (map (algebraMap R Rₚ) 𝔭) ^ n)) s) = 0 at hs
              exact (tensorQuotientToSemilocalPowQuotientAlgEquiv
                (R := R) (S := S) (𝔭 := 𝔭) n).injective <| by
                  simpa using hs
    _ = RingHom.ker
          (((Ideal.Quotient.mk ((map (algebraMap S Sₚ) 𝔭S) ^ n))).comp
            (algebraMap S Sₚ)) := by
            rw [tensorQuotientToSemilocalPowQuotientAlgEquiv_comp_includeLeft
              (R := R) (S := S) (𝔭 := 𝔭) n]

end Ideal

end
