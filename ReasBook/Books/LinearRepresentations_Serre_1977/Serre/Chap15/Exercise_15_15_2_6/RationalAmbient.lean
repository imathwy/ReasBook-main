import LinearRepresentations_Serre_1977.Serre.Chap15.Exercise_15_15_2_6.Foundations

noncomputable section

open LinearMap (BilinForm)
open LinearMap.BilinForm
open scoped Pointwise TensorProduct

universe u v w

section ThompsonExercise

variable {G : Type u} [Group G]
variable {E : Type v} [AddCommGroup E] [Module ℤ E]

section IntegralLatticeAmbient

variable [Module.Free ℤ E] [Module.Finite ℤ E]

/-- Helper for Exercise 15-15.2-6: the coefficient ring `ℤ_(p)` has the same fraction field as
`ℤ`. This closes the ring-side half of Serre's primewise localization route; the remaining
unresolved part of `(b)` is to put the localized module itself inside a compatible
fraction-field representation. -/
theorem prime_local_fraction_field_bridge
    (p : ℕ) [Fact p.Prime] :
    IsFractionRing (Localization.AtPrime (Representation.primeIdeal p)) (FractionRing ℤ) := by
  infer_instance

/-- Helper for Exercise 15-15.2-6: register the standard identification of the fraction field of
`ℤ_(p)` with `ℚ` so the exact-owner base-change map can use ordinary instance search. -/
instance prime_local_fraction_field_instance
    (p : ℕ) [Fact p.Prime] :
    IsFractionRing (Localization.AtPrime (Representation.primeIdeal p)) (FractionRing ℤ) :=
  prime_local_fraction_field_bridge p

/-- Helper for Exercise 15-15.2-6: the prime localization `ℤ_(p)` acts on itself through the
ambient `ℤ`-algebra structure, so the first tensor factor can be treated as an
`ℤ_(p)`-module when building the comparison map to `ℚ ⊗[ℤ] E`. -/
instance prime_localization_self_isScalarTower
    (p : ℕ) [Fact p.Prime] :
    IsScalarTower ℤ (Localization.AtPrime (Representation.primeIdeal p))
      (Localization.AtPrime (Representation.primeIdeal p)) := by
  refine ⟨?_⟩
  intro r a z
  simp [Algebra.smul_def, mul_assoc]

/-- Helper for Exercise 15-15.2-6: the rational tensor ambient is naturally a scalar tower from
`ℤ` through `ℚ`, so localization-spanning lemmas can be applied directly to `ℚ ⊗[ℤ] E`. -/
instance fractionRing_tensor_isScalarTower :
    IsScalarTower ℤ (FractionRing ℤ) (FractionRing ℤ ⊗[ℤ] E) := by
  infer_instance

/-- Helper for Exercise 15-15.2-6: on the rational tensor ambient, the visible `ℤ`-action agrees
with scalar multiplication by the corresponding rational number. -/
theorem fractionRing_tensor_algebraMap_smul
    (r : ℤ) (z : FractionRing ℤ ⊗[ℤ] E) :
    (algebraMap ℤ (FractionRing ℤ) r) • z = r • z := by
  induction z using TensorProduct.induction_on with
  | zero =>
      rw [smul_zero, zsmul_zero]
  | tmul a x =>
      change ((algebraMap ℤ (FractionRing ℤ) r) * a) ⊗ₜ[ℤ] x = (r • a) ⊗ₜ[ℤ] x
      simp [Int.zsmul_eq_mul]
  | add z₁ z₂ hz₁ hz₂ =>
      rw [smul_add, zsmul_add, hz₁, hz₂]

/-- Helper for Exercise 15-15.2-6: the localized tensor product carries its canonical
`ℤ_(p)`-module structure through the left tensor factor. -/
instance prime_localization_tensor_module
    (p : ℕ) [Fact p.Prime] :
    Module (Localization.AtPrime (Representation.primeIdeal p))
      (Localization.AtPrime (Representation.primeIdeal p) ⊗[ℤ] E) := by
  infer_instance

/-- Helper for Exercise 15-15.2-6: the localized tensor owner carries the expected scalar tower
from `ℤ` through `ℤ_(p)`. -/
instance prime_localization_tensor_isScalarTower
    (p : ℕ) [Fact p.Prime] :
    IsScalarTower ℤ (Localization.AtPrime (Representation.primeIdeal p))
      (Localization.AtPrime (Representation.primeIdeal p) ⊗[ℤ] E) := by
  infer_instance

/-- Helper for Exercise 15-15.2-6: the prime-localized module itself carries the expected scalar
tower from `ℤ` through `ℤ_(p)`. -/
instance prime_localized_module_isScalarTower
    (p : ℕ) [Fact p.Prime] :
    IsScalarTower ℤ (Localization.AtPrime (Representation.primeIdeal p))
      (LocalizedModule.AtPrime (Representation.primeIdeal p) E) := by
  infer_instance

/-- Helper for Exercise 15-15.2-6: after identifying `ℤ_(p)` with a subring of `ℚ`, the common
rational tensor ambient carries the induced `ℤ_(p)`-module structure. -/
instance prime_local_fractionRing_tensor_module
    (p : ℕ) [Fact p.Prime] :
    Module (Localization.AtPrime (Representation.primeIdeal p))
      (FractionRing ℤ ⊗[ℤ] E) := by
  infer_instance

/-- Helper for Exercise 15-15.2-6: the rational tensor ambient sits in the scalar tower
`ℤ → ℤ_(p) → ℚ ⊗[ℤ] E`. -/
instance prime_local_fractionRing_tensor_isScalarTower
    (p : ℕ) [Fact p.Prime] :
    IsScalarTower ℤ (Localization.AtPrime (Representation.primeIdeal p))
      (FractionRing ℤ ⊗[ℤ] E) := by
  infer_instance

/-- Helper for Exercise 15-15.2-6: every prime denominator acts invertibly on the common rational
tensor ambient, so the localization universal property can target `ℚ ⊗[ℤ] E` directly. -/
theorem prime_denominator_isUnit_on_fractionRing_tensor
    (p : ℕ) [Fact p.Prime] (s : (Representation.primeIdeal p).primeCompl) :
    IsUnit ((algebraMap ℤ (Module.End ℤ (FractionRing ℤ ⊗[ℤ] E))) s.1) := by
  let M := FractionRing ℤ ⊗[ℤ] E
  have hs_ne_zero : (s : ℤ) ≠ 0 := by
    intro hs_zero
    have hs_mem : (s : ℤ) ∈ Representation.primeIdeal p := by
      simpa [Representation.primeIdeal, hs_zero]
    exact s.2 hs_mem
  have hs_unit_fraction :
      IsUnit (algebraMap ℤ (FractionRing ℤ) s.1) := by
    exact
      IsFractionRing.isUnit_map_of_injective
        (g := algebraMap ℤ (FractionRing ℤ))
        (IsFractionRing.injective ℤ (FractionRing ℤ))
        ⟨s.1, by simpa [mem_nonZeroDivisors_iff_ne_zero] using hs_ne_zero⟩
  let q : FractionRing ℤ := algebraMap ℤ (FractionRing ℤ) s.1
  have hq_ne_zero : q ≠ 0 := by
    simpa [q] using hs_ne_zero
  let invEnd : Module.End ℤ M :=
    { toFun := fun z ↦ q⁻¹ • z
      map_add' := by
        intro z w
        simp [smul_add]
      map_smul' := by
        intro n z
        simpa [smul_smul, mul_comm] using smul_comm (q⁻¹) n z }
  refine ⟨⟨algebraMap ℤ (Module.End ℤ M) s.1, invEnd, ?_, ?_⟩, rfl⟩
  · apply LinearMap.ext
    intro w
    rw [show ((algebraMap ℤ (Module.End ℤ M) s.1) * invEnd) w =
        (algebraMap ℤ (Module.End ℤ M) s.1) (invEnd w) by rfl]
    rw [Module.algebraMap_end_apply]
    rw [show invEnd w = q⁻¹ • w by rfl]
    rw [← fractionRing_tensor_algebraMap_smul (E := E) (s : ℤ) (q⁻¹ • w)]
    rw [show (algebraMap ℤ (FractionRing ℤ) s.1) = q by rfl]
    rw [smul_smul, mul_inv_cancel₀ hq_ne_zero, one_smul]
    simp
  · apply LinearMap.ext
    intro w
    rw [show (invEnd * algebraMap ℤ (Module.End ℤ M) s.1) w =
        invEnd ((algebraMap ℤ (Module.End ℤ M) s.1) w) by rfl]
    rw [Module.algebraMap_end_apply]
    rw [show invEnd ((s : ℤ) • w) = q⁻¹ • ((s : ℤ) • w) by rfl]
    rw [← fractionRing_tensor_algebraMap_smul (E := E) (s : ℤ) w]
    rw [show (algebraMap ℤ (FractionRing ℤ) s.1) = q by rfl]
    rw [smul_smul, inv_mul_cancel₀ hq_ne_zero, one_smul]
    simp

/-- Helper for Exercise 15-15.2-6: the integral inclusion into the rational tensor ambient is the
denominator-`1` leg used in the prime-local comparison map. -/
noncomputable def include_in_fractionRing_tensor :
    E →ₗ[ℤ] FractionRing ℤ ⊗[ℤ] E :=
  (TensorProduct.mk ℤ (FractionRing ℤ) E) 1

/-- Helper for Exercise 15-15.2-6: the literal map `x ↦ 1 ⊗ x` into the rational tensor ambient
is injective. -/
theorem include_in_fractionRing_tensor_injective :
    Function.Injective (include_in_fractionRing_tensor (E := E)) := by
  classical
  let b : Module.Basis (Module.Free.ChooseBasisIndex ℤ E) ℤ E := Module.Free.chooseBasis ℤ E
  intro x y hxy
  change ((1 : FractionRing ℤ) ⊗ₜ[ℤ] x) = ((1 : FractionRing ℤ) ⊗ₜ[ℤ] y) at hxy
  apply b.repr.injective
  ext i
  have hcoord0 := congrArg (fun z ↦ (TensorProduct.equivFinsuppOfBasisRight b z) i) hxy
  have hcoord :
      algebraMap ℤ (FractionRing ℤ) (b.repr x i) =
        algebraMap ℤ (FractionRing ℤ) (b.repr y i) := by
    simpa [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply] using hcoord0
  exact (IsFractionRing.injective ℤ (FractionRing ℤ)) hcoord

/-- Helper for Exercise 15-15.2-6: the localized module itself already maps to the common rational
ambient by the localization universal property, before any tensor-owner comparison is invoked. -/
noncomputable def prime_localization_to_rational_ambient_raw
    (p : ℕ) [Fact p.Prime] :
    LocalizedModule.AtPrime (Representation.primeIdeal p) E →ₗ[ℤ]
      FractionRing ℤ ⊗[ℤ] E :=
  LocalizedModule.lift (S := (Representation.primeIdeal p).primeCompl)
    (include_in_fractionRing_tensor (E := E))
    (prime_denominator_isUnit_on_fractionRing_tensor (E := E) p)

/-- Helper for Exercise 15-15.2-6: first place the prime-local tensor model in the rational
ambient at the `ℤ`-linear level, before upgrading back to `ℤ_(p)`-linearity. -/
noncomputable def localized_at_prime_tensor_to_fractionRing_tensor_raw
    (p : ℕ) [Fact p.Prime] :
    Localization (Representation.primeIdeal p).primeCompl ⊗[ℤ] E →ₗ[ℤ]
      FractionRing ℤ ⊗[ℤ] E :=
  TensorProduct.AlgebraTensorModule.map
    (Algebra.linearMap
      (Localization (Representation.primeIdeal p).primeCompl) (FractionRing ℤ))
    (LinearMap.id : E →ₗ[ℤ] E)

/-- Helper for Exercise 15-15.2-6: the raw `ℤ`-linear tensor leg already sends pure tensors to
the expected scalar multiple of `1 ⊗ x` in the rational ambient. -/
theorem localized_at_prime_tensor_to_fractionRing_tensor_raw_apply_tmul
    (p : ℕ) [Fact p.Prime] (a : Localization (Representation.primeIdeal p).primeCompl) (x : E) :
    localized_at_prime_tensor_to_fractionRing_tensor_raw (E := E) p (a ⊗ₜ[ℤ] x) =
      (algebraMap (Localization (Representation.primeIdeal p).primeCompl) (FractionRing ℤ) a) •
        ((1 : FractionRing ℤ) ⊗ₜ[ℤ] x) := by
  calc
    localized_at_prime_tensor_to_fractionRing_tensor_raw (E := E) p (a ⊗ₜ[ℤ] x) =
        (algebraMap (Localization (Representation.primeIdeal p).primeCompl)
            (FractionRing ℤ) a) ⊗ₜ[ℤ] x := by
          rfl
    _ =
        (algebraMap (Localization (Representation.primeIdeal p).primeCompl)
            (FractionRing ℤ) a) • ((1 : FractionRing ℤ) ⊗ₜ[ℤ] x) := by
          simpa [one_mul] using
            (TensorProduct.smul_tmul'
              (algebraMap (Localization (Representation.primeIdeal p).primeCompl)
                (FractionRing ℤ) a)
              (1 : FractionRing ℤ) x).symm

/-- Helper for Exercise 15-15.2-6: the raw localization lift is already linear for the
`ℤ_(p)`-action on the exact `LocalizedModule` owner, so the repaired ambient map can reuse the
same underlying function without any tensor-owner transport. -/
theorem prime_localization_to_rational_ambient_raw_map_smul
    (p : ℕ) [Fact p.Prime] (a : Localization.AtPrime (Representation.primeIdeal p))
    (z : LocalizedModule.AtPrime (Representation.primeIdeal p) E) :
    prime_localization_to_rational_ambient_raw (E := E) p (a • z) =
      a • prime_localization_to_rational_ambient_raw (E := E) p z := by
  -- Route correction: reduce both the localization scalar and the localized vector to generators,
  -- then compare the scalar factors in the common rational ambient.
  induction a using Localization.induction_on with
  | H y =>
      rcases y with ⟨r, t⟩
      induction z using LocalizedModule.induction_on with
      | h x s =>
          -- Record the raw generator formula locally so this theorem does not depend on later
          -- declarations in the file.
          have hraw_apply_mk
              (x' : E) (s' : (Representation.primeIdeal p).primeCompl) :
              prime_localization_to_rational_ambient_raw (E := E) p (LocalizedModule.mk x' s') =
                (algebraMap (Localization (Representation.primeIdeal p).primeCompl)
                    (FractionRing ℤ) (Localization.mk 1 s')) •
                  ((1 : FractionRing ℤ) ⊗ₜ[ℤ] x') := by
            -- Evaluate the localization lift on a generator, then clear the denominator in the
            -- rational tensor ambient by multiplying back by `s'`.
            rw [show prime_localization_to_rational_ambient_raw (E := E) p
                (LocalizedModule.mk x' s') =
                (prime_denominator_isUnit_on_fractionRing_tensor (E := E) p s').unit⁻¹.val
                  (((TensorProduct.mk ℤ (FractionRing ℤ) E) 1) x') by
                simpa [prime_localization_to_rational_ambient_raw] using
                  (LocalizedModule.lift_mk (S := (Representation.primeIdeal p).primeCompl)
                    (g := include_in_fractionRing_tensor (E := E))
                    (h := prime_denominator_isUnit_on_fractionRing_tensor (E := E) p)
                    x' s')]
            exact
              (Module.End.algebraMap_isUnit_inv_apply_eq_iff
                (S := ℤ)
                (h := prime_denominator_isUnit_on_fractionRing_tensor (E := E) p s')
                (((TensorProduct.mk ℤ (FractionRing ℤ) E) 1) x')
                ((algebraMap (Localization.AtPrime (Representation.primeIdeal p)) (FractionRing ℤ)
                  (Localization.mk 1 s')) • ((1 : FractionRing ℤ) ⊗ₜ[ℤ] x'))).2 <| by
                  change ((1 : FractionRing ℤ) ⊗ₜ[ℤ] x') =
                    (s' : ℤ) •
                      ((algebraMap (Localization.AtPrime (Representation.primeIdeal p))
                        (FractionRing ℤ) (Localization.mk 1 s')) •
                        ((1 : FractionRing ℤ) ⊗ₜ[ℤ] x'))
                  rw [← fractionRing_tensor_algebraMap_smul (E := E) (s' : ℤ)
                    (((algebraMap (Localization.AtPrime (Representation.primeIdeal p))
                      (FractionRing ℤ) (Localization.mk 1 s')) •
                      ((1 : FractionRing ℤ) ⊗ₜ[ℤ] x')))]
                  rw [smul_smul]
                  have hs_mul :
                      (algebraMap ℤ (FractionRing ℤ) s'.1) *
                        (algebraMap (Localization.AtPrime (Representation.primeIdeal p))
                          (FractionRing ℤ) (Localization.mk 1 s')) = 1 := by
                    have hs_local :
                        (Localization.mk 1 s' :
                            Localization.AtPrime (Representation.primeIdeal p)) *
                          algebraMap ℤ (Localization.AtPrime (Representation.primeIdeal p))
                            s'.1 = 1 := by
                      simpa [Localization.mk_eq_mk'] using
                        (IsLocalization.mk'_spec
                          (S := Localization.AtPrime (Representation.primeIdeal p)) (1 : ℤ) s')
                    have hs_frac := congrArg
                      (algebraMap (Localization.AtPrime (Representation.primeIdeal p))
                        (FractionRing ℤ))
                      hs_local
                    simpa [map_mul, mul_comm] using hs_frac
                  rw [hs_mul, one_smul]
          -- Rewrite the scalar action on the localized generator using the concrete `mk` formula.
          have hmk :
              (Localization.mk r t : Localization.AtPrime (Representation.primeIdeal p)) •
                  LocalizedModule.mk x s =
                LocalizedModule.mk (r • x) (t * s) := by
            convert
              (LocalizedModule.mk_smul_mk (S := (Representation.primeIdeal p).primeCompl)
                (r := r) (m := x) (s := t) (t := s)) using 2
            simpa using (int_smul_eq_zsmul (inferInstance : Module ℤ E) r x).symm
          -- Normalize the two localization scalars to the same product in `ℤ_(p)`.
          have hmk_num :
              (Localization.mk r t : Localization.AtPrime (Representation.primeIdeal p)) =
                algebraMap ℤ (Localization.AtPrime (Representation.primeIdeal p)) r *
                  Localization.mk 1 t := by
            simpa [Localization.mk_eq_mk'] using
              (IsLocalization.mk'_eq_mul_mk'_one
                (S := Localization.AtPrime (Representation.primeIdeal p)) r t)
          have hmk_den :
              (Localization.mk 1 (t * s) : Localization.AtPrime (Representation.primeIdeal p)) =
                Localization.mk 1 t * Localization.mk 1 s := by
            simpa [Localization.mk_eq_mk'] using
              (IsLocalization.mk'_mul
                (S := Localization.AtPrime (Representation.primeIdeal p)) 1 1 t s)
          have hscalar_local :
              (Localization.mk 1 (t * s) : Localization.AtPrime (Representation.primeIdeal p)) *
                  algebraMap ℤ (Localization.AtPrime (Representation.primeIdeal p)) r =
                Localization.mk r t * Localization.mk 1 s := by
            calc
              (Localization.mk 1 (t * s) : Localization.AtPrime (Representation.primeIdeal p)) *
                  algebraMap ℤ (Localization.AtPrime (Representation.primeIdeal p)) r =
                algebraMap ℤ (Localization.AtPrime (Representation.primeIdeal p)) r *
                  Localization.mk 1 (t * s) := by
                    rw [mul_comm]
              _ = algebraMap ℤ (Localization.AtPrime (Representation.primeIdeal p)) r *
                    (Localization.mk 1 t * Localization.mk 1 s) := by
                      rw [hmk_den]
              _ = (algebraMap ℤ (Localization.AtPrime (Representation.primeIdeal p)) r *
                    Localization.mk 1 t) * Localization.mk 1 s := by
                      rw [mul_assoc]
              _ = Localization.mk r t * Localization.mk 1 s := by
                    rw [← hmk_num]
          have hscalar_frac :
              (algebraMap (Localization.AtPrime (Representation.primeIdeal p)) (FractionRing ℤ)
                  (Localization.mk 1 (t * s)) *
                algebraMap ℤ (FractionRing ℤ) r) =
              (algebraMap (Localization.AtPrime (Representation.primeIdeal p)) (FractionRing ℤ)
                  (Localization.mk r t) *
                algebraMap (Localization.AtPrime (Representation.primeIdeal p)) (FractionRing ℤ)
                  (Localization.mk 1 s)) := by
            have hmap := congrArg
              (algebraMap (Localization.AtPrime (Representation.primeIdeal p)) (FractionRing ℤ))
              hscalar_local
            simpa [map_mul] using hmap
          -- After evaluating both generator formulas, the remaining equality is the scalar
          -- identity already established in the localized coefficient ring.
          rw [hmk]
          rw [hraw_apply_mk]
          rw [hraw_apply_mk]
          have htensor :
              ((1 : FractionRing ℤ) ⊗ₜ[ℤ] (r • x)) =
                (algebraMap ℤ (FractionRing ℤ) r) • ((1 : FractionRing ℤ) ⊗ₜ[ℤ] x) := by
            -- Move the integral scalar from the right tensor leg into the left coefficient ring.
            change ((TensorProduct.mk ℤ (FractionRing ℤ) E 1) (r • x)) =
              (algebraMap ℤ (FractionRing ℤ) r) • ((1 : FractionRing ℤ) ⊗ₜ[ℤ] x)
            calc
              ((TensorProduct.mk ℤ (FractionRing ℤ) E 1) (r • x)) =
                  (r : ℤ) • ((1 : FractionRing ℤ) ⊗ₜ[ℤ] x) := by
                    simp
              _ = (algebraMap ℤ (FractionRing ℤ) r) • ((1 : FractionRing ℤ) ⊗ₜ[ℤ] x) := by
                    symm
                    exact
                      fractionRing_tensor_algebraMap_smul (E := E) r
                        ((1 : FractionRing ℤ) ⊗ₜ[ℤ] x)
          rw [htensor]
          rw [smul_smul]
          rw [hscalar_frac]
          -- The right-hand scalar action on `ℚ` is the restriction of multiplication by the
          -- image of `Localization.mk r t`, so associativity finishes the comparison.
          change
            ((Localization.mk r t : Localization.AtPrime (Representation.primeIdeal p)) •
              ((algebraMap (Localization.AtPrime (Representation.primeIdeal p)) (FractionRing ℤ)
                (Localization.mk 1 s)))) • ((1 : FractionRing ℤ) ⊗ₜ[ℤ] x) =
              (Localization.mk r t : Localization.AtPrime (Representation.primeIdeal p)) •
                (algebraMap (Localization.AtPrime (Representation.primeIdeal p)) (FractionRing ℤ)
                  (Localization.mk 1 s)) • ((1 : FractionRing ℤ) ⊗ₜ[ℤ] x)
          rw [smul_assoc]

/-- Helper for Exercise 15-15.2-6: the prime-local module maps canonically into the global
fraction-field ambient by first identifying localization with base change and then extending
scalars along `ℤ_(p) → ℚ`. -/
noncomputable def prime_localization_to_rational_ambient
    (p : ℕ) [Fact p.Prime] :
    LocalizedModule (Representation.primeIdeal p).primeCompl E →ₗ[
      Localization (Representation.primeIdeal p).primeCompl] FractionRing ℤ ⊗[ℤ] E :=
  -- Reuse the raw localization lift on the exact owner and record the recovered `ℤ_(p)`-linearity.
  { toFun := prime_localization_to_rational_ambient_raw (E := E) p
    map_add' := (prime_localization_to_rational_ambient_raw (E := E) p).map_add
    map_smul' := prime_localization_to_rational_ambient_raw_map_smul (E := E) p }

/-- Helper for Exercise 15-15.2-6: on a localized generator, the repaired exact-owner ambient map
inverts the denominator in the rational coefficient field and then takes `1 ⊗ x`. -/
theorem prime_localization_to_rational_ambient_apply_mk
    (p : ℕ) [Fact p.Prime] (x : E) (s : (Representation.primeIdeal p).primeCompl) :
    prime_localization_to_rational_ambient (E := E) p (LocalizedModule.mk x s) =
      (algebraMap (Localization (Representation.primeIdeal p).primeCompl) (FractionRing ℤ)
          (Localization.mk 1 s)) • ((1 : FractionRing ℤ) ⊗ₜ[ℤ] x) := by
  -- The repaired exact-owner map has the same underlying function as the raw localization lift,
  -- so we can prove the generator formula directly on that underlying function.
  change prime_localization_to_rational_ambient_raw (E := E) p (LocalizedModule.mk x s) =
    (algebraMap (Localization (Representation.primeIdeal p).primeCompl) (FractionRing ℤ)
      (Localization.mk 1 s)) • ((1 : FractionRing ℤ) ⊗ₜ[ℤ] x)
  rw [show prime_localization_to_rational_ambient_raw (E := E) p (LocalizedModule.mk x s) =
      (prime_denominator_isUnit_on_fractionRing_tensor (E := E) p s).unit⁻¹.val
        (((TensorProduct.mk ℤ (FractionRing ℤ) E) 1) x) by
      simpa [prime_localization_to_rational_ambient_raw] using
        (LocalizedModule.lift_mk (S := (Representation.primeIdeal p).primeCompl)
          (g := include_in_fractionRing_tensor (E := E))
          (h := prime_denominator_isUnit_on_fractionRing_tensor (E := E) p)
          x s)]
  exact
    (Module.End.algebraMap_isUnit_inv_apply_eq_iff
      (S := ℤ)
      (h := prime_denominator_isUnit_on_fractionRing_tensor (E := E) p s)
      (((TensorProduct.mk ℤ (FractionRing ℤ) E) 1) x)
      ((algebraMap (Localization.AtPrime (Representation.primeIdeal p)) (FractionRing ℤ)
        (Localization.mk 1 s)) • ((1 : FractionRing ℤ) ⊗ₜ[ℤ] x))).2 <| by
        change ((1 : FractionRing ℤ) ⊗ₜ[ℤ] x) =
          (s : ℤ) •
            ((algebraMap (Localization.AtPrime (Representation.primeIdeal p)) (FractionRing ℤ)
              (Localization.mk 1 s)) • ((1 : FractionRing ℤ) ⊗ₜ[ℤ] x))
        rw [← fractionRing_tensor_algebraMap_smul (E := E) (s : ℤ)
          (((algebraMap (Localization.AtPrime (Representation.primeIdeal p)) (FractionRing ℤ)
            (Localization.mk 1 s)) • ((1 : FractionRing ℤ) ⊗ₜ[ℤ] x)))]
        rw [smul_smul]
        have hs_mul :
            (algebraMap ℤ (FractionRing ℤ) s.1) *
              (algebraMap (Localization.AtPrime (Representation.primeIdeal p)) (FractionRing ℤ)
                (Localization.mk 1 s)) = 1 := by
          -- The denominator scalar becomes invertible already inside the localization ring.
          have hs_local :
              (Localization.mk 1 s : Localization.AtPrime (Representation.primeIdeal p)) *
                algebraMap ℤ (Localization.AtPrime (Representation.primeIdeal p)) s.1 = 1 := by
            simpa [Localization.mk_eq_mk'] using
              (IsLocalization.mk'_spec (S := Localization.AtPrime (Representation.primeIdeal p))
                (1 : ℤ) s)
          have hs_frac := congrArg
            (algebraMap (Localization.AtPrime (Representation.primeIdeal p)) (FractionRing ℤ))
            hs_local
          simpa [map_mul, mul_comm] using hs_frac
        rw [hs_mul, one_smul]

/-- Helper for Exercise 15-15.2-6: on an integral vector with denominator `1`, the canonical
prime-local comparison map is the expected pure tensor `1 ⊗ x`. -/
@[simp] theorem prime_localization_to_rational_ambient_apply_mk_one
    (p : ℕ) [Fact p.Prime] (x : E) :
    prime_localization_to_rational_ambient (E := E) p (LocalizedModule.mk x 1) =
      (1 : FractionRing ℤ) ⊗ₜ[ℤ] x := by
  -- Specialize the generator formula to denominator `1`, where the scalar is literally `1`.
  rw [prime_localization_to_rational_ambient_apply_mk (E := E) p x (1 : _)]
  have hmk_one :
      (Localization.mk (1 : ℤ) (1 : (Representation.primeIdeal p).primeCompl) :
          Localization.AtPrime (Representation.primeIdeal p)) = 1 := by
    simpa [Localization.mk_eq_mk'] using
      (IsLocalization.mk'_one (S := Localization.AtPrime (Representation.primeIdeal p)) (1 : ℤ))
  rw [hmk_one, map_one, one_smul]

/-- Helper for Exercise 15-15.2-6: the raw localization lift already sends a localized generator
to the expected scalar multiple of `1 ⊗ x` in the rational ambient. -/
theorem prime_localization_to_rational_ambient_raw_apply_mk
    (p : ℕ) [Fact p.Prime] (x : E) (s : (Representation.primeIdeal p).primeCompl) :
    prime_localization_to_rational_ambient_raw (E := E) p (LocalizedModule.mk x s) =
      (algebraMap (Localization (Representation.primeIdeal p).primeCompl) (FractionRing ℤ)
        (Localization.mk 1 s)) • ((1 : FractionRing ℤ) ⊗ₜ[ℤ] x) := by
  -- Reuse the exact-owner generator formula since the repaired map was defined from the raw one.
  simpa [prime_localization_to_rational_ambient] using
    prime_localization_to_rational_ambient_apply_mk (E := E) p x s

/-- Helper for Exercise 15-15.2-6: the raw localization-universal map agrees with the tensor-model
comparison map after restricting scalars back to `ℤ`. -/
theorem prime_localization_to_rational_ambient_restrictScalars_eq_raw
    (p : ℕ) [Fact p.Prime] :
    (prime_localization_to_rational_ambient (E := E) p).restrictScalars ℤ =
      prime_localization_to_rational_ambient_raw (E := E) p := by
  -- The repaired exact-owner map was defined by reusing the raw localization lift as its function.
  rfl

/-- Helper for Exercise 15-15.2-6: on localized generators, the raw localization lift agrees with
the raw tensor-leg comparison map. This is the verified prefix before the remaining owner bridge
for arbitrary localized elements. -/
theorem prime_localization_to_rational_ambient_raw_eq_tensor_comparison
    (p : ℕ) [Fact p.Prime] (x : E) (s : (Representation.primeIdeal p).primeCompl) :
    prime_localization_to_rational_ambient_raw (E := E) p (LocalizedModule.mk x s) =
      localized_at_prime_tensor_to_fractionRing_tensor_raw (E := E) p
        (Localization.mk 1 s ⊗ₜ[ℤ] x) := by
  -- Both maps send a generator to the same scalar multiple of `1 ⊗ x`.
  rw [prime_localization_to_rational_ambient_raw_apply_mk]
  rw [localized_at_prime_tensor_to_fractionRing_tensor_raw_apply_tmul]

/-- Helper for Exercise 15-15.2-6: the tensor-model comparison map from the prime-local module to
the rational ambient is injective. -/
theorem prime_localization_to_rational_ambient_injective
    (p : ℕ) [Fact p.Prime] :
    Function.Injective (prime_localization_to_rational_ambient (E := E) p) := by
  have hraw_injective :
      Function.Injective (prime_localization_to_rational_ambient_raw (E := E) p) := by
    intro z w hzw
    have hsub :
        prime_localization_to_rational_ambient_raw (E := E) p (z - w) = 0 := by
      simpa [map_sub, hzw]
    have hzero : z - w = 0 := by
      revert hsub
      induction (z - w) using LocalizedModule.induction_on with
      | h x s =>
          intro hxs
          rw [prime_localization_to_rational_ambient_raw_apply_mk (E := E) p x s] at hxs
          have hs_unit_local :
              IsUnit (Localization.mk (1 : ℤ) s :
                Localization.AtPrime (Representation.primeIdeal p)) := by
            refine
              ⟨⟨Localization.mk (1 : ℤ) s,
                algebraMap ℤ (Localization.AtPrime (Representation.primeIdeal p)) s.1,
                ?_, ?_⟩, rfl⟩
            · simpa [Localization.mk_eq_mk', mul_comm] using
                (IsLocalization.mk'_spec (S := Localization.AtPrime (Representation.primeIdeal p))
                  (1 : ℤ) s)
            · simpa [Localization.mk_eq_mk', mul_comm] using
                (IsLocalization.mk'_spec (S := Localization.AtPrime (Representation.primeIdeal p))
                  (1 : ℤ) s)
          have hs_unit :
              IsUnit
                (algebraMap (Localization.AtPrime (Representation.primeIdeal p)) (FractionRing ℤ)
                  (Localization.mk (1 : ℤ) s)) := by
            exact hs_unit_local.map
              (algebraMap (Localization.AtPrime (Representation.primeIdeal p)) (FractionRing ℤ))
          have hx_zero : include_in_fractionRing_tensor (E := E) x = 0 := by
            change
              (algebraMap (Localization.AtPrime (Representation.primeIdeal p)) (FractionRing ℤ)
                  (Localization.mk (1 : ℤ) s)) • include_in_fractionRing_tensor (E := E) x = 0 at hxs
            exact (hs_unit.smul_eq_zero.mp hxs)
          have hx_eq_zero : x = 0 := by
            apply include_in_fractionRing_tensor_injective (E := E)
            simpa using hx_zero
          simpa [hx_eq_zero]
    exact sub_eq_zero.mp hzero
  intro z w hzw
  exact hraw_injective (by simpa [prime_localization_to_rational_ambient] using hzw)

/-- Helper for Exercise 15-15.2-6: the raw localization-universal comparison map is injective,
because it is the scalar-restriction of the repaired tensor-model comparison map. -/
theorem prime_localization_to_rational_ambient_raw_injective
    (p : ℕ) [Fact p.Prime] :
    Function.Injective (prime_localization_to_rational_ambient_raw (E := E) p) := by
  -- The raw and exact-owner maps have the same underlying function, so injectivity is the same
  -- statement after forgetting the localized scalar structure.
  intro z w hzw
  exact
    (prime_localization_to_rational_ambient_injective (E := E) p)
      (by simpa [prime_localization_to_rational_ambient_restrictScalars_eq_raw] using hzw)

/-- Helper for Exercise 15-15.2-6: on the common rational tensor ambient, the raw tensor action
coming from `ρ g` is already linear over `ℚ`. -/
theorem fractionRingTensorAction_map_smul
    (ρ : Representation ℤ G E) (g : G) (a : FractionRing ℤ)
    (z : FractionRing ℤ ⊗[ℤ] E) :
    (TensorProduct.map (LinearMap.id : FractionRing ℤ →ₗ[ℤ] FractionRing ℤ) (ρ g)) (a • z) =
      a • (TensorProduct.map (LinearMap.id : FractionRing ℤ →ₗ[ℤ] FractionRing ℤ) (ρ g)) z := by
  -- Verify `ℚ`-linearity on pure tensors and extend by additivity.
  induction z using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul b x =>
      simp [TensorProduct.smul_tmul']
  | add z w hz hw =>
      simp [hz, hw, smul_add]

/-- Helper for Exercise 15-15.2-6: the common rational ambient carries the tensor action of
`ρ g`, fixing the rational coefficient and acting on the integral factor. -/
noncomputable def fractionRingTensorAction
    (ρ : Representation ℤ G E) (g : G) :
    FractionRing ℤ ⊗[ℤ] E →ₗ[FractionRing ℤ] FractionRing ℤ ⊗[ℤ] E :=
  { toFun := fun z ↦
      (TensorProduct.map (LinearMap.id : FractionRing ℤ →ₗ[ℤ] FractionRing ℤ) (ρ g)) z
    map_add' := (TensorProduct.map (LinearMap.id : FractionRing ℤ →ₗ[ℤ] FractionRing ℤ) (ρ g)).map_add
    map_smul' := fractionRingTensorAction_map_smul (ρ := ρ) g }

/-- Helper for Exercise 15-15.2-6: the tensor action of the identity element is the identity map
on the common rational ambient. -/
theorem fractionRingTensorAction_one
    (ρ : Representation ℤ G E) :
    fractionRingTensorAction (ρ := ρ) 1 = 1 := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero =>
      simp [fractionRingTensorAction]
  | tmul a x =>
      simp [fractionRingTensorAction]
  | add z w hz hw =>
      simpa [fractionRingTensorAction, map_add, hz, hw] using congrArg₂ HAdd.hAdd hz hw

/-- Helper for Exercise 15-15.2-6: the tensor actions multiply in the same way as the original
representation operators. -/
theorem fractionRingTensorAction_mul
    (ρ : Representation ℤ G E) (g h : G) :
    fractionRingTensorAction (ρ := ρ) (g * h) =
      fractionRingTensorAction (ρ := ρ) g * fractionRingTensorAction (ρ := ρ) h := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero =>
      simp [fractionRingTensorAction]
  | tmul a x =>
      simp [fractionRingTensorAction]
  | add z w hz hw =>
      simpa [fractionRingTensorAction, map_add, hz, hw] using congrArg₂ HAdd.hAdd hz hw

/-- Helper for Exercise 15-15.2-6: the rational tensor ambient carries the scalar extension of the
original integral representation. -/
def fractionRing_tensor_representation (ρ : Representation ℤ G E) :
    Representation (FractionRing ℤ) G (FractionRing ℤ ⊗[ℤ] E) :=
  -- Route correction: package the scalar extension as the explicit tensor action on the exact
  -- owner, instead of re-entering the old `baseChange` owner mismatch.
  { toFun := fractionRingTensorAction (ρ := ρ)
    map_one' := fractionRingTensorAction_one (ρ := ρ)
    map_mul' := fractionRingTensorAction_mul (ρ := ρ) }

/-- Helper for Exercise 15-15.2-6: the scalar-extended representation acts on pure tensors by
leaving the rational coefficient in place and acting on the integral factor. -/
theorem fractionRing_tensor_representation_apply_tmul
    (ρ : Representation ℤ G E) (g : G) (a : FractionRing ℤ) (x : E) :
    fractionRing_tensor_representation (ρ := ρ) g (a ⊗ₜ[ℤ] x) = a ⊗ₜ[ℤ] (ρ g x) := by
  -- The repaired tensor action fixes the rational coefficient and applies `ρ g` on the right leg.
  rfl

/-- Helper for Exercise 15-15.2-6: the prime-local comparison map intertwines the localized action
of `ρ` with the scalar-extended action on the common rational ambient. -/
theorem prime_localization_to_rational_ambient_is_intertwining
    (ρ : Representation ℤ G E) (p : ℕ) [Fact p.Prime] (g : G)
    (z : LocalizedModule (Representation.primeIdeal p).primeCompl E) :
    prime_localization_to_rational_ambient (E := E) p ((ρ.localizedAtPrime p) g z) =
      fractionRing_tensor_representation (ρ := ρ) g
        (prime_localization_to_rational_ambient (E := E) p z) := by
  -- Compare both sides on localized generators and then use `LocalizedModule.induction_on`.
  induction z using LocalizedModule.induction_on with
  | h x s =>
      simp [Representation.localizedAtPrime, LocalizedModule.map_mk,
        prime_localization_to_rational_ambient_apply_mk,
        fractionRing_tensor_representation_apply_tmul, LinearMap.map_smul_of_tower]

/-- Helper for Exercise 15-15.2-6: the image of the prime-local comparison map already spans the
global rational ambient over `ℚ`, because it contains the pure tensors coming from an integral
basis of `E`. -/
theorem prime_localization_to_rational_ambient_range_span_eq_top
    (p : ℕ) [Fact p.Prime] :
    Submodule.span (FractionRing ℤ)
        ((prime_localization_to_rational_ambient (E := E) p).range :
          Set (FractionRing ℤ ⊗[ℤ] E)) = ⊤ := by
  -- Every pure tensor is a scalar multiple of one coming from the denominator-`1` image, so the
  -- range already spans the whole rational tensor ambient.
  apply eq_top_iff.2
  intro z _
  induction z using TensorProduct.induction_on with
  | zero =>
      exact Submodule.zero_mem _
  | tmul a x =>
      have hx :
          ((1 : FractionRing ℤ) ⊗ₜ[ℤ] x) ∈
            Submodule.span (FractionRing ℤ)
              (((prime_localization_to_rational_ambient
                  (E := E) p).range : Submodule
                    (Localization.AtPrime (Representation.primeIdeal p))
                    (FractionRing ℤ ⊗[ℤ] E)) :
                Set (FractionRing ℤ ⊗[ℤ] E)) := by
        apply Submodule.subset_span
        exact ⟨LocalizedModule.mk x 1,
          prime_localization_to_rational_ambient_apply_mk_one (E := E) p x⟩
      have htmul :
          (a ⊗ₜ[ℤ] x : FractionRing ℤ ⊗[ℤ] E) =
            a • ((1 : FractionRing ℤ) ⊗ₜ[ℤ] x) := by
        simpa [one_mul] using
          (TensorProduct.smul_tmul' a (1 : FractionRing ℤ) x).symm
      rw [htmul]
      exact Submodule.smul_mem _ a hx
  | add z w ihz ihw =>
      exact Submodule.add_mem _ (ihz (by simp)) (ihw (by simp))

/-- Helper for Exercise 15-15.2-6: the image of the prime-local comparison map is a genuine
`ℤ_(p)`-lattice inside the common rational ambient. -/
theorem prime_localization_to_rational_ambient_range_isLattice
    (p : ℕ) [Fact p.Prime] :
    Submodule.IsLattice (FractionRing ℤ)
      ((prime_localization_to_rational_ambient (E := E) p).range) := by
  refine ⟨?_, prime_localization_to_rational_ambient_range_span_eq_top (E := E) p⟩
  -- The range is the image of the finitely generated localized source module.
  rw [LinearMap.range_eq_map]
  exact Submodule.FG.map _ Module.Finite.fg_top

/-- Helper for Exercise 15-15.2-6: the range of the prime-local comparison map is a stable lattice
inside the common rational ambient representation. -/
noncomputable def prime_local_range_stableLattice
    (ρ : Representation ℤ G E) (p : ℕ) [Fact p.Prime] :
    StableLattice (Localization.AtPrime (Representation.primeIdeal p))
      (fractionRing_tensor_representation (ρ := ρ)) :=
  { toSubmodule := (prime_localization_to_rational_ambient (E := E) p).range
    apply_mem_toSubmodule g := by
      rintro _ ⟨z, rfl⟩
      exact ⟨(ρ.localizedAtPrime p) g z,
        prime_localization_to_rational_ambient_is_intertwining (ρ := ρ) (E := E) p g z⟩
    isLattice := prime_localization_to_rational_ambient_range_isLattice (E := E) p }

/-- Helper for Exercise 15-15.2-6: the repaired prime-local comparison map identifies the
localized module with the transported range lattice inside the common rational ambient. -/
noncomputable def prime_localization_to_range_linearEquiv
    (ρ : Representation ℤ G E) (p : ℕ) [Fact p.Prime] :
    LocalizedModule.AtPrime (Representation.primeIdeal p) E ≃ₗ[
      Localization.AtPrime (Representation.primeIdeal p)]
      (prime_local_range_stableLattice (ρ := ρ) p).toSubmodule := by
  -- The codomain is literally the range of the injective prime-local comparison map.
  simpa [prime_local_range_stableLattice] using
    (LinearEquiv.ofInjective (prime_localization_to_rational_ambient (E := E) p)
      (prime_localization_to_rational_ambient_injective (E := E) p))

/-- Helper for Exercise 15-15.2-6: the localized source lattice and the transported range lattice
are intertwined by the repaired prime-local comparison equivalence. -/
theorem prime_localization_to_range_linearEquiv_is_intertwining
    (ρ : Representation ℤ G E) (p : ℕ) [Fact p.Prime] (g : G)
    (x : (ρ.primeStableLattice p).toSubmodule) :
    prime_localization_to_range_linearEquiv (ρ := ρ) p
        ((ρ.primeStableLattice p).toRepresentation g x) =
      (prime_local_range_stableLattice (ρ := ρ) p).toRepresentation g
        (prime_localization_to_range_linearEquiv (ρ := ρ) p x) := by
  -- Compare both lattice elements through their common image in the rational tensor ambient.
  apply Subtype.ext
  change
    prime_localization_to_rational_ambient (E := E) p
        (((ρ.localizedAtPrime p) g) (x : LocalizedModule (Representation.primeIdeal p).primeCompl E)) =
      fractionRing_tensor_representation (ρ := ρ) g
        (prime_localization_to_rational_ambient (E := E) p
          (x : LocalizedModule (Representation.primeIdeal p).primeCompl E))
  exact prime_localization_to_rational_ambient_is_intertwining
    (ρ := ρ) (E := E) p g (x : LocalizedModule (Representation.primeIdeal p).primeCompl E)

/-- Helper for Exercise 15-15.2-6: a thin local wrapper around the generic reduction-transport
equivalence keeps later prime-local applications in a stable elaboration normal form. -/
theorem reductionNonemptyEquivOfIntertwiningWrapper
    {A : Type*} [CommRing A] [IsLocalRing A]
    {K₁ : Type*} [CommRing K₁] [Algebra A K₁]
    {V₁ : Type*} [AddCommGroup V₁] [Module A V₁] [Module K₁ V₁]
    [IsScalarTower A K₁ V₁]
    {K₂ : Type*} [CommRing K₂] [Algebra A K₂]
    {V₂ : Type*} [AddCommGroup V₂] [Module A V₂] [Module K₂ V₂]
    [IsScalarTower A K₂ V₂]
    {ρ₁ : Representation K₁ G V₁} {ρ₂ : Representation K₂ G V₂}
    {L₁ : StableLattice A ρ₁} {L₂ : StableLattice A ρ₂}
    (e : L₁.toSubmodule ≃ₗ[A] L₂.toSubmodule)
    (he : ∀ g : G, ∀ x : L₁.toSubmodule,
      e (L₁.toRepresentation g x) = L₂.toRepresentation g (e x)) :
    Nonempty (L₁.reductionRepresentation.Equiv L₂.reductionRepresentation) := by
  -- Route correction: the reduction transport only depends on the common local ring `A`, so we
  -- rebuild it here without forcing the two ambient coefficient rings to coincide.
  have hmap :
      L₁.maximalIdealSubmodule.map e.toLinearMap = L₂.maximalIdealSubmodule := by
    rw [StableLattice.maximalIdealSubmodule, StableLattice.maximalIdealSubmodule,
      Submodule.map_smul'']
    have htop : (⊤ : Submodule A L₁.toSubmodule).map e.toLinearMap = ⊤ := by
      rw [Submodule.map_top]
      exact LinearMap.range_eq_top.2 e.surjective
    simp [htop]
  let eA : L₁.reduction ≃ₗ[A] L₂.reduction :=
    Submodule.Quotient.equiv L₁.maximalIdealSubmodule L₂.maximalIdealSubmodule e hmap
  have heA_apply (x : L₁.toSubmodule) :
      eA (Submodule.Quotient.mk x : L₁.reduction) =
        (Submodule.Quotient.mk (e x) : L₂.reduction) := by
    simp [eA, Submodule.Quotient.equiv_apply]
  let eRed : L₁.reduction ≃ₗ[IsLocalRing.ResidueField A] L₂.reduction :=
    { toFun := eA
      invFun := eA.symm
      left_inv := eA.left_inv
      right_inv := eA.right_inv
      map_add' := eA.map_add
      map_smul' := by
        intro c x
        refine Quotient.inductionOn' c ?_
        intro a
        refine Quotient.inductionOn' x ?_
        intro y
        change
          eA ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a :
              IsLocalRing.ResidueField A) •
            (Submodule.Quotient.mk y : L₁.reduction)) =
            _
        rw [StableLattice.reduction_smul_mk (L := L₁) a y]
        rw [heA_apply]
        calc
          (Submodule.Quotient.mk (e (a • y)) : L₂.reduction) =
              (Submodule.Quotient.mk (a • e y) : L₂.reduction) := by
                simp
          _ =
              (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a :
                IsLocalRing.ResidueField A) •
                (Submodule.Quotient.mk (e y) : L₂.reduction) := by
                  rw [StableLattice.reduction_smul_mk (L := L₂)]
          _ =
              (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a :
                IsLocalRing.ResidueField A) • eA (Submodule.Quotient.mk y : L₁.reduction) := by
                  rw [heA_apply] }
  let f :
      L₁.reductionRepresentation.IntertwiningMap L₂.reductionRepresentation :=
    eRed.toLinearMap.intertwiningMap_of_isIntertwiningMap
      L₁.reductionRepresentation L₂.reductionRepresentation
      (fun g x ↦ by
        refine Quotient.inductionOn' x ?_
        intro y
        -- Check intertwining on represented quotient classes, where both actions are explicit.
        change
          eRed ((L₁.reductionRepresentation g) (Submodule.Quotient.mk y : L₁.reduction)) =
            (L₂.reductionRepresentation g)
              (eRed (Submodule.Quotient.mk y : L₁.reduction))
        rw [StableLattice.reductionRepresentation_apply_mk]
        simpa [eRed, heA_apply, StableLattice.reductionRepresentation_apply_mk, he g y])
  exact ⟨f.ofBijective eRed.bijective⟩

/-- Helper for Exercise 15-15.2-6: after passing to quotient classes, the prime-local comparison
map already satisfies the required reduction-level intertwining identity on represented classes. -/
theorem primeLocalRangeReduction_apply_mk
    (ρ : Representation ℤ G E) (p : ℕ) [Fact p.Prime] (g : G)
    (x : (ρ.primeStableLattice p).toSubmodule) :
    (Submodule.Quotient.mk
        (prime_localization_to_range_linearEquiv (ρ := ρ) p
          ((ρ.primeStableLattice p).toRepresentation g x)) :
        (prime_local_range_stableLattice (ρ := ρ) p).reduction) =
      (prime_local_range_stableLattice (ρ := ρ) p).reductionRepresentation g
        (Submodule.Quotient.mk
          (prime_localization_to_range_linearEquiv (ρ := ρ) p x) :
          (prime_local_range_stableLattice (ρ := ρ) p).reduction) := by
  -- The reduced target action on a represented class is still the quotient class upstairs.
  rw [StableLattice.reductionRepresentation_apply_mk]
  congr 1
  exact
    prime_localization_to_range_linearEquiv_is_intertwining
      (ρ := ρ) (E := E) p g x

/-- Helper for Exercise 15-15.2-6: the canonical prime-local comparison first identifies the top
source lattice `ρ.primeStableLattice p` with the localized module itself, and then with the
transported range lattice in the common rational ambient. -/
noncomputable def primeLocalRangeTopLinearEquiv
    (ρ : Representation ℤ G E) (p : ℕ) [Fact p.Prime] :
    (ρ.primeStableLattice p).toSubmodule ≃ₗ[Localization.AtPrime (Representation.primeIdeal p)]
      (prime_local_range_stableLattice (ρ := ρ) p).toSubmodule := by
  -- `ρ.primeStableLattice p` is literally the top localized lattice, so `Submodule.topEquiv`
  -- reduces the source owner to the ambient localized module.
  simpa [Representation.primeStableLattice] using
    ((Submodule.topEquiv :
        (⊤ : Submodule (Localization.AtPrime (Representation.primeIdeal p))
          (LocalizedModule.AtPrime (Representation.primeIdeal p) E)) ≃ₗ[
            Localization.AtPrime (Representation.primeIdeal p)]
          LocalizedModule.AtPrime (Representation.primeIdeal p) E).trans
      (prime_localization_to_range_linearEquiv (ρ := ρ) p))

/-- Helper for Exercise 15-15.2-6: the stabilized top-lattice comparison equivalence still
intertwines the localized action with the transported range-lattice action. -/
theorem primeLocalRangeTopLinearEquiv_is_intertwining
    (ρ : Representation ℤ G E) (p : ℕ) [Fact p.Prime] (g : G)
    (x : (ρ.primeStableLattice p).toSubmodule) :
    primeLocalRangeTopLinearEquiv (ρ := ρ) (E := E) p
        ((ρ.primeStableLattice p).toRepresentation g x) =
      (prime_local_range_stableLattice (ρ := ρ) p).toRepresentation g
        (primeLocalRangeTopLinearEquiv (ρ := ρ) (E := E) p x) := by
  -- `primeLocalRangeTopLinearEquiv` only inserts the top-lattice identification on the source.
  simpa [primeLocalRangeTopLinearEquiv, Representation.primeStableLattice] using
    prime_localization_to_range_linearEquiv_is_intertwining
      (ρ := ρ) (E := E) p g x

/-- Helper for Exercise 15-15.2-6: descending the prime-local comparison equivalence modulo the
maximal ideal yields an equivalence of the two prime-local reduction representations. -/
private noncomputable def primeLocalSourceLattice
    (ρ : Representation ℤ G E) (p : ℕ) [Fact p.Prime] :
    StableLattice (Localization.AtPrime (Representation.primeIdeal p)) (ρ.localizedAtPrime p) :=
  ρ.primeStableLattice p

/-- Helper for Exercise 15-15.2-6: descending the prime-local comparison equivalence modulo the
maximal ideal yields an equivalence of the two prime-local reduction representations. -/
private noncomputable def primeLocalTargetLattice
    (ρ : Representation ℤ G E) (p : ℕ) [Fact p.Prime] :
    StableLattice (Localization.AtPrime (Representation.primeIdeal p))
      (fractionRing_tensor_representation (ρ := ρ)) :=
  prime_local_range_stableLattice (ρ := ρ) p

/-- Helper for Exercise 15-15.2-6: descending the prime-local comparison equivalence modulo the
maximal ideal yields an equivalence of the two prime-local reduction representations. -/
private noncomputable def primeLocalRangeTopLinearEquivCached
    (ρ : Representation ℤ G E) (p : ℕ) [Fact p.Prime] :
    (primeLocalSourceLattice (ρ := ρ) p).toSubmodule ≃ₗ[
      Localization.AtPrime (Representation.primeIdeal p)]
      (primeLocalTargetLattice (ρ := ρ) p).toSubmodule := by
  -- Freeze the source and target lattice owners before descending to the reduction.
  simpa [primeLocalSourceLattice, primeLocalTargetLattice] using
    primeLocalRangeTopLinearEquiv (ρ := ρ) (E := E) p

/-- Helper for Exercise 15-15.2-6: descending the prime-local comparison equivalence modulo the
maximal ideal yields an equivalence of the two prime-local reduction representations. -/
private theorem primeLocalRangeTopLinearEquivCached_is_intertwining
    (ρ : Representation ℤ G E) (p : ℕ) [Fact p.Prime] (g : G)
    (x : (primeLocalSourceLattice (ρ := ρ) p).toSubmodule) :
    primeLocalRangeTopLinearEquivCached (ρ := ρ) (E := E) p
        ((primeLocalSourceLattice (ρ := ρ) p).toRepresentation g x) =
      (primeLocalTargetLattice (ρ := ρ) p).toRepresentation g
        (primeLocalRangeTopLinearEquivCached (ρ := ρ) (E := E) p x) := by
  -- The cached source and target owners preserve the same top-lattice intertwining statement.
  simpa [primeLocalRangeTopLinearEquivCached, primeLocalSourceLattice,
    primeLocalTargetLattice] using
    primeLocalRangeTopLinearEquiv_is_intertwining (ρ := ρ) (E := E) p g x

/-- Helper for Exercise 15-15.2-6: descending the prime-local comparison equivalence modulo the
maximal ideal yields an equivalence of the two prime-local reduction representations. -/
private theorem primeLocalRangeReductionEquivCached
    (ρ : Representation ℤ G E) (p : ℕ) [Fact p.Prime] :
    Nonempty ((primeLocalSourceLattice (ρ := ρ) p).reductionRepresentation.Equiv
      (primeLocalTargetLattice (ρ := ρ) p).reductionRepresentation) := by
  -- Descend the cached intertwining equivalence directly on the frozen source and target owners.
  exact
    reductionNonemptyEquivOfIntertwiningWrapper
      (primeLocalRangeTopLinearEquivCached (ρ := ρ) (E := E) p)
      (primeLocalRangeTopLinearEquivCached_is_intertwining (ρ := ρ) (E := E) p)

/-- Helper for Exercise 15-15.2-6: descending the prime-local comparison equivalence modulo the
maximal ideal yields an equivalence of the two prime-local reduction representations. -/
theorem prime_local_range_reduction_equiv
    (ρ : Representation ℤ G E) (p : ℕ) [Fact p.Prime] :
    Nonempty ((ρ.primeStableLattice p).reductionRepresentation.Equiv
      (prime_local_range_stableLattice (ρ := ρ) p).reductionRepresentation) := by
  -- Route correction: consume the cached reduction equivalence on the frozen owners and rewrite
  -- only at the public boundary.
  simpa [primeLocalSourceLattice, primeLocalTargetLattice] using
    primeLocalRangeReductionEquivCached (ρ := ρ) (E := E) p

/-- Helper for Exercise 15-15.2-6: the transported range lattice has irreducible reduction at
every prime because it is equivalent to the canonical prime reduction of `ρ`. -/
theorem prime_local_range_reduction_isIrreducible
    (ρ : Representation ℤ G E) (hρ : ρ.HasSimplePrimeReductions) (p : ℕ) [Fact p.Prime] :
    (prime_local_range_stableLattice (ρ := ρ) p).reductionRepresentation.IsIrreducible := by
  letI : (ρ.primeStableLattice p).reductionRepresentation.IsIrreducible :=
    hρ.irreducible p
  exact Representation.isIrreducible_of_nonempty_equiv
    (ρ := (ρ.primeStableLattice p).reductionRepresentation)
    (σ := (prime_local_range_stableLattice (ρ := ρ) p).reductionRepresentation)
    (prime_local_range_reduction_equiv (ρ := ρ) (E := E) p)

end IntegralLatticeAmbient

end ThompsonExercise
