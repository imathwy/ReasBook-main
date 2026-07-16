import stacks_proof.stacks_project.Chap10.Lemma_10_108_6.MultilinearBaseChange

universe u v w z

open PrimeSpectrum
open TensorProduct.AlgebraTensorModule

section

variable {R : Type u} [CommRing R]

/-- Helper for Chap10 Lemma 10 108 6: restrict scalars on the `A`-exterior power along
`R → A`. -/
local instance baseChangeExteriorPowerModule
    {A : Type w} [CommRing A] [Algebra R A]
    {M : Type v} [AddCommGroup M] [Module R M] (n : ℕ) :
    Module R (⋀[A]^n (TensorProduct R A M)) :=
  Module.compHom _ (algebraMap R A)

/-- Helper for Chap10 Lemma 10 108 6: the restricted and original scalar actions on the
`A`-exterior power form a scalar tower. -/
local instance baseChangeExteriorPowerIsScalarTower
    {A : Type w} [CommRing A] [Algebra R A]
    {M : Type v} [AddCommGroup M] [Module R M] (n : ℕ) :
    IsScalarTower R A (⋀[A]^n (TensorProduct R A M)) :=
  IsScalarTower.of_compHom R A _

/-- Helper for Chap10 Lemma 10 108 6: multiplying the exterior generator of `1 ⊗ m` by the
product of the scalars is the exterior generator of the scaled pure tensors. -/
theorem exteriorPower_ιMulti_smul_one_tmul
    {A : Type w} [CommRing A] [Algebra R A]
    {M : Type v} [AddCommGroup M] [Module R M]
    (n : ℕ) (a : Fin n → A) (m : Fin n → M) :
    (∏ j, a j) • (exteriorPower.ιMulti A n) (fun i => (1 : A) ⊗ₜ[R] m i) =
      (exteriorPower.ιMulti A n) (fun j => a j ⊗ₜ[R] m j) := by
  classical
  -- First move the product of scalars into the alternating map coordinatewise.
  calc
    (∏ j, a j) • (exteriorPower.ιMulti A n) (fun i => (1 : A) ⊗ₜ[R] m i) =
        (exteriorPower.ιMulti A n) (fun i => a i • ((1 : A) ⊗ₜ[R] m i)) := by
          symm
          exact AlternatingMap.map_smul_univ (exteriorPower.ιMulti A n) a
            (fun i => (1 : A) ⊗ₜ[R] m i)
    _ = (exteriorPower.ιMulti A n) (fun j => a j ⊗ₜ[R] m j) := by
          -- Each coordinate scalar action on `A ⊗[R] M` is scalar multiplication on the left
          -- tensor factor.
          congr 1
          funext j
          simpa using (TensorProduct.smul_tmul' (R := R) (R' := A)
            (r := a j) (m := (1 : A)) (n := m j))

/-- Helper for Chap10 Lemma 10 108 6: the `R`-alternating map that sends an `M`-tuple to its
exterior product after applying `m ↦ 1 ⊗ m`. -/
noncomputable def baseChangeExteriorPowerForwardMultilinear
    {A : Type w} [CommRing A] [Algebra R A]
    {M : Type v} [AddCommGroup M] [Module R M] (n : ℕ) :
    MultilinearMap R (fun _ : Fin n => M) (⋀[A]^n (TensorProduct R A M)) :=
  ((exteriorPower.ιMulti A n (M := TensorProduct R A M)).toMultilinearMap.restrictScalars R).compLinearMap
    (fun _ => TensorProduct.mk R A M 1)

/-- Helper for Chap10 Lemma 10 108 6: the forward base-change multilinear map is alternating. -/
theorem baseChangeExteriorPowerForward_map_eq_zero
    {A : Type w} [CommRing A] [Algebra R A]
    {M : Type v} [AddCommGroup M] [Module R M] (n : ℕ) :
    ∀ (v : Fin n → M) (i j : Fin n), v i = v j → i ≠ j →
      baseChangeExteriorPowerForwardMultilinear (R := R) (A := A) (M := M) n v = 0 := by
  -- Alternation is inherited from the exterior-power generator over `A`.
  intro v i j hv hij
  have hTensor : (1 : A) ⊗ₜ[R] v i = (1 : A) ⊗ₜ[R] v j := by rw [hv]
  simpa [baseChangeExteriorPowerForwardMultilinear, MultilinearMap.compLinearMap_apply] using
    (exteriorPower.ιMulti A n (M := TensorProduct R A M)).map_eq_zero_of_eq
      (fun k => (1 : A) ⊗ₜ[R] v k) hTensor hij

/-- Helper for Chap10 Lemma 10 108 6: the forward alternating map defining exterior-power
base change. -/
noncomputable def baseChangeExteriorPowerForwardAlternatingMap
    {A : Type w} [CommRing A] [Algebra R A]
    {M : Type v} [AddCommGroup M] [Module R M] (n : ℕ) :
    M [⋀^Fin n]→ₗ[R] (⋀[A]^n (TensorProduct R A M)) :=
  { baseChangeExteriorPowerForwardMultilinear (R := R) (A := A) (M := M) n with
    map_eq_zero_of_eq' := baseChangeExteriorPowerForward_map_eq_zero (R := R) (A := A) n }

/-- Helper for Chap10 Lemma 10 108 6: the forward linear map
`A ⊗[R] ⋀[R]^n M → ⋀[A]^n (A ⊗[R] M)`. -/
noncomputable def baseChangeExteriorPowerForward
    {A : Type w} [CommRing A] [Algebra R A]
    {M : Type v} [AddCommGroup M] [Module R M] (n : ℕ) :
    TensorProduct R A (⋀[R]^n M) →ₗ[A] ⋀[A]^n (TensorProduct R A M) :=
  (exteriorPower.alternatingMapLinearEquiv
    (baseChangeExteriorPowerForwardAlternatingMap (R := R) (A := A) (M := M) n)).liftBaseChange A

/-- Helper for Chap10 Lemma 10 108 6: the backward alternating map
`(A ⊗[R] M)^n → A ⊗[R] ⋀[R]^n M`. -/
noncomputable def baseChangeExteriorPowerBackwardAlternatingMap
    {A : Type w} [CommRing A] [Algebra R A]
    {M : Type v} [AddCommGroup M] [Module R M] (n : ℕ) :
    (TensorProduct R A M) [⋀^Fin n]→ₗ[A] TensorProduct R A (⋀[R]^n M) :=
  baseChangeAlternatingMap (R := R) (A := A) (M := M)
    (N := TensorProduct R A (⋀[R]^n M)) n
    ((TensorProduct.mk R A (⋀[R]^n M) 1).compAlternatingMap (exteriorPower.ιMulti R n))

/-- Helper for Chap10 Lemma 10 108 6: the backward linear map
`⋀[A]^n (A ⊗[R] M) → A ⊗[R] ⋀[R]^n M`. -/
noncomputable def baseChangeExteriorPowerBackward
    {A : Type w} [CommRing A] [Algebra R A]
    {M : Type v} [AddCommGroup M] [Module R M] (n : ℕ) :
    ⋀[A]^n (TensorProduct R A M) →ₗ[A] TensorProduct R A (⋀[R]^n M) :=
  exteriorPower.alternatingMapLinearEquiv
    (baseChangeExteriorPowerBackwardAlternatingMap (R := R) (A := A) (M := M) n)

/-- Helper for Chap10 Lemma 10 108 6: the backward base-change map is a left inverse to the
forward map. -/
theorem baseChangeExteriorPower_left_inverse
    {A : Type w} [CommRing A] [Algebra R A]
    {M : Type v} [AddCommGroup M] [Module R M] (n : ℕ) :
    baseChangeExteriorPowerBackward (R := R) (A := A) (M := M) n ∘ₗ
      baseChangeExteriorPowerForward (R := R) (A := A) (M := M) n =
        LinearMap.id := by
  -- It is enough to compare on pure tensors and then on exterior generators in the right factor.
  apply TensorProduct.AlgebraTensorModule.ext
  intro a x
  let F : ⋀[R]^n M →ₗ[R] TensorProduct R A (⋀[R]^n M) :=
    ((baseChangeExteriorPowerBackward (R := R) (A := A) (M := M) n ∘ₗ
      baseChangeExteriorPowerForward (R := R) (A := A) (M := M) n).restrictScalars R).comp
        (TensorProduct.mk R A (⋀[R]^n M) a)
  let G : ⋀[R]^n M →ₗ[R] TensorProduct R A (⋀[R]^n M) :=
    TensorProduct.mk R A (⋀[R]^n M) a
  have hFG : F = G := by
    -- The exterior-power universal property reduces the comparison to pure wedge generators.
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro m
    simp [F, G, baseChangeExteriorPowerForward, baseChangeExteriorPowerBackward,
      baseChangeExteriorPowerForwardAlternatingMap, baseChangeExteriorPowerBackwardAlternatingMap,
      baseChangeExteriorPowerForwardMultilinear, baseChangeAlternatingMap_apply_pure]
    simpa using (TensorProduct.smul_tmul' (R := R) (R' := A)
      (r := a) (m := (1 : A)) (n := (exteriorPower.ιMulti R n) m))
  exact LinearMap.congr_fun hFG x

/-- Helper for Chap10 Lemma 10 108 6: the forward base-change map is a left inverse to the
backward map. -/
theorem baseChangeExteriorPower_right_inverse
    {A : Type w} [CommRing A] [Algebra R A]
    {M : Type v} [AddCommGroup M] [Module R M] (n : ℕ) :
    baseChangeExteriorPowerForward (R := R) (A := A) (M := M) n ∘ₗ
      baseChangeExteriorPowerBackward (R := R) (A := A) (M := M) n =
        LinearMap.id := by
  -- The target exterior power is generated by pure wedges, and each tensor-product coordinate is
  -- generated by pure tensors.
  apply exteriorPower.linearMap_ext
  apply alternatingMap_tensorProduct_ext_pure (R := R) (A := A) (M := M)
  intro a m
  simpa [baseChangeExteriorPowerForward, baseChangeExteriorPowerBackward,
    baseChangeExteriorPowerForwardAlternatingMap, baseChangeExteriorPowerBackwardAlternatingMap,
    baseChangeExteriorPowerForwardMultilinear, baseChangeAlternatingMap_apply_pure] using
    exteriorPower_ιMulti_smul_one_tmul (R := R) (A := A) (M := M) n a m

/-- Helper for Chap10 Lemma 10 108 6: fixed-degree exterior powers commute with scalar
extension. -/
noncomputable def baseChangeExteriorPowerLinearEquiv
    {A : Type w} [CommRing A] [Algebra R A]
    {M : Type v} [AddCommGroup M] [Module R M] (n : ℕ) :
    TensorProduct R A (⋀[R]^n M) ≃ₗ[A] ⋀[A]^n (TensorProduct R A M) :=
  LinearEquiv.ofLinear
    (baseChangeExteriorPowerForward (R := R) (A := A) (M := M) n)
    (baseChangeExteriorPowerBackward (R := R) (A := A) (M := M) n)
    (baseChangeExteriorPower_right_inverse (R := R) (A := A) (M := M) n)
    (baseChangeExteriorPower_left_inverse (R := R) (A := A) (M := M) n)

/-- Helper for Chap10 Lemma 10 108 6: the uncurried multilinear map associated to a curried
family of alternating maps vanishes on repeated first-tail entries. -/
theorem alternatingMap_uncurryLeft_map_eq_zero
    {A : Type w} [CommRing A]
    {V : Type v} [AddCommGroup V] [Module A V]
    {N : Type z} [AddCommGroup N] [Module A N]
    {n : ℕ} (f : V →ₗ[A] V [⋀^Fin n]→ₗ[A] N)
    (hdiag : ∀ (x : V) (v : Fin n → V) (i : Fin n), v i = x → f x v = 0)
    (v : Fin (n + 1) → V) (i j : Fin (n + 1)) (hv : v i = v j) (hij : i ≠ j) :
    LinearMap.uncurryLeft (R := A) (M := fun _ : Fin (n + 1) => V) (M₂ := N)
      ((AlternatingMap.toMultilinearMapLM :
        (V [⋀^Fin n]→ₗ[A] N) →ₗ[A] MultilinearMap A (fun _ : Fin n => V) N).comp f) v = 0 := by
  -- Split according to whether the repeated entries occur in the first coordinate or the tail.
  cases i using Fin.cases with
  | zero =>
      cases j using Fin.cases with
      | zero => exact (hij rfl).elim
      | succ j =>
          rw [LinearMap.uncurryLeft_apply]
          exact hdiag (v 0) (Fin.tail v) j (by simpa [Fin.tail] using hv.symm)
  | succ i =>
      cases j using Fin.cases with
      | zero =>
          rw [LinearMap.uncurryLeft_apply]
          exact hdiag (v 0) (Fin.tail v) i (by simpa [Fin.tail] using hv)
      | succ j =>
          rw [LinearMap.uncurryLeft_apply]
          exact (f (v 0)).map_eq_zero_of_eq (Fin.tail v)
            (by simpa [Fin.tail] using hv)
            (by intro hij'; exact hij (by simpa using congrArg Fin.succ hij'))

/-- Helper for Chap10 Lemma 10 108 6: uncurry a linear family of alternating maps once the
first-tail diagonal vanishing condition is known. -/
noncomputable def alternatingMapOfCurryLeft
    {A : Type w} [CommRing A]
    {V : Type v} [AddCommGroup V] [Module A V]
    {N : Type z} [AddCommGroup N] [Module A N]
    {n : ℕ} (f : V →ₗ[A] V [⋀^Fin n]→ₗ[A] N)
    (hdiag : ∀ (x : V) (v : Fin n → V) (i : Fin n), v i = x → f x v = 0) :
    V [⋀^Fin (n + 1)]→ₗ[A] N :=
  { LinearMap.uncurryLeft (R := A) (M := fun _ : Fin (n + 1) => V) (M₂ := N)
      ((AlternatingMap.toMultilinearMapLM :
        (V [⋀^Fin n]→ₗ[A] N) →ₗ[A] MultilinearMap A (fun _ : Fin n => V) N).comp f) with
    map_eq_zero_of_eq' := alternatingMap_uncurryLeft_map_eq_zero f hdiag }

/-- Helper for Chap10 Lemma 10 108 6: after tensoring with a residue field, exterior powers
commute with base change in a fixed degree. -/
noncomputable def residueFieldTensorExteriorPowerEquiv
    {M : Type v} [AddCommGroup M] [Module R M] (p : PrimeSpectrum R) (i : ℕ) :
    TensorProduct R p.asIdeal.ResidueField (⋀[R]^i M) ≃ₗ[p.asIdeal.ResidueField]
      ⋀[p.asIdeal.ResidueField]^i (TensorProduct R p.asIdeal.ResidueField M) :=
  baseChangeExteriorPowerLinearEquiv (R := R) (A := p.asIdeal.ResidueField) (M := M) i

/-- Helper for Chap10 Lemma 10 108 6: an exterior power of a finite-dimensional vector space is
nonzero exactly up to the vector-space dimension. -/
theorem nontrivial_exteriorPower_iff_le_finrank
    {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    [Module.Finite K V] (i : ℕ) :
    Nontrivial (⋀[K]^i V) ↔ i ≤ Module.finrank K V := by
  -- Over a field the module is free, so nontriviality is detected by positive finrank.
  letI : Module.Free K V := Module.Free.of_divisionRing K V
  letI : Module.Free K (⋀[K]^i V) := inferInstance
  letI : Module.Finite K (⋀[K]^i V) := inferInstance
  rw [← Module.finrank_pos_iff_of_free (R := K) (M := ⋀[K]^i V)]
  -- The exterior-power finrank is the binomial coefficient, which is positive exactly when
  -- the exterior degree is at most the ambient dimension.
  rw [exteriorPower.finrank_eq]
  rw [Nat.pos_iff_ne_zero, Nat.choose_ne_zero_iff]
end
