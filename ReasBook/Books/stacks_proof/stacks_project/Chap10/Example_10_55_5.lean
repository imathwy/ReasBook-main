import stacks_proof.stacks_project.Chap10.Example_10_55_5.Index
-- Declarations for this item will be appended below by the statement pipeline.
noncomputable section
open scoped TensorProduct CategoryTheory
universe u
section
variable (k : Type u) [Field k]
local notation "R" => equal_endpoint_poly_subring k
local notation "K0→K0'" =>
  ModulePropertyK0.map R (finiteProjectiveModuleProperty_le_isFG R)
-- Proof sketch: classify finitely generated projective modules over
-- `R = {f ∈ k[x] | f(0) = f(1)}` by rank together with a unit parameter, and identify `K'_0(R)`
-- with `ℤ` via the finite-module Grothendieck group used canonically in this chapter.
/-- Helper for Example 10.55.5: tensoring a finite `R`-module with the endpoint field produces a
endpoint-supported module, so its class already vanishes in `K'_0(R)`. -/
private theorem equal_endpoint_tensor_field_class_eq_zero
    (M : FGModuleCat.{u, u} R) :
    finiteGrothendieckGroupOf R (FGModuleCat.of R (k ⊗[R] M.obj)) = 0 := by
  -- The tensor product is an endpoint-field module; the existing endpoint-supported vanishing
  -- theorem applies after installing the finite `R`-module instance for this literal owner.
  let _ : Module.Finite R (k ⊗[R] M.obj) :=
    equal_endpoint_tensor_field_module_finite (k := k) M
  exact equal_endpoint_endpoint_supported_class_eq_zero (k := k) (V := k ⊗[R] M.obj)

/-- Helper for Example 10.55.5: the conductor polynomial `X^2 - X` vanishes at both endpoints, so
every one of its multiples lies in the equal-endpoint ring. -/
private theorem equal_endpoint_conductor_mul_mem (q : Polynomial k) :
    ((Polynomial.X ^ 2 - Polynomial.X) * q : Polynomial k) ∈ R := by
  -- The conductor factor evaluates to `0` at both `0` and `1`, so the product has equal endpoint
  -- values.
  rw [mem_equal_endpoint_poly_subring_iff]
  simp

/-- Helper for Example 10.55.5: the conductor polynomial factors as `X (X - 1)`. -/
private theorem equal_endpoint_conductor_factor :
    (Polynomial.X ^ 2 - Polynomial.X : Polynomial k) =
      Polynomial.X * (Polynomial.X - Polynomial.C (1 : k)) := by
  calc
    (Polynomial.X ^ 2 - Polynomial.X : Polynomial k) =
        Polynomial.X * Polynomial.X - Polynomial.X * Polynomial.C (1 : k) := by
      simp [pow_two]
    _ = Polynomial.X * (Polynomial.X - Polynomial.C (1 : k)) := by
      ring

/-- Helper for Example 10.55.5: the conductor polynomial is nonzero. -/
private theorem equal_endpoint_conductor_ne_zero :
    (Polynomial.X ^ 2 - Polynomial.X : Polynomial k) ≠ 0 := by
  rw [equal_endpoint_conductor_factor (k := k)]
  exact mul_ne_zero Polynomial.X_ne_zero (Polynomial.X_sub_C_ne_zero (1 : k))

/-- Helper for Example 10.55.5: an equal-endpoint polynomial vanishing at `0` is divisible by the
conductor `X^2 - X`. -/
private theorem equal_endpoint_conductor_dvd_of_endpoint_zero (r : R)
    (h0 : (r : Polynomial k).eval 0 = 0) :
    (Polynomial.X ^ 2 - Polynomial.X : Polynomial k) ∣ (r : Polynomial k) := by
  have h1 : (r : Polynomial k).eval 1 = 0 := by
    have hr_eq :
        (r : Polynomial k).eval 0 = (r : Polynomial k).eval 1 :=
      (mem_equal_endpoint_poly_subring_iff (k := k) (r : Polynomial k)).mp r.2
    calc
      (r : Polynomial k).eval 1 = (r : Polynomial k).eval 0 := hr_eq.symm
      _ = 0 := h0
  have hX : Polynomial.X ∣ (r : Polynomial k) := by
    apply Polynomial.X_dvd_iff.mpr
    simpa [Polynomial.coeff_zero_eq_eval_zero] using h0
  have hX1 : Polynomial.X - Polynomial.C (1 : k) ∣ (r : Polynomial k) := by
    simpa [h1] using
      (Polynomial.X_sub_C_dvd_sub_C_eval (p := (r : Polynomial k)) (a := (1 : k)))
  have hcoprime : IsCoprime (Polynomial.X : Polynomial k) (Polynomial.X - Polynomial.C (1 : k)) := by
    simpa using
      (Polynomial.isCoprime_X_sub_C_of_isUnit_sub
        (a := (0 : k)) (b := (1 : k))
        (show IsUnit ((0 : k) - 1) by
          exact isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr zero_ne_one)))
  rcases hcoprime.mul_dvd hX hX1 with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  calc
    (r : Polynomial k) = (Polynomial.X * (Polynomial.X - Polynomial.C (1 : k))) * q := by
      simpa [mul_assoc] using hq
    _ = (Polynomial.X ^ 2 - Polynomial.X) * q := by
      rw [equal_endpoint_conductor_factor (k := k)]

/-- Helper for Example 10.55.5: endpoint evaluation zero is exactly the conductor-divisibility
condition needed for the source-faithful exact row. -/
private theorem equal_endpoint_conductor_dvd_of_eval_zero (r : R)
    (hr : equal_endpoint_eval k r = 0) :
    (Polynomial.X ^ 2 - Polynomial.X : Polynomial k) ∣ (r : Polynomial k) := by
  -- Reinterpret the endpoint-evaluation kernel as vanishing at `0`, then apply the coprime-factor
  -- divisibility argument from the source proof.
  have h0 : (r : Polynomial k).eval 0 = 0 := by
    simpa [Polynomial.coeff_zero_eq_eval_zero, equal_endpoint_eval] using hr
  exact equal_endpoint_conductor_dvd_of_endpoint_zero (k := k) r h0

/-- Helper for Example 10.55.5: the normalization `k[X]`, viewed as its regular module over
itself, packaged as an object of `FGModuleCat (Polynomial k)`. -/
private noncomputable def equal_endpoint_polynomial_regular_fgModule :
    FGModuleCat (Polynomial k) :=
  letI : Module (Polynomial k) (Polynomial k) := Semiring.toModule
  letI : Module.Finite (Polynomial k) (Polynomial k) := Module.Finite.self (Polynomial k)
  FGModuleCat.of (Polynomial k) (Polynomial k)

/-- Helper for Example 10.55.5: fix the normalization object `k[X]|_R` on the exact restricted
owner used by the conductor row. -/
private noncomputable abbrev equal_endpoint_conductor_source : FGModuleCat R :=
  -- Route correction: keep the restricted-scalars owner, but make it reducible so the conductor
  -- map sees the literal polynomial carrier and shares the support-file scalar-action normal form.
  equal_endpoint_restrictScalars_object (k := k)
    (equal_endpoint_polynomial_regular_fgModule (k := k))

/-- Helper for Example 10.55.5: multiplication by the conductor `X^2 - X` defines the left map in
the source short exact row `0 → k[X] → R → k → 0`. -/
private theorem equal_endpoint_conductor_mul_smul
    (r : R) (q : Polynomial k) :
    ((Polynomial.X ^ 2 - Polynomial.X) * (r • q : Polynomial k) : Polynomial k) =
      ((r : Polynomial k) * ((Polynomial.X ^ 2 - Polynomial.X) * q) : Polynomial k) := by
  -- The conductor product commutes with the restricted `R`-action because both are ordinary
  -- polynomial multiplication after scalar restriction.
  rw [equal_endpoint_polynomial_smul]
  ring

/-- Helper for Example 10.55.5: the conductor multiplication formula is additive on the literal
carrier owner `k[X]|_R`. -/
private theorem equal_endpoint_conductor_linearMap_map_add
    (q₁ q₂ : Polynomial k) :
    ((⟨(Polynomial.X ^ 2 - Polynomial.X) * (q₁ + q₂),
        equal_endpoint_conductor_mul_mem (k := k) (q₁ + q₂)⟩ : R)) =
      (⟨(Polynomial.X ^ 2 - Polynomial.X) * q₁,
          equal_endpoint_conductor_mul_mem (k := k) q₁⟩ : R) +
        ⟨(Polynomial.X ^ 2 - Polynomial.X) * q₂,
          equal_endpoint_conductor_mul_mem (k := k) q₂⟩ := by
  -- The conductor multiplier is an ambient polynomial multiplication map, so additivity is
  -- checked on underlying polynomials.
  apply Subtype.ext
  simp [mul_add]

/-- Helper for Example 10.55.5: the conductor multiplication formula is `R`-linear on the literal
carrier owner `k[X]|_R`. -/
private theorem equal_endpoint_conductor_linearMap_map_smul
    (r : R) (q : Polynomial k) :
    ((⟨(Polynomial.X ^ 2 - Polynomial.X) * (r • q : Polynomial k),
        equal_endpoint_conductor_mul_mem (k := k) (r • q : Polynomial k)⟩ : R)) =
      r • (⟨(Polynomial.X ^ 2 - Polynomial.X) * q,
        equal_endpoint_conductor_mul_mem (k := k) q⟩ : R) := by
  -- The `R`-action on both sides is still ambient polynomial multiplication after restriction of
  -- scalars.
  apply Subtype.ext
  exact equal_endpoint_conductor_mul_smul (k := k) r q

/-- Helper for Example 10.55.5: multiplication by the conductor `X^2 - X` defines the left map in
the source short exact row `0 → k[X] → R → k → 0`. -/
private noncomputable def equal_endpoint_conductor_linearMap :
    equal_endpoint_conductor_source (k := k) →ₗ[R] R :=
  { toFun := fun (q : Polynomial k) =>
      ⟨(Polynomial.X ^ 2 - Polynomial.X) * q,
        equal_endpoint_conductor_mul_mem (k := k) q⟩
    map_add' := fun (q₁ : Polynomial k) (q₂ : Polynomial k) =>
      equal_endpoint_conductor_linearMap_map_add (k := k)
        q₁ q₂
    map_smul' := fun r (q : Polynomial k) =>
      equal_endpoint_conductor_linearMap_map_smul (k := k) r q }

/-- Helper for Example 10.55.5: endpoint evaluation is the right map in the source short exact row
`0 → k[X] → R → k → 0`. -/
private noncomputable def equal_endpoint_eval_linearMap : R →ₗ[R] k where
  toFun := equal_endpoint_eval k
  map_add' r s := by
    -- Endpoint evaluation is already additive as a ring homomorphism.
    exact (equal_endpoint_eval k).map_add r s
  map_smul' r s := by
    -- The codomain scalar action is defined through the same endpoint-evaluation homomorphism.
    change equal_endpoint_eval k (r * s) = r • equal_endpoint_eval k s
    rw [equal_endpoint_eval_smul]
    simpa using (equal_endpoint_eval k).map_mul r s

/-- Helper for Example 10.55.5: endpoint evaluation kills every multiple of the conductor
polynomial. -/
private theorem equal_endpoint_conductor_image_eval_zero (q : Polynomial k) :
    equal_endpoint_eval k
        ⟨(Polynomial.X ^ 2 - Polynomial.X) * q, equal_endpoint_conductor_mul_mem (k := k) q⟩ = 0 := by
  -- Evaluating a conductor multiple at the common endpoint kills the conductor factor.
  simp [equal_endpoint_eval]

/-- Helper for Example 10.55.5: in the conductor row, endpoint evaluation annihilates the image
of conductor multiplication. -/
private theorem equal_endpoint_conductor_shortComplex_zero :
    (equal_endpoint_eval_linearMap (k := k)).comp (equal_endpoint_conductor_linearMap (k := k)) = 0 := by
  -- The zero composite is checked after applying both linear maps to a polynomial source element.
  ext q
  exact equal_endpoint_conductor_image_eval_zero (k := k) (q : Polynomial k)

/-- Helper for Example 10.55.5: the conductor linear map as a bundled morphism of finite
`R`-modules. -/
private noncomputable abbrev equal_endpoint_conductor_hom :
    equal_endpoint_conductor_source (k := k) ⟶ FGModuleCat.of R R :=
  CategoryTheory.ConcreteCategory.ofHom (equal_endpoint_conductor_linearMap (k := k))

/-- Helper for Example 10.55.5: endpoint evaluation as a bundled morphism of finite
`R`-modules. -/
private noncomputable abbrev equal_endpoint_eval_hom :
    FGModuleCat.of R R ⟶ FGModuleCat.of R k :=
  CategoryTheory.ConcreteCategory.ofHom (equal_endpoint_eval_linearMap (k := k))

/-- Helper for Example 10.55.5: the linear zero-composite upgrades to the bundled finite-module
category. -/
private theorem equal_endpoint_conductor_shortComplex_zero_hom :
    ((equal_endpoint_conductor_hom (k := k)) ≫ (equal_endpoint_eval_hom (k := k))) = 0 := by
  -- The bundled morphism equality is extensional on source elements and reduces to the linear
  -- zero-composite already proved.
  ext q
  exact LinearMap.congr_fun (equal_endpoint_conductor_shortComplex_zero (k := k)) q

/-- Helper for Example 10.55.5: the conductor row
`0 → k[X]|_R --(X^2-X)--> R --ev--> k → 0` packaged in `FGModuleCat R`. -/
private noncomputable def equal_endpoint_conductor_shortComplex :
    CategoryTheory.ShortComplex (FGModuleCat R) :=
  { X₁ := equal_endpoint_conductor_source (k := k)
    X₂ := FGModuleCat.of R R
    X₃ := FGModuleCat.of R k
    f := equal_endpoint_conductor_hom (k := k)
    g := equal_endpoint_eval_hom (k := k)
    zero := equal_endpoint_conductor_shortComplex_zero_hom (k := k) }

/-- Helper for Example 10.55.5: conductor multiplication is injective on `k[X]` because the
conductor polynomial is nonzero. -/
private theorem equal_endpoint_conductor_linearMap_injective :
    Function.Injective (equal_endpoint_conductor_linearMap (k := k)) := by
  -- After applying the map, equality in the subring is equality of polynomial products; cancel
  -- the nonzero conductor factor.
  intro q₁ q₂ h
  apply mul_left_cancel₀ (equal_endpoint_conductor_ne_zero (k := k))
  exact congrArg Subtype.val h

/-- Helper for Example 10.55.5: endpoint evaluation on the equal-endpoint ring is surjective,
realized by constant polynomials. -/
private theorem equal_endpoint_eval_linearMap_surjective :
    Function.Surjective (equal_endpoint_eval_linearMap (k := k)) := by
  intro a
  refine ⟨equal_endpoint_constant (k := k) a, ?_⟩
  -- Constant polynomials evaluate to the chosen scalar.
  simp [equal_endpoint_eval_linearMap, equal_endpoint_eval, equal_endpoint_constant]

/-- Helper for Example 10.55.5: the underlying ring map `R → k` is surjective. -/
private theorem equal_endpoint_eval_surjective :
    Function.Surjective (equal_endpoint_eval k) := by
  intro a
  refine ⟨equal_endpoint_constant (k := k) a, ?_⟩
  -- The same constant-polynomial witness already realizes surjectivity on the ring level.
  simp [equal_endpoint_eval, equal_endpoint_constant]

/-- Helper for Example 10.55.5: the kernel of endpoint evaluation is exactly the conductor image
inside the equal-endpoint ring. -/
private theorem equal_endpoint_eval_ker_eq_conductor_range :
    ((RingHom.ker (equal_endpoint_eval k) : Ideal R) : Submodule R R) =
      LinearMap.range (equal_endpoint_conductor_linearMap (k := k)) := by
  -- The forward inclusion divides by the conductor; the reverse inclusion uses that conductor
  -- multiples evaluate to zero.
  ext r
  constructor
  · intro hr
    have hev : equal_endpoint_eval k r = 0 := by
      simpa [RingHom.mem_ker] using hr
    rcases equal_endpoint_conductor_dvd_of_eval_zero (k := k) r hev with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    apply Subtype.ext
    exact hq.symm
  · rintro ⟨q, hq⟩
    have hzero : equal_endpoint_eval k ((equal_endpoint_conductor_linearMap (k := k)) q) = 0 := by
      exact equal_endpoint_conductor_image_eval_zero (k := k) (q : Polynomial k)
    have hker : equal_endpoint_eval k r = 0 := by
      rw [← hq]
      exact hzero
    simpa [RingHom.mem_ker] using hker

/-- Helper for Example 10.55.5: quotienting the equal-endpoint ring by the conductor kernel
recovers the endpoint field `k`. -/
private noncomputable def equal_endpoint_conductor_quotient_equiv_field :
    (R ⧸ RingHom.ker (equal_endpoint_eval k)) ≃+* k :=
  (equal_endpoint_eval k).quotientKerEquivOfSurjective
    (equal_endpoint_eval_surjective (k := k))

/-- Helper for Example 10.55.5: the conductor-quotient equivalence sends the class of `r` to its
endpoint value. -/
private theorem equal_endpoint_conductor_quotient_equiv_field_apply_mk (r : R) :
    equal_endpoint_conductor_quotient_equiv_field (k := k)
        (Ideal.Quotient.mk (RingHom.ker (equal_endpoint_eval k)) r) =
      equal_endpoint_eval k r := by
  -- This is the defining computation rule for the first-isomorphism-theorem equivalence.
  simpa [equal_endpoint_conductor_quotient_equiv_field] using
    RingHom.quotientKerEquivOfSurjective_apply_mk
      (f := equal_endpoint_eval k)
      (equal_endpoint_eval_surjective (k := k))
      r

/-- Helper for Chap10 Example 10 55 5: an `R`-module annihilated by the endpoint-evaluation
kernel is endpoint-supported, hence has zero class in `K'_0(R)`. -/
private theorem equal_endpoint_evalKernel_torsion_class_eq_zero
    (V : Type u) [AddCommGroup V] [Module R V] [Module.Finite R V]
    (hV : Module.IsTorsionBySet R V (RingHom.ker (equal_endpoint_eval k))) :
    finiteGrothendieckGroupOf R (FGModuleCat.of R V) = 0 := by
  let Q : Type u := R ⧸ RingHom.ker (equal_endpoint_eval k)
  letI : Module Q V := Module.IsTorsionBySet.module hV
  letI : IsScalarTower R Q V := Module.IsTorsionBySet.isScalarTower hV
  letI : Module k V :=
    Module.compHom V (equal_endpoint_conductor_quotient_equiv_field (k := k)).symm.toRingHom
  have hTower : IsScalarTower R k V := by
    -- The quotient action transported to `k` agrees with the original `R`-action through endpoint
    -- evaluation, because the quotient equivalence sends `mk r` to `eval(r)`.
    refine IsScalarTower.of_algebraMap_smul fun r v => ?_
    change
      ((equal_endpoint_conductor_quotient_equiv_field (k := k)).symm
          (equal_endpoint_eval k r)) • v = r • v
    have hmk :
        (equal_endpoint_conductor_quotient_equiv_field (k := k)).symm
            (equal_endpoint_eval k r) =
          Ideal.Quotient.mk (RingHom.ker (equal_endpoint_eval k)) r := by
      simpa [equal_endpoint_conductor_quotient_equiv_field] using
        (RingHom.quotientKerEquivOfSurjective_symm_apply
          (equal_endpoint_eval_surjective (k := k)) r)
    rw [hmk]
    exact Module.IsTorsionBySet.mk_smul hV r v
  letI : IsScalarTower R k V := hTower
  letI : SMulCommClass R k V := inferInstance
  -- Once the action factors through `k`, the already-proved endpoint-supported vanishing theorem
  -- applies to this finite module owner.
  exact equal_endpoint_endpoint_supported_class_eq_zero (k := k) (V := V)

/-- Helper for Example 10.55.5: the conductor map and endpoint evaluation form an exact pair on
the carrier-level source row `k[X] → R → k`. -/
private theorem equal_endpoint_conductor_eval_exact :
    Function.Exact
      (equal_endpoint_conductor_linearMap (k := k))
      (equal_endpoint_eval_linearMap (k := k)) := by
  -- Exactness is precisely the equality between the kernel of evaluation and the conductor range.
  rw [LinearMap.exact_iff]
  exact equal_endpoint_eval_ker_eq_conductor_range (k := k)

private theorem equal_endpoint_conductor_shortExact :
    ((equal_endpoint_conductor_shortComplex (k := k)).map (ModuleCat.isFG R).ι).ShortExact := by
  -- The bundled row is short exact because the underlying linear maps are exact, injective, and
  -- surjective.
  refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
  · exact equal_endpoint_conductor_eval_exact (k := k)
  · exact equal_endpoint_conductor_linearMap_injective (k := k)
  · exact equal_endpoint_eval_linearMap_surjective (k := k)

/-- The generic-rank invariant on finite `R`-modules, computed after base change to the fraction
field of `R`. -/
private noncomputable def equalEndpointRank (M : FGModuleCat R) : ℤ :=
  let _ : Module.Finite R M.obj := M.property
  (Module.finrank (FractionRing R) ((FractionRing R) ⊗[R] M.obj) : ℤ)

/-- Helper for Example 10.55.5: the tensorized short complex over `FractionRing R`. -/
private noncomputable def equal_endpoint_fractionRing_tensor_shortComplex
    (S : CategoryTheory.ShortComplex (FGModuleCat R)) :
    CategoryTheory.ShortComplex (ModuleCat (FractionRing R)) :=
  let U : CategoryTheory.ShortComplex (ModuleCat R) := S.map (ModuleCat.isFG R).ι
  { X₁ := ModuleCat.of (FractionRing R) ((FractionRing R) ⊗[R] U.X₁)
    X₂ := ModuleCat.of (FractionRing R) ((FractionRing R) ⊗[R] U.X₂)
    X₃ := ModuleCat.of (FractionRing R) ((FractionRing R) ⊗[R] U.X₃)
    f := ModuleCat.ofHom (LinearMap.lTensor (FractionRing R) U.f.hom)
    g := ModuleCat.ofHom (LinearMap.lTensor (FractionRing R) U.g.hom)
    zero := by
      -- The tensorized maps still compose to zero because `lTensor` respects composition.
      apply ModuleCat.hom_ext
      let hzero : U.g.hom.comp U.f.hom = 0 := by
        ext x
        simpa [LinearMap.comp_apply] using U.moduleCat_zero_apply x
      ext x
      simpa [LinearMap.comp_apply, LinearMap.lTensor_comp] using
        LinearMap.congr_fun (congrArg (LinearMap.lTensor (FractionRing R)) hzero) x }

/-- Helper for Example 10.55.5: tensoring a short exact sequence of finite `R`-modules with the
fraction field produces a short exact sequence of `FractionRing R`-modules. -/
private theorem equal_endpoint_fractionRing_tensor_shortExact
    (S : CategoryTheory.ShortComplex (FGModuleCat R))
    (hS : (S.map (ModuleCat.isFG R).ι).ShortExact) :
    (equal_endpoint_fractionRing_tensor_shortComplex (k := k) S).ShortExact := by
  let U : CategoryTheory.ShortComplex (ModuleCat R) := S.map (ModuleCat.isFG R).ι
  -- Repackage the tensorized row in `ModuleCat` so the exactness and mono/epi bridges apply
  -- directly to the underlying linear maps.
  refine ModuleCat.shortComplex_shortExact
      (equal_endpoint_fractionRing_tensor_shortComplex (k := k) S) ?_ ?_ ?_
  · have hExactBase : Function.Exact U.f.hom U.g.hom := by
      exact (CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact U).1 hS.exact
    -- Flat base change to the fraction field preserves exactness of the middle row.
    simpa [equal_endpoint_fractionRing_tensor_shortComplex, U] using
      (Module.Flat.lTensor_exact (FractionRing R) hExactBase)
  · have hf : Function.Injective U.f.hom := by
      simpa [U] using hS.moduleCat_injective_f
    -- Flatness also preserves injectivity of the first map after tensoring.
    simpa [equal_endpoint_fractionRing_tensor_shortComplex, U] using
      (Module.Flat.lTensor_preserves_injective_linearMap
        (M := FractionRing R) U.f.hom hf)
  · have hg : Function.Surjective U.g.hom := by
      simpa [U] using hS.moduleCat_surjective_g
    -- Right exactness of tensor product gives surjectivity of the last map.
    simpa [equal_endpoint_fractionRing_tensor_shortComplex, U] using
      (LinearMap.lTensor_surjective (FractionRing R) hg)

/-- Helper for Example 10.55.5: generic rank is additive on short exact sequences of finite
`R`-modules after tensoring with the fraction field. -/
private theorem equalEndpointRank_respects_shortExact
    (S : CategoryTheory.ShortComplex (FGModuleCat R))
    (hS : (S.map (ModuleCat.isFG R).ι).ShortExact) :
    equalEndpointRank k S.X₂ =
      equalEndpointRank k S.X₁ + equalEndpointRank k S.X₃ := by
  let T : CategoryTheory.ShortComplex (ModuleCat (FractionRing R)) :=
    equal_endpoint_fractionRing_tensor_shortComplex (k := k) S
  have hT : T.ShortExact := by
    simpa [T] using equal_endpoint_fractionRing_tensor_shortExact (k := k) S hS
  -- The tensor factors are finite-dimensional vector spaces over the fraction field, so the
  -- standard short-exact finrank additivity theorem applies to the tensorized row.
  let _ : Module.Finite (FractionRing R) T.X₁ := by
    let U : CategoryTheory.ShortComplex (ModuleCat R) := S.map (ModuleCat.isFG R).ι
    let _ : Module.Finite R U.X₁ := by
      simpa [U] using (inferInstance : Module.Finite R S.X₁.obj)
    simpa [T, U, equal_endpoint_fractionRing_tensor_shortComplex] using
      (inferInstance : Module.Finite (FractionRing R) ((FractionRing R) ⊗[R] U.X₁))
  let _ : Module.Finite (FractionRing R) T.X₃ := by
    let U : CategoryTheory.ShortComplex (ModuleCat R) := S.map (ModuleCat.isFG R).ι
    let _ : Module.Finite R U.X₃ := by
      simpa [U] using (inferInstance : Module.Finite R S.X₃.obj)
    simpa [T, U, equal_endpoint_fractionRing_tensor_shortComplex] using
      (inferInstance : Module.Finite (FractionRing R) ((FractionRing R) ⊗[R] U.X₃))
  let _ : Module.Finite (FractionRing R) T.X₂ := by
    let U : CategoryTheory.ShortComplex (ModuleCat R) := S.map (ModuleCat.isFG R).ι
    let _ : Module.Finite R U.X₂ := by
      simpa [U] using (inferInstance : Module.Finite R S.X₂.obj)
    simpa [T, U, equal_endpoint_fractionRing_tensor_shortComplex] using
      (inferInstance : Module.Finite (FractionRing R) ((FractionRing R) ⊗[R] U.X₂))
  let _ : Module.Free (FractionRing R) T.X₁ :=
    Module.Free.of_divisionRing (FractionRing R) T.X₁
  let _ : Module.Free (FractionRing R) T.X₃ :=
    Module.Free.of_divisionRing (FractionRing R) T.X₃
  let _ : Module.Free (FractionRing R) T.X₂ :=
    Module.Free.of_divisionRing (FractionRing R) T.X₂
  have hfinrank :
      Module.finrank (FractionRing R) T.X₂ =
        Module.finrank (FractionRing R) T.X₁ + Module.finrank (FractionRing R) T.X₃ := by
    simpa [T] using
      (ModuleCat.free_shortExact_finrank_add (S := T) hT rfl rfl)
  let _ : Module.Free (FractionRing R) ((FractionRing R) ⊗[R] S.X₁.obj) :=
    Module.Free.of_divisionRing (FractionRing R) ((FractionRing R) ⊗[R] S.X₁.obj)
  let _ : Module.Free (FractionRing R) ((FractionRing R) ⊗[R] S.X₂.obj) :=
    Module.Free.of_divisionRing (FractionRing R) ((FractionRing R) ⊗[R] S.X₂.obj)
  let _ : Module.Free (FractionRing R) ((FractionRing R) ⊗[R] S.X₃.obj) :=
    Module.Free.of_divisionRing (FractionRing R) ((FractionRing R) ⊗[R] S.X₃.obj)
  -- Cast the finite-dimensional equality from `ℕ` to `ℤ` to match `equalEndpointRank`.
  simpa [equalEndpointRank, T, Nat.cast_add] using
    congrArg (fun n : ℕ ↦ (n : ℤ)) hfinrank

/-- The Grothendieck relations for finite `R`-modules lie in the kernel of the generic-rank
functional. -/
private theorem equalEndpointRelations_le_ker_rank :
    modulePropertyK0Relations R (ModuleCat.isFG R) ≤
      (FreeAbelianGroup.lift (equalEndpointRank k)).ker := by
  rw [modulePropertyK0Relations, AddSubgroup.closure_le]
  rintro _ ⟨⟨S, hS⟩, rfl⟩
  change
    FreeAbelianGroup.lift (equalEndpointRank k)
      (FreeAbelianGroup.of S.X₂ - FreeAbelianGroup.of S.X₁ - FreeAbelianGroup.of S.X₃) = 0
  simp only [FreeAbelianGroup.lift_apply_of, map_sub]
  have hrank :
      equalEndpointRank k S.X₂ =
        equalEndpointRank k S.X₁ + equalEndpointRank k S.X₃ :=
    equalEndpointRank_respects_shortExact (k := k) S hS
  -- Each defining Grothendieck relation maps to the additive rank identity from the short exact
  -- sequence.
  rw [hrank]
  abel

/-- The generic-rank map `K'_0(R) → ℤ` for the equal-endpoint ring. -/
private noncomputable def equalEndpointRankMap :
    finiteGrothendieckGroup R →+ ℤ :=
  ModulePropertyK0.lift R (equalEndpointRank k)
    (equalEndpointRelations_le_ker_rank k)

/-- Helper for Example 10.55.5: the descended generic-rank map evaluates on a generator class by
the original generic rank. -/
private theorem equalEndpointRankMap_apply_of
    (M : FGModuleCat R) :
    equalEndpointRankMap k (finiteGrothendieckGroupOf R M) = equalEndpointRank k M := by
  -- The quotient lift defining `equalEndpointRankMap` agrees with the generator-level invariant.
  simpa using ModulePropertyK0.lift_of R
    (equalEndpointRank k)
    (equalEndpointRelations_le_ker_rank k)
    M

/-- Helper for Example 10.55.5: the Grothendieck class of the free rank-one module over the
equal-endpoint ring. -/
private noncomputable def equal_endpoint_free_class : finiteGrothendieckGroup R :=
  finiteGrothendieckGroupOf R (FGModuleCat.of R R)

/-- Helper for Example 10.55.5: the free rank-one class has generic rank `1`. -/
private theorem equal_endpoint_free_class_rank :
    equalEndpointRankMap k (equal_endpoint_free_class k) = 1 := by
  -- Evaluate the descended rank map on the free generator class.
  simpa [equal_endpoint_free_class, equalEndpointRank, Module.finrank_tensorProduct,
    Module.finrank_self] using
    (equalEndpointRankMap_apply_of (k := k) (FGModuleCat.of R R))

/-- Helper for Example 10.55.5: the conductor short exact row identifies the normalization class
`[k[X]]` over `R` with the free rank-one class `[R]` in `K'_0(R)`. -/
private theorem equal_endpoint_polynomial_class_eq_free_class :
    finiteGrothendieckGroupOf R (equal_endpoint_conductor_source (k := k)) =
      equal_endpoint_free_class k := by
  -- The conductor short exact relation says `[R] = [k[X]] + [k]`; the endpoint field term has
  -- zero class, so the normalization class equals the free class.
  have hrel :
      equal_endpoint_free_class k =
        finiteGrothendieckGroupOf R (equal_endpoint_conductor_source (k := k)) +
          finiteGrothendieckGroupOf R (FGModuleCat.of R k) := by
    simpa [equal_endpoint_conductor_shortComplex, equal_endpoint_free_class,
      finiteGrothendieckGroupOf] using
      ModulePropertyK0.of_shortExact R
        (equal_endpoint_conductor_shortComplex (k := k))
        (equal_endpoint_conductor_shortExact (k := k))
  rw [equal_endpoint_field_class_eq_zero] at hrel
  simpa using hrel.symm

/-- Helper for Chap10 Example 10 55 5: tensoring the conductor inclusion with a finite
`R`-module gives the canonical comparison from the normalization tensor back to the module. -/
private noncomputable def equal_endpoint_conductor_tensor_linearMap
    (M : FGModuleCat R) :
    ((equal_endpoint_conductor_source (k := k)).obj ⊗[R] M.obj) →ₗ[R] M.obj :=
  (TensorProduct.lid R M.obj).toLinearMap.comp
    ((equal_endpoint_conductor_linearMap (k := k)).rTensor M.obj)

/-- Helper for Chap10 Example 10 55 5: the kernel of the conductor-tensor comparison is finite
over the equal-endpoint ring. -/
private theorem equal_endpoint_conductor_tensor_kernel_finite
    (M : FGModuleCat R) :
    Module.Finite R
      (LinearMap.ker (equal_endpoint_conductor_tensor_linearMap (k := k) M)) := by
  -- The equal-endpoint ring is Noetherian, and the conductor-tensor domain is finite over it.
  -- Therefore every submodule of that domain, in particular the kernel, is finite.
  let _ : IsNoetherianRing R := equal_endpoint_poly_subring_isNoetherian (k := k)
  let _ : Module.Finite R
      (((equal_endpoint_conductor_source (k := k)).obj) ⊗[R] M.obj) := inferInstance
  exact Module.IsNoetherian.finite R
    (LinearMap.ker (equal_endpoint_conductor_tensor_linearMap (k := k) M))

/-- Helper for Chap10 Example 10 55 5: the Grothendieck class of a finite module is the sum of
the classes of a finite submodule and the corresponding quotient. -/
private theorem finiteGrothendieckGroupOf_eq_submodule_add_quotient
    {V : Type u} [AddCommGroup V] [Module R V] [Module.Finite R V]
    (N : Submodule R V) [Module.Finite R N] :
    finiteGrothendieckGroupOf R (FGModuleCat.of R V) =
      finiteGrothendieckGroupOf R (FGModuleCat.of R N) +
        finiteGrothendieckGroupOf R (FGModuleCat.of R (V ⧸ N)) := by
  -- Package the canonical row `0 → N → V → V/N → 0` as a short exact sequence of finite
  -- modules, then read off the defining Grothendieck relation.
  let S : CategoryTheory.ShortComplex (FGModuleCat R) :=
    { X₁ := FGModuleCat.of R N
      X₂ := FGModuleCat.of R V
      X₃ := FGModuleCat.of R (V ⧸ N)
      f := FGModuleCat.ofHom N.subtype
      g := FGModuleCat.ofHom N.mkQ
      zero := by
        ext x
        change N.mkQ (N.subtype x) = 0
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact x.2 }
  have hS : (S.map (ModuleCat.isFG R).ι).ShortExact := by
    -- Forgetting the finiteness owner recovers the standard exact row for a submodule.
    refine ModuleCat.shortComplex_shortExact (S.map (ModuleCat.isFG R).ι)
      (LinearMap.exact_subtype_mkQ N) Subtype.val_injective (Submodule.mkQ_surjective N)
  simpa [finiteGrothendieckGroupOf, S] using
    ModulePropertyK0.of_shortExact R S hS

/-- Helper for Chap10 Example 10 55 5: the Grothendieck class of the domain of a linear map
splits as the class of its kernel plus the class of its range. -/
private theorem finiteGrothendieckGroupOf_eq_ker_add_range
    {V W : Type u} [AddCommGroup V] [Module R V] [Module.Finite R V]
    [AddCommGroup W] [Module R W]
    (f : V →ₗ[R] W) [Module.Finite R (LinearMap.ker f)]
    [Module.Finite R (LinearMap.range f)] :
    finiteGrothendieckGroupOf R (FGModuleCat.of R V) =
      finiteGrothendieckGroupOf R (FGModuleCat.of R (LinearMap.ker f)) +
        finiteGrothendieckGroupOf R (FGModuleCat.of R (LinearMap.range f)) := by
  -- First decompose the domain into its kernel and quotient by the kernel.
  have hdecomp :
      finiteGrothendieckGroupOf R (FGModuleCat.of R V) =
        finiteGrothendieckGroupOf R (FGModuleCat.of R (LinearMap.ker f)) +
          finiteGrothendieckGroupOf R (FGModuleCat.of R (V ⧸ LinearMap.ker f)) := by
    exact finiteGrothendieckGroupOf_eq_submodule_add_quotient (k := k) (LinearMap.ker f)
  -- The first isomorphism theorem identifies that quotient with the range.
  have hquot :
      finiteGrothendieckGroupOf R (FGModuleCat.of R (V ⧸ LinearMap.ker f)) =
        finiteGrothendieckGroupOf R (FGModuleCat.of R (LinearMap.range f)) := by
    have h0 : ModuleCat.isFG R (ModuleCat.of R PUnit) := by
      rw [ModuleCat.isFG_iff]
      infer_instance
    have hIso :
        ModulePropertyK0.of R (ModuleCat.isFG R) (FGModuleCat.of R (V ⧸ LinearMap.ker f)) =
          ModulePropertyK0.of R (ModuleCat.isFG R) (FGModuleCat.of R (LinearMap.range f)) := by
      exact (@ModulePropertyK0.of_iso R _ (ModuleCat.isFG R) h0 _ _
        (CategoryTheory.ObjectProperty.isoMk (P := ModuleCat.isFG R)
          (LinearMap.quotKerEquivRange f).toModuleIso) :
          ModulePropertyK0.of R (ModuleCat.isFG R) (FGModuleCat.of R (V ⧸ LinearMap.ker f)) =
            ModulePropertyK0.of R (ModuleCat.isFG R) (FGModuleCat.of R (LinearMap.range f)))
    simpa [finiteGrothendieckGroupOf] using hIso
  rw [hdecomp, hquot]

/-- Helper for Chap10 Example 10 55 5: the quotient of a finite module by the conductor-tensor
range is annihilated by the endpoint-evaluation kernel. -/
private theorem equal_endpoint_conductor_tensor_quotient_torsion
    (M : FGModuleCat R) :
    Module.IsTorsionBySet R
      (M.obj ⧸ LinearMap.range (equal_endpoint_conductor_tensor_linearMap (k := k) M))
      (RingHom.ker (equal_endpoint_eval k)) := by
  rw [Module.isTorsionBySet_quotient_iff]
  intro m r hr
  -- Replace an element of the endpoint kernel by a conductor multiple, then evaluate the
  -- corresponding simple tensor under the conductor tensor map.
  have hrange :
      r ∈ LinearMap.range (equal_endpoint_conductor_linearMap (k := k)) := by
    have hrSub :
        (r : R) ∈ ((RingHom.ker (equal_endpoint_eval k) : Ideal R) : Submodule R R) := hr
    simpa [equal_endpoint_eval_ker_eq_conductor_range (k := k)] using hrSub
  rcases hrange with ⟨q, hq⟩
  refine ⟨q ⊗ₜ[R] m, ?_⟩
  -- On a simple tensor, the tensor comparison sends `q ⊗ m` to the scalar action of the
  -- conductor multiple on `m`.
  simpa [equal_endpoint_conductor_tensor_linearMap, hq]
    using congrArg (fun a : R ↦ a • m) hq

/-- Helper for Chap10 Example 10 55 5: on a simple tensor, conductor multiplication can be moved
from the left tensor factor to the module factor after commuting polynomial factors. -/
private theorem equal_endpoint_conductor_tensor_smul_tmul
    (M : FGModuleCat R) (q : Polynomial k)
    (b : (equal_endpoint_conductor_source (k := k)).obj) (m : M.obj) :
    ((equal_endpoint_conductor_linearMap (k := k) q) •
        (TensorProduct.tmul R b m) :
          (equal_endpoint_conductor_source (k := k)).obj ⊗[R] M.obj) =
      TensorProduct.tmul R
        (M := (equal_endpoint_conductor_source (k := k)).obj) (N := M.obj)
        (q : (equal_endpoint_conductor_source (k := k)).obj)
        ((equal_endpoint_conductor_linearMap (k := k) b) • m) := by
  -- Move the scalar on the right side across the tensor product; both sides are then simple
  -- tensors with the same module factor.
  rw [TensorProduct.tmul_smul]
  -- The remaining comparison is the commutativity of the ambient polynomial product defining the
  -- conductor map.
  rw [TensorProduct.smul_tmul']
  congr 1
  dsimp [equal_endpoint_conductor_source, equal_endpoint_polynomial_regular_fgModule,
    equal_endpoint_restrictScalars_object] at b ⊢
  change (((equal_endpoint_conductor_linearMap (k := k) q : R) : Polynomial k) *
      b) =
    (((equal_endpoint_conductor_linearMap (k := k) b : R) : Polynomial k) *
      q)
  simp [equal_endpoint_conductor_linearMap]
  ring

/-- Helper for Chap10 Example 10 55 5: acting on the tensor domain by a conductor multiple is the
same as applying the conductor-tensor map and then tensoring with the multiplier. -/
private theorem equal_endpoint_conductor_tensor_smul_eq_tmul_map
    (M : FGModuleCat R) (q : Polynomial k)
    (x : ((equal_endpoint_conductor_source (k := k)).obj ⊗[R] M.obj)) :
    (equal_endpoint_conductor_linearMap (k := k) q) • x =
      TensorProduct.tmul R
        (M := (equal_endpoint_conductor_source (k := k)).obj) (N := M.obj)
        (q : (equal_endpoint_conductor_source (k := k)).obj)
        (equal_endpoint_conductor_tensor_linearMap (k := k) M x) :=
  -- Tensor induction reduces the statement to the simple-tensor conductor identity above.
  TensorProduct.induction_on x
    (by simp)
    (fun b m ↦ by
      simpa [equal_endpoint_conductor_tensor_linearMap] using
        equal_endpoint_conductor_tensor_smul_tmul (k := k) M q b m)
    (fun x y hx hy ↦ by
      rw [TensorProduct.smul_add, LinearMap.map_add, TensorProduct.tmul_add, hx, hy])

/-- Helper for Chap10 Example 10 55 5: the PID normal form over `k[X]`, after restriction of
scalars to the equal-endpoint ring, is a multiple of the free `R`-class. -/
private theorem equal_endpoint_restrictScalars_pid_class_eq_rank_smul_free_class
    (N : FGModuleCat (Polynomial k)) :
    finiteGrothendieckGroupOf R (equal_endpoint_restrictScalars_object (k := k) N) =
      finiteGrothendieckGroup_pidRankMap (Polynomial k)
          (finiteGrothendieckGroupOf (Polynomial k) N) •
        equal_endpoint_free_class k := by
  letI : Module (Polynomial k) (Polynomial k) := Semiring.toModule
  letI : Module.Finite (Polynomial k) (Polynomial k) := Module.Finite.self (Polynomial k)
  let c : ℤ :=
    finiteGrothendieckGroup_pidRankMap (Polynomial k)
      (finiteGrothendieckGroupOf (Polynomial k) N)
  let ηB : finiteGrothendieckGroup (Polynomial k) :=
    finiteGrothendieckGroupOf (Polynomial k) (FGModuleCat.of (Polynomial k) (Polynomial k))
  have hfreeB :
      finiteGrothendieckGroup_pidEquiv (Polynomial k) ηB = 1 := by
    -- The rank-one free `k[X]`-module has PID generic rank one.
    rw [finiteGrothendieckGroup_pidEquiv_apply, finiteGrothendieckGroup_pidRankMap_apply_of]
    simpa [ηB, Module.finrank_tensorProduct, Module.finrank_self]
  have hpid :
      finiteGrothendieckGroupOf (Polynomial k) N = c • ηB := by
    -- The PID equivalence identifies every class with its generic-rank coefficient.
    apply (finiteGrothendieckGroup_pidEquiv (Polynomial k)).injective
    calc
      finiteGrothendieckGroup_pidEquiv (Polynomial k)
          (finiteGrothendieckGroupOf (Polynomial k) N) = c := by
            simp [c, finiteGrothendieckGroup_pidEquiv_apply]
      _ = finiteGrothendieckGroup_pidEquiv (Polynomial k) (c • ηB) := by
            rw [map_zsmul, hfreeB]
            simp
  calc
    finiteGrothendieckGroupOf R (equal_endpoint_restrictScalars_object (k := k) N) =
        equal_endpoint_finiteGrothendieckGroup_restrictScalars (k := k)
          (finiteGrothendieckGroupOf (Polynomial k) N) := by
          exact (equal_endpoint_finiteGrothendieckGroup_restrictScalars_apply_of
            (k := k) N).symm
    _ = equal_endpoint_finiteGrothendieckGroup_restrictScalars (k := k) (c • ηB) := by
          rw [hpid]
    _ = c •
        equal_endpoint_finiteGrothendieckGroup_restrictScalars (k := k) ηB := by
          simp
    _ = c • finiteGrothendieckGroupOf R (equal_endpoint_conductor_source (k := k)) := by
          have hηB :
              equal_endpoint_finiteGrothendieckGroup_restrictScalars (k := k) ηB =
                finiteGrothendieckGroupOf R (equal_endpoint_conductor_source (k := k)) := by
            simpa [ηB, equal_endpoint_conductor_source, equal_endpoint_polynomial_regular_fgModule]
              using
                equal_endpoint_finiteGrothendieckGroup_restrictScalars_apply_of (k := k)
                  (FGModuleCat.of (Polynomial k) (Polynomial k))
          rw [hηB]
    _ = c • equal_endpoint_free_class k := by
          rw [equal_endpoint_polynomial_class_eq_free_class]

/-- Helper for Example 10.55.5: the source-faithful conductor/tensor comparison should force every
generator class in `K'_0(R)` to be its generic rank times the free rank-one class. -/
private theorem equal_endpoint_generator_class_eq_rank_smul_free_class
    (M : FGModuleCat R) :
    finiteGrothendieckGroupOf R M =
      equalEndpointRank k M • equal_endpoint_free_class k := by
  let _ : Module.Finite R M.obj := M.property
  letI : Module R (Polynomial k) := Algebra.toModule
  letI : Module (Polynomial k) (Polynomial k) := Semiring.toModule
  letI : SMulCommClass R (Polynomial k) (Polynomial k) := inferInstance
  letI : Module (Polynomial k) ((Polynomial k) ⊗[R] M.obj) := TensorProduct.leftModule
  let _ : Module.Finite (Polynomial k) ((Polynomial k) ⊗[R] M.obj) :=
    Module.Finite.base_change R (Polynomial k) M.obj
  let N : FGModuleCat (Polynomial k) := FGModuleCat.of (Polynomial k) ((Polynomial k) ⊗[R] M.obj)
  let c : ℤ :=
    finiteGrothendieckGroup_pidRankMap (Polynomial k)
      (finiteGrothendieckGroupOf (Polynomial k) N)
  let f : (((equal_endpoint_conductor_source (k := k)).obj) ⊗[R] M.obj) →ₗ[R] M.obj :=
    equal_endpoint_conductor_tensor_linearMap (k := k) M
  -- The finite Tor term is isolated as a named helper, so the K0 assembly below only consumes
  -- explicit finite and endpoint-support inputs.
  have hkernelFinite : Module.Finite R (LinearMap.ker f) := by
    simpa [f] using equal_endpoint_conductor_tensor_kernel_finite (k := k) M
  let _ : Module.Finite R (LinearMap.ker f) := hkernelFinite
  let _ : Module.Finite R (LinearMap.range f) := Module.Finite.range f
  have hnormalize :
      finiteGrothendieckGroupOf R M =
        finiteGrothendieckGroupOf R (equal_endpoint_restrictScalars_object (k := k) N) := by
    -- The tensor comparison gives `[B ⊗ M] = [ker f] + [range f]`.
    have hdomain :
        finiteGrothendieckGroupOf R
            (FGModuleCat.of R (((equal_endpoint_conductor_source (k := k)).obj) ⊗[R] M.obj)) =
          finiteGrothendieckGroupOf R (FGModuleCat.of R (LinearMap.ker f)) +
            finiteGrothendieckGroupOf R (FGModuleCat.of R (LinearMap.range f)) := by
      exact finiteGrothendieckGroupOf_eq_ker_add_range (k := k) f
    -- The range row gives `[M] = [range f] + [M/range f]`.
    have hrange :
        finiteGrothendieckGroupOf R M =
          finiteGrothendieckGroupOf R (FGModuleCat.of R (LinearMap.range f)) +
            finiteGrothendieckGroupOf R (FGModuleCat.of R (M.obj ⧸ LinearMap.range f)) := by
      simpa using
        finiteGrothendieckGroupOf_eq_submodule_add_quotient (k := k)
          (V := M.obj) (LinearMap.range f)
    -- The quotient is annihilated by the endpoint kernel, hence vanishes in `K'_0(R)`.
    have hquotientZero :
        finiteGrothendieckGroupOf R (FGModuleCat.of R (M.obj ⧸ LinearMap.range f)) = 0 := by
      exact equal_endpoint_evalKernel_torsion_class_eq_zero (k := k)
        (V := M.obj ⧸ LinearMap.range f)
        (equal_endpoint_conductor_tensor_quotient_torsion (k := k) M)
    -- TODO: prove the kernel is annihilated by the endpoint kernel via the conductor ideal
    -- normal form; then its class vanishes by the same endpoint-supported argument.
    have hkernelTorsion :
        Module.IsTorsionBySet R (LinearMap.ker f) (RingHom.ker (equal_endpoint_eval k)) := by
      intro x r
      have hrange :
          (r : R) ∈ LinearMap.range (equal_endpoint_conductor_linearMap (k := k)) := by
        have hrSub :
            (r : R) ∈ ((RingHom.ker (equal_endpoint_eval k) : Ideal R) : Submodule R R) :=
          r.2
        simpa [equal_endpoint_eval_ker_eq_conductor_range (k := k)] using hrSub
      rcases hrange with ⟨q, hq⟩
      -- The tensor-action bridge turns multiplication by a conductor-kernel element into
      -- tensoring the image under `f`, which is zero for a kernel element.
      apply Subtype.ext
      calc
        ((r : R) • (x : ((equal_endpoint_conductor_source (k := k)).obj ⊗[R] M.obj)) :
            ((equal_endpoint_conductor_source (k := k)).obj ⊗[R] M.obj)) =
            (equal_endpoint_conductor_linearMap (k := k) q) •
              (x : ((equal_endpoint_conductor_source (k := k)).obj ⊗[R] M.obj)) := by
              rw [hq]
        _ = TensorProduct.tmul R
              (M := (equal_endpoint_conductor_source (k := k)).obj) (N := M.obj)
              (q : (equal_endpoint_conductor_source (k := k)).obj)
              (equal_endpoint_conductor_tensor_linearMap (k := k) M
                (x : ((equal_endpoint_conductor_source (k := k)).obj ⊗[R] M.obj))) := by
              exact equal_endpoint_conductor_tensor_smul_eq_tmul_map (k := k) M q x
        _ = 0 := by
              rw [x.2]
              simp
    have hkernelZero :
        finiteGrothendieckGroupOf R (FGModuleCat.of R (LinearMap.ker f)) = 0 := by
      exact equal_endpoint_evalKernel_torsion_class_eq_zero (k := k)
        (V := LinearMap.ker f) hkernelTorsion
    have hdomainRange :
        finiteGrothendieckGroupOf R
            (FGModuleCat.of R (((equal_endpoint_conductor_source (k := k)).obj) ⊗[R] M.obj)) =
          finiteGrothendieckGroupOf R (FGModuleCat.of R (LinearMap.range f)) := by
      rw [hdomain, hkernelZero, zero_add]
    have hdomainOwner :
        finiteGrothendieckGroupOf R
            (FGModuleCat.of R (((equal_endpoint_conductor_source (k := k)).obj) ⊗[R] M.obj)) =
          finiteGrothendieckGroupOf R (equal_endpoint_restrictScalars_object (k := k) N) := by
      -- The conductor source is the restricted polynomial regular module, so the tensor owner is
      -- the same restricted `k[X]`-module used by `N`.
      exact (rfl :
        finiteGrothendieckGroupOf R (FGModuleCat.of R ((Polynomial k) ⊗[R] M.obj)) =
          finiteGrothendieckGroupOf R (FGModuleCat.of R ((Polynomial k) ⊗[R] M.obj)))
    calc
      finiteGrothendieckGroupOf R M =
          finiteGrothendieckGroupOf R (FGModuleCat.of R (LinearMap.range f)) +
            finiteGrothendieckGroupOf R (FGModuleCat.of R (M.obj ⧸ LinearMap.range f)) := hrange
      _ = finiteGrothendieckGroupOf R (FGModuleCat.of R (LinearMap.range f)) := by
            rw [hquotientZero, add_zero]
      _ = finiteGrothendieckGroupOf R
            (FGModuleCat.of R (((equal_endpoint_conductor_source (k := k)).obj) ⊗[R] M.obj)) :=
            hdomainRange.symm
      _ = finiteGrothendieckGroupOf R (equal_endpoint_restrictScalars_object (k := k) N) :=
            hdomainOwner
  have hpid :
      finiteGrothendieckGroupOf R (equal_endpoint_restrictScalars_object (k := k) N) =
        c • equal_endpoint_free_class k := by
    exact equal_endpoint_restrictScalars_pid_class_eq_rank_smul_free_class (k := k) N
  have hcoeff : c = equalEndpointRank k M := by
    -- Apply the generic-rank homomorphism to the class comparison; this recovers the coefficient
    -- without comparing the two fraction fields directly.
    have hclass :
        finiteGrothendieckGroupOf R M = c • equal_endpoint_free_class k := hnormalize.trans hpid
    have hmap := congrArg (equalEndpointRankMap k) hclass
    simpa [equalEndpointRankMap_apply_of, map_zsmul, equal_endpoint_free_class_rank] using hmap.symm
  -- The remaining assembly is now only the normalization comparison followed by the PID normal
  -- form and coefficient identification.
  calc
    finiteGrothendieckGroupOf R M =
        finiteGrothendieckGroupOf R (equal_endpoint_restrictScalars_object (k := k) N) :=
          hnormalize
    _ = c • equal_endpoint_free_class k := hpid
    _ = equalEndpointRank k M • equal_endpoint_free_class k := by
          rw [hcoeff]

/-- Helper for Example 10.55.5: the free rank-one class defines the canonical section
`ℤ → K'_0(R)` once the rank is identified with the generator coefficient. -/
private noncomputable def equalEndpointRankSection :
    ℤ →+ finiteGrothendieckGroup R where
  toFun z := z • equal_endpoint_free_class k
  map_zero' := by
    -- The zero integer acts trivially on the distinguished free rank-one class.
    simp [equal_endpoint_free_class]
  map_add' m n := by
    -- Integer multiplication by the free class is additive in the coefficient.
    simp [add_zsmul]

/-- Helper for Example 10.55.5: on a generator class, the section sends the generic rank back to
that class. -/
private theorem equalEndpointRankSection_apply_rank
    (M : FGModuleCat R) :
    equalEndpointRankSection k (equalEndpointRank k M) =
      finiteGrothendieckGroupOf R M := by
  -- The pending source-faithful normal form states exactly that `[M] = rank(M) [R]`.
  simpa [equalEndpointRankSection] using
    (equal_endpoint_generator_class_eq_rank_smul_free_class (k := k) M).symm

/-- Helper for Example 10.55.5: once generator classes satisfy `[M] = rank(M) [R]`, the free
rank-one section is a left inverse to the generic-rank map on all of `K'_0(R)`. -/
private theorem equalEndpointRankSection_leftInverse :
    Function.LeftInverse
      (equalEndpointRankSection k)
      ((equalEndpointRankMap k) : finiteGrothendieckGroup.{u, u} R →+ ℤ) := by
  intro x
  refine Quotient.inductionOn x ?_
  intro z
  induction z using FreeAbelianGroup.induction_on with
  | zero =>
      -- Both the descended rank map and its section preserve the zero class.
      simp [equalEndpointRankSection, equalEndpointRankMap, ModulePropertyK0.lift]
  | of M =>
      -- The generator case is exactly the source-faithful normal form `[M] = rank(M) [R]`.
      simpa [finiteGrothendieckGroupOf] using
        equalEndpointRankSection_apply_rank (k := k) M
  | neg z hz =>
      -- Additivity of both maps reduces the inverse statement for `-z` to the one for `z`.
      simpa [equalEndpointRankSection, equalEndpointRankMap, ModulePropertyK0.lift] using
        congrArg (fun y : finiteGrothendieckGroup R ↦ -y) hz
  | add z w hz hw =>
      -- The inverse statement is compatible with addition on the free abelian representatives.
      simpa [equalEndpointRankSection, equalEndpointRankMap, ModulePropertyK0.lift, add_zsmul] using
        congrArg₂ (fun a b : finiteGrothendieckGroup R ↦ a + b) hz hw

/-- Helper for Example 10.55.5: once the free rank-one class maps to `1`, integer multiples of
that class already show that the generic-rank map is surjective. -/
private theorem equalEndpointRankMap_surjective_of_free_class_rank
    (hfree : equalEndpointRankMap k (equal_endpoint_free_class k) = 1) :
    Function.Surjective
      ((equalEndpointRankMap k) : finiteGrothendieckGroup.{u, u} R →+ ℤ) := by
  intro z
  -- The class `z • [R]` maps to the integer `z`.
  refine ⟨(z • equal_endpoint_free_class k : finiteGrothendieckGroup.{u, u} R), ?_⟩
  rw [map_zsmul, hfree]
  simp

/-- The generic-rank map on `K'_0(R)` is bijective for the equal-endpoint ring. -/
-- Proof sketch: surjectivity is realized by the class of a free rank-one module. Injectivity is
-- the equal-endpoint analogue of the PID generic-rank computation, using the classification of
-- finite modules over this ring to show that the `K'_0`-class is determined by generic rank.
private theorem equalEndpointRankMap_bijective :
    Function.Bijective
      ((equalEndpointRankMap k) : finiteGrothendieckGroup.{u, u} R →+ ℤ) := by
  have hsurj :
      Function.Surjective
        ((equalEndpointRankMap k) : finiteGrothendieckGroup.{u, u} R →+ ℤ) := by
    exact equalEndpointRankMap_surjective_of_free_class_rank (k := k)
      (equal_endpoint_free_class_rank (k := k))
  have hleft :
      Function.LeftInverse
        (equalEndpointRankSection k)
        ((equalEndpointRankMap k) : finiteGrothendieckGroup.{u, u} R →+ ℤ) :=
    equalEndpointRankSection_leftInverse (k := k)
  have hinj :
      Function.Injective
        ((equalEndpointRankMap k) : finiteGrothendieckGroup.{u, u} R →+ ℤ) :=
    hleft.injective
  exact ⟨hinj, hsurj⟩

/-- Example 10.55.5 (1): for `R = {f ∈ k[x] | f(0) = f(1)}`, the finite-module Grothendieck group
`K'_0(R)` is canonically identified with `ℤ` by the generic-rank map. -/
@[stacks 00JG]
noncomputable def equal_endpoint_ring_finiteGrothendieckGroup :
    finiteGrothendieckGroup R ≃+ ℤ :=
  AddEquiv.ofBijective (equalEndpointRankMap k) (equalEndpointRankMap_bijective k)

/-- The additive equivalence `K'_0(R) ≃+ ℤ` acts by the generic-rank map. -/
theorem equal_endpoint_ring_finiteGrothendieckGroup_apply (x : finiteGrothendieckGroup R) :
    equal_endpoint_ring_finiteGrothendieckGroup k x =
      equalEndpointRankMap k x := rfl

/-- Helper for Chap10 Example 10 55 5: projective generic rank is finite comparison plus rank. -/
private theorem equalEndpointProjectiveRankMap_eq_finiteComparison :
    equalEndpointProjectiveRankMap k = (equal_endpoint_ring_finiteGrothendieckGroup k).toAddMonoidHom.comp K0→K0' := by
  -- Check the comparison on projective generators, where both sides are the same generic rank.
  apply QuotientAddGroup.addMonoidHom_ext
  apply FreeAbelianGroup.lift_ext
  intro M
  let _ : Module.Finite R M.obj := M.property.1
  -- Compare the projective and finite generic-rank maps after forgetting finite projectivity.
  calc
    equalEndpointProjectiveRankMap k (projectiveGrothendieckGroupOf R M) =
        equalEndpointProjectiveRank k M := by
      rw [equalEndpointProjectiveRankMap_apply_of]
    _ = equalEndpointRank k (FGModuleCat.of R M.obj) := rfl
    _ = ((equal_endpoint_ring_finiteGrothendieckGroup k).toAddMonoidHom.comp K0→K0')
          (projectiveGrothendieckGroupOf R M) := by
      have hfinite :
          equal_endpoint_ring_finiteGrothendieckGroup k
              (finiteGrothendieckGroupOf R (FGModuleCat.of R M.obj)) =
            equalEndpointRank k (FGModuleCat.of R M.obj) := by
        rw [equal_endpoint_ring_finiteGrothendieckGroup_apply, equalEndpointRankMap_apply_of]
      simpa [AddMonoidHom.comp_apply, ModulePropertyK0.map_of, finiteGrothendieckGroupOf]
        using hfinite.symm

/-- Example 10.55.5 (2): for `R = {f ∈ k[x] | f(0) = f(1)}`, the Grothendieck group `K₀(R)` of finite
projective `R`-modules is identified with `Additive kˣ × ℤ`. -/
@[stacks 00JG]
theorem equal_endpoint_ring_projectiveGrothendieckGroup :
    ∃ e : projectiveGrothendieckGroup R ≃+ Additive kˣ × ℤ,
      (AddMonoidHom.snd (Additive kˣ) ℤ).comp e.toAddMonoidHom =
      (equal_endpoint_ring_finiteGrothendieckGroup k).toAddMonoidHom.comp K0→K0' := by
  rcases equalEndpointProjectiveRankProduct_exists k with ⟨e, he⟩
  refine ⟨e, ?_⟩
  -- Rewrite the support-rank classification to the finite-K0 comparison required by the target.
  exact he.trans (equalEndpointProjectiveRankMap_eq_finiteComparison k)
/-- On an element of `K₀(R)`, some additive equivalence
`K₀(R) ≃+ Additive kˣ × ℤ` has `ℤ`-component given by the canonical comparison to `K'_0(R)`
followed by the generic-rank identification of `K'_0(R)` with `ℤ`. -/
theorem equal_endpoint_ring_projectiveGrothendieckGroup_snd_apply
    (x : projectiveGrothendieckGroup R) :
    ∃ e : projectiveGrothendieckGroup R ≃+ Additive kˣ × ℤ,
      (e x).2 =
        equal_endpoint_ring_finiteGrothendieckGroup k (K0→K0' x) := by
  rcases equal_endpoint_ring_projectiveGrothendieckGroup k with ⟨e, he⟩
  refine ⟨e, ?_⟩
  simpa using DFunLike.congr_fun he x
end
