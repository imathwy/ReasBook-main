import StacksProject_2024.Chap10.Lemma_10_69_4.QuotientPolynomialLocalization

universe u v

open RingTheory
open scoped TensorProduct

attribute [local instance] MvPolynomial.algebraMvPolynomial

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

namespace RingTheory.Sequence

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: for modules over an `R`-algebra `A`, fixing the left
factor gives the canonical `R`-linear map into the tensor product over `A`. -/
noncomputable def tensorProductBaseChangeRightMap
    {R A X Y : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    [AddCommMonoid X] [AddCommMonoid Y] [Module R X] [Module R Y]
    [Module A X] [Module A Y] [IsScalarTower R A X] [IsScalarTower R A Y]
    (x : X) : Y →ₗ[R] X ⊗[A] Y :=
  { toFun := fun y ↦ x ⊗ₜ[A] y
    map_add' := by
      intro y₁ y₂
      -- Additivity is the right additivity relation in the tensor product over `A`.
      rw [TensorProduct.tmul_add]
    map_smul' := by
      intro r y
      -- Convert the restricted `R`-action to the `A`-action and use the tensor balancing
      -- relation to move it to the left factor.
      calc
        x ⊗ₜ[A] (r • y) = x ⊗ₜ[A] ((algebraMap R A r) • y) := by
          rw [algebraMap_smul]
        _ = ((algebraMap R A r) • x) ⊗ₜ[A] y := by
          rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
        _ = r • (x ⊗ₜ[A] y) := by
          rw [algebraMap_smul]
          rfl }

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: the canonical base-change pairing
`X → Y → X ⊗[A] Y` is `R`-bilinear. -/
noncomputable def tensorProductBaseChangeBilinear
    {R A X Y : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    [AddCommMonoid X] [AddCommMonoid Y] [Module R X] [Module R Y]
    [Module A X] [Module A Y] [IsScalarTower R A X] [IsScalarTower R A Y] :
    X →ₗ[R] (Y →ₗ[R] X ⊗[A] Y) :=
  { toFun := fun x ↦
      tensorProductBaseChangeRightMap (R := R) (A := A) (X := X) (Y := Y) x
    map_add' := by
      intro x₁ x₂
      apply LinearMap.ext
      intro y
      -- Pointwise, this is the left additivity relation in the tensor product over `A`.
      simpa [tensorProductBaseChangeRightMap] using
        (TensorProduct.add_tmul (R := A) x₁ x₂ y)
    map_smul' := by
      intro r x
      apply LinearMap.ext
      intro y
      -- Pointwise, restricted `R`-scalars are `A`-scalars on the left tensor factor.
      dsimp [tensorProductBaseChangeRightMap]
      calc
        (r • x) ⊗ₜ[A] y = ((algebraMap R A r) • x) ⊗ₜ[A] y := by
          rw [algebraMap_smul]
        _ = r • (x ⊗ₜ[A] y) := by
          rw [algebraMap_smul, TensorProduct.smul_tmul'] }

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: the canonical `R`-linear map from a tensor product over
`R` to the tensor product over an `R`-algebra `A`. -/
noncomputable def tensorProductBaseChangeMap
    {R A X Y : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    [AddCommMonoid X] [AddCommMonoid Y] [Module R X] [Module R Y]
    [Module A X] [Module A Y] [IsScalarTower R A X] [IsScalarTower R A Y] :
    X ⊗[R] Y →ₗ[R] X ⊗[A] Y :=
  TensorProduct.lift
    (tensorProductBaseChangeBilinear (R := R) (A := A) (X := X) (Y := Y))

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: the base-change map sends a pure tensor over `R` to the
same pure tensor over `A`. -/
@[simp] lemma tensorProductBaseChangeMap_tmul
    {R A X Y : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    [AddCommMonoid X] [AddCommMonoid Y] [Module R X] [Module R Y]
    [Module A X] [Module A Y] [IsScalarTower R A X] [IsScalarTower R A Y]
    (x : X) (y : Y) :
    tensorProductBaseChangeMap (R := R) (A := A) (X := X) (Y := Y) (x ⊗ₜ[R] y) =
      x ⊗ₜ[A] y := by
  -- This is the computation rule for the bilinear map used by `TensorProduct.lift`.
  rfl

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: when `A` is a localization of `R`, the explicit
base-change map is the inverse of the canonical tensor comparison for localized modules. -/
lemma tensorProductBaseChangeMap_eq_moduleTensorEquiv_symm
    {R A X Y : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    (S : Submonoid R) [IsLocalization S A]
    [AddCommMonoid X] [AddCommMonoid Y] [Module R X] [Module R Y]
    [Module A X] [Module A Y] [IsScalarTower R A X] [IsScalarTower R A Y] :
    tensorProductBaseChangeMap (R := R) (A := A) (X := X) (Y := Y) =
      (((IsLocalization.moduleTensorEquiv S A X Y).symm).restrictScalars R).toLinearMap := by
  -- Pure tensors generate the source, and both comparison maps send `x ⊗ y` to the same tensor
  -- over the localized algebra.
  ext x y
  dsimp [IsLocalization.moduleTensorEquiv, TensorProduct.equivOfCompatibleSMul]
  rfl

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: the target quotient module used after localizing
`M / Ideal.ofList xs • ⊤`. -/
abbrev localizedOfListQuotientTarget (xs : List R) (S : Submonoid R) : Type (max u v) :=
  (LocalizedModule S M) ⧸
    (Ideal.ofList (xs.map (algebraMap R (Localization S))) • ⊤ :
      Submodule (Localization S) (LocalizedModule S M))

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: the canonical `R / Ideal.ofList xs`-algebra structure on
the localized quotient ring `(Localization S) / Ideal.ofList (xs.map ...)`. -/
noncomputable abbrev localizedOfListQuotientAlgebra
    (xs : List R) (S : Submonoid R) :
    Algebra (R ⧸ Ideal.ofList xs)
      ((Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S)))) :=
  let J : Ideal R := Ideal.ofList xs
  let Qloc : Type u := Localization (Algebra.algebraMapSubmonoid (R ⧸ J) S)
  let eCoeff := localized_ofList_quotientRing_ringEquiv (R := R) xs S
  (eCoeff.toRingHom.comp (algebraMap (R ⧸ J) Qloc)).toAlgebra

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: the canonical module structure of the localized quotient
module over the localized quotient ring. -/
noncomputable abbrev localizedOfListQuotientTargetModule
    (xs : List R) (S : Submonoid R) :
    Module ((Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S))))
      (localizedOfListQuotientTarget (M := M) xs S) :=
  (localized_ofList_smul_top_quotient_isTorsionBySet (M := M) xs S).module

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: the target quotient module as a module over
`R / Ideal.ofList xs`, via the localized quotient ring. -/
noncomputable abbrev localizedOfListQuotientTargetSourceModule
    (xs : List R) (S : Submonoid R) :
    Module (R ⧸ Ideal.ofList xs) (localizedOfListQuotientTarget (M := M) xs S) :=
  @Module.compHom
    ((Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S))))
    (R ⧸ Ideal.ofList xs)
    (localizedOfListQuotientTarget (M := M) xs S)
    _ _ (localizedOfListQuotientTargetModule (M := M) xs S) _
    (@algebraMap (R ⧸ Ideal.ofList xs)
      ((Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S))))
      _ _ (localizedOfListQuotientAlgebra (R := R) xs S))

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: the denominator-one quotient localization map preserves
addition. -/
lemma localizedOfListQuotientMap_add
    (xs : List R) (S : Submonoid R)
    (x y : M ⧸ (Ideal.ofList xs • ⊤ : Submodule R M)) :
    localized_ofList_smul_top_quotient_equiv (M := M) xs S
        (LocalizedModule.mkLinearMap S
          (M ⧸ (Ideal.ofList xs • ⊤ : Submodule R M)) (x + y)) =
      localized_ofList_smul_top_quotient_equiv (M := M) xs S
          (LocalizedModule.mkLinearMap S
            (M ⧸ (Ideal.ofList xs • ⊤ : Submodule R M)) x) +
      localized_ofList_smul_top_quotient_equiv (M := M) xs S
          (LocalizedModule.mkLinearMap S
            (M ⧸ (Ideal.ofList xs • ⊤ : Submodule R M)) y) := by
  -- Both maps in the denominator-one quotient comparison are additive.
  rw [map_add, map_add]

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: on quotient representatives, the denominator-one quotient
localization map is compatible with the transported `R / Ideal.ofList xs`-action. -/
lemma localizedOfListQuotientMap_smul_mk
    (xs : List R) (S : Submonoid R) (r : R) (m : M) :
    let T : Type (max u v) := localizedOfListQuotientTarget (M := M) xs S
    letI : Algebra (R ⧸ Ideal.ofList xs)
        ((Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S)))) :=
      localizedOfListQuotientAlgebra (R := R) xs S
    letI : Module
        ((Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S))))
        (localizedOfListQuotientTarget (M := M) xs S) :=
      localizedOfListQuotientTargetModule (M := M) xs S
    letI : Module (R ⧸ Ideal.ofList xs) (localizedOfListQuotientTarget (M := M) xs S) :=
      localizedOfListQuotientTargetSourceModule (M := M) xs S
    localized_ofList_smul_top_quotient_equiv (M := M) xs S
        (LocalizedModule.mkLinearMap S
          (M ⧸ (Ideal.ofList xs • ⊤ : Submodule R M))
          ((Ideal.Quotient.mk (Ideal.ofList xs) r : R ⧸ Ideal.ofList xs) •
            Submodule.Quotient.mk m)) =
      @SMul.smul (M := R ⧸ Ideal.ofList xs) (α := T)
        (localizedOfListQuotientTargetSourceModule (M := M) xs S).toSMul
        (Ideal.Quotient.mk (Ideal.ofList xs) r)
        (localized_ofList_smul_top_quotient_equiv (M := M) xs S
          (LocalizedModule.mkLinearMap S
            (M ⧸ (Ideal.ofList xs • ⊤ : Submodule R M)) (Submodule.Quotient.mk m))) := by
  intro T
  letI : Algebra (R ⧸ Ideal.ofList xs)
      ((Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S)))) :=
    localizedOfListQuotientAlgebra (R := R) xs S
  letI : Module
      ((Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S))))
      (localizedOfListQuotientTarget (M := M) xs S) :=
    localizedOfListQuotientTargetModule (M := M) xs S
  letI : Module (R ⧸ Ideal.ofList xs) (localizedOfListQuotientTarget (M := M) xs S) :=
    localizedOfListQuotientTargetSourceModule (M := M) xs S
  -- Compute the quotient localization on representatives, then use the normalized scalar action
  -- on the localized quotient target.
  rw [Module.Quotient.mk_smul_mk]
  rw [localized_ofList_smul_top_quotient_equiv_apply_mk]
  rw [localized_ofList_smul_top_quotient_equiv_apply_mk]
  have htarget :
      @SMul.smul (M := R ⧸ Ideal.ofList xs) (α := T)
          (localizedOfListQuotientTargetSourceModule (M := M) xs S).toSMul
          (Ideal.Quotient.mk (Ideal.ofList xs) r)
          (Submodule.Quotient.mk (LocalizedModule.mkLinearMap S M m)) =
        Submodule.Quotient.mk
          ((algebraMap R (Localization S) r) • LocalizedModule.mkLinearMap S M m) := by
    -- The target quotient action was normalized in `QuotientPolynomialLocalization`.
    exact localized_ofList_smul_top_quotient_mk_smul (M := M) xs S r
      (LocalizedModule.mkLinearMap S M m)
  calc
    Submodule.Quotient.mk (LocalizedModule.mkLinearMap S M (r • m)) =
        Submodule.Quotient.mk
          ((algebraMap R (Localization S) r) • LocalizedModule.mkLinearMap S M m) := by
          simpa [algebraMap_smul] using
            congrArg (fun y : LocalizedModule S M ↦
              (Submodule.Quotient.mk y : localizedOfListQuotientTarget (M := M) xs S))
              (map_smul (LocalizedModule.mkLinearMap S M) r m)
    _ =
        @SMul.smul (M := R ⧸ Ideal.ofList xs) (α := T)
          (localizedOfListQuotientTargetSourceModule (M := M) xs S).toSMul
          (Ideal.Quotient.mk (Ideal.ofList xs) r)
          (Submodule.Quotient.mk (LocalizedModule.mkLinearMap S M m)) := by
          exact htarget.symm

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: the denominator-one quotient localization map is
`R / Ideal.ofList xs`-linear. -/
lemma localizedOfListQuotientMap_smul
    (xs : List R) (S : Submonoid R) :
    let T : Type (max u v) := localizedOfListQuotientTarget (M := M) xs S
    letI : Algebra (R ⧸ Ideal.ofList xs)
        ((Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S)))) :=
      localizedOfListQuotientAlgebra (R := R) xs S
    letI : Module
        ((Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S))))
        (localizedOfListQuotientTarget (M := M) xs S) :=
      localizedOfListQuotientTargetModule (M := M) xs S
    letI : Module (R ⧸ Ideal.ofList xs) (localizedOfListQuotientTarget (M := M) xs S) :=
      localizedOfListQuotientTargetSourceModule (M := M) xs S
    ∀ (a : R ⧸ Ideal.ofList xs)
      (x : M ⧸ (Ideal.ofList xs • ⊤ : Submodule R M)),
      localized_ofList_smul_top_quotient_equiv (M := M) xs S
          (LocalizedModule.mkLinearMap S
            (M ⧸ (Ideal.ofList xs • ⊤ : Submodule R M)) (a • x)) =
        @SMul.smul (M := R ⧸ Ideal.ofList xs) (α := T)
          (localizedOfListQuotientTargetSourceModule (M := M) xs S).toSMul a
          (localized_ofList_smul_top_quotient_equiv (M := M) xs S
            (LocalizedModule.mkLinearMap S
              (M ⧸ (Ideal.ofList xs • ⊤ : Submodule R M)) x)) := by
  intro T
  letI : Algebra (R ⧸ Ideal.ofList xs)
      ((Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S)))) :=
    localizedOfListQuotientAlgebra (R := R) xs S
  letI : Module
      ((Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S))))
      (localizedOfListQuotientTarget (M := M) xs S) :=
    localizedOfListQuotientTargetModule (M := M) xs S
  letI : Module (R ⧸ Ideal.ofList xs) (localizedOfListQuotientTarget (M := M) xs S) :=
    localizedOfListQuotientTargetSourceModule (M := M) xs S
  intro a x
  -- Reduce scalar compatibility to representatives in the quotient ring and quotient module.
  refine Quotient.inductionOn' a ?_
  intro r
  refine Quotient.inductionOn' x ?_
  intro m
  exact localizedOfListQuotientMap_smul_mk (M := M) xs S r m

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: the denominator-one map
`M / Ideal.ofList xs • ⊤ → (M_S) / Ideal.ofList xs_S • ⊤` as a linear map over
`R / Ideal.ofList xs`. -/
noncomputable def localizedOfListQuotientMap
    (xs : List R) (S : Submonoid R) :
    letI : Algebra (R ⧸ Ideal.ofList xs)
        ((Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S)))) :=
      localizedOfListQuotientAlgebra (R := R) xs S
    letI : Module
        ((Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S))))
        (localizedOfListQuotientTarget (M := M) xs S) :=
      localizedOfListQuotientTargetModule (M := M) xs S
    letI : Module (R ⧸ Ideal.ofList xs) (localizedOfListQuotientTarget (M := M) xs S) :=
      localizedOfListQuotientTargetSourceModule (M := M) xs S
    (M ⧸ (Ideal.ofList xs • ⊤ : Submodule R M)) →ₗ[R ⧸ Ideal.ofList xs]
      localizedOfListQuotientTarget (M := M) xs S :=
  letI : Algebra (R ⧸ Ideal.ofList xs)
        ((Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S)))) :=
      localizedOfListQuotientAlgebra (R := R) xs S
  letI : Module
        ((Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S))))
        (localizedOfListQuotientTarget (M := M) xs S) :=
      localizedOfListQuotientTargetModule (M := M) xs S
  letI : Module (R ⧸ Ideal.ofList xs) (localizedOfListQuotientTarget (M := M) xs S) :=
    localizedOfListQuotientTargetSourceModule (M := M) xs S
  { toFun := fun x ↦
      localized_ofList_smul_top_quotient_equiv (M := M) xs S
        (LocalizedModule.mkLinearMap S
          (M ⧸ (Ideal.ofList xs • ⊤ : Submodule R M)) x)
    map_add' := localizedOfListQuotientMap_add (M := M) xs S
    map_smul' := localizedOfListQuotientMap_smul (M := M) xs S }

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: the denominator-one quotient map sends a quotient
representative to the quotient class of the localized numerator. -/
lemma localizedOfListQuotientMap_mk
    (xs : List R) (S : Submonoid R) (m : M) :
    letI : Algebra (R ⧸ Ideal.ofList xs)
        ((Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S)))) :=
      localizedOfListQuotientAlgebra (R := R) xs S
    letI : Module
        ((Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S))))
        (localizedOfListQuotientTarget (M := M) xs S) :=
      localizedOfListQuotientTargetModule (M := M) xs S
    letI : Module (R ⧸ Ideal.ofList xs) (localizedOfListQuotientTarget (M := M) xs S) :=
      localizedOfListQuotientTargetSourceModule (M := M) xs S
    localizedOfListQuotientMap (M := M) xs S (Submodule.Quotient.mk m) =
      (Submodule.Quotient.mk (LocalizedModule.mkLinearMap S M m) :
        localizedOfListQuotientTarget (M := M) xs S) := by
  letI : Algebra (R ⧸ Ideal.ofList xs)
      ((Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S)))) :=
    localizedOfListQuotientAlgebra (R := R) xs S
  letI : Module
      ((Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S))))
      (localizedOfListQuotientTarget (M := M) xs S) :=
    localizedOfListQuotientTargetModule (M := M) xs S
  letI : Module (R ⧸ Ideal.ofList xs) (localizedOfListQuotientTarget (M := M) xs S) :=
    localizedOfListQuotientTargetSourceModule (M := M) xs S
  -- Unfold only the packaged linear map and use the existing denominator-one computation.
  exact localized_ofList_smul_top_quotient_equiv_apply_mk (M := M) xs S m

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: the transported `R ⧸ Ideal.ofList xs`-module structure
on the localized quotient target is compatible with the original `R`-module structure. -/
lemma localizedOfListQuotientTarget_isScalarTower
    (xs : List R) (S : Submonoid R) :
    let Q : Type u := R ⧸ Ideal.ofList xs
    let Qs : Type u :=
      (Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S)))
    let T : Type (max u v) := localizedOfListQuotientTarget (M := M) xs S
    letI : Algebra Q Qs := localizedOfListQuotientAlgebra (R := R) xs S
    letI : Module Qs T := localizedOfListQuotientTargetModule (M := M) xs S
    letI : Module Q T := localizedOfListQuotientTargetSourceModule (M := M) xs S
    IsScalarTower R Q T := by
  let Q : Type u := R ⧸ Ideal.ofList xs
  let Qs : Type u :=
    (Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S)))
  let T : Type (max u v) := localizedOfListQuotientTarget (M := M) xs S
  letI : Algebra Q Qs := localizedOfListQuotientAlgebra (R := R) xs S
  let instQs : Module Qs T := localizedOfListQuotientTargetModule (M := M) xs S
  let instQ : Module Q T := localizedOfListQuotientTargetSourceModule (M := M) xs S
  letI : SMul Qs T := instQs.toSMul
  letI : MulAction Qs T := instQs.toDistribMulAction.toMulAction
  letI : DistribMulAction Qs T := instQs.toDistribMulAction
  letI : Module Qs T := instQs
  letI : SMul Q T := instQ.toSMul
  letI : MulAction Q T := instQ.toDistribMulAction.toMulAction
  letI : DistribMulAction Q T := instQ.toDistribMulAction
  letI : Module Q T := instQ
  -- Check the scalar-tower identity on quotient representatives, where both actions have
  -- denominator-one formulas.
  refine IsScalarTower.of_algebraMap_smul fun r x ↦ ?_
  refine Quotient.inductionOn' x ?_
  intro y
  calc
    (algebraMap R Q r) • (Submodule.Quotient.mk y : T) =
        Submodule.Quotient.mk ((algebraMap R (Localization S) r) • y) := by
          simpa [Q, T] using
            localized_ofList_smul_top_quotient_mk_smul (M := M) xs S r y
    _ = r • (Submodule.Quotient.mk y : T) := by
          rw [Submodule.Quotient.mk_smul]
          simp [algebraMap_smul]

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: the denominator-one quotient map is a localization over
`R ⧸ Ideal.ofList xs` at the image of `S`. -/
lemma localizedOfListQuotientMap_isLocalizedModule
    (xs : List R) (S : Submonoid R) :
    letI : Algebra (R ⧸ Ideal.ofList xs)
        ((Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S)))) :=
      localizedOfListQuotientAlgebra (R := R) xs S
    letI : Module
        ((Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S))))
        (localizedOfListQuotientTarget (M := M) xs S) :=
      localizedOfListQuotientTargetModule (M := M) xs S
    letI : Module (R ⧸ Ideal.ofList xs) (localizedOfListQuotientTarget (M := M) xs S) :=
      localizedOfListQuotientTargetSourceModule (M := M) xs S
    IsLocalizedModule (Algebra.algebraMapSubmonoid (R ⧸ Ideal.ofList xs) S)
      (localizedOfListQuotientMap (M := M) xs S) := by
  let Q : Type u := R ⧸ Ideal.ofList xs
  let Qs : Type u :=
    (Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S)))
  let T : Type (max u v) := localizedOfListQuotientTarget (M := M) xs S
  letI : Algebra Q Qs := localizedOfListQuotientAlgebra (R := R) xs S
  let instQs : Module Qs T := localizedOfListQuotientTargetModule (M := M) xs S
  let instQ : Module Q T := localizedOfListQuotientTargetSourceModule (M := M) xs S
  letI : SMul Qs T := instQs.toSMul
  letI : MulAction Qs T := instQs.toDistribMulAction.toMulAction
  letI : DistribMulAction Qs T := instQs.toDistribMulAction
  letI : Module Qs T := instQs
  letI : SMul Q T := instQ.toSMul
  letI : MulAction Q T := instQ.toDistribMulAction.toMulAction
  letI : DistribMulAction Q T := instQ.toDistribMulAction
  letI : Module Q T := instQ
  letI : IsScalarTower R Q T :=
    localizedOfListQuotientTarget_isScalarTower (M := M) xs S
  let f := localizedOfListQuotientMap (M := M) xs S
  have hfR : IsLocalizedModule S (f.restrictScalars R) := by
    -- Over `R`, the quotient map is just the usual quotient localization map followed by the
    -- already proved quotient equivalence.
    change IsLocalizedModule S
      ((((localized_ofList_smul_top_quotient_equiv (M := M) xs S).toLinearMap).restrictScalars R).comp
        (LocalizedModule.mkLinearMap S
          (M ⧸ (Ideal.ofList xs • ⊤ : Submodule R M))))
    exact IsLocalizedModule.of_linearEquiv S
      (LocalizedModule.mkLinearMap S (M ⧸ (Ideal.ofList xs • ⊤ : Submodule R M)))
      ((localized_ofList_smul_top_quotient_equiv (M := M) xs S).restrictScalars R)
  let _ : IsLocalizedModule S (f.restrictScalars R) := hfR
  -- Upgrade the `R`-localization owner to the quotient-ring image submonoid by descending and
  -- lifting the same denominators through `R → R ⧸ Ideal.ofList xs`.
  refine ⟨?_, ?_, ?_⟩
  · intro t
    rcases t with ⟨_, s, hs, rfl⟩
    have hunit := IsLocalizedModule.map_units (f.restrictScalars R) (⟨s, hs⟩ : S)
    rw [Module.End.isUnit_iff] at hunit ⊢
    convert hunit using 1
    ext y
    exact algebraMap_smul Q s y
  · intro y
    obtain ⟨⟨x, s⟩, hs⟩ :=
      IsLocalizedModule.surj (S := S) (f := f.restrictScalars R) y
    exact ⟨⟨x, ⟨algebraMap R Q (s : R), (s : R), s.2, rfl⟩⟩, by
      exact (algebraMap_smul Q (s : R) y).trans hs⟩
  · intro x₁ x₂ h
    obtain ⟨s, hs⟩ :=
      IsLocalizedModule.exists_of_eq (S := S) (f := f.restrictScalars R) h
    exact ⟨⟨algebraMap R Q (s : R), (s : R), s.2, rfl⟩, by
      exact (algebraMap_smul Q (s : R) x₁).trans
        (hs.trans (algebraMap_smul Q (s : R) x₂).symm)⟩

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: the canonical renaming equivalence changes polynomial
variables from `Fin xs.length` to the length of the localized list. -/
noncomputable def localizedOfListPolynomialRenameEquiv
    (xs : List R) (S : Submonoid R) :
    MvPolynomial (Fin xs.length)
        ((Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S)))) ≃ₗ[
      ((Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S))))]
      MvPolynomial (Fin (xs.map (algebraMap R (Localization S))).length)
        ((Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S)))) :=
  (MvPolynomial.renameEquiv
    ((Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S))))
    (finCongr (List.length_map (as := xs) (algebraMap R (Localization S))).symm)).toLinearEquiv

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: the polynomial renaming equivalence sends monomials to
the corresponding monomials under the `List.length_map` index transport. -/
lemma localizedOfListPolynomialRenameEquiv_monomial
    (xs : List R) (S : Submonoid R) (e : Fin xs.length →₀ ℕ) :
    localizedOfListPolynomialRenameEquiv (R := R) xs S
      (MvPolynomial.monomial e
        (1 : (Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S))))) =
      MvPolynomial.monomial
        (e.mapDomain (Fin.cast (List.length_map (as := xs) (algebraMap R (Localization S))).symm))
        (1 : (Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S)))) := by
  -- The owner equivalence is exactly `MvPolynomial.renameEquiv` along the length equality.
  dsimp [localizedOfListPolynomialRenameEquiv]
  rw [MvPolynomial.rename_monomial]
  rfl

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: the coefficient-localization polynomial map followed by the
canonical variable rename. -/
noncomputable def localizedOfListRenamedPolynomialMap
    (xs : List R) (S : Submonoid R) :
    let J : Ideal R := Ideal.ofList xs
    let JS : Ideal (Localization S) := Ideal.ofList (xs.map (algebraMap R (Localization S)))
    let Q : Type u := R ⧸ J
    let Qs : Type u := (Localization S) ⧸ JS
    letI : Algebra Q Qs := localizedOfListQuotientAlgebra (R := R) xs S
    MvPolynomial (Fin xs.length) Q →ₗ[Q]
      MvPolynomial (Fin (xs.map (algebraMap R (Localization S))).length) Qs :=
  let J : Ideal R := Ideal.ofList xs
  let JS : Ideal (Localization S) := Ideal.ofList (xs.map (algebraMap R (Localization S)))
  let Q : Type u := R ⧸ J
  let Qs : Type u := (Localization S) ⧸ JS
  letI : Algebra Q Qs := localizedOfListQuotientAlgebra (R := R) xs S
  letI : Module Q Qs := Algebra.toModule
  let eFin : Fin xs.length ≃ Fin (xs.map (algebraMap R (Localization S))).length :=
    finCongr (List.length_map (as := xs) (algebraMap R (Localization S))).symm
  let fCoeff : MvPolynomial (Fin xs.length) Q →ₐ[Q] MvPolynomial (Fin xs.length) Qs :=
    MvPolynomial.mapAlgHom (σ := Fin xs.length) (Algebra.ofId Q Qs)
  let fRename :
      MvPolynomial (Fin xs.length) Qs →ₐ[Q]
        MvPolynomial (Fin (xs.map (algebraMap R (Localization S))).length) Qs :=
    (MvPolynomial.renameEquiv Qs eFin).restrictScalars Q
  (fRename.comp fCoeff).toLinearMap

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: the renamed polynomial map sends denominator-one source
monomials to the transported target monomials. -/
lemma localizedOfListRenamedPolynomialMap_monomial
    (xs : List R) (S : Submonoid R) (e : Fin xs.length →₀ ℕ) :
    let J : Ideal R := Ideal.ofList xs
    let JS : Ideal (Localization S) := Ideal.ofList (xs.map (algebraMap R (Localization S)))
    let Q : Type u := R ⧸ J
    let Qs : Type u := (Localization S) ⧸ JS
    letI : Algebra Q Qs := localizedOfListQuotientAlgebra (R := R) xs S
    localizedOfListRenamedPolynomialMap (R := R) xs S (MvPolynomial.monomial e (1 : Q)) =
      MvPolynomial.monomial
        (e.mapDomain (Fin.cast (List.length_map (as := xs) (algebraMap R (Localization S))).symm))
        (1 : Qs) := by
  let J : Ideal R := Ideal.ofList xs
  let JS : Ideal (Localization S) := Ideal.ofList (xs.map (algebraMap R (Localization S)))
  let Q : Type u := R ⧸ J
  let Qs : Type u := (Localization S) ⧸ JS
  letI : Algebra Q Qs := localizedOfListQuotientAlgebra (R := R) xs S
  letI : Module Q Qs := Algebra.toModule
  -- Compute the coefficient localization on `1`, then apply the explicit variable renaming.
  dsimp [localizedOfListRenamedPolynomialMap]
  rw [MvPolynomial.map_monomial]
  rw [MvPolynomial.rename_monomial]
  rw [map_one]
  rfl

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: the renamed polynomial denominator-one map is a
localization over `R ⧸ Ideal.ofList xs` at the image of `S`. -/
lemma localizedOfListRenamedPolynomialMap_isLocalizedModule
    (xs : List R) (S : Submonoid R) :
    let J : Ideal R := Ideal.ofList xs
    let JS : Ideal (Localization S) := Ideal.ofList (xs.map (algebraMap R (Localization S)))
    let Q : Type u := R ⧸ J
    let Qs : Type u := (Localization S) ⧸ JS
    letI : Algebra Q Qs := localizedOfListQuotientAlgebra (R := R) xs S
    IsLocalizedModule (Algebra.algebraMapSubmonoid Q S)
      (localizedOfListRenamedPolynomialMap (R := R) xs S) := by
  let J : Ideal R := Ideal.ofList xs
  let JS : Ideal (Localization S) := Ideal.ofList (xs.map (algebraMap R (Localization S)))
  let Q : Type u := R ⧸ J
  let Qloc : Type u := Localization (Algebra.algebraMapSubmonoid Q S)
  let Qs : Type u := (Localization S) ⧸ JS
  let P : Type u := MvPolynomial (Fin xs.length) Q
  let P0 : Type u := MvPolynomial (Fin xs.length) Qs
  let Pt : Type u :=
    MvPolynomial (Fin (xs.map (algebraMap R (Localization S))).length) Qs
  let eCoeff := localized_ofList_quotientRing_ringEquiv (R := R) xs S
  letI : Algebra Q Qs := localizedOfListQuotientAlgebra (R := R) xs S
  letI : Module Q Qs := Algebra.toModule
  letI : IsLocalization (Algebra.algebraMapSubmonoid Q S) Qs :=
    (IsLocalization.isLocalization_iff_of_ringEquiv
      (M := Algebra.algebraMapSubmonoid Q S) (S := Qloc) (P := Qs) eCoeff).mp
      inferInstance
  let fCoeffAlg : P →ₐ[Q] P0 :=
    MvPolynomial.mapAlgHom (σ := Fin xs.length) (Algebra.ofId Q Qs)
  letI : Algebra P P0 := fCoeffAlg.toAlgebra
  letI : IsScalarTower Q P P0 :=
    IsScalarTower.of_algebraMap_eq fun p ↦ (fCoeffAlg.commutes p).symm
  have hSub :
      Algebra.algebraMapSubmonoid P (Algebra.algebraMapSubmonoid Q S) =
        (Algebra.algebraMapSubmonoid Q S).map (MvPolynomial.C (σ := Fin xs.length)) := by
    -- Polynomial denominators are precisely coefficient-denominators embedded as constants.
    ext z
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases hq with ⟨s, hs, rfl⟩
      exact ⟨algebraMap R Q s, ⟨s, hs, rfl⟩, by simp [P, J]⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q, hq, by simp [P]⟩
  letI : IsLocalization (Algebra.algebraMapSubmonoid P (Algebra.algebraMapSubmonoid Q S)) P0 := by
    rw [hSub]
    exact MvPolynomial.isLocalization (σ := Fin xs.length)
      (M := Algebra.algebraMapSubmonoid Q S) Qs
  have hfCoeff : IsLocalizedModule (Algebra.algebraMapSubmonoid Q S) fCoeffAlg.toLinearMap := by
    -- Convert the polynomial-ring localization owner to its module-localization statement.
    change IsLocalizedModule (Algebra.algebraMapSubmonoid Q S)
      (IsScalarTower.toAlgHom Q P P0).toLinearMap
    exact isLocalizedModule_iff_isLocalization.mpr inferInstance
  let _ : IsLocalizedModule (Algebra.algebraMapSubmonoid Q S) fCoeffAlg.toLinearMap := hfCoeff
  let eFin : Fin xs.length ≃ Fin (xs.map (algebraMap R (Localization S))).length :=
    finCongr (List.length_map (as := xs) (algebraMap R (Localization S))).symm
  let fRenameAlg : P0 ≃ₐ[Q] Pt := (MvPolynomial.renameEquiv Qs eFin).restrictScalars Q
  -- Finally transport the coefficient-localization owner across the variable-renaming equivalence.
  change IsLocalizedModule (Algebra.algebraMapSubmonoid Q S)
    (fRenameAlg.toLinearEquiv.toLinearMap.comp fCoeffAlg.toLinearMap)
  exact IsLocalizedModule.of_linearEquiv (Algebra.algebraMapSubmonoid Q S)
    fCoeffAlg.toLinearMap fRenameAlg.toLinearEquiv

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: the localized quotient ring is the localization of
`R ⧸ Ideal.ofList xs` at the image of `S`. -/
lemma localizedOfListQuotientTarget_isLocalization
    (xs : List R) (S : Submonoid R) :
    let J : Ideal R := Ideal.ofList xs
    let JS : Ideal (Localization S) := Ideal.ofList (xs.map (algebraMap R (Localization S)))
    let Q : Type u := R ⧸ J
    let Qs : Type u := (Localization S) ⧸ JS
    letI : Algebra Q Qs := localizedOfListQuotientAlgebra (R := R) xs S
    IsLocalization (Algebra.algebraMapSubmonoid Q S) Qs := by
  intro J JS Q Qs
  let eCoeff := localized_ofList_quotientRing_ringEquiv (R := R) xs S
  letI : Algebra Q Qs := localizedOfListQuotientAlgebra (R := R) xs S
  -- Transport the canonical localization owner across the quotient-ring equivalence.
  exact
    (IsLocalization.isLocalization_iff_of_ringEquiv
      (M := Algebra.algebraMapSubmonoid Q S)
      (S := Localization (Algebra.algebraMapSubmonoid Q S))
      (P := Qs)
      eCoeff).mp inferInstance

end RingTheory.Sequence

end
