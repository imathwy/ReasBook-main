import StacksProject_2024.Chap10.Lemma_10_133_3
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

open scoped PrincipalParts

/-- Helper for Chap10 Remark 10 133 7: evaluating the linear map represented by a differential
operator on the universal principal-parts class recovers the underlying operator value. -/
private theorem principal_parts_linear_map_equiv_symm_apply_universal_differential
    {R S M Q : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    [AddCommGroup Q] [Module S Q] [Module R Q] [IsScalarTower R S Q]
    (k : ℕ) (D : differential_operators_order_le R S M k Q) (m : M) :
    (principal_parts_linear_map_equiv_differential_operators R S M k Q).symm D
      (principal_parts_universal_differential (R := R) (S := S) (M := M) k m) = D.1 m := by
  let e := principal_parts_linear_map_equiv_differential_operators R S M k Q
  -- Evaluate the identity `e (e.symm D) = D` at the source point `m`.
  have h : (e (e.symm D)).1 m = D.1 m := by
    simpa using
      congrArg (fun E : differential_operators_order_le R S M k Q ↦ E.1 m)
        (e.apply_symm_apply D)
  change (e (e.symm D)).1 m = D.1 m
  exact h

/-- Helper for Chap10 Remark 10 133 7: evaluating the differential operator represented by a map
out of principal parts amounts to evaluating that map on the universal class. -/
private theorem principal_parts_linear_map_equiv_apply_universal_differential
    {R S M Q : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    [AddCommGroup Q] [Module S Q] [Module R Q] [IsScalarTower R S Q]
    (k : ℕ) (L : P^{k}_{S⁄R}(M) →ₗ[S] Q) (m : M) :
    ((principal_parts_linear_map_equiv_differential_operators R S M k Q L).1 m) =
      L (principal_parts_universal_differential (R := R) (S := S) (M := M) k m) := by
  let e := principal_parts_linear_map_equiv_differential_operators R S M k Q
  -- Reduce forward evaluation to the inverse-direction formula above.
  simpa [e] using
    (principal_parts_linear_map_equiv_symm_apply_universal_differential
      (R := R) (S := S) (M := M) (Q := Q) k (D := e L) m).symm

/-- Helper for Chap10 Remark 10 133 7: a linear map out of principal parts is determined by its
values on the universal differential classes. -/
private theorem principal_parts_linear_map_eq_of_apply_universal_differential_eq
    {R S M Q : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    [AddCommGroup Q] [Module S Q] [Module R Q] [IsScalarTower R S Q]
    (k : ℕ) {L₁ L₂ : P^{k}_{S⁄R}(M) →ₗ[S] Q}
    (h : ∀ m : M,
      L₁ (principal_parts_universal_differential (R := R) (S := S) (M := M) k m) =
        L₂ (principal_parts_universal_differential (R := R) (S := S) (M := M) k m)) :
    L₁ = L₂ := by
  let e := principal_parts_linear_map_equiv_differential_operators R S M k Q
  -- Equality on the universal classes gives equality of the represented differential operators.
  apply e.injective
  ext m
  simpa [principal_parts_linear_map_equiv_apply_universal_differential] using h m

/- Domain triage:
* primary domain: base change for modules of principal parts over a commutative square of rings;
* sampled owner API:
  `principal_parts_module`,
  `principal_parts_relation_submodule`,
  `principal_parts_linear_map_equiv_differential_operators`,
  `principalPartsBaseChangeMap`;
* source-facing owner: `principalPartsBaseChangeMap`;
* core/canonical owner: `principal_parts_module`;
* bridge/view: the free-presentation map
  `principalPartsBaseChangeMapOnFree` and its compatibility with
  `principal_parts_relation_submodule`.

Primitive-vs-derived split:
* primitive data: the commutative square `A → B`, `A' → B'` and the `B`-linear map `M → M'`;
* derived API: the induced quotient map on principal parts and its composition theorem.

This file is itself the chapter owner for principal-parts base change, so the refinement keeps the
source-facing owner `principalPartsBaseChangeMap` and removes only duplicate local surface syntax.
-/

section BaseChange

variable {A B A' B' : Type u}
variable [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
variable [Algebra A B] [Algebra A A'] [Algebra A B'] [Algebra A' B'] [Algebra B B']
variable [IsScalarTower A B B'] [IsScalarTower A A' B']

variable {M M' : Type u}
variable [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
variable [AddCommGroup M'] [Module B' M'] [Module A M'] [Module A' M'] [Module B M']
variable [IsScalarTower A' B' M'] [IsScalarTower B B' M'] [IsScalarTower A A' M']

/-- Helper for Chap10 Remark 10 133 7: scalar towers compose from `A → A' → B'`
to an `A → B'` action on a target module. -/
private theorem isScalarTower_leftToTarget
    {X : Type u} [AddCommMonoid X] [Module B' X] [Module A' X] [Module A X]
    [IsScalarTower A A' X] [IsScalarTower A' B' X] :
    IsScalarTower A B' X := by
  -- Compare the two `A`-actions by rewriting the algebra map through `A'`.
  refine IsScalarTower.of_algebraMap_smul fun a x ↦ ?_
  calc
    (algebraMap A B' a) • x =
        (algebraMap A' B' (algebraMap A A' a)) • x := by
          rw [IsScalarTower.algebraMap_apply A A' B' a]
    _ = (algebraMap A A' a) • x :=
          IsScalarTower.algebraMap_smul B' (algebraMap A A' a) x
    _ = a • x :=
          IsScalarTower.algebraMap_smul A' a x

/-- Helper for Chap10 Remark 10 133 7: scalar towers compose from `A → B → B'`
to an `A → B` action on a target module already carrying the `A → B'` action. -/
private theorem isScalarTower_leftToIntermediateTarget
    {X : Type u} [AddCommMonoid X] [Module B' X] [Module B X] [Module A X]
    [IsScalarTower B B' X] [IsScalarTower A B' X] :
    IsScalarTower A B X := by
  -- Move the `B`-scalar through `B'`, then compare with the existing `A → B'` tower.
  refine IsScalarTower.of_algebraMap_smul fun a x ↦ ?_
  calc
    (algebraMap A B a) • x =
        (algebraMap B B' (algebraMap A B a)) • x := by
          exact (IsScalarTower.algebraMap_smul B' (algebraMap A B a) x).symm
    _ = (algebraMap A B' a) • x := by
          rw [← IsScalarTower.algebraMap_apply A B B' a]
    _ = a • x :=
          IsScalarTower.algebraMap_smul B' a x

/-- Helper for Chap10 Remark 10 133 7: the `B'`- and `A`-actions commute on target modules
once the composed `A → B'` scalar tower is available. -/
private instance smulCommClass_target_left
    {X : Type u} [AddCommMonoid X] [Module B' X] [Module A X]
    [IsScalarTower A B' X] :
    SMulCommClass B' A X :=
  SMulCommClass.symm A B' X

/-- Helper for Chap10 Remark 10 133 7: the `B`- and `A`-actions commute on target modules
once the composed `A → B` scalar tower is available. -/
private instance smulCommClass_intermediate_left
    {X : Type u} [AddCommMonoid X] [Module B X] [Module A X]
    [IsScalarTower A B X] :
    SMulCommClass B A X :=
  SMulCommClass.symm A B X

/-- The map on the free presentations induced by a morphism of modules over a commutative square
of rings. -/
private abbrev principalPartsBaseChangeMapOnFree (f : M →ₗ[B] M') :
    (M →₀ B) →ₗ[B] (M' →₀ B') :=
  (Finsupp.mapRange.linearMap (Algebra.linearMap B B')).comp (Finsupp.lmapDomain B B f)

omit [Module B' M'] [IsScalarTower B B' M'] in
/-- Helper for Chap10 Remark 10 133 7: the free base-change map sends a basis vector to the basis
vector of the image with the coefficient mapped along `B → B'`. -/
private theorem principalPartsBaseChangeMapOnFree_single
    (f : M →ₗ[B] M') (m : M) (b : B) :
    principalPartsBaseChangeMapOnFree f (Finsupp.single m b) =
      Finsupp.single (f m) (algebraMap B B' b) := by
  -- Both stages of the free map have explicit formulas on `Finsupp.single`.
  simp [principalPartsBaseChangeMapOnFree]

/-- Helper for Chap10 Remark 10 133 7: the universal principal-parts class is represented by
the quotient class of the free basis vector `Finsupp.single m 1`. -/
private theorem principalPartsUniversalDifferential_eq_mkQ_single
    {R S X : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup X] [Module S X] [Module R X] [IsScalarTower R S X]
    (k : ℕ) (x : X) :
    principal_parts_universal_differential (R := R) (S := S) (M := X) k x =
      (principal_parts_relation_submodule R S X k).mkQ (Finsupp.single x (1 : S)) := by
  -- This records the presentation-level normal form exposed by the definition.
  rfl

/-- Helper for Chap10 Remark 10 133 7: the universal class map into the target principal-parts
module is an order-`k` differential operator. -/
private theorem principalPartsUniversalDifferential_isDifferentialOperatorOfOrder
    (k : ℕ) :
    (principal_parts_universal_differential (R := A') (S := B') (M := M') k).IsDifferentialOperatorOfOrder
      B' k := by
  -- The representing equivalence sends the identity map on principal parts to the universal
  -- differential operator.
  let e := principal_parts_linear_map_equiv_differential_operators A' B' M' k (P^{k}_{B'⁄A'}(M'))
  have hId :
      (((e (LinearMap.id : P^{k}_{B'⁄A'}(M') →ₗ[B'] P^{k}_{B'⁄A'}(M'))) :
          differential_operators_order_le A' B' M' k (P^{k}_{B'⁄A'}(M'))).1).IsDifferentialOperatorOfOrder
        B' k := by
    change
      (((e (LinearMap.id : P^{k}_{B'⁄A'}(M') →ₗ[B'] P^{k}_{B'⁄A'}(M'))) :
          differential_operators_order_le A' B' M' k (P^{k}_{B'⁄A'}(M'))).1) ∈
        differential_operators_order_le_submodule A' B' M' k (P^{k}_{B'⁄A'}(M'))
    exact
      ((e (LinearMap.id : P^{k}_{B'⁄A'}(M') →ₗ[B'] P^{k}_{B'⁄A'}(M'))) :
        differential_operators_order_le A' B' M' k (P^{k}_{B'⁄A'}(M'))).2
  simpa [e] using hId

include A' B' in
/-- Helper for Chap10 Remark 10 133 7: the source `B`-linear map can be viewed as an `A`-linear
map along the scalar tower `A → B`. -/
private theorem principalPartsBaseChangeSourceMap_smul
    (f : M →ₗ[B] M') (a : A) (m : M) :
    f (a • m) = a • f m := by
  letI : IsScalarTower A B' M' :=
    isScalarTower_leftToTarget (A := A) (A' := A') (B' := B') (X := M')
  letI : IsScalarTower A B M' :=
    isScalarTower_leftToIntermediateTarget (A := A) (B := B) (B' := B') (X := M')
  -- The `B`-linear scalar formula becomes the desired `A`-linear one through the composed tower.
  simpa using f.map_smul (algebraMap A B a) m

/-- Helper for Chap10 Remark 10 133 7: the source map for base change, regarded as `A`-linear. -/
private def principalPartsBaseChangeSourceMap (f : M →ₗ[B] M') : M →ₗ[A] M' where
  toFun := f
  map_add' := f.map_add
  map_smul' := principalPartsBaseChangeSourceMap_smul
    (A := A) (B := B) (A' := A') (B' := B') (M := M) (M' := M') f

/-- Helper for Chap10 Remark 10 133 7: the target universal differential is also `A`-linear via
the composite map `A → A' → B'`. -/
private theorem principalPartsBaseChangeTargetMap_smul
    (k : ℕ) (a : A) (m : M') :
    principal_parts_universal_differential (R := A') (S := B') (M := M') k (a • m) =
      a • principal_parts_universal_differential (R := A') (S := B') (M := M') k m := by
  simpa using
    (principal_parts_universal_differential (R := A') (S := B') (M := M') k).map_smul
      (algebraMap A A' a) m

/-- Helper for Chap10 Remark 10 133 7: the target universal differential, regarded as an
`A`-linear map. -/
private def principalPartsBaseChangeTargetMap (k : ℕ) : M' →ₗ[A] P^{k}_{B'⁄A'}(M') :=
  (principal_parts_universal_differential (R := A') (S := B') (M := M') k).restrictScalars A

omit [Algebra A B'] [IsScalarTower A A' B'] in
/-- Helper for Chap10 Remark 10 133 7: restricting scalars on the base ring does not change the
order of a `B'`-differential operator. -/
private theorem restrictScalars_isDifferentialOperatorOfOrder
    {X Y : Type u} [AddCommGroup X] [AddCommGroup Y]
    [Module B' X] [Module A' X] [Module A X]
    [IsScalarTower A A' X] [IsScalarTower A' B' X]
    [SMulCommClass B' A X] [SMulCommClass B' A' X]
    [Module B' Y] [Module A' Y] [Module A Y]
    [IsScalarTower A A' Y] [IsScalarTower A' B' Y]
    [SMulCommClass B' A Y] [SMulCommClass B' A' Y]
    {D : X →ₗ[A'] Y} {k : ℕ}
    (hD : D.IsDifferentialOperatorOfOrder B' k) :
    (D.restrictScalars A).IsDifferentialOperatorOfOrder B' k := by
  induction k generalizing X Y D with
  | zero =>
      -- Restricting the base ring leaves the order-zero commutation formula unchanged.
      rw [LinearMap.isDifferentialOperatorOfOrder_zero_iff] at hD ⊢
      exact hD
  | succ k ih =>
      -- The successor clause is preserved because scalar commutators commute with
      -- `restrictScalars`.
      rw [LinearMap.isDifferentialOperatorOfOrder_succ_iff] at hD ⊢
      intro b
      simpa [LinearMap.scalarCommutator] using
        (ih (D := D.scalarCommutator b) (hD b))

omit [Algebra A B] [Algebra A B'] [IsScalarTower A B B'] in
/-- Helper for Chap10 Remark 10 133 7: an order bound over `B'` descends to the restricted
`B`-action along `B → B'`. -/
private theorem isDifferentialOperatorOfOrder_restrictAlongAlgebraMap
    {X Y : Type u} [AddCommGroup X] [AddCommGroup Y]
    [Module B' X] [Module A X] [Module B X]
    [SMulCommClass B A X] [SMulCommClass B' A X] [IsScalarTower B B' X]
    [Module B' Y] [Module A Y] [Module B Y]
    [SMulCommClass B A Y] [SMulCommClass B' A Y] [IsScalarTower B B' Y]
    {D : X →ₗ[A] Y} {k : ℕ}
    (hD : D.IsDifferentialOperatorOfOrder B' k) :
    D.IsDifferentialOperatorOfOrder B k := by
  induction k generalizing X Y D with
  | zero =>
      -- Order `0` is just scalar-linearity, and the restricted `B`-action is induced by
      -- `algebraMap B B'`.
      rw [LinearMap.isDifferentialOperatorOfOrder_zero_iff] at hD ⊢
      intro b x
      simpa using hD (algebraMap B B' b) x
  | succ k ih =>
      -- Rewrite the `B`-scalar commutator as the corresponding `B'`-scalar commutator and apply
      -- the induction hypothesis to the smaller-order certificate.
      rw [LinearMap.isDifferentialOperatorOfOrder_succ_iff] at hD ⊢
      intro b
      have hcomm :
          D.scalarCommutator (S := B) b =
            D.scalarCommutator (S := B') (algebraMap B B' b) := by
        ext x
        simp
      rw [hcomm]
      exact ih (D := D.scalarCommutator (S := B') (algebraMap B B' b))
        (hD (algebraMap B B' b))

/-- Helper for Chap10 Remark 10 133 7: precomposing the target universal differential with `f`
gives the order-`k` differential operator represented by base change. -/
private theorem principalPartsBaseChangeDifferentialOperator_mem
    (k : ℕ) (f : M →ₗ[B] M') :
    ((principalPartsBaseChangeTargetMap (A := A) (A' := A') (B' := B') (M' := M') k).comp
        (principalPartsBaseChangeSourceMap (A := A) (B := B) (A' := A') (B' := B')
          (M := M) (M' := M') f)).IsDifferentialOperatorOfOrder
      B k := by
  letI : IsScalarTower A B' M' :=
    isScalarTower_leftToTarget (A := A) (A' := A') (B' := B') (X := M')
  letI : IsScalarTower A B M' :=
    isScalarTower_leftToIntermediateTarget (A := A) (B := B) (B' := B') (X := M')
  letI : IsScalarTower A B' (P^{k}_{B'⁄A'}(M')) :=
    isScalarTower_leftToTarget (A := A) (A' := A') (B' := B')
      (X := P^{k}_{B'⁄A'}(M'))
  letI : IsScalarTower A B (P^{k}_{B'⁄A'}(M')) :=
    isScalarTower_leftToIntermediateTarget (A := A) (B := B) (B' := B')
      (X := P^{k}_{B'⁄A'}(M'))
  -- Route correction: instead of transporting the whole represented operator at once, first
  -- restrict the universal differential along `A' → A`, then descend its `B'`-order bound along
  -- `B → B'`, and only afterwards compose with the order-zero source map.
  have htargetB' :
      (principalPartsBaseChangeTargetMap (A := A) (A' := A') (B' := B') (M' := M') k).IsDifferentialOperatorOfOrder B' k := by
    exact
      restrictScalars_isDifferentialOperatorOfOrder
        (A := A) (A' := A') (B' := B')
        (D := principal_parts_universal_differential (R := A') (S := B') (M := M') k)
        (principalPartsUniversalDifferential_isDifferentialOperatorOfOrder
          (A' := A') (B' := B') (M' := M') k)
  have htarget :
      (principalPartsBaseChangeTargetMap (A := A) (A' := A') (B' := B') (M' := M') k).IsDifferentialOperatorOfOrder B k := by
    exact
      isDifferentialOperatorOfOrder_restrictAlongAlgebraMap
        (A := A) (B := B) (B' := B')
        (D := principalPartsBaseChangeTargetMap (A := A) (A' := A') (B' := B') (M' := M') k)
        htargetB'
  have hsource :
      (principalPartsBaseChangeSourceMap (A := A) (B := B) (A' := A') (B' := B')
        (M := M) (M' := M') f).IsDifferentialOperatorOfOrder B 0 := by
    -- The source map is already `B`-linear, hence order `0`.
    rw [LinearMap.isDifferentialOperatorOfOrder_zero_iff]
    intro b m
    simpa [principalPartsBaseChangeSourceMap] using f.map_smul b m
  -- Compose the order-`k` target operator with the order-zero source map.
  simpa using LinearMap.isDifferentialOperatorOfOrder_comp hsource htarget

/-- Helper for Chap10 Remark 10 133 7: the universal property gives a canonical principal-parts
base-change map. -/
private noncomputable def principalPartsBaseChangeRepresented
    (k : ℕ) (f : M →ₗ[B] M') :
    P^{k}_{B⁄A}(M) →ₗ[B] P^{k}_{B'⁄A'}(M') :=
  (principal_parts_linear_map_equiv_differential_operators A B M k (P^{k}_{B'⁄A'}(M'))).symm
    ⟨(principalPartsBaseChangeTargetMap (A := A) (A' := A') (B' := B') (M' := M') k).comp
        (principalPartsBaseChangeSourceMap (A := A) (B := B) (A' := A') (B' := B')
          (M := M) (M' := M') f),
      principalPartsBaseChangeDifferentialOperator_mem (A := A) (B := B) (A' := A') (B' := B')
        (M := M) (M' := M') k f⟩

/-- Helper for Chap10 Remark 10 133 7: the represented base-change map sends the universal class
`[m]` to the universal class of `f m`. -/
private theorem principalPartsBaseChangeRepresented_apply_universal_differential
    (k : ℕ) (f : M →ₗ[B] M') (m : M) :
    principalPartsBaseChangeRepresented (A := A) (B := B) (A' := A') (B' := B')
        (M := M) (M' := M') k f
        (principal_parts_universal_differential (R := A) (S := B) (M := M) k m) =
      principal_parts_universal_differential (R := A') (S := B') (M := M') k (f m) := by
  -- Evaluate the represented operator on the source universal class.
  simpa [principalPartsBaseChangeRepresented, principalPartsBaseChangeTargetMap,
    principalPartsBaseChangeSourceMap] using
    principal_parts_linear_map_equiv_symm_apply_universal_differential
      (R := A) (S := B) (M := M) (Q := P^{k}_{B'⁄A'}(M')) k
      (D := ⟨(principalPartsBaseChangeTargetMap (A := A) (A' := A') (B' := B') (M' := M') k).comp
          (principalPartsBaseChangeSourceMap (A := A) (B := B) (A' := A') (B' := B')
            (M := M) (M' := M') f),
        principalPartsBaseChangeDifferentialOperator_mem (A := A) (B := B) (A' := A') (B' := B')
          (M := M) (M' := M') k f⟩) m

/-- Helper for Chap10 Remark 10 133 7: the universal-property construction agrees with the
explicit free-module map after precomposing with the quotient map. -/
private theorem principalPartsBaseChangeRepresented_comp_mkQ
    (k : ℕ) (f : M →ₗ[B] M') :
    (principalPartsBaseChangeRepresented (A := A) (B := B) (A' := A') (B' := B')
        (M := M) (M' := M') k f).comp
        (principal_parts_relation_submodule A B M k).mkQ =
      ((principal_parts_relation_submodule A' B' M' k).restrictScalars B).mkQ.comp
        (principalPartsBaseChangeMapOnFree f) := by
  -- Both maps out of the free presentation are determined by the basis vectors `[m]`.
  apply Finsupp.lhom_ext'
  intro m
  apply LinearMap.ext_ring
  -- On the basis vector `[m]`, both maps produce the target universal class of `f m`.
  change
    principalPartsBaseChangeRepresented (A := A) (B := B) (A' := A') (B' := B')
        (M := M) (M' := M') k f
        (principal_parts_universal_differential (R := A) (S := B) (M := M) k m) =
      ((principal_parts_relation_submodule A' B' M' k).restrictScalars B).mkQ
        (principalPartsBaseChangeMapOnFree f (Finsupp.single m (1 : B)))
  rw [principalPartsBaseChangeRepresented_apply_universal_differential,
    principalPartsBaseChangeMapOnFree_single]
  -- Normalize both target classes to the same free basis vector.
  rw [principalPartsUniversalDifferential_eq_mkQ_single]
  simp
  rfl

/-- The map on free presentations sends the order-`k` principal-parts relations over `A → B`
into the corresponding relation submodule over `A' → B'`. -/
private theorem principalPartsRelationSubmodule_le_comap_baseChangeMapOnFree
    (k : ℕ) (f : M →ₗ[B] M') :
    principal_parts_relation_submodule A B M k ≤
      Submodule.comap (principalPartsBaseChangeMapOnFree f)
        ((principal_parts_relation_submodule A' B' M' k).restrictScalars B) := by
  intro x hx
  rw [Submodule.mem_comap]
  -- The quotient comparison shows that any source relation maps to a target element with
  -- trivial quotient class, hence back into the target relation submodule.
  have hcomp := LinearMap.congr_fun
    (principalPartsBaseChangeRepresented_comp_mkQ
      (A := A) (B := B) (A' := A') (B' := B') (M := M) (M' := M') k f) x
  have hx0 : (principal_parts_relation_submodule A B M k).mkQ x = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hx
  have htarget :
      ((principal_parts_relation_submodule A' B' M' k).restrictScalars B).mkQ
          (principalPartsBaseChangeMapOnFree f x) = 0 := by
    calc
      ((principal_parts_relation_submodule A' B' M' k).restrictScalars B).mkQ
          (principalPartsBaseChangeMapOnFree f x) =
        principalPartsBaseChangeRepresented (A := A) (B := B) (A' := A') (B' := B')
          (M := M) (M' := M') k f
          ((principal_parts_relation_submodule A B M k).mkQ x) := by
            exact hcomp.symm
      _ = 0 := by
            rw [hx0]
            exact LinearMap.map_zero _
  exact
    (Submodule.Quotient.mk_eq_zero
      ((principal_parts_relation_submodule A' B' M' k).restrictScalars B)).1
      (by simpa [Submodule.mkQ_apply] using htarget)

/-- Helper for Chap10 Remark 10 133 7: a commutative square of rings together with a `B`-linear map `M → M'`
induces a canonical map `P^k_{B/A}(M) → P^k_{B'/A'}(M')` on modules of principal parts. -/
@[stacks 09CP]
abbrev principalPartsBaseChangeMap (k : ℕ) (f : M →ₗ[B] M') :
    P^{k}_{B⁄A}(M) →ₗ[B] P^{k}_{B'⁄A'}(M') :=
  Submodule.mapQ
    (principal_parts_relation_submodule A B M k)
    ((principal_parts_relation_submodule A' B' M' k).restrictScalars B)
    (principalPartsBaseChangeMapOnFree f)
    (principalPartsRelationSubmodule_le_comap_baseChangeMapOnFree k f)

/-- Helper for Chap10 Remark 10 133 7: the public base-change map agrees with the universal-property
construction. -/
private theorem principalPartsBaseChangeMap_eq_represented
    (k : ℕ) (f : M →ₗ[B] M') :
    principalPartsBaseChangeMap (A := A) (B := B) (A' := A') (B' := B')
        (M := M) (M' := M') k f =
      principalPartsBaseChangeRepresented (A := A) (B := B) (A' := A') (B' := B')
        (M := M) (M' := M') k f := by
  -- Both quotient maps agree after precomposing with the source quotient map.
  apply Submodule.linearMap_qext
  have hmapQ :
      (principalPartsBaseChangeMap (A := A) (B := B) (A' := A') (B' := B')
            (M := M) (M' := M') k f).comp
          (principal_parts_relation_submodule A B M k).mkQ =
          ((principal_parts_relation_submodule A' B' M' k).restrictScalars B).mkQ.comp
            (principalPartsBaseChangeMapOnFree f) := by
    simpa [principalPartsBaseChangeMap] using
      (Submodule.mapQ_mkQ
        (p := principal_parts_relation_submodule A B M k)
        (q := (principal_parts_relation_submodule A' B' M' k).restrictScalars B)
        (f := principalPartsBaseChangeMapOnFree f))
  have hrepresented :
      (principalPartsBaseChangeRepresented (A := A) (B := B) (A' := A') (B' := B')
          (M := M) (M' := M') k f).comp
          (principal_parts_relation_submodule A B M k).mkQ =
        ((principal_parts_relation_submodule A' B' M' k).restrictScalars B).mkQ.comp
          (principalPartsBaseChangeMapOnFree f) :=
    principalPartsBaseChangeRepresented_comp_mkQ
      (A := A) (B := B) (A' := A') (B' := B') (M := M) (M' := M') k f
  exact hmapQ.trans hrepresented.symm

/-- Helper for Chap10 Remark 10 133 7: the public base-change map sends the universal class `[m]`
to the universal class of `f m`. -/
private theorem principalPartsBaseChangeMap_apply_universal_differential
    (k : ℕ) (f : M →ₗ[B] M') (m : M) :
    principalPartsBaseChangeMap (A := A) (B := B) (A' := A') (B' := B')
        (M := M) (M' := M') k f
        (principal_parts_universal_differential (R := A) (S := B) (M := M) k m) =
      principal_parts_universal_differential (R := A') (S := B') (M := M') k (f m) := by
  -- The public quotient map is the represented map, whose value on universal classes was
  -- already computed by the differential-operator equivalence.
  rw [principalPartsBaseChangeMap_eq_represented]
  exact principalPartsBaseChangeRepresented_apply_universal_differential
    (A := A) (B := B) (A' := A') (B' := B') (M := M) (M' := M') k f m

end BaseChange

section Composition

variable {A B A' B' A'' B'' : Type u}
variable [CommRing A] [CommRing B] [CommRing A'] [CommRing B'] [CommRing A''] [CommRing B'']
variable [Algebra A B] [Algebra A A'] [Algebra A B'] [Algebra A' B'] [Algebra B B']
variable [Algebra A' A''] [Algebra B' B''] [Algebra A' B''] [Algebra A'' B'']
variable [Algebra A A''] [Algebra A B''] [Algebra B B'']
variable [IsScalarTower A B B'] [IsScalarTower A A' B']
variable [IsScalarTower A' B' B''] [IsScalarTower A' A'' B'']
variable [IsScalarTower A A' A''] [IsScalarTower B B' B'']
variable [IsScalarTower A B B''] [IsScalarTower A A'' B'']

variable {M M' M'' : Type u}
variable [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
variable [AddCommGroup M'] [Module B' M'] [Module A M'] [Module A' M'] [Module B M']
variable [IsScalarTower A' B' M'] [IsScalarTower B B' M'] [IsScalarTower A A' M']
variable [AddCommGroup M''] [Module B'' M''] [Module A M''] [Module A' M''] [Module A'' M'']
variable [Module B' M''] [Module B M'']
variable [IsScalarTower B B' M'']
variable [IsScalarTower A'' B'' M''] [IsScalarTower B' B'' M''] [IsScalarTower B B'' M'']
variable [IsScalarTower A A'' M''] [IsScalarTower A' A'' M'']

-- Proof sketch: on the free presentations this is the compatibility of `Finsupp.lmapDomain` and
-- `Finsupp.mapRange.linearMap` with composition. Passing to quotients via `Submodule.mapQ_comp`
-- gives the result for principal parts.
omit [IsScalarTower A A' A''] in
/-- Chap10 Remark 10 133 7: the principal-parts base-change maps are compatible with further
composition of ring squares and module maps. -/
theorem principalPartsBaseChangeMap_comp (k : ℕ) (f : M →ₗ[B] M') (g : M' →ₗ[B'] M'') :
    ((principalPartsBaseChangeMap k g :
          P^{k}_{B'⁄A'}(M') →ₗ[B'] P^{k}_{B''⁄A''}(M'')).restrictScalars B) ∘ₗ
        (principalPartsBaseChangeMap k f :
          P^{k}_{B⁄A}(M) →ₗ[B] P^{k}_{B'⁄A'}(M')) =
      (principalPartsBaseChangeMap k (((g.restrictScalars B).comp f) : M →ₗ[B] M'') :
        P^{k}_{B⁄A}(M) →ₗ[B] P^{k}_{B''⁄A''}(M'')) := by
  -- The source quotient is generated by the universal classes `[m]`, so it suffices to compare
  -- both maps on those generators.
  apply principal_parts_linear_map_eq_of_apply_universal_differential_eq
    (R := A) (S := B) (M := M) (Q := P^{k}_{B''⁄A''}(M'')) k
  intro m
  -- Each side sends `[m]` to the target universal class of `g (f m)`.
  calc
    ((((principalPartsBaseChangeMap k g :
          P^{k}_{B'⁄A'}(M') →ₗ[B'] P^{k}_{B''⁄A''}(M'')).restrictScalars B).comp
        (principalPartsBaseChangeMap k f :
          P^{k}_{B⁄A}(M) →ₗ[B] P^{k}_{B'⁄A'}(M')))
        (principal_parts_universal_differential (R := A) (S := B) (M := M) k m)) =
        ((principalPartsBaseChangeMap k g :
          P^{k}_{B'⁄A'}(M') →ₗ[B'] P^{k}_{B''⁄A''}(M'')).restrictScalars B)
          (principal_parts_universal_differential (R := A') (S := B') (M := M') k (f m)) := by
            rw [LinearMap.comp_apply,
              principalPartsBaseChangeMap_apply_universal_differential
                (A := A) (B := B) (A' := A') (B' := B') (M := M) (M' := M') k f m]
    _ =
        principal_parts_universal_differential (R := A'') (S := B'') (M := M'') k (g (f m)) := by
          simpa using
            (principalPartsBaseChangeMap_apply_universal_differential
              (A := A') (B := B') (A' := A'') (B' := B'') (M := M') (M' := M'') k g (f m))
    _ =
        (principalPartsBaseChangeMap k (((g.restrictScalars B).comp f) : M →ₗ[B] M'') :
          P^{k}_{B⁄A}(M) →ₗ[B] P^{k}_{B''⁄A''}(M''))
          (principal_parts_universal_differential (R := A) (S := B) (M := M) k m) := by
            symm
            exact principalPartsBaseChangeMap_apply_universal_differential
              (A := A) (B := B) (A' := A'') (B' := B'') (M := M) (M' := M'') k
              (((g.restrictScalars B).comp f) : M →ₗ[B] M'') m

end Composition

end
