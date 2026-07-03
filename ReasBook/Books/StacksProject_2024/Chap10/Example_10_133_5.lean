import Mathlib
import StacksProject_2024.Chap10.Definition_10_133_1
import StacksProject_2024.Chap10.Lemma_10_133_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open LinearMap
open KaehlerDifferential

variable {R : Type u} {S : Type u} {N : Type u}
variable [CommRing R] [CommRing S] [AddCommGroup N]
variable [Algebra R S] [Module S N] [Module R N]
variable [SMulCommClass S R S] [SMulCommClass S R N] [IsScalarTower R S N]

/- Domain triage:
* primary domain: first principal parts and first-order differential operators on the
  `R`-algebra `S`;
* sampled owner API:
  `principal_parts_module`,
  `principal_parts_linear_map_equiv_differential_operators`,
  `LinearMap.IsDifferentialOperatorOfOrder`,
  `differential_operators_order_le`,
  `KaehlerDifferential.linearMapEquivDerivation`;
* source-facing owner: `principal_parts_module R S S 1`;
* core/canonical operator owner: `differential_operators_order_le R S S 1 N`;
* bridge/view: the operator-side decomposition into a derivation part and the value at `1`.

Primitive data are the source-facing owner `P^1_{S/R}` from `principal_parts_module`, the
operator owner `differential_operators_order_le R S S 1 N`, and the universal-derivation
equivalence `linearMapEquivDerivation`. The derivation part, the operator-side product
decomposition, and the resulting equivalence `P^1_{S/R} ≃ Ω[S⁄R] × S` are all derived API and
should reuse those owners rather than rebuilding a parallel wrapper. -/

local notation "DO₁" => differential_operators_order_le R S S 1 N
local notation "P^1_{" S "⁄" R "}" => principal_parts_module R S S 1

/-- The multiplication operator `g ↦ g • x` viewed as an `R`-linear map `S → N`. -/
private def firstOrderMultiplicationLinearMap (x : N) : S →ₗ[R] N :=
  LinearMap.smulRight (LinearMap.id : S →ₗ[R] S) x

/-- The `R`-linear map obtained from `D` by removing the multiplication operator by `D(1)`. -/
private def firstOrderDerivationLinearMap (D : DO₁) : S →ₗ[R] N :=
  D.1 - firstOrderMultiplicationLinearMap (D.1 1)

-- Proof sketch: the order-`1` commutator condition forces the correction
-- `g ↦ D g - g • D 1` to satisfy the Leibniz rule, and the subtraction removes the constant part.
/-- The corrected linear map `g ↦ D(g) - g • D(1)` satisfies the Leibniz rule when `D` has order
at most `1`. -/
private theorem firstOrderDerivationLinearMap_leibniz
    (D : DO₁) :
    ∀ g h : S,
      firstOrderDerivationLinearMap D (g * h) =
        g • firstOrderDerivationLinearMap D h +
          h • firstOrderDerivationLinearMap D g := by
  intro g h
  -- Use the order-zero commutator description at the fixed scalar `g`.
  have hD := D.2
  change D.1.IsDifferentialOperatorOfOrder S 1 at hD
  rw [LinearMap.isDifferentialOperatorOfOrder_succ_iff] at hD
  have hcommZero := hD g
  rw [LinearMap.isDifferentialOperatorOfOrder_zero_iff] at hcommZero
  have hcomm :
      D.1 (g * h) - g • D.1 h =
        h • (D.1 g - g • D.1 1) := by
    simpa [LinearMap.scalarCommutator_apply] using hcommZero h (1 : S)
  -- Rearranging the commutator identity gives the Leibniz rule for the corrected map.
  calc
    firstOrderDerivationLinearMap D (g * h)
        = D.1 (g * h) - (g * h) • D.1 1 := by
            rfl
    _ = (g • D.1 h + h • (D.1 g - g • D.1 1)) - (g * h) • D.1 1 := by
          simpa [add_comm] using congrArg (fun z ↦ z + g • D.1 h - (g * h) • D.1 1) hcomm
    _ = g • (D.1 h - h • D.1 1) + h • (D.1 g - g • D.1 1) := by
          simp [sub_eq_add_neg, smul_add, add_smul, smul_sub, smul_smul, mul_comm,
            mul_left_comm, mul_assoc, add_assoc, add_left_comm, add_comm]
    _ = g • firstOrderDerivationLinearMap D h +
          h • firstOrderDerivationLinearMap D g := by
          rfl

/-- The derivation part `σ_D(g) = D(g) - g • D(1)` of a first-order differential operator. -/
def firstOrderDerivationPart
    (D : DO₁) :
    Derivation R S N :=
  Derivation.mk' (firstOrderDerivationLinearMap D)
    (firstOrderDerivationLinearMap_leibniz D)

-- Proof sketch: derivations are first-order differential operators, the map
-- `g ↦ g • x` is also first-order, and the recursive definition is stable under addition.
/-- A derivation plus multiplication by a fixed element of `N` is a first-order differential
operator. -/
private theorem derivation_add_smulRight_isDifferentialOperatorOfOrder_one
    (δ : Derivation R S N) (x : N) :
    (δ.toLinearMap + firstOrderMultiplicationLinearMap x).IsDifferentialOperatorOfOrder S 1 :=
  by
    -- Each scalar commutator is multiplication by the value of the derivation.
    rw [LinearMap.isDifferentialOperatorOfOrder_succ_iff]
    intro g
    rw [LinearMap.isDifferentialOperatorOfOrder_zero_iff]
    intro a h
    have hcomm_apply (t : S) :
        ((δ.toLinearMap + firstOrderMultiplicationLinearMap x).scalarCommutator g) t =
          t • δ g := by
      simp [LinearMap.scalarCommutator_apply, firstOrderMultiplicationLinearMap, Derivation.leibniz,
        smul_add, sub_eq_add_neg, smul_smul, mul_comm, mul_left_comm, mul_assoc, add_assoc,
        add_left_comm, add_comm]
    calc
      ((δ.toLinearMap + firstOrderMultiplicationLinearMap x).scalarCommutator g) (a • h)
          = (a • h) • δ g := by
              simpa using hcomm_apply (a • h)
      _ = a • (h • δ g) := by
            simp [smul_smul, mul_comm, mul_left_comm, mul_assoc]
      _ = a • ((δ.toLinearMap + firstOrderMultiplicationLinearMap x).scalarCommutator g h) := by
            rw [hcomm_apply]

/-- The first-order differential operator attached to a derivation and an element of `N`. -/
private def firstOrderDifferentialOperatorOfDerivationProd (p : Derivation R S N × N) :
    DO₁ :=
  ⟨p.1.toLinearMap + firstOrderMultiplicationLinearMap p.2,
    derivation_add_smulRight_isDifferentialOperatorOfOrder_one p.1 p.2⟩

/-- The derivation part is additive in the first-order differential operator. -/
private theorem firstOrderDerivationPart_map_add (D E : DO₁) :
    firstOrderDerivationPart (D + E) =
      firstOrderDerivationPart D + firstOrderDerivationPart E := by
  -- The correction formula is pointwise additive in the operator.
  ext g
  simp [firstOrderDerivationPart, firstOrderDerivationLinearMap, firstOrderMultiplicationLinearMap,
    sub_eq_add_neg, smul_add, add_smul, add_assoc, add_left_comm, add_comm]

/-- The derivation part is `S`-linear in the first-order differential operator. -/
private theorem firstOrderDerivationPart_map_smul (a : S) (D : DO₁) :
    firstOrderDerivationPart (a • D) = a • firstOrderDerivationPart D := by
  -- The correction formula is pointwise `S`-linear in the operator.
  ext g
  simp [firstOrderDerivationPart, firstOrderDerivationLinearMap, firstOrderMultiplicationLinearMap,
    smul_sub, smul_smul, mul_comm, mul_left_comm, mul_assoc]

/-- Helper for Example 10.133.5: the decomposition map `D ↦ (σ_D, D(1))` is additive. -/
private theorem firstOrderDifferentialOperatorToDerivationProd_map_add
    (D E : DO₁) :
    (firstOrderDerivationPart (D + E), (D + E).1 1) =
      (firstOrderDerivationPart D, D.1 1) + (firstOrderDerivationPart E, E.1 1) := by
  -- Both components are visibly additive.
  exact Prod.ext (firstOrderDerivationPart_map_add D E) rfl

/-- Helper for Example 10.133.5: the decomposition map `D ↦ (σ_D, D(1))` is `S`-linear. -/
private theorem firstOrderDifferentialOperatorToDerivationProd_map_smul
    (a : S) (D : DO₁) :
    (firstOrderDerivationPart (a • D), (a • D).1 1) =
      a • (firstOrderDerivationPart D, D.1 1) := by
  -- Both components are visibly `S`-linear.
  exact Prod.ext (firstOrderDerivationPart_map_smul a D) rfl

/-- The decomposition map `D ↦ (σ_D, D(1))`, packaged as an `S`-linear map. -/
private def firstOrderDifferentialOperatorToDerivationProd :
    DO₁ →ₗ[S] Derivation R S N × N where
  toFun D := (firstOrderDerivationPart D, D.1 1)
  map_add' := firstOrderDifferentialOperatorToDerivationProd_map_add
  map_smul' := firstOrderDifferentialOperatorToDerivationProd_map_smul

/-- Recombining a derivation and a value at `1` is additive. -/
private theorem firstOrderDifferentialOperatorOfDerivationProd_map_add
    (p q : Derivation R S N × N) :
    firstOrderDifferentialOperatorOfDerivationProd (p + q) =
      firstOrderDifferentialOperatorOfDerivationProd p +
        firstOrderDifferentialOperatorOfDerivationProd q := by
  -- Recombining respects addition componentwise.
  apply Subtype.ext
  ext g
  simp [firstOrderDifferentialOperatorOfDerivationProd, firstOrderMultiplicationLinearMap,
    add_assoc, add_left_comm, add_comm, smul_add, add_smul]

/-- Recombining a derivation and a value at `1` is `S`-linear. -/
private theorem firstOrderDifferentialOperatorOfDerivationProd_map_smul
    (a : S) (p : Derivation R S N × N) :
    firstOrderDifferentialOperatorOfDerivationProd (a • p) =
      a • firstOrderDifferentialOperatorOfDerivationProd p := by
  -- Recombining respects the `S`-action componentwise.
  apply Subtype.ext
  ext g
  simp [firstOrderDifferentialOperatorOfDerivationProd, firstOrderMultiplicationLinearMap,
    smul_add, smul_smul, mul_comm, mul_left_comm, mul_assoc]

/-- The inverse decomposition map `(δ, x) ↦ δ + λ_x`, packaged as an `S`-linear map. -/
private def firstOrderDifferentialOperatorOfDerivationProdLinear :
    (Derivation R S N × N) →ₗ[S] DO₁ where
  toFun := firstOrderDifferentialOperatorOfDerivationProd
  map_add' := firstOrderDifferentialOperatorOfDerivationProd_map_add
  map_smul' := firstOrderDifferentialOperatorOfDerivationProd_map_smul

-- Proof sketch: reconstruct `D` pointwise from its derivation part and its value at `1`, using the
-- defining formula `σ_D(g) = D(g) - g • D(1)`.
/-- Recombining the derivation part of a first-order operator with its value at `1` recovers the
original operator. -/
private theorem firstOrderDifferentialOperatorEquivDerivationProd_left_inv
    (D : DO₁) :
    firstOrderDifferentialOperatorOfDerivationProd
        ((firstOrderDerivationPart D), D.1 1) = D := by
  -- Reinsert the corrected derivation part and the value at `1`.
  apply Subtype.ext
  ext g
  simp [firstOrderDifferentialOperatorOfDerivationProd, firstOrderDerivationPart,
    firstOrderDerivationLinearMap, firstOrderMultiplicationLinearMap, sub_eq_add_neg,
    add_assoc, add_left_comm, add_comm]

-- Proof sketch: for `δ + λ_x`, the corrected part `σ_{δ + λ_x}` is `δ`, because derivations
-- vanish at `1` and `λ_x(1) = x`; the second component is exactly `x`.
/-- The derivation-and-value pair attached to `δ + λ_x` is exactly `(δ, x)`. -/
private theorem firstOrderDifferentialOperatorEquivDerivationProd_right_inv
    (p : Derivation R S N × N) :
    (firstOrderDerivationPart (firstOrderDifferentialOperatorOfDerivationProd p),
        (firstOrderDifferentialOperatorOfDerivationProd p).1 1) = p := by
  rcases p with ⟨δ, x⟩
  -- The correction removes exactly the multiplication part, and the value at `1` is `x`.
  apply Prod.ext
  · ext g
    simp [firstOrderDerivationPart, firstOrderDifferentialOperatorOfDerivationProd,
      firstOrderDerivationLinearMap, firstOrderMultiplicationLinearMap, Derivation.map_one_eq_zero,
      sub_eq_add_neg, smul_add, add_smul, smul_smul, mul_comm, mul_left_comm, mul_assoc,
      add_assoc, add_left_comm, add_comm]
  · simp [firstOrderDifferentialOperatorOfDerivationProd, firstOrderMultiplicationLinearMap,
      Derivation.map_one_eq_zero]

/-- Helper for Example 10.133.5: the recombination map is a left inverse on the product side. -/
private theorem firstOrderDifferentialOperatorEquivDerivationProd_comp_from :
    firstOrderDifferentialOperatorToDerivationProd.comp
        firstOrderDifferentialOperatorOfDerivationProdLinear =
      (LinearMap.id : (Derivation R S N × N) →ₗ[S] Derivation R S N × N) := by
  -- The pointwise inverse statement upgrades to equality of linear maps.
  apply LinearMap.ext
  intro p
  exact firstOrderDifferentialOperatorEquivDerivationProd_right_inv p

/-- Helper for Example 10.133.5: the decomposition map is a left inverse on the operator side. -/
private theorem firstOrderDifferentialOperatorEquivDerivationProd_comp_to :
    firstOrderDifferentialOperatorOfDerivationProdLinear.comp
        firstOrderDifferentialOperatorToDerivationProd =
      (LinearMap.id : DO₁ →ₗ[S] DO₁) := by
  -- The pointwise inverse statement upgrades to equality of linear maps.
  apply LinearMap.ext
  intro D
  exact firstOrderDifferentialOperatorEquivDerivationProd_left_inv D

/-- Example 10.133.5 (1): first-order differential operators `S → N` decompose canonically into a
derivation part and a multiplication operator by the value at `1`, giving an `S`-linear
equivalence with `Derivation R S N × N`. -/
def firstOrderDifferentialOperatorEquivDerivationProd :
    DO₁ ≃ₗ[S] Derivation R S N × N :=
  LinearEquiv.ofLinear
    firstOrderDifferentialOperatorToDerivationProd
    firstOrderDifferentialOperatorOfDerivationProdLinear
    firstOrderDifferentialOperatorEquivDerivationProd_comp_from
    firstOrderDifferentialOperatorEquivDerivationProd_comp_to

/-- Example 10.133.5 (2): via the universal property of `Ω[S⁄R]`, first-order differential
operators `S → M` are `S`-linearly equivalent to pairs consisting of an `S`-linear map
`Ω[S⁄R] → M` and an element of `M`. This bridge/view is the canonical general decomposition,
specialized below to recover the source-facing decomposition `P^1_{S/R} ≃ Ω[S⁄R] ⊕ S`. -/
noncomputable abbrev firstOrderDifferentialOperatorEquivDifferentialsProd
    (M : Type u) [AddCommGroup M] [Module S M] [Module R M] [SMulCommClass S R M]
    [IsScalarTower R S M] :
    differential_operators_order_le R S S 1 M ≃ₗ[S] (Ω[S⁄R] →ₗ[S] M) × M :=
  firstOrderDifferentialOperatorEquivDerivationProd.trans
    ((linearMapEquivDerivation R S).symm.prodCongr (LinearEquiv.refl S M))

/-- Helper for Example 10.133.5: postcomposition carries the derivation part by composition. -/
private theorem firstOrderDifferentialOperatorEquivDerivationProd_natural
    {N' : Type u} [AddCommGroup N'] [Module S N'] [Module R N']
    [SMulCommClass S R N'] [IsScalarTower R S N']
    (f : N →ₗ[S] N') (D : DO₁) :
    firstOrderDifferentialOperatorToDerivationProd (R := R) (S := S) (N := N')
        (differential_operators_postcompose (R := R) (S := S) (M := S) 1 f D) =
      (f.compDer (firstOrderDerivationPart D), f (D.1 1)) := by
  -- TODO: unfold `differential_operators_postcompose` to the cod-restricted composite,
  -- rewrite the derivation component as `g ↦ f (D g - g • D 1)`, and finish the pair equality by
  -- `Prod.ext`; the remaining blocker is the exact coercion path from the cod-restricted subtype.
  sorry

/-- Helper for Example 10.133.5: the Kähler-differential lift commutes with postcomposition. -/
private theorem linearMapEquivDerivation_symm_compDer
    {M M' : Type u} [AddCommGroup M] [Module S M] [Module R M] [SMulCommClass S R M]
    [IsScalarTower R S M] [AddCommGroup M'] [Module S M'] [Module R M']
    [SMulCommClass S R M'] [IsScalarTower R S M']
    (f : M →ₗ[S] M') (δ : Derivation R S M) :
    (linearMapEquivDerivation R S).symm (f.compDer δ) =
      (LinearMap.compRight S f) ((linearMapEquivDerivation R S).symm δ) := by
  -- Both candidate linear maps lift the same derivation through `Ω[S⁄R]`.
  apply Derivation.liftKaehlerDifferential_unique
  ext x
  simp [LinearMap.compRight_apply, Derivation.liftKaehlerDifferential_comp_D]

/-- Helper for Example 10.133.5: the decomposition into a differential part and a value at `1`
is natural under postcomposition. -/
private theorem firstOrderDifferentialOperatorEquivDifferentialsProd_natural
    (M M' : Type u) [AddCommGroup M] [Module S M] [Module R M] [SMulCommClass S R M]
    [IsScalarTower R S M] [AddCommGroup M'] [Module S M'] [Module R M']
    [SMulCommClass S R M'] [IsScalarTower R S M']
    (f : M →ₗ[S] M')
    (D : differential_operators_order_le R S S 1 M) :
    firstOrderDifferentialOperatorEquivDifferentialsProd (R := R) (S := S) M'
        (differential_operators_postcompose (R := R) (S := S) (M := S) 1 f D) =
      ((LinearMap.compRight S f)
          (firstOrderDifferentialOperatorEquivDifferentialsProd (R := R) (S := S) M D).1,
        f (firstOrderDifferentialOperatorEquivDifferentialsProd (R := R) (S := S) M D).2) := by
  -- Route correction: push the operator-side naturality equality through the universal-property
  -- equivalence instead of expanding the principal-parts comparison inline.
  change
      (((linearMapEquivDerivation R S).symm
          (firstOrderDifferentialOperatorToDerivationProd (R := R) (S := S) (N := M')
            (differential_operators_postcompose (R := R) (S := S) (M := S) 1 f D)).1),
        (firstOrderDifferentialOperatorToDerivationProd (R := R) (S := S) (N := M')
          (differential_operators_postcompose (R := R) (S := S) (M := S) 1 f D)).2) =
      ((LinearMap.compRight S f)
          (((linearMapEquivDerivation R S).symm
            (firstOrderDifferentialOperatorToDerivationProd (R := R) (S := S) (N := M) D).1)),
        f (firstOrderDifferentialOperatorToDerivationProd (R := R) (S := S) (N := M) D).2)
  rw [firstOrderDifferentialOperatorEquivDerivationProd_natural
    (R := R) (S := S) (N := M) (N' := M') f D]
  -- The derivation component is exactly the `Ω[S⁄R]`-linear map transported by `compRight`.
  apply Prod.ext
  · simpa [firstOrderDifferentialOperatorToDerivationProd]
      using linearMapEquivDerivation_symm_compDer
        (R := R) (S := S) f (firstOrderDerivationPart D)
  · rfl

/-- Helper for Example 10.133.5: an `S`-linear map `S → M` is determined by its value at `1`. -/
private theorem linearMap_eq_smulRight_apply_one
    {M : Type u} [AddCommGroup M] [Module S M]
    (f : S →ₗ[S] M) :
    f = LinearMap.smulRight (LinearMap.id : S →ₗ[S] S) (f 1) := by
  -- `S`-linearity forces every value to be a scalar multiple of the value at `1`.
  ext s
  simpa using f.map_smul s (1 : S)

/-- Helper for Example 10.133.5: the `S`-component of a product map is determined by the image of
`(0, 1)`. -/
private theorem linearMap_comp_inr_eq_smulRight_apply_zero_one
    {M : Type u} [AddCommGroup M] [Module S M]
    (f : Ω[S⁄R] × S →ₗ[S] M) :
    f.comp (LinearMap.inr S Ω[S⁄R] S) =
      LinearMap.smulRight (LinearMap.id : S →ₗ[S] S) (f (0, 1)) := by
  -- Restrict to the second factor and apply the `S → M` classification above.
  simpa using linearMap_eq_smulRight_apply_one (f.comp (LinearMap.inr S Ω[S⁄R] S))

/-- Helper for Example 10.133.5: a map out of `Ω[S⁄R] × S` is determined by its cotangent part
and its value on `(0, 1)`. -/
private theorem linearMap_prod_eq_coprod_inl_smulRight_apply_zero_one
    {M : Type u} [AddCommGroup M] [Module S M]
    (f : Ω[S⁄R] × S →ₗ[S] M) :
    f =
      (f.comp (LinearMap.inl S Ω[S⁄R] S)).coprod
        (LinearMap.smulRight (LinearMap.id : S →ₗ[S] S) (f (0, 1))) := by
  -- Split `f` across the product and rewrite the `S`-factor by its value at `1`.
  rw [← linearMap_comp_inr_eq_smulRight_apply_zero_one (f := f)]
  exact (LinearMap.coprod_comp_inl_inr f).symm

private noncomputable def firstPrincipalPartsToDifferentialsProd :
    P^1_{S⁄R} →ₗ[S] Ω[S⁄R] × S :=
  (principal_parts_linear_map_equiv_differential_operators R S S 1 (Ω[S⁄R] × S)).symm
    (firstOrderDifferentialOperatorOfDerivationProd
      (((linearMapEquivDerivation R S)
          (LinearMap.inl S Ω[S⁄R] S : Ω[S⁄R] →ₗ[S] Ω[S⁄R] × S)),
        ((0 : Ω[S⁄R]), (1 : S))))

private noncomputable def differentialsProdToFirstPrincipalParts :
    Ω[S⁄R] × S →ₗ[S] P^1_{S⁄R} :=
  let p :=
    firstOrderDifferentialOperatorEquivDifferentialsProd (P^1_{S⁄R})
      ((principal_parts_linear_map_equiv_differential_operators R S S 1 P^1_{S⁄R})
        (LinearMap.id : P^1_{S⁄R} →ₗ[S] P^1_{S⁄R}))
  p.1.coprod (LinearMap.smulRight (LinearMap.id : S →ₗ[S] S) p.2)

private theorem firstPrincipalPartsToDifferentialsProd_comp_differentialsProdToFirstPrincipalParts :
    (firstPrincipalPartsToDifferentialsProd : P^1_{S⁄R} →ₗ[S] Ω[S⁄R] × S).comp
        (differentialsProdToFirstPrincipalParts : Ω[S⁄R] × S →ₗ[S] P^1_{S⁄R}) =
      (LinearMap.id : Ω[S⁄R] × S →ₗ[S] Ω[S⁄R] × S) := by
  -- TODO: use `firstOrderDifferentialOperatorEquivDifferentialsProd_natural` together with
  -- `principal_parts_linear_map_equiv_differential_operators_natural` to identify the composite
  -- by its cotangent component and its value at `(0, 1)`, then reconstruct the whole map via
  -- `linearMap_prod_eq_coprod_inl_smulRight_apply_zero_one`.
  sorry

private theorem differentialsProdToFirstPrincipalParts_comp_firstPrincipalPartsToDifferentialsProd :
    (differentialsProdToFirstPrincipalParts : Ω[S⁄R] × S →ₗ[S] P^1_{S⁄R}).comp
        (firstPrincipalPartsToDifferentialsProd : P^1_{S⁄R} →ₗ[S] Ω[S⁄R] × S) =
      (LinearMap.id : P^1_{S⁄R} →ₗ[S] P^1_{S⁄R}) := by
  -- TODO: push the composite through
  -- `principal_parts_linear_map_equiv_differential_operators R S S 1 P^1_{S⁄R}`,
  -- rewrite the resulting operator by
  -- `firstOrderDifferentialOperatorEquivDifferentialsProd_natural`, and use the pair `p`
  -- defining `differentialsProdToFirstPrincipalParts` to recover the represented identity.
  sorry

/-- Example 10.133.5 (2): specializing the principal-parts representation of order-one
differential operators to the source-facing owner `P^1_{S/R}` yields a canonical decomposition
`P^1_{S/R} ≃ Ω[S⁄R] × S`, i.e. the two-term direct-sum form `P^1_{S/R} = Ω_{S/R} ⊕ S`. -/
noncomputable def firstPrincipalPartsEquivDifferentialsProd :
    P^1_{S⁄R} ≃ₗ[S] Ω[S⁄R] × S :=
  LinearEquiv.ofLinear
    firstPrincipalPartsToDifferentialsProd
    differentialsProdToFirstPrincipalParts
    firstPrincipalPartsToDifferentialsProd_comp_differentialsProdToFirstPrincipalParts
    differentialsProdToFirstPrincipalParts_comp_firstPrincipalPartsToDifferentialsProd

end
