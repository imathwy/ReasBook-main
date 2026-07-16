import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_133_1
import stacks_proof.stacks_project.Chap10.Lemma_10_133_3

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
          simp [sub_eq_add_neg, smul_add, smul_smul, mul_comm, add_left_comm, add_comm]
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
      simp [firstOrderMultiplicationLinearMap, Derivation.leibniz, smul_add, sub_eq_add_neg,
        smul_smul, add_assoc, add_left_comm, add_comm]
    calc
      ((δ.toLinearMap + firstOrderMultiplicationLinearMap x).scalarCommutator g) (a • h)
          = (a • h) • δ g := by
              simpa using hcomm_apply (a • h)
      _ = a • (h • δ g) := by
            simp [smul_smul]
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
    sub_eq_add_neg, smul_add, add_assoc, add_left_comm, add_comm]

/-- The derivation part is `S`-linear in the first-order differential operator. -/
private theorem firstOrderDerivationPart_map_smul (a : S) (D : DO₁) :
    firstOrderDerivationPart (a • D) = a • firstOrderDerivationPart D := by
  -- The correction formula is pointwise `S`-linear in the operator.
  ext g
  simp [firstOrderDerivationPart, firstOrderDerivationLinearMap, firstOrderMultiplicationLinearMap,
    smul_sub, smul_smul, mul_comm]

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
    add_assoc, add_left_comm, add_comm, smul_add]

/-- Recombining a derivation and a value at `1` is `S`-linear. -/
private theorem firstOrderDifferentialOperatorOfDerivationProd_map_smul
    (a : S) (p : Derivation R S N × N) :
    firstOrderDifferentialOperatorOfDerivationProd (a • p) =
      a • firstOrderDifferentialOperatorOfDerivationProd p := by
  -- Recombining respects the `S`-action componentwise.
  apply Subtype.ext
  ext g
  simp [firstOrderDifferentialOperatorOfDerivationProd, firstOrderMultiplicationLinearMap,
    smul_add, smul_smul, mul_comm]

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
    add_left_comm, add_comm]

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
      sub_eq_add_neg, add_assoc, add_comm]
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
@[stacks 09CM]
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
@[stacks 09CM]
noncomputable abbrev firstOrderDifferentialOperatorEquivDifferentialsProd
    (M : Type u) [AddCommGroup M] [Module S M] [Module R M] [SMulCommClass S R M]
    [IsScalarTower R S M] :
    differential_operators_order_le R S S 1 M ≃ₗ[S] (Ω[S⁄R] →ₗ[S] M) × M :=
  firstOrderDifferentialOperatorEquivDerivationProd.trans
    ((linearMapEquivDerivation R S).symm.prodCongr (LinearEquiv.refl S M))

/-- Helper for Chap10 Example 10 133 5: postcomposition evaluates by applying the target map
to the value of the original differential operator. -/
private theorem differentialOperatorsPostcompose_apply
    {N' : Type u} [AddCommGroup N'] [Module S N'] [Module R N']
    [SMulCommClass S R N'] [IsScalarTower R S N']
    (k : ℕ) (f : N →ₗ[S] N')
    (D : differential_operators_order_le R S S k N) (s : S) :
    (differential_operators_postcompose (R := R) (S := S) (M := S) k f D).1 s =
      f (D.1 s) := by
  -- The postcomposition map is defined by cod-restricting the ordinary composite.
  rfl

/-- Helper for Example 10.133.5: postcomposition carries the derivation part by composition. -/
private theorem firstOrderDifferentialOperatorEquivDerivationProd_natural
    {N' : Type u} [AddCommGroup N'] [Module S N'] [Module R N']
    [SMulCommClass S R N'] [IsScalarTower R S N']
    (f : N →ₗ[S] N') (D : DO₁) :
    firstOrderDifferentialOperatorToDerivationProd (R := R) (S := S) (N := N')
        (differential_operators_postcompose (R := R) (S := S) (M := S) 1 f D) =
      (f.compDer (firstOrderDerivationPart D), f (D.1 1)) := by
  -- Compare the derivation component pointwise, then compare the value at `1`.
  apply Prod.ext
  · ext s
    simp [firstOrderDifferentialOperatorToDerivationProd, firstOrderDerivationPart,
      firstOrderDerivationLinearMap, firstOrderMultiplicationLinearMap,
      differentialOperatorsPostcompose_apply]
  · simp [firstOrderDifferentialOperatorToDerivationProd,
      differentialOperatorsPostcompose_apply]

omit [SMulCommClass S R S] in
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

omit [SMulCommClass S R S] in
/-- Helper for Chap10 Example 10 133 5: principal-parts representatives commute with
postcomposition in the target module. -/
private theorem principalPartsPostcompose_apply
    {M M' : Type u} [AddCommGroup M] [Module S M] [Module R M] [SMulCommClass S R M]
    [IsScalarTower R S M] [AddCommGroup M'] [Module S M'] [Module R M']
    [SMulCommClass S R M'] [IsScalarTower R S M']
    (f : M →ₗ[S] M') (L : P^1_{S⁄R} →ₗ[S] M) :
    (principal_parts_linear_map_equiv_differential_operators R S S 1 M') (f.comp L) =
      differential_operators_postcompose (R := R) (S := S) (M := S) 1 f
        ((principal_parts_linear_map_equiv_differential_operators R S S 1 M) L) := by
  -- Apply the naturality equality of the representing equivalence to the map `L`.
  have hnat :=
    congrArg (fun g ↦ g L)
      (principal_parts_linear_map_equiv_differential_operators_natural
        (R := R) (S := S) (M := S) 1 f)
  simpa [LinearMap.compRight_apply] using hnat.symm

/-- Helper for Chap10 Example 10 133 5: maps out of first principal parts are equivalently
their differential component and their value component. -/
private noncomputable abbrev principalPartsDifferentialsProdEquiv
    (M : Type u) [AddCommGroup M] [Module S M] [Module R M] [SMulCommClass S R M]
    [IsScalarTower R S M] :
    (P^1_{S⁄R} →ₗ[S] M) ≃ₗ[S] (Ω[S⁄R] →ₗ[S] M) × M :=
  (principal_parts_linear_map_equiv_differential_operators R S S 1 M).trans
    (firstOrderDifferentialOperatorEquivDifferentialsProd (R := R) (S := S) M)

/-- Helper for Chap10 Example 10 133 5: the principal-parts decomposition is natural under
postcomposition. -/
private theorem principalPartsDifferentialsProdEquiv_natural
    (M M' : Type u) [AddCommGroup M] [Module S M] [Module R M] [SMulCommClass S R M]
    [IsScalarTower R S M] [AddCommGroup M'] [Module S M'] [Module R M']
    [SMulCommClass S R M'] [IsScalarTower R S M']
    (f : M →ₗ[S] M') (L : P^1_{S⁄R} →ₗ[S] M) :
    principalPartsDifferentialsProdEquiv (R := R) (S := S) M' (f.comp L) =
      ((LinearMap.compRight S f)
          (principalPartsDifferentialsProdEquiv (R := R) (S := S) M L).1,
        f (principalPartsDifferentialsProdEquiv (R := R) (S := S) M L).2) := by
  -- First move postcomposition through principal parts, then through the first-order splitting.
  have hpost := principalPartsPostcompose_apply (R := R) (S := S) (f := f) (L := L)
  have hfirst :=
    firstOrderDifferentialOperatorEquivDifferentialsProd_natural
      (R := R) (S := S) M M' f
      ((principal_parts_linear_map_equiv_differential_operators R S S 1 M) L)
  calc
    principalPartsDifferentialsProdEquiv (R := R) (S := S) M' (f.comp L)
        =
          firstOrderDifferentialOperatorEquivDifferentialsProd (R := R) (S := S) M'
            ((principal_parts_linear_map_equiv_differential_operators R S S 1 M')
              (f.comp L)) := by
            rfl
    _ =
          firstOrderDifferentialOperatorEquivDifferentialsProd (R := R) (S := S) M'
            (differential_operators_postcompose (R := R) (S := S) (M := S) 1 f
              ((principal_parts_linear_map_equiv_differential_operators R S S 1 M) L)) := by
            rw [hpost]
    _ =
        ((LinearMap.compRight S f)
            (firstOrderDifferentialOperatorEquivDifferentialsProd (R := R) (S := S) M
              ((principal_parts_linear_map_equiv_differential_operators R S S 1 M) L)).1,
          f (firstOrderDifferentialOperatorEquivDifferentialsProd (R := R) (S := S) M
            ((principal_parts_linear_map_equiv_differential_operators R S S 1 M) L)).2) := by
            exact hfirst
    _ =
      ((LinearMap.compRight S f)
          (principalPartsDifferentialsProdEquiv (R := R) (S := S) M L).1,
        f (principalPartsDifferentialsProdEquiv (R := R) (S := S) M L).2) := by
      rfl

/-- Helper for Example 10.133.5: an `S`-linear map `S → M` is determined by its value at `1`. -/
private theorem linearMap_eq_smulRight_apply_one
    {M : Type u} [AddCommGroup M] [Module S M]
    (f : S →ₗ[S] M) :
    f = LinearMap.smulRight (LinearMap.id : S →ₗ[S] S) (f 1) := by
  -- `S`-linearity forces every value to be a scalar multiple of the value at `1`.
  apply LinearMap.ext
  intro s
  simpa using f.map_smul s (1 : S)

omit [SMulCommClass S R S] in
/-- Helper for Example 10.133.5: the `S`-component of a product map is determined by the image of
`(0, 1)`. -/
private theorem linearMap_comp_inr_eq_smulRight_apply_zero_one
    {M : Type u} [AddCommGroup M] [Module S M]
    (f : Ω[S⁄R] × S →ₗ[S] M) :
    f.comp (LinearMap.inr S Ω[S⁄R] S) =
      LinearMap.smulRight (LinearMap.id : S →ₗ[S] S) (f (0, 1)) := by
  -- Restrict to the second factor and apply the `S → M` classification above.
  simpa using linearMap_eq_smulRight_apply_one (f.comp (LinearMap.inr S Ω[S⁄R] S))

omit [SMulCommClass S R S] in
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

/-- Helper for Chap10 Example 10 133 5: the universal map from first principal parts to
`Ω[S⁄R] × S`, represented by the tautological cotangent component and value `1`. -/
private noncomputable def firstPrincipalPartsToDifferentialsProd :
    P^1_{S⁄R} →ₗ[S] Ω[S⁄R] × S :=
  (principalPartsDifferentialsProdEquiv (R := R) (S := S) (Ω[S⁄R] × S)).symm
    (LinearMap.inl S Ω[S⁄R] S, ((0 : Ω[S⁄R]), (1 : S)))

/-- Helper for Chap10 Example 10 133 5: the decomposition pair attached to the identity map on
first principal parts. -/
private noncomputable abbrev firstPrincipalPartsIdentityDecomposition :
    (Ω[S⁄R] →ₗ[S] P^1_{S⁄R}) × P^1_{S⁄R} :=
  principalPartsDifferentialsProdEquiv (R := R) (S := S) P^1_{S⁄R}
    (LinearMap.id : P^1_{S⁄R} →ₗ[S] P^1_{S⁄R})

/-- Helper for Chap10 Example 10 133 5: the universal map has the tautological decomposition
component pair. -/
private theorem firstPrincipalPartsToDifferentialsProd_decomposition :
    principalPartsDifferentialsProdEquiv (R := R) (S := S) (Ω[S⁄R] × S)
        firstPrincipalPartsToDifferentialsProd =
      (LinearMap.inl S Ω[S⁄R] S, ((0 : Ω[S⁄R]), (1 : S))) := by
  -- The map was defined as the inverse image of this pair under the decomposition equivalence.
  simp [firstPrincipalPartsToDifferentialsProd]

/-- Helper for Chap10 Example 10 133 5: postcomposing the identity decomposition by the
universal map recovers the tautological component pair. -/
private theorem firstPrincipalPartsToDifferentialsProd_identityDecomposition :
    ((LinearMap.compRight S firstPrincipalPartsToDifferentialsProd)
        firstPrincipalPartsIdentityDecomposition.1,
      firstPrincipalPartsToDifferentialsProd firstPrincipalPartsIdentityDecomposition.2) =
      (LinearMap.inl S Ω[S⁄R] S, ((0 : Ω[S⁄R]), (1 : S))) := by
  -- Naturality identifies this pair with the decomposition of the universal map itself.
  have hnat :=
    principalPartsDifferentialsProdEquiv_natural
      (R := R) (S := S) (M := P^1_{S⁄R}) (M' := Ω[S⁄R] × S)
      firstPrincipalPartsToDifferentialsProd
      (LinearMap.id : P^1_{S⁄R} →ₗ[S] P^1_{S⁄R})
  rw [← hnat]
  simpa [firstPrincipalPartsIdentityDecomposition]
    using firstPrincipalPartsToDifferentialsProd_decomposition (R := R) (S := S)

/-- Helper for Chap10 Example 10 133 5: the map from `Ω[S⁄R] × S` to first principal parts
recombines the decomposition pair of the identity map. -/
private noncomputable def differentialsProdToFirstPrincipalParts :
    Ω[S⁄R] × S →ₗ[S] P^1_{S⁄R} :=
  firstPrincipalPartsIdentityDecomposition.1.coprod
    (LinearMap.smulRight (LinearMap.id : S →ₗ[S] S)
      firstPrincipalPartsIdentityDecomposition.2)

/-- Helper for Chap10 Example 10 133 5: recombination restricts to the differential component on
the first factor. -/
private theorem differentialsProdToFirstPrincipalParts_comp_inl :
    (differentialsProdToFirstPrincipalParts : Ω[S⁄R] × S →ₗ[S] P^1_{S⁄R}).comp
        (LinearMap.inl S Ω[S⁄R] S) =
      firstPrincipalPartsIdentityDecomposition.1 := by
  -- The `coprod` construction has the chosen first component on the first summand.
  ext x
  simp [differentialsProdToFirstPrincipalParts]

/-- Helper for Chap10 Example 10 133 5: recombination sends `(0, 1)` to the value component of
the identity decomposition. -/
private theorem differentialsProdToFirstPrincipalParts_apply_zero_one :
    differentialsProdToFirstPrincipalParts ((0 : Ω[S⁄R]), (1 : S)) =
      firstPrincipalPartsIdentityDecomposition.2 := by
  -- The first summand vanishes and the second summand evaluates at `1`.
  simp [differentialsProdToFirstPrincipalParts]

private theorem firstPrincipalPartsToDifferentialsProd_comp_differentialsProdToFirstPrincipalParts :
    (firstPrincipalPartsToDifferentialsProd : P^1_{S⁄R} →ₗ[S] Ω[S⁄R] × S).comp
        (differentialsProdToFirstPrincipalParts : Ω[S⁄R] × S →ₗ[S] P^1_{S⁄R}) =
      (LinearMap.id : Ω[S⁄R] × S →ₗ[S] Ω[S⁄R] × S) := by
  -- The composite is determined by its restriction to `Ω[S⁄R]` and by the value at `(0, 1)`.
  have hcomponents :=
    firstPrincipalPartsToDifferentialsProd_identityDecomposition (R := R) (S := S)
  have hcot :
      (firstPrincipalPartsToDifferentialsProd : P^1_{S⁄R} →ₗ[S] Ω[S⁄R] × S).comp
          firstPrincipalPartsIdentityDecomposition.1 =
        LinearMap.inl S Ω[S⁄R] S := by
    simpa [LinearMap.compRight_apply] using congrArg Prod.fst hcomponents
  have hval :
      firstPrincipalPartsToDifferentialsProd firstPrincipalPartsIdentityDecomposition.2 =
        ((0 : Ω[S⁄R]), (1 : S)) := by
    simpa using congrArg Prod.snd hcomponents
  have hcomp_inl :
      ((firstPrincipalPartsToDifferentialsProd : P^1_{S⁄R} →ₗ[S] Ω[S⁄R] × S).comp
          differentialsProdToFirstPrincipalParts).comp
          (LinearMap.inl S Ω[S⁄R] S) =
        LinearMap.inl S Ω[S⁄R] S := by
    rw [LinearMap.comp_assoc, differentialsProdToFirstPrincipalParts_comp_inl, hcot]
  have hcomp_zero_one :
      ((firstPrincipalPartsToDifferentialsProd : P^1_{S⁄R} →ₗ[S] Ω[S⁄R] × S).comp
          differentialsProdToFirstPrincipalParts) ((0 : Ω[S⁄R]), (1 : S)) =
        ((0 : Ω[S⁄R]), (1 : S)) := by
    calc
      ((firstPrincipalPartsToDifferentialsProd : P^1_{S⁄R} →ₗ[S] Ω[S⁄R] × S).comp
          differentialsProdToFirstPrincipalParts) ((0 : Ω[S⁄R]), (1 : S))
          =
        firstPrincipalPartsToDifferentialsProd
          (differentialsProdToFirstPrincipalParts ((0 : Ω[S⁄R]), (1 : S))) := by
          rfl
      _ = firstPrincipalPartsToDifferentialsProd firstPrincipalPartsIdentityDecomposition.2 := by
          rw [differentialsProdToFirstPrincipalParts_apply_zero_one]
      _ = ((0 : Ω[S⁄R]), (1 : S)) := hval
  rw [linearMap_prod_eq_coprod_inl_smulRight_apply_zero_one
    (f := (firstPrincipalPartsToDifferentialsProd : P^1_{S⁄R} →ₗ[S] Ω[S⁄R] × S).comp
      differentialsProdToFirstPrincipalParts)]
  rw [hcomp_inl, hcomp_zero_one]
  -- The reconstructed map is visibly the identity on the product.
  apply LinearMap.ext
  intro x
  rcases x with ⟨ω, s⟩
  simp

private theorem differentialsProdToFirstPrincipalParts_comp_firstPrincipalPartsToDifferentialsProd :
    (differentialsProdToFirstPrincipalParts : Ω[S⁄R] × S →ₗ[S] P^1_{S⁄R}).comp
        (firstPrincipalPartsToDifferentialsProd : P^1_{S⁄R} →ₗ[S] Ω[S⁄R] × S) =
      (LinearMap.id : P^1_{S⁄R} →ₗ[S] P^1_{S⁄R}) := by
  -- Apply the decomposition equivalence; naturality reduces the composite to the identity pair.
  apply (principalPartsDifferentialsProdEquiv (R := R) (S := S) P^1_{S⁄R}).injective
  have hnat :=
    principalPartsDifferentialsProdEquiv_natural
      (R := R) (S := S) (M := Ω[S⁄R] × S) (M' := P^1_{S⁄R})
      differentialsProdToFirstPrincipalParts
      firstPrincipalPartsToDifferentialsProd
  rw [hnat, firstPrincipalPartsToDifferentialsProd_decomposition]
  apply Prod.ext
  · simpa [firstPrincipalPartsIdentityDecomposition, LinearMap.compRight_apply]
      using differentialsProdToFirstPrincipalParts_comp_inl (R := R) (S := S)
  · simpa [firstPrincipalPartsIdentityDecomposition]
      using differentialsProdToFirstPrincipalParts_apply_zero_one (R := R) (S := S)

/-- Chap10 Example 10 133 5: specializing the principal-parts representation of order-one
differential operators to the source-facing owner `P^1_{S/R}` yields a canonical decomposition
`P^1_{S/R} ≃ Ω[S⁄R] × S`, i.e. the two-term direct-sum form `P^1_{S/R} = Ω_{S/R} ⊕ S`. -/
@[stacks 09CM]
noncomputable def firstPrincipalPartsEquivDifferentialsProd :
    P^1_{S⁄R} ≃ₗ[S] Ω[S⁄R] × S :=
  LinearEquiv.ofLinear
    firstPrincipalPartsToDifferentialsProd
    differentialsProdToFirstPrincipalParts
    firstPrincipalPartsToDifferentialsProd_comp_differentialsProdToFirstPrincipalParts
    differentialsProdToFirstPrincipalParts_comp_firstPrincipalPartsToDifferentialsProd

end
