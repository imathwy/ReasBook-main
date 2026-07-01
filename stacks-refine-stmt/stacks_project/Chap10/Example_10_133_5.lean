import Mathlib
import stacks_project.Chap10.Definition_10_133_1
import stacks_project.Chap10.Lemma_10_133_3

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
          h • firstOrderDerivationLinearMap D g := sorry

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
  sorry

/-- The first-order differential operator attached to a derivation and an element of `N`. -/
private def firstOrderDifferentialOperatorOfDerivationProd (p : Derivation R S N × N) :
    DO₁ :=
  ⟨p.1.toLinearMap + firstOrderMultiplicationLinearMap p.2,
    derivation_add_smulRight_isDifferentialOperatorOfOrder_one p.1 p.2⟩

/-- The derivation part is additive in the first-order differential operator. -/
private theorem firstOrderDerivationPart_map_add (D E : DO₁) :
    firstOrderDerivationPart (D + E) =
      firstOrderDerivationPart D + firstOrderDerivationPart E := sorry

/-- The derivation part is `S`-linear in the first-order differential operator. -/
private theorem firstOrderDerivationPart_map_smul (a : S) (D : DO₁) :
    firstOrderDerivationPart (a • D) = a • firstOrderDerivationPart D := sorry

/-- The decomposition map `D ↦ (σ_D, D(1))`, packaged as an `S`-linear map. -/
private def firstOrderDifferentialOperatorToDerivationProd :
    DO₁ →ₗ[S] Derivation R S N × N where
  toFun D := (firstOrderDerivationPart D, D.1 1)
  map_add' := by
    intro D E
    ext <;> simp [firstOrderDerivationPart_map_add]
  map_smul' := by
    intro a D
    ext <;> simp [firstOrderDerivationPart_map_smul]

/-- Recombining a derivation and a value at `1` is additive. -/
private theorem firstOrderDifferentialOperatorOfDerivationProd_map_add
    (p q : Derivation R S N × N) :
    firstOrderDifferentialOperatorOfDerivationProd (p + q) =
      firstOrderDifferentialOperatorOfDerivationProd p +
        firstOrderDifferentialOperatorOfDerivationProd q := sorry

/-- Recombining a derivation and a value at `1` is `S`-linear. -/
private theorem firstOrderDifferentialOperatorOfDerivationProd_map_smul
    (a : S) (p : Derivation R S N × N) :
    firstOrderDifferentialOperatorOfDerivationProd (a • p) =
      a • firstOrderDifferentialOperatorOfDerivationProd p := sorry

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
        ((firstOrderDerivationPart D), D.1 1) = D := sorry

-- Proof sketch: for `δ + λ_x`, the corrected part `σ_{δ + λ_x}` is `δ`, because derivations
-- vanish at `1` and `λ_x(1) = x`; the second component is exactly `x`.
/-- The derivation-and-value pair attached to `δ + λ_x` is exactly `(δ, x)`. -/
private theorem firstOrderDifferentialOperatorEquivDerivationProd_right_inv
    (p : Derivation R S N × N) :
    (firstOrderDerivationPart (firstOrderDifferentialOperatorOfDerivationProd p),
        (firstOrderDifferentialOperatorOfDerivationProd p).1 1) = p := sorry

/-- Example 10.133.5 (1): first-order differential operators `S → N` decompose canonically into a
derivation part and a multiplication operator by the value at `1`, giving an `S`-linear
equivalence with `Derivation R S N × N`. -/
def firstOrderDifferentialOperatorEquivDerivationProd :
    DO₁ ≃ₗ[S] Derivation R S N × N :=
  LinearEquiv.ofLinear
    firstOrderDifferentialOperatorToDerivationProd
    firstOrderDifferentialOperatorOfDerivationProdLinear
    (by
      apply LinearMap.ext
      intro p
      exact firstOrderDifferentialOperatorEquivDerivationProd_right_inv p)
    (by
      apply LinearMap.ext
      intro D
      exact firstOrderDifferentialOperatorEquivDerivationProd_left_inv D)

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
  sorry

private theorem differentialsProdToFirstPrincipalParts_comp_firstPrincipalPartsToDifferentialsProd :
    (differentialsProdToFirstPrincipalParts : Ω[S⁄R] × S →ₗ[S] P^1_{S⁄R}).comp
        (firstPrincipalPartsToDifferentialsProd : P^1_{S⁄R} →ₗ[S] Ω[S⁄R] × S) =
      (LinearMap.id : P^1_{S⁄R} →ₗ[S] P^1_{S⁄R}) := by
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
