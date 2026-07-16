import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_133_1
import StacksProject_2024.stacks_project.Chap10.Remark_10_133_7

-- Declarations for this item will be appended below by the statement pipeline.

open scoped PrincipalParts TensorProduct
open LinearMap
open TensorProduct.AlgebraTensorModule

universe u

noncomputable section

/- Domain triage:
* primary domain: principal parts and differential operators under extension of scalars along a
  formally étale algebra map;
* sampled owner API:
  `principal_parts_module`,
  `principalPartsBaseChangeMap`,
  `TensorProduct.AlgebraTensorModule.mk`,
  `principal_parts_linear_map_equiv_differential_operators`;
* best owner abstraction: the canonical scalar-extension map is already owned upstream by
  `TensorProduct.AlgebraTensorModule.mk`, while the principal-parts owner remains
  `principal_parts_module` together with the source-facing base-change map
  `principalPartsBaseChangeMap`;
* primitive data: the canonical extension-of-scalars map `M → S' ⊗[S] M` and the induced map on
  principal parts;
* derived API: bijectivity of the principal-parts comparison for formally étale maps and the
  resulting unique extension of differential operators.

Source/core/bridge triage:
* `source-facing`: the two clauses of Lemma `10.150.8`;
* `core/canonical`: `principal_parts_module`, `LinearMap.IsDifferentialOperatorOfOrder`, and the
  scalar-extension owner `TensorProduct.AlgebraTensorModule.mk`;
* `bridge/view`: the lifted comparison map
  `((principalPartsBaseChangeMap k (mk S S' S' M (1 : S'))).liftBaseChange S')`. -/

section

variable {R S S' M N X : Type u}
variable [CommRing R] [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra R S'] [Algebra S S']
variable [IsScalarTower R S S']
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

-- Proof sketch: identify both source and target principal-parts modules with quotient models from
-- Lemma `10.133.9`; after tensoring the source quotient by `S'`, Lemma `10.150.7` identifies the
-- resulting diagonal-thickening quotient with the target quotient over `S'`. The canonical map
-- `((principalPartsBaseChangeMap k (mk S S' S' M (1 : S'))).liftBaseChange S')` is exactly the map
-- induced by these identifications, so it is bijective.
/-- Lemma 10.150.8 (1): if `S → S'` is formally étale and `M' = S' ⊗[S] M`, then the canonical map
`S' ⊗[S] P^k_{S/R}(M) → P^k_{S'/R}(M')` is bijective. -/
theorem principalPartsFormallyEtaleBaseChangeMap_bijective [Algebra.FormallyEtale S S']
    (k : ℕ) :
    Function.Bijective
      (((principalPartsBaseChangeMap k (mk S S' S' M (1 : S'))).liftBaseChange S') :
        S' ⊗[S] P^{k}_{S⁄R}(M) →ₗ[S'] P^{k}_{S'⁄R}(S' ⊗[S] M)) :=
  sorry

-- Proof sketch: represent `D` by the corresponding `S`-linear map `P^k_{S/R}(M) → N` using
-- Lemma `10.133.3`, tensor that map with `S'`, and transport it across
-- `principalPartsFormallyEtaleBaseChangeMap_bijective` to obtain an `S'`-linear map
-- `P^k_{S'/R}(S' ⊗[S] M) → S' ⊗[S] N`. Then apply the same representation theorem again to recover
-- the unique differential operator extending `D`.
/-- Lemma 10.150.8 (2): every order-`k` differential operator `D : M → N` extends uniquely to an
order-`k` differential operator `S' ⊗[S] M → S' ⊗[S] N` along a formally étale map `S → S'`. -/
theorem existsUnique_baseChange_extension_of_isDifferentialOperatorOfOrder_of_formallyEtale
    [Algebra.FormallyEtale S S'] {D : M →ₗ[R] N} {k : ℕ}
    (hD : D.IsDifferentialOperatorOfOrder S k) :
    ∃! D' : S' ⊗[S] M →ₗ[R] S' ⊗[S] N,
      D'.comp ((mk S S' S' M (1 : S')).restrictScalars R) =
          ((mk S S' S' N (1 : S')).restrictScalars R).comp D ∧
        D'.IsDifferentialOperatorOfOrder S' k := sorry

end
