import Mathlib
import StacksProject_2024.Chap10.Definition_10_133_1

-- Declarations for this item will be appended below by the statement pipeline.

/-
Domain triage:
* primary domain: algebraic principal parts and differential operators for a commutative
  `R`-algebra `S`;
* sampled owner API:
  `LinearMap.IsDifferentialOperatorOfOrder`,
  `LinearMap.isDifferentialOperatorOfOrder_zero_iff`,
  `LinearMap.isDifferentialOperatorOfOrder_succ_iff`,
  `principal_parts_module`;
* source-facing owner: `principal_parts_module R S M k` with
  `principal_parts_universal_differential`;
* core/canonical operator owner: `differential_operators_order_le R S M k N`;
* bridge/view: `principal_parts_linear_map_equiv_differential_operators`.

The free-module presentation coordinates are implementation data. The quotient module and the
operator subtype are the public owners; only the relation submodule stays public because direct
comparison lemmas downstream use it.
-/

universe u

noncomputable section

variable {R S M : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]

/-- The free `S`-module on the underlying set of `M` used to present principal parts. -/
private abbrev principal_parts_free : Type u := M →₀ S

/-- The basis vector `[m]` in the free module used to present principal parts. -/
private abbrev principal_parts_basis_vector (m : M) : M →₀ S :=
  Finsupp.single m (1 : S)

/-- The iterated commutator relation attached to a finite list of scalars in `S`. -/
private def principal_parts_commutator_relation : List S → M → M →₀ S
  | [], m => principal_parts_basis_vector m
  | s :: l, m =>
      principal_parts_commutator_relation l (s • m) -
        s • principal_parts_commutator_relation l m

/-- The generating relations for the `k`-th module of principal parts of `M` over `R → S`. -/
private def principal_parts_relation_set
    (R S M : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M] (k : ℕ) :
    Set (M →₀ S) :=
  { x |
      (∃ m m' : M,
        x = principal_parts_basis_vector (m + m') -
          principal_parts_basis_vector m -
          principal_parts_basis_vector m') ∨
        (∃ r : R, ∃ m : M,
          x = (algebraMap R S r) • principal_parts_basis_vector m -
            principal_parts_basis_vector (r • m)) ∨
          ∃ l : List S, l.length = k + 1 ∧ ∃ m : M,
            x = principal_parts_commutator_relation l m }

/-- The submodule of relations used to define the `k`-th module of principal parts. -/
def principal_parts_relation_submodule
    (R S M : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M] (k : ℕ) :
    Submodule S (M →₀ S) :=
  Submodule.span S (principal_parts_relation_set R S M k)

/-- The `k`-th module of principal parts of `M` over `R → S`, presented by generators and
relations. -/
abbrev principal_parts_module
    (R S M : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M] (k : ℕ) :
    Type u :=
  (M →₀ S) ⧸ (principal_parts_relation_submodule R S M k : Submodule S (M →₀ S))

namespace PrincipalParts

scoped notation "P^{" k "}_{" S "⁄" R "}(" M ")" =>
  principal_parts_module R S M k

end PrincipalParts

open scoped PrincipalParts

-- Proof sketch: the additive and `R`-linear generators of `principal_parts_relation_submodule k`
-- force the quotient class map `m ↦ [m]` to be additive and `R`-linear.
/-- Additivity of the universal class map `M → P^k_{S/R}(M)`. -/
private theorem principal_parts_universal_differential_map_add (k : ℕ) :
    ∀ m m' : M,
      (principal_parts_relation_submodule R S M k).mkQ
          (principal_parts_basis_vector (m + m')) =
        (principal_parts_relation_submodule R S M k).mkQ
            (principal_parts_basis_vector m) +
          (principal_parts_relation_submodule R S M k).mkQ
            (principal_parts_basis_vector m') := sorry

-- Proof sketch: the scalar generator
-- `(algebraMap R S r) • [m] - [r • m]` lies in `principal_parts_relation_submodule k`.
/-- Compatibility of the universal class map `M → P^k_{S/R}(M)` with the `R`-action. -/
private theorem principal_parts_universal_differential_map_smul (k : ℕ) :
    ∀ (r : R) (m : M),
      (principal_parts_relation_submodule R S M k).mkQ
          (principal_parts_basis_vector (r • m)) =
        r • (principal_parts_relation_submodule R S M k).mkQ
          (principal_parts_basis_vector m) := sorry

/-- The universal `R`-linear map `M → P^k_{S/R}(M)` sending `m` to the class of `[m]`. -/
def principal_parts_universal_differential (k : ℕ) :
    M →ₗ[R] P^{k}_{S⁄R}(M) where
  toFun m := (principal_parts_relation_submodule R S M k).mkQ (principal_parts_basis_vector m)
  map_add' := principal_parts_universal_differential_map_add k
  map_smul' := principal_parts_universal_differential_map_smul k

/-- Order-`k` differential operators encoded on the free presentation of principal parts. -/
private def presented_differential_operators_order_le_submodule
    (R S M : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    (k : ℕ) (N : Type u) [AddCommGroup N] [Module S N] :
    Submodule S ((M →₀ S) →ₗ[S] N) :=
  LinearMap.ker <| LinearMap.lcomp S N (principal_parts_relation_submodule R S M k).subtype

/-- Precomposition with the quotient map `principal_parts_free → P^k_{S/R}(M)`. -/
private abbrev presented_principal_parts_precompose
    (R S M : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    (k : ℕ) (N : Type u) [AddCommGroup N] [Module S N] :
    (principal_parts_module R S M k →ₗ[S] N) →ₗ[S] ((M →₀ S) →ₗ[S] N) :=
  LinearMap.lcomp S N (principal_parts_relation_submodule R S M k).mkQ

-- Proof sketch: the quotient map from `principal_parts_free` to `principal_parts_module k` is
-- universal among `S`-linear maps annihilating `principal_parts_relation_submodule k`.
/-- The image of precomposition with the quotient map is the presentation-level differential
operator submodule. -/
private theorem presented_principal_parts_precompose_range_eq_submodule
    (k : ℕ) (N : Type u) [AddCommGroup N] [Module S N] :
    LinearMap.range (presented_principal_parts_precompose R S M k N) =
      presented_differential_operators_order_le_submodule R S M k N := sorry

/-- The quotient presentation identifies maps out of `P^k_{S/R}(M)` with presentation-level
differential operators. -/
private noncomputable def principal_parts_linear_map_equiv_presented_differential_operators
    (R S M : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    (k : ℕ) (N : Type u) [AddCommGroup N] [Module S N] :
    (principal_parts_module R S M k →ₗ[S] N) ≃ₗ[S]
      ↥(presented_differential_operators_order_le_submodule R S M k N) :=
  let p := principal_parts_relation_submodule R S M k
  let e₁ :
      (principal_parts_module R S M k →ₗ[S] N) ≃ₗ[S]
        ↥(LinearMap.range (presented_principal_parts_precompose R S M k N)) :=
    LinearEquiv.ofInjective
      (presented_principal_parts_precompose R S M k N)
      (LinearMap.lcomp_injective_of_surjective p.mkQ (Submodule.mkQ_surjective p))
  let e₂ :
      ↥(LinearMap.range (presented_principal_parts_precompose R S M k N)) ≃ₗ[S]
        ↥(presented_differential_operators_order_le_submodule R S M k N) :=
    LinearEquiv.ofEq
      (LinearMap.range (presented_principal_parts_precompose R S M k N))
      (presented_differential_operators_order_le_submodule R S M k N)
      (presented_principal_parts_precompose_range_eq_submodule k N)
  e₁.trans e₂

-- Proof sketch: evaluate a presentation-level operator on basis vectors `[m]`; the additivity and
-- `R`-linearity relations make the resulting map `M → N` `R`-linear.
/-- Forget the free-presentation encoding of a differential operator by evaluating on basis
vectors. -/
private def presented_differential_operator_to_linear_map (k : ℕ) (N : Type u)
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N] :
    ↥(presented_differential_operators_order_le_submodule R S M k N) →ₗ[S] (M →ₗ[R] N) where
  toFun D :=
    { toFun := fun m ↦ D.1 (principal_parts_basis_vector m)
      map_add' := by
        sorry
      map_smul' := by
        sorry }
  map_add' := by
    sorry
  map_smul' := by
    sorry

-- Proof sketch: the defining presentation relations were chosen so that annihilating them is
-- equivalent to satisfying the recursive commutator definition from `Definition 10.133.1`.
/-- A presentation-level differential operator determines an ordinary differential operator. -/
private theorem presented_differential_operator_mem_differential_operators_order_le_submodule
    (k : ℕ) (N : Type u) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    (D : ↥(presented_differential_operators_order_le_submodule R S M k N)) :
    presented_differential_operator_to_linear_map k N D ∈
      differential_operators_order_le_submodule R S M k N := sorry

/-- The map from presentation-level differential operators to ordinary differential operators. -/
private def presented_differential_operator_to_differential_operator (k : ℕ) (N : Type u)
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N] :
    ↥(presented_differential_operators_order_le_submodule R S M k N) →ₗ[S]
      differential_operators_order_le R S M k N :=
  LinearMap.codRestrict
    (differential_operators_order_le_submodule R S M k N)
    (presented_differential_operator_to_linear_map k N)
    (presented_differential_operator_mem_differential_operators_order_le_submodule k N)

-- Proof sketch: extend an ordinary differential operator `D : M → N` `S`-linearly from the basis
-- vectors `[m]`, and use the differential-operator condition to show that the defining relations of
-- `principal_parts_module` vanish.
/-- Encode an ordinary differential operator as an `S`-linear map on the free presentation. -/
private def differential_operator_to_presented_differential_operator_on_free
    (k : ℕ) (N : Type u) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N] :
    differential_operators_order_le R S M k N →ₗ[S] ((M →₀ S) →ₗ[S] N) where
  toFun D := Finsupp.linearCombination S fun m ↦ (D : M →ₗ[R] N) m
  map_add' := by
    sorry
  map_smul' := by
    sorry

-- Proof sketch: the ordinary differential-operator identities imply that the additive,
-- `R`-linear, and commutator generators of `principal_parts_relation_submodule k` are sent to `0`.
/-- An ordinary differential operator yields a presentation-level operator annihilating the
principal-parts relations. -/
private theorem differential_operator_to_presented_differential_operator_mem
    (k : ℕ) (N : Type u) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    (D : differential_operators_order_le R S M k N) :
    differential_operator_to_presented_differential_operator_on_free k N D ∈
      presented_differential_operators_order_le_submodule R S M k N := sorry

/-- The map from ordinary differential operators to the presentation-level encoding. -/
private def differential_operator_to_presented_differential_operator
    (k : ℕ) (N : Type u) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N] :
    differential_operators_order_le R S M k N →ₗ[S]
      ↥(presented_differential_operators_order_le_submodule R S M k N) :=
  LinearMap.codRestrict
    (presented_differential_operators_order_le_submodule R S M k N)
    (differential_operator_to_presented_differential_operator_on_free k N)
    (differential_operator_to_presented_differential_operator_mem k N)

-- Proof sketch: the two constructions above are inverse by construction on basis vectors `[m]`,
-- and by the universal property of the free module they are inverse on the whole presentation.
/-- The free-presentation encoding of differential operators is equivalent to the canonical owner
submodule of ordinary differential operators. -/
private noncomputable def presented_differential_operators_equiv_differential_operators
    (k : ℕ) (N : Type u) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N] :
    ↥(presented_differential_operators_order_le_submodule R S M k N) ≃ₗ[S]
      differential_operators_order_le R S M k N :=
  LinearEquiv.ofLinear
    (presented_differential_operator_to_differential_operator k N)
    (differential_operator_to_presented_differential_operator k N)
    (by
      sorry)
    (by
      sorry)

/-- Lemma 10.133.3: the `k`-th module of principal parts `P^k_{S/R}(M)` represents order-`k`
differential operators from `M` to an `S`-module `N`. -/
noncomputable def principal_parts_linear_map_equiv_differential_operators
    (R S M : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    (k : ℕ) (N : Type u) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N] :
    (P^{k}_{S⁄R}(M) →ₗ[S] N) ≃ₗ[S] differential_operators_order_le R S M k N :=
  (principal_parts_linear_map_equiv_presented_differential_operators R S M k N).trans
    (presented_differential_operators_equiv_differential_operators k N)

-- Proof sketch: postcomposition with `f` preserves the recursive differential-operator condition
-- because `f`, viewed as an `R`-linear map, is order `0`.
/-- Postcomposition with an `S`-linear map preserves differential operators of order `k`. -/
theorem differential_operators_postcompose_mem
    (k : ℕ) {N N' : Type u}
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [AddCommGroup N'] [Module S N'] [Module R N'] [IsScalarTower R S N']
    (f : N →ₗ[S] N') (D : differential_operators_order_le R S M k N) :
    ((f.restrictScalars R).comp D.1) ∈
      differential_operators_order_le_submodule R S M k N' := sorry

/-- Postcomposition of differential operators with an `S`-linear map between target modules. -/
noncomputable def differential_operators_postcompose
    (k : ℕ) {N N' : Type u}
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [AddCommGroup N'] [Module S N'] [Module R N'] [IsScalarTower R S N']
    (f : N →ₗ[S] N') :
    differential_operators_order_le R S M k N →ₗ[S]
      differential_operators_order_le R S M k N' :=
  { toFun := fun D ↦ ⟨(f.restrictScalars R).comp D.1, differential_operators_postcompose_mem k f D⟩
    map_add' := by
      sorry
    map_smul' := by
      sorry }

-- Proof sketch: both sides are induced by postcomposition with `f` on maps out of
-- `principal_parts_module k`; the bridge from the free presentation to ordinary differential
-- operators is compatible with that postcomposition.
/-- The principal-parts representation of differential operators is functorial in the target
`S`-module. -/
theorem principal_parts_linear_map_equiv_differential_operators_natural
    (k : ℕ) {N N' : Type u}
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [AddCommGroup N'] [Module S N'] [Module R N'] [IsScalarTower R S N']
    (f : N →ₗ[S] N') :
    (differential_operators_postcompose k f) ∘ₗ
        (principal_parts_linear_map_equiv_differential_operators
          R S M k N).toLinearMap =
      (principal_parts_linear_map_equiv_differential_operators
        R S M k N').toLinearMap ∘ₗ
        LinearMap.compRight S f := sorry

end
