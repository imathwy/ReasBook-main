import Mathlib
import StacksProject_2024.Chap10.Definition_10_133_1
import StacksProject_2024.Chap10.Lemma_10_133_2

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

/-- Helper for Lemma 10.133.3: recursively evaluate the iterated scalar commutator determined by a
finite list of scalars. -/
private def iterated_commutator_eval
    (N : Type u) [AddCommGroup N] [Module S N] (l : List S) (f : M → N) : M → N :=
  match l with
  | [] => f
  | s :: l =>
      fun m ↦
        iterated_commutator_eval N l f (s • m) - s • iterated_commutator_eval N l f m

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
            (principal_parts_basis_vector m') := by
  intro m m'
  let p := principal_parts_relation_submodule R S M k
  -- The additive generator is one of the defining relations, so its class vanishes in the quotient.
  have hrel :
      principal_parts_basis_vector (m + m') -
          principal_parts_basis_vector m -
          principal_parts_basis_vector m' ∈ p := by
    apply Submodule.subset_span
    exact Or.inl ⟨m, m', rfl⟩
  have hzero :
      p.mkQ
          (principal_parts_basis_vector (m + m') -
            principal_parts_basis_vector m -
            principal_parts_basis_vector m') = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hrel
  -- Expanding the quotient map across the relation isolates the desired additivity identity.
  rw [LinearMap.map_sub, LinearMap.map_sub] at hzero
  have hzero' :
      p.mkQ (principal_parts_basis_vector (m + m')) -
          (p.mkQ (principal_parts_basis_vector m) +
            p.mkQ (principal_parts_basis_vector m')) = 0 := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hzero
  exact sub_eq_zero.mp hzero'

-- Proof sketch: the scalar generator
-- `(algebraMap R S r) • [m] - [r • m]` lies in `principal_parts_relation_submodule k`.
/-- Compatibility of the universal class map `M → P^k_{S/R}(M)` with the `R`-action. -/
private theorem principal_parts_universal_differential_map_smul (k : ℕ) :
    ∀ (r : R) (m : M),
      (principal_parts_relation_submodule R S M k).mkQ
          (principal_parts_basis_vector (r • m)) =
        r • (principal_parts_relation_submodule R S M k).mkQ
          (principal_parts_basis_vector m) := by
  intro r m
  let p := principal_parts_relation_submodule R S M k
  -- The `R`-scalar relation identifies `[r • m]` with `(algebraMap R S r) • [m]`.
  have hrel :
      (algebraMap R S r) • principal_parts_basis_vector m -
          principal_parts_basis_vector (r • m) ∈ p := by
    apply Submodule.subset_span
    exact Or.inr <| Or.inl ⟨r, m, rfl⟩
  have hzero :
      p.mkQ
          ((algebraMap R S r) • principal_parts_basis_vector m -
            principal_parts_basis_vector (r • m)) = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hrel
  -- After rewriting the quotient map through the relation, the scalar-tower action gives the claim.
  rw [LinearMap.map_sub, LinearMap.map_smul] at hzero
  have hzero' :
      (algebraMap R S r) • p.mkQ (principal_parts_basis_vector m) -
          p.mkQ (principal_parts_basis_vector (r • m)) = 0 := by
    simpa using hzero
  have hEq :
      p.mkQ (principal_parts_basis_vector (r • m)) =
        (algebraMap R S r) • p.mkQ (principal_parts_basis_vector m) :=
    (sub_eq_zero.mp hzero').symm
  simpa [Algebra.smul_def] using hEq

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
      presented_differential_operators_order_le_submodule R S M k N := by
  let p := principal_parts_relation_submodule R S M k
  ext F
  constructor
  · rintro ⟨L, rfl⟩
    -- A map factoring through the quotient vanishes on the relation submodule by construction.
    rw [presented_differential_operators_order_le_submodule, LinearMap.mem_ker]
    ext x
    have hx : p.mkQ x = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact x.2
    change L (p.mkQ x) = 0
    rw [hx]
    simp
  · intro hF
    rw [presented_differential_operators_order_le_submodule, LinearMap.mem_ker] at hF
    -- Conversely, any map killing the relations descends uniquely to the quotient.
    have hker : p ≤ LinearMap.ker F := by
      intro x hx
      have hzero := LinearMap.congr_fun hF ⟨x, hx⟩
      simpa [LinearMap.lcomp_apply] using hzero
    refine ⟨p.liftQ F hker, ?_⟩
    ext x
    simp [presented_principal_parts_precompose]

/-- Helper for Lemma 10.133.3: a presentation-level differential operator vanishes on every
defining principal-parts relation. -/
private theorem presented_differential_operator_apply_eq_zero_of_mem_relation
    (k : ℕ) (N : Type u) [AddCommGroup N] [Module S N]
    (D : ↥(presented_differential_operators_order_le_submodule R S M k N))
    {x : M →₀ S}
    (hx : x ∈ principal_parts_relation_submodule R S M k) :
    D.1 x = 0 := by
  let p := principal_parts_relation_submodule R S M k
  have hker : LinearMap.lcomp S N p.subtype D.1 = 0 := by
    simpa [presented_differential_operators_order_le_submodule, LinearMap.mem_ker] using D.2
  -- Membership in the kernel says exactly that `D` kills every element of the relation submodule.
  have hzero := LinearMap.congr_fun hker ⟨x, hx⟩
  change D.1 x = 0 at hzero
  exact hzero

/-- Helper for Lemma 10.133.3: evaluating a commutator relation under any `S`-linear map on the
free presentation recovers the corresponding iterated scalar commutator on basis evaluation. -/
private theorem principal_parts_commutator_relation_apply
    (N : Type u) [AddCommGroup N] [Module S N]
    (L : (M →₀ S) →ₗ[S] N) :
    ∀ l : List S, ∀ m : M,
      L (principal_parts_commutator_relation l m) =
        iterated_commutator_eval N l (fun m ↦ L (principal_parts_basis_vector m)) m := by
  intro l
  induction l with
  | nil =>
      intro m
      -- The empty commutator relation is just the basis vector `[m]`.
      rfl
  | cons s l ih =>
      intro m
      -- The recursive relation matches the recursive commutator evaluation after linearity.
      rw [principal_parts_commutator_relation, LinearMap.map_sub, LinearMap.map_smul, ih, ih]
      rfl

/-- Helper for Lemma 10.133.3: the list recursion for iterated commutators agrees with taking one
scalar commutator first and then iterating on the tail. -/
private theorem iterated_commutator_eval_cons_scalarCommutator
    (N : Type u) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    (E : M →ₗ[R] N) (g : S) (l : List S) (m : M) :
    iterated_commutator_eval N (g :: l) (fun m ↦ E m) m =
      iterated_commutator_eval N l (fun m ↦ E.scalarCommutator g m) m := by
  induction l generalizing m with
  | nil =>
      -- For an empty tail, the statement is exactly the scalar-commutator formula.
      simp [iterated_commutator_eval]
  | cons s l ih =>
      -- After one more recursive step, both sides are obtained from the induction hypothesis by
      -- expanding the outer commutators and commuting the scalar actions in the commutative ring.
      calc
        iterated_commutator_eval N (g :: s :: l) (fun m ↦ E m) m =
            iterated_commutator_eval N (g :: l) (fun m ↦ E m) (s • m) -
              s • iterated_commutator_eval N (g :: l) (fun m ↦ E m) m := by
          simp [iterated_commutator_eval, smul_smul, sub_eq_add_neg, add_assoc, add_left_comm,
            add_comm, mul_comm]
        _ =
            iterated_commutator_eval N l (fun m ↦ E.scalarCommutator g m) (s • m) -
              s • iterated_commutator_eval N l (fun m ↦ E.scalarCommutator g m) m := by
          rw [ih, ih]
        _ = iterated_commutator_eval N (s :: l) (fun m ↦ E.scalarCommutator g m) m := by
          rfl

/-- Helper for Lemma 10.133.3: order-`k` differential operators are exactly the maps whose
length-`k + 1` iterated scalar commutators vanish. -/
private theorem isDifferentialOperatorOfOrder_iff_iterated_commutator_eval_eq_zero
    (k : ℕ) (N : Type u) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    (E : M →ₗ[R] N) :
    E.IsDifferentialOperatorOfOrder S k ↔
      ∀ l : List S, l.length = k + 1 → ∀ m : M,
        iterated_commutator_eval N l (fun m ↦ E m) m = 0 := by
  induction k generalizing E with
  | zero =>
      constructor
      · intro h l hl m
        rw [LinearMap.isDifferentialOperatorOfOrder_zero_iff] at h
        cases l with
        | nil =>
            simp at hl
        | cons g l =>
            cases l with
            | nil =>
                -- For a singleton list, the iterated commutator is the ordinary scalar commutator.
                simpa [iterated_commutator_eval, LinearMap.scalarCommutator_apply] using
                  sub_eq_zero.mpr (h g m)
            | cons g' l =>
                simp at hl
      · intro h
        rw [LinearMap.isDifferentialOperatorOfOrder_zero_iff]
        intro g m
        -- The converse reads the vanishing condition on the singleton list `[g]`.
        have hzero := h [g] (by simp) m
        exact sub_eq_zero.mp <| by
          simpa [iterated_commutator_eval, LinearMap.scalarCommutator_apply] using hzero
  | succ k ih =>
      constructor
      · intro h l hl m
        rw [LinearMap.isDifferentialOperatorOfOrder_succ_iff] at h
        cases l with
        | nil =>
            simp at hl
        | cons g l =>
            have hl' : l.length = k + 1 := by
              simpa using hl
            -- Peel off the first scalar and apply the induction hypothesis to the scalar
            -- commutator.
            have hzero :=
              (ih (E := E.scalarCommutator g)).1 (h g) l hl' m
            simpa [iterated_commutator_eval_cons_scalarCommutator] using hzero
      · intro h
        rw [LinearMap.isDifferentialOperatorOfOrder_succ_iff]
        intro g
        -- Vanishing on lists of length `k + 2` specializes to vanishing of the scalar commutator
        -- on tails of length `k + 1`.
        exact (ih (E := E.scalarCommutator g)).2 (by
          intro l hl m
          have hzero := h (g :: l) (by simpa using congrArg Nat.succ hl) m
          simpa [iterated_commutator_eval_cons_scalarCommutator] using hzero)

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
/-- Helper for Lemma 10.133.3: evaluating a presentation-level operator on basis vectors is
additive in `M`. -/
private theorem presented_differential_operator_eval_add
    (k : ℕ) (N : Type u) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    (D : ↥(presented_differential_operators_order_le_submodule R S M k N)) :
    ∀ m m' : M,
      D.1 (principal_parts_basis_vector (m + m')) =
        D.1 (principal_parts_basis_vector m) +
          D.1 (principal_parts_basis_vector m') := by
  intro m m'
  let p := principal_parts_relation_submodule R S M k
  have hrel :
      principal_parts_basis_vector (m + m') -
          principal_parts_basis_vector m -
          principal_parts_basis_vector m' ∈ p := by
    apply Submodule.subset_span
    exact Or.inl ⟨m, m', rfl⟩
  -- Applying `D` to the additive generator gives the additivity constraint on basis vectors.
  have hzero :=
    presented_differential_operator_apply_eq_zero_of_mem_relation k N D hrel
  rw [LinearMap.map_sub, LinearMap.map_sub] at hzero
  have hzero' :
      D.1 (principal_parts_basis_vector (m + m')) -
          (D.1 (principal_parts_basis_vector m) +
            D.1 (principal_parts_basis_vector m')) = 0 := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hzero
  exact sub_eq_zero.mp hzero'

/-- Helper for Lemma 10.133.3: evaluating a presentation-level operator on basis vectors is
compatible with the `R`-action on `M`. -/
private theorem presented_differential_operator_eval_smul
    (k : ℕ) (N : Type u) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    (D : ↥(presented_differential_operators_order_le_submodule R S M k N)) :
    ∀ (r : R) (m : M),
      D.1 (principal_parts_basis_vector (r • m)) =
        r • D.1 (principal_parts_basis_vector m) := by
  intro r m
  let p := principal_parts_relation_submodule R S M k
  have hrel :
      (algebraMap R S r) • principal_parts_basis_vector m -
          principal_parts_basis_vector (r • m) ∈ p := by
    apply Submodule.subset_span
    exact Or.inr <| Or.inl ⟨r, m, rfl⟩
  -- Applying `D` to the scalar relation identifies evaluation on `[r • m]` with scalar action.
  have hzero :=
    presented_differential_operator_apply_eq_zero_of_mem_relation k N D hrel
  rw [LinearMap.map_sub, LinearMap.map_smul] at hzero
  have hzero' :
      (algebraMap R S r) • D.1 (principal_parts_basis_vector m) -
          D.1 (principal_parts_basis_vector (r • m)) = 0 := by
    simpa using hzero
  have hEq :
      D.1 (principal_parts_basis_vector (r • m)) =
        (algebraMap R S r) • D.1 (principal_parts_basis_vector m) :=
    (sub_eq_zero.mp hzero').symm
  simpa [Algebra.smul_def] using hEq

/-- Helper for Lemma 10.133.3: evaluating a presentation-level operator on basis vectors produces
an `R`-linear map on `M`. -/
private def presented_differential_operator_to_linear_map_fun
    (k : ℕ) (N : Type u) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    (D : ↥(presented_differential_operators_order_le_submodule R S M k N)) :
    M →ₗ[R] N where
  toFun m := D.1 (principal_parts_basis_vector m)
  map_add' := presented_differential_operator_eval_add k N D
  map_smul' := presented_differential_operator_eval_smul k N D

/-- Helper for Lemma 10.133.3: the basis-evaluation construction is additive in the presented
operator. -/
private theorem presented_differential_operator_to_linear_map_fun_add
    (k : ℕ) (N : Type u) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N] :
    ∀ D E : ↥(presented_differential_operators_order_le_submodule R S M k N),
      presented_differential_operator_to_linear_map_fun k N (D + E) =
        presented_differential_operator_to_linear_map_fun k N D +
          presented_differential_operator_to_linear_map_fun k N E := by
  intro D E
  -- Addition is pointwise on the underlying presentation-level maps.
  ext m
  rfl

/-- Helper for Lemma 10.133.3: the basis-evaluation construction is `S`-linear in the presented
operator. -/
private theorem presented_differential_operator_to_linear_map_fun_smul
    (k : ℕ) (N : Type u) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N] :
    ∀ (s : S) (D : ↥(presented_differential_operators_order_le_submodule R S M k N)),
      presented_differential_operator_to_linear_map_fun k N (s • D) =
        s • presented_differential_operator_to_linear_map_fun k N D := by
  intro s D
  -- Scalar multiplication is also pointwise on the free-presentation encoding.
  ext m
  rfl

/-- Forget the free-presentation encoding of a differential operator by evaluating on basis
vectors. -/
private def presented_differential_operator_to_linear_map (k : ℕ) (N : Type u)
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N] :
    ↥(presented_differential_operators_order_le_submodule R S M k N) →ₗ[S] (M →ₗ[R] N) where
  toFun := presented_differential_operator_to_linear_map_fun k N
  map_add' := presented_differential_operator_to_linear_map_fun_add k N
  map_smul' := presented_differential_operator_to_linear_map_fun_smul k N

-- Proof sketch: the defining presentation relations were chosen so that annihilating them is
-- equivalent to satisfying the recursive commutator definition from `Definition 10.133.1`.
/-- A presentation-level differential operator determines an ordinary differential operator. -/
private theorem presented_differential_operator_mem_differential_operators_order_le_submodule
    (k : ℕ) (N : Type u) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    (D : ↥(presented_differential_operators_order_le_submodule R S M k N)) :
    presented_differential_operator_to_linear_map k N D ∈
      differential_operators_order_le_submodule R S M k N := by
  -- Route correction: prove the recursive differential-operator condition through the explicit
  -- iterated commutator presentation, rather than by a bespoke induction inside this membership
  -- proof.
  change (presented_differential_operator_to_linear_map k N D).IsDifferentialOperatorOfOrder S k
  refine
    (isDifferentialOperatorOfOrder_iff_iterated_commutator_eval_eq_zero
      (k := k) (N := N) (E := presented_differential_operator_to_linear_map k N D)).2 ?_
  intro l hl m
  let p := principal_parts_relation_submodule R S M k
  have hrel : principal_parts_commutator_relation l m ∈ p := by
    apply Submodule.subset_span
    exact Or.inr <| Or.inr ⟨l, hl, m, rfl⟩
  -- The length-`k + 1` commutator generator lies in the presentation kernel, so `D` kills it.
  have hzero :=
    presented_differential_operator_apply_eq_zero_of_mem_relation k N D hrel
  rw [principal_parts_commutator_relation_apply (N := N) D.1 l m] at hzero
  simpa [presented_differential_operator_to_linear_map,
      presented_differential_operator_to_linear_map_fun] using hzero

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
/-- Helper for Lemma 10.133.3: the free extension attached to a differential operator. -/
private def differential_operator_to_presented_differential_operator_on_free_fun
    (k : ℕ) (N : Type u) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    (D : differential_operators_order_le R S M k N) :
    (M →₀ S) →ₗ[S] N :=
  Finsupp.linearCombination S fun m ↦ (D : M →ₗ[R] N) m

/-- Helper for Lemma 10.133.3: the free-extension construction is additive in the differential
operator. -/
private theorem differential_operator_to_presented_differential_operator_on_free_fun_add
    (k : ℕ) (N : Type u) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N] :
    ∀ D E : differential_operators_order_le R S M k N,
      differential_operator_to_presented_differential_operator_on_free_fun k N (D + E) =
        differential_operator_to_presented_differential_operator_on_free_fun k N D +
          differential_operator_to_presented_differential_operator_on_free_fun k N E := by
  intro D E
  -- It is enough to compare the two `S`-linear maps on basis vectors of the free module.
  apply Finsupp.lhom_ext
  intro m s
  simp [differential_operator_to_presented_differential_operator_on_free_fun]

/-- Helper for Lemma 10.133.3: the free-extension construction is `S`-linear in the differential
operator. -/
private theorem differential_operator_to_presented_differential_operator_on_free_fun_smul
    (k : ℕ) (N : Type u) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N] :
    ∀ (s : S) (D : differential_operators_order_le R S M k N),
      differential_operator_to_presented_differential_operator_on_free_fun k N (s • D) =
        s • differential_operator_to_presented_differential_operator_on_free_fun k N D := by
  intro s D
  -- The free extension respects the external `S`-action pointwise on basis vectors.
  apply Finsupp.lhom_ext
  intro m t
  simp [differential_operator_to_presented_differential_operator_on_free_fun]
  simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc]

/-- Encode an ordinary differential operator as an `S`-linear map on the free presentation. -/
private def differential_operator_to_presented_differential_operator_on_free
    (k : ℕ) (N : Type u) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N] :
    differential_operators_order_le R S M k N →ₗ[S] ((M →₀ S) →ₗ[S] N) where
  toFun := differential_operator_to_presented_differential_operator_on_free_fun k N
  map_add' := differential_operator_to_presented_differential_operator_on_free_fun_add k N
  map_smul' := differential_operator_to_presented_differential_operator_on_free_fun_smul k N

/-- Helper for Lemma 10.133.3: the free extension of a differential operator evaluates a basis
vector `[m]` to the original value `D m`. -/
private theorem differential_operator_to_presented_differential_operator_on_free_basis_vector
    (k : ℕ) (N : Type u) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    (D : differential_operators_order_le R S M k N) (m : M) :
    differential_operator_to_presented_differential_operator_on_free k N D
        (principal_parts_basis_vector m) =
      (D : M →ₗ[R] N) m := by
  -- The free extension is determined by its values on basis vectors.
  simp [differential_operator_to_presented_differential_operator_on_free,
    differential_operator_to_presented_differential_operator_on_free_fun,
    principal_parts_basis_vector, Finsupp.linearCombination_single]

/-- Helper for Lemma 10.133.3: the free extension sends a single basis vector with coefficient
`s` to `s • D m`. -/
private theorem differential_operator_to_presented_differential_operator_on_free_single
    (k : ℕ) (N : Type u) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    (D : differential_operators_order_le R S M k N) (m : M) (s : S) :
    differential_operator_to_presented_differential_operator_on_free k N D (Finsupp.single m s) =
      s • (D : M →ₗ[R] N) m := by
  -- The free extension is the linear combination map, so it reads the coefficient of `[m]`.
  simp [differential_operator_to_presented_differential_operator_on_free,
    differential_operator_to_presented_differential_operator_on_free_fun,
    Finsupp.linearCombination_single]

-- Proof sketch: the ordinary differential-operator identities imply that the additive,
-- `R`-linear, and commutator generators of `principal_parts_relation_submodule k` are sent to `0`.
/-- An ordinary differential operator yields a presentation-level operator annihilating the
principal-parts relations. -/
private theorem differential_operator_to_presented_differential_operator_mem
    (k : ℕ) (N : Type u) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    (D : differential_operators_order_le R S M k N) :
    differential_operator_to_presented_differential_operator_on_free k N D ∈
      presented_differential_operators_order_le_submodule R S M k N := by
  rw [presented_differential_operators_order_le_submodule, LinearMap.mem_ker]
  ext x
  let F := differential_operator_to_presented_differential_operator_on_free k N D
  change F x.1 = 0
  -- It suffices to check vanishing on the spanning generators of the relation submodule.
  exact Submodule.span_induction (p := fun y _ ↦ F y = 0)
    (by
    intro y hy
    rcases hy with hadd | hsmul | hcomm
    · rcases hadd with ⟨m, m', rfl⟩
      -- The additive generator records additivity of the underlying `R`-linear map.
      rw [LinearMap.map_sub, LinearMap.map_sub]
      rw [differential_operator_to_presented_differential_operator_on_free_basis_vector,
        differential_operator_to_presented_differential_operator_on_free_basis_vector,
        differential_operator_to_presented_differential_operator_on_free_basis_vector]
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        sub_eq_zero.mpr ((D : M →ₗ[R] N).map_add m m')
    · rcases hsmul with ⟨r, m, rfl⟩
      -- The `R`-linear generator records compatibility with the `R`-action.
      have hEq :
          (algebraMap R S r) • (D : M →ₗ[R] N) m =
            (D : M →ₗ[R] N) (r • m) := by
        simpa [Algebra.smul_def] using ((D : M →ₗ[R] N).map_smul r m).symm
      rw [LinearMap.map_sub, LinearMap.map_smul]
      rw [differential_operator_to_presented_differential_operator_on_free_basis_vector,
        differential_operator_to_presented_differential_operator_on_free_basis_vector]
      simpa using sub_eq_zero.mpr hEq
    · rcases hcomm with ⟨l, hl, m, rfl⟩
      -- The length-`k + 1` commutator generators vanish by the differential-operator
      -- hypothesis and the commutator evaluation lemma.
      have hzero :=
        (isDifferentialOperatorOfOrder_iff_iterated_commutator_eval_eq_zero
          (k := k) (N := N) (E := (D : M →ₗ[R] N))).1 D.2 l hl m
      have hEval :=
        principal_parts_commutator_relation_apply
          (N := N) (differential_operator_to_presented_differential_operator_on_free k N D) l m
      rw [hEval]
      simpa [differential_operator_to_presented_differential_operator_on_free_basis_vector] using
        hzero)
    (by
      -- The free extension is linear, so it sends `0` to `0`.
      simp)
    (by
      intro a b _ _ ha hb
      -- Vanishing is preserved under addition because the free extension is linear.
      simpa [map_add, ha, hb])
    (by
      intro s y _ hy
      -- Vanishing is also preserved under scalar multiplication.
      simpa [map_smul, hy])
    x.2

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
      -- On ordinary differential operators, extend from basis vectors and then evaluate back.
      ext D m
      simp [presented_differential_operator_to_differential_operator,
        presented_differential_operator_to_linear_map,
        presented_differential_operator_to_linear_map_fun,
        differential_operator_to_presented_differential_operator,
        differential_operator_to_presented_differential_operator_on_free_basis_vector])
    (by
      -- On presented operators, equality on basis vectors determines equality on the free module.
      apply LinearMap.ext
      intro D
      apply Subtype.ext
      apply Finsupp.lhom_ext
      intro m s
      -- Compare both sides on the generator `single m s`.
      calc
        ((differential_operator_to_presented_differential_operator k N
              (presented_differential_operator_to_differential_operator k N D) :
            (M →₀ S) →ₗ[S] N) (Finsupp.single m s)) =
            s • ((presented_differential_operator_to_differential_operator k N D : M →ₗ[R] N) m) := by
          simpa [differential_operator_to_presented_differential_operator] using
            differential_operator_to_presented_differential_operator_on_free_single k N
              (presented_differential_operator_to_differential_operator k N D) m s
        _ = s • D.1 (principal_parts_basis_vector m) := by
          rfl
        _ = D.1 (Finsupp.single m s) := by
          have hsingle : (Finsupp.single m s : M →₀ S) = s • principal_parts_basis_vector m := by
            ext a
            by_cases h : a = m
            · subst h
              simp [principal_parts_basis_vector]
            · simp [principal_parts_basis_vector, h]
          rw [hsingle, LinearMap.map_smul]
      )

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
      differential_operators_order_le_submodule R S M k N' := by
  change ((f.restrictScalars R).comp D.1).IsDifferentialOperatorOfOrder S k
  have hf : (f.restrictScalars R).IsDifferentialOperatorOfOrder S 0 := by
    rw [LinearMap.isDifferentialOperatorOfOrder_zero_iff]
    intro g n
    -- An `S`-linear map is a differential operator of order `0`.
    simpa using f.map_smul g n
  simpa using LinearMap.isDifferentialOperatorOfOrder_comp D.2 hf

/-- Helper for Lemma 10.133.3: postcomposition by an `S`-linear map is additive on the ordinary
differential-operator subtype. -/
private theorem differential_operators_postcompose_fun_add
    (k : ℕ) {N N' : Type u}
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [AddCommGroup N'] [Module S N'] [Module R N'] [IsScalarTower R S N']
    (f : N →ₗ[S] N') :
    ∀ D E : differential_operators_order_le R S M k N,
      (f.restrictScalars R).comp (D + E : differential_operators_order_le R S M k N).1 =
        (f.restrictScalars R).comp D.1 + (f.restrictScalars R).comp E.1 := by
  intro D E
  -- Composition with a fixed linear map is pointwise additive.
  ext m
  simp

/-- Helper for Lemma 10.133.3: postcomposition by an `S`-linear map is `S`-linear on the ordinary
differential-operator subtype. -/
private theorem differential_operators_postcompose_fun_smul
    (k : ℕ) {N N' : Type u}
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [AddCommGroup N'] [Module S N'] [Module R N'] [IsScalarTower R S N']
    (f : N →ₗ[S] N') :
    ∀ (s : S) (D : differential_operators_order_le R S M k N),
      (f.restrictScalars R).comp (s • D : differential_operators_order_le R S M k N).1 =
        s • (f.restrictScalars R).comp D.1 := by
  intro s D
  -- Composition also commutes with the external `S`-action pointwise.
  ext m
  simp

/-- Helper for Lemma 10.133.3: postcomposition as a linear map into the underlying `R`-linear
maps. -/
private def differential_operators_postcompose_to_linear_map
    (k : ℕ) {N N' : Type u}
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [AddCommGroup N'] [Module S N'] [Module R N'] [IsScalarTower R S N']
    (f : N →ₗ[S] N') :
    differential_operators_order_le R S M k N →ₗ[S] (M →ₗ[R] N') where
  toFun D := (f.restrictScalars R).comp D.1
  map_add' := differential_operators_postcompose_fun_add k f
  map_smul' := differential_operators_postcompose_fun_smul k f

/-- Postcomposition of differential operators with an `S`-linear map between target modules. -/
noncomputable def differential_operators_postcompose
    (k : ℕ) {N N' : Type u}
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [AddCommGroup N'] [Module S N'] [Module R N'] [IsScalarTower R S N']
    (f : N →ₗ[S] N') :
    differential_operators_order_le R S M k N →ₗ[S]
      differential_operators_order_le R S M k N' :=
  LinearMap.codRestrict
    (differential_operators_order_le_submodule R S M k N')
    (differential_operators_postcompose_to_linear_map (R := R) (S := S) (M := M) k f)
    (differential_operators_postcompose_mem (R := R) (S := S) (M := M) k f)

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
        LinearMap.compRight S f := by
  ext L m
  -- Both sides evaluate to `f` applied to the class-map value of `L` on `[m]`.
  rfl

end
