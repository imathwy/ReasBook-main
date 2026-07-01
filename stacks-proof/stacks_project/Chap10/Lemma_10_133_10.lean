import Mathlib
import stacks_project.Chap10.Definition_10_133_1
import stacks_project.Chap10.Lemma_10_132_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open LinearMap

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/- Domain triage:
* primary domain: algebraic de Rham differentials on exterior powers of Kähler differentials;
* sampled owner API: `LinearMap.IsDifferentialOperatorOfOrder`, `deRhamDifferentialFamily`,
  `isExteriorPowerDeRhamDifferential_deRhamDifferentialFamily`, and `KaehlerDifferential.D`;
* owner abstraction: the canonical recursive family `deRhamDifferentialFamily A B`;
* primitive data vs. derived API: the primitive object is the canonical de Rham differential
  family from Lemma `10.132.2`, while “the `p`th differential is first-order” is derived
  theorem-level API and should be stated directly for that owner rather than via a parallel pair of
  parameters `δ` and `hd`.
-/

variable (A B)

/-- Helper for Lemma 10.133.10: in degree `0`, the scalar commutator of the de Rham differential
is multiplication by the exact form `d b`. -/
theorem de_rham_degree_zero_scalar_commutator_apply
    (b x : B) :
    (deRhamDifferentialFamily A B 0).scalarCommutator b x =
      x • KaehlerDifferential.D A B b :=
  -- TODO: rewrite degree `0` forms to `B`, expand `LinearMap.scalarCommutator_apply`, and use the
  -- Leibniz rule for `KaehlerDifferential.D A B` to isolate the surviving `x • d b` term.
  sorry

/-- Helper for Lemma 10.133.10: the degree-zero de Rham differential is a first-order
differential operator. -/
theorem de_rham_degree_zero_is_order_one :
    (deRhamDifferentialFamily A B 0).IsDifferentialOperatorOfOrder B 1 :=
  -- TODO: after the previous commutator formula is stabilized, rewrite the order-zero condition
  -- for `Ω^[0][B⁄A] = B` and check the resulting `B`-linearity by a one-line scalar-associativity
  -- simplification.
  sorry

/-- Helper for Lemma 10.133.10: on basic degree-one forms, the scalar commutator retains only the
leftmost exact factor `d b`. -/
theorem de_rham_degree_one_scalar_commutator_smul_D
    (b c x : B) :
    (deRhamDifferentialFamily A B 1).scalarCommutator b (c • KaehlerDifferential.D A B x) =
      c • exteriorPower.ιMulti B 2
        (Fin.cases (KaehlerDifferential.D A B b) fun _ ↦ KaehlerDifferential.D A B x) :=
  -- TODO: expand the scalar commutator, rewrite the two degree-one differentials by
  -- `hd.degree_one`, apply the Leibniz rule to `d (b * c)`, and cancel the `b • d c ∧ d x`
  -- contribution via multilinearity of `exteriorPower.ιMulti`.
  sorry

/-- Helper for Lemma 10.133.10: on basic higher-degree forms, the scalar commutator again retains
only the new leftmost exact factor `d b`. -/
theorem de_rham_higher_scalar_commutator_smul_iMulti
    (q : ℕ) (b c : B) (fs : Fin (q + 2) → B) :
    (deRhamDifferentialFamily A B (q + 2)).scalarCommutator b
        (c • exteriorPower.ιMulti B (q + 2) (fun i ↦ KaehlerDifferential.D A B (fs i))) =
      c • exteriorPower.ιMulti B (q + 3)
        (Fin.cases (KaehlerDifferential.D A B b) fun i ↦ KaehlerDifferential.D A B (fs i)) :=
  -- TODO: follow the same commutator-plus-Leibniz calculation as in degree `1`, but with
  -- `hd.higher` and the higher exterior-power multilinearity on the leftmost wedge factor.
  sorry

/-- Helper for Lemma 10.133.10: every positive-degree de Rham differential is first-order. -/
theorem de_rham_positive_degree_is_order_one
    (q : ℕ) :
    (deRhamDifferentialFamily A B (q + 1)).IsDifferentialOperatorOfOrder B 1 :=
  -- TODO: use the two generator calculations above and a `B`-span induction on exact one-forms,
  -- respectively basic wedges of exact one-forms, to show each scalar commutator is order `0`.
  sorry

/-- Lemma 10.133.10: in the canonical relative de Rham complex of `B` over `A`, the universal
derivation and all positive-degree de Rham differentials are differential operators of order `1`.
-/
-- Proof sketch: for degree `0`, expand the scalar commutator of `δ 0` and use
-- `IsExteriorPowerDeRhamDifferential.degree_zero` to identify it with the universal derivation.
-- For higher degrees, evaluate the commutator of `δ (i + 1)` on basic forms and use the de Rham
-- rule encoded by `IsExteriorPowerDeRhamDifferential` to see that each commutator is `B`-linear,
-- hence order `0`.
theorem de_rham_differentials_are_order_one_differential_operators
    (p : ℕ) :
    (deRhamDifferentialFamily A B p).IsDifferentialOperatorOfOrder B 1 := by
  cases p with
  | zero =>
      -- Degree `0` is the universal derivation, handled directly from Leibniz.
      exact de_rham_degree_zero_is_order_one (A := A) (B := B)
  | succ q =>
      -- Positive degrees are controlled by the scalar commutator on basic generators.
      exact de_rham_positive_degree_is_order_one (A := A) (B := B) q

end
