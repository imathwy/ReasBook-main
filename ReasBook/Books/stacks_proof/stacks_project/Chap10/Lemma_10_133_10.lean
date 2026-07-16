import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_133_1
import stacks_proof.stacks_project.Chap10.Lemma_10_132_2

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

/-- Helper for Chap10 Lemma 10 133 10: an `R`-linear map that commutes with `S`-scalars on a
spanning set is an order-zero differential operator. -/
private theorem isDifferentialOperatorOfOrder_zero_of_span
    {R S M N : Type*} [Semiring R] [Semiring S]
    [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [Module S M] [Module S N]
    [SMulCommClass S R M] [SMulCommClass S R N]
    (D : M →ₗ[R] N) {s : Set M}
    (hs : Submodule.span S s = ⊤)
    (hD : ∀ x ∈ s, ∀ b : S, D (b • x) = b • D x) :
    D.IsDifferentialOperatorOfOrder S 0 := by
  -- Reduce order zero to scalar commutation and prove it by induction from the spanning set.
  rw [LinearMap.isDifferentialOperatorOfOrder_zero_iff]
  intro b x
  have hx : x ∈ Submodule.span S s := by
    rw [hs]
    exact Submodule.mem_top
  revert b
  induction hx using Submodule.span_induction with
  | mem y hy =>
      intro b
      exact hD y hy b
  | zero =>
      intro b
      simp
  | add y z _ _ hy hz =>
      intro b
      calc
        D (b • (y + z)) = D (b • y + b • z) := by
          rw [smul_add]
        _ = D (b • y) + D (b • z) := by
          rw [map_add]
        _ = b • D y + b • D z := by
          rw [hy b, hz b]
        _ = b • (D y + D z) := by
          rw [smul_add]
        _ = b • D (y + z) := by
          rw [map_add]
  | smul c y _ hy =>
      intro b
      calc
        D (b • (c • y)) = D ((b * c) • y) := by
          rw [smul_smul]
        _ = (b * c) • D y := hy (b * c)
        _ = b • (c • D y) := by
          rw [smul_smul]
        _ = b • D (c • y) := by
          rw [hy c]

/-- Helper for Chap10 Lemma 10 133 10: exact one-forms generate the corresponding exterior
power through the canonical alternating map. -/
private theorem de_rham_exactExteriorPower_span
    (n : ℕ) :
    Submodule.span B
        (exteriorPower.ιMulti B n ''
          {ω : Fin n → Ω[B⁄A] | Set.range ω ⊆ Set.range (KaehlerDifferential.D A B)}) =
      ⊤ := by
  -- Push the standard spanning theorem for Kähler differentials through the exterior-power
  -- generator theorem.
  simpa using
    (exteriorPower.ιMulti_span_of_span (R := B) (n := n) (M := Ω[B⁄A])
      (s := Set.range (KaehlerDifferential.D A B))
      (KaehlerDifferential.span_range_derivation (R := A) (S := B)))

/-- Helper for Chap10 Lemma 10 133 10: expanding the first coordinate of a basic exterior form
separates the Leibniz summands and cancels the scalar multiple already present in the
commutator. -/
private theorem iMulti_fin_cases_smul_add_smul_sub
    {M : Type*} [AddCommGroup M] [Module B M]
    (n : ℕ) (b c : B) (η ξ : M) (tail : Fin n → M) :
    exteriorPower.ιMulti B (n + 1) (Fin.cases (b • η + c • ξ) tail) -
        b • exteriorPower.ιMulti B (n + 1) (Fin.cases η tail) =
      c • exteriorPower.ιMulti B (n + 1) (Fin.cases ξ tail) := by
  -- Rewrite `Fin.cases` as an update at the first coordinate so multilinearity applies once.
  let base : Fin (n + 1) → M := Fin.cases 0 tail
  have hsum :
      Fin.cases (b • η + c • ξ) tail =
        Function.update base 0 (b • η + c • ξ) := by
    ext i
    cases i using Fin.cases with
    | zero =>
        simp [base]
    | succ i =>
        simp [base]
  have hη :
      Fin.cases η tail = Function.update base 0 η := by
    ext i
    cases i using Fin.cases with
    | zero =>
        simp [base]
    | succ i =>
        simp [base]
  have hξ :
      Fin.cases ξ tail = Function.update base 0 ξ := by
    ext i
    cases i using Fin.cases with
    | zero =>
        simp [base]
    | succ i =>
        simp [base]
  -- The alternating map is linear in the updated coordinate; the remaining equality is additive
  -- cancellation.
  rw [hsum, hη, hξ]
  rw [(exteriorPower.ιMulti B (n + 1)).map_update_add base 0 (b • η) (c • ξ),
    (exteriorPower.ιMulti B (n + 1)).map_update_smul base 0 b η,
    (exteriorPower.ιMulti B (n + 1)).map_update_smul base 0 c ξ]
  abel

/-- Helper for Chap10 Lemma 10 133 10: in degree `0`, the scalar commutator of the de Rham differential
is multiplication by the exact form `d b`. -/
theorem de_rham_degree_zero_scalar_commutator_apply
    (b x : B) :
    (deRhamDifferentialFamily A B 0).scalarCommutator b x =
      x • KaehlerDifferential.D A B b :=
  by
  -- Identify the degree-zero differential with the universal derivation, then apply Leibniz.
  have hzero :=
    (isExteriorPowerDeRhamDifferential_deRhamDifferentialFamily (A := A) (B := B)).degree_zero
  rw [LinearMap.scalarCommutator_apply,
    hzero]
  change (KaehlerDifferential.D A B) (b * x) - b • (KaehlerDifferential.D A B) x =
    x • KaehlerDifferential.D A B b
  rw [(KaehlerDifferential.D A B).leibniz b x]
  abel

/-- Helper for Chap10 Lemma 10 133 10: the degree-zero de Rham differential is a first-order
differential operator. -/
theorem de_rham_degree_zero_is_order_one :
    (deRhamDifferentialFamily A B 0).IsDifferentialOperatorOfOrder B 1 :=
  by
  -- A first-order operator is one whose scalar commutators are order zero.
  rw [LinearMap.isDifferentialOperatorOfOrder_succ_iff]
  intro b
  rw [LinearMap.isDifferentialOperatorOfOrder_zero_iff]
  intro c x
  -- The explicit commutator formula is compatible with scalar multiplication in degree zero.
  rw [de_rham_degree_zero_scalar_commutator_apply,
    de_rham_degree_zero_scalar_commutator_apply]
  exact mul_smul c x (KaehlerDifferential.D A B b)

/-- Helper for Chap10 Lemma 10 133 10: on basic degree-one forms, the scalar commutator retains only the
leftmost exact factor `d b`. -/
theorem de_rham_degree_one_scalar_commutator_smul_D
    (b c x : B) :
    (deRhamDifferentialFamily A B 1).scalarCommutator b (c • KaehlerDifferential.D A B x) =
      c • exteriorPower.ιMulti B 2
        (Fin.cases (KaehlerDifferential.D A B b) fun _ ↦ KaehlerDifferential.D A B x) :=
  by
  -- Expand the commutator and evaluate the degree-one differential on exact generators.
  rw [LinearMap.scalarCommutator_apply]
  have hsmul :
      b • (c • KaehlerDifferential.D A B x) =
        (b * c) • KaehlerDifferential.D A B x := by
    rw [smul_smul]
  have hd :=
    isExteriorPowerDeRhamDifferential_deRhamDifferentialFamily (A := A) (B := B)
  have hbc := hd.degree_one (b * c) x
  have hc := hd.degree_one c x
  change (deRhamDifferentialFamily A B 1) (b • (c • KaehlerDifferential.D A B x)) -
      b • (deRhamDifferentialFamily A B 1) (c • KaehlerDifferential.D A B x) =
    c • exteriorPower.ιMulti B 2
      (Fin.cases (KaehlerDifferential.D A B b) fun _ ↦ KaehlerDifferential.D A B x)
  rw [hsmul]
  rw [hbc, hc]
  -- Leibniz turns the first new coordinate into the sum whose `b • d c` part cancels.
  rw [(KaehlerDifferential.D A B).leibniz b c]
  exact iMulti_fin_cases_smul_add_smul_sub (B := B) 1 b c
    (KaehlerDifferential.D A B c) (KaehlerDifferential.D A B b)
    (fun _ ↦ KaehlerDifferential.D A B x)

/-- Helper for Chap10 Lemma 10 133 10: on an exact degree-one generator, the scalar commutator is
left wedge by `d b`. -/
theorem de_rham_degree_one_scalar_commutator_D
    (b x : B) :
    (deRhamDifferentialFamily A B 1).scalarCommutator b (KaehlerDifferential.D A B x) =
      exteriorPower.ιMulti B 2
        (Fin.cases (KaehlerDifferential.D A B b) fun _ ↦ KaehlerDifferential.D A B x) :=
  by
  -- Specialize the scalar-generator formula at coefficient `1`.
  simpa using
    (de_rham_degree_one_scalar_commutator_smul_D (A := A) (B := B) b 1 x)

/-- Helper for Chap10 Lemma 10 133 10: on basic higher-degree forms, the scalar commutator again retains
only the new leftmost exact factor `d b`. -/
theorem de_rham_higher_scalar_commutator_smul_iMulti
    (q : ℕ) (b c : B) (fs : Fin (q + 2) → B) :
    (deRhamDifferentialFamily A B (q + 2)).scalarCommutator b
        (c • exteriorPower.ιMulti B (q + 2) (fun i ↦ KaehlerDifferential.D A B (fs i))) =
      c • exteriorPower.ιMulti B (q + 3)
        (Fin.cases (KaehlerDifferential.D A B b) fun i ↦ KaehlerDifferential.D A B (fs i)) :=
  by
  -- The higher-degree calculation is the same generator computation with the `higher` field.
  rw [LinearMap.scalarCommutator_apply]
  have hsmul :
      b • (c • exteriorPower.ιMulti B (q + 2)
          (fun i ↦ KaehlerDifferential.D A B (fs i))) =
        (b * c) • exteriorPower.ιMulti B (q + 2)
          (fun i ↦ KaehlerDifferential.D A B (fs i)) := by
    rw [smul_smul]
  have hd :=
    isExteriorPowerDeRhamDifferential_deRhamDifferentialFamily (A := A) (B := B)
  have hbc := hd.higher q (b * c) fs
  have hc := hd.higher q c fs
  change (deRhamDifferentialFamily A B (q + 2))
        (b • (c • exteriorPower.ιMulti B (q + 2)
          (fun i ↦ KaehlerDifferential.D A B (fs i)))) -
      b • (deRhamDifferentialFamily A B (q + 2))
        (c • exteriorPower.ιMulti B (q + 2)
          (fun i ↦ KaehlerDifferential.D A B (fs i))) =
    c • exteriorPower.ιMulti B (q + 3)
      (Fin.cases (KaehlerDifferential.D A B b) fun i ↦ KaehlerDifferential.D A B (fs i))
  rw [hsmul]
  rw [hbc, hc]
  -- As in degree one, the Leibniz expansion splits the first coordinate and cancels the
  -- commutator's second summand.
  rw [(KaehlerDifferential.D A B).leibniz b c]
  exact iMulti_fin_cases_smul_add_smul_sub (B := B) (q + 2) b c
    (KaehlerDifferential.D A B c) (KaehlerDifferential.D A B b)
    (fun i ↦ KaehlerDifferential.D A B (fs i))

/-- Helper for Chap10 Lemma 10 133 10: on a basic higher-degree exact wedge, the scalar commutator is
left wedge by `d b`. -/
theorem de_rham_higher_scalar_commutator_iMulti
    (q : ℕ) (b : B) (fs : Fin (q + 2) → B) :
    (deRhamDifferentialFamily A B (q + 2)).scalarCommutator b
        (exteriorPower.ιMulti B (q + 2) (fun i ↦ KaehlerDifferential.D A B (fs i))) =
      exteriorPower.ιMulti B (q + 3)
        (Fin.cases (KaehlerDifferential.D A B b) fun i ↦ KaehlerDifferential.D A B (fs i)) :=
  by
  -- Specialize the higher-degree scalar-generator formula at coefficient `1`.
  simpa using
    (de_rham_higher_scalar_commutator_smul_iMulti (A := A) (B := B) q b 1 fs)

/-- Helper for Chap10 Lemma 10 133 10: every positive-degree de Rham differential is first-order. -/
theorem de_rham_positive_degree_is_order_one
    (q : ℕ) :
    (deRhamDifferentialFamily A B (q + 1)).IsDifferentialOperatorOfOrder B 1 :=
  by
  -- It is enough to prove every scalar commutator is order zero, separately in degree one and in
  -- higher exterior degrees.
  rw [LinearMap.isDifferentialOperatorOfOrder_succ_iff]
  intro b
  cases q with
  | zero =>
      -- Exact one-forms span `Ω[B⁄A]`, so the degree-one generator formula gives order zero.
      refine isDifferentialOperatorOfOrder_zero_of_span
        ((deRhamDifferentialFamily A B 1).scalarCommutator b)
        (s := Set.range (KaehlerDifferential.D A B)) ?_ ?_
      · exact KaehlerDifferential.span_range_derivation (R := A) (S := B)
      · rintro _ ⟨x, rfl⟩ c
        exact
          (de_rham_degree_one_scalar_commutator_smul_D (A := A) (B := B) b c x).trans
            (congrArg (fun y ↦ c • y)
              (de_rham_degree_one_scalar_commutator_D (A := A) (B := B) b x).symm)
  | succ q =>
      -- In higher degree, basic wedges of exact one-forms span the exterior power.
      refine isDifferentialOperatorOfOrder_zero_of_span
        ((deRhamDifferentialFamily A B (q + 2)).scalarCommutator b)
        (s := exteriorPower.ιMulti B (q + 2) ''
          {ω : Fin (q + 2) → Ω[B⁄A] |
            Set.range ω ⊆ Set.range (KaehlerDifferential.D A B)}) ?_ ?_
      · exact de_rham_exactExteriorPower_span (A := A) (B := B) (q + 2)
      · rintro _ ⟨ω, hω, rfl⟩ c
        classical
        choose fs hfs using fun i : Fin (q + 2) => hω ⟨i, rfl⟩
        have hωeq : ω = fun i ↦ KaehlerDifferential.D A B (fs i) := by
          ext i
          exact (hfs i).symm
        rw [hωeq]
        exact
          (de_rham_higher_scalar_commutator_smul_iMulti (A := A) (B := B) q b c fs).trans
            (congrArg (fun y ↦ c • y)
              (de_rham_higher_scalar_commutator_iMulti (A := A) (B := B) q b fs).symm)

/-- Chap10 Lemma 10 133 10: in the canonical relative de Rham complex of `B` over `A`, the universal
derivation and all positive-degree de Rham differentials are differential operators of order `1`.
-/
-- Proof sketch: for degree `0`, expand the scalar commutator of `δ 0` and use
-- `IsExteriorPowerDeRhamDifferential.degree_zero` to identify it with the universal derivation.
-- For higher degrees, evaluate the commutator of `δ (i + 1)` on basic forms and use the de Rham
-- rule encoded by `IsExteriorPowerDeRhamDifferential` to see that each commutator is `B`-linear,
-- hence order `0`.
@[stacks 0G34]
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
