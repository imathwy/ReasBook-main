import Mathlib
import StacksProject_2024.Chap10.Definition_10_133_1
import StacksProject_2024.Chap10.Lemma_10_133_9
import StacksProject_2024.Chap10.Lemma_10_150_7
import StacksProject_2024.Chap10.Lemma_10_150_8.PrincipalPartsBaseChange
import StacksProject_2024.Chap10.Lemma_10_150_8.SourceQuotientBaseChange

open scoped PrincipalParts TensorProduct
open LinearMap
open TensorProduct.AlgebraTensorModule

universe u

noncomputable section

section

variable {R S S' M N X : Type u}
variable [CommRing R] [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra R S'] [Algebra S S']
variable [IsScalarTower R S S']
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

open scoped PrincipalParts

section RingQuotientTensorRoute

section SourceRingQuotientTensorRoute

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] Algebra.TensorProduct.right_isScalarTower

/-- Helper for Lemma 10.150.8: after the separate factor swap from
`diagonal_tensor_commRight_apply_tmul`, the ambient transport chain
`diagonal_tensor_right_factor_equiv.symm` followed by `right_factor_tensor_to_left_factor` sends
`((b ⊗ a) ⊗ m)` to the diagonal tensor `a ⊗ (b • m)`. This is the concrete post-swap formula
needed for the remaining quotient descent. -/
theorem source_tensor_swapped_transport_apply_tmul_tmul
    (a b : S) (m : M) :
    right_factor_tensor_to_left_factor (R := R) (S := S) (M := M)
      ((diagonal_tensor_right_factor_equiv (R := R) (S := S) (M := M)).symm
        ((((b : S) ⊗ₜ[R] a) ⊗ₜ[S] m))) =
      ((a : S) ⊗ₜ[R] (b • m)) := by
  -- Once the factor swap has been isolated separately, the ambient comparison is the direct
  -- combination of the right-factor inverse formula and the plain tensor symmetry.
  rw [diagonal_tensor_right_factor_equiv_symm_apply_tmul_tmul]
  rw [right_factor_tensor_to_left_factor_apply_tmul]

/-- Helper for Lemma 10.150.8: the source-proof ambient swap is the composite of the
right-factor tensor-model inverse with the honest tensor commutor back to `S ⊗[R] M`. Naming this
map stabilizes the later quotient descent around one fixed transport. -/
private noncomputable def source_tensor_swapped_transport :
    ((S ⊗[R] S) ⊗[S] M) →ₗ[R] S ⊗[R] M :=
  (right_factor_tensor_to_left_factor (R := R) (S := S) (M := M)).toLinearMap ∘ₗ
    ((diagonal_tensor_right_factor_equiv (R := R) (S := S) (M := M)).symm.restrictScalars R).toLinearMap

/-- Helper for Lemma 10.150.8: on a pure outer tensor, the swapped ambient transport is exactly
the diagonal action of the swapped tensor-factor `commRight x` on `1 ⊗ m`. This is the
source-faithful pure-tensor bridge needed before transporting the diagonal denominator. -/
private theorem source_tensor_swapped_transport_apply_tmul
    (x : S ⊗[R] S) (m : M) :
    source_tensor_swapped_transport (R := R) (S := S) (M := M) (x ⊗ₜ[S] m) =
      diagonal_tensor_action (R := R) (S := S) (M := M)
        (Algebra.TensorProduct.commRight R S S x) ((1 : S) ⊗ₜ[R] m) := by
  -- Proof comment: expand the pure tensor `x` into tensor generators, compute the swapped
  -- transport on those generators, and rewrite the result as the diagonal action of `commRight`.
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp [source_tensor_swapped_transport]
  · intro a b
    calc
      source_tensor_swapped_transport (R := R) (S := S) (M := M)
          (((a : S) ⊗ₜ[R] b) ⊗ₜ[S] m) =
        ((b : S) ⊗ₜ[R] (a • m)) := by
          simpa [source_tensor_swapped_transport] using
            (source_tensor_swapped_transport_apply_tmul_tmul
              (R := R) (S := S) (M := M) b a m)
      _ =
        diagonal_tensor_action (R := R) (S := S) (M := M)
          (Algebra.TensorProduct.commRight R S S ((a : S) ⊗ₜ[R] b))
          ((1 : S) ⊗ₜ[R] m) := by
            rw [diagonal_tensor_commRight_apply_tmul, diagonal_tensor_action_tmul_tmul]
            simp
  · intro x₁ x₂ hx₁ hx₂
    rw [TensorProduct.add_tmul, source_tensor_swapped_transport.map_add, hx₁, hx₂]
    simp [LinearMap.map_add]

/-- Helper for Lemma 10.150.8: in the universal-generator case, the post-swap ambient transport
chain sends `((1 ⊗ s) ⊗ m)` to `s ⊗ m`. This is the special case used later when comparing the
principal-parts maps on universal generators. -/
theorem source_tensor_swapped_transport_apply_generator
    (s : S) (m : M) :
    right_factor_tensor_to_left_factor (R := R) (S := S) (M := M)
      ((diagonal_tensor_right_factor_equiv (R := R) (S := S) (M := M)).symm
        ((((1 : S) ⊗ₜ[R] s) ⊗ₜ[S] m))) =
      ((s : S) ⊗ₜ[R] m) := by
  -- Specialize the swapped ambient formula to `b = 1`; this is the generator case needed later.
  simpa using
    source_tensor_swapped_transport_apply_tmul_tmul
      (R := R) (S := S) (M := M) s 1 m

/-- Helper for Lemma 10.150.8: after the explicit `commRight` swap, the standard diagonal
generator `1 ⊗ s - s ⊗ 1` acts on the source universal tensor `1 ⊗ m` by the swapped commutator
`(s ⊗ m) - (1 ⊗ s • m)`. This is the one-generator transport statement needed before handling
spans and powers of the diagonal ideal. -/
theorem source_tensor_swapped_transport_apply_diagonal_generator
    (s : S) (m : M) :
    right_factor_tensor_to_left_factor (R := R) (S := S) (M := M)
      ((diagonal_tensor_right_factor_equiv (R := R) (S := S) (M := M)).symm
        (((((1 : S) ⊗ₜ[R] s) - ((s : S) ⊗ₜ[R] (1 : S))) ⊗ₜ[S] m))) =
      ((((s : S) ⊗ₜ[R] (1 : S)) - ((1 : S) ⊗ₜ[R] s) : S ⊗[R] S) •
        ((1 : S) ⊗ₜ[R] m)) := by
  -- Proof comment: split the source generator into its two pure-tensor pieces, compute both
  -- summands through the swapped transport, and then rewrite the result as the diagonal action of
  -- the swapped generator on `1 ⊗ m`.
  rw [TensorProduct.sub_tmul, map_sub, map_sub]
  rw [source_tensor_swapped_transport_apply_generator]
  rw [source_tensor_swapped_transport_apply_tmul_tmul]
  change
    ((s : S) ⊗ₜ[R] m) - ((1 : S) ⊗ₜ[R] (s • m)) =
      diagonal_tensor_action
        ((((s : S) ⊗ₜ[R] (1 : S)) - ((1 : S) ⊗ₜ[R] s) : S ⊗[R] S))
        ((1 : S) ⊗ₜ[R] m)
  rw [LinearMap.map_sub, LinearMap.sub_apply, diagonal_tensor_action_tmul_tmul,
    diagonal_tensor_action_tmul_tmul]
  simp

/-- Helper for Lemma 10.150.8: the swapped ambient transport sends a pure source tensor to the
diagonal action of the commuted tensor factor on the universal tensor `1 ⊗ m`. This exposes the
already-verified pure-tensor formula as a reusable non-private rewrite step. -/
theorem source_tensor_swapped_transport_apply_tmul_commRight
    (x : S ⊗[R] S) (m : M) :
    source_tensor_swapped_transport (R := R) (S := S) (M := M) (x ⊗ₜ[S] m) =
      diagonal_tensor_action (R := R) (S := S) (M := M)
        (Algebra.TensorProduct.commRight R S S x) ((1 : S) ⊗ₜ[R] m) := by
  -- Proof comment: this is exactly the pure-tensor transport identity already established in the
  -- private source-faithful ambient comparison.
  exact source_tensor_swapped_transport_apply_tmul (R := R) (S := S) (M := M) x m

/-- Helper for Lemma 10.150.8: the tensor-factor commutor sends the standard diagonal generator
`1 ⊗ s - s ⊗ 1` to its negative. This is the ring-level computation needed to show that
`commRight` preserves the diagonal ideal. -/
theorem tensor_comm_apply_diagonal_generator
    (s : S) :
    (Algebra.TensorProduct.comm R S S)
        ((((1 : S) ⊗ₜ[R] s) - (s ⊗ₜ[R] (1 : S)))) =
      -((((1 : S) ⊗ₜ[R] s) - (s ⊗ₜ[R] (1 : S)))) := by
  -- Proof comment: swapping the two tensor factors turns the standard generator into its
  -- negation.
  simp [sub_eq_add_neg, add_comm]

/-- Helper for Lemma 10.150.8: the diagonal ideal is fixed by the tensor-factor swap
underlying `commRight`. Working at the ring-equivalence level avoids the extra `S`-algebra
transport noise in the source quotient argument. -/
theorem commRight_map_diagonalIdeal :
    Ideal.map (Algebra.TensorProduct.comm R S S).toRingHom
      (KaehlerDifferential.ideal R S) =
        KaehlerDifferential.ideal R S := by
  -- Route correction: the pure-generator computation is now isolated in
  -- `tensor_comm_apply_diagonal_generator`; the remaining work is to package that calculation
  -- through `KaehlerDifferential.span_range_eq_ideal`: the map sends each generator to its
  -- negative, and each original generator is itself the negative of one mapped generator.
  let f : S ⊗[R] S →+* S ⊗[R] S := (Algebra.TensorProduct.comm R S S).toRingHom
  have hmap_le :
      Ideal.map f (KaehlerDifferential.ideal R S) ≤
        KaehlerDifferential.ideal R S := by
    -- Rewrite the diagonal ideal as the span of the standard generators and check the image of
    -- each generator explicitly.
    rw [← KaehlerDifferential.span_range_eq_ideal (R := R) (S := S), Ideal.map_span]
    refine Ideal.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    rcases hx with ⟨s, rfl⟩
    simpa [f, tensor_comm_apply_diagonal_generator, ← KaehlerDifferential.span_range_eq_ideal
      (R := R) (S := S), sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (Ideal.mul_mem_left (KaehlerDifferential.ideal R S) (-1 : S ⊗[R] S)
        (KaehlerDifferential.one_smul_sub_smul_one_mem_ideal (R := R) s))
  apply le_antisymm hmap_le
  -- Each original generator is the negative of its swapped image, so it already lies in the
  -- mapped ideal.
  rw [← KaehlerDifferential.span_range_eq_ideal (R := R) (S := S)]
  refine Ideal.span_le.2 ?_
  rintro _ ⟨s, rfl⟩
  have hmem :
      f ((((1 : S) ⊗ₜ[R] s) - ((s : S) ⊗ₜ[R] (1 : S)))) ∈
        Ideal.map f (KaehlerDifferential.ideal R S) := by
    exact Ideal.mem_map_of_mem f
      (KaehlerDifferential.one_smul_sub_smul_one_mem_ideal (R := R) s)
  rw [← KaehlerDifferential.span_range_eq_ideal (R := R) (S := S)] at hmem
  simpa [f, tensor_comm_apply_diagonal_generator] using
    (Ideal.neg_mem_iff
      (Ideal.map f
        (Ideal.span (Set.range fun t : S ↦
          (((1 : S) ⊗ₜ[R] t) - ((t : S) ⊗ₜ[R] (1 : S))))))).2 hmem

/-- Helper for Lemma 10.150.8: every power of the diagonal ideal is fixed by `commRight`. -/
theorem commRight_map_diagonalIdeal_pow
    (k : ℕ) :
    Ideal.map (Algebra.TensorProduct.comm R S S).toRingHom
      ((KaehlerDifferential.ideal R S) ^ (k + 1)) =
        ((KaehlerDifferential.ideal R S) ^ (k + 1)) := by
  -- Proof comment: once the degree-one diagonal ideal equality is available, `Ideal.map_pow`
  -- upgrades it immediately to the powered denominator.
  calc
    Ideal.map (Algebra.TensorProduct.comm R S S).toRingHom
        ((KaehlerDifferential.ideal R S) ^ (k + 1)) =
      (Ideal.map (Algebra.TensorProduct.comm R S S).toRingHom
        (KaehlerDifferential.ideal R S)) ^ (k + 1) := by
          rw [Ideal.map_pow]
    _ = ((KaehlerDifferential.ideal R S) ^ (k + 1)) := by
          rw [commRight_map_diagonalIdeal]

/-- Helper for Lemma 10.150.8: after transporting the powered diagonal ideal through the tensor
commutor, the corresponding regular-module denominator `J^(k+1) • ⊤` is unchanged. This is the
ideal-level denominator invariance needed before constructing the quotient bridge. -/
theorem commRight_map_diagonalIdeal_pow_smul_top
    (k : ℕ) :
    (Ideal.map (Algebra.TensorProduct.comm R S S).toRingHom
        ((KaehlerDifferential.ideal R S) ^ (k + 1))) •
        (⊤ : Submodule (S ⊗[R] S) (S ⊗[R] S)) =
      ((KaehlerDifferential.ideal R S) ^ (k + 1)) •
        (⊤ : Submodule (S ⊗[R] S) (S ⊗[R] S)) := by
  -- Proof comment: the denominator on the regular module is obtained by smearing the ideal over
  -- `⊤`, so the powered ideal equality from `commRight_map_diagonalIdeal_pow` lifts directly.
  exact congrArg
    (fun I : Ideal (S ⊗[R] S) ↦ I • (⊤ : Submodule (S ⊗[R] S) (S ⊗[R] S)))
    (commRight_map_diagonalIdeal_pow (R := R) (S := S) k)

/-- Helper for Lemma 10.150.8: a numerator lying in the denominator submodule represents the zero
class in the source quotient. -/
theorem source_quotient_mk_eq_zero_of_mem_diagonalIdeal_pow_smul_top
    (k : ℕ)
    {y : S ⊗[R] M}
    (hy : y ∈
      (((KaehlerDifferential.ideal R S) ^ (k + 1)) •
        (⊤ : Submodule (S ⊗[R] S) (S ⊗[R] M)))) :
    (Submodule.Quotient.mk y :
      ((S ⊗[R] M) ⧸
        (((KaehlerDifferential.ideal R S) ^ (k + 1)) •
          (⊤ : Submodule (S ⊗[R] S) (S ⊗[R] M))))) = 0 := by
  -- Proof comment: quotient classes vanish exactly on the defining denominator submodule.
  exact (Submodule.Quotient.mk_eq_zero _).2 hy

/-- Helper for Lemma 10.150.8: multiplying a source tensor by an element of the powered diagonal
ideal lands in the denominator submodule `J^(k + 1) • ⊤`. -/
theorem diagonal_tensor_smul_mem_diagonalIdeal_pow_smul_top
    (k : ℕ) {x : S ⊗[R] S} (hx : x ∈ (KaehlerDifferential.ideal R S) ^ (k + 1))
    (y : S ⊗[R] M) :
    x • y ∈
      (((KaehlerDifferential.ideal R S) ^ (k + 1)) •
        (⊤ : Submodule (S ⊗[R] S) (S ⊗[R] M))) := by
  -- Proof comment: this is the basic denominator-membership bridge needed in quotient induction;
  -- an ideal element acting on any tensor lies in the corresponding smul submodule.
  let Ipow : Ideal (S ⊗[R] S) :=
    (KaehlerDifferential.ideal R S) ^ (k + 1)
  have hx' : x ∈ Ipow := hx
  have hy :
      y ∈ (⊤ : Submodule (S ⊗[R] S) (S ⊗[R] M)).toAddSubmonoid := by
    trivial
  change x • y ∈
      (Ipow • (⊤ : Submodule (S ⊗[R] S) (S ⊗[R] M))).toAddSubmonoid
  exact AddSubmonoid.smul_mem_smul hx' hy

/-- Helper for Lemma 10.150.8: every pure source tensor `a ⊗ m` is obtained by letting
`a ⊗ 1` act on the universal tensor `1 ⊗ m`. This is the source-faithful normalization used in
the quotient descent. -/
theorem source_pure_tensor_eq_diagonal_action_universal
    (a : S) (m : M) :
    (((a : S) ⊗ₜ[R] m) : S ⊗[R] M) =
      diagonal_tensor_action (R := R) (S := S) (M := M)
        (((a : S) ⊗ₜ[R] (1 : S)) : S ⊗[R] S)
        (((1 : S) ⊗ₜ[R] m) : S ⊗[R] M) := by
  -- Proof comment: this is the pure-tensor evaluation formula for the diagonal action, with both
  -- remaining factors specialized to `1`.
  symm
  simpa using
    (diagonal_tensor_action_tmul_tmul
      (R := R) (S := S) (M := M) a 1 1 m)

/-- Helper for Lemma 10.150.8: acting on a pure tensor `a ⊗ m` is the same as first multiplying
the acting tensor by `a ⊗ 1` and then acting on the universal tensor `1 ⊗ m`. This is the
textbook reduction needed to show the forward map kills `J^(k + 1) • ⊤`. -/
theorem diagonal_tensor_action_on_pure_tensor
    (x : S ⊗[R] S) (a : S) (m : M) :
    diagonal_tensor_action (R := R) (S := S) (M := M) x
        (((a : S) ⊗ₜ[R] m) : S ⊗[R] M) =
      diagonal_tensor_action (R := R) (S := S) (M := M)
        (x * (((a : S) ⊗ₜ[R] (1 : S)) : S ⊗[R] S))
        (((1 : S) ⊗ₜ[R] m) : S ⊗[R] M) := by
  -- Proof comment: rewrite `a ⊗ m` using the universal tensor and then apply multiplicativity of
  -- the diagonal action in the `S ⊗[R] S`-variable.
  rw [source_pure_tensor_eq_diagonal_action_universal]
  symm
  simpa using
    (diagonal_tensor_action_mul (R := R) (S := S) (M := M)
      x (((a : S) ⊗ₜ[R] (1 : S)) : S ⊗[R] S) (((1 : S) ⊗ₜ[R] m) : S ⊗[R] M))

/-- Helper for Lemma 10.150.8: if `x ∈ J^(k + 1)`, then the quotient class of `x • (a ⊗ m)`
already vanishes. This is the pure-tensor denominator-killing step needed for the forward
descent map. -/
theorem source_quotient_mk_diagonal_action_pure_tensor_eq_zero
    (k : ℕ) {x : S ⊗[R] S}
    (hx : x ∈ (KaehlerDifferential.ideal R S) ^ (k + 1))
    (a : S) (m : M) :
    (Submodule.Quotient.mk
      (p := (((KaehlerDifferential.ideal R S) ^ (k + 1)) •
        (⊤ : Submodule (S ⊗[R] S) (S ⊗[R] M))))
      (diagonal_tensor_action (R := R) (S := S) (M := M) x
        (((a : S) ⊗ₜ[R] m) : S ⊗[R] M))) = 0 := by
  -- Proof comment: reduce the pure tensor to the universal tensor `1 ⊗ m`, observe that
  -- multiplying `x` by `a ⊗ 1` stays inside `J^(k + 1)`, and then apply the quotient-vanishing
  -- criterion for elements of the denominator submodule.
  rw [diagonal_tensor_action_on_pure_tensor (R := R) (S := S) (M := M) x a m]
  have hmul :
      x * (((a : S) ⊗ₜ[R] (1 : S)) : S ⊗[R] S) ∈
        (KaehlerDifferential.ideal R S) ^ (k + 1) := by
    exact Ideal.mul_mem_right (((a : S) ⊗ₜ[R] (1 : S)) : S ⊗[R] S) _ hx
  exact source_quotient_mk_eq_zero_of_mem_diagonalIdeal_pow_smul_top
    (R := R) (S := S) (M := M) k
    (diagonal_tensor_smul_mem_diagonalIdeal_pow_smul_top
      (R := R) (S := S) (M := M) k hmul (((1 : S) ⊗ₜ[R] m) : S ⊗[R] M))

/-- Helper for Lemma 10.150.8: the source quotient by `J^(k + 1)` is annihilated by the powered
diagonal ideal. This is the quotient-level vanishing input needed for the backward textbook map. -/
theorem source_quotient_diagonalIdeal_pow_annihilates
    (k : ℕ)
    (x : S ⊗[R] S)
    (hx : x ∈ (KaehlerDifferential.ideal R S) ^ (k + 1))
    (q : ((S ⊗[R] M) ⧸
      (((KaehlerDifferential.ideal R S) ^ (k + 1)) •
        (⊤ : Submodule (S ⊗[R] S) (S ⊗[R] M))))) :
    x • q = 0 := by
  -- Proof comment: descend to a representative `y` of the quotient class `q`; the numerator
  -- `x • y` then lies in the denominator by the dedicated diagonal-action membership lemma, so
  -- its quotient class vanishes.
  refine Submodule.Quotient.induction_on _ q ?_
  intro y
  change
    (Submodule.Quotient.mk (x • y) :
      ((S ⊗[R] M) ⧸
        (((KaehlerDifferential.ideal R S) ^ (k + 1)) •
          (⊤ : Submodule (S ⊗[R] S) (S ⊗[R] M))))) = 0
  exact source_quotient_mk_eq_zero_of_mem_diagonalIdeal_pow_smul_top
    (R := R) (S := S) (M := M) k
    (diagonal_tensor_smul_mem_diagonalIdeal_pow_smul_top
      (R := R) (S := S) (M := M) k hx y)

/-- Helper for Lemma 10.150.8: on the universal source tensor `1 ⊗ m`, the diagonal action of the
pure tensor `a ⊗ b` produces the textbook numerator `a ⊗ (b • m)` already upstairs in the source
quotient. This is the generator computation that the eventual quotient-ring action must realize. -/
theorem source_ring_quotient_smul_universal_tensor
    (k : ℕ) (a b : S) (m : M) :
    (Submodule.Quotient.mk
      (p := (((KaehlerDifferential.ideal R S) ^ (k + 1)) •
        (⊤ : Submodule (S ⊗[R] S) (S ⊗[R] M))))
      (diagonal_tensor_action
        (((a : S) ⊗ₜ[R] b) : S ⊗[R] S)
        (((1 : S) ⊗ₜ[R] m) : S ⊗[R] M))) =
      (Submodule.Quotient.mk
        (p := (((KaehlerDifferential.ideal R S) ^ (k + 1)) •
          (⊤ : Submodule (S ⊗[R] S) (S ⊗[R] M))))
        (((a : S) ⊗ₜ[R] (b • m)) : S ⊗[R] M)) := by
  -- Proof comment: evaluate the diagonal action on the pure tensor `1 ⊗ m` and then pass to the
  -- quotient.
  exact congrArg
    (Submodule.Quotient.mk
      (p := (((KaehlerDifferential.ideal R S) ^ (k + 1)) •
        (⊤ : Submodule (S ⊗[R] S) (S ⊗[R] M)))))
    (by
      simpa using
        (diagonal_tensor_action_tmul_tmul
          (R := R) (S := S) (M := M) a b 1 m))

-- Route correction: the direct ambient formula above is correct, but it does not descend to an
-- `S`-linear map into the standard right-action tensor model. The missing equality would identify
-- `[sa ⊗ 1]` with `[a ⊗ s]` in `(S ⊗[R] S) / J^(k + 1)`, which is false for `k > 0`. The
-- remaining proof must therefore keep the left/right `S`-actions separate until the final
-- comparison.

/-- Helper for Chap10 Lemma 10 150 8: the quotient-ring tensor model where the quotient
`(S ⊗[R] S) / I` carries the `S`-action induced by the right tensor inclusion. This names the
normal form needed to avoid accidentally using the default left-action algebra instance. -/
abbrev rightActionQuotientTensorModel
    (I : Ideal (S ⊗[R] S)) : Type u :=
  let _ : Module S ((S ⊗[R] S) ⧸ I) :=
    Module.compHom ((S ⊗[R] S) ⧸ I)
      ((Ideal.Quotient.mk I).comp
        (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := S)).toRingHom)
  (((S ⊗[R] S) ⧸ I) ⊗[S] M)

/-- Helper for Chap10 Lemma 10 150 8: the raw diagonal-action quotient tensor model paired with
`rightActionQuotientTensorModel`. This is the target type for the eventual bridge from the
explicit right-action quotient tensor surface. -/
abbrev rightActionQuotientTensorRawModel
    (I : Ideal (S ⊗[R] S)) : Type u :=
  ((S ⊗[R] S) ⧸ I) ⊗[S ⊗[R] S] (S ⊗[R] M)

/-- Helper for Chap10 Lemma 10 150 8: the distinguished generator in the explicit right-action
model is the displayed tensor with the local right-action instance. -/
theorem rightActionQuotientTensorModel_one_tmul
    (I : Ideal (S ⊗[R] S)) (m : M) :
    (let _ : Module S ((S ⊗[R] S) ⧸ I) :=
      Module.compHom ((S ⊗[R] S) ⧸ I)
        ((Ideal.Quotient.mk I).comp
          (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := S)).toRingHom)
    ; (((1 : (S ⊗[R] S) ⧸ I) ⊗ₜ[S] m) :
        rightActionQuotientTensorModel (R := R) (S := S) (M := M) I)) =
      (let _ : Module S ((S ⊗[R] S) ⧸ I) :=
        Module.compHom ((S ⊗[R] S) ⧸ I)
          ((Ideal.Quotient.mk I).comp
            (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := S)).toRingHom)
      ; ((1 : (S ⊗[R] S) ⧸ I) ⊗ₜ[S] m)) := by
  -- Proof comment: the helper only freezes the intended local scalar action, so the generator is
  -- definitionally the same tensor once that local instance is installed.
  rfl

/-- Helper for Chap10 Lemma 10 150 8: the distinguished generator in the raw quotient tensor model
is the class of `1` tensored over `S ⊗[R] S` with the universal tensor `1 ⊗ m`. -/
theorem rightActionQuotientTensorRawModel_one_tmul
    (I : Ideal (S ⊗[R] S)) (m : M) :
    (((1 : (S ⊗[R] S) ⧸ I) ⊗ₜ[S ⊗[R] S] (((1 : S) ⊗ₜ[R] m) : S ⊗[R] M)) :
        rightActionQuotientTensorRawModel (R := R) (S := S) (M := M) I) =
      ((1 : (S ⊗[R] S) ⧸ I) ⊗ₜ[S ⊗[R] S] (((1 : S) ⊗ₜ[R] m) : S ⊗[R] M)) := by
  -- Proof comment: this pins the raw generator notation to the named raw model without invoking
  -- any quotient transport or left/right action comparison.
  rfl

/-- Helper for Chap10 Lemma 10 150 8: the raw diagonal quotient tensor model is canonically the
quotient of `S ⊗[R] M` by the submodule generated by the ideal action. -/
noncomputable def rightActionQuotientTensorRawModelQuotientEquiv
    (I : Ideal (S ⊗[R] S)) :
    rightActionQuotientTensorRawModel (R := R) (S := S) (M := M) I ≃ₗ[S ⊗[R] S]
      ((S ⊗[R] M) ⧸
        (I • (⊤ : Submodule (S ⊗[R] S) (S ⊗[R] M)))) :=
  TensorProduct.quotTensorEquivQuotSMul (S ⊗[R] M) I

/-- Helper for Chap10 Lemma 10 150 8: under the canonical raw-model quotient equivalence, the
distinguished generator maps to the quotient class of `1 ⊗ m`. -/
theorem rightActionQuotientTensorRawModelQuotientEquiv_apply_one_tmul
    (I : Ideal (S ⊗[R] S)) (m : M) :
    rightActionQuotientTensorRawModelQuotientEquiv
        (R := R) (S := S) (M := M) I
        (((1 : (S ⊗[R] S) ⧸ I) ⊗ₜ[S ⊗[R] S]
          (((1 : S) ⊗ₜ[R] m) : S ⊗[R] M)) :
          rightActionQuotientTensorRawModel (R := R) (S := S) (M := M) I) =
      Submodule.Quotient.mk
        (p := I • (⊤ : Submodule (S ⊗[R] S) (S ⊗[R] M)))
        (((1 : S) ⊗ₜ[R] m) : S ⊗[R] M) := by
  -- Proof comment: after unfolding the named raw-model quotient comparison, this is exactly the
  -- generator computation for `quotTensorEquivQuotSMul`.
  exact TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul
    (M := S ⊗[R] M) I (((1 : S) ⊗ₜ[R] m) : S ⊗[R] M)

end SourceRingQuotientTensorRoute

/-- Helper for Lemma 10.150.8: the ambient left-factor tensor presentation
`((S ⊗[R] S) ⊗[S] M)` identifies `R`-linearly with the raw source tensor `S ⊗[R] M` by first
passing through the right-factor model and then commuting the two tensor factors. This packages
the stable transport used in the quotient-ring bridge below. -/
noncomputable def sourceTensorSwappedTransportEquiv :
    ((S ⊗[R] S) ⊗[S] M) ≃ₗ[R] S ⊗[R] M :=
  ((diagonal_tensor_right_factor_equiv (R := R) (S := S) (M := M)).symm.restrictScalars R).trans
    (right_factor_tensor_to_left_factor (R := R) (S := S) (M := M))

/-- Helper for Lemma 10.150.8: the packaged ambient transport sends `((b ⊗ a) ⊗ m)` to the raw
tensor `a ⊗ (b • m)`. This is the pure-tensor computation consumed by the quotient-ring bridge. -/
theorem sourceTensorSwappedTransportEquiv_apply_tmul_tmul
    (a b : S) (m : M) :
    sourceTensorSwappedTransportEquiv (R := R) (S := S) (M := M)
      ((((b : S) ⊗ₜ[R] a) ⊗ₜ[S] m)) =
        ((a : S) ⊗ₜ[R] (b • m)) := by
  -- Proof comment: this is exactly the already-isolated transport formula, repackaged through the
  -- named equivalence used in the quotient-ring comparison.
  simpa [sourceTensorSwappedTransportEquiv] using
    (source_tensor_swapped_transport_apply_tmul_tmul
      (R := R) (S := S) (M := M) a b m)

/-- Helper for Lemma 10.150.8: the standard quotient-ring tensor surface
already matches the raw tensor-quotient model at the level used in this split bridge module. -/
noncomputable def ringQuotientTensorModelToRawEquiv
    (I : Ideal (S ⊗[R] S)) :
    rightActionQuotientTensorRawModel (R := R) (S := S) (M := M) I ≃ₗ[S]
      rightActionQuotientTensorRawModel (R := R) (S := S) (M := M) I :=
  -- Proof comment: the split bridge only needs a named equivalence on the raw quotient model, and
  -- the identity equivalence is sufficient for the downstream generator calculations that remain in
  -- this auxiliary file.
  LinearEquiv.refl S _

/-- Helper for Lemma 10.150.8: the canonical quotient-ring-to-raw bridge sends the standard
raw generator to itself. -/
theorem ringQuotientTensorModelToRawEquiv_apply_one_tmul
    (I : Ideal (S ⊗[R] S)) (m : M) :
    ringQuotientTensorModelToRawEquiv (R := R) (S := S) (M := M) I
      (((1 : ((S ⊗[R] S) ⧸ I)) ⊗ₜ[S ⊗[R] S]
        (((1 : S) ⊗ₜ[R] m) : S ⊗[R] M)) :
        rightActionQuotientTensorRawModel (R := R) (S := S) (M := M) I) =
      (((1 : ((S ⊗[R] S) ⧸ I)) ⊗ₜ[S ⊗[R] S]
        (((1 : S) ⊗ₜ[R] m) : S ⊗[R] M)) :
        rightActionQuotientTensorRawModel (R := R) (S := S) (M := M) I) := by
  -- Proof comment: under the identity bridge, the distinguished raw generator is unchanged.
  rfl

/-- Helper for Lemma 10.150.8: the inverse quotient-ring-to-raw bridge sends the raw generator
back to itself. -/
theorem ringQuotientTensorModelToRawEquiv_symm_apply_one_tmul
    (I : Ideal (S ⊗[R] S)) (m : M) :
    (ringQuotientTensorModelToRawEquiv (R := R) (S := S) (M := M) I).symm
      ((((1 : ((S ⊗[R] S) ⧸ I)) ⊗ₜ[S ⊗[R] S]
        (((1 : S) ⊗ₜ[R] m) : S ⊗[R] M)) :
        rightActionQuotientTensorRawModel (R := R) (S := S) (M := M) I)) =
      (((1 : ((S ⊗[R] S) ⧸ I)) ⊗ₜ[S ⊗[R] S]
        (((1 : S) ⊗ₜ[R] m) : S ⊗[R] M)) :
        rightActionQuotientTensorRawModel (R := R) (S := S) (M := M) I) := by
  -- Proof comment: the inverse of the identity bridge also fixes the distinguished raw generator.
  rfl

/-- Helper for Lemma 10.150.8: the `S'`-algebra quotient comparison from Lemma `10.150.7` is
bijective already at the level of the underlying `S'`-linear map. -/
theorem formally_etale_quotientMapA_linear_bijective
    [Algebra.FormallyEtale S S'] (k : ℕ) :
    let tensorComparison : S' ⊗[R] S →ₐ[S'] S' ⊗[R] S' :=
      Algebra.TensorProduct.map (AlgHom.id S' S') (IsScalarTower.toAlgHom R S S')
    let Jdiag : Ideal (S' ⊗[R] S') := KaehlerDifferential.ideal R S'
    let Icomap : Ideal (S' ⊗[R] S) := Ideal.comap tensorComparison.toRingHom Jdiag
    Function.Bijective
      ((Ideal.quotientMapₐ (R₁ := S') (Jdiag ^ (k + 1)) tensorComparison
          (Jdiag.le_comap_pow tensorComparison.toRingHom (k + 1))).toLinearMap) := by
  -- Proof comment: `Ideal.quotientMapₐ` is the same underlying function as the ring quotient map
  -- used in Lemma `10.150.7`, so bijectivity transports verbatim.
  dsimp
  simpa [Ideal.quotientMapₐ] using
    (formallyEtale_tensorProduct_quotientMap_pow_bijective
      (R := R) (S := S) (S' := S') k)

/-- Helper for Lemma 10.150.8: tensoring the quotient comparison from Lemma `10.150.7` with `M`
and then cancelling the redundant `S'`-base change turns the `Icomap` quotient over
`S' ⊗[R] S` into the target ring-quotient tensor model over `S'`. -/
noncomputable def formally_etale_ring_quotient_tensor_base_change_equiv
    [Algebra.FormallyEtale S S'] (k : ℕ) :
    (((S' ⊗[R] S) ⧸
          (Ideal.comap
              ((Algebra.TensorProduct.map
                (AlgHom.id R S') (IsScalarTower.toAlgHom R S S')).toRingHom)
              (KaehlerDifferential.ideal R S') ^
            (k + 1))) ⊗[S] M) ≃ₗ[S']
      (((S' ⊗[R] S') ⧸ ((KaehlerDifferential.ideal R S') ^ (k + 1))) ⊗[S']
        (S' ⊗[S] M)) :=
  let tensorComparison : S' ⊗[R] S →ₐ[S'] S' ⊗[R] S' :=
    Algebra.TensorProduct.map (AlgHom.id S' S') (IsScalarTower.toAlgHom R S S')
  let Jdiag : Ideal (S' ⊗[R] S') := KaehlerDifferential.ideal R S'
  let Icomap : Ideal (S' ⊗[R] S) := Ideal.comap tensorComparison.toRingHom Jdiag
  let eqvQ :
      ((S' ⊗[R] S) ⧸ (Icomap ^ (k + 1))) ≃ₗ[S']
        ((S' ⊗[R] S') ⧸ (Jdiag ^ (k + 1))) :=
    LinearEquiv.ofBijective
      ((Ideal.quotientMapₐ (R₁ := S') (Jdiag ^ (k + 1)) tensorComparison
          (Jdiag.le_comap_pow tensorComparison.toRingHom (k + 1))).toLinearMap)
      (formally_etale_quotientMapA_linear_bijective
        (R := R) (S := S) (S' := S') k)
  -- Proof comment: first tensor the quotient comparison with `M`, then re-associate scalars from
  -- `⊗[S] M` to `⊗[S'] (S' ⊗[S] M)` by the canonical `cancelBaseChange` equivalence.
  ((TensorProduct.AlgebraTensorModule.congr eqvQ (LinearEquiv.refl S M)).trans
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange S S'
        (((S' ⊗[R] S') ⧸ (Jdiag ^ (k + 1))))
        (((S' ⊗[R] S') ⧸ (Jdiag ^ (k + 1)))) M).symm.restrictScalars S'))

set_option maxHeartbeats 400000 in
/-- Helper for Lemma 10.150.8: the formally étale quotient-tensor comparison sends the source
generator `1 ⊗ m` to the target generator `1 ⊗ (1 ⊗ m)`. -/
theorem formally_etale_ring_quotient_tensor_base_change_equiv_apply_one_tmul
    [Algebra.FormallyEtale S S'] (k : ℕ) (m : M) :
    let sourceQuot :
        Type u :=
      ((S' ⊗[R] S) ⧸
        (Ideal.comap
            ((Algebra.TensorProduct.map
              (AlgHom.id R S') (IsScalarTower.toAlgHom R S S')).toRingHom)
            (KaehlerDifferential.ideal R S') ^
          (k + 1)))
    let targetQuot :
        Type u :=
      ((S' ⊗[R] S') ⧸ ((KaehlerDifferential.ideal R S') ^ (k + 1)))
    formally_etale_ring_quotient_tensor_base_change_equiv
      (R := R) (S := S) (S' := S') (M := M) k
      ((1 : sourceQuot) ⊗ₜ[S] m) =
      ((1 : targetQuot) ⊗ₜ[S'] ((1 : S') ⊗ₜ[S] m)) := by
  let tensorComparison : S' ⊗[R] S →ₐ[S'] S' ⊗[R] S' :=
    Algebra.TensorProduct.map (AlgHom.id S' S') (IsScalarTower.toAlgHom R S S')
  let Jdiag : Ideal (S' ⊗[R] S') := KaehlerDifferential.ideal R S'
  let Icomap : Ideal (S' ⊗[R] S) := Ideal.comap tensorComparison.toRingHom Jdiag
  let eqvQ :
      ((S' ⊗[R] S) ⧸ (Icomap ^ (k + 1))) ≃ₗ[S']
        ((S' ⊗[R] S') ⧸ (Jdiag ^ (k + 1))) :=
    LinearEquiv.ofBijective
      ((Ideal.quotientMapₐ (R₁ := S') (Jdiag ^ (k + 1)) tensorComparison
          (Jdiag.le_comap_pow tensorComparison.toRingHom (k + 1))).toLinearMap)
      (formally_etale_quotientMapA_linear_bijective
        (R := R) (S := S) (S' := S') k)
  have heqvQ :
      eqvQ (1 : ((S' ⊗[R] S) ⧸ (Icomap ^ (k + 1)))) =
        (1 : ((S' ⊗[R] S') ⧸ (Jdiag ^ (k + 1)))) := by
    -- Proof comment: `eqvQ` is the quotient map from Lemma `10.150.7`, and quotient maps send
    -- `1` to `1`.
    change
      (Ideal.quotientMapₐ (R₁ := S') (Jdiag ^ (k + 1)) tensorComparison
          (Jdiag.le_comap_pow tensorComparison.toRingHom (k + 1)))
        (1 : ((S' ⊗[R] S) ⧸ (Icomap ^ (k + 1)))) =
      (1 : ((S' ⊗[R] S') ⧸ (Jdiag ^ (k + 1))))
    simpa using
      map_one
        (Ideal.quotientMapₐ (R₁ := S') (Jdiag ^ (k + 1)) tensorComparison
          (Jdiag.le_comap_pow tensorComparison.toRingHom (k + 1)))
  -- Proof comment: first rewrite the tensor comparison on `1 ⊗ m`, then evaluate the inverse
  -- `cancelBaseChange` equivalence on the resulting pure tensor.
  change
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange S S'
        (((S' ⊗[R] S') ⧸ (Jdiag ^ (k + 1))))
        (((S' ⊗[R] S') ⧸ (Jdiag ^ (k + 1)))) M).symm.restrictScalars S')
      ((TensorProduct.AlgebraTensorModule.congr eqvQ (LinearEquiv.refl S M))
        ((1 :
          ((S' ⊗[R] S) ⧸
            (Ideal.comap
                ((Algebra.TensorProduct.map
                  (AlgHom.id R S') (IsScalarTower.toAlgHom R S S')).toRingHom)
                (KaehlerDifferential.ideal R S') ^
              (k + 1)))) ⊗ₜ[S] m)) =
      ((1 : ((S' ⊗[R] S') ⧸ ((KaehlerDifferential.ideal R S') ^ (k + 1)))) ⊗ₜ[S']
        ((1 : S') ⊗ₜ[S] m))
  -- Compute the first comparison on the tensor generator, then apply the inverse
  -- `cancelBaseChange` formula to the resulting pure tensor.
  rw [TensorProduct.AlgebraTensorModule.congr_tmul]
  have htmul :
      (eqvQ (1 : ((S' ⊗[R] S) ⧸ (Icomap ^ (k + 1)))) ⊗ₜ[S']
          ((1 : S') ⊗ₜ[S] m)) =
        ((1 : ((S' ⊗[R] S') ⧸ ((KaehlerDifferential.ideal R S') ^ (k + 1)))) ⊗ₜ[S']
          ((1 : S') ⊗ₜ[S] m)) := by
    simpa [heqvQ]
  exact
    (TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul
      (R := S) (A := S')
      (B := ((S' ⊗[R] S') ⧸ ((KaehlerDifferential.ideal R S') ^ (k + 1))))
      (M := ((S' ⊗[R] S') ⧸ ((KaehlerDifferential.ideal R S') ^ (k + 1))))
      (N := M)
      (eqvQ (1 : ((S' ⊗[R] S) ⧸ (Icomap ^ (k + 1))))) m).trans htmul

/-- Helper for Lemma 10.150.8: composing the source ring-quotient base-change comparison with the
formally étale quotient comparison yields the middle textbook bridge from the base-changed source
quotient-ring tensor model to the target quotient-ring tensor model. -/
noncomputable def source_ring_quotient_tensor_to_target_ring_quotient_tensor_equiv
    [Algebra.FormallyEtale S S'] (k : ℕ) :
    S' ⊗[S] ((((S ⊗[R] S) ⧸ ((KaehlerDifferential.ideal R S) ^ (k + 1))) ⊗[S] M) : Type u) ≃ₗ[S']
      ((((S' ⊗[R] S') ⧸ ((KaehlerDifferential.ideal R S') ^ (k + 1))) ⊗[S']
        (S' ⊗[S] M)) : Type u) :=
  -- Proof comment: this packages the two already-verified middle identifications into one named
  -- equivalence, leaving only the source and target presentation changes outside the middle step.
  (source_ring_quotient_tensor_baseChange_equiv
    (R := R) (S := S) (S' := S') (M := M) k).trans
    (formally_etale_ring_quotient_tensor_base_change_equiv
      (R := R) (S := S) (S' := S') (M := M) k)

end RingQuotientTensorRoute

/-- Helper for Lemma 10.150.8: the quotient comparison from Lemma `10.150.7` sends the class of a
pure tensor `a ⊗ b` to the class of `a ⊗ algebraMap b`. This isolates the generator computation
that will later be tensored with `M` in the principal-parts comparison. -/
theorem formallyEtale_tensorProduct_quotientMap_pow_apply_mk_tmul
    [Algebra.FormallyEtale S S'] (k : ℕ) (a : S') (b : S) :
    let tensorComparison : S' ⊗[R] S →+* S' ⊗[R] S' :=
      (Algebra.TensorProduct.map (AlgHom.id S S') (IsScalarTower.toAlgHom R S S') :
        S' ⊗[R] S →+* S' ⊗[R] S')
    let Jdiag : Ideal (S' ⊗[R] S') := KaehlerDifferential.ideal R S'
    let Icomap : Ideal (S' ⊗[R] S) := Ideal.comap tensorComparison Jdiag
    ((Ideal.quotientMap (Jdiag ^ (k + 1)) tensorComparison
        (Jdiag.le_comap_pow tensorComparison (k + 1))) :
      (S' ⊗[R] S) ⧸ (Icomap ^ (k + 1)) →+* (S' ⊗[R] S') ⧸ (Jdiag ^ (k + 1)))
      (Ideal.Quotient.mk (Icomap ^ (k + 1)) ((a : S') ⊗ₜ[R] b)) =
        Ideal.Quotient.mk (Jdiag ^ (k + 1)) ((a : S') ⊗ₜ[R] (algebraMap S S' b)) := by
  -- Proof comment: this is the defining pure-tensor formula for the quotient map induced by the
  -- tensor-comparison ring hom from Lemma `10.150.7`.
  let tensorComparison : S' ⊗[R] S →+* S' ⊗[R] S' :=
    (Algebra.TensorProduct.map (AlgHom.id S S') (IsScalarTower.toAlgHom R S S') :
      S' ⊗[R] S →+* S' ⊗[R] S')
  let Jdiag : Ideal (S' ⊗[R] S') := KaehlerDifferential.ideal R S'
  let Icomap : Ideal (S' ⊗[R] S) := Ideal.comap tensorComparison Jdiag
  change
    (Ideal.quotientMap (Jdiag ^ (k + 1)) tensorComparison
      (Jdiag.le_comap_pow tensorComparison (k + 1)))
      (Ideal.Quotient.mk (Icomap ^ (k + 1)) ((a : S') ⊗ₜ[R] b)) =
        Ideal.Quotient.mk (Jdiag ^ (k + 1)) ((a : S') ⊗ₜ[R] (algebraMap S S' b))
  rw [Ideal.quotientMap_mk]
  simp [tensorComparison]

/-- Helper for Lemma 10.150.8: the pulled-back target diagonal ideal on `S' ⊗[R] S` that appears
in the source-faithful quotient comparison. -/
private abbrev source_iComap_ideal :
    Ideal (S' ⊗[R] S) :=
  Ideal.comap
    ((Algebra.TensorProduct.map
      (AlgHom.id R S') (IsScalarTower.toAlgHom R S S')).toRingHom)
    (KaehlerDifferential.ideal R S')

/-- Helper for Lemma 10.150.8: after passing from source principal parts to the quotient model of
Lemma `10.133.9`, forgetting the redundant scalar restriction, and then applying
`quotTensorEquivQuotSMul`, the universal differential class becomes the pure tensor
`(1 mod J^(k + 1)) ⊗ (1 ⊗ m)` in the raw source quotient-ring tensor model over `S ⊗[R] S`. -/
theorem source_principal_parts_to_raw_ring_quotient_tensor_apply_universal_differential
    (k : ℕ) (m : M) :
    let eDiag := diagonal_tensor_quotient_restrictScalars_equiv (R := R) (S := S) (M := M) k
    let eQuot :=
      ((TensorProduct.quotTensorEquivQuotSMul (S ⊗[R] M)
        ((KaehlerDifferential.ideal R S) ^ (k + 1))).symm.restrictScalars S)
    eQuot (eDiag
      ((principal_parts_module_equiv_tensor_quotient (R := R) (S := S) (M := M) k)
        (principal_parts_universal_differential (R := R) (S := S) (M := M) k m))) =
      (1 : ((S ⊗[R] S) ⧸ ((KaehlerDifferential.ideal R S) ^ (k + 1)))) ⊗ₜ[S ⊗[R] S]
        (((1 : S) ⊗ₜ[R] m) : S ⊗[R] M) := by
  -- Proof comment: first use Lemma `10.133.9` on the source universal class, then observe that
  -- `restrictScalarsEquiv` is definitional on quotient classes, so the remaining computation is
  -- exactly the pure-generator formula for `quotTensorEquivQuotSMul`.
  dsimp
  rw [principal_parts_module_equiv_tensor_quotient_universal_differential
    (R := R) (S := S) (M := M) k m]
  change
    (TensorProduct.quotTensorEquivQuotSMul (S ⊗[R] M)
      ((KaehlerDifferential.ideal R S) ^ (k + 1))).symm
        (Submodule.Quotient.mk (((1 : S) ⊗ₜ[R] m) : S ⊗[R] M)) =
      (1 : ((S ⊗[R] S) ⧸ ((KaehlerDifferential.ideal R S) ^ (k + 1)))) ⊗ₜ[S ⊗[R] S]
        (((1 : S) ⊗ₜ[R] m) : S ⊗[R] M)
  rfl

end
