import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct

universe u v w

section

variable {k : Type u} {R : Type v} {S : Type w}
variable [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]

/-- A pair of finitely generated `k`-subalgebras of `R` and `S`. -/
structure FGSubalgebraPair where
  left : Subalgebra k R
  right : Subalgebra k S
  left_fg : left.FG
  right_fg : right.FG

/-- A witness that a ring contains two nonzero elements whose product is zero. -/
structure NonzeroZeroDivisorWitness (A : Type*) [Mul A] [Zero A] where
  left : A
  right : A
  left_ne_zero : left ≠ 0
  right_ne_zero : right ≠ 0
  mul_eq_zero : left * right = 0

/-- A witness that a ring contains an idempotent different from `0` and `1`. -/
structure NontrivialIdempotentWitness (A : Type*) [Mul A] [One A] [Zero A] where
  elem : A
  isIdempotent : IsIdempotentElem elem
  ne_zero : elem ≠ 0
  ne_one : elem ≠ 1

/-
Domain triage:
- `source-facing`: the three public statements detect nonreducedness, zerodivisors, and nontrivial
  idempotents in `R ⊗[k] S` on finitely generated `k`-subalgebras on both sides.
- `core/canonical`: one-sided finite descent in tensor products is already owned by
  `exists_fg_and_mem_baseChange`, and reducedness over a field is detected from finitely generated
  subalgebras by `IsReduced.tensorProduct_of_flat_of_forall_fg`.
- `bridge/view`: for parts `(2)` and `(3)`, the finite-family bookkeeping is derived by iterating
  `exists_fg_and_mem_baseChange` and commuting tensor factors, rather than by introducing a
  parallel local helper abstraction.

Primitive data are only the two `k`-algebras and the witness tensor elements. No extra wrapper
carrying finite-stage data is mathematically primary here.
-/

/-- Helper for Lemma 10.43.4: the comparison map from a finitely generated tensor stage into
`R ⊗[k] S` is injective. -/
lemma tensorProduct_map_injective_of_fgSubalgebraPair
    (T : @FGSubalgebraPair k R S _ _ _ _ _) :
    Function.Injective (Algebra.TensorProduct.map T.left.val T.right.val) := by
  -- Over a field, tensoring the two inclusion maps preserves injectivity.
  simpa using TensorProduct.map_injective_of_flat_flat
    T.left.val.toLinearMap T.right.val.toLinearMap
    Subtype.val_injective Subtype.val_injective

/-- Helper for Lemma 10.43.4: every element of `R ⊗[k] S` already comes from the tensor product of
finitely generated `k`-subalgebras on both sides. -/
lemma exists_fg_subalgebras_tensorProduct_lift (x : R ⊗[k] S) :
    ∃ T : @FGSubalgebraPair k R S _ _ _ _ _,
      ∃ x' : T.left ⊗[k] T.right,
        Algebra.TensorProduct.map T.left.val T.right.val x' = x := by
  -- First descend the tensor to finitely many coefficients on the `S`-side.
  obtain ⟨B, hBfg, hxB⟩ := exists_fg_and_mem_baseChange (R := k) (A := R) (B := S) x
  obtain ⟨u, hu⟩ := hxB
  -- Then commute the tensor and descend the remaining coefficients on the `R`-side.
  obtain ⟨A, hAfg, huA⟩ := exists_fg_and_mem_baseChange
    (R := k) (A := B) (B := R) (Algebra.TensorProduct.comm k R B u)
  obtain ⟨v, hv⟩ := huA
  have hu' : Algebra.TensorProduct.map (AlgHom.id k R) B.val u = x := hu
  have hv' : Algebra.TensorProduct.map (AlgHom.id k B) A.val v =
      Algebra.TensorProduct.comm k R B u := hv
  refine ⟨{
    left := A
    right := B
    left_fg := hAfg
    right_fg := hBfg
  }, Algebra.TensorProduct.comm k B A v, ?_⟩
  change Algebra.TensorProduct.map A.val B.val (Algebra.TensorProduct.comm k B A v) = x
  -- Compare after commuting: both one-sided lifts now line up with the same tensor.
  apply (Algebra.TensorProduct.comm k R S).injective
  calc
    Algebra.TensorProduct.comm k R S
        (Algebra.TensorProduct.map A.val B.val (Algebra.TensorProduct.comm k B A v))
      = Algebra.TensorProduct.map B.val A.val
          (Algebra.TensorProduct.comm k A B (Algebra.TensorProduct.comm k B A v)) := by
          simpa using
            (Algebra.TensorProduct.comm_comp_map_apply
              (f := A.val)
              (g := B.val)
              (Algebra.TensorProduct.comm k B A v))
    _ = Algebra.TensorProduct.map B.val A.val v := by
          have hcomm : Algebra.TensorProduct.comm k A B
              (Algebra.TensorProduct.comm k B A v) = v := by
            change Algebra.TensorProduct.comm k A B
                ((Algebra.TensorProduct.comm k A B).symm v) = v
            exact AlgEquiv.apply_symm_apply (Algebra.TensorProduct.comm k A B) v
          rw [hcomm]
    _ = Algebra.TensorProduct.comm k R S x := by
          calc
            Algebra.TensorProduct.map B.val A.val v
              = ((Algebra.TensorProduct.map B.val (AlgHom.id k R)).comp
                  (Algebra.TensorProduct.map (AlgHom.id k B) A.val)) v := by
                  simpa using congrArg (fun f => f v)
                    (Algebra.TensorProduct.map_comp
                      (f₂ := B.val)
                      (f₁ := AlgHom.id k B)
                      (g₂ := AlgHom.id k R)
                      (g₁ := A.val))
            _ = Algebra.TensorProduct.map B.val (AlgHom.id k R)
                  (Algebra.TensorProduct.map (AlgHom.id k B) A.val v) := rfl
            _ = Algebra.TensorProduct.map B.val (AlgHom.id k R)
                  (Algebra.TensorProduct.comm k R B u) := by rw [hv']
            _ = Algebra.TensorProduct.comm k R S
                  (Algebra.TensorProduct.map (AlgHom.id k R) B.val u) := by
                  symm
                  simpa using
                    (Algebra.TensorProduct.comm_comp_map_apply
                      (f := AlgHom.id k R) (g := B.val) u)
            _ = Algebra.TensorProduct.comm k R S x := by rw [hu']

/-- Helper for Lemma 10.43.4: two tensor elements can be realized inside one common finitely
generated tensor stage. -/
lemma exists_fg_subalgebras_tensorProduct_lift_pair (x y : R ⊗[k] S) :
    ∃ T : @FGSubalgebraPair k R S _ _ _ _ _,
      ∃ x' y' : T.left ⊗[k] T.right,
        Algebra.TensorProduct.map T.left.val T.right.val x' = x ∧
          Algebra.TensorProduct.map T.left.val T.right.val y' = y := by
  -- Lift each tensor separately, then enlarge by the sup of the two finitely generated stages.
  obtain ⟨Tx, x', hx⟩ := exists_fg_subalgebras_tensorProduct_lift (k := k) (R := R) (S := S) x
  obtain ⟨Ty, y', hy⟩ := exists_fg_subalgebras_tensorProduct_lift (k := k) (R := R) (S := S) y
  let T : FGSubalgebraPair := {
    left := Tx.left ⊔ Ty.left
    right := Tx.right ⊔ Ty.right
    left_fg := Subalgebra.FG.sup Tx.left_fg Ty.left_fg
    right_fg := Subalgebra.FG.sup Tx.right_fg Ty.right_fg
  }
  let x'' : T.left ⊗[k] T.right := Algebra.TensorProduct.map
    (Subalgebra.inclusion (show Tx.left ≤ T.left from le_sup_left))
    (Subalgebra.inclusion (show Tx.right ≤ T.right from le_sup_left)) x'
  let y'' : T.left ⊗[k] T.right := Algebra.TensorProduct.map
    (Subalgebra.inclusion (show Ty.left ≤ T.left from le_sup_right))
    (Subalgebra.inclusion (show Ty.right ≤ T.right from le_sup_right)) y'
  refine ⟨T, x'', y'', ?_, ?_⟩
  · -- The enlarged left/right stages still map `x''` to the original tensor `x`.
    calc
      Algebra.TensorProduct.map T.left.val T.right.val x''
        = Algebra.TensorProduct.map Tx.left.val Tx.right.val x' := by
            simpa [T, x''] using congrArg (fun f => f x')
              (Algebra.TensorProduct.map_comp
                (f₂ := T.left.val)
                (f₁ := Subalgebra.inclusion (show Tx.left ≤ T.left from le_sup_left))
                (g₂ := T.right.val)
                (g₁ := Subalgebra.inclusion (show Tx.right ≤ T.right from le_sup_left))).symm
      _ = x := hx
  · -- The same sup-enlargement carries `y''` to `y`.
    calc
      Algebra.TensorProduct.map T.left.val T.right.val y''
        = Algebra.TensorProduct.map Ty.left.val Ty.right.val y' := by
            simpa [T, y''] using congrArg (fun f => f y')
              (Algebra.TensorProduct.map_comp
                (f₂ := T.left.val)
                (f₁ := Subalgebra.inclusion (show Ty.left ≤ T.left from le_sup_right))
                (g₂ := T.right.val)
                (g₁ := Subalgebra.inclusion (show Ty.right ≤ T.right from le_sup_right))).symm
      _ = y := hy

-- Proof sketch: use the contrapositive of
-- `IsReduced.tensorProduct_of_flat_of_forall_fg` twice, first in the `S`-variable and then in the
-- `R`-variable. Over a field, all modules are flat, so the nonreduced nilpotent element already
-- lives in the tensor product of finitely generated subalgebras on both sides.
/-- Lemma 10.43.4 (1): if `R ⊗[k] S` is not reduced, then there exist finitely generated
`k`-subalgebras `R' ⊆ R` and `S' ⊆ S` such that `R' ⊗[k] S'` is not reduced. -/
theorem exists_fg_subalgebras_not_isReduced_tensorProduct
    (h : ¬ IsReduced (R ⊗[k] S)) :
    ∃ T : @FGSubalgebraPair k R S _ _ _ _ _,
      ¬ IsReduced (T.left ⊗[k] T.right) := by
  -- Choose a nonzero nilpotent witness for nonreducedness in the ambient tensor product.
  obtain ⟨z, hz_ne_zero, hz_nilpotent⟩ := exists_isNilpotent_of_not_isReduced h
  -- Lift that witness to a finitely generated tensor stage on both sides.
  obtain ⟨T, z', hz_map⟩ := exists_fg_subalgebras_tensorProduct_lift (k := k) (R := R) (S := S) z
  have h_inj := tensorProduct_map_injective_of_fgSubalgebraPair (k := k) (R := R) (S := S) T
  have hz'_nilpotent : IsNilpotent z' := by
    rw [← IsNilpotent.map_iff h_inj, hz_map]
    exact hz_nilpotent
  have hz'_ne_zero : z' ≠ 0 := by
    intro hz'_eq_zero
    apply hz_ne_zero
    simpa [hz'_eq_zero] using hz_map.symm
  refine ⟨T, ?_⟩
  -- The descended nilpotent stays nonzero, so the smaller tensor product is not reduced.
  intro hReduced
  exact hz'_ne_zero (hReduced.eq_zero z' hz'_nilpotent)

-- Proof sketch: apply `exists_fg_and_mem_baseChange` to `z`, then after commuting tensor factors
-- apply it again to the resulting coefficients needed for `w`, obtaining a common finitely
-- generated stage on both sides. The equalities `z ≠ 0`, `w ≠ 0`, and `z * w = 0` then descend
-- along the induced map from the smaller tensor product.
/-- Lemma 10.43.4 (2): if `R ⊗[k] S` contains a nonzero zerodivisor, then it already appears in
the tensor product of finitely generated `k`-subalgebras on both sides. -/
theorem exists_fg_subalgebras_tensorProduct_has_nonzero_zerodivisor
    (h : Nonempty (NonzeroZeroDivisorWitness (R ⊗[k] S))) :
    ∃ T : @FGSubalgebraPair k R S _ _ _ _ _,
      Nonempty (NonzeroZeroDivisorWitness (T.left ⊗[k] T.right)) := by
  -- Start from a zerodivisor witness and descend both elements to one common finite stage.
  obtain ⟨w⟩ := h
  obtain ⟨T, z', w', hz_map, hw_map⟩ := exists_fg_subalgebras_tensorProduct_lift_pair
    (k := k) (R := R) (S := S) w.left w.right
  have h_inj := tensorProduct_map_injective_of_fgSubalgebraPair (k := k) (R := R) (S := S) T
  have hz'_ne_zero : z' ≠ 0 := by
    intro hz'_eq_zero
    apply w.left_ne_zero
    simpa [hz'_eq_zero] using hz_map.symm
  have hw'_ne_zero : w' ≠ 0 := by
    intro hw'_eq_zero
    apply w.right_ne_zero
    simpa [hw'_eq_zero] using hw_map.symm
  have hmul_eq_zero : z' * w' = 0 := by
    apply h_inj
    simpa [map_mul, hz_map, hw_map] using w.mul_eq_zero
  refine ⟨T, ?_⟩
  -- Injectivity transports the zerodivisor equations and nonvanishing to the smaller stage.
  exact ⟨{
    left := z'
    right := w'
    left_ne_zero := hz'_ne_zero
    right_ne_zero := hw'_ne_zero
    mul_eq_zero := hmul_eq_zero
  }⟩

-- Proof sketch: iterate `exists_fg_and_mem_baseChange` to place the idempotent `e` in a common
-- finitely generated tensor stage, then transport the equations `e * e = e`, `e ≠ 0`, and
-- `e ≠ 1` along the comparison map.
/-- Lemma 10.43.4 (3): if `R ⊗[k] S` contains a nontrivial idempotent, then it already appears in
finitely generated `k`-subalgebras on both sides. -/
theorem exists_fg_subalgebras_tensorProduct_has_nontrivial_idempotent
    (h : Nonempty (NontrivialIdempotentWitness (R ⊗[k] S))) :
    ∃ T : @FGSubalgebraPair k R S _ _ _ _ _,
      Nonempty (NontrivialIdempotentWitness (T.left ⊗[k] T.right)) := by
  -- Lift the idempotent itself to a finitely generated tensor stage.
  obtain ⟨w⟩ := h
  obtain ⟨T, e', he_map⟩ := exists_fg_subalgebras_tensorProduct_lift
    (k := k) (R := R) (S := S) w.elem
  have h_inj := tensorProduct_map_injective_of_fgSubalgebraPair (k := k) (R := R) (S := S) T
  have he'_idempotent : IsIdempotentElem e' := by
    apply h_inj
    simpa [map_mul, he_map] using w.isIdempotent.eq
  have he'_ne_zero : e' ≠ 0 := by
    intro he'_eq_zero
    apply w.ne_zero
    simpa [he'_eq_zero] using he_map.symm
  have he'_ne_one : e' ≠ 1 := by
    intro he'_eq_one
    apply w.ne_one
    simpa [he'_eq_one] using he_map.symm
  refine ⟨T, ?_⟩
  -- Injectivity also transports the inequalities against `0` and `1`.
  exact ⟨{
    elem := e'
    isIdempotent := he'_idempotent
    ne_zero := he'_ne_zero
    ne_one := he'_ne_one
  }⟩

end
