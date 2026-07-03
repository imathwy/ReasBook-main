import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_1_2_1 (from Chap01) -/
universe u

variable {X : Type u} [TopologicalSpace X] {x y : X}

/- Definition 1.2.1: Two paths from `x` to `y` are equivalent when they are homotopic through
paths from `x` to `y`, so the endpoints remain fixed throughout the homotopy. -/
recall Path.Homotopic (f g : Path x y) : Prop

/-! ### Definition_1_2_2 (from Chap01) -/
universe u

variable {X : Type u} [TopologicalSpace X] {x : X}

/- Definition 1.2.2: a loop at `x` is a path from `x` to itself, namely an element of `Path x x`. -/
#check (Path x x)

/- The set `π₁(X, x)` is the quotient `Path.Homotopic.Quotient x x` of loops at `x` by
endpoint-fixed homotopy. -/
#check (Path.Homotopic.Quotient x x)

/-! ### Definition_1_2_3 (from Chap01) -/
universe u

variable {X : Type u} [TopologicalSpace X] {x y z : X}

/- Definition 1.2.3: for paths `f : Path x y` and `g : Path y z`, the composite
`Path.trans f g` traverses `f` on the first half of `I` and `g` on the second half, each at
double speed. -/
recall Path.trans (f : Path x y) (g : Path y z) : Path x z

/-! ### Definition_1_2_4 (from Chap01) -/
universe u

variable {X : Type u} [TopologicalSpace X] {x y : X}

/- Definition 1.2.4: the reverse of a path `f : Path x y` is `Path.symm f`, corresponding to
the parametrization `s ↦ f (1 - s)`, and the constant loop at `x` is `Path.refl x`. -/
recall Path.symm (f : Path x y) : Path y x

/- The constant loop at a point is the constant path `Path.refl x`. -/
recall Path.refl (x : X) : Path x x

/-! ### Lemma_1_2_5 (from Chap01) -/
universe u

open Path.Homotopic.Quotient

variable {X : Type u} [TopologicalSpace X] {x y z : X}

/- Lemma 1.2.5: path composition is well defined on endpoint-fixed homotopy classes. For
`f : Path x y` and `g : Path y z`, the class of the concatenated path `f.trans g` depends only on
the classes of `f` and `g`, so `[g][f] = [g · f]`. -/
recall mk_trans (f : Path x y) (g : Path y z) :
  mk (f.trans g) = (mk f).trans (mk g)

/-! ### Lemma_1_2_6 (from Chap01) -/
universe u

open Path.Homotopic.Quotient

variable {X : Type u} [TopologicalSpace X] {w x y z : X}

/- Lemma 1.2.6: composition of path classes is associative; for endpoint-fixed homotopy classes
represented by composable paths `f`, `g`, and `h`, the classes of `h · (g · f)` and
`(h · g) · f` coincide. -/
recall trans_assoc (f : Path.Homotopic.Quotient w x) (g : Path.Homotopic.Quotient x y)
    (h : Path.Homotopic.Quotient y z) :
    trans (trans f g) h = trans f (trans g h)

/-! ### Lemma_1_2_7 (from Chap01) -/
universe u

open Path.Homotopic.Quotient

variable {X : Type u} [TopologicalSpace X] {x y : X}

/- Lemma 1.2.7 (1): constant paths are right units up to endpoint-fixed homotopy, so for a path
`f : Path x y`, the class of `f.trans (Path.refl y)` equals the class of `f`. -/
recall trans_refl (γ : Path.Homotopic.Quotient x y) :
  trans γ (refl y) = γ

/- Lemma 1.2.7 (2): constant paths are left units up to endpoint-fixed homotopy, so for a path
`f : Path x y`, the class of `(Path.refl x).trans f` equals the class of `f`. -/
recall refl_trans (γ : Path.Homotopic.Quotient x y) :
  trans (refl x) γ = γ

/-! ### Lemma_1_2_8 (from Chap01) -/
universe u

open Path.Homotopic.Quotient

variable {X : Type u} [TopologicalSpace X] {x y : X}

/- Lemma 1.2.8 (1): a path class followed by its reverse is endpoint-fixed homotopic to the
constant path at the starting point, so for `γ : Path.Homotopic.Quotient x y`,
`γ.trans γ.symm = refl x`. -/
recall trans_symm (γ : Path.Homotopic.Quotient x y) :
  γ.trans γ.symm = refl x

/- Lemma 1.2.8 (2): the reverse of a path class followed by the original path class is
endpoint-fixed homotopic to the constant path at the endpoint, so for
`γ : Path.Homotopic.Quotient x y`, `γ.symm.trans γ = refl y`. -/
recall symm_trans (γ : Path.Homotopic.Quotient x y) :
  γ.symm.trans γ = refl y

/-! ### Theorem_1_2_9 (from Chap01) -/
universe u

open Path.Homotopic.Quotient

noncomputable section

variable {X : Type u} [TopologicalSpace X] {x : X}

/-- Theorem 1.2.9: `π₁(X, x) = Path.Homotopic.Quotient x x` carries the group structure induced by
path composition, with unit the constant loop class and inverse given by path reversal. -/
instance loop_homotopy_group (x : X) : Group (Path.Homotopic.Quotient x x) := by
  change Group (FundamentalGroup X x)
  infer_instance

/-- Group multiplication on loop classes is induced by path composition. -/
theorem loop_homotopy_mul_eq_trans (γ δ : Path.Homotopic.Quotient x x) :
    γ * δ = δ.trans γ := rfl

/-- The identity element in the loop-class group is the constant loop class. -/
theorem loop_homotopy_one_eq_refl :
    (1 : Path.Homotopic.Quotient x x) = refl x := rfl

/-- Inversion in the loop-class group is induced by reversing paths. -/
theorem loop_homotopy_inv_eq_symm (γ : Path.Homotopic.Quotient x x) :
    γ⁻¹ = γ.symm := rfl

/-! ### Remark_1_2_10 (from Chap01) -/
universe u

open scoped Topology

variable {X : Type u} [TopologicalSpace X] (x : X)

/- Remark 1.2.10: later homotopy groups are organized into the family `π_ n X x`; the
fundamental group is the first member of this family, so `π_ 1 X x` is canonically identified
with `FundamentalGroup X x`. -/
recall HomotopyGroup.pi1EquivFundamentalGroup : π_ 1 X x ≃ FundamentalGroup X x
