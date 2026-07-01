import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial
open scoped TensorProduct

universe u v w

/- Domain-style sampling for Lemma 15.111.6:
- primary domain: invariant theory for finite group actions on a tensor-product base change
- sampled owner declarations:
  `FixedPoints.subring`,
  `FixedPoints.subalgebra`,
  `MulSemiringAction.compHom`,
  `Algebra.TensorProduct.map`
- best owner abstraction: the fixed-object owners `FixedPoints.subring` / `FixedPoints.subalgebra`,
  with the induced tensor action treated only as the bridge obtained from
  `Algebra.TensorProduct.map` and `MulSemiringAction.compHom`
- primitive data: a `G`-action on `R`, an `R^G`-algebra `A`, and the canonical base-change ring
  `A ⊗[R^G] R`
- derived API: the induced right-factor `G`-action on `A ⊗[R^G] R`, its fixed subalgebra, and the
  orbit-polynomial consequences for invariant elements

Layer triage:
- `source-facing`: the two orbit-polynomial statements for invariant elements and kernel elements
- `core/canonical`: `FixedPoints.subring`, `FixedPoints.subalgebra`, `MulSemiringAction.compHom`,
  and `Algebra.TensorProduct.map`
- `bridge/view`: the induced action on `A ⊗[R^G] R`, acting trivially on `A` and through the given
  `G`-action on `R`

The source-facing theorems should stay here, but the bridge layer should reuse the canonical tensor
and fixed-point owners instead of carrying a longer hand-rolled action API than needed.
-/

section

variable {R : Type u} {G : Type v}
variable [CommRing R] [Group G] [MulSemiringAction G R]

local notation "RFix" => FixedPoints.subring R G

-- Proof sketch: if `r ∈ R^G`, then every `g : G` fixes `r`; therefore `g • (r * x) = r * (g • x)`
-- for all `x : R`, so the action is `R^G`-linear.
/-- Fixed scalars from `R^G` commute with the given `G`-action on `R`. -/
instance fixedPointsSubring_smulCommClass :
    SMulCommClass G RFix R := sorry

end

section

variable {R : Type u} {G : Type v} {A : Type w}
variable [CommRing R] [Group G] [MulSemiringAction G R]
variable [CommRing A] [Algebra (FixedPoints.subring R G) A]

local notation "RFix" => FixedPoints.subring R G
local notation "BaseChange" => A ⊗[RFix] R

private noncomputable abbrev tensorBaseChangeRightAlgHom (g : G) :
    BaseChange →ₐ[RFix] BaseChange :=
  Algebra.TensorProduct.map (AlgHom.id RFix A) (MulSemiringAction.toAlgHom RFix R g)

private noncomputable def tensorBaseChangeRightAction :
    G →* (BaseChange →+* BaseChange) where
  toFun g := (tensorBaseChangeRightAlgHom g).toRingHom
  map_one' := by
    refine Algebra.TensorProduct.ringHom_ext ?_ ?_
    · ext a
      simp [tensorBaseChangeRightAlgHom]
    · ext r
      simp [tensorBaseChangeRightAlgHom]
  map_mul' g h := by
    refine Algebra.TensorProduct.ringHom_ext ?_ ?_
    · ext a
      simp [tensorBaseChangeRightAlgHom]
    · ext r
      simp [tensorBaseChangeRightAlgHom, mul_smul]

/-- The induced `G`-action on `A ⊗[R^G] R`, acting on the right tensor factor and trivially on
`A`. -/
noncomputable instance tensorBaseChangeRightMulSemiringAction :
    MulSemiringAction G BaseChange :=
  MulSemiringAction.compHom BaseChange
    (tensorBaseChangeRightAction : G →* (BaseChange →+* BaseChange))

@[simp]
theorem tensorBaseChangeRight_smul_tmul (g : G) (a : A) (r : R) :
    g • ((a ⊗ₜ[RFix] r : BaseChange)) = a ⊗ₜ[RFix] (g • r) := by
  change
    ((tensorBaseChangeRightAction : G →* (BaseChange →+* BaseChange)) g) (a ⊗ₜ[RFix] r) =
    a ⊗ₜ[RFix] (g • r)
  rfl

instance tensorBaseChangeRight_smulCommClass :
    SMulCommClass G RFix BaseChange where
  smul_comm g x z := by
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · simp
    · intro a r
      simp [TensorProduct.smul_tmul']
    · intro z w hz hw
      simp [hz, hw]

end

section

variable {R : Type u} {G : Type v} {A : Type w}
variable [CommRing R] [Group G] [Finite G] [MulSemiringAction G R]
variable [CommRing A] [Algebra (FixedPoints.subring R G) A]

local notation "RFix" => FixedPoints.subring R G
local notation "BaseChange" => A ⊗[RFix] R
local notation "BaseChangeFixed" => FixedPoints.subalgebra RFix BaseChange G

-- Proof sketch: choose a polynomial algebra `E` over `R^G` mapping surjectively to `A`, lift `b`
-- to an invariant element of `E ⊗[R^G] R`, apply Lemma `15.111.4` to that polynomial algebra,
-- and descend the resulting monic polynomial to `A`.
/-- Lemma 15.111.6 (1): if `b : A ⊗[R^G] R` is fixed by the induced right `G`-action, then there
exists a monic polynomial over `A` whose image in `(A ⊗[R^G] R)[T]` is `(X - C b)^|G|`. -/
theorem exists_monic_polynomial_over_baseChange_eq_X_sub_C_pow_of_fixed
    (b : BaseChangeFixed) :
    ∃ P : Polynomial A,
      P.Monic ∧
        P.map (Algebra.TensorProduct.includeLeft : A →ₐ[RFix] BaseChange) =
          (X - C (b : BaseChange)) ^ Nat.card G := sorry

-- Proof sketch: apply the first clause to the image of `a` in `A ⊗[R^G] R`; because `a` lies in
-- the kernel of `A → A ⊗[R^G] R`, its image is zero, so the translated polynomial identity
-- reduces to `(X - C a)^|G| = X^|G|` in `A[T]`.
/-- Lemma 15.111.6 (2): if `a` maps to zero under the canonical base-change map
`A → A ⊗[R^G] R`, then `(X - C a)^|G| = X^|G|` in `A[T]`. -/
theorem kernelElement_X_sub_pow_eq_X_pow_of_baseChange
    (a : RingHom.ker (Algebra.TensorProduct.includeLeft : A →ₐ[RFix] BaseChange)) :
    ((X - C a.1) ^ Nat.card G : Polynomial A) = X ^ Nat.card G := sorry

end
