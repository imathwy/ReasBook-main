import StacksProject_2024.stacks_project.Chap29.Definition_29_49_4

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` surfaced the integral owner `Scheme.functionField`, and
-- local mathlib source confirmed `isField_stalk_of_closure_mem_irreducibleComponents` for reduced
-- schemes. Since mathlib does not currently expose a non-integral scheme owner for `R(X)`, this
-- file records the finite-component source through the canonical product indexed by
-- `genericPoints X`.

/- Lemma 29.49.5 (1): this is the source-facing restatement of
`Scheme.rationalFunctionRing_def`; the owner `X.rationalFunctionRing` was introduced in
Definition 29.49.4. -/
#check AlgebraicGeometry.Scheme.rationalFunctionRing_def

/-- Lemma 29.49.5 (2): if `X` is reduced, then the product of the generic-point local rings is
canonically identified with the product of the corresponding residue fields. -/
noncomputable def rationalFunctionRingToPiResidueField
    (X : Scheme.{u}) [IsReduced X] :
    X.rationalFunctionRing →+* ∀ η : genericPoints X, X.residueField η.1 where
  toFun g := fun η ↦ X.residue η.1 (g η)
  map_one' := by
    ext η
    rfl
  map_mul' _ _ := by
    ext η
    rfl
  map_zero' := by
    ext η
    rfl
  map_add' _ _ := by
    ext η
    rfl

@[simp] theorem rationalFunctionRingToPiResidueField_apply
    (X : Scheme.{u}) [IsReduced X] (g : X.rationalFunctionRing) (η : genericPoints X) :
    X.rationalFunctionRingToPiResidueField g η = X.residue η.1 (g η) :=
  rfl

/-- The canonical comparison from `R(X)` to the product of the residue fields at the generic
points is bijective. -/
theorem rationalFunctionRingToPiResidueField_bijective
    (X : Scheme.{u}) [IsReduced X] :
    Function.Bijective
      (X.rationalFunctionRingToPiResidueField :
        X.rationalFunctionRing → ∀ η : genericPoints X, X.residueField η.1) := sorry

/-- Companion recall: when `X` is integral, the ring of rational functions agrees with the
canonical function field. -/
#check AlgebraicGeometry.Scheme.rationalFunctionRing_equiv_functionField

/-- Lemma 29.49.5 (3): if `X` is integral with generic point `η`, then the ring of rational
functions maps canonically to `κ(η)` via the function field `𝒪_{X, η}`. -/
noncomputable def rationalFunctionRingToResidueField_genericPoint
    (X : Scheme.{u}) [IsIntegral X] :
    X.rationalFunctionRing →+* X.residueField (genericPoint X) :=
  (X.residue (genericPoint X)).comp
    (X.rationalFunctionRing_equiv_functionField : X.rationalFunctionRing →+* X.functionField)

@[simp] theorem rationalFunctionRingToResidueField_genericPoint_apply
    (X : Scheme.{u}) [IsIntegral X] (f : X.rationalFunctionRing) :
    X.rationalFunctionRingToResidueField_genericPoint f =
      X.residue (genericPoint X) (X.rationalFunctionRing_equiv_functionField f) :=
  rfl

/-- In the integral case, the canonical map from `R(X)` to the residue field at the generic point
is bijective. -/
theorem rationalFunctionRingToResidueField_genericPoint_bijective
    (X : Scheme.{u}) [IsIntegral X] :
    Function.Bijective
      (X.rationalFunctionRingToResidueField_genericPoint :
        X.rationalFunctionRing → X.residueField (genericPoint X)) :=
  sorry

end AlgebraicGeometry.Scheme
