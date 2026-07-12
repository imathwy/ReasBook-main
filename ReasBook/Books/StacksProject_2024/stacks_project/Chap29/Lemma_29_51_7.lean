import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

/- Semantic recall: `lean_leansearch` surfaced the canonical owners `IsDominant`,
`Scheme.functionField`, `LocallyOfFiniteType`, and `IsFinite`. Local Chapter 29 precedent uses
`Algebra.trdeg Y.functionField X.functionField` and `FiniteDimensional Y.functionField
X.functionField` for the induced function-field extension once its algebra structure is in scope,
and uses `f.resLE V U hUV` / `f ∣_ V` for finite restrictions to opens. The source tag evidence
is consistent for tag `02NX`. -/

/-- Lemma 29.51.7 (1): for a dominant locally finite type morphism of integral schemes, the
function-field extension having transcendence degree `0`, being finite, finite restriction over
some nonempty affine opens, and having singleton fiber over the generic point are equivalent. -/
@[stacks 02NX]
theorem tfae_functionFieldTrdeg_eq_zero_finite_exists_finite_affineOpen_genericFiber_singleton
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    [LocallyOfFiniteType f] [IsDominant f]
    [Algebra Y.functionField X.functionField] :
    List.TFAE
      [ Algebra.trdeg Y.functionField X.functionField = 0
      , FiniteDimensional Y.functionField X.functionField
      , ∃ (U : X.Opens) (_ : Nonempty U) (V : Y.Opens) (_ : Nonempty V)
            (_ : IsAffineOpen U) (_ : IsAffineOpen V) (hUV : U ≤ f ⁻¹ᵁ V),
          IsFinite (f.resLE V U hUV)
      , f.base ⁻¹' ({genericPoint Y} : Set Y) = ({genericPoint X} : Set X)
      ] := sorry

/-- Lemma 29.51.7 (2): if the same morphism is separated or quasi-compact, the preceding
equivalent conditions are also equivalent to finiteness over the preimage of some nonempty affine
open of the target. -/
@[stacks 02NX]
theorem tfae_functionFieldTrdeg_eq_zero_finite_exists_finite_affineOpen_genericFiber_singleton_exists_finite_preimage
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    [LocallyOfFiniteType f] [IsDominant f]
    [Algebra Y.functionField X.functionField]
    (hqc_or_sep : QuasiCompact f ∨ IsSeparated f) :
    List.TFAE
      [ Algebra.trdeg Y.functionField X.functionField = 0
      , FiniteDimensional Y.functionField X.functionField
      , ∃ (U : X.Opens) (_ : Nonempty U) (V : Y.Opens) (_ : Nonempty V)
            (_ : IsAffineOpen U) (_ : IsAffineOpen V) (hUV : U ≤ f ⁻¹ᵁ V),
          IsFinite (f.resLE V U hUV)
      , f.base ⁻¹' ({genericPoint Y} : Set Y) = ({genericPoint X} : Set X)
      , ∃ (V : Y.Opens) (_ : Nonempty V) (_ : IsAffineOpen V), IsFinite (f ∣_ V)
      ] := sorry

end Scheme.Hom
end AlgebraicGeometry
