import Mathlib
import StacksProject_2024.stacks_project.Chap29.Definition_29_21_1
import StacksProject_2024.stacks_project.Chap29.Definition_29_25_1
import StacksProject_2024.stacks_project.Chap31.Definition_31_18_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the mathlib owners
-- `LocallyOfFinitePresentation` and `Flat`; local Chapter 26 and Chapter 31 precedent fixes
-- fibers as `Scheme.Hom.fiber f s`, closed subscheme restriction as `IdealSheafData.comap`,
-- and relative effective Cartier divisors as `IsRelativeEffectiveCartierDivisor f D`.

/-- Lemma 31.18.9 (1): let `f : X ⟶ S` be flat and locally of finite presentation, let
`Z ⊆ X` be a closed subscheme, and let `x ∈ Z`. If the fibre `Z_s ⊆ X_s` over
`s = f(x)` is an effective Cartier divisor in a neighbourhood of `x`, then after replacing `X`
by an open neighbourhood `U` of `x` there is a relative effective Cartier divisor `D ⊆ U`
containing `Z ∩ U` whose fibre over `s` is exactly `(Z ∩ U)_s`. -/
@[stacks 062Y]
theorem exists_open_relativeEffectiveCartierDivisor_le_fiber_eq_of_fiber_isEffectiveCartier_near
    {X S : Scheme.{u}} (f : X ⟶ S) (Z : X.IdealSheafData) (x : Z.subscheme)
    [Flat f] [LocallyOfFinitePresentation f]
    (hfiber :
      ∃ W : (Scheme.Hom.fiber f (f (Z.subschemeι x))).Opens,
        Scheme.Hom.asFiber f (Z.subschemeι x) ∈
            (W : Set (Scheme.Hom.fiber f (f (Z.subschemeι x)))) ∧
          IsEffectiveCartierDivisor
            ((Z.comap (Scheme.Hom.fiberι f (f (Z.subschemeι x)))).comap W.ι)) :
    ∃ U : X.Opens,
      ∃ _ : Z.subschemeι x ∈ (U : Set X),
        ∃ D : U.toScheme.IdealSheafData,
          ∃ _ : IsRelativeEffectiveCartierDivisor (U.ι ≫ f) D,
            ∃ _ : Z.comap U.ι ≤ D,
              (Z.comap U.ι).comap
                  (Scheme.Hom.fiberι (U.ι ≫ f) (f (Z.subschemeι x))) =
                D.comap (Scheme.Hom.fiberι (U.ι ≫ f) (f (Z.subschemeι x))) := sorry

/-- Lemma 31.18.9 (2): under the hypotheses of part (1), if in addition the closed immersion
`Z ⟶ X` is of finite presentation and the structural morphism `Z ⟶ S` is flat at `x`, then the
open neighbourhood and relative effective Cartier divisor may be chosen so that `Z ∩ U = D`. -/
@[stacks 062Y]
theorem exists_open_relativeEffectiveCartierDivisor_eq_of_finitePresentation_flatAt
    {X S : Scheme.{u}} (f : X ⟶ S) (Z : X.IdealSheafData) (x : Z.subscheme)
    [Flat f] [LocallyOfFinitePresentation f]
    [Scheme.Hom.FinitePresentation Z.subschemeι]
    (hZflat : Scheme.Hom.flatAt (Z.subschemeι ≫ f) x)
    (hfiber :
      ∃ W : (Scheme.Hom.fiber f (f (Z.subschemeι x))).Opens,
        Scheme.Hom.asFiber f (Z.subschemeι x) ∈
            (W : Set (Scheme.Hom.fiber f (f (Z.subschemeι x)))) ∧
          IsEffectiveCartierDivisor
            ((Z.comap (Scheme.Hom.fiberι f (f (Z.subschemeι x)))).comap W.ι)) :
    ∃ U : X.Opens,
      ∃ _ : Z.subschemeι x ∈ (U : Set X),
        ∃ D : U.toScheme.IdealSheafData,
          ∃ _ : IsRelativeEffectiveCartierDivisor (U.ι ≫ f) D,
            Z.comap U.ι = D := sorry

/-- Lemma 31.18.9 (3): under the hypotheses of part (1), if `Z` is locally principal near `x`,
then the open neighbourhood and relative effective Cartier divisor may be chosen so that
`Z ∩ U = D`. The local-principal hypothesis is stated by a single affine neighbourhood of `x`
on which the ideal of `Z` is principal. -/
@[stacks 062Y]
theorem exists_open_relativeEffectiveCartierDivisor_eq_of_locallyPrincipal_near
    {X S : Scheme.{u}} (f : X ⟶ S) (Z : X.IdealSheafData) (x : Z.subscheme)
    [Flat f] [LocallyOfFinitePresentation f]
    (hprincipal :
      ∃ V : X.affineOpens,
        ∃ _ : Z.subschemeι x ∈ (V : Set X),
          ∃ g : Γ(X, V), Z.ideal V = Ideal.span ({g} : Set (Γ(X, V))))
    (hfiber :
      ∃ W : (Scheme.Hom.fiber f (f (Z.subschemeι x))).Opens,
        Scheme.Hom.asFiber f (Z.subschemeι x) ∈
            (W : Set (Scheme.Hom.fiber f (f (Z.subschemeι x)))) ∧
          IsEffectiveCartierDivisor
            ((Z.comap (Scheme.Hom.fiberι f (f (Z.subschemeι x)))).comap W.ι)) :
    ∃ U : X.Opens,
      ∃ _ : Z.subschemeι x ∈ (U : Set X),
        ∃ D : U.toScheme.IdealSheafData,
          ∃ _ : IsRelativeEffectiveCartierDivisor (U.ι ≫ f) D,
            Z.comap U.ι = D := sorry

/-- Lemma 31.18.9 (4): if `Z ⟶ S` is locally of finite presentation and flat, and every fibre
`Z_s ⊆ X_s` is an effective Cartier divisor, then `Z` is a relative effective Cartier divisor on
`X/S`. -/
@[stacks 062Y]
theorem isRelativeEffectiveCartierDivisor_of_flat_locallyOfFinitePresentation_fibers
    {X S : Scheme.{u}} (f : X ⟶ S) (Z : X.IdealSheafData)
    [Flat f] [LocallyOfFinitePresentation f]
    [LocallyOfFinitePresentation (Z.subschemeι ≫ f)] [Flat (Z.subschemeι ≫ f)]
    (hfibers : ∀ s : S, IsEffectiveCartierDivisor (Z.comap (Scheme.Hom.fiberι f s))) :
    IsRelativeEffectiveCartierDivisor f Z := sorry

/-- Lemma 31.18.9 (5): if `Z` is locally principal on `X` and every fibre `Z_s ⊆ X_s` is an
effective Cartier divisor, then `Z` is a relative effective Cartier divisor on `X/S`. -/
@[stacks 062Y]
theorem isRelativeEffectiveCartierDivisor_of_locallyPrincipal_fibers
    {X S : Scheme.{u}} (f : X ⟶ S) (Z : X.IdealSheafData)
    [Flat f] [LocallyOfFinitePresentation f]
    (hprincipal :
      ∀ x : X, x ∈ Z.support →
        ∃ V : X.affineOpens,
          x ∈ (V : Set X) ∧
            ∃ g : Γ(X, V), Z.ideal V = Ideal.span ({g} : Set (Γ(X, V))))
    (hfibers : ∀ s : S, IsEffectiveCartierDivisor (Z.comap (Scheme.Hom.fiberι f s))) :
    IsRelativeEffectiveCartierDivisor f Z := sorry

end AlgebraicGeometry
