import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import StacksProject_2024.stacks_project.Chap29.Definition_29_21_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-morphism owners
-- `LocallyOfFiniteType`, `LocallyOfFinitePresentation`, and `IsImmersion`. The Stacks source
-- tag evidence is consistent with tag `01ZE`.

/-- A proof-only property for a factorization through a scheme of finite presentation by an
immersion. -/
@[stacks 01ZE]
class FinitePresentationImmersionFactorization
    {X S X' : Scheme.{u}} (f : X ⟶ S) (i : X ⟶ X') (f' : X' ⟶ S) : Prop extends
    Scheme.Hom.FinitePresentation f', IsImmersion i where
  /-- The factorization composes to the original morphism. -/
  fac : i ≫ f' = f

/-- Finite-presentation immersion factorization structures are proposition-valued. -/
instance instSubsingletonFinitePresentationImmersionFactorization
    {X S X' : Scheme.{u}} {f : X ⟶ S} {i : X ⟶ X'} {f' : X' ⟶ S}
    : Subsingleton (FinitePresentationImmersionFactorization f i f') :=
  inferInstance

/-- Constructor-facing companion for `FinitePresentationImmersionFactorization` from the three
separate source conditions. -/
theorem finitePresentationImmersionFactorization_mk
    {X S X' : Scheme.{u}} {f : X ⟶ S} {i : X ⟶ X'} {f' : X' ⟶ S}
    (hfp : Scheme.Hom.FinitePresentation f') (hi : IsImmersion i)
    (hfac : i ≫ f' = f) :
    FinitePresentationImmersionFactorization f i f' := sorry

/-- Lemma 32.9.1: let `f : X ⟶ S` be locally of finite type, with `X` quasi-compact and
quasi-separated. Then `f` factors over `S` through an immersion `X ⟶ X'`, where
`X' ⟶ S` is of finite presentation. -/
@[stacks 01ZE]
theorem exists_finitePresentation_immersion_factorization_of_locallyOfFiniteType
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    [CompactSpace X.carrier] [QuasiSeparatedSpace X.carrier] :
    ∃ (X' : Scheme.{u}) (i : X ⟶ X') (f' : X' ⟶ S),
      FinitePresentationImmersionFactorization f i f' := sorry

end AlgebraicGeometry
