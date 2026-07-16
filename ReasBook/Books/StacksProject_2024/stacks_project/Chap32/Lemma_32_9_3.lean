import StacksProject_2024.stacks_project.Chap32.Lemma_32_9_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-morphism owners
-- `IsClosedImmersion`, `LocallyOfFiniteType`, plus finite-presentation morphisms; local Chapter 32
-- precedent represents this factorization by explicit witnesses with the equation over the base.

/-- A proof-only property for a factorization through a scheme of finite presentation by a closed
immersion. -/
@[stacks 01ZG]
class FinitePresentationClosedImmersionFactorization
    {X S X' : Scheme.{u}} (f : X ⟶ S) (i : X ⟶ X') (f' : X' ⟶ S) : Prop extends
    Scheme.Hom.FinitePresentation f', IsClosedImmersion i where
  /-- The factorization composes to the original morphism. -/
  fac : i ≫ f' = f

/-- Finite-presentation closed-immersion factorization structures are proposition-valued. -/
instance instSubsingletonFinitePresentationClosedImmersionFactorization
    {X S X' : Scheme.{u}} {f : X ⟶ S} {i : X ⟶ X'} {f' : X' ⟶ S} :
    Subsingleton (FinitePresentationClosedImmersionFactorization f i f') :=
  inferInstance

/-- Constructor-facing companion for `FinitePresentationClosedImmersionFactorization` from the
three separate source conditions. -/
theorem finitePresentationClosedImmersionFactorization_mk
    {X S X' : Scheme.{u}} {f : X ⟶ S} {i : X ⟶ X'} {f' : X' ⟶ S}
    (hfp : Scheme.Hom.FinitePresentation f') (hi : IsClosedImmersion i)
    (hfac : i ≫ f' = f) :
    FinitePresentationClosedImmersionFactorization f i f' := sorry

/-- Lemma 32.9.3: let `f : X ⟶ S` be locally of finite type; assume `X` is quasi-compact,
`X` is quasi-separated, plus `S` is quasi-separated. Then `f` factors over `S` through a
closed immersion `X ⟶ X'`, where `X' ⟶ S` is of finite presentation. -/
@[stacks 01ZG]
theorem exists_finitePresentation_closedImmersion_factorization_of_locallyOfFiniteType
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    [CompactSpace X.carrier] [QuasiSeparatedSpace X.carrier] [QuasiSeparatedSpace S.carrier] :
    ∃ (X' : Scheme.{u}) (i : X ⟶ X') (f' : X' ⟶ S),
      FinitePresentationClosedImmersionFactorization f i f' := sorry

end AlgebraicGeometry
