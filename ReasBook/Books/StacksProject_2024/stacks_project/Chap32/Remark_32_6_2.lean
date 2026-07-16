import StacksProject_2024.stacks_project.Chap32.Proposition_32_6_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-morphism owner
-- `AlgebraicGeometry.LocallyOfFinitePresentation`; local Proposition 32.6.1 already states the
-- affine inverse-limit criterion using `yoneda.obj (Over.mk f)`. The Stacks source tag evidence is
-- consistent with tag `05LX`.

/-- Remark 32.6.2 (1): a set-valued functor on `(Sch/S)ᵒᵖ` is limit preserving if, for every
directed inverse system of affine `S`-schemes with limit cone `c`, the induced cocone on its
values is a colimit. This is the Lean form of `F(lim_i T_i) = colim_i F(T_i)`. -/
@[stacks 05LX]
class PreservesDirectedAffineLimits (S : Scheme.{u}) (F : (Over S)ᵒᵖ ⥤ Type u) : Prop where
  isColimit :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : OrderDual I ⥤ Over S) (c : Cone D),
        IsLimit c →
        (∀ i : I, IsAffine (D.obj i).left) →
        Nonempty (IsColimit (F.mapCocone c.op))

/-- Characterization of the source-facing limit-preservation class by its directed affine
inverse-system colimit condition. -/
@[stacks 05LX]
theorem preservesDirectedAffineLimits_iff {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} :
    PreservesDirectedAffineLimits S F ↔
      ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
        (D : OrderDual I ⥤ Over S) (c : Cone D),
          IsLimit c →
          (∀ i : I, IsAffine (D.obj i).left) →
          Nonempty (IsColimit (F.mapCocone c.op)) := sorry

/-- Source-facing field specification for `PreservesDirectedAffineLimits`: every directed affine
inverse system with a limit cone is sent by `F` to a colimit cocone of sets. -/
@[stacks 05LX]
theorem PreservesDirectedAffineLimits.isColimit.spec {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} [hF : PreservesDirectedAffineLimits S F]
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Over S) (c : Cone D)
    (hc : IsLimit c) (hD : ∀ i : I, IsAffine (D.obj i).left) :
    Nonempty (IsColimit (F.mapCocone c.op)) := sorry

/-- Remark 32.6.2 (2): in the terminology of limit preserving functors, Proposition 32.6.1 says
that the functor of points of an `S`-scheme `X` is limit preserving exactly when `X` is locally of
finite presentation over `S`. -/
@[stacks 05LX]
theorem locallyOfFinitePresentation_iff_preservesDirectedAffineLimits_yoneda
    {X S : Scheme.{u}} (f : X ⟶ S) :
    LocallyOfFinitePresentation f ↔
      PreservesDirectedAffineLimits S (yoneda.obj (Over.mk f)) := sorry

/-- A locally finitely presented `S`-scheme has a limit-preserving functor of points on
directed affine inverse systems over `S`. -/
@[stacks 05LX, instance]
instance instPreservesDirectedAffineLimitsYonedaOfLocallyOfFinitePresentation
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f] :
    PreservesDirectedAffineLimits S (yoneda.obj (Over.mk f)) := sorry

end AlgebraicGeometry
