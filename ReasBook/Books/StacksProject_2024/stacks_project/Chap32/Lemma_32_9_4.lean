import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-morphism owners
-- `IsClosedImmersion`, `LocallyOfFinitePresentation`, and `QuasiCompact`; local Chapter 32
-- precedent states directed limits of schemes as diagrams `OrderDual I ⥤ Scheme` with explicit
-- cones and explicit structure morphisms over the base.

/-- A proof-only property for a directed diagram over `Y`: limiting cone from `X`,
transition-compatible structure maps, factorization of `i`, with each structure map a closed
immersion of finite presentation. -/
@[stacks 09ZP]
class ClosedImmersionFinitePresentationLimitPresentation {I : Type u} [Preorder I]
    {X Y : Scheme.{u}} (i : X ⟶ Y) (D : OrderDual I ⥤ Scheme.{u})
    (π : (Functor.const (OrderDual I)).obj X ⟶ D)
    (σ : ∀ j : I, D.obj j ⟶ Y) : Prop where
  isLimit : Nonempty (IsLimit (⟨X, π⟩ : Cone D))
  compatible : ∀ {j k : I} (hjk : j ≤ k), D.map (homOfLE hjk) ≫ σ j = σ k
  fac : ∀ j : I, π.app j ≫ σ j = i
  isClosedImmersion : ∀ j : I, IsClosedImmersion (σ j)
  locallyOfFinitePresentation : ∀ j : I, LocallyOfFinitePresentation (σ j)
  quasiCompact : ∀ j : I, QuasiCompact (σ j)

/-- Lemma 32.9.4: if `i : X ⟶ Y` is a closed immersion with `Y` quasi-compact,
quasi-separated, then `X` is the directed limit of schemes over `Y` whose structure morphisms are
closed immersions of finite presentation. -/
@[stacks 09ZP]
theorem exists_isLimit_closedImmersion_finitePresentation_of_isClosedImmersion
    {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i]
    [CompactSpace Y] [QuasiSeparatedSpace Y] :
    ∃ (I : Type u), ∃ (_ : Preorder I), ∃ (_ : Nonempty I),
      ∃ (_ : IsDirected I (· ≤ ·)), ∃ (D : OrderDual I ⥤ Scheme.{u}),
        ∃ (π : (Functor.const (OrderDual I)).obj X ⟶ D),
          ∃ (σ : ∀ j : I, D.obj j ⟶ Y),
            ClosedImmersionFinitePresentationLimitPresentation i D π σ := sorry

end AlgebraicGeometry
