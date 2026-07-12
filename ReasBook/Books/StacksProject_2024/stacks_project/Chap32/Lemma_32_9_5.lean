import StacksProject_2024.Chap32.Lemma_32_9_4
import StacksProject_2024.Chap29.Definition_29_21_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical morphism owners
-- `IsClosedImmersion`, `LocallyOfFiniteType`, and `LocallyOfFinitePresentation`; local Chapter 32
-- precedent represents directed limits of schemes as diagrams `OrderDual I ⥤ Scheme` with an
-- explicit limiting cone and compatible structure morphisms to the base.

/-- A directed inverse-system presentation of a locally finite type morphism by quasi-compact
quasi-separated schemes of finite presentation over the same base, with closed-immersion
transition maps. -/
@[stacks 09ZQ]
class FinitePresentationClosedImmersionLimitPresentation {I : Type u} [Preorder I]
    {X S : Scheme.{u}} (f : X ⟶ S) (D : OrderDual I ⥤ Scheme.{u})
    (π : (Functor.const (OrderDual I)).obj X ⟶ D)
    (σ : ∀ j : I, D.obj j ⟶ S) : Prop where
  /-- The cone from `X` to the approximating schemes is limiting. -/
  isLimit : Nonempty (IsLimit (⟨X, π⟩ : Cone D))
  /-- The stage structure morphisms are compatible with transition maps. -/
  compatible : ∀ {j k : I} (hjk : j ≤ k), D.map (homOfLE hjk) ≫ σ j = σ k
  /-- Each projection followed by the stage structure morphism recovers the original morphism. -/
  fac : ∀ j : I, π.app j ≫ σ j = f
  /-- Each stage is of finite presentation over the base. -/
  finitePresentation : ∀ j : I, Scheme.Hom.FinitePresentation (σ j)
  /-- Each stage is quasi-compact. -/
  quasiCompact : ∀ j : I, CompactSpace (D.obj j)
  /-- Each stage is quasi-separated. -/
  quasiSeparated : ∀ j : I, QuasiSeparatedSpace (D.obj j)
  /-- Transition morphisms between stages are closed immersions. -/
  transitionClosedImmersion : ∀ {j k : I} (hjk : j ≤ k),
    IsClosedImmersion (D.map (homOfLE hjk))
  /-- The projections from the limit to the stages are closed immersions. -/
  projectionClosedImmersion : ∀ j : I, IsClosedImmersion (π.app j)

/-- Lemma 32.9.5: if `f : X ⟶ S` is locally of finite type, `X` is quasi-compact
and quasi-separated, and `S` is quasi-separated, then `X` is a directed limit of
quasi-compact quasi-separated schemes of finite presentation over `S`, with closed-immersion
transition morphisms and closed-immersion projections from `X` to every stage. -/
@[stacks 09ZQ]
theorem exists_isLimit_finitePresentation_closedImmersion_of_locallyOfFiniteType
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    [CompactSpace X] [QuasiSeparatedSpace X] [QuasiSeparatedSpace S] :
    ∃ (I : Type u), ∃ (_ : Preorder I), ∃ (_ : Nonempty I),
      ∃ (_ : IsDirected I (· ≤ ·)), ∃ (D : OrderDual I ⥤ Scheme.{u}),
        ∃ (π : (Functor.const (OrderDual I)).obj X ⟶ D),
          ∃ (σ : ∀ j : I, D.obj j ⟶ S),
            FinitePresentationClosedImmersionLimitPresentation f D π σ := sorry

end AlgebraicGeometry
