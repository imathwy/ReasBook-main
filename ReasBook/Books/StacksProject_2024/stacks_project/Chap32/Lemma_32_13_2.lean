import StacksProject_2024.Chap32.Lemma_32_9_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-morphism owner `IsProper`.
-- Local Chapter 32 precedent represents directed limits of schemes by diagrams
-- `OrderDual I ⥤ Scheme` with an explicit limiting cone and stage morphisms over the base.
-- The Stacks source tag evidence is consistent with tag `09ZR`.

/-- A directed inverse-system presentation of a proper morphism by proper finite-presentation
schemes over the same base, with closed-immersion transition maps and closed-immersion
projections from the limit. -/
@[stacks 09ZR]
class ProperFinitePresentationClosedImmersionLimitPresentation {I : Type u} [Preorder I]
    {X S : Scheme.{u}} (f : X ⟶ S) (D : OrderDual I ⥤ Scheme.{u})
    (π : (Functor.const (OrderDual I)).obj X ⟶ D)
    (σ : ∀ j : I, D.obj j ⟶ S) : Prop where
  /-- The cone from `X` to the approximating schemes is limiting. -/
  isLimit : Nonempty (IsLimit (⟨X, π⟩ : Cone D))
  /-- The stage structure morphisms are compatible with transition maps. -/
  compatible : ∀ {j k : I} (hjk : j ≤ k), D.map (homOfLE hjk) ≫ σ j = σ k
  /-- Each projection followed by the stage structure morphism recovers the original morphism. -/
  fac : ∀ j : I, π.app j ≫ σ j = f
  /-- Each stage is proper over the base. -/
  proper : ∀ j : I, IsProper (σ j)
  /-- Each stage is of finite presentation over the base. -/
  finitePresentation : ∀ j : I, Scheme.Hom.FinitePresentation (σ j)
  /-- Transition morphisms between stages are closed immersions. -/
  transitionClosedImmersion : ∀ {j k : I} (hjk : j ≤ k),
    IsClosedImmersion (D.map (homOfLE hjk))
  /-- The projections from the limit to the stages are closed immersions. -/
  projectionClosedImmersion : ∀ j : I, IsClosedImmersion (π.app j)

/-- Lemma 32.13.2: let `f : X ⟶ S` be a proper morphism with `S` quasi-compact and
quasi-separated. Then `X` is a directed limit of schemes `X_i` proper and of finite presentation
over `S`, such that all transition morphisms and all projections `X ⟶ X_i` are closed
immersions. -/
@[stacks 09ZR]
theorem exists_isLimit_proper_finitePresentation_closedImmersion_of_isProper
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    [CompactSpace S] [QuasiSeparatedSpace S] :
    ∃ (I : Type u), ∃ (_ : Preorder I), ∃ (_ : Nonempty I),
      ∃ (_ : IsDirected I (· ≤ ·)), ∃ (D : OrderDual I ⥤ Scheme.{u}),
        ∃ (π : (Functor.const (OrderDual I)).obj X ⟶ D),
          ∃ (σ : ∀ j : I, D.obj j ⟶ S),
            ProperFinitePresentationClosedImmersionLimitPresentation f D π σ := sorry

end AlgebraicGeometry
