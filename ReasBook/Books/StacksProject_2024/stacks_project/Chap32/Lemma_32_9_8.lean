import StacksProject_2024.stacks_project.Chap32.Lemma_32_9_5
import StacksProject_2024.stacks_project.Chap32.Lemma_32_4_19

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-morphism owners
-- `IsFinite`, `IsClosedImmersion`, and `Scheme.Hom.FinitePresentation`. Local Chapter 32
-- precedent represents directed limits of schemes as diagrams `OrderDual I ⥤ Scheme` with an
-- explicit limiting cone and compatible structure morphisms to the base. The Stacks source tag
-- evidence is consistent with tag `09YY`.

/-- A directed inverse-system presentation of a finite morphism by schemes finite and of finite
presentation over the same base, with closed-immersion transition maps. -/
@[stacks 09YY]
class FiniteClosedImmersionFinitePresentationLimitPresentation {I : Type u} [Preorder I]
    {X S : Scheme.{u}} (f : X ⟶ S) (D : OrderDual I ⥤ Scheme.{u})
    (π : (Functor.const (OrderDual I)).obj X ⟶ D)
    (σ : ∀ j : I, D.obj j ⟶ S) : Prop where
  /-- The cone from `X` to the approximating schemes is limiting. -/
  isLimit : Nonempty (IsLimit (⟨X, π⟩ : Cone D))
  /-- The stage structure morphisms are compatible with transition maps. -/
  compatible : ∀ {j k : I} (hjk : j ≤ k), D.map (homOfLE hjk) ≫ σ j = σ k
  /-- Each projection followed by the stage structure morphism recovers the original morphism. -/
  fac : ∀ j : I, π.app j ≫ σ j = f
  /-- Transition morphisms between stages are closed immersions. -/
  transitionClosedImmersion : ∀ {j k : I} (hjk : j ≤ k),
    IsClosedImmersion (D.map (homOfLE hjk))
  /-- Each stage is finite over the base. -/
  finite : ∀ j : I, IsFinite (σ j)
  /-- Each stage is of finite presentation over the base. -/
  finitePresentation : ∀ j : I, Scheme.Hom.FinitePresentation (σ j)

/-- Lemma 32.9.8: let `f : X ⟶ S` be a morphism of schemes. Assume `f` is finite, and `S`
is quasi-compact and quasi-separated. Then `X` is a directed limit `X = lim_i X_i` where the
transition maps are closed immersions and the objects `X_i` are finite and of finite presentation
over `S`. -/
@[stacks 09YY]
theorem exists_isLimit_finite_closedImmersion_finitePresentation_of_isFinite
    {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f]
    [CompactSpace S] [QuasiSeparatedSpace S] :
    ∃ (I : Type u), ∃ (_ : Preorder I), ∃ (_ : Nonempty I),
      ∃ (_ : IsDirected I (· ≤ ·)), ∃ (D : OrderDual I ⥤ Scheme.{u}),
        ∃ (π : (Functor.const (OrderDual I)).obj X ⟶ D),
          ∃ (σ : ∀ j : I, D.obj j ⟶ S),
            FiniteClosedImmersionFinitePresentationLimitPresentation f D π σ := sorry

end AlgebraicGeometry
