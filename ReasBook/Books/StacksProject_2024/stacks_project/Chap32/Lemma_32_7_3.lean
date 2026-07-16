import Mathlib
import StacksProject_2024.stacks_project.Chap29.Definition_29_21_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-morphism owners
-- `IsIntegralHom`, `IsFinite`, and `LocallyOfFinitePresentation`. Local Chapter 32 precedent
-- states scheme limits using diagrams `OrderDual I ⥤ Scheme` with explicit cones and structure
-- maps over the base. The Stacks source tag evidence for this item is consistent with tag `09YZ`.

/-- A directed inverse-system presentation of an integral morphism by finite morphisms of finite
presentation over the same base. -/
@[stacks 09YZ]
class IntegralFinitePresentationLimitPresentation {I : Type u} [Preorder I]
    {X S : Scheme.{u}} (f : X ⟶ S) (D : OrderDual I ⥤ Scheme.{u})
    (π : (Functor.const (OrderDual I)).obj X ⟶ D)
    (σ : ∀ j : I, D.obj j ⟶ S) : Prop where
  /-- The cone from `X` to the approximating schemes is limiting. -/
  isLimit : Nonempty (IsLimit (⟨X, π⟩ : Cone D))
  /-- The structure morphisms to the base are compatible with transition maps. -/
  compatible : ∀ {j k : I} (hjk : j ≤ k), D.map (homOfLE hjk) ≫ σ j = σ k
  /-- Each projection followed by the stage structure morphism recovers the original map. -/
  fac : ∀ j : I, π.app j ≫ σ j = f
  /-- Each stage is finite over the base. -/
  isFinite : ∀ j : I, IsFinite (σ j)
  /-- Each stage is of finite presentation over the base. -/
  finitePresentation : ∀ j : I, Scheme.Hom.FinitePresentation (σ j)

/-- Lemma 32.7.3: let `X ⟶ S` be an integral morphism with `S` quasi-compact and
quasi-separated. Then `X` is a directed limit of schemes `X_i` over `S` whose structure morphisms
`X_i ⟶ S` are finite and of finite presentation. -/
@[stacks 09YZ]
theorem exists_isLimit_finite_finitePresentation_of_isIntegralHom
    {X S : Scheme.{u}} (f : X ⟶ S) [IsIntegralHom f]
    [CompactSpace S] [QuasiSeparatedSpace S] :
    ∃ (I : Type u), ∃ (_ : Preorder I), ∃ (_ : Nonempty I),
      ∃ (_ : IsDirected I (· ≤ ·)), ∃ (D : OrderDual I ⥤ Scheme.{u}),
        ∃ (π : (Functor.const (OrderDual I)).obj X ⟶ D),
          ∃ (σ : ∀ j : I, D.obj j ⟶ S),
            IntegralFinitePresentationLimitPresentation f D π σ := sorry

end AlgebraicGeometry
