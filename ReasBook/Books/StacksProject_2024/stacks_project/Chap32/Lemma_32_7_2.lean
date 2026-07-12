import StacksProject_2024.Chap29.Definition_29_21_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the affine-transition scheme-limit API and the
-- canonical morphism owners `IsAffineHom` and `Scheme.Hom.FinitePresentation`. Local Chapter 32
-- precedent represents directed inverse limits of schemes over a fixed base by a diagram
-- `D : OrderDual I ⥤ Scheme`, a cone from the limit object, and compatible structure morphisms to
-- the base. The Stacks source tag evidence is consistent with tag `09MV`.

/-- A directed inverse-system presentation of a morphism by schemes of finite presentation over
the same base, with affine transition morphisms over that base. -/
@[stacks 09MV]
class FinitePresentationLimitPresentation {I : Type u} [Preorder I]
    {X S : Scheme.{u}} (f : X ⟶ S) (D : OrderDual I ⥤ Scheme.{u})
    (π : (Functor.const (OrderDual I)).obj X ⟶ D)
    (σ : ∀ j : I, D.obj j ⟶ S) : Prop where
  /-- The cone from `X` to the approximating schemes is limiting. -/
  isLimit : Nonempty (IsLimit (⟨X, π⟩ : Cone D))
  /-- The stage structure morphisms are compatible with transition maps. -/
  compatible : ∀ {j k : I} (hjk : j ≤ k), D.map (homOfLE hjk) ≫ σ j = σ k
  /-- Each projection followed by the stage structure morphism recovers the original map. -/
  fac : ∀ j : I, π.app j ≫ σ j = f
  /-- Transition maps between approximating schemes are affine. -/
  transitionAffine : ∀ {j k : I} (hjk : j ≤ k), IsAffineHom (D.map (homOfLE hjk))
  /-- Each stage is of finite presentation over the base. -/
  finitePresentation : ∀ j : I, Scheme.Hom.FinitePresentation (σ j)

/-- Lemma 32.7.2: let `f : X ⟶ S` be a morphism of schemes. Assume that `X` is quasi-compact
and quasi-separated, and `S` is quasi-separated. Then `X = lim_i X_i` is a limit of a directed
system of schemes `X_i` of finite presentation over `S` with affine transition morphisms over
`S`. -/
@[stacks 09MV]
theorem exists_isLimit_finitePresentation_of_qcqs
    {X S : Scheme.{u}} (f : X ⟶ S) [CompactSpace X] [QuasiSeparatedSpace X]
    [QuasiSeparatedSpace S] :
    ∃ (I : Type u), ∃ (_ : Preorder I), ∃ (_ : Nonempty I),
      ∃ (_ : IsDirected I (· ≤ ·)), ∃ (D : OrderDual I ⥤ Scheme.{u}),
        ∃ (π : (Functor.const (OrderDual I)).obj X ⟶ D),
          ∃ (σ : ∀ j : I, D.obj j ⟶ S),
            FinitePresentationLimitPresentation f D π σ := sorry

end AlgebraicGeometry
