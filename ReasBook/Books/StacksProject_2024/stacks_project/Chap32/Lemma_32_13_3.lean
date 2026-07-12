import StacksProject_2024.Chap32.Lemma_32_13_2
import StacksProject_2024.Chap32.Proposition_32_5_4
import StacksProject_2024.Chap29.Definition_29_15_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced `IsProper` and the affine-transition limit API;
-- local Chapter 32 precedent represents inverse systems by `OrderDual I ⥤ Scheme` with explicit
-- cones, and absolute finite-type bases by objects of `Over (Spec (CommRingCat.of ℤ))`.
-- The Stacks source tag evidence is consistent with tag `0A0P`.

/-- A directed inverse-system presentation of a proper morphism by proper morphisms over
absolute finite-type bases, with affine transition maps on both sources and bases. -/
@[stacks 0A0P]
class ProperAbsoluteNoetherianLimitPresentation {I : Type u} [Preorder I]
    {X S : Scheme} (f : X ⟶ S)
    (Xsys : OrderDual I ⥤ Scheme)
    (Ssys : OrderDual I ⥤ Over (Spec (CommRingCat.of ℤ)))
    (πX : (Functor.const (OrderDual I)).obj X ⟶ Xsys)
    (πS : (Functor.const (OrderDual I)).obj S ⟶
      Ssys ⋙ Over.forget (Spec (CommRingCat.of ℤ)))
    (φ : Xsys ⟶ Ssys ⋙ Over.forget (Spec (CommRingCat.of ℤ))) : Prop where
  /-- The cone from `X` to the source schemes `X_i` is limiting. -/
  sourceIsLimit : Nonempty (IsLimit (⟨X, πX⟩ : Cone Xsys))
  /-- The cone from `S` to the base schemes `S_i` is limiting. -/
  baseIsLimit : Nonempty (IsLimit (⟨S, πS⟩ :
    Cone (Ssys ⋙ Over.forget (Spec (CommRingCat.of ℤ)))))
  /-- The limit morphism is compatible with the stage morphisms `f_i : X_i ⟶ S_i`. -/
  fac : ∀ i : I, πX.app i ≫ φ.app i = f ≫ πS.app i
  /-- Transition morphisms between the source schemes are affine. -/
  sourceTransitionAffine : ∀ {i i' : I} (hii' : i ≤ i'),
    IsAffineHom (Xsys.map (homOfLE hii'))
  /-- Transition morphisms between the base schemes are affine. -/
  baseTransitionAffine : ∀ {i i' : I} (hii' : i ≤ i'),
    IsAffineHom (Ssys.map (homOfLE hii')).left
  /-- Each stage morphism `f_i : X_i ⟶ S_i` is proper. -/
  proper : ∀ i : I, IsProper (φ.app i)
  /-- Each base scheme `S_i` is of finite type over `Spec ℤ`. -/
  baseFiniteType : ∀ i : I, Scheme.Hom.FiniteType (Ssys.obj i).hom

/-- Lemma 32.13.3: let `f : X ⟶ S` be a proper morphism with `S` quasi-compact and
quasi-separated. Then `f` is the limit of an inverse system of proper morphisms
`f_i : X_i ⟶ S_i`, with affine transition morphisms on both `X_i` and `S_i`, and with each
`S_i` of finite type over `ℤ`. -/
@[stacks 0A0P]
theorem exists_isLimit_proper_absoluteNoetherianApproximation_of_isProper
    {X S : Scheme} (f : X ⟶ S) [IsProper f]
    [CompactSpace S] [QuasiSeparatedSpace S] :
    ∃ (I : Type u), ∃ (_ : Preorder I), ∃ (_ : Nonempty I),
      ∃ (_ : IsDirected I (· ≤ ·)), ∃ (Xsys : OrderDual I ⥤ Scheme),
        ∃ (Ssys : OrderDual I ⥤ Over (Spec (CommRingCat.of ℤ))),
          ∃ (πX : (Functor.const (OrderDual I)).obj X ⟶ Xsys),
            ∃ (πS : (Functor.const (OrderDual I)).obj S ⟶
              Ssys ⋙ Over.forget (Spec (CommRingCat.of ℤ))),
              ∃ (φ : Xsys ⟶ Ssys ⋙ Over.forget (Spec (CommRingCat.of ℤ))),
                ProperAbsoluteNoetherianLimitPresentation f Xsys Ssys πX πS φ := sorry

end AlgebraicGeometry
