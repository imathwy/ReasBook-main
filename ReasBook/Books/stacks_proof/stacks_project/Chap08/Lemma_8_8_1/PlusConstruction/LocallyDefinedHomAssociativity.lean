import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.PlusConstruction.LocallyDefinedHomCategoryLaws

universe u v uX vX

namespace CategoryTheory

open Bicategory
open FibredCategoryMor
open Functor
open Opposite
open scoped CategoryTheory.Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

attribute [local instance] Types.instFunLike Types.instConcreteCategory

namespace FibredCategoryMor
namespace LocallyDefinedHomRepresentativeOver

private theorem associativity_overMorphism_heq_of_left_heq
    {U : C} {A B A' B' : Over U} (hA : A = A') (hB : B = B')
    {f : A ⟶ B} {g : A' ⟶ B'} (hleft : HEq f.left g.left) :
    HEq f g := by
  cases hA
  cases hB
  exact heq_of_eq (Over.OverMorphism.ext (eq_of_heq hleft))

/-- The source-proof triple cover for associativity, written with the left bracketing.

Unfolding the binary composition cover, this is the formal incarnation of
`U_i ×_V V_j ×_W W_k`. -/
noncomputable abbrev associativityTripleCover
    {X : FibredCategoryOver.{u, v, uX, vX} C} {w x y z : X.S}
    {f : X.p.obj w ⟶ X.p.obj x}
    {g : X.p.obj x ⟶ X.p.obj y}
    {k : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (γ : LocallyDefinedHomRepresentativeOver (J := J) X k) :
    (J.over (X.p.obj w)).Cover (Over.mk (𝟙 (X.p.obj w))) :=
  compositionCover (J := J) (composeOver (J := J) α β) γ

/-- Projection of the associativity triple cover to the left binary-composite cover
`U_i ×_V V_j`. -/
noncomputable abbrev associativityTripleCoverToLeftComposite
    {X : FibredCategoryOver.{u, v, uX, vX} C} {w x y z : X.S}
    {f : X.p.obj w ⟶ X.p.obj x}
    {g : X.p.obj x ⟶ X.p.obj y}
    {k : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (γ : LocallyDefinedHomRepresentativeOver (J := J) X k)
    (I : (associativityTripleCover (J := J) α β γ).Arrow) :
    (compositionCover (J := J) α β).Arrow :=
  compositionCoverToLeft (J := J) (composeOver (J := J) α β) γ I

/-- Projection of the associativity triple cover to the original `α`-cover. -/
noncomputable abbrev associativityTripleCoverToAlpha
    {X : FibredCategoryOver.{u, v, uX, vX} C} {w x y z : X.S}
    {f : X.p.obj w ⟶ X.p.obj x}
    {g : X.p.obj x ⟶ X.p.obj y}
    {k : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (γ : LocallyDefinedHomRepresentativeOver (J := J) X k)
    (I : (associativityTripleCover (J := J) α β γ).Arrow) :
    α.cover.Arrow :=
  compositionCoverToLeft (J := J) α β
    (associativityTripleCoverToLeftComposite (J := J) α β γ I)

/-- Projection of the associativity triple cover to the original `β`-cover. -/
noncomputable abbrev associativityTripleCoverToBeta
    {X : FibredCategoryOver.{u, v, uX, vX} C} {w x y z : X.S}
    {f : X.p.obj w ⟶ X.p.obj x}
    {g : X.p.obj x ⟶ X.p.obj y}
    {k : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (γ : LocallyDefinedHomRepresentativeOver (J := J) X k)
    (I : (associativityTripleCover (J := J) α β γ).Arrow) :
    β.cover.Arrow :=
  compositionCoverToRight (J := J) α β
    (associativityTripleCoverToLeftComposite (J := J) α β γ I)

/-- Projection of the associativity triple cover to the original `γ`-cover. -/
noncomputable abbrev associativityTripleCoverToGamma
    {X : FibredCategoryOver.{u, v, uX, vX} C} {w x y z : X.S}
    {f : X.p.obj w ⟶ X.p.obj x}
    {g : X.p.obj x ⟶ X.p.obj y}
    {k : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (γ : LocallyDefinedHomRepresentativeOver (J := J) X k)
    (I : (associativityTripleCover (J := J) α β γ).Arrow) :
    γ.cover.Arrow :=
  compositionCoverToRight (J := J) (composeOver (J := J) α β) γ I

@[simp]
theorem associativityTripleCoverToAlpha_f
    {X : FibredCategoryOver.{u, v, uX, vX} C} {w x y z : X.S}
    {f : X.p.obj w ⟶ X.p.obj x}
    {g : X.p.obj x ⟶ X.p.obj y}
    {k : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (γ : LocallyDefinedHomRepresentativeOver (J := J) X k)
    (I : (associativityTripleCover (J := J) α β γ).Arrow) :
    (associativityTripleCoverToAlpha (J := J) α β γ I).f = I.f :=
  rfl

@[simp]
theorem associativityTripleCoverToBeta_hom
    {X : FibredCategoryOver.{u, v, uX, vX} C} {w x y z : X.S}
    {f : X.p.obj w ⟶ X.p.obj x}
    {g : X.p.obj x ⟶ X.p.obj y}
    {k : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (γ : LocallyDefinedHomRepresentativeOver (J := J) X k)
    (I : (associativityTripleCover (J := J) α β γ).Arrow) :
    (associativityTripleCoverToBeta (J := J) α β γ I).Y.hom = I.Y.hom ≫ f :=
  rfl

@[simp]
theorem associativityTripleCoverToGamma_hom
    {X : FibredCategoryOver.{u, v, uX, vX} C} {w x y z : X.S}
    {f : X.p.obj w ⟶ X.p.obj x}
    {g : X.p.obj x ⟶ X.p.obj y}
    {k : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (γ : LocallyDefinedHomRepresentativeOver (J := J) X k)
    (I : (associativityTripleCover (J := J) α β γ).Arrow) :
    (associativityTripleCoverToGamma (J := J) α β γ I).Y.hom = I.Y.hom ≫ (f ≫ g) :=
  rfl

/-- The left-associated source cover refines the right-associated source cover.

In the Stacks notation this is the inclusion of
`(U_i ×_V V_j) ×_W W_k` into the triple common cover read as
`U_i ×_V (V_j ×_W W_k)`.  Formally, the target cover is expressed through the
already-defined binary `composeOver β γ`, so the proof explicitly converts slice-cover membership
back and forth through the underlying base cover. -/
noncomputable def assocCoverLeftToRightHom
    {X : FibredCategoryOver.{u, v, uX, vX} C} {w x y z : X.S}
    {f : X.p.obj w ⟶ X.p.obj x}
    {g : X.p.obj x ⟶ X.p.obj y}
    {k : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (γ : LocallyDefinedHomRepresentativeOver (J := J) X k) :
    compositionCover (J := J) (composeOver (J := J) α β) γ ⟶
      compositionCover (J := J) α (composeOver (J := J) β γ) :=
  homOfLE (by
    intro Y a ha
    refine ⟨?_, ?_⟩
    · exact ha.1.1
    · have hβbase :
          (β.baseCover : Sieve (X.p.obj x)) (a.left ≫ f) := by
        have hslice :
            ((identitySliceCoverOfBaseCover (J := J)
                (((J.pullback f).obj β.baseCover)) :
                (J.over (X.p.obj w)).Cover (Over.mk (𝟙 (X.p.obj w)))) :
                Sieve (Over.mk (𝟙 (X.p.obj w)))) a := ha.1.2
        have hconverted :=
          (Sieve.overEquiv_symm_iff
            (Y := Over.mk (𝟙 (X.p.obj w)))
            (((J.pullback f).obj β.baseCover) : Sieve (X.p.obj w)) a).1 hslice
        change (β.baseCover : Sieve (X.p.obj x)) (a.left ≫ f) at hconverted
        exact hconverted
      have hγbase :
          (γ.baseCover : Sieve (X.p.obj y)) ((a.left ≫ f) ≫ g) := by
        have hslice :
            ((identitySliceCoverOfBaseCover (J := J)
                (((J.pullback (f ≫ g)).obj γ.baseCover)) :
                (J.over (X.p.obj w)).Cover (Over.mk (𝟙 (X.p.obj w)))) :
                Sieve (Over.mk (𝟙 (X.p.obj w)))) a := ha.2
        have hconverted :=
          (Sieve.overEquiv_symm_iff
            (Y := Over.mk (𝟙 (X.p.obj w)))
            (((J.pullback (f ≫ g)).obj γ.baseCover) : Sieve (X.p.obj w)) a).1 hslice
        change (γ.baseCover : Sieve (X.p.obj y)) (a.left ≫ (f ≫ g)) at hconverted
        simpa [Category.assoc] using hconverted
      have hβθ :
          (β.cover : Sieve (Over.mk (𝟙 (X.p.obj x))))
            (Over.homMk (a.left ≫ f) :
              Over.mk ((a.left ≫ f) ≫ 𝟙 (X.p.obj x)) ⟶
                Over.mk (𝟙 (X.p.obj x))) := by
        exact
          (Sieve.overEquiv_iff (Y := Over.mk (𝟙 (X.p.obj x)))
            (β.cover : Sieve (Over.mk (𝟙 (X.p.obj x)))) (a.left ≫ f)).1 hβbase
      have hγpull :
          (((J.pullback g).obj γ.baseCover) : Sieve (X.p.obj x)) (a.left ≫ f) := by
        change (γ.baseCover : Sieve (X.p.obj y)) ((a.left ≫ f) ≫ g)
        exact hγbase
      have hβγslice :
          ((compositionCover (J := J) β γ :
              (J.over (X.p.obj x)).Cover (Over.mk (𝟙 (X.p.obj x)))) :
              Sieve (Over.mk (𝟙 (X.p.obj x))))
            (Over.homMk (a.left ≫ f) :
              Over.mk ((a.left ≫ f) ≫ 𝟙 (X.p.obj x)) ⟶
                Over.mk (𝟙 (X.p.obj x))) := by
        exact ⟨hβθ, by
          exact
            (Sieve.overEquiv_symm_iff
              (Y := Over.mk (𝟙 (X.p.obj x)))
              (((J.pullback g).obj γ.baseCover) : Sieve (X.p.obj x))
              (Over.homMk (a.left ≫ f) :
                Over.mk ((a.left ≫ f) ≫ 𝟙 (X.p.obj x)) ⟶
                  Over.mk (𝟙 (X.p.obj x)))).2 hγpull⟩
      have hβγbase :
          ((composeOver (J := J) β γ).baseCover : Sieve (X.p.obj x)) (a.left ≫ f) := by
        exact
          (Sieve.overEquiv_iff (Y := Over.mk (𝟙 (X.p.obj x)))
            ((composeOver (J := J) β γ).cover :
              Sieve (Over.mk (𝟙 (X.p.obj x)))) (a.left ≫ f)).2 hβγslice
      have hpull :
          (((J.pullback f).obj (composeOver (J := J) β γ).baseCover) :
            Sieve (X.p.obj w)) a.left := by
        change ((composeOver (J := J) β γ).baseCover : Sieve (X.p.obj x)) (a.left ≫ f)
        exact hβγbase
      exact
        (Sieve.overEquiv_symm_iff
          (Y := Over.mk (𝟙 (X.p.obj w)))
          (((J.pullback f).obj (composeOver (J := J) β γ).baseCover) :
            Sieve (X.p.obj w)) a).2 hpull)

/-- The right-associated source cover refines the left-associated source cover.

This is the reverse reading of the same triple common cover
`U_i ×_V V_j ×_W W_k`.  The point of keeping this as a separate lemma is that later
family-level associativity can choose either bracketing as the common refinement without hiding
the owner conversions through definitional equality. -/
noncomputable def assocCoverRightToLeftHom
    {X : FibredCategoryOver.{u, v, uX, vX} C} {w x y z : X.S}
    {f : X.p.obj w ⟶ X.p.obj x}
    {g : X.p.obj x ⟶ X.p.obj y}
    {k : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (γ : LocallyDefinedHomRepresentativeOver (J := J) X k) :
    compositionCover (J := J) α (composeOver (J := J) β γ) ⟶
      compositionCover (J := J) (composeOver (J := J) α β) γ :=
  homOfLE (by
    intro Y a ha
    have hβγbase :
        ((composeOver (J := J) β γ).baseCover : Sieve (X.p.obj x)) (a.left ≫ f) := by
      have hslice :
          ((identitySliceCoverOfBaseCover (J := J)
              (((J.pullback f).obj (composeOver (J := J) β γ).baseCover)) :
              (J.over (X.p.obj w)).Cover (Over.mk (𝟙 (X.p.obj w)))) :
              Sieve (Over.mk (𝟙 (X.p.obj w)))) a := ha.2
      have hconverted :=
        (Sieve.overEquiv_symm_iff
          (Y := Over.mk (𝟙 (X.p.obj w)))
          (((J.pullback f).obj (composeOver (J := J) β γ).baseCover) :
            Sieve (X.p.obj w)) a).1 hslice
      change ((composeOver (J := J) β γ).baseCover : Sieve (X.p.obj x))
        (a.left ≫ f) at hconverted
      exact hconverted
    have hβγslice :
        ((compositionCover (J := J) β γ :
            (J.over (X.p.obj x)).Cover (Over.mk (𝟙 (X.p.obj x)))) :
            Sieve (Over.mk (𝟙 (X.p.obj x))))
          (Over.homMk (a.left ≫ f) :
            Over.mk ((a.left ≫ f) ≫ 𝟙 (X.p.obj x)) ⟶
              Over.mk (𝟙 (X.p.obj x))) := by
      exact
        (Sieve.overEquiv_iff (Y := Over.mk (𝟙 (X.p.obj x)))
          ((composeOver (J := J) β γ).cover :
            Sieve (Over.mk (𝟙 (X.p.obj x)))) (a.left ≫ f)).1 hβγbase
    have hβbase :
        (β.baseCover : Sieve (X.p.obj x)) (a.left ≫ f) := by
      exact
        (Sieve.overEquiv_iff (Y := Over.mk (𝟙 (X.p.obj x)))
          (β.cover : Sieve (Over.mk (𝟙 (X.p.obj x)))) (a.left ≫ f)).2 hβγslice.1
    have hβpull :
        (((J.pullback f).obj β.baseCover) : Sieve (X.p.obj w)) a.left := by
      change (β.baseCover : Sieve (X.p.obj x)) (a.left ≫ f)
      exact hβbase
    have hαβslice :
        ((compositionCover (J := J) α β :
            (J.over (X.p.obj w)).Cover (Over.mk (𝟙 (X.p.obj w)))) :
            Sieve (Over.mk (𝟙 (X.p.obj w)))) a := by
      refine ⟨ha.1, ?_⟩
      exact
        (Sieve.overEquiv_symm_iff
          (Y := Over.mk (𝟙 (X.p.obj w)))
          (((J.pullback f).obj β.baseCover) : Sieve (X.p.obj w)) a).2 hβpull
    have hγpullOverX :
        (((J.pullback g).obj γ.baseCover) : Sieve (X.p.obj x)) (a.left ≫ f) := by
      have hconverted :=
        (Sieve.overEquiv_symm_iff
          (Y := Over.mk (𝟙 (X.p.obj x)))
          (((J.pullback g).obj γ.baseCover) : Sieve (X.p.obj x))
          (Over.homMk (a.left ≫ f) :
            Over.mk ((a.left ≫ f) ≫ 𝟙 (X.p.obj x)) ⟶
              Over.mk (𝟙 (X.p.obj x)))).1 hβγslice.2
      change (γ.baseCover : Sieve (X.p.obj y)) ((a.left ≫ f) ≫ g) at hconverted
      change (γ.baseCover : Sieve (X.p.obj y)) ((a.left ≫ f) ≫ g)
      exact hconverted
    have hγpull :
        (((J.pullback (f ≫ g)).obj γ.baseCover) : Sieve (X.p.obj w)) a.left := by
      change (γ.baseCover : Sieve (X.p.obj y)) (a.left ≫ (f ≫ g))
      simpa [Category.assoc] using hγpullOverX
    refine ⟨hαβslice, ?_⟩
    exact
      (Sieve.overEquiv_symm_iff
        (Y := Over.mk (𝟙 (X.p.obj w)))
        (((J.pullback (f ≫ g)).obj γ.baseCover) : Sieve (X.p.obj w)) a).2 hγpull)

/-- The same triple-cover member, regarded as a member of the right-associated composite cover. -/
noncomputable abbrev associativityTripleCoverToRightMember
    {X : FibredCategoryOver.{u, v, uX, vX} C} {w x y z : X.S}
    {f : X.p.obj w ⟶ X.p.obj x}
    {g : X.p.obj x ⟶ X.p.obj y}
    {k : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (γ : LocallyDefinedHomRepresentativeOver (J := J) X k)
    (I : (associativityTripleCover (J := J) α β γ).Arrow) :
    (compositionCover (J := J) α (composeOver (J := J) β γ)).Arrow :=
  ⟨I.Y, I.f, (leOfHom (assocCoverLeftToRightHom (J := J) α β γ)) _ I.hf⟩

/-- Projection of the triple cover to the right binary-composite cover `V_j ×_W W_k`, using
the right-associated bracketing. -/
noncomputable abbrev associativityTripleCoverToRightComposite
    {X : FibredCategoryOver.{u, v, uX, vX} C} {w x y z : X.S}
    {f : X.p.obj w ⟶ X.p.obj x}
    {g : X.p.obj x ⟶ X.p.obj y}
    {k : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (γ : LocallyDefinedHomRepresentativeOver (J := J) X k)
    (I : (associativityTripleCover (J := J) α β γ).Arrow) :
    (compositionCover (J := J) β γ).Arrow :=
  compositionCoverToRight (J := J) α (composeOver (J := J) β γ)
    (associativityTripleCoverToRightMember (J := J) α β γ I)

/-- Projection of the right-associated view of the triple cover to the original `β`-cover. -/
noncomputable abbrev associativityTripleCoverToRightBeta
    {X : FibredCategoryOver.{u, v, uX, vX} C} {w x y z : X.S}
    {f : X.p.obj w ⟶ X.p.obj x}
    {g : X.p.obj x ⟶ X.p.obj y}
    {k : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (γ : LocallyDefinedHomRepresentativeOver (J := J) X k)
    (I : (associativityTripleCover (J := J) α β γ).Arrow) :
    β.cover.Arrow :=
  compositionCoverToLeft (J := J) β γ
    (associativityTripleCoverToRightComposite (J := J) α β γ I)

/-- Projection of the right-associated view of the triple cover to the original `γ`-cover. -/
noncomputable abbrev associativityTripleCoverToRightGamma
    {X : FibredCategoryOver.{u, v, uX, vX} C} {w x y z : X.S}
    {f : X.p.obj w ⟶ X.p.obj x}
    {g : X.p.obj x ⟶ X.p.obj y}
    {k : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (γ : LocallyDefinedHomRepresentativeOver (J := J) X k)
    (I : (associativityTripleCover (J := J) α β γ).Arrow) :
    γ.cover.Arrow :=
  compositionCoverToRight (J := J) β γ
    (associativityTripleCoverToRightComposite (J := J) α β γ I)

@[simp]
theorem associativityTripleCoverToRightBeta_hom
    {X : FibredCategoryOver.{u, v, uX, vX} C} {w x y z : X.S}
    {f : X.p.obj w ⟶ X.p.obj x}
    {g : X.p.obj x ⟶ X.p.obj y}
    {k : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (γ : LocallyDefinedHomRepresentativeOver (J := J) X k)
    (I : (associativityTripleCover (J := J) α β γ).Arrow) :
    (associativityTripleCoverToRightBeta (J := J) α β γ I).Y.hom = I.Y.hom ≫ f :=
  rfl

@[simp]
theorem associativityTripleCoverToRightGamma_hom
    {X : FibredCategoryOver.{u, v, uX, vX} C} {w x y z : X.S}
    {f : X.p.obj w ⟶ X.p.obj x}
    {g : X.p.obj x ⟶ X.p.obj y}
    {k : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (γ : LocallyDefinedHomRepresentativeOver (J := J) X k)
    (I : (associativityTripleCover (J := J) α β γ).Arrow) :
    (associativityTripleCoverToRightGamma (J := J) α β γ I).Y.hom =
      (I.Y.hom ≫ f) ≫ g :=
  rfl

/-- On the associativity triple cover, both bracketings use the same local `α`-factor. -/
theorem associativityTripleCover_alphaLocal_down_heq
    {X : FibredCategoryOver.{u, v, uX, vX} C} {w x y z : X.S}
    {f : X.p.obj w ⟶ X.p.obj x}
    {g : X.p.obj x ⟶ X.p.obj y}
    {k : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (γ : LocallyDefinedHomRepresentativeOver (J := J) X k)
    (I : (associativityTripleCover (J := J) α β γ).Arrow) :
    HEq
      ((compositionLeftLocal (J := J) α β
        (associativityTripleCoverToLeftComposite (J := J) α β γ I)).down)
      ((compositionLeftLocal (J := J) α (composeOver (J := J) β γ)
        (associativityTripleCoverToRightMember (J := J) α β γ I)).down) := by
  rfl

/-- On the associativity triple cover, both bracketings use the same local `β`-factor. -/
theorem associativityTripleCover_betaLocal_down_heq
    {X : FibredCategoryOver.{u, v, uX, vX} C} {w x y z : X.S}
    {f : X.p.obj w ⟶ X.p.obj x}
    {g : X.p.obj x ⟶ X.p.obj y}
    {k : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (γ : LocallyDefinedHomRepresentativeOver (J := J) X k)
    (I : (associativityTripleCover (J := J) α β γ).Arrow) :
    HEq
      ((compositionRightLocal (J := J) α β
        (associativityTripleCoverToLeftComposite (J := J) α β γ I)).down)
      ((compositionLeftLocal (J := J) β γ
        (associativityTripleCoverToRightComposite (J := J) α β γ I)).down) := by
  rfl

/-- The two presentations of the local `γ` base arrow on the associativity triple cover differ
only by categorical associativity. -/
theorem associativityTripleCover_gamma_hom_eq
    {X : FibredCategoryOver.{u, v, uX, vX} C} {w x y z : X.S}
    {f : X.p.obj w ⟶ X.p.obj x}
    {g : X.p.obj x ⟶ X.p.obj y}
    {k : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (γ : LocallyDefinedHomRepresentativeOver (J := J) X k)
    (I : (associativityTripleCover (J := J) α β γ).Arrow) :
    (associativityTripleCoverToGamma (J := J) α β γ I).Y.hom =
      (associativityTripleCoverToRightGamma (J := J) α β γ I).Y.hom := by
  simp [Category.assoc]

/-- On the associativity triple cover, both bracketings use the same local `γ`-factor, up to
the owner transport coming from associativity of the displayed base arrow. -/
theorem associativityTripleCover_gammaLocal_down_heq
    {X : FibredCategoryOver.{u, v, uX, vX} C} {w x y z : X.S}
    {f : X.p.obj w ⟶ X.p.obj x}
    {g : X.p.obj x ⟶ X.p.obj y}
    {k : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (γ : LocallyDefinedHomRepresentativeOver (J := J) X k)
    (I : (associativityTripleCover (J := J) α β γ).Arrow) :
    HEq
      ((compositionRightLocal (J := J) (composeOver (J := J) α β) γ I).down)
      ((compositionRightLocal (J := J) β γ
        (associativityTripleCoverToRightComposite (J := J) α β γ I)).down) := by
  have hY :
      (associativityTripleCoverToGamma (J := J) α β γ I).Y =
        (associativityTripleCoverToRightGamma (J := J) α β γ I).Y := by
    change Over.mk (I.Y.hom ≫ (f ≫ g)) = Over.mk ((I.Y.hom ≫ f) ≫ g)
    simp [Category.assoc]
  have hA :
      associativityTripleCoverToGamma (J := J) α β γ I =
        associativityTripleCoverToRightGamma (J := J) α β γ I := by
    apply GrothendieckTopology.Cover.Arrow.ext
    · exact hY
    · apply associativity_overMorphism_heq_of_left_heq
      · exact hY
      · rfl
      · simp [LocallyDefinedHomRepresentative.compositionCoverToRight, Category.assoc]
  exact congr_arg_heq (fun A : γ.cover.Arrow => ((γ.family A).down)) hA

/-- The triple cover maps to the transported left-associated representative cover, the left leg
of the common-refinement proof for associativity. -/
noncomputable def associativityTripleCoverToCastLeftHom
    {X : FibredCategoryOver.{u, v, uX, vX} C} {w x y z : X.S}
    {f : X.p.obj w ⟶ X.p.obj x}
    {g : X.p.obj x ⟶ X.p.obj y}
    {k : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (γ : LocallyDefinedHomRepresentativeOver (J := J) X k) :
    associativityTripleCover (J := J) α β γ ⟶
      (castBase (J := J)
        (by simp [Category.assoc] : (f ≫ g) ≫ k = f ≫ (g ≫ k))
        (composeOver (J := J) (composeOver (J := J) α β) γ)).cover :=
  coverHomCastBase (J := J)
    (by simp [Category.assoc] : (f ≫ g) ≫ k = f ≫ (g ≫ k))
    (composeOver (J := J) (composeOver (J := J) α β) γ)

/-- The triple cover maps to the right-associated representative cover, the right leg of the
common-refinement proof for associativity. -/
noncomputable def associativityTripleCoverToRightHom
    {X : FibredCategoryOver.{u, v, uX, vX} C} {w x y z : X.S}
    {f : X.p.obj w ⟶ X.p.obj x}
    {g : X.p.obj x ⟶ X.p.obj y}
    {k : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (γ : LocallyDefinedHomRepresentativeOver (J := J) X k) :
    associativityTripleCover (J := J) α β γ ⟶
      (composeOver (J := J) α (composeOver (J := J) β γ)).cover :=
  assocCoverLeftToRightHom (J := J) α β γ

end LocallyDefinedHomRepresentativeOver
end FibredCategoryMor

end CategoryTheory
