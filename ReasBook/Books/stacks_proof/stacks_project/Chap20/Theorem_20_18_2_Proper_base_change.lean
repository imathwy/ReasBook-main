import Mathlib
import stacks_proof.stacks_project.Chap13.Definition_13_11_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits ComplexShape
open scoped CategoryTheory

noncomputable section

universe u

namespace Stacks.Chap20.Thm18_2

/-- Sheaves of abelian groups on a topological space `X`, the category in which the
cohomology theory of this section takes place. -/
abbrev ShAb (X : TopCat.{u}) := TopCat.Sheaf AddCommGrpCat.{u} X

/- Domain-style sampling:
- primary domain: the six-operations formalism for sheaves of abelian groups on topological
  spaces, restricted here to the four functors `Rf_*`, `Rg_*`, `g^{-1}`, `g'^{-1}` attached to a
  cartesian square and the base change map relating them;
- sampled owner declarations:
  `TopCat.Sheaf.pushforward`, `TopCat.Sheaf.pullback`,
  `TopCat.Sheaf.pullbackPushforwardAdjunction`,
  `Functor.totalRightDerived`, `Functor.mapDerivedCategory`,
  `CategoryTheory.mateEquiv`, `CategoryTheory.TwoSquare`,
  `DerivedCategory.TStructure.t.plus`;
- owner abstraction:
  `source-facing`: the topological proper base change statement (tag 09V6);
  `core/canonical`: the derived pushforward `totalRightDerived` of the additive direct image
    and the derived inverse image `mapDerivedCategory` of the exact pullback;
  `bridge/view`: the base change natural transformation as the mate (`mateEquiv`) of the
    canonical composition comparison `R(f∘g')_* ⟶ R(g∘f')_*`. -/

/-- The right derived pushforward `Rf_* : D(\mathrm{Sh}(X)) ⥤ D(\mathrm{Sh}(Y))` attached to a
continuous map `f : X ⟶ Y`. It is the total right derived functor of the additive direct image
`TopCat.Sheaf.pushforward AddCommGrpCat.{u} f`, computed through the canonical localization functor
`DerivedCategory.Q` and the quasi-isomorphisms of cochain complexes. -/
def derivedPushforward {X Y : TopCat.{u}} (f : X ⟶ Y)
    [HasDerivedCategory.{u} (ShAb X)] [HasDerivedCategory.{u} (ShAb Y)]
    [(TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).Additive]
    [(((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex (up ℤ)) ⋙
        DerivedCategory.Q).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso (ShAb X) (up ℤ))] :
    D((ShAb X)) ⥤ D((ShAb Y)) :=
  Functor.totalRightDerived
    (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex (up ℤ)) ⋙
      DerivedCategory.Q)
    DerivedCategory.Q (HomologicalComplex.quasiIso (ShAb X) (up ℤ))

/-- The derived inverse image `g^{-1} : D(\mathrm{Sh}(Y)) ⥤ D(\mathrm{Sh}(Y'))` attached to a
continuous map `g : Y' ⟶ Y`. The inverse image `TopCat.Sheaf.pullback AddCommGrpCat.{u} g` is exact
(it preserves finite limits and finite colimits), so it descends to the derived category via
`Functor.mapDerivedCategory`. -/
def derivedInverseImage {Y Y' : TopCat.{u}} (g : Y' ⟶ Y)
    [HasDerivedCategory.{u} (ShAb Y)] [HasDerivedCategory.{u} (ShAb Y')]
    [(TopCat.Sheaf.pullback AddCommGrpCat.{u} g).Additive]
    [PreservesFiniteLimits (TopCat.Sheaf.pullback AddCommGrpCat.{u} g)]
    [PreservesFiniteColimits (TopCat.Sheaf.pullback AddCommGrpCat.{u} g)] :
    D((ShAb Y)) ⥤ D((ShAb Y')) :=
  (TopCat.Sheaf.pullback AddCommGrpCat.{u} g).mapDerivedCategory

section BaseChange

variable {X Y Y' : TopCat.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)

/-- The fibre product `X' = Y' ×_Y X` of the cartesian square, formed in `TopCat`. -/
abbrev pullbackSpace : TopCat.{u} := Limits.pullback g f

/-- The second projection `g' : X' = Y' ×_Y X ⟶ X` of the cartesian square. -/
abbrev pullbackToX : pullbackSpace f g ⟶ X := pullback.snd g f

/-- The first projection `f' : X' = Y' ×_Y X ⟶ Y'` of the cartesian square. -/
abbrev pullbackToY' : pullbackSpace f g ⟶ Y' := pullback.fst g f

/-- The base change natural transformation `g^{-1} ∘ Rf_* ⟶ Rf'_* ∘ (g')^{-1}` of Lemma 20.17.1
attached to the cartesian square `X' = Y' ×_Y X`.

It is constructed as the mate (via `mateEquiv`) of the canonical comparison
`τ : R(f∘g')_* ⟶ R(g∘f')_*` along the two derived adjunctions
`adj₁ : (g')^{-1} ⊣ Rg'_*` and `adj₂ : g^{-1} ⊣ Rg_*`.  Concretely
`((mateEquiv adj₁ adj₂).symm τ).app E` is a morphism
`(Rf_* ⋙ g^{-1}).obj E ⟶ ((g')^{-1} ⋙ Rf'_*).obj E`, i.e. `g^{-1}Rf_*E ⟶ Rf'_*(g')^{-1}E`.

The comparison `τ` together with the derived adjunctions are supplied as the canonical context
data of the situation: they are the standard structural inputs (functoriality of derived
pushforward along the equal composites `f∘g' = g∘f'` and the derived inverse-image/pushforward
adjunctions), which Mathlib does not yet package as a single derived-functor calculus. -/
def baseChangeMap
    [HasDerivedCategory.{u} (ShAb X)] [HasDerivedCategory.{u} (ShAb Y)]
    [HasDerivedCategory.{u} (ShAb Y')]
    [HasDerivedCategory.{u} (ShAb (pullbackSpace f g))]
    [(TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).Additive]
    [(((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex (up ℤ)) ⋙
        DerivedCategory.Q).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso (ShAb X) (up ℤ))]
    [(TopCat.Sheaf.pushforward AddCommGrpCat.{u} (pullbackToY' f g)).Additive]
    [(((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (pullbackToY' f g)).mapHomologicalComplex
          (up ℤ)) ⋙ DerivedCategory.Q).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso (ShAb (pullbackSpace f g)) (up ℤ))]
    [(TopCat.Sheaf.pushforward AddCommGrpCat.{u} g).Additive]
    [(((TopCat.Sheaf.pushforward AddCommGrpCat.{u} g).mapHomologicalComplex (up ℤ)) ⋙
        DerivedCategory.Q).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso (ShAb Y') (up ℤ))]
    [(TopCat.Sheaf.pushforward AddCommGrpCat.{u} (pullbackToX f g)).Additive]
    [(((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (pullbackToX f g)).mapHomologicalComplex
          (up ℤ)) ⋙ DerivedCategory.Q).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso (ShAb (pullbackSpace f g)) (up ℤ))]
    [(TopCat.Sheaf.pullback AddCommGrpCat.{u} g).Additive]
    [PreservesFiniteLimits (TopCat.Sheaf.pullback AddCommGrpCat.{u} g)]
    [PreservesFiniteColimits (TopCat.Sheaf.pullback AddCommGrpCat.{u} g)]
    [(TopCat.Sheaf.pullback AddCommGrpCat.{u} (pullbackToX f g)).Additive]
    [PreservesFiniteLimits (TopCat.Sheaf.pullback AddCommGrpCat.{u} (pullbackToX f g))]
    [PreservesFiniteColimits (TopCat.Sheaf.pullback AddCommGrpCat.{u} (pullbackToX f g))]
    (adj₁ : derivedInverseImage (pullbackToX f g) ⊣ derivedPushforward (pullbackToX f g))
    (adj₂ : derivedInverseImage g ⊣ derivedPushforward g)
    (τ : TwoSquare (derivedPushforward (pullbackToX f g)) (derivedPushforward (pullbackToY' f g))
      (derivedPushforward f) (derivedPushforward g)) :
    TwoSquare (derivedPushforward f) (derivedInverseImage (pullbackToX f g))
      (derivedInverseImage g) (derivedPushforward (pullbackToY' f g)) :=
  (mateEquiv adj₁ adj₂).symm τ

end BaseChange

/-- **Theorem 20.18.2 (Proper base change in topology, tag 09V6).**

Let
```
   X' --g'--> X
   |          |
   f'         f
   v          v
   Y' --g---> Y
```
be a cartesian square of topological spaces, with `X' = Y' ×_Y X`, `g' = pr_X`, `f' = pr_{Y'}`,
and assume `f` is proper.  Let `E ∈ D⁺(X)`.  Then the base change map
`g^{-1}Rf_*E ⟶ Rf'_*(g')^{-1}E` of Lemma 20.17.1 is an isomorphism in `D⁺(Y')`.

We phrase the base change map as `baseChangeMap`, the mate of the canonical comparison
`τ : R(f∘g')_* ⟶ R(g∘f')_*` along the derived adjunctions `adj₁`, `adj₂`; these structural inputs
are taken as the canonical context data of the situation (see `baseChangeMap`). The conclusion is
that this natural transformation is an isomorphism at the bounded-below object `E`. -/
theorem proper_base_change
    {X Y Y' : TopCat.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (hf : IsProperMap (f : X → Y))
    [HasDerivedCategory.{u} (ShAb X)] [HasDerivedCategory.{u} (ShAb Y)]
    [HasDerivedCategory.{u} (ShAb Y')]
    [HasDerivedCategory.{u} (ShAb (pullbackSpace f g))]
    [(TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).Additive]
    [(((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex (up ℤ)) ⋙
        DerivedCategory.Q).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso (ShAb X) (up ℤ))]
    [(TopCat.Sheaf.pushforward AddCommGrpCat.{u} (pullbackToY' f g)).Additive]
    [(((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (pullbackToY' f g)).mapHomologicalComplex
          (up ℤ)) ⋙ DerivedCategory.Q).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso (ShAb (pullbackSpace f g)) (up ℤ))]
    [(TopCat.Sheaf.pushforward AddCommGrpCat.{u} g).Additive]
    [(((TopCat.Sheaf.pushforward AddCommGrpCat.{u} g).mapHomologicalComplex (up ℤ)) ⋙
        DerivedCategory.Q).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso (ShAb Y') (up ℤ))]
    [(TopCat.Sheaf.pushforward AddCommGrpCat.{u} (pullbackToX f g)).Additive]
    [(((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (pullbackToX f g)).mapHomologicalComplex
          (up ℤ)) ⋙ DerivedCategory.Q).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso (ShAb (pullbackSpace f g)) (up ℤ))]
    [(TopCat.Sheaf.pullback AddCommGrpCat.{u} g).Additive]
    [PreservesFiniteLimits (TopCat.Sheaf.pullback AddCommGrpCat.{u} g)]
    [PreservesFiniteColimits (TopCat.Sheaf.pullback AddCommGrpCat.{u} g)]
    [(TopCat.Sheaf.pullback AddCommGrpCat.{u} (pullbackToX f g)).Additive]
    [PreservesFiniteLimits (TopCat.Sheaf.pullback AddCommGrpCat.{u} (pullbackToX f g))]
    [PreservesFiniteColimits (TopCat.Sheaf.pullback AddCommGrpCat.{u} (pullbackToX f g))]
    (adj₁ : derivedInverseImage (pullbackToX f g) ⊣ derivedPushforward (pullbackToX f g))
    (adj₂ : derivedInverseImage g ⊣ derivedPushforward g)
    (τ : TwoSquare (derivedPushforward (pullbackToX f g)) (derivedPushforward (pullbackToY' f g))
      (derivedPushforward f) (derivedPushforward g))
    [IsIso τ.natTrans]
    (E : D((ShAb X)))
    (hE : (DerivedCategory.TStructure.t.plus : ObjectProperty (D((ShAb X)))) E) :
    IsIso ((baseChangeMap f g adj₁ adj₂ τ).natTrans.app E) := sorry

end Stacks.Chap20.Thm18_2
