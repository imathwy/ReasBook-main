import StacksProject_2024.Chap20.Remark_20_28_3

open CategoryTheory
open ComplexShape
open AlgebraicGeometry
open scoped RingedSpace.Hom RingedSpaceDerivedPullback RingedSpaceDerivedPushforward

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

attribute [local instance] HasDerivedCategory.standard

section Composition

variable {X' X Y' Y Z' Z : RingedSpace.{u}}
variable (k : X' ⟶ X) (f' : X' ⟶ Y') (l : Y' ⟶ Y) (f : X ⟶ Y)
variable (m : Z' ⟶ Z) (g' : Y' ⟶ Z') (g : Y ⟶ Z)

variable [(k^*).Additive]
variable [(f' _*).Additive]
variable [(l^*).Additive]
variable [(f _*).Additive]
variable [(m^*).Additive]
variable [(g' _*).Additive]
variable [(g _*).Additive]
variable [(g'^*).Additive]
variable [(g^*).Additive]
variable [(f'^*).Additive]
variable [(f^*).Additive]
variable [((f' ≫ g')^*).Additive]
variable [((f ≫ g)^*).Additive]

variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived k) (ModuleQis X)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived l) (ModuleQis Y)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived m) (ModuleQis Z)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g') (ModuleQis Z')]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g) (ModuleQis Z)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f') (ModuleQis Y')]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]

/- Domain-style sampling for Remark 20.28.4:
- primary domain: unbounded derived base change for vertically composable squares of ringed
  spaces;
- sampled owner declarations:
  `IsUnboundedDerivedBaseChangeMap`,
  `unboundedDerivedBaseChangeMap`,
  `derivedPushforwardCompIsoOfAdjunctions`,
  `unboundedDerivedBaseChangeMap_spec`;
- best owner abstraction:
  `source-facing`: the source theorem that the composite of the two inner base-change maps is the
    base-change map for the outer rectangle;
  `core/canonical`: `IsUnboundedDerivedBaseChangeMap`;
  `bridge/view`: the composed pullback comparison `outerRectanglePullbackIso` together with the
    chosen pushforward comparison `derivedPushforwardCompIsoOfAdjunctions`.

Primitive data are the two chosen pullback comparison isomorphisms for the inner squares, the
comparison isomorphisms for pullback and pushforward along composites, the chosen adjunctions, and
the two inner base-change maps. The deleted `outerRectangleBaseChangeMap` wrapper was only derived
syntax for the explicit composite already appearing in the source statement, so the public API
should expose that composite directly and reserve named bridges only for the reusable outer
pullback comparison and the chosen pushforward comparison.
-/

/-- The pullback comparison isomorphisms for the two inner squares, together with the chosen
pullback comparison isomorphisms for the vertical composites, combine to the pullback comparison
for the outer rectangle. -/
noncomputable abbrev outerRectanglePullbackIso
    (hpull₁ : L(l)^* ⋙ L(f')^* ≅ L(f)^* ⋙ L(k)^*)
    (hpull₂ : L(m)^* ⋙ L(g')^* ≅ L(g)^* ⋙ L(l)^*)
    (hpull_fg : L(g)^* ⋙ L(f)^* ≅ modulePullbackDerived (f ≫ g))
    (hpull_f'g' : L(g')^* ⋙ L(f')^* ≅ modulePullbackDerived (f' ≫ g')) :
    L(m)^* ⋙ modulePullbackDerived (f' ≫ g') ≅ modulePullbackDerived (f ≫ g) ⋙ L(k)^* :=
  Functor.isoWhiskerLeft (L(m)^*) hpull_f'g'.symm ≪≫
    Functor.associator (L(m)^*) (L(g')^*) (L(f')^*) ≪≫
    Functor.isoWhiskerRight hpull₂ (L(f')^*) ≪≫
    Functor.associator (L(g)^*) (L(l)^*) (L(f')^*) ≪≫
    Functor.isoWhiskerLeft (L(g)^*) hpull₁ ≪≫
    (Functor.associator (L(g)^*) (L(f)^*) (L(k)^*)).symm ≪≫
    Functor.isoWhiskerRight hpull_fg (L(k)^*)

/-- The pushforward comparison induced by chosen adjunctions for `f`, `g`, and `f ≫ g`, together
with a chosen pullback comparison `L(g)^* ⋙ L(f)^* ≅ L((f ≫ g))^*`. -/
noncomputable abbrev derivedPushforwardCompIsoOfAdjunctions
    (adjf : L(f)^* ⊣ R(f)_*)
    (adjg : L(g)^* ⊣ R(g)_*)
    (adjfg : L((f ≫ g))^* ⊣ R((f ≫ g))_*)
    (hpull_fg : L(g)^* ⋙ L(f)^* ≅ L((f ≫ g))^*) :
    R(f)_* ⋙ R(g)_* ≅ R((f ≫ g))_* :=
  ((adjg.comp adjf).ofNatIsoLeft hpull_fg).rightAdjointUniq adjfg

-- Proof sketch: first rewrite the chosen inner morphisms to the canonical base-change maps using
-- Remark `20.28.3`, then transpose the resulting vertical composite across the outer adjunction.
-- The remaining normalization is the source-faithful counit computation for the outer rectangle.
/-- Helper for Remark 20.28.4: after replacing the inner maps by the canonical maps of Remark
20.28.3, the resulting vertical composite should satisfy the outer-rectangle mate formula. -/
private theorem verticalComposite_canonical_isUnboundedDerivedBaseChangeMap
    (adjf : L(f)^* ⊣ R(f)_*)
    (adjf' : L(f')^* ⊣ R(f')_*)
    (adjg : L(g)^* ⊣ R(g)_*)
    (adjg' : L(g')^* ⊣ R(g')_*)
    (adjfg : L((f ≫ g))^* ⊣ R((f ≫ g))_*)
    (adjf'g' : L((f' ≫ g'))^* ⊣ R((f' ≫ g'))_*)
    (hpull₁ : L(l)^* ⋙ L(f')^* ≅ L(f)^* ⋙ L(k)^*)
    (hpull₂ : L(m)^* ⋙ L(g')^* ≅ L(g)^* ⋙ L(l)^*)
    (hpull_fg : L(g)^* ⋙ L(f)^* ≅ L((f ≫ g))^*)
    (hpull_f'g' : L(g')^* ⋙ L(f')^* ≅ L((f' ≫ g'))^*)
    (K : DerivedCategory (RingedSpace.Modules X)) :
    IsUnboundedDerivedBaseChangeMap
      k
      (f' ≫ g')
      (f ≫ g)
      m
      adjfg
      adjf'g'
      (outerRectanglePullbackIso k f' l f m g' g hpull₁ hpull₂ hpull_fg hpull_f'g')
      K
      ((Functor.isoWhiskerRight
          (derivedPushforwardCompIsoOfAdjunctions f g adjf adjg adjfg hpull_fg)
          (L(m)^*)).inv.app K ≫
        unboundedDerivedBaseChangeMap l g' g m adjg adjg' hpull₂ ((R(f)_*).obj K) ≫
        (R(g')_*).map (unboundedDerivedBaseChangeMap k f' f l adjf adjf' hpull₁ K) ≫
      (derivedPushforwardCompIsoOfAdjunctions
          f' g' adjf' adjg' adjf'g' hpull_f'g').hom.app ((L(k)^*).obj K)) := by
  -- Route correction: the remaining issue is not the inner-map rewriting but the outer
  -- coherence between the canonical pushforward comparison and the arbitrary outer comparison
  -- data `hpull_fg`, `hpull_f'g'`, `adjfg`, and `adjf'g'`.
  rw [IsUnboundedDerivedBaseChangeMap]
  sorry

-- Proof sketch: rewrite the source and target of the composite
-- `Lm^* Rg_* Rf_* K ⟶ Rg'_* Ll^* Rf_* K ⟶ Rg'_* Rf'_* Lk^* K`
-- using the derived-pushforward comparison isomorphisms for `f ≫ g` and `f' ≫ g'`. After
-- transposing along `L(f' ≫ g')^* ⊣ R(f' ≫ g')_*`, the resulting morphism is exactly the outer
-- pullback comparison followed by the counit for `L(f ≫ g)^* ⊣ R(f ≫ g)_*`.
/-- Remark 20.28.4: for a commutative diagram of ringed spaces
`X' ⟶ X`, `Y' ⟶ Y`, `Z' ⟶ Z` with vertical maps `f' : X' ⟶ Y'`, `f : X ⟶ Y`,
`g' : Y' ⟶ Z'`, and `g : Y ⟶ Z`, if `τ₁` and `τ₂` are the base-change maps for the upper and
lower squares as in Remark 20.28.3, then the composite
`Lm^* Rg_* Rf_* K ⟶ Rg'_* Ll^* Rf_* K ⟶ Rg'_* Rf'_* Lk^* K` is the base-change map for the
outer rectangle. -/
@[stacks 0ATL]
theorem verticalComposite_isUnboundedDerivedBaseChangeMap
    (adjf : L(f)^* ⊣ R(f)_*)
    (adjf' : L(f')^* ⊣ R(f')_*)
    (adjg : L(g)^* ⊣ R(g)_*)
    (adjg' : L(g')^* ⊣ R(g')_*)
    (adjfg : L((f ≫ g))^* ⊣ R((f ≫ g))_*)
    (adjf'g' : L((f' ≫ g'))^* ⊣ R((f' ≫ g'))_*)
    (hpull₁ : L(l)^* ⋙ L(f')^* ≅ L(f)^* ⋙ L(k)^*)
    (hpull₂ : L(m)^* ⋙ L(g')^* ≅ L(g)^* ⋙ L(l)^*)
    (hpull_fg : L(g)^* ⋙ L(f)^* ≅ L((f ≫ g))^*)
    (hpull_f'g' : L(g')^* ⋙ L(f')^* ≅ L((f' ≫ g'))^*)
    (K : DerivedCategory (RingedSpace.Modules X))
    (τ₁ : derivedBaseChangeSource f l K ⟶ derivedBaseChangeTarget k f' K)
    (hτ₁ : IsUnboundedDerivedBaseChangeMap k f' f l adjf adjf' hpull₁ K τ₁)
    (τ₂ : derivedBaseChangeSource g m ((R(f)_*).obj K) ⟶
      derivedBaseChangeTarget l g' ((R(f)_*).obj K))
    (hτ₂ : IsUnboundedDerivedBaseChangeMap l g' g m adjg adjg' hpull₂
      ((R(f)_*).obj K) τ₂) :
    IsUnboundedDerivedBaseChangeMap
      k
      (f' ≫ g')
      (f ≫ g)
      m
      adjfg
      adjf'g'
      (outerRectanglePullbackIso k f' l f m g' g hpull₁ hpull₂ hpull_fg hpull_f'g')
      K
      ((Functor.isoWhiskerRight
          (derivedPushforwardCompIsoOfAdjunctions f g adjf adjg adjfg hpull_fg)
          (L(m)^*)).inv.app K ≫
        τ₂ ≫
        (R(g')_*).map τ₁ ≫
        (derivedPushforwardCompIsoOfAdjunctions
          f' g' adjf' adjg' adjf'g' hpull_f'g').hom.app ((L(k)^*).obj K)) := by
  -- First replace the chosen inner maps by the canonical owners from Remark `20.28.3`.
  simpa [eq_unboundedDerivedBaseChangeMap k f' f l adjf adjf' hpull₁ K τ₁ hτ₁,
    eq_unboundedDerivedBaseChangeMap l g' g m adjg adjg' hpull₂ ((R(f)_*).obj K) τ₂ hτ₂] using
    verticalComposite_canonical_isUnboundedDerivedBaseChangeMap
      k f' l f m g' g
      adjf adjf' adjg adjg' adjfg adjf'g'
      hpull₁ hpull₂ hpull_fg hpull_f'g' K

end Composition

end AlgebraicGeometry.RingedSpace
