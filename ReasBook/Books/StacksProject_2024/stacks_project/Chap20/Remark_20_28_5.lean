import StacksProject_2024.Chap20.Remark_20_28_4

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open ComplexShape
open scoped RingedSpace.Hom RingedSpaceDerivedPullback RingedSpaceDerivedPushforward

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

attribute [local instance] HasDerivedCategory.standard

section

variable {X'' X' X Y'' Y' Y : RingedSpace.{u}}
variable (g' : X'' ⟶ X') (g : X' ⟶ X)
variable (f'' : X'' ⟶ Y'') (f' : X' ⟶ Y') (f : X ⟶ Y)
variable (h' : Y'' ⟶ Y') (h : Y' ⟶ Y)

variable [(g'^*).Additive]
variable [(g^*).Additive]
variable [((g' ≫ g)^*).Additive]
variable [(h'^*).Additive]
variable [(h^*).Additive]
variable [((h' ≫ h)^*).Additive]
variable [(f''^*).Additive]
variable [(f'^*).Additive]
variable [(f^*).Additive]
variable [(f'' _*).Additive]
variable [(f' _*).Additive]
variable [(f _*).Additive]

variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g') (ModuleQis X')]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g) (ModuleQis X)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived (g' ≫ g)) (ModuleQis X)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived h') (ModuleQis Y')]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived h) (ModuleQis Y)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived (h' ≫ h)) (ModuleQis Y)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f'') (ModuleQis Y'')]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f') (ModuleQis Y')]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]

/- Domain-style sampling for Remark 20.28.5:
- primary domain: unbounded derived base change for two horizontally composable squares of ringed
  spaces;
- sampled owner declarations:
  `IsUnboundedDerivedBaseChangeMap`,
  `unboundedDerivedBaseChangeMap`,
  `outerRectanglePullbackIso`,
  `derivedBaseChangeSource`,
  `derivedBaseChangeTarget`;
- best owner abstraction:
  `source-facing`: the horizontal-composition statement for base-change maps;
  `core/canonical`: `IsUnboundedDerivedBaseChangeMap` together with the pullback-comparison owner
    `outerRectanglePullbackIso` from Remark `20.28.4`;
  `bridge/view`: the explicit composite morphism obtained by transporting `η₀` and `η₁` through
    `hcomp` and `gcomp`.

Primitive data here are the two square comparison isomorphisms `hpull₀`, `hpull₁`, the composite
pullback identifications `hcomp`, `gcomp`, and the two base-change maps `η₀`, `η₁`. The deleted
horizontal wrapper abbreviations were only derived formulas, so the public theorem surface should
reuse the chapter owners directly instead of introducing parallel local names.
-/

-- Proof sketch: expand the outer pullback commutativity isomorphism by composing the two square
-- isomorphisms with associators, then transpose the composite morphism along the adjunction
-- `L(f'')^* ⊣ R(f'')_*`. The hypotheses identifying `η₀` and `η₁` as base-change maps reduce the
-- transpose to the counit expression for the outer rectangle.
/-- Remark 20.28.5: for two composable squares of ringed spaces, if `η₀` and `η₁` are
unbounded derived base-change maps for the two inner squares, then their horizontal composite is
an unbounded derived base-change map for the outer rectangle. -/
@[stacks 0ATM]
theorem horizontalComposite_isUnboundedDerivedBaseChangeMap
    (hpull₀ : L(h)^* ⋙ L(f')^* ≅ L(f)^* ⋙ L(g)^*)
    (hpull₁ : L(h')^* ⋙ L(f'')^* ≅ L(f')^* ⋙ L(g')^*)
    (hcomp : L((h' ≫ h))^* ≅ L(h)^* ⋙ L(h')^*)
    (gcomp : L((g' ≫ g))^* ≅ L(g)^* ⋙ L(g')^*)
    (adj_f : L(f)^* ⊣ R(f)_*)
    (adj_f' : L(f')^* ⊣ R(f')_*)
    (adj_f'' : L(f'')^* ⊣ R(f'')_*)
    (K : DerivedCategory (RingedSpace.Modules X))
    (η₀ : derivedBaseChangeSource f h K ⟶ derivedBaseChangeTarget g f' K)
    (η₁ :
      derivedBaseChangeSource f' h' ((L(g)^*).obj K) ⟶
        derivedBaseChangeTarget g' f'' ((L(g)^*).obj K))
    (hη₀ : IsUnboundedDerivedBaseChangeMap g f' f h adj_f adj_f' hpull₀ K η₀)
    (hη₁ :
      IsUnboundedDerivedBaseChangeMap g' f'' f' h' adj_f' adj_f'' hpull₁
        ((L(g)^*).obj K) η₁) :
    IsUnboundedDerivedBaseChangeMap
      (g' ≫ g)
      f''
      f
      (h' ≫ h)
      adj_f
      adj_f''
      ((outerRectanglePullbackIso f'' g' f' h' f g h hpull₁.symm hpull₀.symm hcomp.symm
        gcomp.symm).symm)
      K
      ((hcomp.hom.app ((R(f)_*).obj K)) ≫
        (L(h')^*).map η₀ ≫
        η₁ ≫
        (R(f'')_*).map (gcomp.inv.app K)) := by
  -- The statement/API surface is the point of this file; the mate computation is deferred.
  sorry

/-- Companion canonical form of Remark 20.28.5: the canonical base-change maps of Remark 20.28.3
for the two inner squares compose to the canonical base-change map for the outer rectangle. -/
theorem horizontalComposite_unboundedDerivedBaseChangeMap_spec
    (hpull₀ : L(h)^* ⋙ L(f')^* ≅ L(f)^* ⋙ L(g)^*)
    (hpull₁ : L(h')^* ⋙ L(f'')^* ≅ L(f')^* ⋙ L(g')^*)
    (hcomp : L((h' ≫ h))^* ≅ L(h)^* ⋙ L(h')^*)
    (gcomp : L((g' ≫ g))^* ≅ L(g)^* ⋙ L(g')^*)
    (adj_f : L(f)^* ⊣ R(f)_*)
    (adj_f' : L(f')^* ⊣ R(f')_*)
    (adj_f'' : L(f'')^* ⊣ R(f'')_*)
    (K : DerivedCategory (RingedSpace.Modules X)) :
    ((hcomp.hom.app ((R(f)_*).obj K)) ≫
      (L(h')^*).map (unboundedDerivedBaseChangeMap g f' f h adj_f adj_f' hpull₀ K) ≫
      unboundedDerivedBaseChangeMap g' f'' f' h' adj_f' adj_f'' hpull₁
        ((L(g)^*).obj K) ≫
      (R(f'')_*).map (gcomp.inv.app K)) =
      unboundedDerivedBaseChangeMap
        (g' ≫ g)
        f''
        f
        (h' ≫ h)
        adj_f
        adj_f''
        ((outerRectanglePullbackIso f'' g' f' h' f g h hpull₁.symm hpull₀.symm hcomp.symm
          gcomp.symm).symm)
        K := by
  exact
    eq_unboundedDerivedBaseChangeMap
      (g' ≫ g)
      f''
      f
      (h' ≫ h)
      adj_f
      adj_f''
      ((outerRectanglePullbackIso f'' g' f' h' f g h hpull₁.symm hpull₀.symm hcomp.symm
        gcomp.symm).symm)
      K
      ((hcomp.hom.app ((R(f)_*).obj K)) ≫
        (L(h')^*).map (unboundedDerivedBaseChangeMap g f' f h adj_f adj_f' hpull₀ K) ≫
        unboundedDerivedBaseChangeMap g' f'' f' h' adj_f' adj_f'' hpull₁
          ((L(g)^*).obj K) ≫
        (R(f'')_*).map (gcomp.inv.app K))
      (horizontalComposite_isUnboundedDerivedBaseChangeMap
        g' g f'' f' f h' h
        hpull₀ hpull₁ hcomp gcomp adj_f adj_f' adj_f'' K
        (unboundedDerivedBaseChangeMap g f' f h adj_f adj_f' hpull₀ K)
        (unboundedDerivedBaseChangeMap g' f'' f' h' adj_f' adj_f'' hpull₁
          ((L(g)^*).obj K))
        (unboundedDerivedBaseChangeMap_spec g f' f h adj_f adj_f' hpull₀ K)
        (unboundedDerivedBaseChangeMap_spec g' f'' f' h' adj_f' adj_f'' hpull₁
          ((L(g)^*).obj K)))

end

end AlgebraicGeometry.RingedSpace
