import StacksProject_2024.stacks_project.Chap21.Lemma_21_19_2
import StacksProject_2024.stacks_project.Chap21.Remark_21_19_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape
open scoped RingedSite.Hom RingedSiteDerived

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace RingedSite.Hom

/- Domain-style sampling for Remark 21.19.4:
- primary domain: unbounded derived base-change morphisms for module sheaves on ringed sites and
  their composition across vertically composable squares;
- sampled owner declarations:
  `RingedSite.Hom.IsUnboundedBaseChangeMap`,
  `RingedSite.Hom.unboundedBaseChangeMap`,
  `RingedSite.Hom.modulePullbackDerived_pushforward_adjunction`,
  `CategoryTheory.IsDerivedBaseChangeMap`,
  `CategoryTheory.derivedBaseChangeMap`,
  `RingedSite.Hom.modulePushforwardDerived_compIso`;
- best owner abstraction: the source-facing owners are the ringed-site specialization
  `unboundedBaseChangeMap` and its proof-oriented companion `IsUnboundedBaseChangeMap` from Remark
  `21.19.3`; the core categorical owner remains `derivedBaseChangeMap`; the chapter's canonical
  adjunction owner is `modulePullbackDerived_pushforward_adjunction`, and the canonical
  pushforward-composition comparison is already owned by `modulePushforwardDerived_compIso`; the
  only new local bridge datum that should be built here is the outer pullback comparison for the
  composite rectangle;
- primitive data: the six ringed-site morphisms, the two square pullback commutativity
  isomorphisms, the two pullback-composition isomorphisms, and the two square-wise base-change
  morphisms;
- derived API: the outer-rectangle pullback bridge, the proof-oriented composition criterion
  `verticalComposite_isUnboundedBaseChangeMap`, and the source-facing canonical equality
  `verticalComposite_unboundedBaseChangeMap_spec`.

Source/core/bridge triage:
- `source-facing`: the canonical-map equality
  `verticalComposite_unboundedBaseChangeMap_spec`;
- `core/canonical`: `CategoryTheory.derivedBaseChangeMap`, `CategoryTheory.IsDerivedBaseChangeMap`,
  and `modulePullbackDerived_pushforward_adjunction` from Remark `21.19.3` and Lemma `21.19.1`,
  together with
  `modulePushforwardDerived_compIso` from Lemma `21.19.2`;
- `bridge/view`: `verticalOuterRectanglePullbackIso`, which packages the outer pullback
  comparison induced by the two inner squares and the pullback-composition isomorphisms, together
  with the private derived-level helper used to prove
  `verticalComposite_isUnboundedBaseChangeMap`. -/

section

variable {B' B C' C D' D : RingedSite.{u, v}}
variable (k : B' ⟶ B) (f' : B' ⟶ C')
variable (f : B ⟶ C) (l : C' ⟶ C)
variable (g' : C' ⟶ D') (g : C ⟶ D)
variable (m : D' ⟶ D)

variable [HasWeakSheafify B.siteTopology AddCommGrpCat.{max u v}]
variable [HasWeakSheafify B'.siteTopology AddCommGrpCat.{max u v}]
variable [HasWeakSheafify C.siteTopology AddCommGrpCat.{max u v}]
variable [HasWeakSheafify C'.siteTopology AddCommGrpCat.{max u v}]
variable [HasWeakSheafify D'.siteTopology AddCommGrpCat.{max u v}]

variable [B.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [B'.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [C.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [C'.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [D'.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

variable [(PresheafOfModules.pushforward.{max u v} f.structureSheafMap.hom).IsRightAdjoint]
variable [(PresheafOfModules.pushforward.{max u v} f'.structureSheafMap.hom).IsRightAdjoint]
variable [(PresheafOfModules.pushforward.{max u v} g.structureSheafMap.hom).IsRightAdjoint]
variable [(PresheafOfModules.pushforward.{max u v} g'.structureSheafMap.hom).IsRightAdjoint]
variable [(PresheafOfModules.pushforward.{max u v} k.structureSheafMap.hom).IsRightAdjoint]
variable [(PresheafOfModules.pushforward.{max u v} l.structureSheafMap.hom).IsRightAdjoint]
variable [(PresheafOfModules.pushforward.{max u v} m.structureSheafMap.hom).IsRightAdjoint]
variable [(PresheafOfModules.pushforward.{max u v} (f ≫ g).structureSheafMap.hom).IsRightAdjoint]
variable [(PresheafOfModules.pushforward.{max u v} (f' ≫ g').structureSheafMap.hom).IsRightAdjoint]

variable [f.modulePushforward.Additive]
variable [f'.modulePushforward.Additive]
variable [g.modulePushforward.Additive]
variable [g'.modulePushforward.Additive]
variable [(modulePushforward (f ≫ g)).Additive]
variable [(modulePushforward (f' ≫ g')).Additive]

variable [(f^*).Additive]
variable [(f'^*).Additive]
variable [(g^*).Additive]
variable [(g'^*).Additive]
variable [(k^*).Additive]
variable [(l^*).Additive]
variable [(m^*).Additive]
variable [((f ≫ g)^*).Additive]
variable [((f' ≫ g')^*).Additive]

variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis B)]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f') (ModuleQis B')]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived g) (ModuleQis C)]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived g') (ModuleQis C')]
variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived (f ≫ g)) (ModuleQis B)]
variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived (f' ≫ g')) (ModuleQis B')]

variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis C)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f') (ModuleQis C')]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g) (ModuleQis D)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g') (ModuleQis D')]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived k) (ModuleQis B)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived l) (ModuleQis C)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived m) (ModuleQis D)]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived (f ≫ g)) (ModuleQis D)]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived (f' ≫ g')) (ModuleQis D')]

/-- The pullback comparisons for two vertically composable squares, together with the chosen
pullback-composition isomorphisms, induce the pullback comparison for the outer rectangle. -/
noncomputable abbrev verticalOuterRectanglePullbackIso
    (hpull_top :
      L(l)^* ⋙ L(f')^* ≅ L(f)^* ⋙ L(k)^*)
    (hpull_bottom :
      L(m)^* ⋙ L(g')^* ≅ L(g)^* ⋙ L(l)^*)
    (hpull_fg :
      L(g)^* ⋙ L(f)^* ≅ L((f ≫ g))^*)
    (hpull_f'g' :
      L(g')^* ⋙ L(f')^* ≅ L((f' ≫ g'))^*) :
    L(m)^* ⋙ L((f' ≫ g'))^* ≅ L((f ≫ g))^* ⋙ L(k)^* :=
  Functor.isoWhiskerLeft (L(m)^*) hpull_f'g'.symm ≪≫
    Functor.associator (L(m)^*) (L(g')^*) (L(f')^*) ≪≫
    Functor.isoWhiskerRight hpull_bottom (L(f')^*) ≪≫
    Functor.associator (L(g)^*) (L(l)^*) (L(f')^*) ≪≫
    Functor.isoWhiskerLeft (L(g)^*) hpull_top ≪≫
    (Functor.associator (L(g)^*) (L(f)^*) (L(k)^*)).symm ≪≫
    Functor.isoWhiskerRight hpull_fg (L(k)^*)

/-- Helper for Remark 21.19.4: after rewriting the two inner maps to the canonical categorical
base-change maps, the resulting vertical composite satisfies the outer-rectangle mate formula. -/
private theorem verticalComposite_canonical_isDerivedBaseChangeMap
    (hpull_top :
      L(l)^* ⋙ L(f')^* ≅ L(f)^* ⋙ L(k)^*)
    (hpull_bottom :
      L(m)^* ⋙ L(g')^* ≅ L(g)^* ⋙ L(l)^*)
    (hpull_fg :
      L(g)^* ⋙ L(f)^* ≅ L((f ≫ g))^*)
    (hpull_f'g' :
      L(g')^* ⋙ L(f')^* ≅ L((f' ≫ g'))^*)
    (K : ModuleDerived B) :
    IsDerivedBaseChangeMap
      (L((f ≫ g))^*) (L((f' ≫ g'))^*) (L(m)^*) (L(k)^*)
      (R((f ≫ g))_*) (R((f' ≫ g'))_*)
      (modulePullbackDerived_pushforward_adjunction (f ≫ g))
      (modulePullbackDerived_pushforward_adjunction (f' ≫ g'))
      (verticalOuterRectanglePullbackIso k f' f l g' g m
        hpull_top hpull_bottom hpull_fg hpull_f'g')
      K
      ((Functor.isoWhiskerRight
          (modulePushforwardDerived_compIso f g hpull_fg)
          (L(m)^*)).inv.app K ≫
        derivedBaseChangeMap
          (L(g)^*) (L(g')^*) (L(m)^*) (L(l)^*) (R(g)_*) (R(g')_*)
          (modulePullbackDerived_pushforward_adjunction g)
          (modulePullbackDerived_pushforward_adjunction g')
          hpull_bottom
          ((R(f)_*).obj K) ≫
        (R(g')_*).map
          (derivedBaseChangeMap
            (L(f)^*) (L(f')^*) (L(l)^*) (L(k)^*) (R(f)_*) (R(f')_*)
            (modulePullbackDerived_pushforward_adjunction f)
            (modulePullbackDerived_pushforward_adjunction f')
            hpull_top
            K) ≫
      ((Functor.isoWhiskerLeft
          (L(k)^*)
          (modulePushforwardDerived_compIso f' g' hpull_f'g')).hom.app
          K)) := by
  sorry

/- Proof sketch: transpose the claimed outer morphism across the canonical adjunction
`modulePullbackDerived_pushforward_adjunction (f' ≫ g')`. The transpose reduces, via the
canonical pushforward-composition
comparison isomorphisms from Lemma `21.19.2` and the hypotheses that `η_top` and `η_bottom`
satisfy the square-wise adjunction formulas, to the pullback along `Lk^*` of the counit for
`modulePullbackDerived_pushforward_adjunction (f ≫ g)`, transported through
`verticalOuterRectanglePullbackIso`. -/
/- Derived-level implementation of Remark `21.19.4`, kept private so the public surface reuses the
ringed-site specialization from Remark `21.19.3`. -/
private theorem verticalComposite_isDerivedBaseChangeMap
    (hpull_top :
      L(l)^* ⋙ L(f')^* ≅ L(f)^* ⋙ L(k)^*)
    (hpull_bottom :
      L(m)^* ⋙ L(g')^* ≅ L(g)^* ⋙ L(l)^*)
    (hpull_fg :
      L(g)^* ⋙ L(f)^* ≅ L((f ≫ g))^*)
    (hpull_f'g' :
      L(g')^* ⋙ L(f')^* ≅ L((f' ≫ g'))^*)
    (K : ModuleDerived B)
    (η_top :
      ((L(l)^*).obj ((R(f)_*).obj K)) ⟶
        ((R(f')_*).obj ((L(k)^*).obj K)))
    (η_bottom :
      ((L(m)^*).obj
          ((R(g)_*).obj ((R(f)_*).obj K))) ⟶
      ((R(g')_*).obj
          ((L(l)^*).obj ((R(f)_*).obj K))))
    (hη_top :
      IsDerivedBaseChangeMap
        (L(f)^*) (L(f')^*) (L(l)^*) (L(k)^*) (R(f)_*) (R(f')_*)
        (modulePullbackDerived_pushforward_adjunction f)
        (modulePullbackDerived_pushforward_adjunction f')
        hpull_top
        K η_top)
    (hη_bottom :
      IsDerivedBaseChangeMap
        (L(g)^*) (L(g')^*) (L(m)^*) (L(l)^*) (R(g)_*) (R(g')_*)
        (modulePullbackDerived_pushforward_adjunction g)
        (modulePullbackDerived_pushforward_adjunction g')
        hpull_bottom
        ((R(f)_*).obj K) η_bottom) :
    IsDerivedBaseChangeMap
      (L((f ≫ g))^*) (L((f' ≫ g'))^*) (L(m)^*) (L(k)^*)
      (R((f ≫ g))_*) (R((f' ≫ g'))_*)
      (modulePullbackDerived_pushforward_adjunction (f ≫ g))
      (modulePullbackDerived_pushforward_adjunction (f' ≫ g'))
      (verticalOuterRectanglePullbackIso k f' f l g' g m
        hpull_top hpull_bottom hpull_fg hpull_f'g')
      K
      ((Functor.isoWhiskerRight
          (modulePushforwardDerived_compIso f g hpull_fg)
          (L(m)^*)).inv.app K ≫
        η_bottom ≫
        (R(g')_*).map η_top ≫
      ((Functor.isoWhiskerLeft
          (L(k)^*)
          (modulePushforwardDerived_compIso f' g' hpull_f'g')).hom.app
          K)) := by
  -- Replace the chosen inner base-change maps by the canonical ones before invoking the
  -- canonical outer-rectangle computation.
  convert
    verticalComposite_canonical_isDerivedBaseChangeMap
      k f' f l g' g m hpull_top hpull_bottom hpull_fg hpull_f'g' K
  · simpa using hη_bottom.eq_derivedBaseChangeMap
  · simpa using hη_top.eq_derivedBaseChangeMap

/-- Remark 21.19.4: for a composable pair of commutative squares of ringed topoi, if `η_top` and
`η_bottom` are unbounded base-change morphisms for the top and bottom squares, then after
identifying the composite derived pushforwards with the derived pushforwards of the composite
morphisms, their composition is an unbounded base-change morphism for the outer rectangle. -/
@[stacks 0E46]
theorem verticalComposite_isUnboundedBaseChangeMap
    (hpull_top :
      L(l)^* ⋙ L(f')^* ≅ L(f)^* ⋙ L(k)^*)
    (hpull_bottom :
      L(m)^* ⋙ L(g')^* ≅ L(g)^* ⋙ L(l)^*)
    (hpull_fg :
      L(g)^* ⋙ L(f)^* ≅ L((f ≫ g))^*)
    (hpull_f'g' :
      L(g')^* ⋙ L(f')^* ≅ L((f' ≫ g'))^*)
    (K : ModuleDerived B)
    (η_top :
      ((L(l)^*).obj ((R(f)_*).obj K)) ⟶
        ((R(f')_*).obj ((L(k)^*).obj K)))
    (η_bottom :
      ((L(m)^*).obj
          ((R(g)_*).obj ((R(f)_*).obj K))) ⟶
      ((R(g')_*).obj
          ((L(l)^*).obj ((R(f)_*).obj K))))
    (hη_top :
      IsUnboundedBaseChangeMap k f' f l hpull_top K η_top)
    (hη_bottom :
      IsUnboundedBaseChangeMap l g' g m hpull_bottom ((R(f)_*).obj K) η_bottom) :
    IsUnboundedBaseChangeMap
      k (f' ≫ g') (f ≫ g) m
      (verticalOuterRectanglePullbackIso k f' f l g' g m
        hpull_top hpull_bottom hpull_fg hpull_f'g')
      K
      ((Functor.isoWhiskerRight
          (modulePushforwardDerived_compIso f g hpull_fg)
          (L(m)^*)).inv.app K ≫
        η_bottom ≫
        (R(g')_*).map η_top ≫
      ((Functor.isoWhiskerLeft
          (L(k)^*)
          (modulePushforwardDerived_compIso f' g' hpull_f'g')).hom.app
          K)) := by
  simpa [IsUnboundedBaseChangeMap] using
    (verticalComposite_isDerivedBaseChangeMap
      k f' f l g' g m
      hpull_top hpull_bottom hpull_fg hpull_f'g'
      K η_top η_bottom hη_top hη_bottom)

/-- The canonical base-change maps from Remark `21.19.3` compose to the canonical base-change map
for the outer rectangle. -/
theorem verticalComposite_unboundedBaseChangeMap_spec
    (hpull_top :
      L(l)^* ⋙ L(f')^* ≅ L(f)^* ⋙ L(k)^*)
    (hpull_bottom :
      L(m)^* ⋙ L(g')^* ≅ L(g)^* ⋙ L(l)^*)
    (hpull_fg :
      L(g)^* ⋙ L(f)^* ≅ L((f ≫ g))^*)
    (hpull_f'g' :
      L(g')^* ⋙ L(f')^* ≅ L((f' ≫ g'))^*)
    (K : ModuleDerived B) :
    ((Functor.isoWhiskerRight
        (modulePushforwardDerived_compIso f g hpull_fg)
        (L(m)^*)).inv.app K ≫
      unboundedBaseChangeMap l g' g m hpull_bottom ((R(f)_*).obj K) ≫
      (R(g')_*).map (unboundedBaseChangeMap k f' f l hpull_top K) ≫
      ((Functor.isoWhiskerLeft
        (L(k)^*)
        (modulePushforwardDerived_compIso f' g' hpull_f'g')).hom.app K)) =
      unboundedBaseChangeMap
        k (f' ≫ g') (f ≫ g) m
        (verticalOuterRectanglePullbackIso k f' f l g' g m
          hpull_top hpull_bottom hpull_fg hpull_f'g')
        K := by
  -- Specialize the proof-oriented theorem to the canonical base-change maps and use uniqueness
  -- of unbounded base-change morphisms from Remark `21.19.3`.
  simpa [unboundedBaseChangeMap] using
    (verticalComposite_isUnboundedBaseChangeMap
      k f' f l g' g m
      hpull_top hpull_bottom hpull_fg hpull_f'g'
      K
      (unboundedBaseChangeMap k f' f l hpull_top K)
      (unboundedBaseChangeMap l g' g m hpull_bottom ((R(f)_*).obj K))
      (unboundedBaseChangeMap_isUnboundedBaseChangeMap k f' f l hpull_top K)
      (unboundedBaseChangeMap_isUnboundedBaseChangeMap
        l g' g m hpull_bottom ((R(f)_*).obj K))).eq_unboundedBaseChangeMap

end

end RingedSite.Hom
