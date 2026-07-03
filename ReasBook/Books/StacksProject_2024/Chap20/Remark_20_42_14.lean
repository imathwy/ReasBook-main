import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open ComplexShape

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The structure sheaf of a ringed space, regarded as a `RingCat`-valued sheaf. -/
/-- The category of sheaves of `\mathcal O_X`-modules on a ringed space. -/
/-- The derived category `D(\mathcal O_X)` of sheaves of `\mathcal O_X`-modules on a ringed
space. -/
private abbrev DMod (X : RingedSpace.{u}) :=
  DerivedCategory (SheafOfModules (ringCatSheaf X))

/-- The structure-sheaf morphism `\mathcal O_Y \to f_*\mathcal O_X` attached to a morphism of
ringed spaces. -/
noncomputable abbrev commRingSheafPushforwardMap {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    Y.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).obj X.sheaf :=
  ⟨f.hom.c⟩

/-- The structure-sheaf morphism of a ringed-space morphism after forgetting commutativity. -/
noncomputable abbrev pushforwardStructureSheafHom {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    (RingedSpace.ringCatSheaf Y) ⟶
      (TopCat.Sheaf.pushforward RingCat.{u} f.hom.base).obj (RingedSpace.ringCatSheaf X) :=
  (sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat RingCat.{u})).map
    (commRingSheafPushforwardMap f)

/-- The direct-image functor on `\mathcal O_X`-modules attached to a morphism of ringed spaces. -/
noncomputable abbrev modulePushforward {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    (RingedSpace.Modules X) ⥤ (RingedSpace.Modules Y) :=
  SheafOfModules.pushforward (pushforwardStructureSheafHom f)

/-- The pullback functor on `\mathcal O_Y`-modules attached to a morphism of ringed spaces. -/
noncomputable abbrev modulePullback {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    (RingedSpace.Modules Y) ⥤ (RingedSpace.Modules X) :=
  SheafOfModules.pullback (pushforwardStructureSheafHom f)

/-- The quasi-isomorphisms in the homotopy category of `\mathcal O_X`-module complexes. -/
abbrev ModuleQis (X : RingedSpace.{u}) :=
  HomotopyCategory.quasiIso (RingedSpace.Modules X) (up ℤ)

/-- The homotopy-category functor used to define the total left derived pullback. -/
abbrev modulePullbackToDerived {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(modulePullback f).Additive] :
    HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤ DMod X :=
  (modulePullback f).mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh

/-- The homotopy-category functor used to define the total right derived pushforward. -/
abbrev modulePushforwardToDerived {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(modulePushforward f).Additive] :
    HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤ DMod Y :=
  (modulePushforward f).mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh

/-- The derived pullback functor `Lf^* : D(\mathcal O_Y) ⥤ D(\mathcal O_X)`. -/
abbrev modulePullbackDerived {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    [(modulePullback f).Additive]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)] :
    DMod Y ⥤ DMod X :=
  Functor.totalLeftDerived (modulePullbackToDerived f)
    (DerivedCategory.Qh : HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤ DMod Y)
    (ModuleQis Y)

/-- The derived pushforward functor `Rf_* : D(\mathcal O_X) ⥤ D(\mathcal O_Y)`. -/
abbrev moduleDerivedPushforward {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(modulePushforward f).Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)] :
    DMod X ⥤ DMod Y :=
  Functor.totalRightDerived (modulePushforwardToDerived f)
    (DerivedCategory.Qh : HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤ DMod X)
    (ModuleQis X)

/-- The tensor-internal-Hom adjunction on `D(\mathcal O_X)`, written in the Stacks Project order
`A ⊗ B`. -/
private abbrev ringedSpaceDerivedInternalHomAdjunction
    (X : RingedSpace.{u})
    [MonoidalCategory (DMod X)] [BraidedCategory (DMod X)] [MonoidalClosed (DMod X)]
    (A B C : DMod X) :
    (A ⟶ (ihom B).obj C) ≃ (A ⊗ B ⟶ C) :=
  ((ihom.adjunction B).homEquiv A C).symm.trans
    ((β_ A B).symm.homCongr (Iso.refl C))

/-- The evaluation morphism
`R\mathcal H\!\mathit{om}(K, L) \otimes^{\mathbf L} K \to L`
in `D(\mathcal O_X)`. -/
private abbrev ringedSpaceDerivedInternalHomEvaluation
    (X : RingedSpace.{u})
    [MonoidalCategory (DMod X)] [BraidedCategory (DMod X)] [MonoidalClosed (DMod X)]
    (K L : DMod X) :
    (ihom K).obj L ⊗ K ⟶ L :=
  ringedSpaceDerivedInternalHomAdjunction X ((ihom K).obj L) K L (𝟙 ((ihom K).obj L))

section

variable {X Y : RingedSpace.{u}}

variable (leftDerivedPullback : DMod Y ⥤ DMod X)

variable [MonoidalCategory (DMod X)]
variable [BraidedCategory (DMod X)]
variable [MonoidalClosed (DMod X)]
variable [MonoidalCategory (DMod Y)]
variable [BraidedCategory (DMod Y)]
variable [MonoidalClosed (DMod Y)]

/-- The pullback comparison
`Lh^* R\mathcal H\!\mathit{om}(K, L) \to
R\mathcal H\!\mathit{om}(Lh^* K, Lh^* L)` induced by the pullback-tensor comparison. -/
noncomputable def pullbackDerivedInternalHomComparison
    (pullbackTensorIso :
      ∀ (A B : DMod Y),
        leftDerivedPullback.obj (A ⊗ B) ≅
          (leftDerivedPullback.obj A ⊗ leftDerivedPullback.obj B))
    (K L : DMod Y) :
    leftDerivedPullback.obj ((ihom K).obj L) ⟶
      (ihom (leftDerivedPullback.obj K)).obj (leftDerivedPullback.obj L) :=
  (ringedSpaceDerivedInternalHomAdjunction X
      (leftDerivedPullback.obj ((ihom K).obj L))
      (leftDerivedPullback.obj K)
      (leftDerivedPullback.obj L)).symm
    ((pullbackTensorIso ((ihom K).obj L) K).inv ≫
      leftDerivedPullback.map (ringedSpaceDerivedInternalHomEvaluation Y K L))

-- Proof sketch: unfold `pullbackDerivedInternalHomComparison`; by definition it is the inverse
-- image of the pulled-back evaluation morphism under the target-side tensor-internal-Hom
-- adjunction, after transporting along the pullback-tensor comparison.
/-- Applying the tensor-internal-Hom adjunction to the pullback comparison recovers the pullback
of the evaluation morphism after transport across the pullback-tensor comparison. -/
theorem pullbackDerivedInternalHomComparison_spec
    (pullbackTensorIso :
      ∀ (A B : DMod Y),
        leftDerivedPullback.obj (A ⊗ B) ≅
          (leftDerivedPullback.obj A ⊗ leftDerivedPullback.obj B))
    (K L : DMod Y) :
    ringedSpaceDerivedInternalHomAdjunction X
        (leftDerivedPullback.obj ((ihom K).obj L))
        (leftDerivedPullback.obj K)
        (leftDerivedPullback.obj L)
        (pullbackDerivedInternalHomComparison leftDerivedPullback pullbackTensorIso K L) =
      (pullbackTensorIso ((ihom K).obj L) K).inv ≫
        leftDerivedPullback.map (ringedSpaceDerivedInternalHomEvaluation Y K L) := sorry

end

section

variable {X' X S' S : RingedSpace.{u}}
variable (h : X' ⟶ X) (f' : X' ⟶ S') (g : S' ⟶ S) (f : X ⟶ S)

variable [CategoryWithHomology (RingedSpace.Modules X')]
variable [CategoryWithHomology (RingedSpace.Modules X)]
variable [CategoryWithHomology (RingedSpace.Modules S')]
variable [CategoryWithHomology (RingedSpace.Modules S)]

variable [(modulePullback h).Additive]
variable [(modulePullback f').Additive]
variable [(modulePullback g).Additive]
variable [(modulePullback f).Additive]
variable [(modulePushforward f').Additive]
variable [(modulePushforward f).Additive]

variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived h) (ModuleQis X)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f') (ModuleQis S')]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g) (ModuleQis S)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis S)]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f') (ModuleQis X')]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]

variable [MonoidalCategory (DMod X')]
variable [BraidedCategory (DMod X')]
variable [MonoidalClosed (DMod X')]
variable [MonoidalCategory (DMod X)]
variable [BraidedCategory (DMod X)]
variable [MonoidalClosed (DMod X)]

/-- Remark 20.42.14: given a commutative square of ringed spaces together with the induced
pullback-commutativity isomorphism on derived pullbacks, the adjunctions `Lf^* ⊣ Rf_*` and
`L(f')^* ⊣ R(f')_*`, and the pullback-tensor comparison for `h`, there is a canonical base-change
morphism
`Lg^* Rf_* R\mathcal H\!\mathit{om}(K, L) ⟶
R(f')_* R\mathcal H\!\mathit{om}(Lh^* K, Lh^* L)`. -/
noncomputable def derivedInternalHomBaseChangeMap
    (pullbackCommIso :
      modulePullbackDerived g ⋙ modulePullbackDerived f' ≅
        modulePullbackDerived f ⋙ modulePullbackDerived h)
    (adj_f : modulePullbackDerived f ⊣ moduleDerivedPushforward f)
    (adj_f' : modulePullbackDerived f' ⊣ moduleDerivedPushforward f')
    (pullbackTensorIso_h :
      ∀ (A B : DMod X),
        (modulePullbackDerived h).obj (A ⊗ B) ≅
          ((modulePullbackDerived h).obj A ⊗ (modulePullbackDerived h).obj B))
    (K L : DMod X) :
    (modulePullbackDerived g).obj ((moduleDerivedPushforward f).obj ((ihom K).obj L)) ⟶
      (moduleDerivedPushforward f').obj
        ((ihom ((modulePullbackDerived h).obj K)).obj ((modulePullbackDerived h).obj L)) :=
  adj_f'.homEquiv
      ((modulePullbackDerived g).obj ((moduleDerivedPushforward f).obj ((ihom K).obj L)))
      ((ihom ((modulePullbackDerived h).obj K)).obj ((modulePullbackDerived h).obj L))
    (pullbackCommIso.hom.app ((moduleDerivedPushforward f).obj ((ihom K).obj L)) ≫
      (modulePullbackDerived h).map (adj_f.counit.app ((ihom K).obj L)) ≫
      pullbackDerivedInternalHomComparison (modulePullbackDerived h) pullbackTensorIso_h K L)

-- Proof sketch: unfold `derivedInternalHomBaseChangeMap`. By definition it is the transpose,
-- under `L(f')^* ⊣ R(f')_*`, of the composite obtained by transporting `L(f')^*Lg^*` to
-- `Lh^*Lf^*`, applying the counit `Lf^*Rf_* → 𝟭`, and then using the pullback-internal-Hom
-- comparison from Remark `20.42.13`.
/-- Applying the adjunction `L(f')^* ⊣ R(f')_*` to the internal-Hom base-change map recovers the
composite prescribed in the remark. -/
theorem derivedInternalHomBaseChangeMap_spec
    (pullbackCommIso :
      modulePullbackDerived g ⋙ modulePullbackDerived f' ≅
        modulePullbackDerived f ⋙ modulePullbackDerived h)
    (adj_f : modulePullbackDerived f ⊣ moduleDerivedPushforward f)
    (adj_f' : modulePullbackDerived f' ⊣ moduleDerivedPushforward f')
    (pullbackTensorIso_h :
      ∀ (A B : DMod X),
        (modulePullbackDerived h).obj (A ⊗ B) ≅
          ((modulePullbackDerived h).obj A ⊗ (modulePullbackDerived h).obj B))
    (K L : DMod X) :
    (adj_f'.homEquiv
        ((modulePullbackDerived g).obj ((moduleDerivedPushforward f).obj ((ihom K).obj L)))
        ((ihom ((modulePullbackDerived h).obj K)).obj ((modulePullbackDerived h).obj L))
        ).symm
        (derivedInternalHomBaseChangeMap h f' g f pullbackCommIso adj_f adj_f'
          pullbackTensorIso_h K L) =
      pullbackCommIso.hom.app ((moduleDerivedPushforward f).obj ((ihom K).obj L)) ≫
        (modulePullbackDerived h).map (adj_f.counit.app ((ihom K).obj L)) ≫
        pullbackDerivedInternalHomComparison (modulePullbackDerived h) pullbackTensorIso_h K L := sorry

end

end AlgebraicGeometry.RingedSpace
