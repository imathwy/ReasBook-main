import Mathlib
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_20_28_1 (from Chap20) -/
open CategoryTheory
open ComplexShape
open AlgebraicGeometry

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The structure sheaf of a ringed space, regarded as a sheaf of not-necessarily-commutative
rings. -/
/-- The category of sheaves of `\mathcal O_X`-modules on a ringed space. -/
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

/-- Applying an additive functor termwise and then localizing gives a functor from the homotopy
category to the derived category. -/
abbrev mapHomotopyCategoryToDerived
    {𝒜 : Type u} {ℬ : Type u}
    [Category 𝒜] [Category ℬ]
    [Abelian 𝒜] [Abelian ℬ] [HasDerivedCategory ℬ]
    (F : 𝒜 ⥤ ℬ) [F.Additive] :
    HomotopyCategory 𝒜 (up ℤ) ⥤ DerivedCategory ℬ :=
  F.mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh

/-- The quasi-isomorphisms in the homotopy category of `\mathcal O_X`-module complexes. -/
abbrev ModuleQis (X : RingedSpace.{u}) :=
  HomotopyCategory.quasiIso (RingedSpace.Modules X) (up ℤ)

/-- The homotopy-category functor used to define the total left derived pullback. -/
abbrev modulePullbackToDerived {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(modulePullback f).Additive] :=
  mapHomotopyCategoryToDerived (modulePullback f)

/-- The derived pullback functor `Lf^* : D(\mathcal O_Y) ⥤ D(\mathcal O_X)`. -/
abbrev modulePullbackDerived
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    [(modulePullback f).Additive]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)] :
    DerivedCategory (RingedSpace.Modules Y) ⥤ DerivedCategory (RingedSpace.Modules X) :=
  Functor.totalLeftDerived (modulePullbackToDerived f)
    (DerivedCategory.Qh : HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤ DerivedCategory (RingedSpace.Modules Y))
    (ModuleQis Y)

/-- The cochain-level pushforward functor followed by localization to the derived category. -/
abbrev modulePushforwardToDerived {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(modulePushforward f).Additive] :
    CochainComplex (RingedSpace.Modules X) ℤ ⥤ DerivedCategory (RingedSpace.Modules Y) :=
  (modulePushforward f).mapHomologicalComplex (up ℤ) ⋙
    (DerivedCategory.Q : CochainComplex (RingedSpace.Modules Y) ℤ ⥤ DerivedCategory (RingedSpace.Modules Y))

/-- The derived pushforward functor `Rf_* : D(\mathcal O_X) ⥤ D(\mathcal O_Y)`. -/
abbrev moduleDerivedPushforward {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(modulePushforward f).Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f)
      (HomologicalComplex.quasiIso (RingedSpace.Modules X) (up ℤ))] :
    DerivedCategory (RingedSpace.Modules X) ⥤ DerivedCategory (RingedSpace.Modules Y) :=
  (modulePushforwardToDerived f).totalRightDerived
    (DerivedCategory.Q : CochainComplex (RingedSpace.Modules X) ℤ ⥤ DerivedCategory (RingedSpace.Modules X))
    (HomologicalComplex.quasiIso (RingedSpace.Modules X) (up ℤ))

-- Proof sketch: the underived adjunction `f^* ⊣ f_*` for sheaves of modules is
-- `SheafOfModules.pullbackPushforwardAdjunction`. Lemma `20.27.1` gives the total left derived
-- functor `Lf^*`, and the earlier construction of `Rf_*` gives the total right derived functor.
-- Apply the general derived-adjunction formalism to these two derived functors.
/-- Derived pullback and derived pushforward along a morphism of ringed spaces form an adjoint
pair. -/
theorem modulePullbackDerived_pushforward_adjunction
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    [(modulePullback f).Additive] [(modulePushforward f).Additive]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f)
      (HomologicalComplex.quasiIso (RingedSpace.Modules X) (up ℤ))] :
    Nonempty
      ((modulePullbackDerived f : DerivedCategory (RingedSpace.Modules Y) ⥤ DerivedCategory (RingedSpace.Modules X)) ⊣
        (moduleDerivedPushforward f :
          DerivedCategory (RingedSpace.Modules X) ⥤ DerivedCategory (RingedSpace.Modules Y))) := sorry

-- Proof sketch: choose an adjunction from
-- `modulePullbackDerived_pushforward_adjunction f` and apply its `homEquiv` to the pair
-- `(𝒢, ℱ)`. This is exactly the bifunctorial Hom-set identification expressing that
-- `Lf^*` is left adjoint to `Rf_*`.
/-- Lemma 20.28.1: the derived pullback `Lf^*` and derived pushforward `Rf_*` induce a
bifunctorial equivalence
`Hom_{D(\mathcal O_X)}(Lf^* \mathcal G^\bullet, \mathcal F^\bullet) ≃
Hom_{D(\mathcal O_Y)}(\mathcal G^\bullet, Rf_* \mathcal F^\bullet)`. -/
theorem modulePullbackDerived_pushforward_homEquiv
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    [(modulePullback f).Additive] [(modulePushforward f).Additive]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f)
      (HomologicalComplex.quasiIso (RingedSpace.Modules X) (up ℤ))]
    (ℱ : DerivedCategory (RingedSpace.Modules X)) (𝒢 : DerivedCategory (RingedSpace.Modules Y)) :
    Nonempty
      (((modulePullbackDerived f).obj 𝒢 ⟶ ℱ) ≃
        (𝒢 ⟶ (moduleDerivedPushforward f).obj ℱ)) := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_28_2 (from Chap20) -/
open CategoryTheory
open ComplexShape
open AlgebraicGeometry

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The structure sheaf of a ringed space, regarded as a sheaf of not-necessarily-commutative
rings. -/
/-- The category of sheaves of `\mathcal O_X`-modules on a ringed space. -/
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

/-- Applying an additive functor termwise and then localizing gives a functor from the homotopy
category to the derived category. -/
abbrev mapHomotopyCategoryToDerived
    {𝒜 : Type u} {ℬ : Type u}
    [Category 𝒜] [Category ℬ]
    [Abelian 𝒜] [Abelian ℬ] [HasDerivedCategory ℬ]
    (F : 𝒜 ⥤ ℬ) [F.Additive] :
    HomotopyCategory 𝒜 (up ℤ) ⥤ DerivedCategory ℬ :=
  F.mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh

/-- The quasi-isomorphisms in the homotopy category of `\mathcal O_X`-module complexes. -/
abbrev ModuleQis (X : RingedSpace.{u}) :=
  HomotopyCategory.quasiIso (RingedSpace.Modules X) (up ℤ)

/-- The homotopy-category functor used to define the total left derived pullback. -/
abbrev modulePullbackToDerived {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(modulePullback f).Additive] :=
  mapHomotopyCategoryToDerived (modulePullback f)

/-- The derived pullback functor `Lf^* : D(\mathcal O_Y) ⥤ D(\mathcal O_X)`. -/
abbrev modulePullbackDerived
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    [(modulePullback f).Additive]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)] :
    DerivedCategory (RingedSpace.Modules Y) ⥤ DerivedCategory (RingedSpace.Modules X) :=
  Functor.totalLeftDerived (modulePullbackToDerived f)
    (DerivedCategory.Qh : HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤ DerivedCategory (RingedSpace.Modules Y))
    (ModuleQis Y)

/-- The cochain-level pushforward functor followed by localization to the derived category. -/
abbrev modulePushforwardToDerived {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(modulePushforward f).Additive] :
    CochainComplex (RingedSpace.Modules X) ℤ ⥤ DerivedCategory (RingedSpace.Modules Y) :=
  (modulePushforward f).mapHomologicalComplex (up ℤ) ⋙
    (DerivedCategory.Q : CochainComplex (RingedSpace.Modules Y) ℤ ⥤ DerivedCategory (RingedSpace.Modules Y))

/-- The derived pushforward functor `Rf_* : D(\mathcal O_X) ⥤ D(\mathcal O_Y)`. -/
abbrev moduleDerivedPushforward {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(modulePushforward f).Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f)
      (HomologicalComplex.quasiIso (RingedSpace.Modules X) (up ℤ))] :
    DerivedCategory (RingedSpace.Modules X) ⥤ DerivedCategory (RingedSpace.Modules Y) :=
  (modulePushforwardToDerived f).totalRightDerived
    (DerivedCategory.Q : CochainComplex (RingedSpace.Modules X) ℤ ⥤ DerivedCategory (RingedSpace.Modules X))
    (HomologicalComplex.quasiIso (RingedSpace.Modules X) (up ℤ))

/-- Lemma 20.28.2: for composable morphisms of ringed spaces `f : X ⟶ Y` and `g : Y ⟶ Z`, once
the canonical comparison `Lg^* ⋙ Lf^* ≅ L(g \circ f)^*` and the derived adjunctions are fixed,
the composite derived pushforward `Rf_* ⋙ Rg_*` is canonically isomorphic to the derived
pushforward of the composite morphism `R(g \circ f)_*`. This formalizes the equality
`Rg_* \circ Rf_* = R(g \circ f)_*` on `D(\mathcal O_X)`. -/
noncomputable abbrev moduleDerivedPushforward_compIso
    {X Y Z : RingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    [CategoryWithHomology (RingedSpace.Modules Z)]
    [(modulePushforward f).Additive] [(modulePushforward g).Additive]
    [(modulePushforward (f ≫ g)).Additive]
    [(modulePullback f).Additive] [(modulePullback g).Additive]
    [(modulePullback (f ≫ g)).Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f)
      (HomologicalComplex.quasiIso (RingedSpace.Modules X) (up ℤ))]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived g)
      (HomologicalComplex.quasiIso (RingedSpace.Modules Y) (up ℤ))]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived (f ≫ g))
      (HomologicalComplex.quasiIso (RingedSpace.Modules X) (up ℤ))]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g) (ModuleQis Z)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived (f ≫ g)) (ModuleQis Z)]
    (hpull : modulePullbackDerived g ⋙ modulePullbackDerived f ≅
      modulePullbackDerived (f ≫ g))
    (adj_f : modulePullbackDerived f ⊣ moduleDerivedPushforward f)
    (adj_g : modulePullbackDerived g ⊣ moduleDerivedPushforward g)
    (adj_comp : modulePullbackDerived (f ≫ g) ⊣ moduleDerivedPushforward (f ≫ g)) :
    moduleDerivedPushforward f ⋙ moduleDerivedPushforward g ≅
      moduleDerivedPushforward (f ≫ g) :=
  Adjunction.rightAdjointUniq
    (Adjunction.ofNatIsoLeft (adj_g.comp adj_f) hpull)
    adj_comp

-- Proof sketch: unfold `moduleDerivedPushforward_compIso` and apply the standard formula
-- `Adjunction.rightAdjointUniq_hom_counit` for the uniqueness isomorphism of right adjoints.
/-- The comparison isomorphism from iterated derived pushforward to the derived pushforward of the
composite is characterized by compatibility with the counits of the chosen derived adjunctions. -/
theorem moduleDerivedPushforward_compIso_hom_counit
    {X Y Z : RingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    [CategoryWithHomology (RingedSpace.Modules Z)]
    [(modulePushforward f).Additive] [(modulePushforward g).Additive]
    [(modulePushforward (f ≫ g)).Additive]
    [(modulePullback f).Additive] [(modulePullback g).Additive]
    [(modulePullback (f ≫ g)).Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f)
      (HomologicalComplex.quasiIso (RingedSpace.Modules X) (up ℤ))]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived g)
      (HomologicalComplex.quasiIso (RingedSpace.Modules Y) (up ℤ))]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived (f ≫ g))
      (HomologicalComplex.quasiIso (RingedSpace.Modules X) (up ℤ))]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g) (ModuleQis Z)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived (f ≫ g)) (ModuleQis Z)]
    (hpull : modulePullbackDerived g ⋙ modulePullbackDerived f ≅
      modulePullbackDerived (f ≫ g))
    (adj_f : modulePullbackDerived f ⊣ moduleDerivedPushforward f)
    (adj_g : modulePullbackDerived g ⊣ moduleDerivedPushforward g)
    (adj_comp : modulePullbackDerived (f ≫ g) ⊣ moduleDerivedPushforward (f ≫ g)) :
    Functor.whiskerRight
        (moduleDerivedPushforward_compIso f g hpull adj_f adj_g adj_comp).hom
        (modulePullbackDerived (f ≫ g)) ≫
      adj_comp.counit =
        (Adjunction.ofNatIsoLeft (adj_g.comp adj_f) hpull).counit :=
  sorry

end AlgebraicGeometry.RingedSpace

/-! ### Remark_20_28_3 (from Chap20) -/
open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

attribute [local instance] HasDerivedCategory.standard

variable {X X' S S' : RingedSpace.{u}}

/-- The source object `Lg^* Rf_* K` of the unbounded base-change map. -/
abbrev derivedBaseChangeSource (f : X ⟶ S) (g : S' ⟶ S)
    [(modulePushforward f).Additive]
    [(modulePullback g).Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f)
      (HomologicalComplex.quasiIso (RingedSpace.Modules X) (up ℤ))]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g) (ModuleQis S)]
    (K : DerivedCategory (RingedSpace.Modules X)) : DerivedCategory (RingedSpace.Modules S') :=
  (modulePullbackDerived g).obj ((moduleDerivedPushforward f).obj K)

/-- The target object `R(f')_* L(g')^* K` of the unbounded base-change map. -/
abbrev derivedBaseChangeTarget (g' : X' ⟶ X) (f' : X' ⟶ S')
    [(modulePullback g').Additive]
    [(modulePushforward f').Additive]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g') (ModuleQis X)]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f')
      (HomologicalComplex.quasiIso (RingedSpace.Modules X') (up ℤ))]
    (K : DerivedCategory (RingedSpace.Modules X)) : DerivedCategory (RingedSpace.Modules S') :=
  (moduleDerivedPushforward f').obj ((modulePullbackDerived g').obj K)

/-- A morphism `Lg^* Rf_* K ⟶ R(f')_* L(g')^* K` is an unbounded derived base-change map if,
after transposing along `L(f')^* ⊣ R(f')_*`, it is the pullback along `L(g')^*` of the counit
`Lf^* Rf_* K ⟶ K`, transported across the chosen comparison isomorphism
`L(f')^* ∘ Lg^* ≅ L(g')^* ∘ Lf^*`. -/
def IsUnboundedDerivedBaseChangeMap
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    [(modulePullback g').Additive]
    [(modulePushforward f').Additive]
    [(modulePushforward f).Additive]
    [(modulePullback g).Additive]
    [(modulePullback f).Additive]
    [(modulePullback f').Additive]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g') (ModuleQis X)]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f')
      (HomologicalComplex.quasiIso (RingedSpace.Modules X') (up ℤ))]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f)
      (HomologicalComplex.quasiIso (RingedSpace.Modules X) (up ℤ))]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g) (ModuleQis S)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis S)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f') (ModuleQis S')]
    (hpull : modulePullbackDerived g ⋙ modulePullbackDerived f' ≅
      modulePullbackDerived f ⋙ modulePullbackDerived g')
    (adjf : modulePullbackDerived f ⊣ moduleDerivedPushforward f)
    (adjf' : modulePullbackDerived f' ⊣ moduleDerivedPushforward f')
    (K : DerivedCategory (RingedSpace.Modules X))
    (τ : derivedBaseChangeSource f g K ⟶ derivedBaseChangeTarget g' f' K) : Prop :=
  ((adjf'.homEquiv (derivedBaseChangeSource f g K) ((modulePullbackDerived g').obj K)).symm τ) =
    (hpull.app ((moduleDerivedPushforward f).obj K)).hom ≫
      (modulePullbackDerived g').map (adjf.counit.app K)

-- Proof sketch: use the derived adjunction for `f'` to identify morphisms
-- `Lg^* Rf_* K ⟶ R(f')_* L(g')^* K` with morphisms
-- `L(f')^* Lg^* Rf_* K ⟶ L(g')^* K`. The latter is obtained by first transporting along the
-- chosen comparison isomorphism `hpull`, then applying `L(g')^*` to the counit
-- `Lf^* Rf_* K ⟶ K`.
/-- Remark 20.28.3: for morphisms of ringed spaces
`g' : X' ⟶ X`, `f' : X' ⟶ S'`, `f : X ⟶ S`, and `g : S' ⟶ S`, once the unbounded derived
pullbacks and pushforwards are chosen together with adjunctions
`Lf^* ⊣ Rf_*` and `L(f')^* ⊣ R(f')_*`, and once a comparison isomorphism
`L(f')^* \circ Lg^* \cong L(g')^* \circ Lf^*` is fixed, every object
`K ∈ D(\mathcal O_X)` admits a base-change morphism
`Lg^* Rf_* K ⟶ R(f')_* L(g')^* K` whose adjoint is the composite
`L(f')^* Lg^* Rf_* K \to L(g')^* Lf^* Rf_* K \to L(g')^* K`
described in the remark. -/
theorem exists_unbounded_derived_baseChange_map
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    [(modulePullback g').Additive]
    [(modulePushforward f').Additive]
    [(modulePushforward f).Additive]
    [(modulePullback g).Additive]
    [(modulePullback f).Additive]
    [(modulePullback f').Additive]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g') (ModuleQis X)]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f')
      (HomologicalComplex.quasiIso (RingedSpace.Modules X') (up ℤ))]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f)
      (HomologicalComplex.quasiIso (RingedSpace.Modules X) (up ℤ))]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g) (ModuleQis S)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis S)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f') (ModuleQis S')]
    (adjf : modulePullbackDerived f ⊣ moduleDerivedPushforward f)
    (adjf' : modulePullbackDerived f' ⊣ moduleDerivedPushforward f')
    (hpull : modulePullbackDerived g ⋙ modulePullbackDerived f' ≅
      modulePullbackDerived f ⋙ modulePullbackDerived g')
    (K : DerivedCategory (RingedSpace.Modules X)) :
    ∃ τ : derivedBaseChangeSource f g K ⟶ derivedBaseChangeTarget g' f' K,
      IsUnboundedDerivedBaseChangeMap g' f' f g hpull adjf adjf' K τ := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Remark_20_28_4 (from Chap20) -/
open CategoryTheory
open ComplexShape
open AlgebraicGeometry
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

attribute [local instance] HasDerivedCategory.standard

/-- The structure sheaf of a ringed space, viewed as a sheaf with values in `RingCat`. -/
abbrev ringedSpaceRingCatSheaf (X : RingedSpace.{u}) : TopCat.Sheaf RingCat.{u} X :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat RingCat.{u})).obj X.sheaf

/-- The category of sheaves of `\mathcal O_X`-modules on a ringed space. -/
/-- The structure-sheaf morphism `\mathcal O_Y \to f_*\mathcal O_X` attached to a morphism of
ringed spaces. -/
noncomputable abbrev ringedSpaceCommRingSheafPushforwardMap {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    Y.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).obj X.sheaf :=
  ⟨f.hom.c⟩

/-- The structure-sheaf morphism of a morphism of ringed spaces after forgetting commutativity. -/
noncomputable abbrev ringedSpacePushforwardStructureSheafHom {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    ringedSpaceRingCatSheaf Y ⟶
      (TopCat.Sheaf.pushforward RingCat.{u} f.hom.base).obj (ringedSpaceRingCatSheaf X) :=
  (sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat RingCat.{u})).map
    (ringedSpaceCommRingSheafPushforwardMap f)

/-- The direct-image functor on `\mathcal O_X`-modules attached to a morphism of ringed spaces. -/
noncomputable abbrev ringedSpaceModulePushforward {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    SheafOfModules (ringedSpaceRingCatSheaf X) ⥤
      SheafOfModules (ringedSpaceRingCatSheaf Y) :=
  SheafOfModules.pushforward (ringedSpacePushforwardStructureSheafHom f)

/-- The pullback functor on `\mathcal O_Y`-modules attached to a morphism of ringed spaces. -/
noncomputable abbrev ringedSpaceModulePullback {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    SheafOfModules (ringedSpaceRingCatSheaf Y) ⥤
      SheafOfModules (ringedSpaceRingCatSheaf X) :=
  SheafOfModules.pullback (ringedSpacePushforwardStructureSheafHom f)

/-- The quasi-isomorphisms in the homotopy category of unbounded complexes of
`\mathcal O_X`-modules on a ringed space. -/
abbrev ModuleQis (X : RingedSpace.{u}) :=
  HomotopyCategory.quasiIso (RingedSpace.Modules X) (up ℤ)

/-- The unbounded derived category `D(\mathcal O_X)` of a ringed space. -/
abbrev ModuleDerived (X : RingedSpace.{u}) :=
  DerivedCategory (RingedSpace.Modules X)

/-- The homotopy-to-derived functor induced by direct image on module sheaves. -/
abbrev modulePushforwardToDerived {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(ringedSpaceModulePushforward f).Additive] :
    HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤ ModuleDerived Y :=
  (ringedSpaceModulePushforward f).mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh

/-- The homotopy-to-derived functor induced by inverse image on module sheaves. -/
abbrev modulePullbackToDerived {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(ringedSpaceModulePullback f).Additive] :
    HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤ ModuleDerived X :=
  (ringedSpaceModulePullback f).mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh

/-- The unbounded derived direct image functor `Rf_*`. -/
abbrev modulePushforwardDerived {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(ringedSpaceModulePushforward f).Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)] :
    ModuleDerived X ⥤ ModuleDerived Y :=
  Functor.totalRightDerived (modulePushforwardToDerived f)
    (DerivedCategory.Qh : HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤ ModuleDerived X)
    (ModuleQis X)

/-- The unbounded derived inverse-image functor `Lf^*`. -/
abbrev modulePullbackDerived {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(ringedSpaceModulePullback f).Additive]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)] :
    ModuleDerived Y ⥤ ModuleDerived X :=
  Functor.totalLeftDerived (modulePullbackToDerived f)
    (DerivedCategory.Qh : HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤ ModuleDerived Y)
    (ModuleQis Y)

/-- The source object `Lg^* Rf_* K` of the unbounded base-change map. -/
abbrev derivedBaseChangeSource {X S S' : RingedSpace.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [(ringedSpaceModulePushforward f).Additive]
    [(ringedSpaceModulePullback g).Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g) (ModuleQis S)]
    (K : ModuleDerived X) : ModuleDerived S' :=
  (modulePullbackDerived g).obj ((modulePushforwardDerived f).obj K)

/-- The target object `R(f')_* L(g')^* K` of the unbounded base-change map. -/
abbrev derivedBaseChangeTarget {X X' S' : RingedSpace.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S')
    [(ringedSpaceModulePullback g').Additive]
    [(ringedSpaceModulePushforward f').Additive]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g') (ModuleQis X)]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f') (ModuleQis X')]
    (K : ModuleDerived X) : ModuleDerived S' :=
  (modulePushforwardDerived f').obj ((modulePullbackDerived g').obj K)

/-- The defining adjoint formula for the unbounded base-change map of a single square. -/
def IsUnboundedDerivedBaseChangeMap
    {X' X Y' Y : RingedSpace.{u}}
    (k : X' ⟶ X) (f' : X' ⟶ Y') (l : Y' ⟶ Y) (f : X ⟶ Y)
    [(ringedSpaceModulePullback k).Additive]
    [(ringedSpaceModulePushforward f').Additive]
    [(ringedSpaceModulePullback l).Additive]
    [(ringedSpaceModulePushforward f).Additive]
    [(ringedSpaceModulePullback f').Additive]
    [(ringedSpaceModulePullback f).Additive]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived k) (ModuleQis X)]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f') (ModuleQis X')]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived l) (ModuleQis Y)]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f') (ModuleQis Y')]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]
    (adjf : modulePullbackDerived f ⊣ modulePushforwardDerived f)
    (adjf' : modulePullbackDerived f' ⊣ modulePushforwardDerived f')
    (hpull : modulePullbackDerived l ⋙ modulePullbackDerived f' ≅
      modulePullbackDerived f ⋙ modulePullbackDerived k)
    (K : ModuleDerived X)
    (τ : derivedBaseChangeSource f l K ⟶ derivedBaseChangeTarget k f' K) : Prop :=
  ((adjf'.homEquiv (derivedBaseChangeSource f l K) ((modulePullbackDerived k).obj K)).symm τ) =
    (hpull.hom.app ((modulePushforwardDerived f).obj K) ≫
      (modulePullbackDerived k).map (adjf.counit.app K))

/-- The source object `Lm^* Rg_* Rf_* K` for the composed base-change map of the outer
rectangle. -/
abbrev composedDerivedBaseChangeSource
    {X Y Z Z' : RingedSpace.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (m : Z' ⟶ Z)
    [(ringedSpaceModulePushforward f).Additive]
    [(ringedSpaceModulePushforward g).Additive]
    [(ringedSpaceModulePullback m).Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived g) (ModuleQis Y)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived m) (ModuleQis Z)]
    (K : ModuleDerived X) : ModuleDerived Z' :=
  (modulePullbackDerived m).obj (((modulePushforwardDerived f) ⋙ (modulePushforwardDerived g)).obj K)

/-- The target object `Rg'_* Rf'_* Lk^* K` for the composed base-change map of the outer
rectangle. -/
abbrev composedDerivedBaseChangeTarget
    {X' X Y' Z' : RingedSpace.{u}}
    (k : X' ⟶ X) (f' : X' ⟶ Y') (g' : Y' ⟶ Z')
    [(ringedSpaceModulePullback k).Additive]
    [(ringedSpaceModulePushforward f').Additive]
    [(ringedSpaceModulePushforward g').Additive]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived k) (ModuleQis X)]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f') (ModuleQis X')]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived g') (ModuleQis Y')]
    (K : ModuleDerived X) : ModuleDerived Z' :=
  ((modulePushforwardDerived f') ⋙ (modulePushforwardDerived g')).obj ((modulePullbackDerived k).obj K)

/-- The defining adjoint formula for the composite of two unbounded base-change maps in a
three-row diagram of ringed spaces. -/
def IsComposedUnboundedDerivedBaseChangeMap
    {X' X Y' Y Z' Z : RingedSpace.{u}}
    (k : X' ⟶ X) (f' : X' ⟶ Y') (l : Y' ⟶ Y) (f : X ⟶ Y) (m : Z' ⟶ Z) (g' : Y' ⟶ Z')
    (g : Y ⟶ Z)
    [(ringedSpaceModulePullback k).Additive]
    [(ringedSpaceModulePushforward f').Additive]
    [(ringedSpaceModulePullback l).Additive]
    [(ringedSpaceModulePushforward f).Additive]
    [(ringedSpaceModulePullback m).Additive]
    [(ringedSpaceModulePushforward g').Additive]
    [(ringedSpaceModulePushforward g).Additive]
    [(ringedSpaceModulePullback g').Additive]
    [(ringedSpaceModulePullback g).Additive]
    [(ringedSpaceModulePullback f').Additive]
    [(ringedSpaceModulePullback f).Additive]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived k) (ModuleQis X)]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f') (ModuleQis X')]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived l) (ModuleQis Y)]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived m) (ModuleQis Z)]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived g') (ModuleQis Y')]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived g) (ModuleQis Y)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g') (ModuleQis Z')]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g) (ModuleQis Z)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f') (ModuleQis Y')]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]
    (adjf : modulePullbackDerived f ⊣ modulePushforwardDerived f)
    (adjf' : modulePullbackDerived f' ⊣ modulePushforwardDerived f')
    (adjg : modulePullbackDerived g ⊣ modulePushforwardDerived g)
    (adjg' : modulePullbackDerived g' ⊣ modulePushforwardDerived g')
    (hpull₁ : modulePullbackDerived l ⋙ modulePullbackDerived f' ≅
      modulePullbackDerived f ⋙ modulePullbackDerived k)
    (hpull₂ : modulePullbackDerived m ⋙ modulePullbackDerived g' ≅
      modulePullbackDerived g ⋙ modulePullbackDerived l)
    (K : ModuleDerived X)
    (τ : composedDerivedBaseChangeSource f g m K ⟶ composedDerivedBaseChangeTarget k f' g' K) :
    Prop :=
  (((adjg'.comp adjf').homEquiv (composedDerivedBaseChangeSource f g m K)
      ((modulePullbackDerived k).obj K)).symm τ) =
    ((Functor.whiskerRight hpull₂.hom (modulePullbackDerived f')).app
        (((modulePushforwardDerived f) ⋙ (modulePushforwardDerived g)).obj K) ≫
      (Functor.whiskerLeft (modulePullbackDerived g) hpull₁.hom).app
        (((modulePushforwardDerived f) ⋙ (modulePushforwardDerived g)).obj K) ≫
      (modulePullbackDerived k).map ((adjg.comp adjf).counit.app K))

section Composition

variable {X' X Y' Y Z' Z : RingedSpace.{u}}
variable (k : X' ⟶ X) (f' : X' ⟶ Y') (l : Y' ⟶ Y) (f : X ⟶ Y)
variable (m : Z' ⟶ Z) (g' : Y' ⟶ Z') (g : Y ⟶ Z)

variable [(ringedSpaceModulePullback k).Additive]
variable [(ringedSpaceModulePushforward f').Additive]
variable [(ringedSpaceModulePullback l).Additive]
variable [(ringedSpaceModulePushforward f).Additive]
variable [(ringedSpaceModulePullback m).Additive]
variable [(ringedSpaceModulePushforward g').Additive]
variable [(ringedSpaceModulePushforward g).Additive]
variable [(ringedSpaceModulePullback g').Additive]
variable [(ringedSpaceModulePullback g).Additive]
variable [(ringedSpaceModulePullback f').Additive]
variable [(ringedSpaceModulePullback f).Additive]

variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived k) (ModuleQis X)]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f') (ModuleQis X')]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived l) (ModuleQis Y)]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived m) (ModuleQis Z)]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived g') (ModuleQis Y')]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived g) (ModuleQis Y)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g') (ModuleQis Z')]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g) (ModuleQis Z)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f') (ModuleQis Y')]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]

-- Proof sketch: transpose the composite `Lm^*Rg_*Rf_*K ⟶ Rg'_*Ll^*Rf_*K ⟶ Rg'_*Rf'_*Lk^*K`
-- across the composite adjunction `Lg'^* ⋙ Lf'^* ⊣ Rf'_* ⋙ Rg'_*`. Naturality of the two
-- hom-set equivalences identifies its adjoint with the lower-square pullback comparison, then the
-- upper-square pullback comparison, followed by the counit for the composite adjunction
-- `(adjg.comp adjf)`, which is exactly the rectangle formula.
/-- Remark 20.28.4: for a commutative diagram of ringed spaces
`X' \xrightarrow{k} X`, `Y' \xrightarrow{l} Y`, `Z' \xrightarrow{m} Z` with vertical maps
`f' : X' \to Y'`, `f : X \to Y`, `g' : Y' \to Z'`, and `g : Y \to Z`, if `τ₁` and `τ₂` are the
base-change maps for the upper and lower squares as in Remark 20.28.3, then the composite
`Lm^* Rg_* Rf_* K \to Rg'_* Ll^* Rf_* K \to Rg'_* Rf'_* Lk^* K` is the base-change map for the
outer rectangle. -/
theorem unbounded_derived_baseChange_map_comp
    (adjf : modulePullbackDerived f ⊣ modulePushforwardDerived f)
    (adjf' : modulePullbackDerived f' ⊣ modulePushforwardDerived f')
    (adjg : modulePullbackDerived g ⊣ modulePushforwardDerived g)
    (adjg' : modulePullbackDerived g' ⊣ modulePushforwardDerived g')
    (hpull₁ : modulePullbackDerived l ⋙ modulePullbackDerived f' ≅
      modulePullbackDerived f ⋙ modulePullbackDerived k)
    (hpull₂ : modulePullbackDerived m ⋙ modulePullbackDerived g' ≅
      modulePullbackDerived g ⋙ modulePullbackDerived l)
    (K : ModuleDerived X)
    (τ₁ : derivedBaseChangeSource f l K ⟶ derivedBaseChangeTarget k f' K)
    (hτ₁ : IsUnboundedDerivedBaseChangeMap k f' l f adjf adjf' hpull₁ K τ₁)
    (τ₂ : derivedBaseChangeSource g m ((modulePushforwardDerived f).obj K) ⟶
      derivedBaseChangeTarget l g' ((modulePushforwardDerived f).obj K))
    (hτ₂ : IsUnboundedDerivedBaseChangeMap l g' m g adjg adjg' hpull₂
      ((modulePushforwardDerived f).obj K) τ₂) :
    IsComposedUnboundedDerivedBaseChangeMap k f' l f m g' g adjf adjf' adjg adjg' hpull₁ hpull₂ K
      (τ₂ ≫ (modulePushforwardDerived g').map τ₁) := sorry

end Composition

end AlgebraicGeometry.RingedSpace

/-! ### Remark_20_28_5 (from Chap20) -/
open CategoryTheory
open ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

attribute [local instance] HasDerivedCategory.standard

/-- The pullback functor on `\mathcal O_Y`-modules attached to a morphism of ringed spaces. -/
noncomputable abbrev ringedSpaceModulePullback {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    SheafOfModules ((RingedSpace.ringCatSheaf Y)) ⥤
      SheafOfModules ((RingedSpace.ringCatSheaf X)) :=
  SheafOfModules.pullback (ringedSpacePushforwardStructureSheafHom f)

/-- The category of sheaves of `\mathcal O_X`-modules on a ringed space. -/
/-- The quasi-isomorphisms in the homotopy category of unbounded complexes of
`\mathcal O_X`-modules on a ringed space. -/
abbrev ModuleQis (X : RingedSpace.{u}) :=
  HomotopyCategory.quasiIso (RingedSpace.Modules X) (up ℤ)

/-- The unbounded derived category `D(\mathcal O_X)` of a ringed space. -/
abbrev ModuleDerived (X : RingedSpace.{u}) :=
  DerivedCategory (RingedSpace.Modules X)

/-- The functor on homotopy categories induced by direct image on module sheaves. -/
abbrev modulePushforwardToDerived {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(ringedSpaceModulePushforward f).Additive] :
    HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤ ModuleDerived Y :=
  (ringedSpaceModulePushforward f).mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh

/-- The functor on homotopy categories induced by inverse image on module sheaves. -/
abbrev modulePullbackToDerived {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(ringedSpaceModulePullback f).Additive] :
    HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤ ModuleDerived X :=
  (ringedSpaceModulePullback f).mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh

/-- The unbounded derived direct image functor `Rf_*` on module sheaves over ringed spaces. -/
abbrev modulePushforwardDerived {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(ringedSpaceModulePushforward f).Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)] :
    ModuleDerived X ⥤ ModuleDerived Y :=
  Functor.totalRightDerived (modulePushforwardToDerived f)
    (DerivedCategory.Qh : HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤ ModuleDerived X)
    (ModuleQis X)

/-- The unbounded derived inverse-image functor `Lf^*`. -/
abbrev modulePullbackDerived {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(ringedSpaceModulePullback f).Additive]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)] :
    ModuleDerived Y ⥤ ModuleDerived X :=
  Functor.totalLeftDerived (modulePullbackToDerived f)
    (DerivedCategory.Qh : HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤ ModuleDerived Y)
    (ModuleQis Y)

/-- The source object `Lg^* Rf_* K` of an unbounded derived base-change morphism. -/
abbrev derivedBaseChangeSource {X S S' : RingedSpace.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [(ringedSpaceModulePushforward f).Additive]
    [(ringedSpaceModulePullback g).Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g) (ModuleQis S)]
    (K : ModuleDerived X) : ModuleDerived S' :=
  (modulePullbackDerived g).obj ((modulePushforwardDerived f).obj K)

/-- The target object `R(f')_* L(g')^* K` of an unbounded derived base-change morphism. -/
abbrev derivedBaseChangeTarget {X X' S' : RingedSpace.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S')
    [(ringedSpaceModulePullback g').Additive]
    [(ringedSpaceModulePushforward f').Additive]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g') (ModuleQis X)]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f') (ModuleQis X')]
    (K : ModuleDerived X) : ModuleDerived S' :=
  (modulePushforwardDerived f').obj ((modulePullbackDerived g').obj K)

/-- A morphism `Lg^* Rf_* K ⟶ R(f')_* L(g')^* K` is an unbounded derived base-change map if,
after transposing across `L(f')^* ⊣ R(f')_*`, it is the pullback of the counit
`Lf^* Rf_* K ⟶ K` transported along the chosen pullback-commutativity isomorphism. -/
def IsUnboundedBaseChangeMap
    {X' X Y' Y : RingedSpace.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y)
    [(ringedSpaceModulePushforward f).Additive]
    [(ringedSpaceModulePushforward f').Additive]
    [(ringedSpaceModulePullback f).Additive]
    [(ringedSpaceModulePullback f').Additive]
    [(ringedSpaceModulePullback g).Additive]
    [(ringedSpaceModulePullback g').Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f') (ModuleQis X')]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g) (ModuleQis Y)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g') (ModuleQis X)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f') (ModuleQis Y')]
    (hpull : modulePullbackDerived g ⋙ modulePullbackDerived f' ≅
      modulePullbackDerived f ⋙ modulePullbackDerived g')
    (adj_f : modulePullbackDerived f ⊣ modulePushforwardDerived f)
    (adj_f' : modulePullbackDerived f' ⊣ modulePushforwardDerived f')
    (K : ModuleDerived X)
    (η : derivedBaseChangeSource f g K ⟶ derivedBaseChangeTarget g' f' K) : Prop :=
  ((adj_f'.homEquiv (derivedBaseChangeSource f g K) ((modulePullbackDerived g').obj K)).symm η) =
    (hpull.hom.app ((modulePushforwardDerived f).obj K) ≫
      (modulePullbackDerived g').map (adj_f.counit.app K))

section

variable {X'' X' X Y'' Y' Y : RingedSpace.{u}}
variable (g' : X'' ⟶ X') (g : X' ⟶ X)
variable (f'' : X'' ⟶ Y'') (f' : X' ⟶ Y') (f : X ⟶ Y)
variable (h' : Y'' ⟶ Y') (h : Y' ⟶ Y)

variable [(ringedSpaceModulePullback g').Additive]
variable [(ringedSpaceModulePullback g).Additive]
variable [(ringedSpaceModulePullback (g' ≫ g)).Additive]
variable [(ringedSpaceModulePullback h').Additive]
variable [(ringedSpaceModulePullback h).Additive]
variable [(ringedSpaceModulePullback (h' ≫ h)).Additive]
variable [(ringedSpaceModulePullback f'').Additive]
variable [(ringedSpaceModulePullback f').Additive]
variable [(ringedSpaceModulePullback f).Additive]
variable [(ringedSpaceModulePushforward f'').Additive]
variable [(ringedSpaceModulePushforward f').Additive]
variable [(ringedSpaceModulePushforward f).Additive]

variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g') (ModuleQis X')]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g) (ModuleQis X)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived (g' ≫ g)) (ModuleQis X)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived h') (ModuleQis Y')]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived h) (ModuleQis Y)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived (h' ≫ h)) (ModuleQis Y)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f'') (ModuleQis Y'')]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f') (ModuleQis Y')]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f'') (ModuleQis X'')]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f') (ModuleQis X')]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]

/-- The pullback commutativity isomorphisms for two horizontally composable squares combine to
the pullback commutativity isomorphism for the outer rectangle. -/
def horizontalCompositePullbackIso
    (hpull₀ : modulePullbackDerived h ⋙ modulePullbackDerived f' ≅
      modulePullbackDerived f ⋙ modulePullbackDerived g)
    (hpull₁ : modulePullbackDerived h' ⋙ modulePullbackDerived f'' ≅
      modulePullbackDerived f' ⋙ modulePullbackDerived g')
    (hcomp : modulePullbackDerived (h' ≫ h) ≅
      modulePullbackDerived h ⋙ modulePullbackDerived h')
    (gcomp : modulePullbackDerived (g' ≫ g) ≅
      modulePullbackDerived g ⋙ modulePullbackDerived g') :
    modulePullbackDerived (h' ≫ h) ⋙ modulePullbackDerived f'' ≅
      modulePullbackDerived f ⋙ modulePullbackDerived (g' ≫ g) :=
  Functor.isoWhiskerRight hcomp (modulePullbackDerived f'') ≪≫
    Functor.associator (modulePullbackDerived h) (modulePullbackDerived h')
      (modulePullbackDerived f'') ≪≫
    Functor.isoWhiskerLeft (modulePullbackDerived h) hpull₁ ≪≫
    (Functor.associator (modulePullbackDerived h) (modulePullbackDerived f')
      (modulePullbackDerived g')).symm ≪≫
    Functor.isoWhiskerRight hpull₀ (modulePullbackDerived g') ≪≫
    Functor.associator (modulePullbackDerived f) (modulePullbackDerived g)
      (modulePullbackDerived g') ≪≫
    Functor.isoWhiskerLeft (modulePullbackDerived f) gcomp.symm

/-- The composite of the two base-change maps associated to adjacent squares, rewritten as a
morphism from the outer pullback of `Rf_*` to the outer pushforward of the iterated pullback. -/
def horizontalCompositeUnboundedBaseChangeMap
    (K : ModuleDerived X)
    (η₀ : derivedBaseChangeSource f h K ⟶ derivedBaseChangeTarget g f' K)
    (η₁ :
      derivedBaseChangeSource f' h' ((modulePullbackDerived g).obj K) ⟶
        derivedBaseChangeTarget g' f'' ((modulePullbackDerived g).obj K))
    (hcomp : modulePullbackDerived (h' ≫ h) ≅
      modulePullbackDerived h ⋙ modulePullbackDerived h')
    (gcomp : modulePullbackDerived (g' ≫ g) ≅
      modulePullbackDerived g ⋙ modulePullbackDerived g') :
    derivedBaseChangeSource f (h' ≫ h) K ⟶ derivedBaseChangeTarget (g' ≫ g) f'' K :=
  (hcomp.hom.app ((modulePushforwardDerived f).obj K)) ≫
    (modulePullbackDerived h').map η₀ ≫
    η₁ ≫
    (modulePushforwardDerived f'').map (gcomp.inv.app K)

-- Proof sketch: expand the outer pullback commutativity isomorphism by composing the two square
-- isomorphisms with associators, then transpose the composite morphism along the adjunction
-- `L(f'')^* ⊣ R(f'')_*`. The hypotheses identifying `η₀` and `η₁` as base-change maps reduce the
-- transpose to the counit expression for the outer rectangle.
/-- Remark 20.28.5: for two composable squares of ringed spaces, the base-change maps of Remark
20.28.3 for the two inner squares compose to the base-change map for the outer rectangle. -/
theorem horizontalComposite_isUnboundedBaseChangeMap
    (hpull₀ : modulePullbackDerived h ⋙ modulePullbackDerived f' ≅
      modulePullbackDerived f ⋙ modulePullbackDerived g)
    (hpull₁ : modulePullbackDerived h' ⋙ modulePullbackDerived f'' ≅
      modulePullbackDerived f' ⋙ modulePullbackDerived g')
    (hcomp : modulePullbackDerived (h' ≫ h) ≅
      modulePullbackDerived h ⋙ modulePullbackDerived h')
    (gcomp : modulePullbackDerived (g' ≫ g) ≅
      modulePullbackDerived g ⋙ modulePullbackDerived g')
    (adj_f : modulePullbackDerived f ⊣ modulePushforwardDerived f)
    (adj_f' : modulePullbackDerived f' ⊣ modulePushforwardDerived f')
    (adj_f'' : modulePullbackDerived f'' ⊣ modulePushforwardDerived f'')
    (K : ModuleDerived X)
    (η₀ : derivedBaseChangeSource f h K ⟶ derivedBaseChangeTarget g f' K)
    (η₁ :
      derivedBaseChangeSource f' h' ((modulePullbackDerived g).obj K) ⟶
        derivedBaseChangeTarget g' f'' ((modulePullbackDerived g).obj K))
    (hη₀ : IsUnboundedBaseChangeMap g f' f h hpull₀ adj_f adj_f' K η₀)
    (hη₁ :
      IsUnboundedBaseChangeMap g' f'' f' h' hpull₁ adj_f' adj_f''
        ((modulePullbackDerived g).obj K) η₁) :
    IsUnboundedBaseChangeMap
      (g' ≫ g)
      f''
      f
      (h' ≫ h)
      (horizontalCompositePullbackIso g' g f'' f' f h' h hpull₀ hpull₁ hcomp gcomp)
      adj_f
      adj_f''
      K
      (horizontalCompositeUnboundedBaseChangeMap g' g f'' f' f h' h K η₀ η₁ hcomp gcomp) := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_28_6 (from Chap20) -/
open CategoryTheory
open ComplexShape
open AlgebraicGeometry

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The structure sheaf of a ringed space, regarded as a sheaf of not-necessarily-commutative
rings. -/
/-- The category of sheaves of `\mathcal O_X`-modules on a ringed space `X`. -/
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

/-- The direct-image functor on module sheaves induced by a morphism of ringed spaces. -/
noncomputable abbrev modulePushforward {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    (RingedSpace.Modules X) ⥤ (RingedSpace.Modules Y) :=
  SheafOfModules.pushforward (pushforwardStructureSheafHom f)

/-- The pullback functor on module sheaves induced by a morphism of ringed spaces. -/
noncomputable abbrev modulePullback {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    (RingedSpace.Modules Y) ⥤ (RingedSpace.Modules X) :=
  SheafOfModules.pullback (pushforwardStructureSheafHom f)

/-- The quasi-isomorphisms used to localize the homotopy category of `\mathcal O_X`-modules. -/
abbrev ModuleQis (X : RingedSpace.{u}) :=
  HomotopyCategory.quasiIso (RingedSpace.Modules X) (up ℤ)

/-- The unbounded derived category `D(\mathcal O_X)` of `\mathcal O_X`-module sheaves. -/
abbrev ModuleDerived (X : RingedSpace.{u}) :=
  DerivedCategory (RingedSpace.Modules X)

/-- The localization functor from complexes to the homotopy category. -/
abbrev complexToHomotopy (X : RingedSpace.{u}) :
    CochainComplex (RingedSpace.Modules X) ℤ ⥤ HomotopyCategory (RingedSpace.Modules X) (up ℤ) :=
  HomotopyCategory.quotient (RingedSpace.Modules X) (up ℤ)

/-- The functor on homotopy categories induced by pullback on module sheaves. -/
abbrev modulePullbackHomotopy {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(modulePullback f).Additive] :
    HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤ HomotopyCategory (RingedSpace.Modules X) (up ℤ) :=
  (modulePullback f).mapHomotopyCategory (up ℤ)

/-- The functor on homotopy categories induced by pushforward on module sheaves. -/
abbrev modulePushforwardHomotopy {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(modulePushforward f).Additive] :
    HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤ HomotopyCategory (RingedSpace.Modules Y) (up ℤ) :=
  (modulePushforward f).mapHomotopyCategory (up ℤ)

/-- The functor on homotopy categories followed by localization that models the underived
pullback on complexes in the derived category. -/
abbrev modulePullbackToDerived {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(modulePullback f).Additive] :
    HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤ ModuleDerived X :=
  modulePullbackHomotopy f ⋙ DerivedCategory.Qh

/-- The functor on homotopy categories followed by localization that models the underived
direct image on complexes in the derived category. -/
abbrev modulePushforwardToDerived {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(modulePushforward f).Additive] :
    HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤ ModuleDerived Y :=
  modulePushforwardHomotopy f ⋙ DerivedCategory.Qh

/-- The derived pullback functor `Lf^* : D(\mathcal O_Y) ⥤ D(\mathcal O_X)`. -/
abbrev modulePullbackDerived {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    [(modulePullback f).Additive]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)] :
    ModuleDerived Y ⥤ ModuleDerived X :=
  Functor.totalLeftDerived (modulePullbackToDerived f)
    (DerivedCategory.Qh : HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤ ModuleDerived Y)
    (ModuleQis Y)

/-- The derived direct-image functor `Rf_* : D(\mathcal O_X) ⥤ D(\mathcal O_Y)`. -/
abbrev moduleDerivedPushforward {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(modulePushforward f).Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)] :
    ModuleDerived X ⥤ ModuleDerived Y :=
  Functor.totalRightDerived (modulePushforwardToDerived f)
    (DerivedCategory.Qh : HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤ ModuleDerived X)
    (ModuleQis X)

/-- The canonical comparison `Lf^* \to f^*` on homotopy-category representatives of complexes. -/
noncomputable abbrev derivedPullbackCounit {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    [(modulePullback f).Additive]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)] :
    (DerivedCategory.Qh : HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤ ModuleDerived Y) ⋙
      modulePullbackDerived f ⟶ modulePullbackToDerived f :=
  Functor.totalLeftDerivedCounit (modulePullbackToDerived f)
    (DerivedCategory.Qh : HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤ ModuleDerived Y)
    (ModuleQis Y)

/-- The canonical comparison `f_* \to Rf_*` on homotopy-category representatives of complexes. -/
noncomputable abbrev derivedPushforwardUnit {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(modulePushforward f).Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)] :
    modulePushforwardToDerived f ⟶
      (DerivedCategory.Qh : HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤ ModuleDerived X) ⋙
        moduleDerivedPushforward f :=
  Functor.totalRightDerivedUnit (modulePushforwardToDerived f)
    (DerivedCategory.Qh : HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤ ModuleDerived X)
    (ModuleQis X)

/-- The canonical counit `Lf^* Rf_* \to \mathrm{id}` induced by a chosen homotopy-level adjunction
between pullback and pushforward. -/
noncomputable abbrev derivedPullbackPushforwardCounit
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    [(modulePullback f).Additive] [(modulePushforward f).Additive]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
    (adj : modulePullbackHomotopy f ⊣ modulePushforwardHomotopy f)
    [((moduleDerivedPushforward f) ⋙ (modulePullbackDerived f)).IsRightDerivedFunctor
      (Functor.whiskerRight (derivedPushforwardUnit f) (modulePullbackDerived f) ≫
        (Functor.associator
          (DerivedCategory.Qh : HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤ ModuleDerived X)
          (moduleDerivedPushforward f) (modulePullbackDerived f)).hom) (ModuleQis X)] :
    moduleDerivedPushforward f ⋙ modulePullbackDerived f ⟶ 𝟭 (ModuleDerived X) :=
  adj.derivedε (ModuleQis X) (derivedPullbackCounit f) (derivedPushforwardUnit f)

-- Proof sketch: specialize `Adjunction.derivedε_fac_app` to the pullback-pushforward adjunction on
-- homotopy categories. The left vertical arrow is `Lf^*` applied to the canonical map
-- `f_* K^\bullet \to Rf_* K^\bullet`, the top horizontal arrow is the counit
-- `Lf^*(f_* K^\bullet) \to f^* f_* K^\bullet`, and the right vertical arrow is the image of the
-- underived adjunction counit `f^* f_* K^\bullet \to K^\bullet` in the derived category.
/-- Lemma 20.28.6: for a morphism of ringed spaces and a complex `K^\bullet`, the square in the
derived category obtained from the comparison `Lf^* \to f^*` on complexes, the comparison
`f_* \to Rf_*` on complexes, and the counit `Lf^* Rf_* \to \mathrm{id}` of the derived adjunction
commutes. The underived right edge is taken with respect to a chosen adjunction on homotopy
categories representing `f^* \dashv f_*`. -/
theorem derived_pullback_pushforward_counit_square_commutes
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    [(modulePullback f).Additive] [(modulePushforward f).Additive]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
    (adj : modulePullbackHomotopy f ⊣ modulePushforwardHomotopy f)
    [((moduleDerivedPushforward f) ⋙ (modulePullbackDerived f)).IsRightDerivedFunctor
      (Functor.whiskerRight (derivedPushforwardUnit f) (modulePullbackDerived f) ≫
        (Functor.associator
          (DerivedCategory.Qh : HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤ ModuleDerived X)
          (moduleDerivedPushforward f) (modulePullbackDerived f)).hom) (ModuleQis X)]
    (K : CochainComplex (RingedSpace.Modules X) ℤ) :
    (modulePullbackDerived f).map ((derivedPushforwardUnit f).app ((complexToHomotopy X).obj K)) ≫
        (derivedPullbackPushforwardCounit f adj).app
          ((DerivedCategory.Qh : HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤ ModuleDerived X).obj
            ((complexToHomotopy X).obj K)) =
      (derivedPullbackCounit f).app
          ((modulePushforwardHomotopy f).obj ((complexToHomotopy X).obj K)) ≫
        (DerivedCategory.Qh : HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤ ModuleDerived X).map
          (adj.counit.app ((complexToHomotopy X).obj K)) := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Remark_20_28_7 (from Chap20) -/
open CategoryTheory

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The structure sheaf of a ringed space, regarded as a sheaf of rings. -/
section

variable {X Y : RingedSpace.{u}}

local notation "DModX" => DerivedCategory (SheafOfModules (ringCatSheaf X))
local notation "DModY" => DerivedCategory (SheafOfModules (ringCatSheaf Y))

variable (leftDerivedPullback : DModY ⥤ DModX)
variable (rightDerivedPushforward : DModX ⥤ DModY)
variable (pullPushAdj : leftDerivedPullback ⊣ rightDerivedPushforward)
variable (derivedTensorX : DModX ⥤ DModX ⥤ DModX)
variable (derivedTensorY : DModY ⥤ DModY ⥤ DModY)
variable (pullbackTensorIso :
  ∀ (A B : DModY),
    leftDerivedPullback.obj ((derivedTensorY.obj B).obj A) ≅
      ((derivedTensorX.obj (leftDerivedPullback.obj B)).obj (leftDerivedPullback.obj A)))

/-- The adjoint-side morphism whose transpose is the relative cup product. -/
private noncomputable abbrev relativeDerivedCupProductAdjoint
    (K L : DModX) :
    leftDerivedPullback.obj
        ((derivedTensorY.obj (rightDerivedPushforward.obj L)).obj
          (rightDerivedPushforward.obj K)) ⟶
      ((derivedTensorX.obj L).obj K) :=
  (pullbackTensorIso
      (rightDerivedPushforward.obj K)
      (rightDerivedPushforward.obj L)).hom ≫
    ((derivedTensorX.map (pullPushAdj.counit.app L)).app
      (leftDerivedPullback.obj (rightDerivedPushforward.obj K))) ≫
    ((derivedTensorX.obj L).map (pullPushAdj.counit.app K))

/-- Remark 20.28.7: given the adjunction `Lf^* ⊣ Rf_*` and the pullback-tensor comparison of
Lemma 20.27.3, there is a canonical relative cup product
`Rf_* K \otimes^{\mathbf L} Rf_* L ⟶ Rf_*(K \otimes^{\mathbf L} L)`. -/
noncomputable def relativeDerivedCupProduct
    (K L : DModX) :
    ((derivedTensorY.obj (rightDerivedPushforward.obj L)).obj
      (rightDerivedPushforward.obj K)) ⟶
      rightDerivedPushforward.obj ((derivedTensorX.obj L).obj K) :=
  (pullPushAdj.homEquiv _ _)
    (relativeDerivedCupProductAdjoint
      leftDerivedPullback rightDerivedPushforward pullPushAdj derivedTensorX derivedTensorY
      pullbackTensorIso K L)

-- Proof sketch: unfold `relativeDerivedCupProduct`; it was defined by applying the adjunction
-- equivalence `Hom(Lf^* -, -) ≃ Hom(-, Rf_* -)` to the counit-induced composite after the
-- pullback-tensor comparison.
/-- The relative cup product is adjoint to the pullback-tensor comparison followed by the two
counit maps `Lf^* Rf_* K ⟶ K` and `Lf^* Rf_* L ⟶ L`. -/
theorem relativeDerivedCupProduct_homEquiv
    (K L : DModX) :
    (pullPushAdj.homEquiv _ _)
        (relativeDerivedCupProduct leftDerivedPullback rightDerivedPushforward pullPushAdj
          derivedTensorX derivedTensorY pullbackTensorIso K L) =
      relativeDerivedCupProductAdjoint leftDerivedPullback rightDerivedPushforward pullPushAdj
        derivedTensorX derivedTensorY pullbackTensorIso K L := sorry

end

end AlgebraicGeometry.RingedSpace
