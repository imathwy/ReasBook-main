import Mathlib
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_21_18_1 (from Chap21) -/
open CategoryTheory
open ComplexShape
open CochainComplex

noncomputable section

universe u

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify JC AddCommGrpCat.{u}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify JD AddCommGrpCat.{u}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (F : C ⥤ D) [Functor.IsContinuous F JC JD]
variable {𝒪 : Sheaf JC CommRingCat.{u}} {𝒪' : Sheaf JD CommRingCat.{u}}
variable (φ : 𝒪 ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪')

/-- The underlying `RingCat`-valued structure map attached to the site-presented morphism of
ringed topoi determined by `φ`. -/
private abbrev ringedSiteUnderlyingStructureMap :
    (sheafCompose JC (forget₂ CommRingCat RingCat)).obj 𝒪 ⟶
      (F.sheafPushforwardContinuous RingCat JC JD).obj
        ((sheafCompose JD (forget₂ CommRingCat RingCat)).obj 𝒪') :=
  (sheafCompose JC (forget₂ CommRingCat RingCat)).map φ

variable [MonoidalCategory (SheafOfModules ((sheafCompose JC (forget₂ CommRingCat RingCat)).obj 𝒪))]
variable [MonoidalPreadditive
  (SheafOfModules ((sheafCompose JC (forget₂ CommRingCat RingCat)).obj 𝒪))]
variable [MonoidalCategory (SheafOfModules ((sheafCompose JD (forget₂ CommRingCat RingCat)).obj 𝒪'))]
variable [MonoidalPreadditive
  (SheafOfModules ((sheafCompose JD (forget₂ CommRingCat RingCat)).obj 𝒪'))]

-- Proof sketch: apply Lemma `18.39.1` degreewise to obtain flatness of every pulled-back term.
-- For K-flatness, follow the textbook resolution argument: replace `K` by the sequential
-- bounded-above flat resolution tower from Lemma `21.17.10`, pull that tower back termwise,
-- use Lemmas `21.17.8` and `21.17.9` to keep the pulled-back colimit K-flat, and then apply the
-- short-exact-sequence criterion of Lemma `21.17.7` after pulling back the comparison short exact
-- sequence via Lemma `18.39.4`.
/-- Lemma 21.18.1: for a site-presented morphism of ringed topoi, pulling back a K-flat cochain
complex of `\mathcal O`-modules whose terms are flat yields a K-flat cochain complex of
`\mathcal O'`-modules whose terms are flat. -/
theorem pullback_isKFlat_and_termwiseFlat_of_isKFlat_and_termwiseFlat
    (K : CochainComplex
      (SheafOfModules ((sheafCompose JC (forget₂ CommRingCat RingCat)).obj 𝒪)) ℤ)
    (hKFlat : IsKFlat K)
    (hFlat : ∀ n : ℤ, IsFlat 𝒪 (K.X n)) :
    IsKFlat
      (((SheafOfModules.pullback (ringedSiteUnderlyingStructureMap F φ)
          ).mapHomologicalComplex (up ℤ)).obj K) ∧
    ∀ n : ℤ,
      IsFlat 𝒪'
        ((SheafOfModules.pullback (ringedSiteUnderlyingStructureMap F φ)).obj (K.X n)) := sorry

end

end SheafOfModules.RingedSite

/-! ### Lemma_21_18_2 (from Chap21) -/
open CategoryTheory
open ComplexShape

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify JC AddCommGrpCat.{u}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasSheafify JD AddCommGrpCat.{u}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The category `\mathrm{Mod}(\mathcal O)` of sheaves of modules on a site with structure sheaf
`\mathcal O`. -/
abbrev RingedSiteModules (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{u}) :=
  SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)

/-- The unbounded derived category `D(\mathcal O)` of module sheaves on a ringed site. -/
abbrev RingedSiteDerived (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{u}) :=
  DerivedCategory (RingedSiteModules J 𝒪)

/-- The quasi-isomorphisms in the homotopy category of cochain complexes of `\mathcal O`-modules.
-/
abbrev RingedSiteQis (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{u}) :=
  HomotopyCategory.quasiIso (RingedSiteModules J 𝒪) (up ℤ)

variable (F : C ⥤ D) [Functor.IsContinuous F JC JD]
variable {𝒪' : Sheaf JC CommRingCat.{u}} {𝒪 : Sheaf JD CommRingCat.{u}}
variable (φ : 𝒪' ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪)

/-- The underlying `RingCat`-valued structure map attached to the site-presented morphism of
ringed topoi determined by `φ`. -/
abbrev ringedSiteUnderlyingStructureMap
    (F : C ⥤ D) [Functor.IsContinuous F JC JD]
    (φ : 𝒪' ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪) :
    (sheafCompose JC (forget₂ CommRingCat RingCat)).obj 𝒪' ⟶
      (F.sheafPushforwardContinuous RingCat.{u} JC JD).obj
        ((sheafCompose JD (forget₂ CommRingCat RingCat)).obj 𝒪) :=
  (sheafCompose JC (forget₂ CommRingCat RingCat)).map φ

variable [(SheafOfModules.pushforward (ringedSiteUnderlyingStructureMap F φ)).IsRightAdjoint]

/-- The inverse-image functor on module sheaves attached to the site-presented morphism of ringed
topoi determined by `φ`. -/
abbrev pullbackFunctor
    (F : C ⥤ D) [Functor.IsContinuous F JC JD]
    (φ : 𝒪' ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪) :
    RingedSiteModules JC 𝒪' ⥤ RingedSiteModules JD 𝒪 :=
  SheafOfModules.pullback (ringedSiteUnderlyingStructureMap F φ)

variable [Abelian (RingedSiteModules JC 𝒪')]
variable [CategoryWithHomology (RingedSiteModules JC 𝒪')]
variable [Abelian (RingedSiteModules JD 𝒪)]
variable [CategoryWithHomology (RingedSiteModules JD 𝒪)]
variable [MonoidalCategory (RingedSiteModules JC 𝒪')]
variable [MonoidalPreadditive (RingedSiteModules JC 𝒪')]
variable [MonoidalCategory (RingedSiteModules JD 𝒪)]
variable [MonoidalPreadditive (RingedSiteModules JD 𝒪)]

local instance instPreadditiveTarget : Preadditive (RingedSiteModules JC 𝒪') :=
  (inferInstance : Abelian (RingedSiteModules JC 𝒪')).toPreadditive

local instance instPreadditiveSource : Preadditive (RingedSiteModules JD 𝒪) :=
  (inferInstance : Abelian (RingedSiteModules JD 𝒪)).toPreadditive
/-- Lemma 21.18.2: the pullback functor on homotopy categories of module sheaves associated to a
site-presented morphism of ringed topoi admits a total left derived functor, giving the
unbounded derived pullback `Lf^* : D(\mathcal O') \to D(\mathcal O)`. -/
-- Proof sketch: apply Lemma `13.14.15` to the class of quasi-isomorphisms in the homotopy
-- category. Lemma `21.17.11` provides enough K-flat complexes with flat terms, while
-- Lemmas `21.18.1` and `21.17.12` show that pullback sends quasi-isomorphisms between those
-- chosen resolutions to quasi-isomorphisms.
theorem pullbackToDerived_hasLeftDerivedFunctor
    [hadd : (pullbackFunctor F φ).Additive] :
    Functor.HasLeftDerivedFunctor
      (mapHomotopyCategoryToDerived (pullbackFunctor F φ))
      (HomotopyCategory.quasiIso (RingedSiteModules JC 𝒪') (up ℤ)) := sorry

end

end SheafOfModules.RingedSite

/-! ### Lemma_21_18_3 (from Chap21) -/
open CategoryTheory
open ComplexShape

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C]
variable {D : Type u} [Category.{u} D]
variable {E : Type u} [Category.{u} E]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D} {JE : GrothendieckTopology E}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JE.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify JC AddCommGrpCat.{u}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasSheafify JD AddCommGrpCat.{u}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasSheafify JE AddCommGrpCat.{u}]
variable [JE.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The category `\mathrm{Mod}(\mathcal O)` of sheaves of modules on a site with structure sheaf
`\mathcal O`. -/
abbrev RingedSiteModules {X : Type u} [Category.{u} X]
    (J : GrothendieckTopology X) (𝒪 : Sheaf J CommRingCat.{u}) :=
  SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)

/-- The unbounded derived category `D(\mathcal O)` of module sheaves on a ringed site. -/
abbrev RingedSiteDerived {X : Type u} [Category.{u} X]
    (J : GrothendieckTopology X) (𝒪 : Sheaf J CommRingCat.{u}) :=
  DerivedCategory (RingedSiteModules J 𝒪)

/-- The quasi-isomorphisms in the homotopy category of cochain complexes of `\mathcal O`-modules.
-/
abbrev RingedSiteQis {X : Type u} [Category.{u} X]
    (J : GrothendieckTopology X) (𝒪 : Sheaf J CommRingCat.{u}) :=
  HomotopyCategory.quasiIso (RingedSiteModules J 𝒪) (up ℤ)

variable (F : C ⥤ D) [Functor.IsContinuous F JC JD]
variable (G : D ⥤ E) [Functor.IsContinuous G JD JE]
variable {𝒪C : Sheaf JC CommRingCat.{u}}
variable {𝒪D : Sheaf JD CommRingCat.{u}}
variable {𝒪E : Sheaf JE CommRingCat.{u}}
variable (φ : 𝒪C ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪D)
variable (ψ : 𝒪D ⟶ (G.sheafPushforwardContinuous CommRingCat.{u} JD JE).obj 𝒪E)

/-- The underlying `RingCat`-valued structure map attached to the site-presented morphism of
ringed topoi determined by `φ`. -/
abbrev ringedSiteUnderlyingStructureMap
    (F : C ⥤ D) [Functor.IsContinuous F JC JD]
    (φ : 𝒪C ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪D) :
    (sheafCompose JC (forget₂ CommRingCat RingCat)).obj 𝒪C ⟶
      (F.sheafPushforwardContinuous RingCat.{u} JC JD).obj
        ((sheafCompose JD (forget₂ CommRingCat RingCat)).obj 𝒪D) :=
  (sheafCompose JC (forget₂ CommRingCat RingCat)).map φ

variable [(SheafOfModules.pushforward (ringedSiteUnderlyingStructureMap F φ)).IsRightAdjoint]
variable [(SheafOfModules.pushforward (ringedSiteUnderlyingStructureMap G ψ)).IsRightAdjoint]

/-- The inverse-image functor on module sheaves attached to the site-presented morphism of ringed
topoi determined by `φ`. -/
abbrev pullbackFunctor
    (F : C ⥤ D) [Functor.IsContinuous F JC JD]
    (φ : 𝒪C ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪D) :
    RingedSiteModules JC 𝒪C ⥤ RingedSiteModules JD 𝒪D :=
  SheafOfModules.pullback (ringedSiteUnderlyingStructureMap F φ)

variable [Abelian (RingedSiteModules JC 𝒪C)]
variable [CategoryWithHomology (RingedSiteModules JC 𝒪C)]
variable [Abelian (RingedSiteModules JD 𝒪D)]
variable [CategoryWithHomology (RingedSiteModules JD 𝒪D)]
variable [Abelian (RingedSiteModules JE 𝒪E)]
variable [CategoryWithHomology (RingedSiteModules JE 𝒪E)]

local instance instPreadditiveModulesJC : Preadditive (RingedSiteModules JC 𝒪C) :=
  (inferInstance : Abelian (RingedSiteModules JC 𝒪C)).toPreadditive

local instance instPreadditiveModulesJD : Preadditive (RingedSiteModules JD 𝒪D) :=
  (inferInstance : Abelian (RingedSiteModules JD 𝒪D)).toPreadditive

local instance instPreadditiveModulesJE : Preadditive (RingedSiteModules JE 𝒪E) :=
  (inferInstance : Abelian (RingedSiteModules JE 𝒪E)).toPreadditive

/-- The homotopy-to-derived functor obtained by first pulling back along `F` on homotopy
categories and then applying the underived pullback-to-derived functor for `G`. -/
private abbrev compositeUnderivedPullbackToDerived
    (F : C ⥤ D) [Functor.IsContinuous F JC JD]
    (G : D ⥤ E) [Functor.IsContinuous G JD JE]
    (φ : 𝒪C ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪D)
    (ψ : 𝒪D ⟶ (G.sheafPushforwardContinuous CommRingCat.{u} JD JE).obj 𝒪E)
    [(SheafOfModules.pushforward (ringedSiteUnderlyingStructureMap F φ)).IsRightAdjoint]
    [(SheafOfModules.pushforward (ringedSiteUnderlyingStructureMap G ψ)).IsRightAdjoint]
    [(pullbackFunctor F φ).Additive]
    [(pullbackFunctor G ψ).Additive] :
    HomotopyCategory (RingedSiteModules JC 𝒪C) (up ℤ) ⥤
      DerivedCategory (RingedSiteModules JE 𝒪E) :=
  let FH :
      HomotopyCategory (RingedSiteModules JC 𝒪C) (up ℤ) ⥤
        HomotopyCategory (RingedSiteModules JD 𝒪D) (up ℤ) :=
    (pullbackFunctor F φ).mapHomotopyCategory (up ℤ)
  let GH :
      HomotopyCategory (RingedSiteModules JD 𝒪D) (up ℤ) ⥤
        HomotopyCategory (RingedSiteModules JE 𝒪E) (up ℤ) :=
    (pullbackFunctor G ψ).mapHomotopyCategory (up ℤ)
  FH ⋙ GH ⋙ DerivedCategory.Qh

variable [(pullbackFunctor F φ).Additive]
variable [(pullbackFunctor G ψ).Additive]

-- Proof sketch: apply the general composition comparison for total left derived functors from
-- Lemma `21.17.11` to resolve by K-flat complexes with flat terms, then pull those resolutions
-- back successively using Lemma `21.18.1`. This shows that the composite underived pullback
-- already computes the iterated derived pullback, so it admits a total left derived functor.
/-- Lemma 21.18.3: the composite underived pullback-to-derived functor attached to two composable
site-presented morphisms of ringed topoi admits a total left derived functor. This is the
statement-stage core underlying the identity `Lf^* \circ Lg^* = L(g \circ f)^*`. -/
theorem compositeUnderivedPullbackToDerived_hasLeftDerivedFunctor :
    CategoryTheory.Functor.HasRightKanExtension
      (DerivedCategory.Qh :
        HomotopyCategory (RingedSiteModules JC 𝒪C) (up ℤ) ⥤
          DerivedCategory (RingedSiteModules JC 𝒪C))
      (compositeUnderivedPullbackToDerived F G φ ψ)
      := sorry

end
end RingedSite
end SheafOfModules

/-! ### Lemma_21_18_4 (from Chap21) -/
open CategoryTheory
open ComplexShape

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify JC AddCommGrpCat.{u}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasSheafify JD AddCommGrpCat.{u}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The unbounded derived category `D(\mathcal O)` of module sheaves on a ringed site. -/
abbrev RingedSiteDerived (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{u}) :=
  DerivedCategory (RingedSiteModules J 𝒪)

/-- The quasi-isomorphisms in the homotopy category of cochain complexes of `\mathcal O`-modules.
-/
abbrev RingedSiteQis (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{u}) :=
  HomotopyCategory.quasiIso (RingedSiteModules J 𝒪) (up ℤ)

variable (F : C ⥤ D) [Functor.IsContinuous F JC JD]
variable {𝒪' : Sheaf JC CommRingCat.{u}} {𝒪 : Sheaf JD CommRingCat.{u}}
variable (φ : 𝒪' ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪)

/-- The underlying `RingCat`-valued structure map attached to the site-presented morphism of
ringed topoi determined by `φ`. -/
abbrev ringedSiteUnderlyingStructureMap
    (F : C ⥤ D) [Functor.IsContinuous F JC JD]
    (φ : 𝒪' ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪) :
    (sheafCompose JC (forget₂ CommRingCat RingCat)).obj 𝒪' ⟶
      (F.sheafPushforwardContinuous RingCat.{u} JC JD).obj
        ((sheafCompose JD (forget₂ CommRingCat RingCat)).obj 𝒪) :=
  (sheafCompose JC (forget₂ CommRingCat RingCat)).map φ

variable [(SheafOfModules.pushforward (ringedSiteUnderlyingStructureMap F φ)).IsRightAdjoint]

/-- The inverse-image functor on module sheaves attached to the site-presented morphism of ringed
topoi determined by `φ`. -/
abbrev pullbackFunctor
    (F : C ⥤ D) [Functor.IsContinuous F JC JD]
    (φ : 𝒪' ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪) :
    RingedSiteModules JC 𝒪' ⥤ RingedSiteModules JD 𝒪 :=
  SheafOfModules.pullback (ringedSiteUnderlyingStructureMap F φ)

variable [Abelian (RingedSiteModules JC 𝒪')]
variable [CategoryWithHomology (RingedSiteModules JC 𝒪')]
variable [Abelian (RingedSiteModules JD 𝒪)]
variable [CategoryWithHomology (RingedSiteModules JD 𝒪)]
variable [MonoidalCategory (RingedSiteModules JC 𝒪')]
variable [MonoidalPreadditive (RingedSiteModules JC 𝒪')]
variable [MonoidalCategory (RingedSiteModules JD 𝒪)]
variable [MonoidalPreadditive (RingedSiteModules JD 𝒪)]
variable [(pullbackFunctor F φ).Additive]

local instance instPreadditiveTarget : Preadditive (RingedSiteModules JC 𝒪') :=
  (inferInstance : Abelian (RingedSiteModules JC 𝒪')).toPreadditive

local instance instPreadditiveSource : Preadditive (RingedSiteModules JD 𝒪) :=
  (inferInstance : Abelian (RingedSiteModules JD 𝒪)).toPreadditive

/-- The quasi-isomorphisms in the homotopy category of complexes of `\mathcal O'`-modules,
recorded using the local `Preadditive` instance induced from the abelian structure. -/
private abbrev sourceQis :
    MorphismProperty (HomotopyCategory (RingedSiteModules JC 𝒪') (up ℤ)) :=
  HomotopyCategory.quasiIso (RingedSiteModules JC 𝒪') (up ℤ)

/-- The functor on homotopy categories induced by pullback of module sheaves for the
site-presented morphism of ringed topoi determined by `φ`. -/
abbrev pullbackToDerived :
    HomotopyCategory (RingedSiteModules JC 𝒪') (up ℤ) ⥤
      DerivedCategory (RingedSiteModules JD 𝒪) :=
  (pullbackFunctor F φ).mapHomotopyCategory (up ℤ) ⋙
    (show HomotopyCategory (RingedSiteModules JD 𝒪) (up ℤ) ⥤
        DerivedCategory (RingedSiteModules JD 𝒪) from
      (DerivedCategory.Qh :
        HomotopyCategory (RingedSiteModules JD 𝒪) (up ℤ) ⥤
          DerivedCategory (RingedSiteModules JD 𝒪)))

-- Proof sketch: apply the total-left-derived-functor existence criterion to the homotopy-level
-- pullback functor. The intended proof later uses K-flat resolutions with flat terms to show that
-- pullback sends quasi-isomorphisms between suitable resolutions to quasi-isomorphisms.
/-- The homotopy-level pullback functor attached to the site-presented morphism of ringed topoi
determined by `φ` has an everywhere-defined total left derived functor. -/
theorem pullbackToDerived_hasLeftDerivedFunctor :
    Functor.HasLeftDerivedFunctor
      (pullbackToDerived F φ)
      sourceQis := sorry

/-- The homotopy-level pullback functor for the site-presented morphism of ringed topoi determined
by `φ` has its canonical total left derived functor. -/
instance pullbackFunctor_hasLeftDerivedFunctor :
    Functor.HasLeftDerivedFunctor
      (pullbackToDerived F φ)
      sourceQis :=
  pullbackToDerived_hasLeftDerivedFunctor F φ

/-- The derived pullback functor `Lf^* : D(\mathcal O') \to D(\mathcal O)` attached to the
site-presented morphism of ringed topoi determined by `φ`. -/
noncomputable abbrev leftDerivedPullback :
    DerivedCategory (RingedSiteModules JC 𝒪') ⥤
      DerivedCategory (RingedSiteModules JD 𝒪) :=
  Functor.totalLeftDerived
    (pullbackToDerived F φ)
    (show HomotopyCategory (RingedSiteModules JC 𝒪') (up ℤ) ⥤
        DerivedCategory (RingedSiteModules JC 𝒪') from
      (DerivedCategory.Qh :
        HomotopyCategory (RingedSiteModules JC 𝒪') (up ℤ) ⥤
          DerivedCategory (RingedSiteModules JC 𝒪')))
    sourceQis

/-- The derived pullback functor `Lf^*` specialized to the fixed site-presented morphism of ringed
topoi determined by `φ`. -/
noncomputable abbrev leftDerivedPullbackFunctor :=
  leftDerivedPullback F φ

local notation "Lf" => leftDerivedPullbackFunctor F φ

variable
  (derivedTensorTarget :
    DerivedCategory (RingedSiteModules JC 𝒪') ⥤
      DerivedCategory (RingedSiteModules JC 𝒪') ⥤
        DerivedCategory (RingedSiteModules JC 𝒪'))
  (derivedTensorSource :
    DerivedCategory (RingedSiteModules JD 𝒪) ⥤
      DerivedCategory (RingedSiteModules JD 𝒪) ⥤
        DerivedCategory (RingedSiteModules JD 𝒪))

-- Proof sketch: replace both inputs by K-flat complexes with flat terms, compute both derived
-- tensor products by total tensor complexes, and compare the resulting ordinary pullback-tensor
-- constructions using the underived tensor compatibility from Lemma `18.26.2`. The
-- quasi-isomorphism-invariance of derived pullback and derived tensor product then descends this
-- comparison to the derived categories, and functoriality in both variables comes from the
-- naturality of the termwise comparison morphisms.
/-- Lemma 21.18.4: for the site-presented morphism of ringed topoi determined by `φ`, there is a
canonical bifunctorial isomorphism identifying the derived pullback of the derived tensor product
over `\mathcal O'` with the derived tensor product over `\mathcal O` of the two derived
pullbacks. -/
theorem leftDerivedPullback_tensorComparison :
    ∃ η :
      ∀ (ℱ 𝒢 : DerivedCategory (RingedSiteModules JC 𝒪')),
        ((Lf).obj (((derivedTensorTarget).obj 𝒢).obj ℱ)) ≅
          (((derivedTensorSource).obj ((Lf).obj 𝒢)).obj
            ((Lf).obj ℱ)),
      ∀ {ℱ₁ ℱ₂ : DerivedCategory (RingedSiteModules JC 𝒪')}
          {𝒢₁ 𝒢₂ : DerivedCategory (RingedSiteModules JC 𝒪')}
          (fℱ : ℱ₁ ⟶ ℱ₂) (f𝒢 : 𝒢₁ ⟶ 𝒢₂),
        (Lf).map
            ((((derivedTensorTarget).map f𝒢).app ℱ₁) ≫
              (((derivedTensorTarget).obj 𝒢₂).map fℱ)) ≫
          (η ℱ₂ 𝒢₂).hom =
        (η ℱ₁ 𝒢₁).hom ≫
          (((derivedTensorSource).map ((Lf).map f𝒢)).app ((Lf).obj ℱ₁)) ≫
          (((derivedTensorSource).obj ((Lf).obj 𝒢₂)).map ((Lf).map fℱ)) := sorry

end

end SheafOfModules.RingedSite

/-! ### Lemma_21_18_5 (from Chap21) -/
open CategoryTheory

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable (F : D ⥤ C)
variable [Functor.IsContinuous F JD JC]
variable [JC.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify JC CommRingCat.{max u v}]
variable [HasWeakSheafify JC AddCommGrpCat.{max u v}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [JD.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify JD CommRingCat.{max u v}]
variable [HasWeakSheafify JD AddCommGrpCat.{max u v}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [(F.sheafPushforwardContinuous CommRingCat.{max u v} JD JC).IsRightAdjoint]
variable (𝒪 : Sheaf JC CommRingCat.{max u v}) (𝒪' : Sheaf JD CommRingCat.{max u v})
variable [Abelian (ringedSiteModuleCategory JC 𝒪)]
variable [Abelian (ringedSiteModuleCategory JD 𝒪')]
variable
  [Abelian
    (ringedSiteModuleCategory
      JC
      ((F.sheafPullback CommRingCat.{max u v} JD JC).obj 𝒪'))]

local notation "DModC" => DerivedCategory (ringedSiteModuleCategory JC 𝒪)
local notation "DModD" => DerivedCategory (ringedSiteModuleCategory JD 𝒪')
local notation "DModPull" =>
  DerivedCategory
    (ringedSiteModuleCategory
      JC
      ((F.sheafPullback CommRingCat.{max u v} JD JC).obj 𝒪'))

variable
  (derivedTensorSource : DModC ⥤ DModC ⥤ DModC)
  (derivedTensorPulled : DModPull ⥤ DModC ⥤ DModC)
  (leftDerivedPullback : DModD ⥤ DModC)
  (inverseImageDerived : DModD ⥤ DModPull)

-- Proof sketch: at the abelian level, `f^*` is extension of scalars
-- `\mathcal O \otimes_{f^{-1}\mathcal O'} f^{-1}(-)`. Replace the two derived tensor products by
-- K-flat or projective resolutions, identify the underived comparison on the chosen resolutions,
-- and descend the resulting quasi-isomorphism to the derived categories. The canonical
-- bifunctoriality is encoded as a natural isomorphism in the functor category
-- `D(\mathcal O') ⥤ D(\mathcal O) ⥤ D(\mathcal O)`.
/-- Lemma 21.18.5: for a morphism of ringed topoi presented by a continuous functor of sites and a
structure-sheaf map `f^{-1}\mathcal O' \to \mathcal O`, the canonical bifunctorial isomorphism
`\mathcal F^\bullet \otimes_\mathcal O^{\mathbf L} Lf^* \mathcal G^\bullet \cong
\mathcal F^\bullet \otimes_{f^{-1}\mathcal O'}^{\mathbf L} f^{-1}\mathcal G^\bullet`
is expressed canonically as a natural isomorphism of functors
`D(\mathcal O') ⥤ D(\mathcal O) ⥤ D(\mathcal O)`. -/
theorem derivedTensor_leftDerivedPullback_iso :
    leftDerivedPullback ⋙ derivedTensorSource ≅
      inverseImageDerived ⋙ derivedTensorPulled := sorry

end

end SheafOfModules.RingedSite

/-! ### Lemma_21_18_6 (from Chap21) -/
open CategoryTheory
open ComplexShape
open CochainComplex

noncomputable section

universe u

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [LocallySmall.{u} C]
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {𝒪 : Sheaf J CommRingCat.{u}}

/-- A sheaf of commutative rings on a site, regarded as a `RingCat`-valued sheaf. -/
private abbrev ringedSiteRingSheaf
    (𝒪 : Sheaf J CommRingCat.{u}) :
    Sheaf J RingCat.{u} :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪

/-- The category `\mathrm{Mod}(\mathcal O)` of sheaves of `\mathcal O`-modules on the ringed site
`(\mathcal C, \mathcal O)`. -/
private abbrev RingedSiteModules
    (𝒪 : Sheaf J CommRingCat.{u}) :=
  SheafOfModules (ringedSiteRingSheaf 𝒪)

variable [MonoidalCategory (RingedSiteModules 𝒪)]
variable [MonoidalPreadditive (RingedSiteModules 𝒪)]

/-- The point stalk functor on `\mathcal O`-modules preserves zero morphisms. -/
local instance point_stalkFunctor_preservesZeroMorphisms
    (p : GrothendieckTopology.Point.{u} J) :
    (point_sheaf_module_stalk_functor p
      (ringedSiteRingSheaf 𝒪)).PreservesZeroMorphisms := sorry

/-- The `CommRingCat`-valued presheaf fiber of `\mathcal O` at the point `p`. -/
private abbrev pointCommPresheafStalk
    (𝒪 : Sheaf J CommRingCat.{u})
    (p : GrothendieckTopology.Point.{u} J) :
    CommRingCat.{u} :=
  (p.presheafFiber : (Cᵒᵖ ⥤ CommRingCat.{u}) ⥤ CommRingCat.{u}).obj 𝒪.obj

/-- The forgotten `RingCat` stalk of `\mathcal O` agrees with the `CommRingCat` presheaf fiber
at `p`. -/
private abbrev pointStalkRingEquivPointCommPresheafStalk
    (p : GrothendieckTopology.Point.{u} J) :
    ↑(point_stalk_ring p (ringedSiteRingSheaf 𝒪)) ≃+*
      ↑(pointCommPresheafStalk 𝒪 p) :=
  let e :
      ↑(point_stalk_ring p (ringedSiteRingSheaf 𝒪)) ≃+*
        ↑(pointCommPresheafStalk 𝒪 p) :=
    ((p.presheafFiberCompIso (forget₂ CommRingCat RingCat)).app 𝒪.obj).ringCatIsoToRingEquiv
  e

/-- The stalk complex of a complex of `\mathcal O`-modules at a point `p`, viewed as a cochain
complex of modules over the stalk ring `\mathcal O_p`. -/
abbrev pointStalkComplex
    (p : GrothendieckTopology.Point.{u} J)
    (K : CochainComplex (RingedSiteModules 𝒪) ℤ) :
    CochainComplex (ModuleCat (pointCommPresheafStalk 𝒪 p)) ℤ :=
  (((ModuleCat.restrictScalars
      (pointStalkRingEquivPointCommPresheafStalk p).symm.toRingHom).mapHomologicalComplex
      (up ℤ)).obj
    (((point_sheaf_module_stalk_functor p
      (ringedSiteRingSheaf 𝒪)).mapHomologicalComplex
      (up ℤ)).obj K))

/-- The tensor-acyclicity condition of More on Algebra, Definition `15.59.1`, applied to the
stalk complex at the point `p`. -/
def pointStalkKFlatCondition
    (p : GrothendieckTopology.Point.{u} J)
    (K : CochainComplex (RingedSiteModules 𝒪) ℤ) : Prop :=
  CochainComplex.IsKFlat (pointStalkComplex p K)

-- Proof sketch: choose a quasi-isomorphism from a K-flat complex with flat terms using Lemma
-- `21.17.11`, apply stalkwise preservation of K-flatness for pullbacks from Lemma `21.18.1`,
-- and reduce to the acyclic case. For an acyclic K-flat complex, use finite-presentation tests
-- for module-theoretic K-flatness and the exactness of taking stalks.
/-- Lemma 21.18.6 (1): if a cochain complex of `\mathcal O`-modules on a ringed site is K-flat,
then for every point `p` of the site its stalk complex `\mathcal K_p^\bullet` is K-flat as a
cochain complex of `\mathcal O_p`-modules. -/
theorem pointStalkKFlatCondition_of_isKFlat
    (K : CochainComplex (RingedSiteModules 𝒪) ℤ)
    (hK : CochainComplex.IsKFlat K)
    (p : GrothendieckTopology.Point.{u} J) :
    pointStalkKFlatCondition p K := sorry

-- Proof sketch: for an acyclic test complex `F^\bullet` of `\mathcal O`-modules, exactness of
-- the total tensor product with `K^\bullet` can be checked on stalks when the site has enough
-- points. Stalk formation commutes with tensor products and direct sums, so the stalkwise
-- K-flatness assumptions identify every stalk tensor complex with an acyclic module-theoretic
-- tensor product.
/-- Lemma 21.18.6 (2): if the site has enough points and every stalk complex
`\mathcal K_p^\bullet` is K-flat over `\mathcal O_p`, then `\mathcal K^\bullet` is K-flat on the
ringed site. -/
theorem isKFlat_of_pointStalkKFlatCondition_of_hasEnoughPoints
    [GrothendieckTopology.HasEnoughPoints.{u} J]
    (K : CochainComplex (RingedSiteModules 𝒪) ℤ)
    (hK : ∀ p : GrothendieckTopology.Point.{u} J, pointStalkKFlatCondition p K) :
    CochainComplex.IsKFlat K := sorry

end SheafOfModules.RingedSite

/-! ### Lemma_21_18_7 (from Chap21) -/
open CategoryTheory
open ComplexShape

noncomputable section

universe u

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C] {C' : Type u} [Category.{u} C']
variable {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J'.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasSheafify J' AddCommGrpCat.{u}]
variable [J'.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {𝒪 : Sheaf J CommRingCat.{u}} {𝒪' : Sheaf J' CommRingCat.{u}}
variable [MonoidalCategory (SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪))]
variable [MonoidalPreadditive
  (SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪))]
variable [MonoidalCategory (SheafOfModules ((sheafCompose J' (forget₂ CommRingCat RingCat)).obj 𝒪'))]
variable [MonoidalPreadditive
  (SheafOfModules ((sheafCompose J' (forget₂ CommRingCat RingCat)).obj 𝒪'))]

/-- A cochain complex of `\mathcal O`-modules on a ringed site is K-flat when tensoring it with
any acyclic cochain complex preserves acyclicity. -/
def IsKFlat
    (K : CochainComplex
      (SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)) ℤ) : Prop :=
  ∀ ⦃F : CochainComplex
      (SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)) ℤ⦄
      [_h : HomologicalComplex.HasTensor F K], F.Acyclic →
    (HomologicalComplex.tensorObj F K).Acyclic

-- Proof sketch: this is the defining condition for K-flatness on the ringed site written out
-- explicitly in terms of preservation of acyclic complexes under total tensor product.
/-- Unfolding `IsKFlat` says exactly that total tensoring with the fixed complex preserves acyclic
cochain complexes of `\mathcal O`-modules. -/
theorem isKFlat_iff
    (K : CochainComplex
      (SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)) ℤ) :
    IsKFlat K ↔
      ∀ ⦃F : CochainComplex
          (SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)) ℤ⦄
          [_h : HomologicalComplex.HasTensor F K], F.Acyclic →
        (HomologicalComplex.tensorObj F K).Acyclic := sorry

variable (F : C' ⥤ C) [Functor.IsContinuous F J' J]
variable (φ : 𝒪' ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J' J).obj 𝒪)

/-- The `RingCat`-valued structure map attached to the site-presented morphism of ringed topoi
determined by `φ`. -/
abbrev ringedSiteUnderlyingStructureMap :
    (sheafCompose J' (forget₂ CommRingCat RingCat)).obj 𝒪' ⟶
      (F.sheafPushforwardContinuous RingCat.{u} J' J).obj
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪) :=
  (sheafCompose J' (forget₂ CommRingCat RingCat)).map φ

variable [(SheafOfModules.pushforward (ringedSiteUnderlyingStructureMap F φ)).IsRightAdjoint]
variable [(SheafOfModules.pullback (ringedSiteUnderlyingStructureMap F φ)).PreservesZeroMorphisms]

-- Proof sketch: use Lemma `21.18.6` to reduce K-flatness on the source ringed site to K-flatness
-- of all stalk complexes, which is valid because `(\mathcal C, J)` has enough points. For a
-- source point, identify the stalk of the pulled-back complex with extension of scalars of the
-- corresponding target stalk via Lemma `18.36.4`, and then apply the module-theoretic extension
-- of scalars preservation of K-flatness from Lemma `15.59.3` to the stalkwise K-flatness coming
-- from the target complex.
/-- Lemma 21.18.7: if the source site of a site-presented morphism of ringed topoi has enough
points, then the pullback of a K-flat complex of `\mathcal O'`-modules is a K-flat complex of
`\mathcal O`-modules. -/
theorem pullback_isKFlat_of_isKFlat_of_hasEnoughPoints
    [GrothendieckTopology.HasEnoughPoints.{u} J]
    (K : CochainComplex
      (SheafOfModules ((sheafCompose J' (forget₂ CommRingCat RingCat)).obj 𝒪')) ℤ)
    (hK : IsKFlat K) :
    IsKFlat
      (((SheafOfModules.pullback
          (ringedSiteUnderlyingStructureMap F φ)).mapHomologicalComplex
            (up ℤ)).obj K) := sorry

end

end SheafOfModules.RingedSite

/-! ### Lemma_21_18_8 (from Chap21) -/
open CategoryTheory
open ComplexShape

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify JC AddCommGrpCat.{u}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasSheafify JD AddCommGrpCat.{u}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The category `\mathrm{Mod}(\mathcal O)` of sheaves of modules on a ringed site with
structure sheaf `\mathcal O`. -/
abbrev RingedSiteModules (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{u}) :=
  SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)

/-- The unbounded derived category `D(\mathcal O)` of sheaves of `\mathcal O`-modules. -/
abbrev RingedSiteDerived (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{u}) :=
  DerivedCategory (RingedSiteModules J 𝒪)

/-- The underlying `RingCat`-valued structure map attached to the site-presented morphism of
ringed topoi determined by `φ`. -/
abbrev ringedSiteUnderlyingStructureMap
    (F : C ⥤ D) [Functor.IsContinuous F JC JD]
    {𝒪' : Sheaf JC CommRingCat.{u}} {𝒪 : Sheaf JD CommRingCat.{u}}
    (φ : 𝒪' ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪) :
    (sheafCompose JC (forget₂ CommRingCat RingCat)).obj 𝒪' ⟶
      (F.sheafPushforwardContinuous RingCat.{u} JC JD).obj
        ((sheafCompose JD (forget₂ CommRingCat RingCat)).obj 𝒪) :=
  (sheafCompose JC (forget₂ CommRingCat RingCat)).map φ

/-- The inverse-image functor on module sheaves attached to the site-presented morphism of ringed
topoi determined by `φ`. -/
abbrev pullbackFunctor
    (F : C ⥤ D) [Functor.IsContinuous F JC JD]
    {𝒪' : Sheaf JC CommRingCat.{u}} {𝒪 : Sheaf JD CommRingCat.{u}}
    (φ : 𝒪' ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪) :
    RingedSiteModules JC 𝒪' ⥤ RingedSiteModules JD 𝒪 :=
  SheafOfModules.pullback (ringedSiteUnderlyingStructureMap F φ)

variable (F : C ⥤ D) [Functor.IsContinuous F JC JD]
variable {𝒪' : Sheaf JC CommRingCat.{u}} {𝒪 : Sheaf JD CommRingCat.{u}}
variable (φ : 𝒪' ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪)
variable [Abelian (RingedSiteModules JC 𝒪')]
variable [Abelian (RingedSiteModules JD 𝒪)]

local notation "TargetModules" => RingedSiteModules JC 𝒪'
local notation "SourceModules" => RingedSiteModules JD 𝒪
local notation "TargetDerived" => RingedSiteDerived JC 𝒪'
local notation "SourceDerived" => RingedSiteDerived JD 𝒪

/-- Pullback of a cochain complex along the underlying pullback functor on module sheaves. -/
private abbrev pulledBackComplex
    (K : CochainComplex TargetModules ℤ) :
    CochainComplex SourceModules ℤ :=
  ((pullbackFunctor F φ).mapHomologicalComplex (up ℤ)).obj K

variable
  (targetTensorComplex :
    CochainComplex TargetModules ℤ →
      CochainComplex TargetModules ℤ →
        CochainComplex TargetModules ℤ)
  (sourceTensorComplex :
    CochainComplex SourceModules ℤ →
      CochainComplex SourceModules ℤ →
        CochainComplex SourceModules ℤ)
  (targetComplexToDerived : CochainComplex TargetModules ℤ → TargetDerived)
  (sourceComplexToDerived : CochainComplex SourceModules ℤ → SourceDerived)
  (leftDerivedPullback : TargetDerived ⥤ SourceDerived)
  (derivedTensorTarget :
    TargetDerived ⥤ TargetDerived ⥤ TargetDerived)
  (derivedTensorSource :
    SourceDerived ⥤ SourceDerived ⥤ SourceDerived)

-- Proof sketch: choose K-flat resolutions with flat terms for `K` and `M` as in Lemma `21.17.11`.
-- The top horizontal and bottom horizontal arrows are the counits computing the two derived tensor
-- products on those resolutions, the right vertical arrow is the counit computing derived
-- pullback on `Tot(K ⊗ M)`, the left vertical arrow is the comparison from Lemma `21.18.4`, and
-- the remaining comparison is the ordinary pullback-tensor compatibility on the chosen total
-- tensor complexes. The resolution-level square then commutes by functoriality, and the equality
-- descends to the derived categories.
/-- Lemma 21.18.8: for a site-presented morphism of ringed topoi, the canonical comparison
ladder from `Lf^*(K^\bullet \otimes_{\mathcal O_\mathcal D}^{\mathbf L} M^\bullet)` to
`\mathrm{Tot}(f^*K^\bullet \otimes_{\mathcal O_\mathcal C} f^*M^\bullet)` obtained from derived
tensor counits, the derived pullback counit, the pullback-tensor comparison, and the comparison
of Lemma `21.18.4` is commutative. -/
theorem leftDerivedPullback_tensor_counit_ladder_commutes
    (derivedPullbackTensorComparison :
      ∀ (K M : CochainComplex TargetModules ℤ),
        leftDerivedPullback.obj
            ((derivedTensorTarget.obj (targetComplexToDerived M)).obj
              (targetComplexToDerived K)) ⟶
          ((derivedTensorSource.obj
              (leftDerivedPullback.obj (targetComplexToDerived M))).obj
            (leftDerivedPullback.obj (targetComplexToDerived K))))
    (targetTensorCounit :
      ∀ (K M : CochainComplex TargetModules ℤ),
        ((derivedTensorTarget.obj (targetComplexToDerived M)).obj
          (targetComplexToDerived K)) ⟶
          targetComplexToDerived (targetTensorComplex K M))
    (pullbackCounit :
      ∀ (K : CochainComplex TargetModules ℤ),
        leftDerivedPullback.obj (targetComplexToDerived K) ⟶
          sourceComplexToDerived (pulledBackComplex F φ K))
    (sourceTensorCounit :
      ∀ (K M : CochainComplex SourceModules ℤ),
        ((derivedTensorSource.obj (sourceComplexToDerived M)).obj
          (sourceComplexToDerived K)) ⟶
          sourceComplexToDerived (sourceTensorComplex K M))
    (underivedPullbackTensorComparison :
      ∀ (K M : CochainComplex TargetModules ℤ),
        sourceComplexToDerived
            (pulledBackComplex F φ (targetTensorComplex K M)) ⟶
          sourceComplexToDerived
            (sourceTensorComplex (pulledBackComplex F φ K)
              (pulledBackComplex F φ M)))
    (K M : CochainComplex TargetModules ℤ) :
    leftDerivedPullback.map (targetTensorCounit K M) ≫
        pullbackCounit (targetTensorComplex K M) ≫
        underivedPullbackTensorComparison K M =
      derivedPullbackTensorComparison K M ≫
        ((derivedTensorSource.map (pullbackCounit M)).app
          (leftDerivedPullback.obj (targetComplexToDerived K))) ≫
        ((derivedTensorSource.obj
          (sourceComplexToDerived (pulledBackComplex F φ M))).map
            (pullbackCounit K)) ≫
        sourceTensorCounit (pulledBackComplex F φ K) (pulledBackComplex F φ M) := sorry

end

end SheafOfModules.RingedSite
