import Mathlib
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_18_33_11 (from Chap18) -/
open CategoryTheory
open SheafOfModules.RingedSite
open scoped RingedSite.Hom RelativeDerivation

noncomputable section

universe u

namespace RingedSite.Hom

section

variable {CX : Type u} [Category.{u} CX] {CX' : Type u} [Category.{u} CX']
variable {CY : Type u} [Category.{u} CY] {CY' : Type u} [Category.{u} CY']
variable {JX : GrothendieckTopology CX} {JX' : GrothendieckTopology CX'}
variable {JY : GrothendieckTopology CY} {JY' : GrothendieckTopology CY'}
variable [JX.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JX'.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JY.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JY'.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify JX CommRingCat.{u}]
variable [HasWeakSheafify JX AddCommGrpCat.{u}]
variable [JX.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify JX' CommRingCat.{u}]
variable [HasWeakSheafify JX' AddCommGrpCat.{u}]
variable [JX'.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify JY CommRingCat.{u}]
variable [HasWeakSheafify JY AddCommGrpCat.{u}]
variable [JY.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify JY' CommRingCat.{u}]
variable [HasWeakSheafify JY' AddCommGrpCat.{u}]
variable [JY'.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {𝒪X : Sheaf JX CommRingCat.{u}} {𝒪X' : Sheaf JX' CommRingCat.{u}}
variable {𝒪Y : Sheaf JY CommRingCat.{u}} {𝒪Y' : Sheaf JY' CommRingCat.{u}}

variable
  (f :
    RingedSite.ofCommRingSheaf JX' 𝒪X' ⟶ RingedSite.ofCommRingSheaf JX 𝒪X)
  (g :
    RingedSite.ofCommRingSheaf JY' 𝒪Y' ⟶ RingedSite.ofCommRingSheaf JY 𝒪Y)
  (h :
    RingedSite.ofCommRingSheaf JX 𝒪X ⟶ RingedSite.ofCommRingSheaf JY 𝒪Y)
  (h' :
    RingedSite.ofCommRingSheaf JX' 𝒪X' ⟶ RingedSite.ofCommRingSheaf JY' 𝒪Y')

local instance hom_base_isContinuous {A B : RingedSite.{u, u}} (φ : A ⟶ B) :
    Functor.IsContinuous φ.base B.siteTopology A.siteTopology :=
  φ.isMorphismOfSites.toIsContinuous

local instance f_base_isContinuous :
    Functor.IsContinuous f.base
      (RingedSite.ofCommRingSheaf JX 𝒪X).siteTopology
      (RingedSite.ofCommRingSheaf JX' 𝒪X').siteTopology :=
  f.isMorphismOfSites.toIsContinuous

variable
  [Functor.IsRightAdjoint (SheafOfModules.pushforward f.structureSheafMap)]

/- Domain-style sampling for Lemma 18.33.11:
- primary domain: base change for relative differentials in a commutative square of morphisms of
  ringed topoi presented by sites;
- sampled owner declarations:
  `RingedSite.Hom.inverseImageStructureSheafMap`,
  `RingedSite.Hom.(^*)`,
  `RingedSite.Hom.Ω[_]`,
  `RingedSite.Hom.d[_]`;
- best owner abstraction: the bundled square of morphisms
  `f : X' ⟶ X`, `g : Y' ⟶ Y`, `h : X ⟶ Y`, `h' : X' ⟶ Y'` with
  `hcomm : f ≫ h = h' ≫ g`;
- primitive data: the four bundled morphisms and the commutativity witness `hcomm`;
- derived API: the canonical comparison map `c_f : f^* Ω[h] ⟶ Ω[h']` and its characterization on
  universal differentials of local sections.

Source/core/bridge triage:
- `source-facing`: the base-change morphism `c_f : f^* Ω[h] ⟶ Ω[h']`;
- `core/canonical`: the owner surface `Ω[h]`, `d[h]`, and the pullback-pushforward adjunction for
  `f.structureSheafMap`;
- `bridge/view`: the adjoint map `Ω[h] ⟶ f_* Ω[h']`, whose component on a section `t` sends
  `d[h](t)` to `d[h'](f^♯ t)`.

This file should therefore stay on the bundled `RingedSite.Hom` surface. The generic auxiliary
derivation formerly exposed as primitive data is removed from the public API.
-/

/-- The source-facing characterization property for the base-change map on relative differentials:
after adjunction, it sends the universal differential of a local section `t` of `𝒪_X` to the
universal differential of its pullback along `f^\sharp`. -/
private def pullbackDifferentialsComparisonProperty
    (f :
      RingedSite.ofCommRingSheaf JX' 𝒪X' ⟶ RingedSite.ofCommRingSheaf JX 𝒪X)
    (h :
      RingedSite.ofCommRingSheaf JX 𝒪X ⟶ RingedSite.ofCommRingSheaf JY 𝒪Y)
    (h' :
      RingedSite.ofCommRingSheaf JX' 𝒪X' ⟶ RingedSite.ofCommRingSheaf JY' 𝒪Y')
    [Functor.IsRightAdjoint (SheafOfModules.pushforward f.structureSheafMap)]
    (τ :
      (RingedSite.Hom.modulePullback f).obj (RingedSite.Hom.differentials h) ⟶
        RingedSite.Hom.differentials h') : Prop :=
  ∀ {U : CXᵒᵖ} (t : 𝒪X.obj.obj U),
    let fop := f.base.op
    let fSharp := f.structureSheafMap.hom
    let U' := fop.obj U
    let fSharpU := fSharp.app U
    ((((SheafOfModules.pullbackPushforwardAdjunction f.structureSheafMap).homEquiv _ _) τ).val.app
          U)
        (((d[h]).app U).d t) =
      ((d[h']).app U').d (fSharpU t)

-- Proof sketch: the square hypothesis `hcomm : f ≫ h = h' ≫ g` identifies the composite
-- `f^\sharp ≫ f_* d[h']` as a `Y`-derivation on `𝒪_X`. Apply the universal property of
-- `Ω[h]`, then transpose the resulting map `Ω[h] ⟶ f_* Ω[h']` across
-- `f^* ⊣ f_*`. Uniqueness follows because the sections `d[h](t)` generate `Ω[h]`.
/-- Lemma 18.33.11: for a commutative square of morphisms of ringed topoi presented by sites,
there exists a unique base-change morphism
`c_f : f^* Ω[h] ⟶ Ω[h']`
whose adjoint sends `d[h](t)` to `d[h'](f^\sharp t)` on every local section `t` of `𝒪_X`. -/
theorem existsUnique_pullbackDifferentialsComparison
    (hcomm : f ≫ h = h' ≫ g) :
    ∃! τ :
        (RingedSite.Hom.modulePullback f).obj (RingedSite.Hom.differentials h) ⟶
          RingedSite.Hom.differentials h',
      pullbackDifferentialsComparisonProperty f h h' τ := by
  sorry

/-- The canonical base-change morphism on relative differentials attached to a commutative square
of morphisms of ringed topoi. -/
noncomputable def pullbackDifferentialsComparison
    (hcomm : f ≫ h = h' ≫ g) :
    (RingedSite.Hom.modulePullback f).obj (RingedSite.Hom.differentials h) ⟶
      RingedSite.Hom.differentials h' :=
  Classical.choose
    (ExistsUnique.exists
      (existsUnique_pullbackDifferentialsComparison f g h h' hcomm))

-- Proof sketch: this is the defining property extracted from
-- `existsUnique_pullbackDifferentialsComparison`.
/-- The canonical comparison morphism is characterized by sending `d[h](t)` to
`d[h'](f^\sharp t)` after passage to the adjoint map `Ω[h] ⟶ f_* Ω[h']`. -/
theorem pullbackDifferentialsComparison_characterizing
    (hcomm : f ≫ h = h' ≫ g) :
    pullbackDifferentialsComparisonProperty f h h'
      (pullbackDifferentialsComparison f g h h' hcomm) := by
  sorry

-- Proof sketch: uniqueness in `existsUnique_pullbackDifferentialsComparison` identifies any
-- comparison map satisfying the same sectionwise differential formula with the chosen one.
/-- A morphism `f^* Ω[h] ⟶ Ω[h']` is the canonical base-change map once it carries the universal
differentials `d[h](t)` to `d[h'](f^\sharp t)` on local sections after adjunction. -/
theorem pullbackDifferentialsComparison_unique
    (hcomm : f ≫ h = h' ≫ g)
    (τ :
      (RingedSite.Hom.modulePullback f).obj (RingedSite.Hom.differentials h) ⟶
        RingedSite.Hom.differentials h')
    (hτ : pullbackDifferentialsComparisonProperty f h h' τ) :
    τ = pullbackDifferentialsComparison f g h h' hcomm := by
  sorry

end

end RingedSite.Hom
