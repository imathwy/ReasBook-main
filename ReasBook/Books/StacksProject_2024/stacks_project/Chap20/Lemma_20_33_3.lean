import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Triangulated.Yoneda
import StacksProject_2024.Chap13.Definition_13_27_1
import StacksProject_2024.Chap20.Lemma_20_31_8
import StacksProject_2024.Chap20.Lemma_20_33_1
import StacksProject_2024.Chap20.Open_subspace_module_core

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.ComposableArrows
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open TopologicalSpace
open scoped DerivedExt
open scoped Pretriangulated.Opposite

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}

local notation "DModX" => ModuleDerived X
local notation "DRes[" U "]" => moduleRestrictionToOpenDerived X U
local notation "DRes≤[" h "]" => derivedRestrictionBetweenOpens X h
local notation "DExt[" U "]" => moduleExtensionByZeroFromOpenDerived X U
local notation "DLowerShriek[" U "]" => DRes[U] ⋙ DExt[U]
local notation "DExtAdj[" U "]" => Adjunction.ofIsLeftAdjoint (DExt[U])

/- Domain-style sampling for Lemma 20.33.3:
- primary domain: the exact segment on represented Hom groups obtained from the two-open
  Mayer-Vietoris distinguished triangle in `D(𝒪_X)`;
- sampled owner declarations:
  `moduleDerived_mayerVietoris_distinguishedTriangle`,
  `moduleRestrictionToOpenDerived`,
  `derivedRestrictionBetweenOpens`,
  `moduleRestrictionToOpenDerivedCompIso`,
  `Functor.homologySequenceComposableArrows₅_exact`,
  `triangleOpEquivalence`;
- best owner abstraction:
  `source-facing`: the exact Mayer-Vietoris Hom segment whose middle maps are the source-facing
    restriction and overlap-difference maps, written directly in the theorem statement below;
  `core/canonical`: the Chapter 20 restriction owners
    `moduleRestrictionToOpenDerived`, `derivedRestrictionBetweenOpens`,
    `moduleRestrictionToOpenDerivedCompIso`, together with the canonical represented-Hom exactness
    owner `Functor.homologySequenceComposableArrows₅_exact`;
  `bridge/view`: the theorem-local distinguished-triangle and edge-formula hypotheses identifying
    the displayed source-facing sequence with the canonical represented-Hom exact segment of a
    Mayer-Vietoris distinguished triangle.

Primitive data vs derived API:
- primitive data: the opens `U, V`, the derived objects `E, F`, the Mayer-Vietoris triangle
  maps `α`, `β`, `δ`, and the source-facing boundary morphism `δHom`;
- derived API: the theorem-level displayed restriction and overlap-difference maps for the
  source-facing segment, together with the theorem-level exactness witness induced from the
  canonical represented-Hom exact segment of a distinguished triangle.
 -/

/-- Companion bridge: any lower-shriek Mayer-Vietoris distinguished triangle with the source
restriction and counit formulas induces a source-facing boundary map whose Mayer-Vietoris Hom
segment is exact. -/
private theorem exists_moduleDerivedMayerVietorisHomSequence_exact
    (U V : Opens X.carrier)
    [(Opens.grothendieckTopology (TopCat.of U)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})]
    [(Opens.grothendieckTopology (TopCat.of V)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})]
    [(Opens.grothendieckTopology (TopCat.of ((U ⊓ V : Opens X.carrier)))).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})]
    (E F : DModX)
    (α :
      ((DLowerShriek[U ⊓ V]).obj E) ⟶
        ((DLowerShriek[U]).obj E ⊞ (DLowerShriek[V]).obj E))
    (β : ((DLowerShriek[U]).obj E ⊞ (DLowerShriek[V]).obj E) ⟶ E)
    (δ : E ⟶ ((DLowerShriek[U ⊓ V]).obj E)⟦(1 : ℤ)⟧)
    (hαU :
      let ηU :
          (DRes[U ⊓ V]).obj E ⟶ (DExt[U ⊓ V].rightAdjoint).obj ((DLowerShriek[U]).obj E) := by
        let η' : (DRes[U ⊓ V]).obj E ⟶ (DRes[U ⊓ V]).obj ((DLowerShriek[U]).obj E) := by
          let ηU : (DRes[U]).obj E ⟶ (DRes[U]).obj ((DLowerShriek[U]).obj E) := by
            simpa [moduleExtensionByZeroFromOpenDerived_rightAdjoint_eq] using
              (DExtAdj[U]).unit.app ((DRes[U]).obj E)
          let e₁ := (moduleRestrictionToOpenDerivedCompIso X (inf_le_left : U ⊓ V ≤ U)).app E
          let e₂ :=
            (moduleRestrictionToOpenDerivedCompIso X (inf_le_left : U ⊓ V ≤ U)).app
              ((DLowerShriek[U]).obj E)
          exact e₁.inv ≫ (DRes≤[(inf_le_left : U ⊓ V ≤ U)]).map ηU ≫ e₂.hom
        simpa [moduleExtensionByZeroFromOpenDerived_rightAdjoint_eq] using η'
      (DExtAdj[U ⊓ V]).homEquiv ((DRes[U ⊓ V]).obj E) ((DLowerShriek[U]).obj E)
          (α ≫ biprod.fst) = ηU)
    (hαV :
      let ηV :
          (DRes[U ⊓ V]).obj E ⟶ (DExt[U ⊓ V].rightAdjoint).obj ((DLowerShriek[V]).obj E) := by
        let η' : (DRes[U ⊓ V]).obj E ⟶ (DRes[U ⊓ V]).obj ((DLowerShriek[V]).obj E) := by
          let ηV : (DRes[V]).obj E ⟶ (DRes[V]).obj ((DLowerShriek[V]).obj E) := by
            simpa [moduleExtensionByZeroFromOpenDerived_rightAdjoint_eq] using
              (DExtAdj[V]).unit.app ((DRes[V]).obj E)
          let e₁ := (moduleRestrictionToOpenDerivedCompIso X (inf_le_right : U ⊓ V ≤ V)).app E
          let e₂ :=
            (moduleRestrictionToOpenDerivedCompIso X (inf_le_right : U ⊓ V ≤ V)).app
              ((DLowerShriek[V]).obj E)
          exact e₁.inv ≫ (DRes≤[(inf_le_right : U ⊓ V ≤ V)]).map ηV ≫ e₂.hom
        simpa [moduleExtensionByZeroFromOpenDerived_rightAdjoint_eq] using η'
      (DExtAdj[U ⊓ V]).homEquiv ((DRes[U ⊓ V]).obj E) ((DLowerShriek[V]).obj E)
          (α ≫ biprod.snd) = ηV)
    (hβU :
      let εU : (DLowerShriek[U]).obj E ⟶ E := by
        simpa [moduleExtensionByZeroFromOpenDerived_rightAdjoint_eq] using
          (DExtAdj[U]).counit.app E
      biprod.inl ≫ β = εU)
    (hβV :
      let εV : (DLowerShriek[V]).obj E ⟶ E := by
        simpa [moduleExtensionByZeroFromOpenDerived_rightAdjoint_eq] using
          (DExtAdj[V]).counit.app E
      (- (biprod.inr ≫ β)) = εV)
    (hdist : Triangle.mk α β δ ∈ distTriang DModX) :
    ∃ δHom :
        AddCommGrpCat.of (Ext^(-1)(((DRes[U ⊓ V]).obj E), ((DRes[U ⊓ V]).obj F))) ⟶
          AddCommGrpCat.of (E ⟶ F),
      (mk₃ δHom
          (biprod.lift
            (AddCommGrpCat.ofHom ((DRes[U]).mapAddHom : (E ⟶ F) →+ _))
            (AddCommGrpCat.ofHom ((DRes[V]).mapAddHom : (E ⟶ F) →+ _)))
          (biprod.desc
            (AddCommGrpCat.ofHom <|
              (leftComp _
                  (((moduleRestrictionToOpenDerivedCompIso X
                    (inf_le_left : U ⊓ V ≤ U)).app E).inv)).comp <|
                (rightComp _
                    (((moduleRestrictionToOpenDerivedCompIso X
                      (inf_le_left : U ⊓ V ≤ U)).app F).hom)).comp <|
                  (DRes≤[(inf_le_left : U ⊓ V ≤ U)]).mapAddHom)
            (-(AddCommGrpCat.ofHom <|
              (leftComp _
                  (((moduleRestrictionToOpenDerivedCompIso X
                    (inf_le_right : U ⊓ V ≤ V)).app E).inv)).comp <|
                (rightComp _
                    (((moduleRestrictionToOpenDerivedCompIso X
                      (inf_le_right : U ⊓ V ≤ V)).app F).hom)).comp <|
                  (DRes≤[(inf_le_right : U ⊓ V ≤ V)]).mapAddHom)))).Exact := by
  sorry

-- Proof sketch: choose the lower-shriek Mayer-Vietoris triangle from
-- `moduleDerived_mayerVietoris_distinguishedTriangle`, build the explicit comparison isomorphism
-- above from the adjunction identifications of lower-shriek morphisms with restricted morphisms,
-- and transport exactness from the canonical represented-Hom segment of the distinguished triangle.
/-- Lemma 20.33.3: if a ringed space `X` is covered by two opens `U` and `V`, then for every
`E, F ∈ D(𝒪_X)` there exists a connecting morphism `δHom` such that the source-facing
Mayer-Vietoris Hom segment
`Ext⁻¹(E|_{U ∩ V}, F|_{U ∩ V}) ⟶ Hom(E, F) ⟶
 Hom(E|_U, F|_U) ⊞ Hom(E|_V, F|_V) ⟶ Hom(E|_{U ∩ V}, F|_{U ∩ V})`
with the canonical restriction and overlap-difference maps is exact. -/
@[stacks 08BW]
theorem module_derived_mayer_vietoris_hom_exact_segment
    (U V : Opens X.carrier)
    [(Opens.grothendieckTopology (TopCat.of U)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})]
    [(Opens.grothendieckTopology (TopCat.of V)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})]
    [(Opens.grothendieckTopology (TopCat.of ((U ⊓ V : Opens X.carrier)))).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})]
    (hUV : U ⊔ V = ⊤) (E F : DModX) :
    ∃ δHom :
        AddCommGrpCat.of (Ext^(-1)(((DRes[U ⊓ V]).obj E), ((DRes[U ⊓ V]).obj F))) ⟶
          AddCommGrpCat.of (E ⟶ F),
      (mk₃ δHom
          (biprod.lift
            (AddCommGrpCat.ofHom ((DRes[U]).mapAddHom : (E ⟶ F) →+ _))
            (AddCommGrpCat.ofHom ((DRes[V]).mapAddHom : (E ⟶ F) →+ _)))
          (biprod.desc
            (AddCommGrpCat.ofHom <|
              (leftComp _
                  (((moduleRestrictionToOpenDerivedCompIso X
                    (inf_le_left : U ⊓ V ≤ U)).app E).inv)).comp <|
                (rightComp _
                    (((moduleRestrictionToOpenDerivedCompIso X
                      (inf_le_left : U ⊓ V ≤ U)).app F).hom)).comp <|
                  (DRes≤[(inf_le_left : U ⊓ V ≤ U)]).mapAddHom)
            (-(AddCommGrpCat.ofHom <|
              (leftComp _
                  (((moduleRestrictionToOpenDerivedCompIso X
                    (inf_le_right : U ⊓ V ≤ V)).app E).inv)).comp <|
                (rightComp _
                  (((moduleRestrictionToOpenDerivedCompIso X
                      (inf_le_right : U ⊓ V ≤ V)).app F).hom)).comp <|
                  (DRes≤[(inf_le_right : U ⊓ V ≤ V)]).mapAddHom)))).Exact := by
  obtain ⟨α, β, δ, hαU, hαV, hβU, hβV, hdist⟩ :=
    moduleDerived_mayerVietoris_distinguishedTriangle U V hUV E
  obtain ⟨δHom, hExact⟩ :=
    exists_moduleDerivedMayerVietorisHomSequence_exact
      U V E F α β δ hαU hαV hβU hβV hdist
  exact ⟨δHom, hExact⟩

end

end AlgebraicGeometry.RingedSpace
