import Mathlib
import stacks_project.Chap08.Definition_8_3_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe w₁ w₂ v₁ v₂ u₁ u₂

open CategoryTheory
open SemiRepresentableFamily.Over

namespace CategoryTheory

/- Domain-style sampling for Lemma 8.3.3:
- primary domain: categorical descent data for fixed-target families in a fibred category.
- inspected owner-level declarations:
  `SemiRepresentableFamily.map`,
  `DescentDatum` from 8.3.1,
  `Pseudofunctor.DescentData.pullFunctor`,
  `Pseudofunctor.DescentData.pullFunctorIso`,
  `Pseudofunctor.DescentData'.descentDataEquivalence`.
- best owner abstraction: the fixed-target family owner `SemiRepresentableFamily.Over U`, together
  with the chapter owner `DescentDatum p hc 𝒰`.
- primitive data: a fixed-target family `𝒰`, a second family `𝒱`, and a morphism of families over
  a base map.
- derived API: the equivalence from chosen-overlap descent data to canonical descent data, the
  induced pullback functor, and the canonical isomorphism between pullback functors over the same
  base map.

Source/core/bridge triage:
- `source-facing`: morphisms of fixed-target families over a base map.
- `core/canonical`: `DescentDatum p hc 𝒰` and `Pseudofunctor.DescentData.pullFunctor`.
- `bridge/view`: the equivalence
  `Pseudofunctor.DescentData'.descentDataEquivalence` specialized to the owner-level chosen
  overlaps of `𝒰`.
-/

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

private noncomputable abbrev familyDescentDataEquivalence
    {p : S ⥤ C} [p.IsFibered] (hc : PullbackChoice p)
    {U : C} (𝒰 : SemiRepresentableFamily.Over U) [HasDescentPullbacks 𝒰] :
    DescentDatum p hc 𝒰 ≌
      (hc.fiberPseudofunctor).DescentData (fun i : 𝒰.index ↦ (𝒰.obj i).hom) :=
  Pseudofunctor.DescentData'.descentDataEquivalence
    hc.fiberPseudofunctor
    𝒰.pairwisePullback
    𝒰.triplePullback

section PullbackOfDescentData

variable {p : S ⥤ C} [p.IsFibered] (hc : PullbackChoice p)
variable {U V : C}
variable {𝒰 : SemiRepresentableFamily.Over U} {𝒱 : SemiRepresentableFamily.Over V}
variable [HasDescentPullbacks 𝒰] [HasDescentPullbacks 𝒱]

omit [HasDescentPullbacks 𝒰] [HasDescentPullbacks 𝒱] in
private theorem familyMorphism_w
    (base : U ⟶ V)
    (φ : ((SemiRepresentableFamily.map (Over.map base)).obj 𝒰 ⟶ 𝒱))
    (i : 𝒰.index) :
    (φ.f i).left ≫ (𝒱.obj (φ.α i)).hom = (𝒰.obj i).hom ≫ base := by
  simpa using Over.w (φ.f i)

omit [HasDescentPullbacks 𝒰] [HasDescentPullbacks 𝒱] in
private noncomputable abbrev familyPullFunctor
    (base : U ⟶ V)
    (φ : ((SemiRepresentableFamily.map (Over.map base)).obj 𝒰 ⟶ 𝒱)) :
    (hc.fiberPseudofunctor).DescentData (fun i : 𝒱.index ↦ (𝒱.obj i).hom) ⥤
      (hc.fiberPseudofunctor).DescentData (fun i : 𝒰.index ↦ (𝒰.obj i).hom) :=
  Pseudofunctor.DescentData.pullFunctor hc.fiberPseudofunctor (familyMorphism_w base φ)

omit [HasDescentPullbacks 𝒰] [HasDescentPullbacks 𝒱] in
private noncomputable def familyPullFunctorIso
    (base : U ⟶ V)
    (φ φ' : ((SemiRepresentableFamily.map (Over.map base)).obj 𝒰 ⟶ 𝒱)) :
    familyPullFunctor hc base φ ≅ familyPullFunctor hc base φ' :=
  let wφ : ∀ i : 𝒰.index,
      (φ.f i).left ≫ (fun j : 𝒱.index ↦ (𝒱.obj j).hom) (φ.α i) = (𝒰.obj i).hom ≫ base :=
    familyMorphism_w base φ
  let wφ' : ∀ i : 𝒰.index,
      (φ'.f i).left ≫ (fun j : 𝒱.index ↦ (𝒱.obj j).hom) (φ'.α i) = (𝒰.obj i).hom ≫ base :=
    familyMorphism_w base φ'
  @Pseudofunctor.DescentData.pullFunctorIso
    C _ hc.fiberPseudofunctor
    𝒱.index V
    (fun i : 𝒱.index ↦ (𝒱.obj i).left)
    (fun i : 𝒱.index ↦ (𝒱.obj i).hom)
    U base
    𝒰.index
    (fun i : 𝒰.index ↦ (𝒰.obj i).left)
    (fun i : 𝒰.index ↦ (𝒰.obj i).hom)
    φ.α
    (fun i ↦ (φ.f i).left)
    wφ
    φ'.α
    (fun i ↦ (φ'.f i).left)
    wφ'

/-- Lemma 8.3.3 (1): pullback along a morphism of fixed-target families over `base : U ⟶ V`,
given canonically by a morphism `((SemiRepresentableFamily.map (Over.map base)).obj 𝒰 ⟶ 𝒱)`,
defines a functor on descent data. -/
noncomputable def pullbackFamilyDescentFunctor
    (base : U ⟶ V)
    (φ : ((SemiRepresentableFamily.map (Over.map base)).obj 𝒰 ⟶ 𝒱)) :
    DescentDatum p hc 𝒱 ⥤ DescentDatum p hc 𝒰 :=
  let e𝒱 := familyDescentDataEquivalence hc 𝒱
  let e𝒰 := familyDescentDataEquivalence hc 𝒰
  (e𝒱.functor ⋙ familyPullFunctor hc base φ) ⋙ e𝒰.inverse

/-- The image of one descent datum under the pullback functor from Lemma 8.3.3. -/
noncomputable abbrev pullbackFamilyDescentDatum
    (base : U ⟶ V)
    (φ : ((SemiRepresentableFamily.map (Over.map base)).obj 𝒰 ⟶ 𝒱))
    (D : DescentDatum p hc 𝒱) :
    DescentDatum p hc 𝒰 :=
  (pullbackFamilyDescentFunctor hc base φ).obj D

-- Proof sketch: this is definitional from `pullbackFamilyDescentDatum`.
/-- Applying the pullback functor to `D` gives the pulled-back descent datum. -/
theorem pullbackFamilyDescentFunctor_obj
    (base : U ⟶ V)
    (φ : ((SemiRepresentableFamily.map (Over.map base)).obj 𝒰 ⟶ 𝒱))
    (D : DescentDatum p hc 𝒱) :
    (pullbackFamilyDescentFunctor hc base φ).obj D =
      pullbackFamilyDescentDatum hc base φ D := sorry

/-- Evaluating the pulled-back descent datum at `i` gives the pullback of the local object
`D.obj (φ.α i)` along the component map `Uᵢ ⟶ V_{α(i)}`. -/
theorem pullbackFamilyDescentDatum_obj
    (base : U ⟶ V)
    (φ : ((SemiRepresentableFamily.map (Over.map base)).obj 𝒰 ⟶ 𝒱))
    (D : DescentDatum p hc 𝒱) (i : 𝒰.index) :
    (pullbackFamilyDescentDatum hc base φ D).obj i =
      hc.obj (φ.f i).left (D.obj (φ.α i)) :=
  rfl

/-- Lemma 8.3.3 (2): two pullback functors induced by morphisms of fixed-target families over the
same base map are canonically isomorphic. -/
noncomputable def pullbackFamilyDescentFunctorIso
    (base : U ⟶ V)
    (φ φ' : ((SemiRepresentableFamily.map (Over.map base)).obj 𝒰 ⟶ 𝒱)) :
    pullbackFamilyDescentFunctor hc base φ ≅ pullbackFamilyDescentFunctor hc base φ' :=
  let e𝒱 := familyDescentDataEquivalence hc 𝒱
  let e𝒰 := familyDescentDataEquivalence hc 𝒰
  let pullIso := familyPullFunctorIso hc base φ φ'
  Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft e𝒱.functor pullIso)
    e𝒰.inverse

/-- The component at `D` of the canonical comparison isomorphism between two pullback functors. -/
noncomputable abbrev pullbackFamilyDescentDatumIso
    (base : U ⟶ V)
    (φ φ' : ((SemiRepresentableFamily.map (Over.map base)).obj 𝒰 ⟶ 𝒱))
    (D : DescentDatum p hc 𝒱) :
    pullbackFamilyDescentDatum hc base φ D ≅ pullbackFamilyDescentDatum hc base φ' D :=
  (pullbackFamilyDescentFunctorIso hc base φ φ').app D

-- Proof sketch: this is the objectwise component of the natural isomorphism
-- `pullbackFamilyDescentFunctorIso`.
/-- Evaluating the comparison isomorphism of pullback functors at `D` gives the comparison
isomorphism between the pulled-back descent data. -/
theorem pullbackFamilyDescentFunctorIso_app
    (base : U ⟶ V)
    (φ φ' : ((SemiRepresentableFamily.map (Over.map base)).obj 𝒰 ⟶ 𝒱))
    (D : DescentDatum p hc 𝒱) :
    (pullbackFamilyDescentFunctorIso hc base φ φ').app D =
      pullbackFamilyDescentDatumIso hc base φ φ' D := sorry

end PullbackOfDescentData

end CategoryTheory
