import StacksProject_2024.Chap07.Example_7_14_3
import StacksProject_2024.Chap07.Lemma_7_12_4
import StacksProject_2024.Chap13.Situation_13_15_1
import StacksProject_2024.Chap18.Lemma_18_15_3
import StacksProject_2024.Chap21.Lemma_21_26_3
import StacksProject_2024.Chap21.SiteAbelianDerived

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory
open CochainComplex
open CochainComplex.HomComplex
open ComplexShape
open scoped CategoryTheory.GrothendieckTopology
open scoped GrothendieckTopologyDerivedSections

noncomputable section

universe u v u₁ v₁ u₂ v₂

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.GrothendieckTopology

section

variable {C : Type u} [Category.{v} C]
variable (τ τ' : GrothendieckTopology C)
variable [HasWeakSheafify τ (Type (max u v))]

/-- The identity functor is continuous for the topology comparison `τ' ≤ τ`. -/
instance topologyComparison_isContinuous
    (hle : τ' ≤ τ) :
    Functor.IsContinuous (𝟭 C) τ' τ :=
  id_isContinuous_of_le hle

/-- The underived topology-comparison direct image `ε_*` on abelian sheaves for `τ' ≤ τ`. -/
noncomputable abbrev topologyComparisonPushforward
    (hle : τ' ≤ τ) :
    SiteAbelianSheafCat τ ⥤ SiteAbelianSheafCat τ' := by
  letI : Functor.IsContinuous (𝟭 C) τ' τ := id_isContinuous_of_le hle
  exact (𝟭 C).sheafPushforwardContinuous AddCommGrpCat.{max u v} τ' τ

/-- The topology-comparison direct image is additive on abelian sheaves. -/
instance topologyComparisonPushforward_additive
    (hle : τ' ≤ τ) :
    Functor.Additive (topologyComparisonPushforward τ τ' hle) := by
  refine ⟨?_⟩
  intro F G f g
  ext U x
  rfl

/-- The raw identity-topology-comparison pushforward on abelian sheaves is additive. -/
instance topologyComparisonSheafPushforwardContinuous_additive
    (hle : τ' ≤ τ) :
    by
      letI : Functor.IsContinuous (𝟭 C) τ' τ := id_isContinuous_of_le hle
      exact Functor.Additive ((𝟭 C).sheafPushforwardContinuous AddCommGrpCat.{max u v} τ' τ) := by
  letI : Functor.IsContinuous (𝟭 C) τ' τ := id_isContinuous_of_le hle
  simpa [topologyComparisonPushforward] using topologyComparisonPushforward_additive τ τ' hle

/-- The topology-comparison derived pushforward `R ε_*` for `τ' ≤ τ`. -/
noncomputable abbrev topologyComparisonPushforwardDerived
    (hle : τ' ≤ τ)
    [Functor.HasRightDerivedFunctor
      (mapHomotopyCategoryToDerived (topologyComparisonPushforward τ τ' hle))
      (HomotopyCategory.quasiIso (SiteAbelianSheafCat τ) (up ℤ))] :
    DerivedCategory (SiteAbelianSheafCat τ) ⥤
      DerivedCategory (SiteAbelianSheafCat τ') :=
  Functor.totalRightDerived
    (mapHomotopyCategoryToDerived (topologyComparisonPushforward τ τ' hle))
    DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SiteAbelianSheafCat τ) (up ℤ))

/- Domain-style sampling for Lemma 21.29.3:
- primary domain: Mayer-Vietoris comparison morphisms in the derived category of abelian sheaves
  on a site, for objects lying in the essential image of the topology-comparison derived
  pushforward `R ε_*`, expressed here by the total right derived functor of
  `topologyComparisonPushforward hle`;
- inspected canonical declarations:
  `Functor.essImage`,
  `CochainComplex.mappingCocone.lift`,
  `Functor.totalRightDerived`,
  `mapHomotopyCategoryToDerived`,
  `topologyComparisonPushforward`,
  `siteAbelianInverseImageDerived`,
  `siteAbelianSectionsFunctor`,
  `siteAbelianSectionsDerived`,
  `siteAbelianSectionsDerivedMayerVietorisToBiprod`,
  `siteAbelianSectionsDerivedMayerVietorisDifference`;
- owner abstraction: the source-facing owner is a comparison morphism
  `c^{K'}_{X,Z,Y,E}` for a fixed square `E ⟶ Y`, `E ⟶ Z`, `Y ⟶ X`, `Z ⟶ X`, together with
  explicit bridge data exhibiting it as the canonical mapping-cocone lift of a Mayer-Vietoris
  cochain model whose first two arrows identify with the canonical Mayer-Vietoris restriction
  maps, while the topology-comparison essential-image hypothesis is
  organized by the total right derived functor of `topologyComparisonPushforward hle`,
  which is the topology-comparison specialization of the Chapter 21 derived-pushforward
  construction and, under stronger bridge hypotheses, agrees with
  `siteAbelianInverseImageDerived τ' τ (𝟭 C)`,
  and the section terms
  `RΓ(X,-)`, `RΓ(Y,-)`, `RΓ(Z,-)`, `RΓ(E,-)` are the canonical derived-sections functors
  `siteAbelianSectionsDerived τ' U`;
- primitive data: the topology-comparison morphism `ε : (C, τ) → (C, τ')`, the
  canonical `IsPushout` witness for the sheafified-representable square, the monomorphism
  hypothesis on `h[E]^#[τ] ⟶ h[Y]^#[τ]`, and the object `K'`;
- bridge/view: a cochain model `IX ⟶ IZY ⟶ IE` together with identifications of its terms with
  the canonical derived-section objects, realizing the source-facing comparison morphism by a
  mapping-cocone lift; under the stronger continuous/cocontinuous identity-topology-comparison
  hypotheses, a companion bridge identifies that direct total-right-derived functor with the
  canonical Chap21 owner `siteAbelianInverseImageDerived τ' τ (𝟭 C)`;
- derived API: the theorem that any source-facing comparison morphism is an isomorphism for
  objects in the essential image.

Source/core/bridge triage:
- `source-facing`: a comparison morphism `c^{K'}_{X,Z,Y,E}` for a fixed square
  `E ⟶ Y`, `E ⟶ Z`, `Y ⟶ X`, `Z ⟶ X`, together with explicit bridge data realizing it as the
  canonical lift from a Mayer-Vietoris cochain model whose first two arrows are the canonical
  Mayer-Vietoris restriction maps, and the claim that any such realization is an isomorphism
  for `K'` in the essential image of the topology-comparison total right derived functor of
  `topologyComparisonPushforward hle`;
- `core/canonical`: `topologyComparisonPushforward`, `Functor.totalRightDerived`,
  `siteAbelianInverseImageDerived`,
  `Functor.essImage`, `CochainComplex.mappingCocone.lift`,
  and the canonical derived sections functors `siteAbelianSectionsDerived τ' U`;
- `bridge/view`: the chosen cochain model `IX ⟶ IZY ⟶ IE` together with the isomorphisms
  identifying its three terms with the canonical derived sections objects, realizing a
  source-facing comparison morphism through an explicit equality with the canonical
  `mappingCocone.lift`, and, under stronger assumptions, the functor isomorphism from the
  total right derived functor of `topologyComparisonPushforward hle` to
  `siteAbelianInverseImageDerived τ' τ (𝟭 C)`.
-/

-- Proof sketch: the defining relation for `mappingCocone.lift` with the zero `(-1)`-cochain
-- reduces to the chain-map identity `α ≫ β = 0`.
/-- The zero `(-1)`-cochain satisfies the cocycle relation needed to define the canonical
comparison lift into `mappingCocone β`. -/
theorem mayerVietorisComparisonLift_condition
    {IX IZY IE : CochainComplex AddCommGrpCat ℤ}
    (α : IX ⟶ IZY) (β : IZY ⟶ IE) (hαβ : α ≫ β = 0) :
    δ (-1) 0 (0 : Cochain IX IE (-1)) +
        Cochain.ofHom (α ≫ β) =
      0 := by
  simpa [hαβ]

/-- A morphism `comparison` realizes the Mayer-Vietoris comparison
`c^{K'}_{X,Z,Y,E}` for the square `E ⟶ Y`, `E ⟶ Z`, `Y ⟶ X`, `Z ⟶ X` if it is the canonical
`mappingCocone.lift` arising from a short exact cochain Mayer-Vietoris model whose first two
maps identify with the canonical derived restriction maps
`RΓ[τ'](X,-) ⟶ RΓ[τ'](Z,-) ⊞ RΓ[τ'](Y,-)` and
`RΓ[τ'](Z,-) ⊞ RΓ[τ'](Y,-) ⟶ RΓ[τ'](E,-)`. -/
inductive IsMayerVietorisComparison
    (τ' : GrothendieckTopology C)
    [HasWeakSheafify τ' AddCommGrpCat]
    [IsGrothendieckAbelian.{max u v} (SiteAbelianSheafCat τ')]
    {X Y Z E : C}
    (f : E ⟶ Y) (g : E ⟶ Z) (inY : Y ⟶ X) (inZ : Z ⟶ X)
    (K' : DerivedCategory (SiteAbelianSheafCat τ'))
    {IZY IE : CochainComplex AddCommGrpCat ℤ}
    {β : IZY ⟶ IE}
    (comparison : RΓ[τ'](X).obj K' ⟶ Q.obj (mappingCocone β)) : Prop where
  | mk
      (IX : CochainComplex AddCommGrpCat ℤ)
      (hIX : Q.obj IX ≅ RΓ[τ'](X).obj K')
      (α : IX ⟶ IZY)
      (hαβ : α ≫ β = 0)
      (hIZY : Q.obj IZY ≅ ((RΓ[τ'](Z)) ⊞ (RΓ[τ'](Y))).obj K')
      (hIE : Q.obj IE ≅ RΓ[τ'](E).obj K')
      (hα :
        Q.map α =
          hIX.hom ≫
            ((τ'.siteAbelianSectionsDerivedMayerVietorisToBiprod inY inZ).app K') ≫
              hIZY.inv)
      (hβ :
        Q.map β =
          hIZY.hom ≫
            ((τ'.siteAbelianSectionsDerivedMayerVietorisDifference f g).app K') ≫
              hIE.inv)
      (hshort : (ShortComplex.mk α β hαβ).ShortExact)
      (comparison_eq :
        comparison =
          hIX.inv ≫
            Q.map
              (mappingCocone.lift β α (0 : Cochain IX IE (-1))
                (mayerVietorisComparisonLift_condition α β hαβ))) :
      IsMayerVietorisComparison τ' f g inY inZ K' comparison

/-- Source-facing predicate asserting that the canonical Mayer-Vietoris comparison
`c^{K'}_{X,Z,Y,E}` is an isomorphism. The actual comparison morphism is represented in Lean by any
chosen realization satisfying `IsMayerVietorisComparison`, so this predicate is stated by
quantifying over those bridge realizations rather than introducing new chosen data. -/
def mayerVietorisComparisonIsIso
    (τ' : GrothendieckTopology C)
    [HasWeakSheafify τ' AddCommGrpCat]
    [IsGrothendieckAbelian.{max u v} (SiteAbelianSheafCat τ')]
    {X Y Z E : C}
    (f : E ⟶ Y) (g : E ⟶ Z) (inY : Y ⟶ X) (inZ : Z ⟶ X)
    (K' : DerivedCategory (SiteAbelianSheafCat τ')) : Prop :=
  ∀ ⦃IZY IE : CochainComplex AddCommGrpCat ℤ⦄ ⦃β : IZY ⟶ IE⦄
    (comparison : RΓ[τ'](X).obj K' ⟶ Q.obj (mappingCocone β)),
      IsMayerVietorisComparison τ' f g inY inZ K' comparison → IsIso comparison

/-- Explicit cochain Mayer-Vietoris data produces the source-facing realization predicate for the
comparison morphism `c^{K'}_{X,Z,Y,E}`. -/
theorem isMayerVietorisComparison_of_model
    (τ' : GrothendieckTopology C)
    {X Y Z E : C}
    [HasWeakSheafify τ' AddCommGrpCat]
    [IsGrothendieckAbelian.{max u v} (SiteAbelianSheafCat τ')]
    (f : E ⟶ Y) (g : E ⟶ Z) (inY : Y ⟶ X) (inZ : Z ⟶ X)
    (K' : DerivedCategory (SiteAbelianSheafCat τ'))
    {IX IZY IE : CochainComplex AddCommGrpCat ℤ}
    (hIX : Q.obj IX ≅ RΓ[τ'](X).obj K')
    (α : IX ⟶ IZY)
    (β : IZY ⟶ IE)
    (hαβ : α ≫ β = 0)
    (hIZY : Q.obj IZY ≅ ((RΓ[τ'](Z)) ⊞ (RΓ[τ'](Y))).obj K')
    (hIE : Q.obj IE ≅ RΓ[τ'](E).obj K')
    (hα :
      Q.map α =
        hIX.hom ≫
          ((τ'.siteAbelianSectionsDerivedMayerVietorisToBiprod inY inZ).app K') ≫
            hIZY.inv)
    (hβ :
      Q.map β =
        hIZY.hom ≫
          ((τ'.siteAbelianSectionsDerivedMayerVietorisDifference f g).app K') ≫
            hIE.inv)
    (comparison : RΓ[τ'](X).obj K' ⟶ Q.obj (mappingCocone β))
    (hshort : (ShortComplex.mk α β hαβ).ShortExact)
    (hcomparison :
      comparison =
        hIX.inv ≫
          Q.map
            (mappingCocone.lift β α (0 : Cochain IX IE (-1))
              (mayerVietorisComparisonLift_condition α β hαβ))) :
    IsMayerVietorisComparison τ' f g inY inZ K' comparison := by
  exact .mk IX hIX α hαβ hIZY hIE hα hβ hshort hcomparison

-- Proof sketch: use the essential-image hypothesis to choose a source object whose image under
-- `R ε_*` is `K'`. Lemma `21.20.10` upgrades a K-injective representative along the comparison
-- functor, while Lemma `21.26.3` gives the short exact sequence of section complexes whose
-- canonical lift models `c^{K'}_{X,Z,Y,E}`. The resulting source-facing comparison morphism is
-- therefore an isomorphism.
/-- Lemma 21.29.3: let `ε : (C, τ) ⟶ (C, τ')` be the topology-comparison morphism for `τ' ≤ τ`,
and let `E ⟶ Y`, `E ⟶ Z`, `Y ⟶ X`, `Z ⟶ X` be a square such that `h[X]^#[τ]` is the pushout of
`h[E]^#[τ] ⟶ h[Y]^#[τ]` and `h[E]^#[τ] ⟶ h[Z]^#[τ]`, with `h[E]^#[τ] ⟶ h[Y]^#[τ]` injective. If
`K'` lies in the essential image of the topology-comparison derived pushforward `R ε_*`, then the
Mayer-Vietoris comparison morphism `c^{K'}_{X,Z,Y,E}` attached to any cochain Mayer-Vietoris
model whose first two arrows realize the canonical restriction maps is an isomorphism. In Lean
the public surface is a morphism `comparison` together with bridge data identifying its model
maps with the canonical `siteAbelianSectionsDerivedMayerVietorisToBiprod` and
`siteAbelianSectionsDerivedMayerVietorisDifference`, so the generic `mappingCocone.lift` remains
bridge data rather than the exported owner; a stronger companion theorem below bridges the
topology-comparison derived functor to the canonical Chap21 owner
`siteAbelianInverseImageDerived τ' τ (𝟭 C)`. -/
@[stacks 0F19]
theorem mayerVietorisComparison_isIso_of_mem_essentialImage
    {X Y Z E : C}
    [HasWeakSheafify τ' AddCommGrpCat]
    [IsGrothendieckAbelian.{max u v} (SiteAbelianSheafCat τ')]
    (f : E ⟶ Y) (g : E ⟶ Z)
    (inY : Y ⟶ X) (inZ : Z ⟶ X)
    (hpushout :
      IsPushout
        (τ.sheafifiedRepresentableMap f)
        (τ.sheafifiedRepresentableMap g)
        (τ.sheafifiedRepresentableMap inY)
        (τ.sheafifiedRepresentableMap inZ))
    (hmono : Mono (τ.sheafifiedRepresentableMap f))
    (hle : τ' ≤ τ)
    [Functor.HasRightDerivedFunctor
      (mapHomotopyCategoryToDerived (topologyComparisonPushforward τ τ' hle))
      (HomotopyCategory.quasiIso (SiteAbelianSheafCat τ) (up ℤ))]
    (K' : DerivedCategory (SiteAbelianSheafCat τ'))
    (hK' :
      Functor.essImage
        (topologyComparisonPushforwardDerived τ τ' hle)
        K')
    {IZY IE : CochainComplex AddCommGrpCat ℤ}
    {β : IZY ⟶ IE}
    (comparison : RΓ[τ'](X).obj K' ⟶ Q.obj (mappingCocone β))
    (hcomparison :
      IsMayerVietorisComparison τ' f g inY inZ K' comparison) :
    IsIso comparison := by
  rcases hcomparison with ⟨IX, hIX, α, hαβ, hIZY, hIE, hα, hβ, hshort, rfl⟩
  sorry

/-- Companion API for Lemma `21.29.3`: once `K'` lies in the essential image of
`topologyComparisonPushforwardDerived τ τ' hle`, any explicit realization of the canonical
Mayer-Vietoris comparison map `c^{K'}_{X,Z,Y,E}` is an isomorphism. -/
theorem IsMayerVietorisComparison.isIso_of_mem_essentialImage
    {X Y Z E : C}
    [HasWeakSheafify τ' AddCommGrpCat]
    [IsGrothendieckAbelian.{max u v} (SiteAbelianSheafCat τ')]
    (f : E ⟶ Y) (g : E ⟶ Z)
    (inY : Y ⟶ X) (inZ : Z ⟶ X)
    (hpushout :
      IsPushout
        (τ.sheafifiedRepresentableMap f)
        (τ.sheafifiedRepresentableMap g)
        (τ.sheafifiedRepresentableMap inY)
        (τ.sheafifiedRepresentableMap inZ))
    (hmono : Mono (τ.sheafifiedRepresentableMap f))
    (hle : τ' ≤ τ)
    [Functor.HasRightDerivedFunctor
      (mapHomotopyCategoryToDerived (topologyComparisonPushforward τ τ' hle))
      (HomotopyCategory.quasiIso (SiteAbelianSheafCat τ) (up ℤ))]
    (K' : DerivedCategory (SiteAbelianSheafCat τ'))
    (hK' :
      Functor.essImage
        (topologyComparisonPushforwardDerived τ τ' hle)
        K')
    {IZY IE : CochainComplex AddCommGrpCat ℤ}
    {β : IZY ⟶ IE}
    {comparison : RΓ[τ'](X).obj K' ⟶ Q.obj (mappingCocone β)}
    (hcomparison :
      IsMayerVietorisComparison τ' f g inY inZ K' comparison) :
    IsIso comparison := by
  exact
    mayerVietorisComparison_isIso_of_mem_essentialImage
      τ τ' f g inY inZ hpushout hmono hle K' hK' comparison hcomparison

/-- Source-facing companion to Lemma `21.29.3`: if `K'` lies in the essential image of
`topologyComparisonPushforwardDerived τ τ' hle`, then the canonical Mayer-Vietoris comparison
`c^{K'}_{X,Z,Y,E}` is an isomorphism. -/
theorem mayerVietorisComparisonIsIso_of_mem_essentialImage
    {X Y Z E : C}
    [HasWeakSheafify τ' AddCommGrpCat]
    [IsGrothendieckAbelian.{max u v} (SiteAbelianSheafCat τ')]
    (f : E ⟶ Y) (g : E ⟶ Z)
    (inY : Y ⟶ X) (inZ : Z ⟶ X)
    (hpushout :
      IsPushout
        (τ.sheafifiedRepresentableMap f)
        (τ.sheafifiedRepresentableMap g)
        (τ.sheafifiedRepresentableMap inY)
        (τ.sheafifiedRepresentableMap inZ))
    (hmono : Mono (τ.sheafifiedRepresentableMap f))
    (hle : τ' ≤ τ)
    [Functor.HasRightDerivedFunctor
      (mapHomotopyCategoryToDerived (topologyComparisonPushforward τ τ' hle))
      (HomotopyCategory.quasiIso (SiteAbelianSheafCat τ) (up ℤ))]
    (K' : DerivedCategory (SiteAbelianSheafCat τ'))
    (hK' :
      Functor.essImage
        (topologyComparisonPushforwardDerived τ τ' hle)
        K') :
    mayerVietorisComparisonIsIso τ' f g inY inZ K' := by
  intro IZY IE β comparison hcomparison
  exact
    IsMayerVietorisComparison.isIso_of_mem_essentialImage
      τ τ' f g inY inZ hpushout hmono hle K' hK' hcomparison

/-- Under the stronger identity-topology-comparison hypotheses, essential-image membership for the
direct topology-comparison total right derived functor is equivalent to essential-image
membership for the canonical Chap21 owner `siteAbelianInverseImageDerived τ' τ (𝟭 C)`. -/
theorem topologyComparisonRightDerived_mem_essImage_iff_siteAbelianInverseImageDerived
    (hle : τ' ≤ τ)
    (K' : DerivedCategory (SiteAbelianSheafCat τ'))
    [Functor.IsContinuous (𝟭 C) τ' τ]
    [Functor.Additive ((𝟭 C).sheafPushforwardContinuous AddCommGrpCat.{max u v} τ' τ)]
    [Functor.IsCocontinuous (𝟭 C) τ' τ]
    [HasWeakSheafify τ AddCommGrpCat.{max u v}]
    [HasSheafify τ AddCommGrpCat.{max u v}]
    [HasSheafify τ' AddCommGrpCat.{max u v}]
    [IsGrothendieckAbelian.{max u v} (SiteAbelianSheafCat τ)]
    [Functor.HasRightDerivedFunctor
      (mapHomotopyCategoryToDerived (topologyComparisonPushforward τ τ' hle))
      (HomotopyCategory.quasiIso (SiteAbelianSheafCat τ) (up ℤ))] :
    Functor.essImage
      (topologyComparisonPushforwardDerived τ τ' hle)
        K' ↔
      Functor.essImage (siteAbelianInverseImageDerived τ' τ (𝟭 C)) K' := by
  letI :
      Functor.Additive ((𝟭 C).sheafPushforwardContinuous AddCommGrpCat.{max u v} τ' τ) :=
    topologyComparisonSheafPushforwardContinuous_additive τ τ' hle
  let pushAb : SiteAbelianSheafCat τ ⥤ SiteAbelianSheafCat τ' :=
    (𝟭 C).sheafPushforwardContinuous AddCommGrpCat.{max u v} τ' τ
  let hExact : exactFunctor (SiteAbelianSheafCat τ) (SiteAbelianSheafCat τ') pushAb :=
    Functor.sheafPushforwardContinuous_exact_of_isAlmostCocontinuous (𝟭 C)
  letI : PreservesFiniteLimits pushAb := (CategoryTheory.exactFunctor_iff pushAb).1 hExact |>.1
  letI : PreservesFiniteColimits pushAb := (CategoryTheory.exactFunctor_iff pushAb).1 hExact |>.2
  let derivedPush : DerivedCategory (SiteAbelianSheafCat τ) ⥤
      DerivedCategory (SiteAbelianSheafCat τ') := pushAb.mapDerivedCategory
  let e₁ : topologyComparisonPushforwardDerived τ τ' hle ≅ derivedPush := by
    letI :
        derivedPush.IsRightDerivedFunctor
          pushAb.mapDerivedCategoryFactorsh.inv
          (HomotopyCategory.quasiIso (SiteAbelianSheafCat τ) (ComplexShape.up ℤ)) := by
      simpa [mapHomotopyCategoryToDerived] using
        (Functor.isRightDerivedFunctor_of_inverts
          (HomotopyCategory.quasiIso (SiteAbelianSheafCat τ) (ComplexShape.up ℤ))
          derivedPush
          pushAb.mapDerivedCategoryFactorsh)
    exact
      (topologyComparisonPushforwardDerived τ τ' hle).rightDerivedUnique
        derivedPush
        (Functor.totalRightDerivedUnit
          (mapHomotopyCategoryToDerived pushAb)
          (DerivedCategory.Qh :
            HomotopyCategory (SiteAbelianSheafCat τ) (ComplexShape.up ℤ) ⥤
              DerivedCategory (SiteAbelianSheafCat τ))
          (HomotopyCategory.quasiIso (SiteAbelianSheafCat τ) (ComplexShape.up ℤ)))
        pushAb.mapDerivedCategoryFactorsh.inv
        (HomotopyCategory.quasiIso (SiteAbelianSheafCat τ) (ComplexShape.up ℤ))
  let e₂ : siteAbelianInverseImageDerived τ' τ (𝟭 C) ≅ derivedPush := by
    letI :
        (pushAb.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).HasRightDerivedFunctor
          (HomologicalComplex.quasiIso (SiteAbelianSheafCat τ) (ComplexShape.up ℤ)) :=
      CategoryTheory.mapHomologicalComplexQ_hasRightDerivedFunctor pushAb
    letI :
        derivedPush.IsRightDerivedFunctor
          pushAb.mapDerivedCategoryFactors.inv
          (HomologicalComplex.quasiIso (SiteAbelianSheafCat τ) (ComplexShape.up ℤ)) := by
      simpa using
        (Functor.isRightDerivedFunctor_of_inverts
          (HomologicalComplex.quasiIso (SiteAbelianSheafCat τ) (ComplexShape.up ℤ))
          derivedPush
          pushAb.mapDerivedCategoryFactors)
    exact
      (siteAbelianInverseImageDerived τ' τ (𝟭 C)).rightDerivedUnique
        derivedPush
        (Functor.totalRightDerivedUnit
          (pushAb.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
          DerivedCategory.Q
          (HomologicalComplex.quasiIso (SiteAbelianSheafCat τ) (ComplexShape.up ℤ)))
        pushAb.mapDerivedCategoryFactors.inv
        (HomologicalComplex.quasiIso (SiteAbelianSheafCat τ) (ComplexShape.up ℤ))
  let e : topologyComparisonPushforwardDerived τ τ' hle ≅
      siteAbelianInverseImageDerived τ' τ (𝟭 C) :=
    e₁ ≪≫ e₂.symm
  constructor
  · rintro ⟨K, ⟨i⟩⟩
    exact ⟨K, ⟨asIso (e.inv.app K) ≪≫ i⟩⟩
  · rintro ⟨K, ⟨i⟩⟩
    exact ⟨K, ⟨asIso (e.hom.app K) ≪≫ i⟩⟩

/-- Stronger-assumption companion to Lemma 21.29.3: once the topology-comparison derived
pushforward is bridged to the canonical Chap21 owner `siteAbelianInverseImageDerived τ' τ (𝟭 C)`,
the same Mayer-Vietoris comparison morphisms are isomorphisms for objects in that canonical
essential image. -/
theorem mayerVietorisComparison_isIso_of_mem_essentialImage_siteAbelianInverseImageDerived
    {X Y Z E : C}
    [HasWeakSheafify τ' AddCommGrpCat]
    [IsGrothendieckAbelian.{max u v} (SiteAbelianSheafCat τ')]
    (f : E ⟶ Y) (g : E ⟶ Z)
    (inY : Y ⟶ X) (inZ : Z ⟶ X)
    (hpushout :
      IsPushout
        (τ.sheafifiedRepresentableMap f)
        (τ.sheafifiedRepresentableMap g)
        (τ.sheafifiedRepresentableMap inY)
        (τ.sheafifiedRepresentableMap inZ))
    (hmono : Mono (τ.sheafifiedRepresentableMap f))
    (hle : τ' ≤ τ)
    [Functor.IsContinuous (𝟭 C) τ' τ]
    [Functor.Additive ((𝟭 C).sheafPushforwardContinuous AddCommGrpCat.{max u v} τ' τ)]
    [Functor.IsCocontinuous (𝟭 C) τ' τ]
    [HasWeakSheafify τ AddCommGrpCat.{max u v}]
    [HasSheafify τ AddCommGrpCat.{max u v}]
    [HasSheafify τ' AddCommGrpCat.{max u v}]
    [IsGrothendieckAbelian.{max u v} (SiteAbelianSheafCat τ)]
    [Functor.HasRightDerivedFunctor
      (mapHomotopyCategoryToDerived (topologyComparisonPushforward τ τ' hle))
      (HomotopyCategory.quasiIso (SiteAbelianSheafCat τ) (up ℤ))]
    (K' : DerivedCategory (SiteAbelianSheafCat τ'))
    (hK' : Functor.essImage (siteAbelianInverseImageDerived τ' τ (𝟭 C)) K')
    {IZY IE : CochainComplex AddCommGrpCat ℤ}
    {β : IZY ⟶ IE}
    (comparison : RΓ[τ'](X).obj K' ⟶ Q.obj (mappingCocone β))
    (hcomparison :
      IsMayerVietorisComparison τ' f g inY inZ K' comparison) :
    IsIso comparison := by
  have hK'' :
      Functor.essImage
        (topologyComparisonPushforwardDerived τ τ' hle)
        K' :=
    (topologyComparisonRightDerived_mem_essImage_iff_siteAbelianInverseImageDerived
      τ τ' hle K').2 hK'
  exact
    mayerVietorisComparison_isIso_of_mem_essentialImage
      τ τ' f g inY inZ hpushout hmono hle K' hK'' comparison hcomparison

end

end CategoryTheory.GrothendieckTopology
