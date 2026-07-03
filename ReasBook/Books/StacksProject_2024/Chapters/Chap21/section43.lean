import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.CategoryTheory.ObjectProperty.Extensions
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.ObjectProperty.Kernels
import Mathlib.CategoryTheory.ObjectProperty.Retract
import Mathlib.CategoryTheory.Triangulated.Subcategory

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_21_43_1 (from Chap21) -/
noncomputable section

open CategoryTheory Opposite

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.ModulesOnCategory

/-
Domain-style sampling:
- primary domain: object properties on a derived category and the full subcategories they define;
- sampled owner declarations:
  `CategoryTheory.ObjectProperty.FullSubcategory`,
  `CategoryTheory.derivedCategoryCohomologyInProperty`,
  `SheafOfModules.ChaoticSite.derivedQuasiCoherentProperty`,
  `CategoryTheory.ModulesOnCategory.QC`;
- best owner abstraction: the object property on `D` cut out by the comparison maps, with
  `QC(\mathcal C, \mathcal O)` as the associated full subcategory;
- primitive data: `RGamma`, `derivedRestrict`, and `comparison`;
- derived API: the full subcategory `QC`, with membership unpacked by the inherited field
  `K.property`.

Source/core/bridge triage:
- `source-facing`: the Section `21.43` quasi-coherent condition and its full subcategory;
- `core/canonical`: `ObjectProperty D` and its `FullSubcategory`;
- `bridge/view`: membership in `QC` is read directly through the canonical full-subcategory field
  `K.property`.
-/

section

variable {C : Type u} [Category C]
variable {D : Type v} [Category D]
variable (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u})
variable (RGamma : ∀ U : C, D ⥤ DerivedCategory (ModuleCat (𝒪.obj (op U))))
variable
  (derivedRestrict :
    ∀ {U V : C},
      (U ⟶ V) →
      DerivedCategory (ModuleCat (𝒪.obj (op V))) ⥤
        DerivedCategory (ModuleCat (𝒪.obj (op U))))
variable
  (comparison :
    ∀ {U V : C} (f : U ⟶ V),
      RGamma V ⋙ derivedRestrict f ⟶ RGamma U)

/-- The object property cutting out those `K ∈ D(\mathcal O)` whose derived restriction
comparison morphisms are isomorphisms on every arrow of `\mathcal C`. -/
def isQuasiCoherent : ObjectProperty D :=
  fun K ↦ ∀ ⦃U V : C⦄ (f : U ⟶ V), IsIso ((comparison f).app K)

/-- Definition 21.43.1: `QC(\mathcal C, \mathcal O)` is the full subcategory of `D(\mathcal O)`
consisting of those objects `K` for which, for every arrow `U ⟶ V` in `\mathcal C`, the canonical
derived base-change map `RΓ(V, K) \otimes_{\mathcal O(V)}^{\mathbf L} \mathcal O(U) ⟶ RΓ(U, K)`
is an isomorphism in `D(\mathcal O(U))`. -/
abbrev QC :=
  (isQuasiCoherent 𝒪 RGamma derivedRestrict comparison).FullSubcategory

end

end CategoryTheory.ModulesOnCategory

/-! ### Lemma_21_43_2 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open Opposite

noncomputable section

universe w u v

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

/- Domain-style sampling for Lemma 21.43.2:
- primary domain: weak-LinearRepresentations_Serre_1977 object properties on abelian categories and the derived subcategories
  they cut out by cohomology conditions;
- sampled owner declarations:
  `derivedCategoryCohomologyInProperty`,
  `DerivedCategoryWithCohomologyIn`,
  `derivedCategoryCohomologyInProperty_isClosedUnderIsomorphisms`,
  `derivedCategoryCohomologyInProperty_isTriangulated`;
- best owner abstraction: the Chapter 13 owner
  `derivedCategoryCohomologyInProperty P` on `DerivedCategory A`, with the corresponding full
  subcategory owner `DerivedCategoryWithCohomologyIn P`;
- primitive data: an ambient object property `P : ObjectProperty A`;
- derived API: strict fullness, saturation, triangulated closure, and the colimit-closure result
  for the owner property on `D(A)`.

Source/core/bridge triage:
- `source-facing`: the chaotic-site quasi-coherent derived subcategory `QC(\mathcal O)`;
- `core/canonical`: `derivedCategoryCohomologyInProperty` and
  `DerivedCategoryWithCohomologyIn`;
- `bridge/view`: the specialization to the quasi-coherent module property on
  `Mod(\mathcal O)`. -/

end CategoryTheory

namespace SheafOfModules.ChaoticSite

variable {C : Type u} [Category.{v} C]
variable (𝒪 : Sheaf (⊥ : GrothendieckTopology C) CommRingCat)
variable [((⊥ : GrothendieckTopology C)).HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [∀ U : C, ((⊥ : GrothendieckTopology C).over U).HasSheafCompose
  (forget₂ RingCat AddCommGrpCat)]
variable [∀ U : C, HasWeakSheafify ((⊥ : GrothendieckTopology C).over U) AddCommGrpCat]
variable [∀ U : C, ((⊥ : GrothendieckTopology C).over U).WEqualsLocallyBijective AddCommGrpCat]

local notation "Mod𝒪" => chaoticModuleCategory 𝒪
local notation "QCoh" =>
  SheafOfModules.isQuasicoherent (ringSheaf (⊥ : GrothendieckTopology C) 𝒪)
local notation "DQCoh" => derivedCategoryCohomologyInProperty QCoh

variable [Abelian Mod𝒪]
variable [Fact (∀ ⦃U V : C⦄ (f : U ⟶ V), RingHom.Flat ((𝒪.obj.map f.op).hom))]

-- Proof sketch: flat restriction maps make quasi-coherent modules on the chaotic site into a weak
-- LinearRepresentations_Serre_1977 subcategory by Lemma `18.24.4`; then the generic derived-category statement for
-- `D_P(A)` shows that the degreewise quasi-coherent condition is preserved under isomorphisms.
/-- The object property defining `QC(\mathcal O)` is strictly full inside `D(\mathcal O)`. -/
instance derivedQuasiCoherentProperty_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms DQCoh :=
  derivedCategoryCohomologyInProperty_isClosedUnderIsomorphisms QCoh

-- Proof sketch: after Lemma `18.24.4`, quasi-coherent modules form a weak LinearRepresentations_Serre_1977 subcategory of
-- `Mod(\mathcal O)`, and the generic saturation result for `D_P(A)` identifies retracts in the
-- derived category with direct summands of all cohomology modules.
/-- The object property defining `QC(\mathcal O)` is saturated, i.e. stable under retracts in
`D(\mathcal O)`. -/
instance derivedQuasiCoherentProperty_isStableUnderRetracts :
    ObjectProperty.IsStableUnderRetracts DQCoh :=
  derivedCategoryCohomologyInProperty_isSaturated QCoh

-- Proof sketch: flat restriction maps on the chaotic site imply that quasi-coherent
-- `\mathcal O`-modules form a weak LinearRepresentations_Serre_1977 subcategory of `Mod(\mathcal O)`. The derived
-- cohomology-in-subcategory criterion then shows that the degreewise quasi-coherent condition is
-- preserved under zero objects, shifts, and distinguished triangles.
/-- Lemma 21.43.2: in the chaotic-site module situation, the object property cutting out
`QC(\mathcal O) \subset D(\mathcal O)` is triangulated. The companion declarations in this file
record the strict fullness, saturation, and arbitrary direct-sum closure asserted in the same
lemma. -/
instance derivedQuasiCoherentProperty_isTriangulated :
    ObjectProperty.IsTriangulated DQCoh :=
  derivedCategoryCohomologyInProperty_isTriangulated QCoh

-- Proof sketch: apply the previous colimit-closure criterion to the object property of
-- quasi-coherent `\mathcal O`-modules, using that `H^n` commutes with the chosen coproducts and
-- that quasi-coherent modules are already closed under those coproducts.
/-- If quasi-coherent `\mathcal O`-modules are closed under `ι`-indexed direct sums and each
cohomology functor on `D(\mathcal O)` commutes with those sums, then `QC(\mathcal O)` is also
closed under `ι`-indexed direct sums. -/
instance derivedQuasiCoherentProperty_isClosedUnderDirectSums
    (ι : Type w)
    [IsClosedUnderColimitsOfShape
      QCoh
      (Discrete ι)]
    [∀ n : ℤ, PreservesColimitsOfShape (Discrete ι)
      (DerivedCategory.homologyFunctor Mod𝒪 n)] :
    ObjectProperty.IsClosedUnderColimitsOfShape DQCoh (Discrete ι) :=
  derivedCategoryCohomologyInProperty_isClosedUnderColimitsOfShape QCoh (Discrete ι)

end SheafOfModules.ChaoticSite

/-! ### Lemma_21_43_3 (from Chap21) -/
open CategoryTheory
open Opposite

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.ModulesOnCategory

/- Domain-style sampling for Lemma 21.43.3:
- primary domain: derived quasi-coherence on modules over a category with the chaotic topology,
  together with the ordinary quasi-coherent owner for module sheaves;
- sampled owner declarations:
  `CategoryTheory.ModulesOnCategory.isQuasiCoherent`,
  `CategoryTheory.ModulesOnCategory.QC`,
  `SheafOfModules.isQuasicoherent_iff_tensor_sections_map_isIso`;
- best owner abstraction: the source-facing Section `21.43` owner
  `CategoryTheory.ModulesOnCategory.QC 𝒪 RGamma derivedRestrict comparison`, with the Chapter 18
  owner predicate `SheafOfModules.IsQuasicoherent` as the target notion;
- primitive data: the chaotic-site module category `SheafOfModules (ringSheaf (⊥ : GrothendieckTopology C) 𝒪)`,
  the derived sections functors `RGamma`, the derived restriction functors `derivedRestrict`, and
  their comparison morphisms;
- derived API: membership in `QC` via the inherited field `M.property`, homology objects via
  `DerivedCategory.homologyFunctor`, and the target quasi-coherence predicate on the top
  cohomology sheaf.

Source/core/bridge triage:
- `source-facing`: the Section `21.43` full subcategory `QC(\mathcal C, \mathcal O)`;
- `core/canonical`: the chapter owner `QC` from Definition `21.43.1` and the Chapter 18 owner
  `(H^b M).IsQuasicoherent`;
- `bridge/view`: the present lemma, which passes from the derived base-change condition on `M` to
  quasi-coherence of the top cohomology sheaf. -/

variable {C : Type u} [Category.{u} C]
variable (𝒪 : Sheaf (⊥ : GrothendieckTopology C) CommRingCat)
variable [((⊥ : GrothendieckTopology C)).HasSheafCompose (forget₂ CommRingCat RingCat)]

/-- The category `\mathrm{Mod}(\mathcal O)` of module sheaves on a category with the chaotic
topology. -/
abbrev moduleOnCategory :=
  SheafOfModules (ringSheaf (⊥ : GrothendieckTopology C) 𝒪)

-- Proof sketch: for each arrow `U ⟶ V`, the `QC` hypothesis gives an isomorphism
-- `RΓ(V,M) ⊗^L_{\mathcal O(V)} \mathcal O(U) ≅ RΓ(U,M)`. Because the objectwise cohomology of
-- `M` vanishes above `b`, the Tor spectral sequence degenerates on the top row and identifies the
-- degree-`b` homology of this derived tensor product with ordinary scalar extension of
-- `H^b(RΓ(V,M))`. Lemma `18.24.3` is then the chaotic-topology criterion for quasi-coherence.
/-- Lemma 21.43.3: in the section-`21.43` setup for modules on a category, if `M` satisfies the
derived base-change condition defining `QC(\mathcal C, \mathcal O)` and its objectwise derived
sections have no cohomology above degree `b`, then the cohomology module `H^b(M)` is
quasi-coherent on `(\mathcal C, \mathcal O)` in the sense of Modules on Sites,
Definition 18.23.1. -/
theorem top_cohomology_isQuasicoherent
    (RGamma :
      ∀ U : C,
        DerivedCategory (moduleOnCategory 𝒪) ⥤
          DerivedCategory (ModuleCat (𝒪.1.obj (op U))))
    (derivedRestrict :
      ∀ {U V : C}, (U ⟶ V) →
        DerivedCategory (ModuleCat (𝒪.1.obj (op V))) ⥤
          DerivedCategory (ModuleCat (𝒪.1.obj (op U))))
    (comparison :
      ∀ {U V : C} (f : U ⟶ V),
        RGamma V ⋙ derivedRestrict f ⟶ RGamma U)
    (M :
      QC 𝒪.1 RGamma derivedRestrict comparison)
    (b : ℤ)
    (hvanish :
      ∀ U : C, ∀ i : ℤ, b < i →
        Limits.IsZero
          ((DerivedCategory.homologyFunctor (ModuleCat (𝒪.1.obj (op U))) i).obj
            ((RGamma U).obj M.obj))) :
    (show SheafOfModules (ringSheaf (⊥ : GrothendieckTopology C) 𝒪) from
      (DerivedCategory.homologyFunctor (moduleOnCategory 𝒪) b).obj M.obj).IsQuasicoherent := sorry

end CategoryTheory.ModulesOnCategory

/-! ### Lemma_21_43_4 (from Chap21) -/
noncomputable section

open CategoryTheory Opposite
open CategoryTheory.ObjectProperty

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace CategoryTheory.ModulesOnCategory

section

variable {C : Type u} [Category C]
variable {D : Type v} [Category D]
variable (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u})
variable (RGamma : ∀ U : C, D ⥤ DerivedCategory (ModuleCat (𝒪.obj (op U))))
variable
  (derivedRestrict :
    ∀ {U V : C},
      (U ⟶ V) →
      DerivedCategory (ModuleCat (𝒪.obj (op V))) ⥤
        DerivedCategory (ModuleCat (𝒪.obj (op U))))
variable
  (comparison :
    ∀ {U V : C} (f : U ⟶ V),
      RGamma V ⋙ derivedRestrict f ⟶ RGamma U)
variable (X : C)

/-- The derived category `D(\mathcal O(X))` of modules over the ring of sections at the chosen
object `X`. -/
abbrev terminalSectionsDerived :=
  DerivedCategory (ModuleCat (𝒪.obj (op X)))

/-- The restriction of the derived pushforward `Rf_*` for the obvious morphism
`(\mathcal C,\mathcal O) \to (pt,\mathcal O(X))` to the quasi-coherent full subcategory. In this
formalization it is the evaluation functor `R\Gamma(X,-)` on objects satisfying the defining
comparison isomorphisms. -/
abbrev rightDerivedPushforwardFromQC :
    QC 𝒪 RGamma derivedRestrict comparison ⥤ terminalSectionsDerived 𝒪 X :=
  (isQuasiCoherent 𝒪 RGamma derivedRestrict comparison).ι ⋙ RGamma X

/-- The restriction of a candidate derived pullback `Lf^* : D(\mathcal O(X)) \to D(\mathcal O)`
to the quasi-coherent full subcategory, assuming its essential image is quasi-coherent. -/
abbrev leftDerivedPullbackToQC
    (Lf : terminalSectionsDerived 𝒪 X ⥤ D)
    (hLf_mem : ∀ K : terminalSectionsDerived 𝒪 X,
      isQuasiCoherent 𝒪 RGamma derivedRestrict comparison ((Lf).obj K)) :
    terminalSectionsDerived 𝒪 X ⥤ QC 𝒪 RGamma derivedRestrict comparison :=
  ObjectProperty.lift
    (isQuasiCoherent 𝒪 RGamma derivedRestrict comparison)
    Lf
    hLf_mem

-- Proof sketch: for the terminal object `X`, identify `Rf_*` with `R\Gamma(X,-)`, restrict it to
-- `QC(\mathcal O)`, and restrict `Lf^*` along the defining object property. The given unit and
-- counit isomorphism hypotheses are exactly the data needed to show that the restricted `Lf^*`
-- is an equivalence with quasi-inverse the restricted `Rf_*`.
/-- Lemma 21.43.4: if `X` is a final object of `\mathcal C`, set `R = \mathcal O(X)` and let
`f : (\mathcal C,\mathcal O) \to (pt,R)` be the obvious morphism of ringed sites. Then
`QC(\mathcal O)` is equivalent to `D(R)`, with quasi-inverse functors given by the derived
pullback `Lf^*` and the derived pushforward `Rf_* = R\Gamma(X,-)`. -/
theorem leftDerivedPullbackToQC_isEquivalence
    (hX : Limits.IsTerminal X)
    (Lf : terminalSectionsDerived 𝒪 X ⥤ D)
    (hLf_mem : ∀ K : terminalSectionsDerived 𝒪 X,
      isQuasiCoherent 𝒪 RGamma derivedRestrict comparison ((Lf).obj K))
    (adj : Lf ⊣ RGamma X)
    (hunit : ∀ K : terminalSectionsDerived 𝒪 X, IsIso (adj.unit.app K))
    (hcounit : ∀ K : QC 𝒪 RGamma derivedRestrict comparison,
      IsIso (adj.counit.app K.obj)) :
    Functor.IsEquivalence
      (leftDerivedPullbackToQC 𝒪 RGamma derivedRestrict comparison X Lf hLf_mem) := sorry

end

end CategoryTheory.ModulesOnCategory

/-! ### Lemma_21_43_5 (from Chap21) -/
noncomputable section

open CategoryTheory
open CategoryTheory.ObjectProperty

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace CategoryTheory.ModulesOnCategory

section

variable {D : Type v} [Category D]
variable (QC : ObjectProperty D)
variable {DU : Type u} [Category DU]

/-- Lemma 21.43.5: for a fixed localized site over `U`, if `K` is quasi-coherent and the counit
identifies `K|_U` with `Lf^*(R\Gamma(U, K))`, then morphisms `K|_U ⟶ M|_U` are canonically
equivalent to morphisms `R\Gamma(U, K) ⟶ R\Gamma(U, M)` via the adjunction `Lf ⊣ R\Gamma(U,-)`. -/
noncomputable abbrev quasiCoherent_homEquiv_sections
    (RGammaU : D ⥤ DU)
    (Lf : DU ⥤ D)
    (adj : Lf ⊣ RGammaU)
    (K : QC.FullSubcategory)
    (M : D)
    [IsIso (adj.counit.app K.obj)] :
    (K.obj ⟶ M) ≃ (RGammaU.obj K.obj ⟶ RGammaU.obj M) :=
  (Iso.homCongr (asIso (adj.counit.app K.obj)).symm (Iso.refl M)).trans
    (adj.homEquiv (RGammaU.obj K.obj) M)

-- Proof sketch: use the counit isomorphism to replace `K` by `Lf.obj (RΓ(U,K))`, then apply the
-- adjunction Hom-set equivalence for `Lf ⊣ RΓ(U,-)`.
/-- The Hom-set equivalence of `quasiCoherent_homEquiv_sections` is the composite of the counit
comparison isomorphism with `Adjunction.homEquiv`. -/
theorem quasiCoherent_homEquiv_sections_def
    (RGammaU : D ⥤ DU)
    (Lf : DU ⥤ D)
    (adj : Lf ⊣ RGammaU)
    (K : QC.FullSubcategory)
    (M : D)
    [IsIso (adj.counit.app K.obj)] :
    quasiCoherent_homEquiv_sections QC RGammaU Lf adj K M =
      (Iso.homCongr (asIso (adj.counit.app K.obj)).symm (Iso.refl M)).trans
        (adj.homEquiv (RGammaU.obj K.obj) M) := sorry

end

end CategoryTheory.ModulesOnCategory

/-! ### Lemma_21_43_6 (from Chap21) -/
open CategoryTheory Opposite

universe u v

namespace CategoryTheory.ModulesOnCategory

/- Domain-style sampling for Lemma 21.43.6:
- primary domain: size bounds for cochain complexes of presheaves of modules and mono-presented
  subcomplex inclusions;
- sampled owner declarations:
  `CochainComplex`,
  `PresheafOfModules`,
  `Subobject`;
- best owner abstraction: the canonical subobject `G : Subobject F` of the ambient complex
  `F : CochainComplex (PresheafOfModules 𝒪) ℤ`, with the inclusion map recovered as `G.arrow`;
- primitive data: the ambient complex `F`, the chosen seed family `Ω`, the candidate subcomplex
  `G : Subobject F`, and the chosen seed family `Ω`;
- derived API: the section-cardinality measures and the property that `ι` contains the chosen
  seeds and satisfies the uniform cardinal bound.

Source/core/bridge triage:
- `source-facing`: a bounded subcomplex containing the designated seed sections;
- `core/canonical`: `Subobject F`;
- `bridge/view`: the cardinal-valued size functions
  `CochainComplex.sectionsCardinal` and `CochainComplex.seedSectionsCardinal`, together with the
  inclusion `G.arrow : (G : ModComplex) ⟶ F`. -/

section

variable {C : Type u} [Category.{v} C]
variable (𝒪 : Cᵒᵖ ⥤ RingCat.{u})

local notation "ModComplex" => CochainComplex (PresheafOfModules 𝒪) ℤ

namespace CochainComplex

/-- The total cardinality of the sections occurring in a cochain complex of presheaves of
`\mathcal O`-modules. -/
def sectionsCardinal (F : ModComplex) : Cardinal :=
  Cardinal.mk (Σ i : ℤ, Σ U : C, (F.X i).obj (op U))

/-- The cardinality of a chosen family of seed sections in a cochain complex of presheaves of
`\mathcal O`-modules. -/
def seedSectionsCardinal
    (F : ModComplex)
    (Ω : ∀ i : ℤ, ∀ U : C, Set ((F.X i).obj (op U))) : Cardinal :=
  Cardinal.mk (Σ i : ℤ, Σ U : C, {x : (F.X i).obj (op U) // x ∈ Ω i U})

end CochainComplex

open CategoryTheory.ModulesOnCategory.CochainComplex

-- Proof sketch: choose a cardinal bound depending only on the category `C` and the presheaf of
-- rings `𝒪`. For each complex `F` and family of seed sections `Ω`, generate the smallest
-- objectwise `\mathcal O(U)`-submodules stable under restrictions and differentials that contain
-- all seeds, and assemble them into a subcomplex `H ⟶ F`. The standard closure construction gives
-- the required cardinal estimate.
/-- Lemma 21.43.6: for a category `C` with a presheaf of rings `\mathcal O`, there exists a
cardinal `κ` such that every cochain complex `\mathcal F^\bullet` of presheaves of
`\mathcal O`-modules, together with chosen subsets `Ω^i_U ⊆ \mathcal F^i(U)`, admits a subcomplex
`\mathcal H^\bullet ⊆ \mathcal F^\bullet` whose image contains each `Ω^i_U` and whose total
objectwise cardinality is bounded by `max(κ, |\bigcup Ω^i_U|)`. Here the subcomplex is encoded as
a canonical subobject `G : Subobject F` with inclusion `G.arrow : (G : ModComplex) ⟶ F`. -/
theorem exists_bounded_subcomplex_containing_section_subsets :
    ∃ κ : Cardinal,
      ∀ (F : ModComplex) (Ω : ∀ i : ℤ, ∀ U : C, Set ((F.X i).obj (op U))),
        ∃ G : Subobject F,
          (∀ i : ℤ, ∀ U : C, Ω i U ⊆ Set.range ((G.arrow.f i).app (op U))) ∧
            sectionsCardinal 𝒪 (G : ModComplex) ≤ max κ (seedSectionsCardinal 𝒪 F Ω) := sorry

end

end CategoryTheory.ModulesOnCategory

/-! ### Lemma_21_43_7 (from Chap21) -/
noncomputable section

open CategoryTheory Opposite

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace CategoryTheory.ModulesOnCategory

section

variable {C : Type u} [Category.{v} C]
variable (𝒪 : Cᵒᵖ ⥤ RingCat.{u})

local notation "ModComplex" => CochainComplex (PresheafOfModules 𝒪) ℤ
local notation "DModO" => DerivedCategory (PresheafOfModules 𝒪)

open _root_.CategoryTheory.ModulesOnCategory.CochainComplex

/-- The size `|K|` of an object `K ∈ D(\mathcal O)` is the least cardinal bound among all
cochain complexes of `\mathcal O`-modules representing `K`, measured by the total cardinality of
their objectwise sections. -/
def derivedObjectCardinal
    (K : DModO) : Cardinal :=
  sInf {κ : Cardinal |
    ∃ (F : ModComplex) (_e : DerivedCategory.Q.obj F ≅ K),
      sectionsCardinal 𝒪 F ≤ κ}

-- Proof sketch: the representing complex `F` itself contributes an element of the set of
-- admissible cardinal bounds defining `derivedObjectCardinal 𝒪 K`, so the infimum is bounded
-- above by the cardinal of sections of `F`.
/-- Any chosen complex representing `K` bounds the canonical cardinal `|K|` from above. -/
theorem derivedObjectCardinal_le_of_representation
    (K : DModO)
    (F : ModComplex)
    (e : DerivedCategory.Q.obj F ≅ K) :
    derivedObjectCardinal 𝒪 K ≤ sectionsCardinal 𝒪 F := sorry

/-- A monomorphism `ι : \mathcal H^\bullet \to \mathcal F^\bullet` exhibits `\mathcal H^\bullet`
as a subcomplex of `\mathcal F^\bullet` that becomes isomorphic to `\mathcal F^\bullet` in
`D(\mathcal O)` and whose total section cardinality is bounded by `max(\kappa, |K|)`. When
`\mathcal F^\bullet` represents `K`, this says that `\mathcal H^\bullet` also represents `K`. -/
class IsBoundedRepresentativeSubcomplex
    (κ : Cardinal)
    (K : DModO)
    (F H : ModComplex)
    (ι : H ⟶ F) : Prop where
  mono : Mono ι
  quasiIso : IsIso (DerivedCategory.Q.map ι)
  cardinal_bound :
    sectionsCardinal 𝒪 H ≤ max κ (derivedObjectCardinal 𝒪 K)

-- Proof sketch: start from Lemma `21.43.6` to choose a small subcomplex surjecting onto every
-- cohomology sheaf of `F`. Then enlarge it inductively, still using Lemma `21.43.6`, so that at
-- each stage the kernel of the map on cohomology to `F` stabilizes. The union of this countable
-- chain is a subcomplex whose inclusion is a quasi-isomorphism, and cardinal arithmetic keeps its
-- total size bounded by `max(\kappa, |K|)`.
/-- Lemma 21.43.7: there exists a cardinal `\kappa` such that, whenever a cochain complex
`\mathcal F^\bullet` of `\mathcal O`-modules represents an object `K` of `D(\mathcal O)`, there
is a subcomplex `\mathcal H^\bullet \subset \mathcal F^\bullet` whose inclusion becomes an
isomorphism in `D(\mathcal O)` and whose total section cardinality is bounded by
`max(\kappa, |K|)`. Equivalently, `\mathcal H^\bullet` is a bounded-size subcomplex still
representing `K`. -/
theorem exists_cardinal_for_bounded_representative_subcomplexes :
    ∃ κ : Cardinal,
      ∀ (K : DModO)
        (F : ModComplex) (_e : DerivedCategory.Q.obj F ≅ K),
        ∃ (H : ModComplex) (ι : H ⟶ F),
          IsBoundedRepresentativeSubcomplex 𝒪 κ K F H ι := sorry

end

end CategoryTheory.ModulesOnCategory

/-! ### Lemma_21_43_8 (from Chap21) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open Opposite

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace CategoryTheory.ModulesOnCategory

section

variable {C : Type u} [Category.{v} C]
variable (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u})
variable
  (RGamma :
    ∀ U : C,
      DerivedCategory (PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)) ⥤
        DerivedCategory (ModuleCat (𝒪.obj (op U))))
variable
  (derivedRestrict :
    ∀ {U V : C},
      (U ⟶ V) →
        DerivedCategory (ModuleCat (𝒪.obj (op V))) ⥤
          DerivedCategory (ModuleCat (𝒪.obj (op U))))
variable
  (comparison :
    ∀ {U V : C} (f : U ⟶ V),
      RGamma V ⋙ derivedRestrict f ⟶ RGamma U)

local notation "Ring𝒪" => 𝒪 ⋙ forget₂ CommRingCat RingCat
local notation "DModO" => DerivedCategory (PresheafOfModules Ring𝒪)

local notation "QCoh" => QC 𝒪 RGamma derivedRestrict comparison

/-- A cardinal `κ` controls small nonzero sources in `QC(\mathcal O)` and countable direct-sum
factorizations from `κ`-bounded objects. -/
class IsBoundForSmallSourcesAndCountableCoproductFactorizations
    (κ : Cardinal) : Prop where
  /-- Every nonzero quasi-coherent object receives a nonzero map from a `κ`-bounded
  quasi-coherent object. -/
  nonzero_morphism_from_bounded_object :
    ∀ (K : QCoh), ¬ IsZero K →
      ∃ (E : QCoh) (f : E ⟶ K),
        f ≠ 0 ∧ derivedObjectCardinal 𝒪 E.obj ≤ κ
  /-- Every map from a `κ`-bounded quasi-coherent object into a countable direct sum factors
  through a countable direct sum of `κ`-bounded source objects. -/
  countable_coproduct_factorization :
    ∀ (E : QCoh) (K : ℕ → QCoh) [HasCoproduct K] (α : E ⟶ ∐ K),
      derivedObjectCardinal 𝒪 E.obj ≤ κ →
        ∃ (E' : ℕ → QCoh) (_hE' : HasCoproduct E')
          (φ : ∀ n : ℕ, E' n ⟶ K n) (β : E ⟶ ∐ E'),
          (∀ n : ℕ, derivedObjectCardinal 𝒪 (E' n).obj ≤ κ) ∧
            α = β ≫ Limits.Sigma.desc (fun n : ℕ ↦ φ n ≫ Limits.Sigma.ι K n)

-- Proof sketch: choose `κ` dominating the bounds from Lemmas `21.43.6`, `21.43.7`, and
-- `15.103.5`. For a nonzero `K`, represent a nonzero cohomology class by a small image subcomplex
-- and enlarge it using the quasi-coherent closure construction to obtain a nonzero bounded source.
-- For a map into a countable coproduct, represent it on complexes, factor each component through a
-- bounded quasi-coherent subcomplex, and reassemble these componentwise factorizations into a map
-- through the coproduct of the bounded sources.
/-- Lemma 21.43.8: there exists a cardinal `\kappa` such that every nonzero object of
`QC(\mathcal O)` receives a nonzero morphism from a `\kappa`-bounded object, and every morphism
from a `\kappa`-bounded object into a countable direct sum factors through a countable direct sum
of `\kappa`-bounded source objects. -/
theorem exists_cardinal_for_small_sources_and_countable_coproduct_factorizations :
    ∃ κ : Cardinal,
      IsBoundForSmallSourcesAndCountableCoproductFactorizations
        𝒪 RGamma derivedRestrict comparison κ := sorry

end

end CategoryTheory.ModulesOnCategory

/-! ### Proposition_21_43_9 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open Opposite

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe w uC vC uD vD uD' vD'

namespace CategoryTheory.ModulesOnCategory

section

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
variable [∀ n : ℤ, (shiftFunctor D n).Additive]
variable [Pretriangulated D] [IsTriangulated D] [HasCoproducts.{uD} D]
variable (𝒪 : Cᵒᵖ ⥤ CommRingCat.{uC})
variable
  (RGamma : ∀ U : C, D ⥤ DerivedCategory (ModuleCat (𝒪.obj (op U))))
variable
  (derivedRestrict :
    ∀ {U V : C}, (U ⟶ V) →
      DerivedCategory (ModuleCat (𝒪.obj (op V))) ⥤
        DerivedCategory (ModuleCat (𝒪.obj (op U))))
variable
  (comparison :
    ∀ {U V : C} (f : U ⟶ V),
      RGamma V ⋙ derivedRestrict f ⟶ RGamma U)

local notation "QCP" => isQuasiCoherent 𝒪 RGamma derivedRestrict comparison
local notation "QCoh" => QC 𝒪 RGamma derivedRestrict comparison

-- Proof sketch: this is the strict-fullness assertion in the proposition. In the intended
-- site-theoretic situation it comes from the triangulated-object-property description of
-- `QC(\mathcal O)` and the fact that the defining comparison maps are invariant under
-- isomorphism.
/-- Proposition 21.43.9 (1): the quasi-coherent subcategory `QC(\mathcal O)` is strictly full,
equivalently the defining object property is closed under isomorphisms in `D(\mathcal O)`. -/
instance qc_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms QCP := sorry

-- Proof sketch: the proposition asserts that `QC(\mathcal O)` is saturated. In the intended
-- proof, one combines the triangulated description of `QC(\mathcal O)` with the closure under
-- retracts coming from the quasi-coherent cohomology criterion.
/-- Proposition 21.43.9 (2): the quasi-coherent subcategory `QC(\mathcal O)` is saturated, i.e.
stable under retracts in `D(\mathcal O)`. -/
instance qc_isStableUnderRetracts :
    ObjectProperty.IsStableUnderRetracts QCP := sorry

-- Proof sketch: the proposition identifies `QC(\mathcal O)` as a triangulated subcategory. In the
-- intended site-theoretic proof, this follows from the quasi-coherent cohomology characterization
-- and the weak-LinearRepresentations_Serre_1977 stability of quasi-coherent modules.
/-- Proposition 21.43.9 (3): the quasi-coherent subcategory `QC(\mathcal O)` is triangulated. -/
instance qc_isTriangulated :
    ObjectProperty.IsTriangulated QCP := sorry

-- Proof sketch: the proposition states that `QC(\mathcal O)` is preserved by arbitrary direct
-- sums. In the intended proof, one uses the quasi-coherent cohomology description together with
-- direct-sum closure of quasi-coherent modules and commutation of cohomology with coproducts.
/-- Proposition 21.43.9 (4): the quasi-coherent subcategory `QC(\mathcal O)` is closed under
arbitrary `ι`-indexed direct sums. -/
instance qc_isClosedUnderDirectSums (ι : Type w) :
    ObjectProperty.IsClosedUnderColimitsOfShape QCP (Discrete ι) := sorry

-- Proof sketch: apply Brown representability, in the form of Lemma `13.39.1`, to the Brown set
-- constructed in the preceding lemmas for `QC(\mathcal O)`.
/-- Proposition 21.43.9 (5): every contravariant cohomological functor on `QC(\mathcal O)` that
turns arbitrary direct sums into products is representable. -/
theorem qc_contravariantCohomologicalFunctor_isRepresentable
    (H : QCohᵒᵖ ⥤ AddCommGrpCat.{vD})
    (hH : H.rightOp.IsHomological)
    (hprod : ∀ J : Type uD, PreservesLimitsOfShape (Discrete J) H) :
    ∃ X : QCoh, Nonempty (preadditiveYoneda.obj X ≅ H) := sorry

section RightAdjoints

variable {D' : Type uD'} [Category.{vD'} D']
variable [HasZeroObject D'] [HasShift D' ℤ] [Preadditive D']
variable [∀ n : ℤ, (shiftFunctor D' n).Additive]
variable [Pretriangulated D'] [IsTriangulated D']

-- Proof sketch: use the Brown representability set for `QC(\mathcal O)` and apply Proposition
-- `13.39.2` to the exact coproduct-preserving functor `F`, then package the resulting right
-- adjoint together with its inherited shift compatibility and triangulated structure.
/-- Proposition 21.43.9 (6): every exact functor from `QC(\mathcal O)` to a triangulated category
that preserves arbitrary direct sums has an exact right adjoint. -/
theorem qc_exactFunctor_hasExactRightAdjoint
    (F : QCoh ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]
    [∀ J : Type uD, PreservesColimitsOfShape (Discrete J) F] :
    ∃ (G : D' ⥤ QCoh) (_ : G.CommShift ℤ),
      Nonempty (F ⊣ G) ∧ G.IsTriangulated := sorry

end RightAdjoints

-- Proof sketch: specialize the previous exact-right-adjoint statement to the inclusion functor
-- `QC(\mathcal O) ↪ D(\mathcal O)`, using the direct-sum closure of `QC(\mathcal O)` to see that
-- the inclusion preserves arbitrary direct sums.
/-- Proposition 21.43.9 (7): the inclusion functor `QC(\mathcal O) \to D(\mathcal O)` has an exact
right adjoint. -/
theorem qc_inclusion_hasExactRightAdjoint
    [∀ J : Type uD, PreservesColimitsOfShape (Discrete J) (ObjectProperty.ι QCP : QCoh ⥤ D)] :
    ∃ (G : D ⥤ QCoh) (_ : G.CommShift ℤ),
      Nonempty ((ObjectProperty.ι QCP : QCoh ⥤ D) ⊣ G) ∧ G.IsTriangulated := sorry

end

end CategoryTheory.ModulesOnCategory

/-! ### Lemma_21_43_10 (from Chap21) -/
noncomputable section

open CategoryTheory Opposite

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace CategoryTheory.ModulesOnCategory

section

variable {C : Type u} [Category C]
variable {C' : Type u} [Category C']
variable {D : Type v} [Category D]
variable {D' : Type v} [Category D']
variable (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u})
variable (𝒪' : C'ᵒᵖ ⥤ CommRingCat.{u})
variable (u : C' ⥤ C)
variable (RGamma : ∀ U : C, D ⥤ DerivedCategory (ModuleCat (𝒪.obj (op U))))
variable (RGamma' : ∀ U' : C', D' ⥤ DerivedCategory (ModuleCat (𝒪'.obj (op U'))))
variable
  (derivedRestrict :
    ∀ {U V : C},
      (U ⟶ V) →
      DerivedCategory (ModuleCat (𝒪.obj (op V))) ⥤
        DerivedCategory (ModuleCat (𝒪.obj (op U))))
variable
  (derivedRestrict' :
    ∀ {U' V' : C'},
      (U' ⟶ V') →
      DerivedCategory (ModuleCat (𝒪'.obj (op V'))) ⥤
        DerivedCategory (ModuleCat (𝒪'.obj (op U'))))
variable
  (comparison :
    ∀ {U V : C} (f : U ⟶ V),
      RGamma V ⋙ derivedRestrict f ⟶ RGamma U)
variable
  (comparison' :
    ∀ {U' V' : C'} (f' : U' ⟶ V'),
      RGamma' V' ⋙ derivedRestrict' f' ⟶ RGamma' U')
variable (leftDerivedPullback : D ⥤ D')

-- Proof sketch: for each arrow `f' : U' ⟶ V'`, the sectionwise base-change description of
-- `Lg^*` identifies the target comparison morphism for `leftDerivedPullback.obj K` with the
-- image of the source comparison morphism for `u.map f'`. Thus every isomorphism required by the
-- source `QC` condition transports to the corresponding isomorphism in the target.
/-- Lemma 21.43.10: if the comparison morphisms defining quasi-coherence on the target category
are obtained from those on the source category after applying the derived pullback `Lg^*`, then
`Lg^* : D(\mathcal O) ⥤ D(\mathcal O')` maps `QC(\mathcal O)` into `QC(\mathcal O')`. -/
theorem qc_le_inverseImage_leftDerivedPullback
    (hLg :
      ∀ {U' V' : C'} (f' : U' ⟶ V') {K : D},
        IsIso ((comparison (u.map f')).app K) →
          IsIso ((comparison' f').app (leftDerivedPullback.obj K))) :
    isQuasiCoherent 𝒪 RGamma derivedRestrict comparison ≤
      (isQuasiCoherent 𝒪' RGamma' derivedRestrict' comparison').inverseImage
        leftDerivedPullback := sorry

/-- The derived pullback functor `Lg^*` restricted to the full subcategories cut out by the
sectionwise derived base-change condition. -/
abbrev leftDerivedPullbackToDerivedBaseChangeQC
    (hLg :
      ∀ {U' V' : C'} (f' : U' ⟶ V') {K : D},
        IsIso ((comparison (u.map f')).app K) →
          IsIso ((comparison' f').app (leftDerivedPullback.obj K))) :
    QC 𝒪 RGamma derivedRestrict comparison ⥤
      QC 𝒪' RGamma' derivedRestrict' comparison' :=
  ObjectProperty.lift
    (isQuasiCoherent 𝒪' RGamma' derivedRestrict' comparison')
    ((isQuasiCoherent 𝒪 RGamma derivedRestrict comparison).ι ⋙ leftDerivedPullback)
    (fun K ↦
      (qc_le_inverseImage_leftDerivedPullback
        𝒪 𝒪' u RGamma RGamma' derivedRestrict derivedRestrict'
        comparison comparison' leftDerivedPullback hLg) K.obj K.property)

end

end CategoryTheory.ModulesOnCategory

/-! ### Lemma_21_43_11 (from Chap21) -/
open CategoryTheory
open Opposite
open ComplexShape

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.ModulesOnCategory

variable {C : Type u} [Category.{v} C]
variable (𝒪 : Sheaf (⊥ : GrothendieckTopology C) CommRingCat)
variable [((⊥ : GrothendieckTopology C)).HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [∀ U : C, ((⊥ : GrothendieckTopology C).over U).HasSheafCompose
  (forget₂ RingCat AddCommGrpCat)]
variable [∀ U : C, HasWeakSheafify ((⊥ : GrothendieckTopology C).over U) AddCommGrpCat]
variable [∀ U : C, ((⊥ : GrothendieckTopology C).over U).WEqualsLocallyBijective AddCommGrpCat]

local notation "Mod𝒪" => SheafOfModules (ringSheaf (⊥ : GrothendieckTopology C) 𝒪)
local notation "DMod𝒪" => DerivedCategory Mod𝒪
local notation "Qis𝒪" => HomotopyCategory.quasiIso Mod𝒪 (up ℤ)
local notation "QCoh" =>
  SheafOfModules.isQuasicoherent (ringSheaf (⊥ : GrothendieckTopology C) 𝒪)
local notation "DQCoh" => derivedCategoryCohomologyInProperty QCoh

private noncomputable abbrev chaoticRGamma
    [hAdditive : ∀ U : C,
      (SheafOfModules.evaluation (ringSheaf (⊥ : GrothendieckTopology C) 𝒪) (op U) :
        Mod𝒪 ⥤ ModuleCat (𝒪.1.obj (op U))).Additive]
    [hDerived : ∀ U : C,
      Functor.HasRightDerivedFunctor
        (mapHomotopyCategoryToDerived
          (SheafOfModules.evaluation (ringSheaf (⊥ : GrothendieckTopology C) 𝒪) (op U) :
            Mod𝒪 ⥤ ModuleCat (𝒪.1.obj (op U))))
        Qis𝒪] :
    ∀ U : C, DMod𝒪 ⥤ DerivedCategory (ModuleCat (𝒪.1.obj (op U))) :=
  fun U ↦
    let F : Mod𝒪 ⥤ ModuleCat (𝒪.1.obj (op U)) :=
      SheafOfModules.evaluation (ringSheaf (⊥ : GrothendieckTopology C) 𝒪) (op U)
    let _ : F.Additive := by simpa [F] using hAdditive U
    let _ : Functor.HasRightDerivedFunctor (mapHomotopyCategoryToDerived F) Qis𝒪 := by
      simpa [F] using hDerived U
    Functor.totalRightDerived
      (mapHomotopyCategoryToDerived F)
      (DerivedCategory.Qh : HomotopyCategory Mod𝒪 (up ℤ) ⥤ DerivedCategory Mod𝒪)
      Qis𝒪

private noncomputable abbrev chaoticDerivedRestrict :
    ∀ {U V : C}, (U ⟶ V) →
      DerivedCategory (ModuleCat (𝒪.1.obj (op V))) ⥤
        DerivedCategory (ModuleCat (𝒪.1.obj (op U))) :=
  fun {U V} f ↦
    let _ : Algebra (𝒪.1.obj (op V)) (𝒪.1.obj (op U)) :=
      RingHom.toAlgebra ((𝒪.1.map f.op).hom)
    derivedTensorWithAlgebra _ _

/- Domain-style sampling for Lemma 21.43.11:
- primary domain: derived categories of module sheaves on the chaotic site and the comparison
  between the Section `21.43` base-change condition and cohomologywise quasi-coherence;
- sampled owner declarations:
  `CategoryTheory.ModulesOnCategory.isQuasiCoherent`,
  `CategoryTheory.ModulesOnCategory.QC`,
  `SheafOfModules.isQuasicoherent_iff_tensor_sections_map_isIso`,
  `CategoryTheory.derivedCategoryCohomologyInProperty`;
- best owner abstraction:
  `source-facing`: this lemma is the bridge equating the Section `21.43` comparison property with
    the condition that every cohomology sheaf is quasi-coherent;
  `core/canonical`: `isQuasiCoherent` from Definition `21.43.1`, together with the Chapter 13
    cohomology-in-an-object-property owner specialized to `SheafOfModules.IsQuasicoherent`;
  `bridge/view`: the hypothesis `hcomparison`, which identifies the derived comparison map with
    the sectionwise tensor map from Lemma `18.24.3`;
- primitive data: the sheaf `𝒪`, the sections functors, the derived restriction functors, and the
  comparison natural transformation;
- derived API: the Section `21.43` owner property and the degreewise quasi-coherent conclusion, so
  the theorem surface should reuse the existing owners and inline the canonical
  evaluation/derived-functor constructions instead of naming one-off wrapper declarations. -/

-- Proof sketch: for each arrow `U \to V`, the comparison hypothesis identifies the derived
-- base-change isomorphism for `K` with the tensor-sections criterion of the cohomology sheaves
-- `H^n(K)`. Then the chaotic-topology characterization of quasi-coherence turns that objectwise
-- tensor criterion into quasi-coherence of every cohomology sheaf, and conversely.
/-- Lemma 21.43.11: for a category `\mathcal C` with the chaotic topology and a sheaf of rings
`\mathcal O`, once the source flat base-change comparison has been packaged into `hcomparison`,
an object of `D(\mathcal O)` lies in the Section `21.43` owner property exactly when all of its
cohomology sheaves are quasi-coherent. This is the objectwise form of the agreement
`QC(\mathcal O) = D_{\mathrm{QCoh}}(\mathcal O)`. -/
theorem qc_iff_derivedQuasiCoherent
    [hAdditive : ∀ U : C,
      (SheafOfModules.evaluation (ringSheaf (⊥ : GrothendieckTopology C) 𝒪) (op U) :
        Mod𝒪 ⥤ ModuleCat (𝒪.1.obj (op U))).Additive]
    [hDerived : ∀ U : C,
      Functor.HasRightDerivedFunctor
        (mapHomotopyCategoryToDerived
          (SheafOfModules.evaluation (ringSheaf (⊥ : GrothendieckTopology C) 𝒪) (op U) :
            Mod𝒪 ⥤ ModuleCat (𝒪.1.obj (op U))))
        Qis𝒪]
    :
    let RGamma :
        ∀ U : C,
          DMod𝒪 ⥤ DerivedCategory (ModuleCat (𝒪.1.obj (op U))) :=
      fun U ↦ chaoticRGamma 𝒪 U
    let derivedRestrict :
        ∀ {U V : C}, (U ⟶ V) →
          DerivedCategory (ModuleCat (𝒪.1.obj (op V))) ⥤
            DerivedCategory (ModuleCat (𝒪.1.obj (op U))) :=
      fun {U V} f ↦ chaoticDerivedRestrict 𝒪 f
    ∀ (comparison : ∀ {U V : C} (f : U ⟶ V), RGamma V ⋙ derivedRestrict f ⟶ RGamma U)
      (hcomparison :
        ∀ (K : DMod𝒪) ⦃U V : C⦄ (f : U ⟶ V),
          IsIso ((comparison f).app K) ↔
            ∀ n : ℤ,
              IsIso
                (SheafOfModules.chaoticTensorSectionsMap 𝒪
                  ((DerivedCategory.homologyFunctor Mod𝒪 n).obj K) f))
      (K : DMod𝒪),
      let RGamma' :
          ∀ U : C, DMod𝒪 ⥤ DerivedCategory (ModuleCat (𝒪.1.obj (op U))) :=
        fun U ↦ RGamma U
      let derivedRestrict' :
          ∀ {U V : C}, (U ⟶ V) →
            DerivedCategory (ModuleCat (𝒪.1.obj (op V))) ⥤
              DerivedCategory (ModuleCat (𝒪.1.obj (op U))) :=
        fun {U V} f ↦ derivedRestrict f
      let comparison' :
          ∀ {U V : C} (f : U ⟶ V), RGamma' V ⋙ derivedRestrict' f ⟶ RGamma' U :=
        fun {U V} f ↦ comparison f
      let QCP : ObjectProperty DMod𝒪 :=
        isQuasiCoherent 𝒪.1 RGamma' derivedRestrict'
          (fun {U V : C} (f : U ⟶ V) ↦ comparison' f)
      QCP K ↔ DQCoh K := by
  dsimp
  intro comparison hcomparison K
  change
      (∀ ⦃U V : C⦄ (f : U ⟶ V), IsIso ((comparison f).app K)) ↔
        ∀ n : ℤ, QCoh ((DerivedCategory.homologyFunctor Mod𝒪 n).obj K)
  constructor
  · intro h n
    rw [SheafOfModules.isQuasicoherent_iff_tensor_sections_map_isIso 𝒪]
    intro U V f
    exact (hcomparison K f).mp (h f) n
  · intro h U V f
    refine (hcomparison K f).mpr ?_
    intro n
    exact (SheafOfModules.isQuasicoherent_iff_tensor_sections_map_isIso 𝒪 _).mp (h n) f

end CategoryTheory.ModulesOnCategory

/-! ### Lemma_21_43_12 (from Chap21) -/
open CategoryTheory
open CategoryTheory.ObjectProperty
open Opposite

noncomputable section

universe u v w w'

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.ModulesOnCategory

variable {C : Type u} [Category.{v} C]
variable (𝒪 : Sheaf (⊥ : GrothendieckTopology C) CommRingCat)
variable [((⊥ : GrothendieckTopology C)).HasSheafCompose (forget₂ CommRingCat RingCat)]

/-- The `RingCat`-valued structure sheaf on a category, viewed through the chaotic topology. -/
abbrev chaoticRingSheaf :
    Sheaf (⊥ : GrothendieckTopology C) RingCat :=
  (sheafCompose (⊥ : GrothendieckTopology C) (forget₂ CommRingCat RingCat)).obj 𝒪

/-- The category `\mathrm{Mod}(\mathcal O)` of module sheaves on a category with the chaotic
topology. -/
abbrev moduleOnCategory :=
  SheafOfModules (chaoticRingSheaf 𝒪)

variable [Abelian (moduleOnCategory 𝒪)]
variable [HasDerivedCategory (moduleOnCategory 𝒪)]

variable
  (RGamma :
    ∀ U : C,
      DerivedCategory (moduleOnCategory 𝒪) ⥤
        DerivedCategory (ModuleCat (𝒪.1.obj (op U))))
  (derivedRestrict :
    ∀ {U V : C}, (U ⟶ V) →
      DerivedCategory (ModuleCat (𝒪.1.obj (op V))) ⥤
        DerivedCategory (ModuleCat (𝒪.1.obj (op U))))
  (comparison :
    ∀ {U V : C} (f : U ⟶ V),
      RGamma V ⋙ derivedRestrict f ⟶ RGamma U)

/-- The target-side object property in Lemma `21.43.12`: an object of `D(\mathcal C_\tau,
\mathcal O_\tau)` lies in the relevant full subcategory when its pushforward `Rε_*` belongs to
`QC(\mathcal O)`. -/
abbrev pushforwardQuasiCoherentProperty
    {Dτ : Type w} [Category Dτ]
    (rEpsilonPushforward : Dτ ⥤ DerivedCategory (moduleOnCategory 𝒪)) :
    ObjectProperty Dτ :=
  fun K ↦ isQuasiCoherent 𝒪.1 RGamma derivedRestrict comparison (rEpsilonPushforward.obj K)

-- Proof sketch: this is just the defining expansion of `pushforwardQuasiCoherentProperty`.
/-- Membership in the target subcategory of Lemma `21.43.12` means precisely that the pushed
forward object lies in `QC(\mathcal O)`. -/
theorem mem_pushforwardQuasiCoherentProperty_iff
    {Dτ : Type w} [Category Dτ]
    (rEpsilonPushforward : Dτ ⥤ DerivedCategory (moduleOnCategory 𝒪))
    (K : Dτ) :
    pushforwardQuasiCoherentProperty 𝒪 RGamma derivedRestrict comparison rEpsilonPushforward K ↔
      isQuasiCoherent 𝒪.1 RGamma derivedRestrict comparison (rEpsilonPushforward.obj K) := sorry

/-- The canonical restriction of `Rε_*` from the target full subcategory back to `QC(\mathcal O)`.
-/
abbrev restrictedPushforwardToQC
    {Dτ : Type w} [Category Dτ]
    (rEpsilonPushforward : Dτ ⥤ DerivedCategory (moduleOnCategory 𝒪)) :
    (pushforwardQuasiCoherentProperty 𝒪 RGamma derivedRestrict comparison
      rEpsilonPushforward).FullSubcategory ⥤
        QC 𝒪.1 RGamma derivedRestrict comparison :=
  ObjectProperty.lift
    (isQuasiCoherent 𝒪.1 RGamma derivedRestrict comparison)
    ((pushforwardQuasiCoherentProperty 𝒪 RGamma derivedRestrict comparison
      rEpsilonPushforward).ι ⋙ rEpsilonPushforward)
    (fun K ↦ K.property)

-- Proof sketch: `restrictedPushforwardToQC` is defined by lifting `Rε_*` through the full
-- subcategory cut out by the condition that `Rε_* K` is quasi-coherent.
/-- The restricted pushforward of Lemma `21.43.12` is the lift of `Rε_*` through the defining full
subcategory of objects whose pushforward lies in `QC(\mathcal O)`. -/
abbrev restrictedPushforwardToQC_comp_ι
    {Dτ : Type w} [Category Dτ]
    (rEpsilonPushforward : Dτ ⥤ DerivedCategory (moduleOnCategory 𝒪)) :
    restrictedPushforwardToQC 𝒪 RGamma derivedRestrict comparison rEpsilonPushforward ⋙
        (isQuasiCoherent 𝒪.1 RGamma derivedRestrict comparison).ι ≅
      (pushforwardQuasiCoherentProperty 𝒪 RGamma derivedRestrict comparison
        rEpsilonPushforward).ι ⋙
        rEpsilonPushforward :=
  (isQuasiCoherent 𝒪.1 RGamma derivedRestrict comparison).liftCompιIso
    ((pushforwardQuasiCoherentProperty 𝒪 RGamma derivedRestrict comparison
      rEpsilonPushforward).ι ⋙ rEpsilonPushforward)
    (fun K ↦ K.property)

-- Proof sketch: Section `21.27` provides the adjunction `ε^* ⊣ Rε_*` with `Rε_*` fully faithful,
-- so the counit identifies every object on the target side with one coming from `ε^*`. The
-- K-flat comparison hypothesis computes `Rε_*(ε^* M)` for `M ∈ QC(\mathcal O)` and gives the unit
-- isomorphism on `QC(\mathcal O)`, which upgrades the chosen restriction of `ε^*` and the
-- canonical restricted `Rε_*` to quasi-inverse equivalences.
/-- Lemma 21.43.12: let `ε : (\mathcal C_\tau, \mathcal O_\tau) \to
(\mathcal C_{\tau'}, \mathcal O_{\tau'})` be the topology-change morphism of Section `21.27`, and
assume `τ'` is the chaotic topology on `\mathcal C`. If for every `U ∈ \operatorname{Ob}(\mathcal
C)` and every chosen K-flat complex over `\mathcal O(U)` the comparison map from that complex to
the derived sections of its sheafified tensor with `\mathcal O_U` is a quasi-isomorphism, then the
restriction of `ε^*` to `QC(\mathcal O)` is an equivalence onto the full subcategory of
`D(\mathcal C_\tau, \mathcal O_\tau)` consisting of those `K` with `Rε_* K ∈ QC(\mathcal O)`. The
companion declaration `restrictedPushforwardToQC` is the intended quasi-inverse induced by
`Rε_*`. -/
theorem epsilonPullback_qc_isEquivalence_of_kFlatComparison
    {Dτ : Type w} [Category Dτ]
    (epsilonPullback : DerivedCategory (moduleOnCategory 𝒪) ⥤ Dτ)
    (rEpsilonPushforward : Dτ ⥤ DerivedCategory (moduleOnCategory 𝒪))
    (adj : epsilonPullback ⊣ rEpsilonPushforward)
    [rEpsilonPushforward.Full] [rEpsilonPushforward.Faithful]
    (epsilonPullbackQC :
      QC 𝒪.1 RGamma derivedRestrict comparison ⥤
        (pushforwardQuasiCoherentProperty 𝒪 RGamma derivedRestrict comparison
          rEpsilonPushforward).FullSubcategory)
    (hε :
      epsilonPullbackQC ⋙
          (pushforwardQuasiCoherentProperty 𝒪 RGamma derivedRestrict comparison
            rEpsilonPushforward).ι ≅
        (isQuasiCoherent 𝒪.1 RGamma derivedRestrict comparison).ι ⋙ epsilonPullback)
    {KFlatComplex : C → Type w'} [∀ U : C, Category (KFlatComplex U)]
    (derivedSections : ∀ U : C, KFlatComplex U ⥤ KFlatComplex U)
    (sectionComparison : ∀ U : C, 𝟭 (KFlatComplex U) ⟶ derivedSections U)
    (hKFlat : ∀ U : C, ∀ M : KFlatComplex U, IsIso ((sectionComparison U).app M)) :
    Functor.IsEquivalence epsilonPullbackQC := sorry

end CategoryTheory.ModulesOnCategory

/-! ### Lemma_21_43_13 (from Chap21) -/
noncomputable section

open CategoryTheory
open CategoryTheory.ObjectProperty

universe u v w w'

namespace CategoryTheory.ModulesOnCategory

section

variable {C : Type u} [Category.{v} C]
variable {D : C → Type w} [∀ U : C, Category (D U)]
variable {Dτ : C → Type w'} [∀ U : C, Category (Dτ U)]
variable {DU : C → Type w} [∀ U : C, Category (DU U)]

variable (QC : ∀ U : C, ObjectProperty (D U))
variable (RGamma : ∀ U : C, D U ⥤ DU U)
variable (Lf : ∀ U : C, DU U ⥤ D U)
variable (sectionsAdj : ∀ U : C, Lf U ⊣ RGamma U)
variable (epsilonPullback : ∀ U : C, D U ⥤ Dτ U)
variable (rEpsilonPushforward : ∀ U : C, Dτ U ⥤ D U)
variable (epsilonAdj : ∀ U : C, epsilonPullback U ⊣ rEpsilonPushforward U)
variable (RGammaTau : ∀ U : C, Dτ U ⥤ DU U)
variable (leray : ∀ U : C, RGammaTau U ≅ rEpsilonPushforward U ⋙ RGamma U)

/-- Lemma 21.43.13: for each object `U` of `\mathcal C`, if `K|_U` is quasi-coherent on the
localized chaotic site and `M|_U` is any object on the localized `τ`-site, then the local
adjunction `ε^* ⊣ Rε_*`, the quasi-coherent Hom computation of Lemma `21.43.5`, and the Leray
identification combine to identify morphisms `ε^*(K|_U) ⟶ M|_U` with morphisms
`R\Gamma(U, K) ⟶ R\Gamma(U, M)`. -/
noncomputable abbrev epsilonPullback_homEquiv_sections
    (U : C)
    (K : (QC U).FullSubcategory)
    (M : Dτ U)
    [IsIso ((sectionsAdj U).counit.app K.obj)] :
    ((epsilonPullback U).obj K.obj ⟶ M) ≃
      ((RGamma U).obj K.obj ⟶ (RGammaTau U).obj M) :=
  ((epsilonAdj U).homEquiv K.obj M).trans
    ((quasiCoherent_homEquiv_sections (QC U) (RGamma U) (Lf U) (sectionsAdj U) K
        ((rEpsilonPushforward U).obj M)).trans
      (Iso.homCongr (Iso.refl ((RGamma U).obj K.obj)) ((leray U).app M).symm))

-- Proof sketch: first apply the local adjunction `ε^* ⊣ Rε_*` to replace morphisms
-- `ε^*(K|_U) ⟶ M|_U` by morphisms `K|_U ⟶ Rε_* M|_U`. Then use Lemma `21.43.5` for the
-- quasi-coherent object `K|_U`, and finally transport the target along the Leray isomorphism
-- `R\Gamma(U, M) ≅ R\Gamma(U, Rε_* M)`.
/-- The equivalence `epsilonPullback_homEquiv_sections` is the composite of the local adjunction,
the quasi-coherent sections equivalence, and the Leray comparison isomorphism. -/
theorem epsilonPullback_homEquiv_sections_def
    (U : C)
    (K : (QC U).FullSubcategory)
    (M : Dτ U)
    [IsIso ((sectionsAdj U).counit.app K.obj)] :
    epsilonPullback_homEquiv_sections QC RGamma Lf sectionsAdj epsilonPullback
        rEpsilonPushforward epsilonAdj RGammaTau leray U K M =
      ((epsilonAdj U).homEquiv K.obj M).trans
        ((quasiCoherent_homEquiv_sections (QC U) (RGamma U) (Lf U) (sectionsAdj U) K
            ((rEpsilonPushforward U).obj M)).trans
          (Iso.homCongr (Iso.refl ((RGamma U).obj K.obj)) ((leray U).app M).symm)) := sorry

end

end CategoryTheory.ModulesOnCategory
