import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.CategoryTheory.Monoidal.Category
import StacksProject_2024.Chap12.Lemma_12_7_2
import StacksProject_2024.Chap13.Lemma_13_30_1
import StacksProject_2024.Chap13.Definition_13_31_1
import StacksProject_2024.Chap15.Lemma_15_58_1
import StacksProject_2024.Chap15.Definition_15_59_1
import StacksProject_2024.Chap18.RingedSiteModuleCategory
import StacksProject_2024.Chap21.«21_34_0_2»
import StacksProject_2024.Chap21.Lemma_21_34_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open CochainComplex.HomComplex.CohomologyClass

noncomputable section

universe u v

set_option checkBinderAnnotations false

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [Abelian (ringedSiteModuleCategory J 𝒪)]

private instance instPreadditiveMod : Preadditive (ringedSiteModuleCategory J 𝒪) :=
  Abelian.toPreadditive

variable [HasZeroObject (ringedSiteModuleCategory J 𝒪)]
variable [HasBinaryBiproducts (ringedSiteModuleCategory J 𝒪)]
variable [HasProducts (ringedSiteModuleCategory J 𝒪)]
variable [HasCountableCoproducts (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [SymmetricCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalClosed (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalPreadditive (ringedSiteModuleCategory J 𝒪)]
variable [(curriedTensor (ringedSiteModuleCategory J 𝒪)).Additive]
variable [∀ X : ringedSiteModuleCategory J 𝒪,
  ((curriedTensor (ringedSiteModuleCategory J 𝒪)).obj X).Additive]
variable [∀ G₁ G₂ : GradedObject ℤ (ringedSiteModuleCategory J 𝒪),
  GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (ringedSiteModuleCategory J 𝒪),
  GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (ringedSiteModuleCategory J 𝒪),
  GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ (ringedSiteModuleCategory J 𝒪),
  GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
variable [∀ X : ringedSiteModuleCategory J 𝒪,
  PreservesColimit (Functor.empty.{0} (ringedSiteModuleCategory J 𝒪))
    ((curriedTensor (ringedSiteModuleCategory J 𝒪)).obj X)]
variable [∀ X : ringedSiteModuleCategory J 𝒪,
  PreservesColimit (Functor.empty.{0} (ringedSiteModuleCategory J 𝒪))
    ((curriedTensor (ringedSiteModuleCategory J 𝒪)).flip.obj X)]

local notation "Mod" => ringedSiteModuleCategory J 𝒪
local notation "CpxO" => CochainComplex Mod ℤ
variable [monoidalClosedCpxO : MonoidalClosed CpxO]
local instance instClosedCpxO (A : CpxO) : Closed A := monoidalClosedCpxO.closed A
set_option quotPrecheck false in
local notation:20 A " ⟶[CpxO] " B:19 => (ihom A).obj B

/- The Chapter 15 owner names the canonical symmetric monoidal structure on `CpxO`; the graded
tensor and empty-colimit hypotheses above are the local assumptions that let typeclass inference
recover that owner and the corresponding closed structure on complexes. -/
recall cochainComplexSymmetricCategory

/- Domain-style sampling for Lemma 21.34.8:
- primary domain: K-injectivity of internal-Hom complexes of `𝒪`-module cochain
  complexes on a ringed site;
- sampled owner declarations:
  `(ihom A).obj B`,
  `MonoidalClosed.pre`,
  `CochainComplex.HomComplex.homologyAddEquiv`,
  `quasiIso_ringedSiteModuleComplexInternalHomMap_of_quasiIso_of_isKInjective`;
- best owner abstraction: the internal-Hom complex itself is already owned by the ambient closed
  monoidal structure on `CpxO`, so the public theorem should target the canonical owner
  `L ⟶[CpxO] I` instead of rebuilding a parallel complex by hand;
- primitive data: the K-flat source complex `L`, the K-injective target complex `I`, and the
  ambient closed monoidal structure on `CpxO`;
- derived API: the K-injectivity conclusion for the canonical internal-Hom complex.

Source/core/bridge triage:
- `source-facing`: Lemma 21.34.8;
- `core/canonical`: the complex internal-Hom owner `L ⟶[CpxO] I`;
- `bridge/view`: none. -/

-- `lean_leansearch` recall found no existing mathlib or local theorem for this exact ringed-site
-- specialization, so the source-facing declaration remains this Chapter 21 instance on the
-- canonical internal-Hom owner.

/-- Helper for Lemma 21.34.8: tensoring an acyclic test complex on the right by the fixed
K-flat complex `L` stays acyclic. -/
private theorem tensorRight_acyclic_of_isKFlat
    (L K : CpxO) (hL : L.IsKFlat) (hK : K.Acyclic) :
    ((MonoidalCategory.tensorRight L).obj K).Acyclic := by
  -- Proof comment: this is exactly the Chapter 15 K-flat acyclicity owner, rewritten through the
  -- ambient `tensorRight` notation.
  simpa using
    (CochainComplex.acyclic_tensorObj_of_isKFlat hL hK :
      (HomologicalComplex.tensorObj K L).Acyclic)

/-- Helper for Lemma 21.34.8: the tensor/internal-Hom adjunction carries homotopies on the
tensor side to homotopies on the internal-Hom side. -/
private theorem homotopy_homEquiv_of_tensorRightInternalHomAdjunction
    (L : CpxO)
    (adj : MonoidalCategory.tensorRight L ⊣ CategoryTheory.ihom L)
    {K I : CpxO} {f g : (MonoidalCategory.tensorRight L).obj K ⟶ I}
    (h : Homotopy f g) :
    Homotopy ((adj.homEquiv K I) f) ((adj.homEquiv K I) g) := by
  letI : (CategoryTheory.ihom L).Additive := adj.right_adjoint_additive
  -- Proof comment: map the tensor-side homotopy through the right adjoint and rewrite the
  -- resulting morphisms via the unit formula for `adj.homEquiv`.
  simpa [Adjunction.homEquiv_unit] using
    (((CategoryTheory.ihom L).mapHomotopy h).compLeft (adj.unit.app K))

/-- Lemma 21.34.8: for a ringed site `(𝒞, 𝒪)`, a K-flat complex `𝓛` of `𝒪`-modules, and a
K-injective complex `𝓘` of `𝒪`-modules, the canonical internal-Hom complex from `𝓛` to `𝓘`
is K-injective. -/
private theorem ringedSiteModuleComplexInternalHom_isKInjective_aux
    (L I : CpxO) (hL : L.IsKFlat) [I.IsKInjective] :
    (L ⟶[CpxO] I).IsKInjective := by
  let adj : MonoidalCategory.tensorRight L ⊣ CategoryTheory.ihom L :=
    CategoryTheory.ihom.adjunction L
  refine ⟨fun {K} f hK ↦ ?_⟩
  let f' : (MonoidalCategory.tensorRight L).obj K ⟶ I :=
    ((adj.homEquiv K I).symm f)
  -- Proof comment: K-flatness of `L` turns the acyclic test complex `K` into an acyclic tensor
  -- test complex on which K-injectivity of `I` applies.
  have hTensor : ((MonoidalCategory.tensorRight L).obj K).Acyclic :=
    tensorRight_acyclic_of_isKFlat L K hL hK
  refine ⟨?_⟩
  -- Proof comment: transport the null-homotopy of the curried tensor-side map back across the
  -- tensor/internal-Hom adjunction and rewrite the transposed map to `f`.
  simpa [f'] using
    homotopy_homEquiv_of_tensorRightInternalHomAdjunction L adj
      (IsKInjective.homotopyZero f' hTensor)

/-- Lemma 21.34.8: for a ringed site `(𝒞, 𝒪)`, a K-flat complex `𝓛` of `𝒪`-modules, and a
K-injective complex `𝓘` of `𝒪`-modules, the canonical internal-Hom complex from `𝓛` to `𝓘`
is K-injective. -/
@[stacks 0A96]
instance ringedSiteModuleComplexInternalHom_isKInjective
    (L I : CpxO) (hL : L.IsKFlat) [I.IsKInjective] :
    (L ⟶[CpxO] I).IsKInjective :=
  ringedSiteModuleComplexInternalHom_isKInjective_aux L I hL

end

end SheafOfModules.RingedSite
