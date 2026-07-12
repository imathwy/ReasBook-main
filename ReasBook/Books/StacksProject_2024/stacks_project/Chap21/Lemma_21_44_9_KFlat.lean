import Mathlib
import StacksProject_2024.Chap15.Definition_15_59_1
import StacksProject_2024.Chap21.Definition_21_44_1
import StacksProject_2024.Chap21.Lemma_21_34_1
import StacksProject_2024.Chap21.Lemma_21_34_8

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open ComplexShape

noncomputable section

universe u v

set_option checkBinderAnnotations false

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
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
variable [∀ (K L : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ),
  CochainComplex.HasMapBifunctor K L (curriedTensor (ringedSiteModuleCategory J 𝒪))]
variable [CategoryWithHomology (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalCategory (CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ)]
variable [MonoidalClosed (CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ)]

local notation "Mod" => ringedSiteModuleCategory J 𝒪
local notation "CpxO" => CochainComplex Mod ℤ
local notation "Site" => RingedSite.ofCommRingSheaf J 𝒪
set_option quotPrecheck false in
local notation:20 A " ⟶[CpxO] " B:19 => (ihom A).obj B

/- Domain-style sampling for the K-flatness companion to Lemma 21.44.9:
- primary domain: K-flatness of internal-Hom complexes of `\mathcal O`-modules on a ringed site;
- inspected owner declarations:
  `CochainComplex.IsStrictlyPerfect`,
  `CochainComplex.IsKFlat`,
  `(ihom E).obj F`,
  `CochainComplex.tensorObj_isKFlat_of_isKFlat`;
- best owner abstraction: the canonical internal-Hom owner `(ihom E).obj F`, with
  the strict-perfect source owner `CochainComplex.IsStrictlyPerfect` and
  `CochainComplex.IsKFlat` supplying the target hypothesis;
- primitive data: the complexes `E` and `F`, the owner hypothesis
  `CochainComplex.IsStrictlyPerfect E`, and the K-flatness hypothesis on `F`;
- derived API: the K-flatness conclusion for the canonical internal-Hom complex.

Source/core/bridge triage:
- `source-facing`: the K-flatness consequence used in Chapter 20 for complexes of
  `\mathcal O_X`-modules;
- `core/canonical`: `(ihom E).obj F` together with
  the strict-perfect source owner `CochainComplex.IsStrictlyPerfect` and
  `CochainComplex.IsKFlat`;
- `bridge/view`: the later specialization from the opens site of a ringed space to
  `AlgebraicGeometry.RingedSpace`.

This file keeps the theorem at the ringed-site owner layer so downstream ringed-space files can
recall it directly instead of speaking about a parallel local internal-Hom construction. -/

-- Proof sketch: a strictly perfect complex is obtained from finitely many shifts of finite free
-- modules by iterated cones and retracts. Internal Hom from such a source into a K-flat target is
-- therefore assembled from K-flat complexes using the standard closure properties of K-flatness.
/-- If `E` is strictly perfect and `F` is K-flat, then the canonical internal-Hom complex
`\mathcal H\!\mathit{om}^\bullet(E, F)` on the ringed site is K-flat. -/
theorem ringedSiteModuleComplexInternalHom_isKFlat_of_isStrictlyPerfect
    (E F : CpxO)
    (hE : CochainComplex.IsStrictlyPerfect E)
    (hF : F.IsKFlat) :
    (E ⟶[CpxO] F).IsKFlat := by
  sorry

end

end SheafOfModules.RingedSite
