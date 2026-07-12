import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import StacksProject_2024.Chap18.RingedSiteModuleCategory

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

/- Domain-style sampling for Lemma 21.34.7:
- primary domain: quasi-isomorphism invariance of internal-Hom complexes of `𝒪`-module
  cochain complexes on a ringed site;
- sampled owner declarations:
  `(ihom A).obj B`,
  `MonoidalClosed.pre`,
  `(ihom L).map`,
  `CochainComplex.IsKInjective.Qh_map_bijective`;
- best owner abstraction: the induced map in this lemma is the canonical contravariant/covariant
  functoriality of the ambient closed structure on `CochainComplex ModO ℤ`;
- primitive data: the two comparison morphisms `f` and `g`;
- derived API: the quasi-isomorphism statement below for the canonical internal-Hom comparison
  morphism, with K-injectivity carried by the canonical owner class
  `CochainComplex.IsKInjective` and the ambient homology infrastructure kept out of the public
  binder list.

Source/core/bridge triage:
- `source-facing`: Lemma 21.34.7;
- `core/canonical`: `MonoidalClosed.pre`, `(ihom L).map`, and
  `CochainComplex.IsKInjective.Qh_map_bijective`;
- `bridge/view`: none; the source comparison map is already the canonical composite in the
  ambient closed-monoidal structure. -/

-- Proof sketch: apply Lemma `21.34.6` on every localization `(C / U, 𝒪_U)` to
-- identify the degree-zero cohomology sheaf of each internal-Hom complex with the presheaf
-- `U ↦ Hom_{D(𝒪_U)}(L|_U, I|_U)`. The quasi-isomorphisms `f` and `g` identify the source
-- and target representatives of the same derived objects, so this map induces isomorphisms on all
-- cohomology sheaves. Therefore the canonical map of internal-Hom complexes is a quasi-isomorphism.

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [MonoidalCategory (CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ)]
variable [MonoidalClosed (CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ)]
local notation "ModO" => ringedSiteModuleCategory J 𝒪
local notation "CpxO" => CochainComplex ModO ℤ
set_option quotPrecheck false in
local notation:20 A " ⟶[CpxO] " B:19 => (ihom A).obj B

/-- The canonical internal-Hom morphism induced contravariantly by `f` on the source complex and
covariantly by `g` on the target complex. -/
noncomputable def ringedSiteModuleComplexInternalHomMap
    {L' L I' I : CpxO} (f : L' ⟶ L) (g : I' ⟶ I) :
    (L ⟶[CpxO] I') ⟶ (L' ⟶[CpxO] I) :=
  (ihom L).map g ≫ (MonoidalClosed.pre f).app I

@[simp] theorem ringedSiteModuleComplexInternalHomMap_def
    {L' L I' I : CpxO} (f : L' ⟶ L) (g : I' ⟶ I) :
    ringedSiteModuleComplexInternalHomMap f g =
      (ihom L).map g ≫ (MonoidalClosed.pre f).app I :=
  rfl

end

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [CategoryWithHomology (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalCategory (CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ)]
variable [MonoidalClosed (CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ)]
local notation "ModO" => ringedSiteModuleCategory J 𝒪
local notation "CpxO" => CochainComplex ModO ℤ

/-- Lemma 21.34.7: for a ringed site `(𝒞, 𝒪)`, if `I' ⟶ I` is a quasi-isomorphism of K-injective
cochain complexes of `𝒪`-modules and `L' ⟶ L` is a quasi-isomorphism of cochain complexes of
`𝒪`-modules, then the canonical induced morphism from the internal-Hom complex of `L` into `I'`
to the internal-Hom complex of `L'` into `I` is a quasi-isomorphism. -/
@[stacks 0A95]
theorem quasiIso_ringedSiteModuleComplexInternalHomMap_of_quasiIso_of_isKInjective
    {L' L I' I : CpxO}
    [CochainComplex.IsKInjective I'] [CochainComplex.IsKInjective I]
    (f : L' ⟶ L) (g : I' ⟶ I) (hfi : QuasiIso f) (hgi : QuasiIso g) :
    QuasiIso (ringedSiteModuleComplexInternalHomMap f g) := by
  sorry

end

end SheafOfModules.RingedSite
