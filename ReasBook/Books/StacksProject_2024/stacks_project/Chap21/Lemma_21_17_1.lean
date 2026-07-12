import Mathlib.Tactic.Recall
import StacksProject_2024.Chap13.Remark_13_10_9
import StacksProject_2024.Chap18.RingedSiteModuleCategory

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits ComplexShape MonoidalCategory

noncomputable section

universe u

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable (𝒪 : Sheaf J CommRingCat.{u})

variable [Preadditive (ringedSiteModuleCategory J 𝒪)]
variable [Abelian (ringedSiteModuleCategory J 𝒪)]
variable [HasZeroObject (ringedSiteModuleCategory J 𝒪)]
variable [HasBinaryBiproducts (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [(curriedTensor (ringedSiteModuleCategory J 𝒪)).Additive]
variable [∀ F : ringedSiteModuleCategory J 𝒪,
  ((curriedTensor (ringedSiteModuleCategory J 𝒪)).obj F).Additive]
variable [∀ (F G : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ),
  CochainComplex.HasMapBifunctor F G (curriedTensor (ringedSiteModuleCategory J 𝒪))]

local notation "Mod" => ringedSiteModuleCategory J 𝒪

variable (𝒢 : CochainComplex Mod ℤ)

/- Domain-style sampling for Lemma 21.17.1:
- primary domain: fixed-factor tensor-totalization functors on homotopy categories of cochain
  complexes in the ringed-site module category;
- sampled owner declarations:
  `Functor.map₂CochainComplex`,
  `Functor.mapHomotopyCategory`,
  `Functor.CommShift`,
  `Functor.IsTriangulated`;
- best owner abstraction: the Chapter 13 owners
  `((curriedTensor Mod).map₂CochainComplex.obj 𝒢).mapHomotopyCategory (up ℤ)` and
  `(((curriedTensor Mod).map₂CochainComplex).flip.obj 𝒢).mapHomotopyCategory (up ℤ)`;
- primitive vs derived:
  the primitive data are the ringed-site tensor bifunctor `curriedTensor Mod`, the fixed complex
  `𝒢`, and the additive/map-bifunctor instances;
  the homotopy-category functors together with their exactness structures are derived API provided
  canonically by `Functor.mapHomotopyCategory`.
- redundant ambient assumptions removed in this specialization:
  the ringed-site `Abelian` structure is assumed directly, instead of being recovered through the
  stronger site hypotheses `HasSheafify`/`WEqualsLocallyBijective`; after making that ambient
  owner explicit, the Chapter 13 exactness owners no longer need those stronger site hypotheses or
  `HasCountableCoproducts`.

Source/core/bridge triage:
- `source-facing`: exactness of tensoring on either side by a fixed complex of `𝒪`-modules on a
  ringed site;
- `core/canonical`: `Functor.map₂CochainComplex`, `Functor.mapHomotopyCategory`,
  `Functor.CommShift`, and `Functor.IsTriangulated`;
- `bridge/view`: this file is only the ringed-site specialization of the Chapter 13 owner
  instances, so it should use direct recall rather than keep parallel quotient-lift wrappers. -/

/- Lemma 21.17.1 (left shift form): after fixing the left factor `𝒢`, the induced
tensor-totalization functor on `K(Mod(𝒪))`,
`((curriedTensor Mod).map₂CochainComplex.obj 𝒢).mapHomotopyCategory (up ℤ)`, commutes with the
shift. -/
recall Functor.CommShift :
  Functor.CommShift
    (((curriedTensor Mod).map₂CochainComplex.obj 𝒢).mapHomotopyCategory (up ℤ))
    ℤ

/- Lemma 21.17.1 (left exactness form): after fixing the left factor `𝒢`, the same canonical
owner functor is triangulated. -/
recall Functor.IsTriangulated :
  Functor.IsTriangulated
    (((curriedTensor Mod).map₂CochainComplex.obj 𝒢).mapHomotopyCategory (up ℤ))

/- Lemma 21.17.1 (right shift form): after fixing the right factor `𝒢`, the induced
tensor-totalization functor on `K(Mod(𝒪))`,
`((curriedTensor Mod).map₂CochainComplex.flip.obj 𝒢).mapHomotopyCategory (up ℤ)`, commutes with
the shift. -/
recall Functor.CommShift :
  Functor.CommShift
    (((curriedTensor Mod).map₂CochainComplex.flip.obj 𝒢).mapHomotopyCategory (up ℤ))
    ℤ

/- Lemma 21.17.1 (right exactness form): after fixing the right factor `𝒢`, the corresponding
canonical owner functor is triangulated. -/
recall Functor.IsTriangulated :
  Functor.IsTriangulated
    (((curriedTensor Mod).map₂CochainComplex.flip.obj 𝒢).mapHomotopyCategory (up ℤ))

end

end SheafOfModules.RingedSite
