import StacksProject_2024.stacks_project.Chap15.Lemma_15_58_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_58_1
import StacksProject_2024.stacks_project.Chap21.Lemma_21_17_3
import StacksProject_2024.stacks_project.Chap21.Lemma_21_17_11

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits ComplexShape HomologicalComplex MonoidalCategory
open SheafOfModules.RingedSite.CochainComplex

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

variable {𝒪 : Sheaf J CommRingCat.{max u v}}

variable [Abelian (ringedSiteModuleCategory J 𝒪)]
variable [HasZeroObject (ringedSiteModuleCategory J 𝒪)]
variable [CategoryWithHomology (ringedSiteModuleCategory J 𝒪)]
variable [HasCountableCoproducts (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [SymmetricCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalPreadditive (ringedSiteModuleCategory J 𝒪)]
variable [HasColimits (ringedSiteModuleCategory J 𝒪)]
variable [(curriedTensor (ringedSiteModuleCategory J 𝒪)).Additive]
variable [∀ ℱ : ringedSiteModuleCategory J 𝒪,
  ((curriedTensor (ringedSiteModuleCategory J 𝒪)).obj ℱ).Additive]
variable [∀ (F G : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ),
  CochainComplex.HasMapBifunctor F G (curriedTensor (ringedSiteModuleCategory J 𝒪))]
variable [∀ G₁ G₂ : GradedObject ℤ (ringedSiteModuleCategory J 𝒪), GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (ringedSiteModuleCategory J 𝒪),
  GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (ringedSiteModuleCategory J 𝒪),
  GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ (ringedSiteModuleCategory J 𝒪),
  GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
variable [∀ ℱ : ringedSiteModuleCategory J 𝒪,
  PreservesColimit (Functor.empty.{0} (ringedSiteModuleCategory J 𝒪))
    ((curriedTensor (ringedSiteModuleCategory J 𝒪)).obj ℱ)]
variable [∀ ℱ : ringedSiteModuleCategory J 𝒪,
  PreservesColimit (Functor.empty.{0} (ringedSiteModuleCategory J 𝒪))
    ((curriedTensor (ringedSiteModuleCategory J 𝒪)).flip.obj ℱ)]

local notation "Mod" => ringedSiteModuleCategory J 𝒪

/- Domain-style sampling for Lemma 21.17.12:
- primary domain: quasi-isomorphism invariance of totalized tensoring on cochain complexes of
  `𝒪`-modules over a ringed site;
- sampled owner declarations:
  `CochainComplex.IsKFlat`,
  `HomologicalComplex.tensorHom`,
  `tensorHom_right_quasiIso_of_isKFlat`,
  `exists_termwiseEpi_quasiIso_from_KFlat_complex_of_flat_terms`;
- best owner abstraction: the source-facing Chapter 21 statement should be a local theorem on
  `CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ`, derived from the Chapter 15 fixed-right owner
  `tensorHom_right_quasiIso_of_isKFlat` together with the Chapter 21 K-flat resolution owner
  `exists_termwiseEpi_quasiIso_from_KFlat_complex_of_flat_terms`;
- primitive vs. derived: the primitive data are the complexes `F`, `P`, `Q`, the K-flatness
  proofs for `P` and `Q`, and the quasi-isomorphism `α : P ⟶ Q`. The induced morphism on
  totalized tensor products is the canonical derived API `HomologicalComplex.tensorHom (𝟙 F) α`.

Source/core/bridge triage:
- `source-facing`: the ringed-site formulation of Stacks Project Lemma 21.17.12;
- `core/canonical`: `K.IsKFlat`, `HomologicalComplex.tensorHom`, and the fixed-right tensor theorem
  `tensorHom_right_quasiIso_of_isKFlat`;
- `bridge/view`: the K-flat resolution supplied by Lemma `21.17.11`, which connects an arbitrary
  left tensor factor to the fixed-right owner theorem without introducing a parallel wrapper. -/

-- Proof sketch: choose a quasi-isomorphism `K ⟶ F` from a K-flat complex using Lemma
-- `21.17.11`. Tensoring this comparison with either `P` or `Q` gives quasi-isomorphisms on
-- the vertical arrows by the Chapter 15 fixed-right owner theorem, while tensoring `α` with the
-- K-flat complex `K` gives a quasi-isomorphism on the top horizontal map. The commutative
-- square then forces the bottom horizontal map to be a quasi-isomorphism.
omit [HasCountableCoproducts Mod] [HasColimits Mod] in
/-- Lemma 21.17.12: if `α : P ⟶ Q` is a quasi-isomorphism between K-flat
cochain complexes of `𝒪`-modules on a ringed site `(C, 𝒪)`, then for every complex
`F` the induced map `tensorHom (𝟙 F) α` is a
quasi-isomorphism. -/
@[stacks 06YT]
  lemma quasiIso_totalizedTensor_map_right_of_quasiIso_of_isKFlat
    (F P Q : CochainComplex Mod ℤ)
    (hP : P.IsKFlat) (hQ : Q.IsKFlat)
    (α : P ⟶ Q) (hα : QuasiIso α) :
    QuasiIso (HomologicalComplex.tensorHom (𝟙 F) α) := by
  sorry

end SheafOfModules.RingedSite
