import StacksProject_2024.stacks_project.Chap21.Definition_21_17_2
import StacksProject_2024.stacks_project.Chap21.Definition_21_46_1
import StacksProject_2024.stacks_project.Chap21.Lemma_21_18_1

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape
open DerivedCategory
open RingedSite.Hom (ModuleCat ModuleDerived)
open scoped RingedSite.Hom
open SheafOfModules.RingedSite.CochainComplex

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false

namespace SheafOfModules.RingedSite

section

/- Domain-style sampling for Lemma 21.46.4:
- primary domain: lower tor-amplitude on `D(𝒪_X)` for a commutative ringed-site
  presentation, expressed via flat K-flat representatives;
- sampled owner declarations:
  `SheafOfModules.RingedSite.HasTorAmplitudeGE`,
  `SheafOfModules.RingedSite.pullback_isKFlat_and_termwiseFlat_of_isKFlat_and_termwiseFlat`,
  `RingedSite.Hom.ModuleCat`,
  `RingedSite.Hom.ModuleDerived`,
  `CochainComplex.IsTermwiseFlat`,
  `DerivedCategory.singleFunctor`,
  `DerivedCategory.Q.obj`;
- best owner abstraction: the source-facing owner remains
  `SheafOfModules.RingedSite.HasTorAmplitudeGE` on the bundled ringed site
  `X := RingedSite.ofCommRingSheaf J 𝒪`, with ambient module category `ModuleCat X` and derived
  category `ModuleDerived X`; the representative complex remains the primitive cochain-level data
  in `CochainComplex (ModuleCat X) ℤ`;
- primitive data: the derived object `E`, the lower bound `a`, and a representative complex `K`
  with support condition `K.IsStrictlyGE a`, K-flatness, the canonical Chapter 21 termwise-flat
  owner `CochainComplex.IsTermwiseFlat 𝒪 K`, and an isomorphism `E ≅ DerivedCategory.Q.obj K`;
- derived API: the representative criterion below for the owner `HasTorAmplitudeGE`; the
  degreewise flatness expansion is now delegated to `CochainComplex.isTermwiseFlat_iff`, and the
  Stacks “moreover” pullback-stability clause is obtained by combining
  `HasTorAmplitudeGE.exists_representative` with
  `pullback_isKFlat_and_termwiseFlat_of_isKFlat_and_termwiseFlat`.

Source/core/bridge triage:
- `source-facing`: the representative criterion below for the lower tor-amplitude owner on a
  commutative ringed site;
- `core/canonical`: the bundled ringed site `X := RingedSite.ofCommRingSheaf J 𝒪`, `ModuleCat X`,
  `ModuleDerived X`, `HasTorAmplitudeGE`, `DerivedCategory.Q.obj`,
  `CochainComplex.IsStrictlyGE`, `CochainComplex.IsKFlat`, and
  `CochainComplex.IsTermwiseFlat`;
- `bridge/view`: the Chapter 15 affine analogue `CategoryTheory.HasTorAmplitudeGE`, which guides
  the statement shape, and the companion theorem `CochainComplex.isTermwiseFlat_iff`.
-/

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

local notation "X" => RingedSite.ofCommRingSheaf J 𝒪
local notation "DMod" => ModuleDerived X
local notation "Cpx" => CochainComplex (ModuleCat X) ℤ

variable [Abelian (ModuleCat X)]
variable [CategoryWithHomology (ModuleCat X)]
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [(curriedTensor (ringedSiteModuleCategory J 𝒪)).Additive]
variable [∀ M : ringedSiteModuleCategory J 𝒪,
  ((curriedTensor (ringedSiteModuleCategory J 𝒪)).obj M).Additive]

-- Proof sketch: if `E` is represented by a K-flat complex of flat modules supported in degrees
-- `≥ a`, then derived tensoring with any degree-zero module is computed termwise and has no
-- homology below `a`. Conversely, start from a K-flat flat representative of `E`, use the
-- lower-bound tensor hypothesis together with Lemma `21.46.2` to identify the new degree-`a`
-- cokernel as flat, and replace the complex by its brutal truncation `τ≥ a`.
/-- Lemma 21.46.4: an object `E` of `D(𝒪_X)` satisfies
`E ⊗^L 𝓕[0] ∈ D^{≥ a}` for every `𝒪_X`-module `𝓕` if and only if it is isomorphic in `D(𝒪_X)`
to a K-flat cochain complex `ℰ` of flat `𝒪_X`-modules with `ℰ.X i = 0` for `i < a`. -/
@[stacks 0F1M]
theorem hasTorAmplitudeGE_iff_exists_representative
    [MonoidalCategoryStruct (ModuleDerived X)]
    (E : DMod) (a : ℤ) :
    HasTorAmplitudeGE E a ↔
      ∃ (K : Cpx) (_ : E ≅ Q.obj K),
        K.IsStrictlyGE a ∧ K.IsKFlat ∧ IsTermwiseFlat K := by
  sorry

/-- Companion API for Lemma 21.46.4: lower tor-amplitude is witnessed by a K-flat termwise-flat
representative supported in degrees `≥ a`. -/
theorem HasTorAmplitudeGE.exists_representative
    [MonoidalCategoryStruct (ModuleDerived X)]
    {E : DMod} {a : ℤ} :
    HasTorAmplitudeGE E a →
      ∃ (K : Cpx) (_ : E ≅ Q.obj K),
        K.IsStrictlyGE a ∧ K.IsKFlat ∧ IsTermwiseFlat K :=
  (hasTorAmplitudeGE_iff_exists_representative E a).1

/-- Lemma 21.46.4, moreover clause: the representative for a lower tor-amplitude bound may be
chosen once and for all so that every site-presented pullback remains K-flat and termwise flat. -/
@[stacks 0F1M]
theorem HasTorAmplitudeGE.exists_representative_with_pullback_stability
    [MonoidalCategoryStruct (ModuleDerived X)]
    [MonoidalPreadditive (ringedSiteModuleCategory J 𝒪)]
    {E : DMod} {a : ℤ} :
    HasTorAmplitudeGE E a →
    ∃ (K : Cpx) (_ : E ≅ Q.obj K),
      K.IsStrictlyGE a ∧ K.IsKFlat ∧ IsTermwiseFlat K ∧
        ∀ {D : Type u} [Category.{v} D] {JD : GrothendieckTopology D}
          [JD.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
          (F : C ⥤ D) [Functor.IsContinuous F J JD]
          {𝒪' : Sheaf JD CommRingCat.{max u v}}
          (φ : 𝒪 ⟶ (F.sheafPushforwardContinuous CommRingCat.{max u v} J JD).obj 𝒪')
          [(SheafOfModules.pushforward (ringedSiteUnderlyingStructureMap F φ)).IsRightAdjoint]
          [MonoidalCategory (ringedSiteModuleCategory JD 𝒪')]
          [MonoidalPreadditive (ringedSiteModuleCategory JD 𝒪')],
            (pullbackComplex F φ K).IsKFlat ∧ IsTermwiseFlat (pullbackComplex F φ K) := by
  intro hE
  have hRep :
      ∃ (K : Cpx) (_ : E ≅ Q.obj K),
        K.IsStrictlyGE a ∧ K.IsKFlat ∧ IsTermwiseFlat K :=
    HasTorAmplitudeGE.exists_representative hE
  obtain ⟨K, e, hge, hKFlat, hFlat⟩ := hRep
  refine ⟨K, e, hge, hKFlat, hFlat, ?_⟩
  intro D _ JD _ F _ 𝒪' φ _ _ _
  simpa using
    pullback_isKFlat_and_termwiseFlat_of_isKFlat_and_termwiseFlat F φ K hKFlat hFlat

end

end SheafOfModules.RingedSite
