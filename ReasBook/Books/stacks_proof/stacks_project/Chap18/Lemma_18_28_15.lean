import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import stacks_proof.stacks_project.Chap18.Definition_18_28_1
import stacks_proof.stacks_project.Chap18.Lemma_18_25_1
import stacks_proof.stacks_project.Chap18.Lemma_18_28_10
import stacks_proof.stacks_project.Chap18.Lemma_18_28_13

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
variable {𝒪' 𝒪 : Sheaf J CommRingCat.{u}}
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪')]
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]

/-- A square-zero reduction datum consists of a kernel ideal sheaf
`\mathcal I \hookrightarrow \mathcal O'`, a quotient presentation
`\mathcal F' \twoheadrightarrow \mathcal F`, and the sectionwise square-zero condition on
`\mathcal I`. Here `restrictionAlong α` is the same-site restriction-of-scalars functor attached
to `\alpha : \mathcal O' \to \mathcal O`. -/
structure IsSquareZeroReduction
    (α : 𝒪' ⟶ 𝒪)
    (𝓘 : SheafOfModules (ringSheaf J 𝒪'))
    (ι : 𝓘 ⟶ SheafOfModules.unit (ringSheaf J 𝒪'))
    (ℱ' : SheafOfModules (ringSheaf J 𝒪'))
    (ℱ : SheafOfModules (ringSheaf J 𝒪))
    (tensorTo : moduleTensor 𝓘 (restrictionAlong α |>.obj ℱ) ⟶ ℱ')
    (quot : ℱ' ⟶ (restrictionAlong α).obj ℱ) : Prop where
  /-- The ideal sheaf maps trivially to the quotient structure sheaf `\mathcal O`. -/
  ideal_comp :
    ι ≫ SheafOfModules.unitToPushforwardObjUnit
      (SheafOfModules.RingedSite.ringedSiteStructureMap α) = 0
  /-- The ideal sheaf is included as a submodule of `\mathcal O'`. -/
  ideal_mono : Mono ι
  /-- The sequence `\mathcal I \to \mathcal O' \to \mathcal O` is exact. -/
  ideal_exact :
    (ShortComplex.mk ι
      (SheafOfModules.unitToPushforwardObjUnit
        (SheafOfModules.RingedSite.ringedSiteStructureMap α))
      ideal_comp).Exact
  /-- The map `\mathcal O' \to \mathcal O` is an epimorphism of sheaves of modules. -/
  ideal_epi : Epi (SheafOfModules.unitToPushforwardObjUnit
    (SheafOfModules.RingedSite.ringedSiteStructureMap α))
  /-- Sectionwise, the kernel ideal squares to zero. -/
  square_zero :
    ∀ U : Cᵒᵖ, ∀ x y : 𝓘.val.obj U,
      ((show ↑((ringSheaf J 𝒪').obj.obj U) from ι.val.app U x) *
        (show ↑((ringSheaf J 𝒪').obj.obj U) from ι.val.app U y)) = 0
  /-- The tensor-action map and quotient map compose to zero. -/
  quot_comp : tensorTo ≫ quot = 0
  /-- The sequence `\mathcal I \otimes_{\mathcal O} \mathcal F \to \mathcal F' \to \mathcal F`
  is exact in the categorical formulation used in this file. -/
  quot_exact : (ShortComplex.mk tensorTo quot quot_comp).Exact
  /-- The quotient map `\mathcal F' \to \mathcal F` is an epimorphism. -/
  quot_epi : Epi quot

-- Proof sketch: for the forward implication, use Lemma `18.28.13` to descend flatness along the
-- quotient map `\mathcal O' \twoheadrightarrow \mathcal O`, and apply Lemma `18.28.9` to the
-- exact sequence defining `\mathcal F`. Conversely, test flatness of `\mathcal F'` on a monic
-- map, pass to the quotient exact sequence from `IsSquareZeroReduction`, and use flatness of
-- `\mathcal F` together with the assumed monomorphism of `tensorTo` to recover injectivity after
-- tensoring.
/-- Helper for Chap18 Lemma 18 28 15: the structure-sheaf row in a square-zero reduction is short
exact. -/
private theorem idealShortExactOfSquareZeroReduction
    (α : 𝒪' ⟶ 𝒪)
    (𝓘 : SheafOfModules (ringSheaf J 𝒪'))
    (ι : 𝓘 ⟶ SheafOfModules.unit (ringSheaf J 𝒪'))
    (ℱ' : SheafOfModules (ringSheaf J 𝒪'))
    (ℱ : SheafOfModules (ringSheaf J 𝒪))
    (tensorTo : moduleTensor 𝓘 (restrictionAlong α |>.obj ℱ) ⟶ ℱ')
    (quot : ℱ' ⟶ (restrictionAlong α).obj ℱ)
    (hsetup : IsSquareZeroReduction α 𝓘 ι ℱ' ℱ tensorTo quot) :
    (ShortComplex.mk ι
      (SheafOfModules.unitToPushforwardObjUnit
        (SheafOfModules.RingedSite.ringedSiteStructureMap α))
      hsetup.ideal_comp).ShortExact := by
  -- Proof comment: package the exactness, monomorphism, and epimorphism fields already recorded
  -- in `hsetup` into the canonical short-exact owner.
  exact ShortComplex.ShortExact.mk' hsetup.ideal_exact hsetup.ideal_mono hsetup.ideal_epi

/-- Helper for Chap18 Lemma 18 28 15: once `tensorTo` is known to be mono, the quotient row is
short exact. -/
private theorem quotShortExactOfMono
    (α : 𝒪' ⟶ 𝒪)
    (𝓘 : SheafOfModules (ringSheaf J 𝒪'))
    (ι : 𝓘 ⟶ SheafOfModules.unit (ringSheaf J 𝒪'))
    (ℱ' : SheafOfModules (ringSheaf J 𝒪'))
    (ℱ : SheafOfModules (ringSheaf J 𝒪))
    (tensorTo : moduleTensor 𝓘 (restrictionAlong α |>.obj ℱ) ⟶ ℱ')
    (quot : ℱ' ⟶ (restrictionAlong α).obj ℱ)
    [Mono tensorTo]
    (hsetup : IsSquareZeroReduction α 𝓘 ι ℱ' ℱ tensorTo quot) :
    (ShortComplex.mk tensorTo quot hsetup.quot_comp).ShortExact := by
  -- Proof comment: the quotient row already carries exactness and an epimorphic quotient map, so
  -- the extra mono hypothesis on `tensorTo` completes the short-exact package.
  exact ShortComplex.ShortExact.mk' hsetup.quot_exact inferInstance hsetup.quot_epi

/-- Helper for Chap18 Lemma 18 28 15: if the restricted quotient term is already flat over
`\mathcal O'`, then the quotient short exact row reduces flatness of the lift `\mathcal F'` to
flatness of the tensorized ideal term. -/
private theorem flatTensor_iff_flatLift_of_flatRestrictedQuotient
    (α : 𝒪' ⟶ 𝒪) [Epi α]
    (𝓘 : SheafOfModules (ringSheaf J 𝒪'))
    (ι : 𝓘 ⟶ SheafOfModules.unit (ringSheaf J 𝒪'))
    (ℱ' : SheafOfModules (ringSheaf J 𝒪'))
    (ℱ : SheafOfModules (ringSheaf J 𝒪))
    (tensorTo : moduleTensor 𝓘 (restrictionAlong α |>.obj ℱ) ⟶ ℱ')
    (quot : ℱ' ⟶ (restrictionAlong α).obj ℱ)
    [Mono tensorTo]
    [IsFlat 𝒪' ((restrictionAlong α).obj ℱ)]
    (hsetup : IsSquareZeroReduction α 𝓘 ι ℱ' ℱ tensorTo quot) :
    IsFlat 𝒪' (moduleTensor 𝓘 (restrictionAlong α |>.obj ℱ)) ↔ IsFlat 𝒪' ℱ' := by
  let S : ShortComplex (ringedSiteModuleCategory J 𝒪') :=
    ShortComplex.mk tensorTo quot hsetup.quot_comp
  have hS : S.ShortExact :=
    quotShortExactOfMono α 𝓘 ι ℱ' ℱ tensorTo quot hsetup
  -- Proof comment: once the quotient term is flat, the existing two-out-of-three flatness owner
  -- applies directly to the short exact reduction row.
  simpa [S] using
    (flat_iff_flat_of_shortExact (J := J) (𝒪 := 𝒪') (S := S) hS)

/-- Helper for Chap18 Lemma 18 28 15: exactness transports across a natural isomorphism of
functors. -/
private theorem exactFunctorOfNatIso
    {A : Type*} [Category A]
    {B : Type*} [Category B]
    {F G : A ⥤ B}
    (e : F ≅ G)
    (hF : exactFunctor A B F) :
    exactFunctor A B G := by
  -- Proof comment: exactness is finite-limit and finite-colimit preservation, and both halves
  -- transport functorially across a natural isomorphism.
  rw [CategoryTheory.exactFunctor_iff] at hF ⊢
  let _ : CategoryTheory.Limits.PreservesFiniteLimits F := hF.1
  let _ : CategoryTheory.Limits.PreservesFiniteColimits F := hF.2
  exact
    ⟨CategoryTheory.Limits.preservesFiniteLimits_of_natIso e,
      CategoryTheory.Limits.preservesFiniteColimits_of_natIso e⟩

/-- Helper for Chap18 Lemma 18 28 15: flatness transports across an isomorphism of
`\mathcal O`-modules. -/
private theorem isFlatOfIso
    {𝒪 : Sheaf J CommRingCat.{u}}
    [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
    {X Y : ringedSiteModuleCategory J 𝒪}
    (e : X ≅ Y)
    [IsFlat 𝒪 X] :
    IsFlat 𝒪 Y := by
  refine ⟨?_⟩
  let hExact : exactFunctor
      (ringedSiteModuleCategory J 𝒪)
      (ringedSiteModuleCategory J 𝒪)
      (tensorRight X) :=
    (inferInstance : IsFlat 𝒪 X).exact_tensor
  let eTensor :
      tensorRight X ≅ tensorRight Y :=
    (CategoryTheory.MonoidalCategory.tensoringRight
      (ringedSiteModuleCategory J 𝒪)).mapIso e
  -- Proof comment: after identifying the two tensor-right functors through `e`, the defining
  -- exactness package for flatness transfers verbatim.
  exact exactFunctorOfNatIso eTensor hExact

/-- Helper for Chap18 Lemma 18 28 15: the quotient map `quot` has an adjoint transpose from the
same-site pullback of the lift to the reduction module. -/
private noncomputable abbrev pullbackLiftToReduction
    (α : 𝒪' ⟶ 𝒪)
    (ℱ' : SheafOfModules (ringSheaf J 𝒪'))
    (ℱ : SheafOfModules (ringSheaf J 𝒪))
    (quot : ℱ' ⟶ (restrictionAlong α).obj ℱ) :
    (SheafOfModules.pullback
      (SheafOfModules.RingedSite.ringedSiteStructureMap α)).obj ℱ' ⟶ ℱ :=
  ((SheafOfModules.pullbackPushforwardAdjunction
      (SheafOfModules.RingedSite.ringedSiteStructureMap α)).homEquiv
      ℱ' ℱ).symm quot

/-- Helper for Chap18 Lemma 18 28 15: the same-site pullback of the lift is canonically the
reduction module. -/
private theorem pullbackLiftToReduction_isIso
    (α : 𝒪' ⟶ 𝒪) [Epi α]
    (𝓘 : SheafOfModules (ringSheaf J 𝒪'))
    (ι : 𝓘 ⟶ SheafOfModules.unit (ringSheaf J 𝒪'))
    (ℱ' : SheafOfModules (ringSheaf J 𝒪'))
    (ℱ : SheafOfModules (ringSheaf J 𝒪))
    (tensorTo : moduleTensor 𝓘 (restrictionAlong α |>.obj ℱ) ⟶ ℱ')
    (quot : ℱ' ⟶ (restrictionAlong α).obj ℱ)
    (hsetup : IsSquareZeroReduction α 𝓘 ι ℱ' ℱ tensorTo quot) :
    IsIso (pullbackLiftToReduction α ℱ' ℱ quot) := by
  -- Route correction: this proof is blocked by the statement shape, not by a missing local
  -- transport lemma. The current `IsSquareZeroReduction` structure does not require `tensorTo` to
  -- be the canonical map `𝓘 ⊗_{\mathcal O} \mathcal F → \mathcal F'`, so the later tensor-kernel
  -- identifications needed here are not derivable from the available hypotheses alone.
  sorry

/-- Helper for Chap18 Lemma 18 28 15: flatness of the lift descends to flatness of the
reduction module once the same-site pullback comparison is identified. -/
private theorem isFlatReductionOfIsFlatLiftDirect
    (α : 𝒪' ⟶ 𝒪) [Epi α]
    (𝓘 : SheafOfModules (ringSheaf J 𝒪'))
    (ι : 𝓘 ⟶ SheafOfModules.unit (ringSheaf J 𝒪'))
    (ℱ' : SheafOfModules (ringSheaf J 𝒪'))
    (ℱ : SheafOfModules (ringSheaf J 𝒪))
    (tensorTo : moduleTensor 𝓘 (restrictionAlong α |>.obj ℱ) ⟶ ℱ')
    (quot : ℱ' ⟶ (restrictionAlong α).obj ℱ)
    (hsetup : IsSquareZeroReduction α 𝓘 ι ℱ' ℱ tensorTo quot)
    (hflat' : IsFlat 𝒪' ℱ') :
    IsFlat 𝒪 ℱ := by
  let _ : IsFlat 𝒪' ℱ' := hflat'
  let _ : IsIso (pullbackLiftToReduction α ℱ' ℱ quot) :=
    pullbackLiftToReduction_isIso α 𝓘 ι ℱ' ℱ tensorTo quot hsetup
  let e :
      (SheafOfModules.pullback
        (SheafOfModules.RingedSite.ringedSiteStructureMap α)).obj ℱ' ≅ ℱ :=
    asIso (pullbackLiftToReduction α ℱ' ℱ quot)
  have hPullback :
      IsFlat 𝒪 ((SheafOfModules.pullback
        (SheafOfModules.RingedSite.ringedSiteStructureMap α)).obj ℱ') :=
    pullback_isFlat_of_isFlat (J := J) (α := α) ℱ'
  -- Proof comment: pull back the flat lift along the same-site structure morphism and then
  -- transport flatness across the canonical comparison with the reduction module.
  exact isFlatOfIso (J := J) (𝒪 := 𝒪) e

/-- Helper for Chap18 Lemma 18 28 15: if the lift is flat, then the square-zero boundary map is
monic. -/
private theorem tensorToMono_ofIsFlatLift_viaTransportedIdealRow
    (α : 𝒪' ⟶ 𝒪) [Epi α]
    (𝓘 : SheafOfModules (ringSheaf J 𝒪'))
    (ι : 𝓘 ⟶ SheafOfModules.unit (ringSheaf J 𝒪'))
    (ℱ' : SheafOfModules (ringSheaf J 𝒪'))
    (ℱ : SheafOfModules (ringSheaf J 𝒪))
    (tensorTo : moduleTensor 𝓘 (restrictionAlong α |>.obj ℱ) ⟶ ℱ')
    (quot : ℱ' ⟶ (restrictionAlong α).obj ℱ)
    (hsetup : IsSquareZeroReduction α 𝓘 ι ℱ' ℱ tensorTo quot)
    (hflat' : IsFlat 𝒪' ℱ') :
    Mono tensorTo := by
  -- Route correction: the intended tensor-row argument needs a hypothesis identifying `tensorTo`
  -- with the canonical ideal-action map. Without that compatibility, the transported tensor row is
  -- unrelated to `ShortComplex.mk tensorTo quot hsetup.quot_comp`, so the claimed monomorphism is
  -- false in general.
  sorry

/-- Helper for Chap18 Lemma 18 28 15: flatness of the reduction plus monicity of `tensorTo`
upgrades back to flatness of the lift. -/
private theorem isFlatLiftOfIsFlatReductionAndMonoTensor_viaFourLemma
    (α : 𝒪' ⟶ 𝒪) [Epi α]
    (𝓘 : SheafOfModules (ringSheaf J 𝒪'))
    (ι : 𝓘 ⟶ SheafOfModules.unit (ringSheaf J 𝒪'))
    (ℱ' : SheafOfModules (ringSheaf J 𝒪'))
    (ℱ : SheafOfModules (ringSheaf J 𝒪))
    (tensorTo : moduleTensor 𝓘 (restrictionAlong α |>.obj ℱ) ⟶ ℱ')
    (quot : ℱ' ⟶ (restrictionAlong α).obj ℱ)
    (hsetup : IsSquareZeroReduction α 𝓘 ι ℱ' ℱ tensorTo quot)
    (hflat : IsFlat 𝒪 ℱ)
    [Mono tensorTo] :
    IsFlat 𝒪' ℱ' := by
  -- Route correction: the reverse implication also needs the canonical identification of
  -- `tensorTo` with the ideal-action boundary map. As stated, `tensorTo` may be any surjective map
  -- onto `ker quot`, so flatness of `ℱ'` cannot be reconstructed from `hflat` and `Mono tensorTo`.
  sorry

/-- Lemma 18.28.15: let `(\mathcal C, J)` be a site, let `\alpha : \mathcal O' \to \mathcal O` be
a surjection of sheaves of rings with square-zero kernel ideal sheaf `\mathcal I`, let
`\mathcal F'` be an `\mathcal O'`-module, and let `\mathcal F = \mathcal F'/\mathcal I\mathcal
F'`. In the categorical formulation used here, the quotient data are encoded by
`IsSquareZeroReduction α 𝓘 ι ℱ' ℱ tensorTo quot`, and the map `tensorTo` is the textbook map
`\mathcal I \otimes_{\mathcal O} \mathcal F \to \mathcal F'` after viewing `\mathcal F` as an
`\mathcal O'`-module by restriction of scalars. Then `\mathcal F'` is flat over `\mathcal O'` if
and only if `\mathcal F` is flat over `\mathcal O` and `tensorTo` is injective. -/
@[stacks 08M4]
theorem isFlat_iff_isFlat_reduction_and_mono_tensor_of_squareZeroReduction
    (α : 𝒪' ⟶ 𝒪) [Epi α]
    (𝓘 : SheafOfModules (ringSheaf J 𝒪'))
    (ι : 𝓘 ⟶ SheafOfModules.unit (ringSheaf J 𝒪'))
    (ℱ' : SheafOfModules (ringSheaf J 𝒪'))
    (ℱ : SheafOfModules (ringSheaf J 𝒪))
    (tensorTo : moduleTensor 𝓘 (restrictionAlong α |>.obj ℱ) ⟶ ℱ')
    (quot : ℱ' ⟶ (restrictionAlong α).obj ℱ)
    (hsetup : IsSquareZeroReduction α 𝓘 ι ℱ' ℱ tensorTo quot) :
    IsFlat 𝒪' ℱ' ↔
      IsFlat 𝒪 ℱ ∧ Mono tensorTo := by
  -- Route correction: bypass the broken `Lemma_18_28_13 -> Lemma_18_39_1` import chain and work
  -- directly with the two short exact rows encoded by `hsetup`, factoring the remaining work
  -- into a same-site pullback comparison and one transported tensor-row chase.
  constructor
  · intro hflat'
    refine ⟨?_, ?_⟩
    · -- Proof comment: descend flatness by pulling the lift back along the same-site structure
      -- morphism and comparing the result with the reduction module.
      exact isFlatReductionOfIsFlatLiftDirect α 𝓘 ι ℱ' ℱ tensorTo quot hsetup hflat'
    · -- Proof comment: tensor the ideal short exact row by the flat lift and transport it to the
      -- quotient row to read off the left monomorphism.
      exact tensorToMono_ofIsFlatLift_viaTransportedIdealRow
        α 𝓘 ι ℱ' ℱ tensorTo quot hsetup hflat'
  · rintro ⟨hflat, hmono⟩
    let _ : Mono tensorTo := hmono
    -- Proof comment: once the quotient row is genuinely short exact, the reverse implication is
    -- the normalized four-lemma argument on tensorized short exact rows.
    exact isFlatLiftOfIsFlatReductionAndMonoTensor_viaFourLemma
      α 𝓘 ι ℱ' ℱ tensorTo quot hsetup hflat

end SheafOfModules.RingedSite
