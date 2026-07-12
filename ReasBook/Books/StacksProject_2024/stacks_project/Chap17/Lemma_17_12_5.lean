import Mathlib
import StacksProject_2024.Chap17.Definition_17_12_1
import StacksProject_2024.Chap17.Lemma_17_12_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

variable {X : RingedSpace.{u}}

local notation "ModX" => X.Modules
local notation "𝒪X" => (SheafOfModules.unit X.ringCatSheaf : ModX)

/- Domain-style sampling for coherence versus finite presentation on a ringed space:
- inspected owner declarations:
  `X.Modules`,
  `SheafOfModules.IsCoherent`,
  `SheafOfModules.IsFinitePresentation`
- best owner abstraction:
  the ambient owner is `X.Modules`; coherence and finite presentation are object properties on
  that owner category, and `𝒪X` is the canonical structure-sheaf module owner
- primitive data:
  a ringed space `X`, a module sheaf `ℱ : X.Modules`, and coherence of the structure-sheaf
  module `𝒪X`
- derived API:
  the source-facing equivalence between coherence and finite presentation under the coherent
  structure-sheaf hypothesis

Source/core/bridge triage:
- `source-facing`: the textbook equivalence for `\mathcal O_X`-modules when `\mathcal O_X` is
  coherent
- `core/canonical`: the owner predicates `SheafOfModules.IsCoherent` and
  `SheafOfModules.IsFinitePresentation` on `X.Modules`
- `bridge/view`: this theorem, which relates the two owner predicates under the extra hypothesis on
  the unit module
-/

namespace SheafOfModules

/-- Helper for Lemma 17.12.5: mapping a finite global presentation along restriction preserves the
same finite generator and relation index types. -/
private theorem presentationMapIsFinite
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {𝒪 : Sheaf J RingCat.{u}}
    [HasBinaryProducts C]
    [HasSheafify J AddCommGrpCat]
    [J.WEqualsLocallyBijective AddCommGrpCat]
    [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
    [∀ Y, (J.over Y).HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
    [∀ Y, HasSheafify (J.over Y) AddCommGrpCat]
    [∀ Y, (J.over Y).WEqualsLocallyBijective AddCommGrpCat]
    {ℱ : SheafOfModules 𝒪} (P : ℱ.Presentation) [P.IsFinite] (Y : C) :
    ((P.map (pushforward (𝟙 (𝒪.over Y))) (by rfl))).IsFinite := by
  -- Proof comment: `Presentation.map` only changes the ambient restriction functor, so the
  -- generator and relation index types stay literally the same.
  refine ⟨?_, ?_⟩
  · dsimp [SheafOfModules.Presentation.map, SheafOfModules.presentationOfIsCokernelFree,
      SheafOfModules.generatorsOfIsCokernelFree]
    refine ⟨?_⟩
    change Finite P.generators.I
    infer_instance
  · dsimp [SheafOfModules.Presentation.map, SheafOfModules.presentationOfIsCokernelFree,
      SheafOfModules.relationsOfIsCokernelFree]
    infer_instance

/-- Helper for Lemma 17.12.5: a finite global presentation upgrades to the owner
`IsFinitePresentation`. -/
private theorem isFinitePresentationOfFinitePresentation
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {𝒪 : Sheaf J RingCat.{u}}
    [HasBinaryProducts C]
    [HasSheafify J AddCommGrpCat]
    [J.WEqualsLocallyBijective AddCommGrpCat]
    [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
    [∀ Y, (J.over Y).HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
    [∀ Y, HasSheafify (J.over Y) AddCommGrpCat]
    [∀ Y, (J.over Y).WEqualsLocallyBijective AddCommGrpCat]
    {ℱ : SheafOfModules 𝒪} (P : ℱ.Presentation) [P.IsFinite] :
    ℱ.IsFinitePresentation := by
  -- Proof comment: turn the chosen global presentation into quasi-coherent data on the trivial
  -- cover, then use the previous restriction lemma on each chart.
  refine ⟨P.quasicoherentData, ?_⟩
  constructor
  intro Y
  simpa using presentationMapIsFinite (P := P) Y

/-- Helper for Lemma 17.12.5: a finite free module sheaf over an open subset is of finite type. -/
private theorem finiteFreeOver_isFiniteType
    (U : TopologicalSpace.Opens X) (I : Type u) [Finite I] :
    (SheafOfModules.free (R := X.ringCatSheaf.over U) I).IsFiniteType := by
  let P : (SheafOfModules.free (R := X.ringCatSheaf.over U) I).Presentation :=
    SheafOfModules.presentationOfIsCokernelFree
      (0 : SheafOfModules.free (R := X.ringCatSheaf.over U) Empty ⟶
        SheafOfModules.free (R := X.ringCatSheaf.over U) I)
      (𝟙 _)
      (by simp)
      (CokernelCofork.IsColimit.ofπ' (𝟙 _) (by simp) fun s ↦ ⟨s.π, by simp⟩)
  letI : P.IsFinite := by
    -- Proof comment: this tautological presentation uses the finite basis `I` as generators and
    -- no relations.
    refine ⟨?_, ?_⟩
    · dsimp [P, SheafOfModules.presentationOfIsCokernelFree,
        SheafOfModules.generatorsOfIsCokernelFree]
      exact ⟨inferInstance⟩
    · dsimp [P, SheafOfModules.presentationOfIsCokernelFree,
        SheafOfModules.relationsOfIsCokernelFree]
      infer_instance
  letI : (SheafOfModules.free (R := X.ringCatSheaf.over U) I).IsFinitePresentation :=
    isFinitePresentationOfFinitePresentation P
  -- Proof comment: every finitely presented sheaf is already of finite type.
  infer_instance

/-- Helper for Lemma 17.12.5: coherence over a ringed space should upgrade to finite
presentation. -/
private theorem isFinitePresentation_of_isCoherent
    [SheafOfModules.IsCoherent 𝒪X] (ℱ : ModX) [ℱ.IsCoherent] :
    ℱ.IsFinitePresentation := by
  -- Proof comment: Lemma 17.12.2 already records this as the canonical instance attached to
  -- `SheafOfModules.IsCoherent`.
  infer_instance

/-- Helper for Lemma 17.12.5: finite presentation should restrict to every open subset. -/
private theorem over_isFinitePresentation
    (ℱ : ModX) [ℱ.IsFinitePresentation] (U : TopologicalSpace.Opens X) :
    (ℱ.over U).IsFinitePresentation := by
  let j : restrictedRingedSpace (X := X) U ⟶ X := restrictedOpenInclusion (X := X) U
  -- Proof comment: restriction to `U` is pullback along the canonical open immersion, so the
  -- standard pullback stability theorem for finite presentation applies verbatim.
  simpa [SheafOfModules.over, RingedSpace.Hom.pullback] using
    (SheafOfModules.RingedSite.pullback_isFinitePresentation
      (TopologicalSpace.Opens.map j.hom.base) (RingedSpace.Hom.toRingCatSheafHom j) ℱ)

/-- Helper for Lemma 17.12.5: a kernel into a finitely presented target is finite type as soon as
the source is finite type. -/
private theorem isFiniteType_kernel_of_finiteType_to_finitePresentation
    {U : TopologicalSpace.Opens X}
    {𝒢 ℱ : SheafOfModules (X.ringCatSheaf.over U)} (φ : 𝒢 ⟶ ℱ)
    [𝒢.IsFiniteType] [ℱ.IsFinitePresentation] :
    (kernel φ).IsFiniteType := by
  -- Proof comment: Route correction: rather than rebuilding the image-factorization argument
  -- locally, first upgrade the finitely presented target to a coherent target on the slice site,
  -- then reuse the Chapter 17 kernel theorem for finite-type-to-coherent morphisms.
  let _ : ℱ.IsCoherent := inferInstance
  exact AlgebraicGeometry.RingedSpace.isFiniteType_kernel_of_finiteType_to_coherent φ

/-- Lemma 17.12.5: if the structure sheaf `\mathcal O_X`, regarded as an `\mathcal O_X`-module,
is coherent, then an `\mathcal O_X`-module `\mathcal F` is coherent if and only if it is of
finite presentation. -/
theorem isCoherent_iff_isFinitePresentation
    [SheafOfModules.IsCoherent 𝒪X] (ℱ : ModX) :
    ℱ.IsCoherent ↔ ℱ.IsFinitePresentation := by
  constructor
  · intro hℱ
    letI : ℱ.IsCoherent := hℱ
    -- Proof comment: the forward implication is isolated in a dedicated helper so the main
    -- equivalence keeps the intended textbook shape.
    exact isFinitePresentation_of_isCoherent (X := X) ℱ
  · intro hℱ
    letI : ℱ.IsFinitePresentation := hℱ
    refine SheafOfModules.IsCoherent.mk ?_ ?_
    · -- Proof comment: finitely presented sheaves are in particular of finite type.
      infer_instance
    · intro U r φ
      letI : (ℱ.over U).IsFinitePresentation :=
        over_isFinitePresentation (X := X) ℱ U
      letI :
          (SheafOfModules.free.{u} (R := X.ringCatSheaf.over U) (ULift.{u} (Fin r))).IsFiniteType :=
        finiteFreeOver_isFiniteType (X := X) U (ULift.{u} (Fin r))
      -- Proof comment: apply the generic image-factorization kernel lemma to the finite free
      -- source and the finitely presented target restriction.
      simpa using
        isFiniteType_kernel_of_finiteType_to_finitePresentation (X := X) φ

-- Proof sketch: this is exactly the reverse implication of Lemma 17.12.5.
/-- Helper for Lemma 17.12.5: under coherence of the structure sheaf module, finite presentation
implies coherence. -/
theorem isCoherent_of_isFinitePresentation
    [SheafOfModules.IsCoherent 𝒪X] (ℱ : ModX) [ℱ.IsFinitePresentation] :
    ℱ.IsCoherent := by
  -- Proof comment: reuse the reverse implication already packaged in the main equivalence.
  exact (isCoherent_iff_isFinitePresentation (X := X) ℱ).2 inferInstance

end SheafOfModules
