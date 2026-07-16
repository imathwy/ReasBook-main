import Mathlib
import stacks_proof.stacks_project.Chap12.Lemma_12_7_2
import stacks_proof.stacks_project.Chap18.Definition_18_28_1
import stacks_proof.stacks_project.Chap18.Lemma_18_28_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory MonoidalCategory Opposite
open scoped PresheafOfModules.Monoidal

noncomputable section

universe u

namespace CategoryTheory

/-- Helper for Lemma 18.28.10: in a morphism of short exact rows, monicity of the two outer
vertical maps forces monicity of the middle vertical map by the four lemma. -/
private theorem shortComplex_middle_mono_of_outer_mono
    {A : Type*} [Category A] [Abelian A]
    {R₁ R₂ : ShortComplex A}
    (φ : R₁ ⟶ R₂)
    (hR₁ : R₁.ShortExact)
    (hR₂ : R₂.ShortExact)
    [Mono φ.τ₁] [Mono φ.τ₃] :
    Mono φ.τ₂ := by
  -- Proof comment: chase a generic morphism into the middle term through the exact left row and
  -- cancel it first against the right outer mono and then against the left outer mono.
  rw [Preadditive.mono_iff_cancel_zero]
  intro Z x hx
  have hxg : x ≫ R₁.g = 0 := by
    have haux : x ≫ R₁.g ≫ φ.τ₃ = 0 := by
      calc
        x ≫ R₁.g ≫ φ.τ₃ = x ≫ φ.τ₂ ≫ R₂.g := by
          simpa [Category.assoc] using congrArg (fun k ↦ x ≫ k) φ.comm₂₃.symm
        _ = 0 := by
          simpa [Category.assoc] using congrArg (fun t ↦ t ≫ R₂.g) hx
    exact (cancel_mono φ.τ₃).1 (by simpa [Category.assoc] using haux)
  let y : Z ⟶ R₁.X₁ :=
    hR₁.fIsKernel.lift (Limits.KernelFork.ofι x hxg)
  have hy : y ≫ R₁.f = x := by
    simpa using
      hR₁.fIsKernel.fac (Limits.KernelFork.ofι x hxg) Limits.WalkingParallelPair.zero
  let _ : Mono R₂.f := hR₂.mono_f
  have hya : y ≫ φ.τ₁ = 0 := by
    have haux : y ≫ φ.τ₁ ≫ R₂.f = 0 := by
      calc
        y ≫ φ.τ₁ ≫ R₂.f = y ≫ R₁.f ≫ φ.τ₂ := by
          simpa [Category.assoc] using congrArg (fun k ↦ y ≫ k) φ.comm₁₂
        _ = x ≫ φ.τ₂ := by
          simpa [Category.assoc] using congrArg (fun t ↦ t ≫ φ.τ₂) hy
        _ = 0 := hx
    exact (cancel_mono R₂.f).1 (by simpa [Category.assoc] using haux)
  have hyZero : y = 0 := by
    exact (cancel_mono φ.τ₁).1 (by simpa using hya)
  simpa [hyZero] using hy.symm

/-- Helper for Lemma 18.28.10: in a morphism of short exact rows, epimorphy of the two outer
vertical maps forces epimorphy of the middle vertical map by the four lemma. -/
private theorem shortComplex_middle_epi_of_outer_epi
    {A : Type*} [Category A] [Abelian A]
    {R₁ R₂ : ShortComplex A}
    (φ : R₁ ⟶ R₂)
    (hR₁ : R₁.ShortExact)
    (hR₂ : R₂.ShortExact)
    [Epi φ.τ₁] [Epi φ.τ₃] :
    Epi φ.τ₂ := by
  -- Proof comment: the short-complex four-lemma already upgrades the middle vertical map to an
  -- epimorphism once the lower row is exact, the upper right map is epi, and the two outer
  -- vertical maps are epi.
  let _ : Epi R₁.g := hR₁.epi_g
  exact CategoryTheory.ShortComplex.epi_of_epi_of_epi_of_epi φ hR₂.exact

end CategoryTheory

namespace PresheafOfModules

variable {C : Type u} [Category.{u} C]
variable {𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}}
variable {S : ShortComplex (PresheafOfModules (ringPresheaf 𝒪))}

/-- Helper for Lemma 18.28.10: if tensoring on the right by `X` sends every short exact sequence
to a short exact sequence, then `X` is flat. -/
private theorem isFlat_of_mapsShortExact
    (X : PresheafOfModules (ringPresheaf 𝒪))
    (hX : ∀ T : ShortComplex (PresheafOfModules (ringPresheaf 𝒪)),
      T.ShortExact → (T.map (tensorRight X)).ShortExact) :
    IsFlat X := by
  refine ⟨?_⟩
  -- Proof comment: apply the Chapter 12 exact-functor criterion directly to `tensorRight X`.
  exact
    (CategoryTheory.functor_exact_iff_maps_shortExact_to_exact_mono_epi
      (A := PresheafOfModules (ringPresheaf 𝒪))
      (B := PresheafOfModules (ringPresheaf 𝒪))
      (F := tensorRight X)).2 fun T hT ↦ by
        let hTX := hX T hT
        exact ⟨
          ((T.map (tensorRight X)).exact_iff_exact_toComposableArrows).1 hTX.exact,
          hTX.mono_f,
          hTX.epi_g
        ⟩

/-- Helper for Lemma 18.28.10: flatness of `X` makes left tensoring by `X` exact via the braided
comparison with right tensoring. -/
private theorem tensorLeft_exact_of_isFlat
    (X : PresheafOfModules (ringPresheaf 𝒪))
    [IsFlat X] :
    exactFunctor
      (PresheafOfModules (ringPresheaf 𝒪))
      (PresheafOfModules (ringPresheaf 𝒪))
      (tensorLeft X) := by
  let hExact := (inferInstance : IsFlat X).exact_tensor
  -- Proof comment: transport finite-limit and finite-colimit preservation across the braiding
  -- isomorphism `tensorLeft X ≅ tensorRight X`.
  rw [CategoryTheory.exactFunctor_iff] at hExact
  let _ : CategoryTheory.Limits.PreservesFiniteLimits (tensorRight X) := hExact.1
  let _ : CategoryTheory.Limits.PreservesFiniteColimits (tensorRight X) := hExact.2
  rw [CategoryTheory.exactFunctor_iff]
  exact
    ⟨CategoryTheory.Limits.preservesFiniteLimits_of_natIso
        (CategoryTheory.BraidedCategory.tensorLeftIsoTensorRight X).symm,
      CategoryTheory.Limits.preservesFiniteColimits_of_natIso
        (CategoryTheory.BraidedCategory.tensorLeftIsoTensorRight X).symm⟩

/-- Helper for Lemma 18.28.10: if `X` is flat, then tensoring a short exact sequence on the left
by `X` stays short exact. -/
private theorem shortExact_map_tensorLeft_of_isFlat
    (X : PresheafOfModules (ringPresheaf 𝒪))
    [IsFlat X]
    (T : ShortComplex (PresheafOfModules (ringPresheaf 𝒪)))
    (hT : T.ShortExact) :
    (T.map (tensorLeft X)).ShortExact := by
  -- Proof comment: once left tensoring is exact, mapped short exactness is immediate.
  let hExact := tensorLeft_exact_of_isFlat (𝒪 := 𝒪) X
  let _ : CategoryTheory.Limits.PreservesFiniteLimits (tensorLeft X) :=
    (CategoryTheory.exactFunctor_iff (tensorLeft X)).1 hExact |>.1
  let _ : CategoryTheory.Limits.PreservesFiniteColimits (tensorLeft X) :=
    (CategoryTheory.exactFunctor_iff (tensorLeft X)).1 hExact |>.2
  exact hT.map_of_exact (tensorLeft X)

/-- Helper for Lemma 18.28.10: short exactness of a mapped short complex is invariant under a
natural isomorphism of functors. -/
private theorem shortExact_iff_of_functor_iso
    {A : Type*} {B : Type*}
    [Category A] [Category B]
    [CategoryTheory.Limits.HasZeroMorphisms A] [CategoryTheory.Limits.HasZeroMorphisms B]
    {F G : A ⥤ B}
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    (e : F ≅ G)
    (T : ShortComplex A) :
    (T.map F).ShortExact ↔ (T.map G).ShortExact := by
  -- Proof comment: compare the two mapped short complexes termwise using the functor isomorphism.
  let i : T.map F ≅ T.map G :=
    ShortComplex.isoMk
      (e.app T.X₁)
      (e.app T.X₂)
      (e.app T.X₃)
      (by simpa using e.hom.naturality T.f)
      (by simpa using e.hom.naturality T.g)
  constructor
  · -- Proof comment: transport short exactness forward across the induced short-complex isomorphism.
    intro h
    exact ShortComplex.shortExact_of_iso i h
  · -- Proof comment: transport short exactness backward along the inverse isomorphism.
    intro h
    exact ShortComplex.shortExact_of_iso i.symm h

/-- Helper for Lemma 18.28.10: if `X` is flat, then tensoring a short exact sequence on the right
by `X` stays short exact. -/
private theorem shortExact_map_tensorRight_of_isFlat
    (X : PresheafOfModules (ringPresheaf 𝒪))
    [IsFlat X]
    (T : ShortComplex (PresheafOfModules (ringPresheaf 𝒪)))
    (hT : T.ShortExact) :
    (T.map (tensorRight X)).ShortExact := by
  -- Proof comment: this is the defining exactness property of a flat presheaf module.
  let hExact := IsFlat.exact_tensor (ℱ := X)
  let _ : CategoryTheory.Limits.PreservesFiniteLimits (tensorRight X) :=
    (CategoryTheory.exactFunctor_iff (tensorRight X)).1 hExact |>.1
  let _ : CategoryTheory.Limits.PreservesFiniteColimits (tensorRight X) :=
    (CategoryTheory.exactFunctor_iff (tensorRight X)).1 hExact |>.2
  exact hT.map_of_exact (tensorRight X)

/-- Helper for Lemma 18.28.10: right tensoring is always right exact, so a mapped short exact
sequence stays exact and keeps an epimorphic second map. -/
private theorem tensorRight_mapsShortExact_to_exact_epi
    (X : PresheafOfModules (ringPresheaf 𝒪))
    (T : ShortComplex (PresheafOfModules (ringPresheaf 𝒪)))
    (hT : T.ShortExact) :
    (ComposableArrows.mk₂ ((tensorRight X).map T.f) ((tensorRight X).map T.g)).Exact ∧
      Epi ((tensorRight X).map T.g) := by
  let hRight :
      rightExactFunctor
        (PresheafOfModules (ringPresheaf 𝒪))
        (PresheafOfModules (ringPresheaf 𝒪))
        (tensorRight X) := by
    simpa [CategoryTheory.rightExactFunctor_iff] using
      (inferInstance : CategoryTheory.Limits.PreservesFiniteColimits (tensorRight X))
  -- Proof comment: apply the Chapter 12 right-exactness criterion to the tensor-right functor.
  exact
    (CategoryTheory.functor_rightExact_iff_maps_shortExact_to_exact_epi
      (A := PresheafOfModules (ringPresheaf 𝒪))
      (B := PresheafOfModules (ringPresheaf 𝒪))
      (F := tensorRight X)).1 hRight T hT

/-- Helper for Lemma 18.28.10: the short exactness statement from Lemma 18.28.9 can be rewritten
with left tensoring using braiding. -/
private theorem shortExact_tensor_left_of_flatQuotient
    (X : PresheafOfModules (ringPresheaf 𝒪))
    (hS : S.ShortExact)
    [IsFlat S.X₃] :
    (S.map (tensorLeft X)).ShortExact := by
  let hRight : (S.map (tensorRight X)).ShortExact :=
    shortExact_tensor_right_of_flat_quotient (𝒢 := X) (S := S) hS
  -- Proof comment: transport the right-tensor short exact sequence through the braided
  -- comparison `tensorLeft X ≅ tensorRight X`.
  exact
    (shortExact_iff_of_functor_iso
      (e := CategoryTheory.BraidedCategory.tensorLeftIsoTensorRight X) S).2 hRight

/-- Helper for Lemma 18.28.10: if the left and right terms of `S` are flat, then tensoring any
short exact row `T` by the middle term of `S` stays short exact. -/
private theorem tensorMiddleShortExactOfFlatEnds
    (hS : S.ShortExact)
    [IsFlat S.X₃] [IsFlat S.X₁]
    (T : ShortComplex (PresheafOfModules (ringPresheaf 𝒪)))
    (hT : T.ShortExact) :
    (T.map (tensorRight S.X₂)).ShortExact := by
  let row₁ : (S.map (tensorLeft T.X₁)).ShortExact :=
    shortExact_tensor_left_of_flatQuotient (𝒪 := 𝒪) (S := S) T.X₁ hS
  let row₂ : (S.map (tensorLeft T.X₂)).ShortExact :=
    shortExact_tensor_left_of_flatQuotient (𝒪 := 𝒪) (S := S) T.X₂ hS
  let col₁ : (T.map (tensorRight S.X₁)).ShortExact :=
    shortExact_map_tensorRight_of_isFlat (𝒪 := 𝒪) S.X₁ T hT
  let col₃ : (T.map (tensorRight S.X₃)).ShortExact :=
    shortExact_map_tensorRight_of_isFlat (𝒪 := 𝒪) S.X₃ T hT
  let rowMap :
      S.map (tensorLeft T.X₁) ⟶ S.map (tensorLeft T.X₂) :=
    S.mapNatTrans
      ((CategoryTheory.MonoidalCategory.tensoringLeft
        (PresheafOfModules (ringPresheaf 𝒪))).map T.f)
  have hMiddleMono : Mono ((tensorRight S.X₂).map T.f) := by
    -- Proof comment: the two tensor rows are short exact, and the outer tensor columns are mono
    -- on the left map, so the four lemma upgrades the middle tensor column to a monomorphism.
    let _ : Mono rowMap.τ₁ := by
      simpa [rowMap] using col₁.mono_f
    let _ : Mono rowMap.τ₃ := by
      simpa [rowMap] using col₃.mono_f
    simpa [rowMap] using
      (CategoryTheory.shortComplex_middle_mono_of_outer_mono rowMap row₁ row₂)
  let hExactEpi := tensorRight_mapsShortExact_to_exact_epi (𝒪 := 𝒪) S.X₂ T hT
  -- Proof comment: right exactness supplies exactness and the epimorphic right map, while the
  -- four lemma supplies the missing monomorphism on the left map.
  exact ShortComplex.ShortExact.mk'
    ((T.map (tensorRight S.X₂)).exact_iff_exact_toComposableArrows.2 hExactEpi.1)
    hMiddleMono
    hExactEpi.2

/-- Helper for Lemma 18.28.10: if the middle and right terms of `S` are flat, then tensoring any
short exact row `T` by the left term of `S` stays short exact. -/
private theorem tensorLeftTermShortExactOfFlatMiddleRight
    (hS : S.ShortExact)
    [IsFlat S.X₃] [IsFlat S.X₂]
    (T : ShortComplex (PresheafOfModules (ringPresheaf 𝒪)))
    (hT : T.ShortExact) :
    (T.map (tensorRight S.X₁)).ShortExact := by
  let row₁ : (S.map (tensorLeft T.X₁)).ShortExact :=
    shortExact_tensor_left_of_flatQuotient (𝒪 := 𝒪) (S := S) T.X₁ hS
  let row₂ : (S.map (tensorLeft T.X₂)).ShortExact :=
    shortExact_tensor_left_of_flatQuotient (𝒪 := 𝒪) (S := S) T.X₂ hS
  let middleCol : (T.map (tensorRight S.X₂)).ShortExact :=
    shortExact_map_tensorRight_of_isFlat (𝒪 := 𝒪) S.X₂ T hT
  let rowMap :
      S.map (tensorLeft T.X₁) ⟶ S.map (tensorLeft T.X₂) :=
    S.mapNatTrans
      ((CategoryTheory.MonoidalCategory.tensoringLeft
        (PresheafOfModules (ringPresheaf 𝒪))).map T.f)
  have hLeftMono : Mono ((tensorRight S.X₁).map T.f) := by
    -- Proof comment: the first row map factors through the monomorphism in the middle tensor
    -- column, so cancellation along the second row identifies the left tensor column as mono.
    let _ : Mono rowMap.τ₂ := by
      simpa [rowMap] using middleCol.mono_f
    let _ : Mono (S.map (tensorLeft T.X₁)).f := row₁.mono_f
    have hCompFac :
        rowMap.τ₁ ≫ (S.map (tensorLeft T.X₂)).f =
          (S.map (tensorLeft T.X₁)).f ≫ rowMap.τ₂ := by
      simpa using rowMap.comm₁₂
    have hCompMono : Mono ((S.map (tensorLeft T.X₁)).f ≫ rowMap.τ₂) :=
      CategoryTheory.mono_comp _ _
    let _ : Mono ((S.map (tensorLeft T.X₁)).f ≫ rowMap.τ₂) := hCompMono
    simpa [rowMap] using
      (show Mono rowMap.τ₁ from mono_of_mono_fac hCompFac)
  let hExactEpi := tensorRight_mapsShortExact_to_exact_epi (𝒪 := 𝒪) S.X₁ T hT
  -- Proof comment: right exactness again gives exactness and the epimorphic right map; the
  -- commuting square with the middle flat column supplies the monomorphism on the left.
  exact ShortComplex.ShortExact.mk'
    ((T.map (tensorRight S.X₁)).exact_iff_exact_toComposableArrows.2 hExactEpi.1)
    hLeftMono
    hExactEpi.2

-- Proof sketch: if `S.X₁` is flat, apply Lemma `18.28.9` to see that tensoring `S` on the right
-- preserves short exactness, hence the exact tensor functor criterion gives flatness of `S.X₂`.
-- Conversely, if `S.X₂` is flat, use the exactness of tensoring with `S.X₂` and the snake-lemma
-- argument from the textbook to recover exactness after tensoring with `S.X₁`.
/-- Lemma 18.28.10: for a short exact sequence
`0 ⟶ \mathcal F_2 ⟶ \mathcal F_1 ⟶ \mathcal F_0 ⟶ 0` of presheaves of
`\mathcal O`-modules, if `\mathcal F_0` is flat then `\mathcal F_2` is flat if and only if
`\mathcal F_1` is flat. -/
@[stacks 03EY]
theorem flat_iff_flat_of_shortExact
    (hS : S.ShortExact) [IsFlat S.X₃] :
    IsFlat S.X₁ ↔ IsFlat S.X₂ := by
  constructor
  · intro h₁
    let _ : IsFlat S.X₁ := h₁
    -- Proof comment: tensor every short exact test row by `S.X₂`; right exactness gives the
    -- exact/epi part, and the four lemma forces the left map to be mono.
    exact isFlat_of_mapsShortExact S.X₂ fun T hT ↦
      tensorMiddleShortExactOfFlatEnds (𝒪 := 𝒪) (S := S) hS T hT
  · intro h₂
    let _ : IsFlat S.X₂ := h₂
    -- Proof comment: tensor every short exact test row by `S.X₁`; the middle flat column makes
    -- the left tensor column monic, and right exactness supplies the rest.
    exact isFlat_of_mapsShortExact S.X₁ fun T hT ↦
      tensorLeftTermShortExactOfFlatMiddleRight (𝒪 := 𝒪) (S := S) hS T hT

end PresheafOfModules

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {𝒪 : Sheaf J CommRingCat.{u}}
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable {S : ShortComplex (SheafOfModules (ringSheaf J 𝒪))}

local notation "Mod(" 𝒪 ")" => ringedSiteModuleCategory J 𝒪

omit [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Helper for Lemma 18.28.10: if `X` is flat, then tensoring a short exact sequence on the right
by `X` stays short exact. -/
private theorem shortExact_map_tensorRight_of_isFlat
    (X : Mod(𝒪))
    [IsFlat 𝒪 X]
    (T : ShortComplex (Mod(𝒪)))
    (hT : T.ShortExact) :
    (T.map (tensorRight X)).ShortExact := by
  -- Proof comment: this is the defining exactness property of a flat sheaf module.
  let hExact := (inferInstance : IsFlat 𝒪 X).exact_tensor
  let _ : CategoryTheory.Limits.PreservesFiniteLimits (tensorRight X) :=
    (CategoryTheory.exactFunctor_iff (tensorRight X)).1 hExact |>.1
  let _ : CategoryTheory.Limits.PreservesFiniteColimits (tensorRight X) :=
    (CategoryTheory.exactFunctor_iff (tensorRight X)).1 hExact |>.2
  exact hT.map_of_exact (tensorRight X)

/-- Helper for Lemma 18.28.10: if tensoring on the right by `X` sends every short exact sequence
to a short exact sequence, then `X` is flat. -/
private theorem isFlat_of_mapsShortExact
    (X : Mod(𝒪))
    (hX : ∀ T : ShortComplex (Mod(𝒪)),
      T.ShortExact → (T.map (tensorRight X)).ShortExact) :
    IsFlat 𝒪 X := by
  refine ⟨?_⟩
  -- Proof comment: apply the Chapter 12 exact-functor criterion directly to `tensorRight X`.
  exact
    (CategoryTheory.functor_exact_iff_maps_shortExact_to_exact_mono_epi
      (A := Mod(𝒪))
      (B := Mod(𝒪))
      (F := tensorRight X)).2 fun T hT ↦ by
        let hTX := hX T hT
        exact ⟨
          ((T.map (tensorRight X)).exact_iff_exact_toComposableArrows).1 hTX.exact,
          hTX.mono_f,
          hTX.epi_g
        ⟩

/-- Helper for Lemma 18.28.10: short exactness of a mapped short complex is invariant under a
natural isomorphism of functors. -/
private theorem shortExact_iff_of_functor_iso
    {A : Type*} {B : Type*}
    [Category A] [Category B]
    [CategoryTheory.Limits.HasZeroMorphisms A] [CategoryTheory.Limits.HasZeroMorphisms B]
    {F G : A ⥤ B}
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    (e : F ≅ G)
    (T : ShortComplex A) :
    (T.map F).ShortExact ↔ (T.map G).ShortExact := by
  -- Proof comment: compare the two mapped short complexes termwise using the functor isomorphism.
  let i : T.map F ≅ T.map G :=
    ShortComplex.isoMk
      (e.app T.X₁)
      (e.app T.X₂)
      (e.app T.X₃)
      (by simpa using e.hom.naturality T.f)
      (by simpa using e.hom.naturality T.g)
  constructor
  · -- Proof comment: transport short exactness forward across the induced short-complex isomorphism.
    intro h
    exact ShortComplex.shortExact_of_iso i h
  · -- Proof comment: transport short exactness backward along the inverse isomorphism.
    intro h
    exact ShortComplex.shortExact_of_iso i.symm h

/-- Helper for Lemma 18.28.10: right tensoring is always right exact, so a mapped short exact
sequence stays exact and keeps an epimorphic second map. -/
private theorem tensorRight_mapsShortExact_to_exact_epi
    (X : Mod(𝒪))
    (T : ShortComplex (Mod(𝒪)))
    (hT : T.ShortExact) :
    (ComposableArrows.mk₂ ((tensorRight X).map T.f) ((tensorRight X).map T.g)).Exact ∧
      Epi ((tensorRight X).map T.g) := by
  let hRight :
      rightExactFunctor
        (Mod(𝒪))
        (Mod(𝒪))
        (tensorRight X) := by
    simpa [CategoryTheory.rightExactFunctor_iff] using
      (inferInstance : CategoryTheory.Limits.PreservesFiniteColimits (tensorRight X))
  -- Proof comment: apply the Chapter 12 right-exactness criterion to the tensor-right functor.
  exact
    (CategoryTheory.functor_rightExact_iff_maps_shortExact_to_exact_epi
      (A := Mod(𝒪))
      (B := Mod(𝒪))
      (F := tensorRight X)).1 hRight T hT

/-- Helper for Lemma 18.28.10: the short exactness statement from Lemma 18.28.9 can be rewritten
with left tensoring using braiding. -/
private theorem shortExact_tensorLeft_of_flatQuotient
    (X : Mod(𝒪))
    (hS : S.ShortExact)
    [IsFlat 𝒪 S.X₃] :
    (S.map (tensorLeft X)).ShortExact := by
  let hRight : (S.map (tensorRight X)).ShortExact :=
    shortExact_tensor_right_of_flat_quotient (J := J) (𝒢 := X) (S := S) hS
  -- Proof comment: transport the right-tensor short exact sequence through the braided
  -- comparison `tensorLeft X ≅ tensorRight X`.
  exact
    (shortExact_iff_of_functor_iso
      (e := CategoryTheory.BraidedCategory.tensorLeftIsoTensorRight X) S).2 hRight

/-- Helper for Lemma 18.28.10: if the left and right terms of `S` are flat, then tensoring any
short exact row `T` by the middle term of `S` stays short exact. -/
private theorem tensorMiddleShortExactOfFlatEnds
    (hS : S.ShortExact)
    [IsFlat 𝒪 S.X₃] [IsFlat 𝒪 S.X₁]
    (T : ShortComplex (Mod(𝒪)))
    (hT : T.ShortExact) :
    (T.map (tensorRight S.X₂)).ShortExact := by
  let row₁ : (S.map (tensorLeft T.X₁)).ShortExact :=
    shortExact_tensorLeft_of_flatQuotient (𝒪 := 𝒪) (S := S) T.X₁ hS
  let row₂ : (S.map (tensorLeft T.X₂)).ShortExact :=
    shortExact_tensorLeft_of_flatQuotient (𝒪 := 𝒪) (S := S) T.X₂ hS
  let col₁ : (T.map (tensorRight S.X₁)).ShortExact :=
    shortExact_map_tensorRight_of_isFlat (𝒪 := 𝒪) S.X₁ T hT
  let col₃ : (T.map (tensorRight S.X₃)).ShortExact :=
    shortExact_map_tensorRight_of_isFlat (𝒪 := 𝒪) S.X₃ T hT
  let rowMap :
      S.map (tensorLeft T.X₁) ⟶ S.map (tensorLeft T.X₂) :=
    S.mapNatTrans
      ((CategoryTheory.MonoidalCategory.tensoringLeft (Mod(𝒪))).map T.f)
  have hMiddleMono : Mono ((tensorRight S.X₂).map T.f) := by
    -- Proof comment: the two tensor rows are short exact, and the outer tensor columns are mono
    -- on the left map, so the four lemma upgrades the middle tensor column to a monomorphism.
    let _ : Mono rowMap.τ₁ := by
      simpa [rowMap] using col₁.mono_f
    let _ : Mono rowMap.τ₃ := by
      simpa [rowMap] using col₃.mono_f
    simpa [rowMap] using
      (CategoryTheory.shortComplex_middle_mono_of_outer_mono rowMap row₁ row₂)
  let hExactEpi := tensorRight_mapsShortExact_to_exact_epi (𝒪 := 𝒪) S.X₂ T hT
  -- Proof comment: right exactness supplies exactness and the epimorphic right map, while the
  -- four lemma supplies the missing monomorphism on the left map.
  exact ShortComplex.ShortExact.mk'
    ((T.map (tensorRight S.X₂)).exact_iff_exact_toComposableArrows.2 hExactEpi.1)
    hMiddleMono
    hExactEpi.2

/-- Helper for Lemma 18.28.10: if the middle and right terms of `S` are flat, then tensoring any
short exact row `T` by the left term of `S` stays short exact. -/
private theorem tensorLeftTermShortExactOfFlatMiddleRight
    (hS : S.ShortExact)
    [IsFlat 𝒪 S.X₃] [IsFlat 𝒪 S.X₂]
    (T : ShortComplex (Mod(𝒪)))
    (hT : T.ShortExact) :
    (T.map (tensorRight S.X₁)).ShortExact := by
  let row₁ : (S.map (tensorLeft T.X₁)).ShortExact :=
    shortExact_tensorLeft_of_flatQuotient (𝒪 := 𝒪) (S := S) T.X₁ hS
  let row₂ : (S.map (tensorLeft T.X₂)).ShortExact :=
    shortExact_tensorLeft_of_flatQuotient (𝒪 := 𝒪) (S := S) T.X₂ hS
  let middleCol : (T.map (tensorRight S.X₂)).ShortExact :=
    shortExact_map_tensorRight_of_isFlat (𝒪 := 𝒪) S.X₂ T hT
  let rowMap :
      S.map (tensorLeft T.X₁) ⟶ S.map (tensorLeft T.X₂) :=
    S.mapNatTrans
      ((CategoryTheory.MonoidalCategory.tensoringLeft (Mod(𝒪))).map T.f)
  have hLeftMono : Mono ((tensorRight S.X₁).map T.f) := by
    -- Proof comment: the first row map factors through the monomorphism in the middle tensor
    -- column, so cancellation along the second row identifies the left tensor column as mono.
    let _ : Mono rowMap.τ₂ := by
      simpa [rowMap] using middleCol.mono_f
    let _ : Mono (S.map (tensorLeft T.X₁)).f := row₁.mono_f
    have hCompFac :
        rowMap.τ₁ ≫ (S.map (tensorLeft T.X₂)).f =
          (S.map (tensorLeft T.X₁)).f ≫ rowMap.τ₂ := by
      simpa using rowMap.comm₁₂
    have hCompMono : Mono ((S.map (tensorLeft T.X₁)).f ≫ rowMap.τ₂) :=
      CategoryTheory.mono_comp _ _
    let _ : Mono ((S.map (tensorLeft T.X₁)).f ≫ rowMap.τ₂) := hCompMono
    simpa [rowMap] using
      (show Mono rowMap.τ₁ from mono_of_mono_fac hCompFac)
  let hExactEpi := tensorRight_mapsShortExact_to_exact_epi (𝒪 := 𝒪) S.X₁ T hT
  -- Proof comment: right exactness again gives exactness and the epimorphic right map; the
  -- commuting square with the middle flat column supplies the monomorphism on the left.
  exact ShortComplex.ShortExact.mk'
    ((T.map (tensorRight S.X₁)).exact_iff_exact_toComposableArrows.2 hExactEpi.1)
    hLeftMono
    hExactEpi.2

-- Proof sketch: repeat the presheaf argument in `Mod(\mathcal O)`, using the sheaf version of
-- Lemma `18.28.9` to preserve short exactness under tensor product and the same snake-lemma
-- two-out-of-three argument for flatness.
/-- On a ringed site, if the right term of a short exact sequence of sheaves of
`\mathcal O`-modules is flat, then the left term is flat if and only if the middle term is flat. -/
theorem flat_iff_flat_of_shortExact
    (hS : S.ShortExact) [IsFlat 𝒪 S.X₃] :
    IsFlat 𝒪 S.X₁ ↔ IsFlat 𝒪 S.X₂ := by
  -- Route correction: the successful route is the same as in the presheaf case. Normalize the
  -- tensor rows through `tensorLeftIsoTensorRight`, use right exactness of `tensorRight` for the
  -- exact/epi half, and recover the missing monomorphism from the four lemma.
  constructor
  · intro h₁
    let _ : IsFlat 𝒪 S.X₁ := h₁
    -- Proof comment: tensor every short exact test row by `S.X₂`; right exactness gives the
    -- exact/epi part, and the four lemma forces the left map to be mono.
    exact isFlat_of_mapsShortExact (𝒪 := 𝒪) S.X₂ fun T hT ↦
      tensorMiddleShortExactOfFlatEnds (𝒪 := 𝒪) (S := S) hS T hT
  · intro h₂
    let _ : IsFlat 𝒪 S.X₂ := h₂
    -- Proof comment: tensor every short exact test row by `S.X₁`; the middle flat column makes
    -- the left tensor column monic, and right exactness supplies the rest.
    exact isFlat_of_mapsShortExact (𝒪 := 𝒪) S.X₁ fun T hT ↦
      tensorLeftTermShortExactOfFlatMiddleRight (𝒪 := 𝒪) (S := S) hS T hT

end SheafOfModules.RingedSite
