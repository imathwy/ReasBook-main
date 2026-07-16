import Mathlib
import Mathlib.CategoryTheory.Distributive.Monoidal
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.CategoryTheory.Monoidal.Preadditive
import stacks_proof.stacks_project.Chap12.Lemma_12_7_2
import stacks_proof.stacks_project.Chap18.Definition_18_28_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory MonoidalCategory Opposite
open scoped PresheafOfModules.Monoidal

noncomputable section

universe u

namespace CategoryTheory

/-- Helper for Lemma 18.28.11: short exactness of a mapped short complex is invariant under a
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
  -- Proof comment: compare the two mapped short complexes termwise using the functor
  -- isomorphism.
  let i : T.map F ≅ T.map G :=
    ShortComplex.isoMk
      (e.app T.X₁)
      (e.app T.X₂)
      (e.app T.X₃)
      (by simpa using e.hom.naturality T.f)
      (by simpa using e.hom.naturality T.g)
  constructor
  · -- Proof comment: transport short exactness forward across the induced short-complex
    -- isomorphism.
    intro h
    exact ShortComplex.shortExact_of_iso i h
  · -- Proof comment: transport short exactness backward along the inverse isomorphism.
    intro h
    exact ShortComplex.shortExact_of_iso i.symm h

/-- Helper for Lemma 18.28.11: in a morphism of short exact rows, monicity of the two outer
vertical maps forces monicity of the middle vertical map by the four lemma. -/
private theorem shortComplex_middle_mono_of_outer_mono
    {A : Type*} [Category A] [Abelian A]
    {R₁ R₂ : ShortComplex A}
    (φ : R₁ ⟶ R₂)
    (hR₁ : R₁.ShortExact)
    (hR₂ : R₂.ShortExact)
    [Mono φ.τ₁] [Mono φ.τ₃] :
    Mono φ.τ₂ := by
  -- Proof comment: chase a morphism killed by the middle vertical map through the exact left row,
  -- then cancel successively against the right and left outer monomorphisms.
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

namespace ShortComplex

variable {A : Type*} [Category A] [Abelian A]

/-- Helper for Lemma 18.28.11: the image inclusion of the left map factors through the image of
the right map in any short complex. -/
private theorem imageCompFactorThruImage_eq_zero
    (S : ShortComplex A) :
    Abelian.image.ι S.f ≫ Abelian.factorThruImage S.g = 0 := by
  -- Proof comment: postcompose with the mono image inclusion of `S.g` and recover the original
  -- short-complex relation `S.f ≫ S.g = 0`.
  apply (cancel_mono (Abelian.image.ι S.g)).1
  simpa [Category.assoc, Abelian.image.fac] using S.zero

/-- Helper for Lemma 18.28.11: after applying a zero-morphism-preserving functor, the left map of
the short complex still factors through the image of the right map. -/
private theorem mapImageCompFactorThruImage_eq_zero
    {B : Type*} [Category B] [CategoryTheory.Limits.HasZeroMorphisms B]
    {F : A ⥤ B} [F.PreservesZeroMorphisms]
    (S : ShortComplex A) :
    F.map (Abelian.image.ι S.f) ≫ F.map (Abelian.factorThruImage S.g) = 0 := by
  -- Proof comment: map the already-vanishing image-factor composite through `F`.
  rw [← F.map_comp, imageCompFactorThruImage_eq_zero, Functor.map_zero]

/-- Helper for Lemma 18.28.11: after applying a zero-morphism-preserving functor, the left map of
the short complex still factors through the image of the right map. -/
private theorem mapCompFactorThruImage_eq_zero
    {B : Type*} [Category B] [CategoryTheory.Limits.HasZeroMorphisms B]
    {F : A ⥤ B} [F.PreservesZeroMorphisms]
    (S : ShortComplex A) :
    F.map S.f ≫ F.map (Abelian.factorThruImage S.g) = 0 := by
  -- Proof comment: first factor `S.f` through its image, then use the previous vanishing
  -- image-factor composite.
  have h :
      S.f ≫ Abelian.factorThruImage S.g = 0 := by
    calc
      S.f ≫ Abelian.factorThruImage S.g =
          Abelian.factorThruImage S.f ≫
            (Abelian.image.ι S.f ≫ Abelian.factorThruImage S.g) := by
              simp [Category.assoc, Abelian.image.fac]
      _ = 0 := by
        simp [imageCompFactorThruImage_eq_zero, Category.assoc]
  simpa [Functor.map_comp] using congrArg F.map h

/-- Helper for Lemma 18.28.11: exactness of a short complex transports to the row
`im(f) ⟶ X₂ ⟶ im(g)`. -/
private theorem exactImageFactorRowOfExact
    (S : ShortComplex A)
    (hS : S.Exact) :
    (ShortComplex.mk
      (Abelian.image.ι S.f)
      (Abelian.factorThruImage S.g)
      (imageCompFactorThruImage_eq_zero S)).Exact := by
  let T : ShortComplex A :=
    ShortComplex.mk
      (Abelian.image.ι S.f)
      S.g
      (Abelian.image_ι_comp_eq_zero S.zero)
  let U : ShortComplex A :=
    ShortComplex.mk
      (Abelian.image.ι S.f)
      (Abelian.factorThruImage S.g)
      (imageCompFactorThruImage_eq_zero S)
  have hT : T.Exact := by
    -- Proof comment: exactness of `S` is equivalent to exactness after replacing the left map by
    -- its image inclusion.
    simpa [T] using (ShortComplex.exact_iff_exact_image_ι S).1 hS
  let φ : U ⟶ T :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := Abelian.image.ι S.g
      comm₁₂ := by
        simp [T, U]
      comm₂₃ := by
        simpa [T, U] using (Abelian.image.fac S.g).symm }
  haveI : Epi φ.τ₁ := by
    dsimp [φ]
    infer_instance
  haveI : IsIso φ.τ₂ := by
    dsimp [φ]
    infer_instance
  haveI : Mono φ.τ₃ := by
    dsimp [φ]
    infer_instance
  -- Proof comment: replacing `S.g` by its factor-through-image only changes the right map by the
  -- canonical mono image inclusion.
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 hT

/-- Helper for Lemma 18.28.11: exactness of a mapped image-factor row transports back to
exactness of the original mapped short complex, once the mapped factorization maps have the
expected epi/mono properties. -/
private theorem exactOfMappedImageFactorRow
    {B : Type*} [Category B] [CategoryTheory.Limits.HasZeroMorphisms B]
    {F : A ⥤ B} [F.PreservesZeroMorphisms]
    (S : ShortComplex A)
    (hU :
      (ShortComplex.mk
        (F.map (Abelian.image.ι S.f))
        (F.map (Abelian.factorThruImage S.g))
        (mapImageCompFactorThruImage_eq_zero (F := F) S)).Exact)
    [Epi (F.map (Abelian.factorThruImage S.f))]
    [Mono (F.map (Abelian.image.ι S.g))] :
    (S.map F).Exact := by
  let U : ShortComplex B :=
    ShortComplex.mk
      (F.map (Abelian.image.ι S.f))
      (F.map (Abelian.factorThruImage S.g))
      (mapImageCompFactorThruImage_eq_zero (F := F) S)
  let W : ShortComplex B :=
    ShortComplex.mk
      (F.map S.f)
      (F.map (Abelian.factorThruImage S.g))
      (mapCompFactorThruImage_eq_zero (F := F) S)
  let D : ShortComplex B := S.map F
  let φ : W ⟶ U :=
    { τ₁ := F.map (Abelian.factorThruImage S.f)
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by
        rw [Category.comp_id, ← F.map_comp]
        simpa [W, U] using Abelian.image.fac S.f
      comm₂₃ := by
        simp [W, U] }
  haveI : Epi φ.τ₁ := by
    dsimp [φ]
    infer_instance
  haveI : IsIso φ.τ₂ := by
    dsimp [φ]
    infer_instance
  haveI : Mono φ.τ₃ := by
    dsimp [φ]
    infer_instance
  have hW : W.Exact := by
    -- Proof comment: predecessor surjectivity upgrades the left map from the image inclusion to
    -- the original mapped differential.
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 (by simpa [U] using hU)
  let ψ : W ⟶ D :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := F.map (Abelian.image.ι S.g)
      comm₁₂ := by
        simp [W, D]
      comm₂₃ := by
        simpa [W, D, Functor.map_comp] using
          (congrArg F.map (Abelian.image.fac S.g)).symm }
  haveI : Epi ψ.τ₁ := by
    change Epi (𝟙 W.X₁)
    infer_instance
  haveI : IsIso ψ.τ₂ := by
    change IsIso (𝟙 W.X₂)
    infer_instance
  haveI : Mono ψ.τ₃ := by
    simpa [ψ] using (inferInstance : Mono (F.map (Abelian.image.ι S.g)))
  -- Proof comment: postcompose with the mapped image inclusion of `S.g` to recover the actual
  -- mapped differential row.
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ).1 hW

end ShortComplex

end CategoryTheory

namespace PresheafOfModules

variable {C : Type u} [Category.{u} C]
variable {𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}}

/-- Helper for Lemma 18.28.11: tensoring presheaf modules on the right by a fixed module
preserves zero morphisms. -/
instance tensorRight_preservesZeroMorphisms
    (X : PresheafOfModules (ringPresheaf 𝒪)) :
    (tensorRight X).PreservesZeroMorphisms := by
  -- Proof comment: `tensorRight X` is additive, so it preserves zero morphisms formally.
  let _ : (tensorRight X).Additive := CategoryTheory.MonoidalCategory.tensorRight_additive X
  exact Functor.preservesZeroMorphisms_of_additive (tensorRight X)

/-- Helper for Lemma 18.28.11: if the tensor factor is flat, then right tensoring preserves short
exact sequences of presheaf modules. -/
private theorem shortExact_map_tensorRight_of_isFlat
    (X : PresheafOfModules (ringPresheaf 𝒪))
    [IsFlat X]
    (T : ShortComplex (PresheafOfModules (ringPresheaf 𝒪)))
    (hT : T.ShortExact) :
    (T.map (tensorRight X)).ShortExact := by
  -- Proof comment: this is exactly the defining exactness property packaged in `IsFlat X`.
  let hExact := IsFlat.exact_tensor (ℱ := X)
  let _ : CategoryTheory.Limits.PreservesFiniteLimits (tensorRight X) :=
    (CategoryTheory.exactFunctor_iff (tensorRight X)).1 hExact |>.1
  let _ : CategoryTheory.Limits.PreservesFiniteColimits (tensorRight X) :=
    (CategoryTheory.exactFunctor_iff (tensorRight X)).1 hExact |>.2
  exact hT.map_of_exact (tensorRight X)

/-- Helper for Lemma 18.28.11: right tensoring is always right exact, so it carries a short exact
sequence to an exact sequence whose right map remains an epimorphism. -/
private theorem tensorRight_mapsShortExact_to_exact_epi
    (X : PresheafOfModules (ringPresheaf 𝒪))
    (T : ShortComplex (PresheafOfModules (ringPresheaf 𝒪)))
    (hT : T.ShortExact) :
    (ComposableArrows.mk₂ ((tensorRight X).map T.f) ((tensorRight X).map T.g)).Exact ∧
      Epi ((tensorRight X).map T.g) := by
  let hRight :
      CategoryTheory.rightExactFunctor
        (PresheafOfModules (ringPresheaf 𝒪))
        (PresheafOfModules (ringPresheaf 𝒪))
        (tensorRight X) := by
    simpa [CategoryTheory.rightExactFunctor_iff] using
      (inferInstance :
        CategoryTheory.Limits.PreservesFiniteColimits (tensorRight X))
  -- Proof comment: the Chapter 12 right-exactness criterion supplies the exact/epi package.
  exact
    (CategoryTheory.functor_rightExact_iff_maps_shortExact_to_exact_epi
      (A := PresheafOfModules (ringPresheaf 𝒪))
      (B := PresheafOfModules (ringPresheaf 𝒪))
      (F := tensorRight X)).1 hRight T hT

/-- Helper for Lemma 18.28.11: flatness of `X` makes left tensoring exact via the braided
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

/-- Helper for Lemma 18.28.11: if `X` is flat, then tensoring a short exact sequence on the left
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

/-- Helper for Lemma 18.28.11: left tensoring is always right exact, so it carries a short exact
sequence to an exact sequence whose right map remains an epimorphism. -/
private theorem tensorLeft_mapsShortExact_to_exact_epi
    (X : PresheafOfModules (ringPresheaf 𝒪))
    (T : ShortComplex (PresheafOfModules (ringPresheaf 𝒪)))
    (hT : T.ShortExact) :
    (ComposableArrows.mk₂ ((tensorLeft X).map T.f) ((tensorLeft X).map T.g)).Exact ∧
      Epi ((tensorLeft X).map T.g) := by
  let e := CategoryTheory.BraidedCategory.tensorLeftIsoTensorRight X
  let _ : CategoryTheory.Limits.PreservesFiniteColimits (tensorLeft X) :=
    CategoryTheory.Limits.preservesFiniteColimits_of_natIso e.symm
  let hRight :
      CategoryTheory.rightExactFunctor
        (PresheafOfModules (ringPresheaf 𝒪))
        (PresheafOfModules (ringPresheaf 𝒪))
        (tensorLeft X) := by
    simpa [CategoryTheory.rightExactFunctor_iff] using
      (inferInstance :
        CategoryTheory.Limits.PreservesFiniteColimits (tensorLeft X))
  -- Proof comment: braiding identifies left tensor with the standard right-exact tensor-right
  -- functor.
  exact
    (CategoryTheory.functor_rightExact_iff_maps_shortExact_to_exact_epi
      (A := PresheafOfModules (ringPresheaf 𝒪))
      (B := PresheafOfModules (ringPresheaf 𝒪))
      (F := tensorLeft X)).1 hRight T hT

/-- Helper for Lemma 18.28.11: the flat-cover proof reduces tensor preservation of short
exactness to monicity of the tensorized left map. -/
private theorem tensorRightLeftMono_of_flat_cover
    {𝒢 𝒢' : PresheafOfModules (ringPresheaf 𝒪)}
    (π : 𝒢' ⟶ 𝒢)
    [Epi π] [IsFlat 𝒢']
    (S : ShortComplex (PresheafOfModules (ringPresheaf 𝒪)))
    (hS : S.ShortExact)
    [IsFlat S.X₃] :
    Mono ((tensorRight 𝒢).map S.f) := by
  let T : ShortComplex (PresheafOfModules (ringPresheaf 𝒪)) := ShortComplex.kernelSequence π
  have hT : T.ShortExact := by
    -- Proof comment: the flat cover is the canonical short exact kernel sequence of `π`.
    exact ShortComplex.ShortExact.mk'
      (ShortComplex.kernelSequence_exact π) inferInstance inferInstance
  let hRowGp : (S.map (tensorRight 𝒢')).ShortExact :=
    shortExact_map_tensorRight_of_isFlat (𝒪 := 𝒪) 𝒢' S hS
  let hRowK := tensorRight_mapsShortExact_to_exact_epi (𝒪 := 𝒪) T.X₁ S hS
  let hCol₁ := tensorLeft_mapsShortExact_to_exact_epi (𝒪 := 𝒪) S.X₁ T hT
  let hCol₂ := tensorLeft_mapsShortExact_to_exact_epi (𝒪 := 𝒪) S.X₂ T hT
  let hCol₃ : (T.map (tensorLeft S.X₃)).ShortExact :=
    shortExact_map_tensorLeft_of_isFlat (𝒪 := 𝒪) S.X₃ T hT
  let colMap₁₂ :
      T.map (tensorLeft S.X₁) ⟶ T.map (tensorLeft S.X₂) :=
    T.mapNatTrans
      ((CategoryTheory.MonoidalCategory.tensoringLeft
        (PresheafOfModules (ringPresheaf 𝒪))).map S.f)
  let colMap₂₃ :
      T.map (tensorLeft S.X₂) ⟶ T.map (tensorLeft S.X₃) :=
    T.mapNatTrans
      ((CategoryTheory.MonoidalCategory.tensoringLeft
        (PresheafOfModules (ringPresheaf 𝒪))).map S.g)
  let k₁ : ((T.map (tensorLeft S.X₁)).X₁) ⟶ ((T.map (tensorLeft S.X₁)).X₂) :=
    (tensorLeft S.X₁).map T.f
  let k₂ : ((T.map (tensorLeft S.X₂)).X₁) ⟶ ((T.map (tensorLeft S.X₂)).X₂) :=
    (tensorLeft S.X₂).map T.f
  let k₃ : ((T.map (tensorLeft S.X₃)).X₁) ⟶ ((T.map (tensorLeft S.X₃)).X₂) :=
    (tensorLeft S.X₃).map T.f
  let π₁ : ((T.map (tensorLeft S.X₁)).X₂) ⟶ ((T.map (tensorLeft S.X₁)).X₃) :=
    (tensorLeft S.X₁).map T.g
  let π₂ : ((T.map (tensorLeft S.X₂)).X₂) ⟶ ((T.map (tensorLeft S.X₂)).X₃) :=
    (tensorLeft S.X₂).map T.g
  let π₃ : ((T.map (tensorLeft S.X₃)).X₂) ⟶ ((T.map (tensorLeft S.X₃)).X₃) :=
    (tensorLeft S.X₃).map T.g
  let fK : ((S.map (tensorRight T.X₁)).X₁) ⟶ ((S.map (tensorRight T.X₁)).X₂) :=
    (tensorRight T.X₁).map S.f
  let fGp : ((S.map (tensorRight T.X₂)).X₁) ⟶ ((S.map (tensorRight T.X₂)).X₂) :=
    (tensorRight T.X₂).map S.f
  let fG : ((S.map (tensorRight T.X₃)).X₁) ⟶ ((S.map (tensorRight T.X₃)).X₂) :=
    (tensorRight T.X₃).map S.f
  let gK : ((S.map (tensorRight T.X₁)).X₂) ⟶ ((S.map (tensorRight T.X₁)).X₃) :=
    (tensorRight T.X₁).map S.g
  let gGp : ((S.map (tensorRight T.X₂)).X₂) ⟶ ((S.map (tensorRight T.X₂)).X₃) :=
    (tensorRight T.X₂).map S.g
  -- Proof comment: chase a refined lift through the flat-cover columns; the flat `𝒢'` row gives
  -- the key monomorphism, and the flat `S.X₃` column forces the correction term to come from the
  -- kernel row.
  rw [Preadditive.mono_iff_cancel_zero]
  intro A x hx
  obtain ⟨A₁, ρ₁, _hρ₁, x', hx'⟩ := surjective_up_to_refinements_of_epi π₁ x
  have hx'fπ : x' ≫ fGp ≫ π₂ = 0 := by
    calc
      x' ≫ fGp ≫ π₂ = x' ≫ π₁ ≫ fG := by
        simpa [colMap₁₂, fGp, fG, π₁, π₂, Category.assoc] using colMap₁₂.comm₂₃.symm
      _ = ρ₁ ≫ x ≫ fG := by
        simpa [fG, Category.assoc] using congrArg (fun t ↦ t ≫ fG) hx'
      _ = 0 := by
        simpa [fG, Category.assoc] using congrArg (fun t ↦ ρ₁ ≫ t) hx
  have hCol₂Exact : (T.map (tensorLeft S.X₂)).Exact :=
    (T.map (tensorLeft S.X₂)).exact_iff_exact_toComposableArrows.2 hCol₂.1
  obtain ⟨A₂, ρ₂, _hρ₂, y₂, hy₂⟩ := hCol₂Exact.exact_up_to_refinements (x' ≫ fGp) hx'fπ
  have hy₂gk₃ : y₂ ≫ gK ≫ k₃ = 0 := by
    calc
      y₂ ≫ gK ≫ k₃ = y₂ ≫ k₂ ≫ gGp := by
        simpa [colMap₂₃, gK, gGp, k₂, k₃, Category.assoc] using colMap₂₃.comm₁₂
      _ = ρ₂ ≫ x' ≫ fGp ≫ gGp := by
        simpa [gGp, Category.assoc] using congrArg (fun t ↦ t ≫ gGp) hy₂
      _ = 0 := by
        simpa [fGp, gGp, T, Category.assoc] using congrArg (fun t ↦ ρ₂ ≫ x' ≫ t)
          (S.map (tensorRight T.X₂)).zero
  have hy₂gk : y₂ ≫ gK = 0 := by
    exact (cancel_mono k₃).1 (by simpa [gK, k₃, Category.assoc] using hy₂gk₃)
  have hRowKExact : (S.map (tensorRight T.X₁)).Exact :=
    (S.map (tensorRight T.X₁)).exact_iff_exact_toComposableArrows.2 hRowK.1
  obtain ⟨A₃, ρ₃, _hρ₃, y₁, hy₁⟩ := hRowKExact.exact_up_to_refinements y₂ hy₂gk
  have hLiftEqComp : ρ₃ ≫ ρ₂ ≫ x' ≫ fGp = y₁ ≫ k₁ ≫ fGp := by
    calc
      ρ₃ ≫ ρ₂ ≫ x' ≫ fGp = ρ₃ ≫ y₂ ≫ k₂ := by
        simpa [fGp, k₂, Category.assoc] using congrArg (fun t ↦ ρ₃ ≫ t) hy₂.symm
      _ = y₁ ≫ fK ≫ k₂ := by
        simpa [fK, Category.assoc] using congrArg (fun t ↦ t ≫ k₂) hy₁
      _ = y₁ ≫ k₁ ≫ fGp := by
        simpa [colMap₁₂, fK, fGp, k₁, k₂, Category.assoc] using
          congrArg (fun t ↦ y₁ ≫ t) colMap₁₂.comm₁₂.symm
  have hLiftEq : ρ₃ ≫ ρ₂ ≫ x' = y₁ ≫ k₁ := by
    exact (cancel_mono fGp).1 (by simpa [fGp, Category.assoc] using hLiftEqComp)
  have hRefinedZero : ρ₃ ≫ ρ₂ ≫ ρ₁ ≫ x = 0 := by
    calc
      ρ₃ ≫ ρ₂ ≫ ρ₁ ≫ x = ρ₃ ≫ ρ₂ ≫ x' ≫ π₁ := by
        simpa [π₁, Category.assoc] using congrArg (fun t ↦ ρ₃ ≫ ρ₂ ≫ t) hx'.symm
      _ = y₁ ≫ k₁ ≫ π₁ := by
        simpa [π₁, Category.assoc] using congrArg (fun t ↦ t ≫ π₁) hLiftEq
      _ = 0 := by
        simpa [k₁, π₁, T, Category.assoc] using congrArg ((tensorLeft S.X₁).map) T.zero
  exact
    (cancel_epi ρ₁).1 <|
      (cancel_epi ρ₂).1 <|
        (cancel_epi ρ₃).1 <|
          by simpa [Category.assoc] using hRefinedZero

/-- Helper for Lemma 18.28.11: tensoring a short exact row on the right preserves short
exactness when the quotient is flat. -/
private theorem shortExactTensorRightOfFlatQuotientKernel
    (𝒢 : PresheafOfModules (ringPresheaf 𝒪))
    (S : ShortComplex (PresheafOfModules (ringPresheaf 𝒪)))
    (hS : S.ShortExact)
    [IsFlat S.X₃] :
    (S.map (tensorRight 𝒢)).ShortExact := by
  obtain ⟨𝒢', _h𝒢', π, hπ⟩ := exists_epi_from_flat (𝒪 := 𝒪) 𝒢
  let _ : Epi π := hπ
  have hMono :
      Mono ((tensorRight 𝒢).map S.f) :=
    tensorRightLeftMono_of_flat_cover (𝒪 := 𝒪) (π := π) S hS
  let hExactEpi := tensorRight_mapsShortExact_to_exact_epi (𝒪 := 𝒪) 𝒢 S hS
  -- Proof comment: right exactness supplies exactness and the epimorphic right map, and the
  -- flat-cover mono chase supplies the missing monomorphism on the left map.
  exact ShortComplex.ShortExact.mk'
    ((S.map (tensorRight 𝒢)).exact_iff_exact_toComposableArrows.2 hExactEpi.1)
    hMono
    hExactEpi.2

/-- Helper for Lemma 18.28.11: if tensoring on the right by `X` sends every short exact sequence
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

/-- Helper for Lemma 18.28.11: the short exactness statement above can be rewritten with left
tensoring using the braiding isomorphism. -/
private theorem shortExact_tensorLeft_of_flatQuotient
    (X : PresheafOfModules (ringPresheaf 𝒪))
    {S : ShortComplex (PresheafOfModules (ringPresheaf 𝒪))}
    (hS : S.ShortExact)
    [IsFlat S.X₃] :
    (S.map (tensorLeft X)).ShortExact := by
  let hRight : (S.map (tensorRight X)).ShortExact :=
    shortExactTensorRightOfFlatQuotientKernel (𝒪 := 𝒪) X S hS
  -- Proof comment: transport the right-tensor short exact sequence through the braided
  -- comparison `tensorLeft X ≅ tensorRight X`.
  exact
    (CategoryTheory.shortExact_iff_of_functor_iso
      (e := CategoryTheory.BraidedCategory.tensorLeftIsoTensorRight X) S).2 hRight

/-- Helper for Lemma 18.28.11: if the left and right terms are flat, then tensoring any short
exact row by the middle term stays short exact. -/
private theorem tensorMiddleShortExactOfFlatEnds
    {S : ShortComplex (PresheafOfModules (ringPresheaf 𝒪))}
    (hS : S.ShortExact)
    [IsFlat S.X₃] [IsFlat S.X₁]
    (T : ShortComplex (PresheafOfModules (ringPresheaf 𝒪)))
    (hT : T.ShortExact) :
    (T.map (tensorRight S.X₂)).ShortExact := by
  let row₁ : (S.map (tensorLeft T.X₁)).ShortExact :=
    shortExact_tensorLeft_of_flatQuotient (𝒪 := 𝒪) T.X₁ hS
  let row₂ : (S.map (tensorLeft T.X₂)).ShortExact :=
    shortExact_tensorLeft_of_flatQuotient (𝒪 := 𝒪) T.X₂ hS
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

/-- Helper for Lemma 18.28.11: if the middle and right terms are flat, then tensoring any short
exact row by the left term stays short exact. -/
private theorem tensorLeftTermShortExactOfFlatMiddleRight
    {S : ShortComplex (PresheafOfModules (ringPresheaf 𝒪))}
    (hS : S.ShortExact)
    [IsFlat S.X₃] [IsFlat S.X₂]
    (T : ShortComplex (PresheafOfModules (ringPresheaf 𝒪)))
    (hT : T.ShortExact) :
    (T.map (tensorRight S.X₁)).ShortExact := by
  let row₁ : (S.map (tensorLeft T.X₁)).ShortExact :=
    shortExact_tensorLeft_of_flatQuotient (𝒪 := 𝒪) T.X₁ hS
  let row₂ : (S.map (tensorLeft T.X₂)).ShortExact :=
    shortExact_tensorLeft_of_flatQuotient (𝒪 := 𝒪) T.X₂ hS
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

/-- Helper for Lemma 18.28.11: in a short exact row with flat quotient, flatness of the left term
is equivalent to flatness of the middle term. -/
private theorem flatIffFlatOfShortExactKernel
    {S : ShortComplex (PresheafOfModules (ringPresheaf 𝒪))}
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

/-- Helper for Lemma 18.28.11: in a short exact row with flat middle and flat quotient, the left
term is flat. -/
private theorem flatLeftOfShortExactOfFlatMiddleRight
    {S : ShortComplex (PresheafOfModules (ringPresheaf 𝒪))}
    (hS : S.ShortExact)
    [IsFlat S.X₃] [IsFlat S.X₂] :
    IsFlat S.X₁ := by
  -- Proof comment: this is exactly the backward implication of the local two-out-of-three
  -- flatness kernel replayed from Lemma `18.28.10`.
  exact (flatIffFlatOfShortExactKernel (𝒪 := 𝒪) (S := S) hS).2 inferInstance

/-- Helper for Lemma 18.28.11: tensoring a short exact presheaf row on the right preserves short
exactness when the cokernel is flat. -/
private theorem shortExact_tensor_right_of_flat_quotient
    (𝒢 : PresheafOfModules (ringPresheaf 𝒪))
    (S : ShortComplex (PresheafOfModules (ringPresheaf 𝒪)))
    (hS : S.ShortExact)
    [IsFlat S.X₃] :
    (S.map (tensorRight 𝒢)).ShortExact := by
  -- Proof comment: use the local flat-cover replay of Lemma `18.28.9`.
  exact shortExactTensorRightOfFlatQuotientKernel (𝒪 := 𝒪) 𝒢 S hS

/-- A right-augmented exact complex of presheaves of `\mathcal O`-modules
`\cdots \to \mathcal F_2 \to \mathcal F_1 \to \mathcal F_0 \to \mathcal Q \to 0`,
encoded by exactness at every displayed term and surjectivity of the augmentation. -/
structure RightAugmentedExact
    (ℱ : ℕ → PresheafOfModules (ringPresheaf 𝒪))
    (d : ∀ n : ℕ, ℱ (n + 1) ⟶ ℱ n)
    (𝒬 : PresheafOfModules (ringPresheaf 𝒪))
    (q : ℱ 0 ⟶ 𝒬) : Prop where
  /-- Consecutive differentials in the resolution part compose to zero. -/
  d_comp_d : ∀ n : ℕ, d (n + 1) ≫ d n = 0
  /-- The last differential composes trivially with the augmentation. -/
  d_comp_q : d 0 ≫ q = 0
  /-- Exactness at every term `\mathcal F_n` with `n ≥ 1`. -/
  exact_succ :
      ∀ n : ℕ,
        (ShortComplex.mk (d (n + 1)) (d n) (d_comp_d n)).Exact
  /-- Exactness at `\mathcal F_0`. -/
  exact_zero :
      (ShortComplex.mk (d 0) q d_comp_q).Exact
  /-- Exactness at `\mathcal Q`, equivalently surjectivity of the augmentation. -/
  epi_q : Epi q

/-- Helper for Lemma 18.28.11: the image of the last differential lands in the augmentation
kernel. -/
private theorem zeroImageComp_q
    (ℱ : ℕ → PresheafOfModules (ringPresheaf 𝒪))
    (d : ∀ n : ℕ, ℱ (n + 1) ⟶ ℱ n)
    {𝒬 : PresheafOfModules (ringPresheaf 𝒪)}
    (q : ℱ 0 ⟶ 𝒬)
    (hExact : RightAugmentedExact ℱ d 𝒬 q) :
    CategoryTheory.Abelian.image.ι (d 0) ≫ q = 0 := by
  -- Proof comment: postcompose the image inclusion with the augmentation and cancel the image
  -- factorization to recover the vanishing `d₀ ≫ q = 0`.
  apply (cancel_epi (CategoryTheory.Abelian.factorThruImage (d 0))).1
  simpa [Category.assoc, CategoryTheory.Abelian.image.fac] using hExact.d_comp_q

/-- Helper for Lemma 18.28.11: each interior image inclusion factors through the next image. -/
private theorem succImageComp_factor
    (ℱ : ℕ → PresheafOfModules (ringPresheaf 𝒪))
    (d : ∀ n : ℕ, ℱ (n + 1) ⟶ ℱ n)
    {𝒬 : PresheafOfModules (ringPresheaf 𝒪)}
    (q : ℱ 0 ⟶ 𝒬)
    (hExact : RightAugmentedExact ℱ d 𝒬 q)
    (n : ℕ) :
    CategoryTheory.Abelian.image.ι (d (n + 1)) ≫
        CategoryTheory.Abelian.factorThruImage (d n) = 0 := by
  -- Proof comment: after postcomposing with the mono image inclusion of `dₙ`, the composite
  -- becomes the already-vanishing differential composite `dₙ₊₁ ≫ dₙ`.
  apply (cancel_mono (CategoryTheory.Abelian.image.ι (d n))).1
  simpa [Category.assoc, CategoryTheory.Abelian.image.fac] using hExact.d_comp_d n

/-- Helper for Lemma 18.28.11: the augmentation row
`0 ⟶ im(d₀) ⟶ ℱ₀ ⟶ 𝒬 ⟶ 0` is short exact. -/
private abbrev zeroImageRow
    (ℱ : ℕ → PresheafOfModules (ringPresheaf 𝒪))
    (d : ∀ n : ℕ, ℱ (n + 1) ⟶ ℱ n)
    {𝒬 : PresheafOfModules (ringPresheaf 𝒪)}
    (q : ℱ 0 ⟶ 𝒬)
    (hExact : RightAugmentedExact ℱ d 𝒬 q) :
    ShortComplex (PresheafOfModules (ringPresheaf 𝒪)) :=
  ShortComplex.mk (CategoryTheory.Abelian.image.ι (d 0)) q
    (zeroImageComp_q ℱ d q hExact)

/-- Helper for Lemma 18.28.11: the recurring interior image-factor row
`0 ⟶ im(dₙ₊₁) ⟶ ℱₙ₊₁ ⟶ im(dₙ) ⟶ 0`. -/
private abbrev succImageRow
    (ℱ : ℕ → PresheafOfModules (ringPresheaf 𝒪))
    (d : ∀ n : ℕ, ℱ (n + 1) ⟶ ℱ n)
    {𝒬 : PresheafOfModules (ringPresheaf 𝒪)}
    (q : ℱ 0 ⟶ 𝒬)
    (hExact : RightAugmentedExact ℱ d 𝒬 q)
    (n : ℕ) :
    ShortComplex (PresheafOfModules (ringPresheaf 𝒪)) :=
  ShortComplex.mk (CategoryTheory.Abelian.image.ι (d (n + 1)))
    (CategoryTheory.Abelian.factorThruImage (d n))
    (succImageComp_factor ℱ d q hExact n)

/-- Helper for Lemma 18.28.11: the augmentation row
`0 ⟶ im(d₀) ⟶ ℱ₀ ⟶ 𝒬 ⟶ 0` is short exact. -/
private theorem zeroImageShortExact
    (ℱ : ℕ → PresheafOfModules (ringPresheaf 𝒪))
    (d : ∀ n : ℕ, ℱ (n + 1) ⟶ ℱ n)
    {𝒬 : PresheafOfModules (ringPresheaf 𝒪)}
    (q : ℱ 0 ⟶ 𝒬)
    (hExact : RightAugmentedExact ℱ d 𝒬 q) :
    (zeroImageRow ℱ d q hExact).ShortExact := by
  have hSExact : (zeroImageRow ℱ d q hExact).Exact := by
    -- Proof comment: exactness at `ℱ₀` is the image-formulation of the original augmentation row.
    simpa [zeroImageRow] using
      (ShortComplex.exact_iff_exact_image_ι
        (ShortComplex.mk (d 0) q (hExact.d_comp_q))).1 hExact.exact_zero
  -- Proof comment: combine exactness with the canonical mono image inclusion and the given
  -- surjectivity of the augmentation.
  exact ShortComplex.ShortExact.mk' hSExact inferInstance hExact.epi_q

/-- Helper for Lemma 18.28.11: each interior row
`0 ⟶ im(dₙ₊₁) ⟶ ℱₙ₊₁ ⟶ im(dₙ) ⟶ 0` is short exact. -/
private theorem succImageShortExact
    (ℱ : ℕ → PresheafOfModules (ringPresheaf 𝒪))
    (d : ∀ n : ℕ, ℱ (n + 1) ⟶ ℱ n)
    {𝒬 : PresheafOfModules (ringPresheaf 𝒪)}
    (q : ℱ 0 ⟶ 𝒬)
    (hExact : RightAugmentedExact ℱ d 𝒬 q)
    (n : ℕ) :
    (succImageRow ℱ d q hExact n).ShortExact := by
  let T : ShortComplex (PresheafOfModules (ringPresheaf 𝒪)) :=
    ShortComplex.mk (d (n + 1)) (d n) (hExact.d_comp_d n)
  have hSExact : (succImageRow ℱ d q hExact n).Exact := by
    -- Proof comment: exactness of the original differential row transports to its image-factor
    -- row through the shared `ShortComplex` bridge.
    simpa [succImageRow, T] using
      CategoryTheory.ShortComplex.exactImageFactorRowOfExact T (hExact.exact_succ n)
  -- Proof comment: the image inclusion is mono and the factor-through-image map is epi, so the
  -- exact image row is short exact.
  exact ShortComplex.ShortExact.mk' hSExact inferInstance inferInstance

/-- Helper for Lemma 18.28.11: every differential image in the resolution is flat. -/
private theorem flatImage
    (ℱ : ℕ → PresheafOfModules (ringPresheaf 𝒪))
    (d : ∀ n : ℕ, ℱ (n + 1) ⟶ ℱ n)
    {𝒬 : PresheafOfModules (ringPresheaf 𝒪)}
    (q : ℱ 0 ⟶ 𝒬)
    (hExact : RightAugmentedExact ℱ d 𝒬 q)
    [IsFlat 𝒬]
    [∀ n : ℕ, IsFlat (ℱ n)] :
    ∀ n : ℕ, IsFlat (CategoryTheory.Abelian.image (d n))
  := by
    intro n
    induction n with
    | zero =>
        let S := zeroImageRow ℱ d q hExact
        let _ : IsFlat S.X₃ := by
          simpa [S, zeroImageRow] using (inferInstance : IsFlat 𝒬)
        let _ : IsFlat S.X₂ := by
          simpa [S, zeroImageRow] using (inferInstance : IsFlat (ℱ 0))
        -- Proof comment: the base image row ends in the flat quotient `𝒬`, so the local
        -- flat-left lemma applies directly.
        simpa [S, zeroImageRow] using
          (flatLeftOfShortExactOfFlatMiddleRight (𝒪 := 𝒪)
            (S := S) (zeroImageShortExact ℱ d q hExact))
    | succ n ih =>
        let S := succImageRow ℱ d q hExact n
        let _ : IsFlat (CategoryTheory.Abelian.image (d n)) := ih
        let _ : IsFlat S.X₃ := by
          simpa [S, succImageRow] using
            (inferInstance : IsFlat (CategoryTheory.Abelian.image (d n)))
        let _ : IsFlat S.X₂ := by
          simpa [S, succImageRow] using (inferInstance : IsFlat (ℱ (n + 1)))
        -- Proof comment: the successor image row has flat middle `ℱ (n + 1)` and flat quotient
        -- `im(dₙ)`, so induction propagates flatness to `im(dₙ₊₁)`.
        simpa [S, succImageRow] using
          (flatLeftOfShortExactOfFlatMiddleRight (𝒪 := 𝒪)
            (S := S) (succImageShortExact ℱ d q hExact n))

/-- Helper for Lemma 18.28.11: tensoring preserves the vanishing of each differential composite in
the resolution. -/
private theorem tensorDCompD
    (ℱ : ℕ → PresheafOfModules (ringPresheaf 𝒪))
    (d : ∀ n : ℕ, ℱ (n + 1) ⟶ ℱ n)
    {𝒬 𝒢 : PresheafOfModules (ringPresheaf 𝒪)}
    (q : ℱ 0 ⟶ 𝒬)
    (hExact : RightAugmentedExact ℱ d 𝒬 q)
    (n : ℕ) :
    (tensorRight 𝒢).map (d (n + 1)) ≫ (tensorRight 𝒢).map (d n) = 0 := by
  -- Proof comment: apply the tensor-right functor to the already-zero differential composite.
  rw [← Functor.map_comp, hExact.d_comp_d, Functor.map_zero]

/-- Helper for Lemma 18.28.11: tensoring preserves the vanishing of the augmentation composite. -/
private theorem tensorDCompQ
    (ℱ : ℕ → PresheafOfModules (ringPresheaf 𝒪))
    (d : ∀ n : ℕ, ℱ (n + 1) ⟶ ℱ n)
    {𝒬 𝒢 : PresheafOfModules (ringPresheaf 𝒪)}
    (q : ℱ 0 ⟶ 𝒬)
    (hExact : RightAugmentedExact ℱ d 𝒬 q) :
    (tensorRight 𝒢).map (d 0) ≫ (tensorRight 𝒢).map q = 0 := by
  -- Proof comment: apply the tensor-right functor to the zero composite `d₀ ≫ q`.
  rw [← Functor.map_comp, hExact.d_comp_q, Functor.map_zero]

/-- Helper for Lemma 18.28.11: after tensoring on the right, each canonical image inclusion in
the split resolution rows is still monomorphic. -/
private theorem tensorImageInclusionMono
    (ℱ : ℕ → PresheafOfModules (ringPresheaf 𝒪))
    (d : ∀ n : ℕ, ℱ (n + 1) ⟶ ℱ n)
    {𝒬 𝒢 : PresheafOfModules (ringPresheaf 𝒪)}
    (q : ℱ 0 ⟶ 𝒬)
    (hExact : RightAugmentedExact ℱ d 𝒬 q)
    [IsFlat 𝒬]
    [∀ n : ℕ, IsFlat (ℱ n)]
    (n : ℕ) :
    Mono ((tensorRight 𝒢).map (CategoryTheory.Abelian.image.ι (d n))) := by
  cases n with
  | zero =>
      have hTensor :
          ((zeroImageRow ℱ d q hExact).map (tensorRight 𝒢)).ShortExact :=
        shortExact_tensor_right_of_flat_quotient (𝒢 := 𝒢)
          (S := zeroImageRow ℱ d q hExact) (zeroImageShortExact ℱ d q hExact)
      -- Proof comment: tensor the augmentation image row and read off monicity of its left map.
      simpa [zeroImageRow] using hTensor.mono_f
  | succ n =>
      let _ : IsFlat (CategoryTheory.Abelian.image (d n)) :=
        flatImage ℱ d q hExact n
      have hTensor :
          ((succImageRow ℱ d q hExact n).map (tensorRight 𝒢)).ShortExact :=
        shortExact_tensor_right_of_flat_quotient (𝒢 := 𝒢)
          (S := succImageRow ℱ d q hExact n) (succImageShortExact ℱ d q hExact n)
      -- Proof comment: tensor the successor image row and again extract monicity from the left
      -- edge of the short exact sequence.
      simpa [succImageRow] using hTensor.mono_f

/-- Helper for Lemma 18.28.11: exactness of the mapped image row transports back to the original
tensor differential row. -/
private theorem tensorSuccExactOfMappedImageRow
    (ℱ : ℕ → PresheafOfModules (ringPresheaf 𝒪))
    (d : ∀ n : ℕ, ℱ (n + 1) ⟶ ℱ n)
    {𝒬 𝒢 : PresheafOfModules (ringPresheaf 𝒪)}
    (q : ℱ 0 ⟶ 𝒬)
    (hExact : RightAugmentedExact ℱ d 𝒬 q)
    [IsFlat 𝒬]
    [∀ n : ℕ, IsFlat (ℱ n)]
    (n : ℕ) :
    (ShortComplex.mk
      ((tensorRight 𝒢).map (d (n + 1)))
      ((tensorRight 𝒢).map (d n))
      (tensorDCompD ℱ d (𝒢 := 𝒢) q hExact n)).Exact := by
  let S : ShortComplex (PresheafOfModules (ringPresheaf 𝒪)) :=
    ShortComplex.mk (d (n + 1)) (d n) (hExact.d_comp_d n)
  let U : ShortComplex (PresheafOfModules (ringPresheaf 𝒪)) :=
    succImageRow ℱ d q hExact n
  have hTensorU : (U.map (tensorRight 𝒢)).ShortExact :=
    shortExact_tensor_right_of_flat_quotient (𝒢 := 𝒢) (S := U)
      (succImageShortExact ℱ d q hExact n)
  let _ : IsFlat (CategoryTheory.Abelian.image (d n)) :=
    flatImage ℱ d q hExact n
  let _ : Mono ((tensorRight 𝒢).map (CategoryTheory.Abelian.image.ι (d n))) :=
    tensorImageInclusionMono ℱ d (𝒢 := 𝒢) q hExact n
  -- Proof comment: exactness of the tensorized image row transports back to the original
  -- tensorized differential row once the mapped image inclusion is known to be mono.
  simpa [S, U, succImageRow, tensorDCompD] using
    (CategoryTheory.ShortComplex.exactOfMappedImageFactorRow
      (F := tensorRight 𝒢) S hTensorU.exact)

/-- Helper for Lemma 18.28.11: tensoring the augmentation image row preserves exactness at the
degree-zero term. -/
private theorem tensorZeroExactOfImageRow
    (ℱ : ℕ → PresheafOfModules (ringPresheaf 𝒪))
    (d : ∀ n : ℕ, ℱ (n + 1) ⟶ ℱ n)
    {𝒬 𝒢 : PresheafOfModules (ringPresheaf 𝒪)}
    (q : ℱ 0 ⟶ 𝒬)
    (hExact : RightAugmentedExact ℱ d 𝒬 q)
    [IsFlat 𝒬] :
    (ShortComplex.mk
      ((tensorRight 𝒢).map (d 0))
      ((tensorRight 𝒢).map q)
      (tensorDCompQ ℱ d (𝒢 := 𝒢) q hExact)).Exact := by
  have hTensor :
      ((zeroImageRow ℱ d q hExact).map (tensorRight 𝒢)).ShortExact :=
    shortExact_tensor_right_of_flat_quotient (𝒢 := 𝒢)
      (S := zeroImageRow ℱ d q hExact) (zeroImageShortExact ℱ d q hExact)
  -- Proof comment: tensor the zero-image row, then convert its exactness back to the original
  -- augmentation row through `exact_iff_exact_image_ι`.
  simpa [zeroImageRow, tensorDCompQ] using
    (ShortComplex.exact_iff_exact_image_ι
      (ShortComplex.mk
        ((tensorRight 𝒢).map (d 0))
        ((tensorRight 𝒢).map q)
        (tensorDCompQ ℱ d (𝒢 := 𝒢) q hExact))).2 hTensor.exact

-- Proof sketch: split the augmented exact complex into the short exact sequences
-- `0 → im(d_{n+1}) → ℱ_n → im(d_n) → 0` and `0 → im(d_0) → ℱ_0 → 𝒬 → 0`. Apply Lemma
-- `18.28.9` to preserve each short exact sequence after tensoring with `𝒢`, and use Lemma
-- `18.28.10` inductively to show the successive images remain flat.
/-- Lemma 18.28.11 (1): if
`\cdots \to \mathcal F_2 \to \mathcal F_1 \to \mathcal F_0 \to \mathcal Q \to 0`
is an exact complex of flat presheaves of `\mathcal O`-modules, then tensoring on the right by
any presheaf `\mathcal G` again yields an exact right-augmented complex. -/
@[stacks 03EZ]
theorem rightAugmentedExact_tensor_right_of_flat
    (ℱ : ℕ → PresheafOfModules (ringPresheaf 𝒪))
    (d : ∀ n : ℕ, ℱ (n + 1) ⟶ ℱ n)
    {𝒬 𝒢 : PresheafOfModules (ringPresheaf 𝒪)}
    (q : ℱ 0 ⟶ 𝒬)
    (hExact : RightAugmentedExact ℱ d 𝒬 q)
    [IsFlat 𝒬]
    [∀ n : ℕ, IsFlat (ℱ n)] :
    RightAugmentedExact
      (fun n ↦ (tensorRight 𝒢).obj (ℱ n))
      (fun n ↦ (tensorRight 𝒢).map (d n))
      ((tensorRight 𝒢).obj 𝒬)
      ((tensorRight 𝒢).map q) := by
  refine
    ⟨
      tensorDCompD ℱ d (𝒢 := 𝒢) q hExact,
      tensorDCompQ ℱ d (𝒢 := 𝒢) q hExact,
      ?_,
      ?_,
      (shortExact_tensor_right_of_flat_quotient (𝒢 := 𝒢)
        (S := zeroImageRow ℱ d q hExact) (zeroImageShortExact ℱ d q hExact)).epi_g
    ⟩
  · intro n
    -- Proof comment: every successor row is exact by transport from the tensorized image row.
    exact tensorSuccExactOfMappedImageRow ℱ d (𝒢 := 𝒢) q hExact n
  · -- Proof comment: the degree-zero row is the augmentation specialization of the same tensor
    -- exactness argument.
    exact tensorZeroExactOfImageRow ℱ d (𝒢 := 𝒢) q hExact

end PresheafOfModules

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {𝒪 : Sheaf J CommRingCat.{u}}
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]

local notation "Mod(" 𝒪 ")" => ringedSiteModuleCategory J 𝒪

/-- Helper for Lemma 18.28.11: tensoring sheaf modules on the left by a fixed module preserves
zero morphisms. -/
instance tensorLeft_preservesZeroMorphisms
    (X : Mod(𝒪)) :
    (tensorLeft X).PreservesZeroMorphisms := by
  -- Proof comment: `tensorLeft X` is additive, so it preserves zero morphisms automatically.
  let _ : (tensorLeft X).Additive := CategoryTheory.MonoidalCategory.tensorLeft_additive X
  exact Functor.preservesZeroMorphisms_of_additive (tensorLeft X)

/-- Helper for Lemma 18.28.11: tensoring sheaf modules on the right by a fixed module preserves
zero morphisms. -/
instance tensorRight_preservesZeroMorphisms
    (X : Mod(𝒪)) :
    (tensorRight X).PreservesZeroMorphisms := by
  -- Proof comment: `tensorRight X` is additive, hence preserves zero morphisms.
  exact Functor.preservesZeroMorphisms_of_additive (tensorRight X)

/-- Helper for Lemma 18.28.11: if the tensor factor is flat, then right tensoring preserves short
exact sequences of sheaf modules. -/
private theorem shortExact_map_tensorRight_of_isFlat
    (X : Mod(𝒪))
    [IsFlat 𝒪 X]
    (T : ShortComplex (Mod(𝒪)))
    (hT : T.ShortExact) :
    (T.map (tensorRight X)).ShortExact := by
  -- Proof comment: flatness of `X` is defined by exactness of `tensorRight X`.
  let hExact := (inferInstance : IsFlat 𝒪 X).exact_tensor
  let _ : CategoryTheory.Limits.PreservesFiniteLimits (tensorRight X) :=
    (CategoryTheory.exactFunctor_iff (tensorRight X)).1 hExact |>.1
  let _ : CategoryTheory.Limits.PreservesFiniteColimits (tensorRight X) :=
    (CategoryTheory.exactFunctor_iff (tensorRight X)).1 hExact |>.2
  exact hT.map_of_exact (tensorRight X)

/-- Helper for Lemma 18.28.11: if tensoring on the right by `X` sends every short exact sequence
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

/-- Helper for Lemma 18.28.11: flatness of `X` makes left tensoring exact via the braided
comparison with right tensoring. -/
private theorem tensorLeft_exact_of_isFlat
    (X : Mod(𝒪))
    [IsFlat 𝒪 X] :
    exactFunctor
      (Mod(𝒪))
      (Mod(𝒪))
      (tensorLeft X) := by
  let hExact := (inferInstance : IsFlat 𝒪 X).exact_tensor
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

/-- Helper for Lemma 18.28.11: if `X` is flat, then tensoring a short exact sequence on the left
by `X` stays short exact. -/
private theorem shortExact_map_tensorLeft_of_isFlat
    (X : Mod(𝒪))
    [IsFlat 𝒪 X]
    (T : ShortComplex (Mod(𝒪)))
    (hT : T.ShortExact) :
    (T.map (tensorLeft X)).ShortExact := by
  -- Proof comment: once left tensoring is exact, mapped short exactness is immediate.
  let hExact := tensorLeft_exact_of_isFlat (𝒪 := 𝒪) X
  let _ : CategoryTheory.Limits.PreservesFiniteLimits (tensorLeft X) :=
    (CategoryTheory.exactFunctor_iff (tensorLeft X)).1 hExact |>.1
  let _ : CategoryTheory.Limits.PreservesFiniteColimits (tensorLeft X) :=
    (CategoryTheory.exactFunctor_iff (tensorLeft X)).1 hExact |>.2
  exact hT.map_of_exact (tensorLeft X)

/-- Helper for Lemma 18.28.11: right tensoring is always right exact, so it preserves exactness
and epimorphy of the right map in a short exact sequence. -/
private theorem tensorRight_mapsShortExact_to_exact_epi
    (X : Mod(𝒪))
    (T : ShortComplex (Mod(𝒪)))
    (hT : T.ShortExact) :
    (ComposableArrows.mk₂ ((tensorRight X).map T.f) ((tensorRight X).map T.g)).Exact ∧
      Epi ((tensorRight X).map T.g) := by
  let hRight :
      CategoryTheory.rightExactFunctor
        (Mod(𝒪))
        (Mod(𝒪))
        (tensorRight X) := by
    simpa [CategoryTheory.rightExactFunctor_iff] using
      (inferInstance : CategoryTheory.Limits.PreservesFiniteColimits (tensorRight X))
  -- Proof comment: use the standard right-exact functor criterion on short exact rows.
  exact
    (CategoryTheory.functor_rightExact_iff_maps_shortExact_to_exact_epi
      (A := Mod(𝒪))
      (B := Mod(𝒪))
      (F := tensorRight X)).1 hRight T hT

/-- Helper for Lemma 18.28.11: left tensoring is always right exact, so it carries a short exact
row to an exact row whose right map stays epi. -/
private theorem tensorLeft_mapsShortExact_to_exact_epi
    (X : Mod(𝒪))
    (T : ShortComplex (Mod(𝒪)))
    (hT : T.ShortExact) :
    (ComposableArrows.mk₂ ((tensorLeft X).map T.f) ((tensorLeft X).map T.g)).Exact ∧
      Epi ((tensorLeft X).map T.g) := by
  let e := CategoryTheory.BraidedCategory.tensorLeftIsoTensorRight X
  let _ : CategoryTheory.Limits.PreservesFiniteColimits (tensorLeft X) :=
    CategoryTheory.Limits.preservesFiniteColimits_of_natIso e.symm
  let hRight :
      CategoryTheory.rightExactFunctor
        (Mod(𝒪))
        (Mod(𝒪))
        (tensorLeft X) := by
    simpa [CategoryTheory.rightExactFunctor_iff] using
      (inferInstance :
        CategoryTheory.Limits.PreservesFiniteColimits (tensorLeft X))
  -- Proof comment: braiding again identifies left tensor with the standard right-exact functor.
  exact
    (CategoryTheory.functor_rightExact_iff_maps_shortExact_to_exact_epi
      (A := Mod(𝒪))
      (B := Mod(𝒪))
      (F := tensorLeft X)).1 hRight T hT

/-- Helper for Lemma 18.28.11: the sheaf flat-cover proof reduces tensor preservation of short
exactness to monicity of the tensorized left map. -/
private theorem sheafTensorRightLeftMono_of_flat_cover
    {𝒢 𝒢' : Mod(𝒪)}
    (π : 𝒢' ⟶ 𝒢)
    [Epi π] [IsFlat 𝒪 𝒢']
    (S : ShortComplex (Mod(𝒪)))
    (hS : S.ShortExact)
    [IsFlat 𝒪 S.X₃] :
    Mono ((tensorRight 𝒢).map S.f) := by
  let T : ShortComplex (Mod(𝒪)) := ShortComplex.kernelSequence π
  have hT : T.ShortExact := by
    -- Proof comment: use the canonical short exact kernel sequence of the flat cover.
    exact ShortComplex.ShortExact.mk'
      (ShortComplex.kernelSequence_exact π) inferInstance inferInstance
  let hRowGp : (S.map (tensorRight 𝒢')).ShortExact :=
    shortExact_map_tensorRight_of_isFlat (J := J) (𝒪 := 𝒪) 𝒢' S hS
  let hRowK := tensorRight_mapsShortExact_to_exact_epi (J := J) (𝒪 := 𝒪) T.X₁ S hS
  let hCol₁ := tensorLeft_mapsShortExact_to_exact_epi (J := J) (𝒪 := 𝒪) S.X₁ T hT
  let hCol₂ := tensorLeft_mapsShortExact_to_exact_epi (J := J) (𝒪 := 𝒪) S.X₂ T hT
  let hCol₃ : (T.map (tensorLeft S.X₃)).ShortExact :=
    shortExact_map_tensorLeft_of_isFlat (J := J) (𝒪 := 𝒪) S.X₃ T hT
  let colMap₁₂ :
      T.map (tensorLeft S.X₁) ⟶ T.map (tensorLeft S.X₂) :=
    T.mapNatTrans
      ((CategoryTheory.MonoidalCategory.tensoringLeft (Mod(𝒪))).map S.f)
  let colMap₂₃ :
      T.map (tensorLeft S.X₂) ⟶ T.map (tensorLeft S.X₃) :=
    T.mapNatTrans
      ((CategoryTheory.MonoidalCategory.tensoringLeft (Mod(𝒪))).map S.g)
  let k₁ : ((T.map (tensorLeft S.X₁)).X₁) ⟶ ((T.map (tensorLeft S.X₁)).X₂) :=
    (tensorLeft S.X₁).map T.f
  let k₂ : ((T.map (tensorLeft S.X₂)).X₁) ⟶ ((T.map (tensorLeft S.X₂)).X₂) :=
    (tensorLeft S.X₂).map T.f
  let k₃ : ((T.map (tensorLeft S.X₃)).X₁) ⟶ ((T.map (tensorLeft S.X₃)).X₂) :=
    (tensorLeft S.X₃).map T.f
  let π₁ : ((T.map (tensorLeft S.X₁)).X₂) ⟶ ((T.map (tensorLeft S.X₁)).X₃) :=
    (tensorLeft S.X₁).map T.g
  let π₂ : ((T.map (tensorLeft S.X₂)).X₂) ⟶ ((T.map (tensorLeft S.X₂)).X₃) :=
    (tensorLeft S.X₂).map T.g
  let π₃ : ((T.map (tensorLeft S.X₃)).X₂) ⟶ ((T.map (tensorLeft S.X₃)).X₃) :=
    (tensorLeft S.X₃).map T.g
  let fK : ((S.map (tensorRight T.X₁)).X₁) ⟶ ((S.map (tensorRight T.X₁)).X₂) :=
    (tensorRight T.X₁).map S.f
  let fGp : ((S.map (tensorRight T.X₂)).X₁) ⟶ ((S.map (tensorRight T.X₂)).X₂) :=
    (tensorRight T.X₂).map S.f
  let fG : ((S.map (tensorRight T.X₃)).X₁) ⟶ ((S.map (tensorRight T.X₃)).X₂) :=
    (tensorRight T.X₃).map S.f
  let gK : ((S.map (tensorRight T.X₁)).X₂) ⟶ ((S.map (tensorRight T.X₁)).X₃) :=
    (tensorRight T.X₁).map S.g
  let gGp : ((S.map (tensorRight T.X₂)).X₂) ⟶ ((S.map (tensorRight T.X₂)).X₃) :=
    (tensorRight T.X₂).map S.g
  -- Proof comment: repeat the presheaf refinement chase inside the sheaf module category.
  rw [Preadditive.mono_iff_cancel_zero]
  intro A x hx
  obtain ⟨A₁, ρ₁, _hρ₁, x', hx'⟩ := surjective_up_to_refinements_of_epi π₁ x
  have hx'fπ : x' ≫ fGp ≫ π₂ = 0 := by
    calc
      x' ≫ fGp ≫ π₂ = x' ≫ π₁ ≫ fG := by
        simpa [colMap₁₂, fGp, fG, π₁, π₂, Category.assoc] using colMap₁₂.comm₂₃.symm
      _ = ρ₁ ≫ x ≫ fG := by
        simpa [fG, Category.assoc] using congrArg (fun t ↦ t ≫ fG) hx'
      _ = 0 := by
        simpa [fG, Category.assoc] using congrArg (fun t ↦ ρ₁ ≫ t) hx
  have hCol₂Exact : (T.map (tensorLeft S.X₂)).Exact :=
    (T.map (tensorLeft S.X₂)).exact_iff_exact_toComposableArrows.2 hCol₂.1
  obtain ⟨A₂, ρ₂, _hρ₂, y₂, hy₂⟩ := hCol₂Exact.exact_up_to_refinements (x' ≫ fGp) hx'fπ
  have hy₂gk₃ : y₂ ≫ gK ≫ k₃ = 0 := by
    calc
      y₂ ≫ gK ≫ k₃ = y₂ ≫ k₂ ≫ gGp := by
        simpa [colMap₂₃, gK, gGp, k₂, k₃, Category.assoc] using colMap₂₃.comm₁₂
      _ = ρ₂ ≫ x' ≫ fGp ≫ gGp := by
        simpa [gGp, Category.assoc] using congrArg (fun t ↦ t ≫ gGp) hy₂
      _ = 0 := by
        simpa [fGp, gGp, T, Category.assoc] using congrArg (fun t ↦ ρ₂ ≫ x' ≫ t)
          (S.map (tensorRight T.X₂)).zero
  have hy₂gk : y₂ ≫ gK = 0 := by
    exact (cancel_mono k₃).1 (by simpa [gK, k₃, Category.assoc] using hy₂gk₃)
  have hRowKExact : (S.map (tensorRight T.X₁)).Exact :=
    (S.map (tensorRight T.X₁)).exact_iff_exact_toComposableArrows.2 hRowK.1
  obtain ⟨A₃, ρ₃, _hρ₃, y₁, hy₁⟩ := hRowKExact.exact_up_to_refinements y₂ hy₂gk
  have hLiftEqComp : ρ₃ ≫ ρ₂ ≫ x' ≫ fGp = y₁ ≫ k₁ ≫ fGp := by
    calc
      ρ₃ ≫ ρ₂ ≫ x' ≫ fGp = ρ₃ ≫ y₂ ≫ k₂ := by
        simpa [fGp, k₂, Category.assoc] using congrArg (fun t ↦ ρ₃ ≫ t) hy₂.symm
      _ = y₁ ≫ fK ≫ k₂ := by
        simpa [fK, Category.assoc] using congrArg (fun t ↦ t ≫ k₂) hy₁
      _ = y₁ ≫ k₁ ≫ fGp := by
        simpa [colMap₁₂, fK, fGp, k₁, k₂, Category.assoc] using
          congrArg (fun t ↦ y₁ ≫ t) colMap₁₂.comm₁₂.symm
  have hLiftEq : ρ₃ ≫ ρ₂ ≫ x' = y₁ ≫ k₁ := by
    exact (cancel_mono fGp).1 (by simpa [fGp, Category.assoc] using hLiftEqComp)
  have hRefinedZero : ρ₃ ≫ ρ₂ ≫ ρ₁ ≫ x = 0 := by
    calc
      ρ₃ ≫ ρ₂ ≫ ρ₁ ≫ x = ρ₃ ≫ ρ₂ ≫ x' ≫ π₁ := by
        simpa [π₁, Category.assoc] using congrArg (fun t ↦ ρ₃ ≫ ρ₂ ≫ t) hx'.symm
      _ = y₁ ≫ k₁ ≫ π₁ := by
        simpa [π₁, Category.assoc] using congrArg (fun t ↦ t ≫ π₁) hLiftEq
      _ = 0 := by
        simpa [k₁, π₁, T, Category.assoc] using congrArg ((tensorLeft S.X₁).map) T.zero
  exact
    (cancel_epi ρ₁).1 <|
      (cancel_epi ρ₂).1 <|
        (cancel_epi ρ₃).1 <|
          by simpa [Category.assoc] using hRefinedZero

/-- Helper for Lemma 18.28.11: tensoring a short exact sheaf row on the right preserves short
exactness when the quotient is flat. -/
private theorem shortExactTensorRightOfFlatQuotientKernel
    (𝒢 : Mod(𝒪))
    (S : ShortComplex (Mod(𝒪)))
    (hS : S.ShortExact)
    [IsFlat 𝒪 S.X₃] :
    (S.map (tensorRight 𝒢)).ShortExact := by
  obtain ⟨𝒢', _h𝒢', π, hπ⟩ :=
    SheafOfModules.RingedSite.exists_epi_from_flat (J := J) (𝒪 := 𝒪) 𝒢
  let _ : Epi π := hπ
  have hMono :
      Mono ((tensorRight 𝒢).map S.f) :=
    sheafTensorRightLeftMono_of_flat_cover (J := J) (𝒪 := 𝒪) (π := π) S hS
  let hExactEpi := tensorRight_mapsShortExact_to_exact_epi (J := J) (𝒪 := 𝒪) 𝒢 S hS
  -- Proof comment: right exactness handles exactness and epimorphy, and the flat-cover diagram
  -- supplies the remaining monomorphism on the left map.
  exact ShortComplex.ShortExact.mk'
    ((S.map (tensorRight 𝒢)).exact_iff_exact_toComposableArrows.2 hExactEpi.1)
    hMono
    hExactEpi.2

/-- Helper for Lemma 18.28.11: the short exactness statement above can be rewritten with left
tensoring using the braiding isomorphism. -/
private theorem shortExact_tensorLeft_of_flatQuotient
    (X : Mod(𝒪))
    {S : ShortComplex (Mod(𝒪))}
    (hS : S.ShortExact)
    [IsFlat 𝒪 S.X₃] :
    (S.map (tensorLeft X)).ShortExact := by
  let hRight : (S.map (tensorRight X)).ShortExact :=
    shortExactTensorRightOfFlatQuotientKernel (J := J) (𝒪 := 𝒪) X S hS
  -- Proof comment: transport the right-tensor short exact sequence through the braided
  -- comparison `tensorLeft X ≅ tensorRight X`.
  exact
    (CategoryTheory.shortExact_iff_of_functor_iso
      (e := CategoryTheory.BraidedCategory.tensorLeftIsoTensorRight X) S).2 hRight

/-- Helper for Lemma 18.28.11: if the left and right terms are flat, then tensoring any short
exact row by the middle term stays short exact. -/
private theorem tensorMiddleShortExactOfFlatEnds
    {S : ShortComplex (Mod(𝒪))}
    (hS : S.ShortExact)
    [IsFlat 𝒪 S.X₃] [IsFlat 𝒪 S.X₁]
    (T : ShortComplex (Mod(𝒪)))
    (hT : T.ShortExact) :
    (T.map (tensorRight S.X₂)).ShortExact := by
  let row₁ : (S.map (tensorLeft T.X₁)).ShortExact :=
    shortExact_tensorLeft_of_flatQuotient (J := J) (𝒪 := 𝒪) T.X₁ hS
  let row₂ : (S.map (tensorLeft T.X₂)).ShortExact :=
    shortExact_tensorLeft_of_flatQuotient (J := J) (𝒪 := 𝒪) T.X₂ hS
  let col₁ : (T.map (tensorRight S.X₁)).ShortExact :=
    shortExact_map_tensorRight_of_isFlat (J := J) (𝒪 := 𝒪) S.X₁ T hT
  let col₃ : (T.map (tensorRight S.X₃)).ShortExact :=
    shortExact_map_tensorRight_of_isFlat (J := J) (𝒪 := 𝒪) S.X₃ T hT
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
  let hExactEpi := tensorRight_mapsShortExact_to_exact_epi (J := J) (𝒪 := 𝒪) S.X₂ T hT
  -- Proof comment: right exactness supplies exactness and the epimorphic right map, while the
  -- four lemma supplies the missing monomorphism on the left map.
  exact ShortComplex.ShortExact.mk'
    ((T.map (tensorRight S.X₂)).exact_iff_exact_toComposableArrows.2 hExactEpi.1)
    hMiddleMono
    hExactEpi.2

/-- Helper for Lemma 18.28.11: if the middle and right terms are flat, then tensoring any short
exact row by the left term stays short exact. -/
private theorem tensorLeftTermShortExactOfFlatMiddleRight
    {S : ShortComplex (Mod(𝒪))}
    (hS : S.ShortExact)
    [IsFlat 𝒪 S.X₃] [IsFlat 𝒪 S.X₂]
    (T : ShortComplex (Mod(𝒪)))
    (hT : T.ShortExact) :
    (T.map (tensorRight S.X₁)).ShortExact := by
  let row₁ : (S.map (tensorLeft T.X₁)).ShortExact :=
    shortExact_tensorLeft_of_flatQuotient (J := J) (𝒪 := 𝒪) T.X₁ hS
  let row₂ : (S.map (tensorLeft T.X₂)).ShortExact :=
    shortExact_tensorLeft_of_flatQuotient (J := J) (𝒪 := 𝒪) T.X₂ hS
  let middleCol : (T.map (tensorRight S.X₂)).ShortExact :=
    shortExact_map_tensorRight_of_isFlat (J := J) (𝒪 := 𝒪) S.X₂ T hT
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
  let hExactEpi := tensorRight_mapsShortExact_to_exact_epi (J := J) (𝒪 := 𝒪) S.X₁ T hT
  -- Proof comment: right exactness again gives exactness and the epimorphic right map; the
  -- commuting square with the middle flat column supplies the monomorphism on the left.
  exact ShortComplex.ShortExact.mk'
    ((T.map (tensorRight S.X₁)).exact_iff_exact_toComposableArrows.2 hExactEpi.1)
    hLeftMono
    hExactEpi.2

/-- Helper for Lemma 18.28.11: in a short exact sheaf row with flat quotient, flatness of the
left term is equivalent to flatness of the middle term. -/
private theorem flatIffFlatOfShortExactKernel
    {S : ShortComplex (Mod(𝒪))}
    (hS : S.ShortExact) [IsFlat 𝒪 S.X₃] :
    IsFlat 𝒪 S.X₁ ↔ IsFlat 𝒪 S.X₂ := by
  constructor
  · intro h₁
    let _ : IsFlat 𝒪 S.X₁ := h₁
    -- Proof comment: tensor every short exact test row by `S.X₂`; right exactness gives the
    -- exact/epi part, and the four lemma forces the left map to be mono.
    exact isFlat_of_mapsShortExact (𝒪 := 𝒪) S.X₂ fun T hT ↦
      tensorMiddleShortExactOfFlatEnds (J := J) (𝒪 := 𝒪) (S := S) hS T hT
  · intro h₂
    let _ : IsFlat 𝒪 S.X₂ := h₂
    -- Proof comment: tensor every short exact test row by `S.X₁`; the middle flat column makes
    -- the left tensor column monic, and right exactness supplies the rest.
    exact isFlat_of_mapsShortExact (𝒪 := 𝒪) S.X₁ fun T hT ↦
      tensorLeftTermShortExactOfFlatMiddleRight (J := J) (𝒪 := 𝒪) (S := S) hS T hT

omit [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Helper for Lemma 18.28.11: in a short exact row of sheaf modules with flat middle and flat
quotient, the left term is flat. -/
private theorem flatLeftOfShortExactOfFlatMiddleRight
    {S : ShortComplex (Mod(𝒪))}
    (hS : S.ShortExact)
    [IsFlat 𝒪 S.X₃] [IsFlat 𝒪 S.X₂] :
    IsFlat 𝒪 S.X₁ := by
  -- Proof comment: this is exactly the backward implication of the local sheaf two-out-of-three
  -- flatness kernel replayed from Lemma `18.28.10`.
  exact (flatIffFlatOfShortExactKernel (J := J) (𝒪 := 𝒪) (S := S) hS).2 inferInstance

/-- Helper for Lemma 18.28.11: tensoring a short exact sheaf row on the right preserves short
exactness when the cokernel is flat. -/
private theorem shortExact_tensor_right_of_flat_quotient
    (𝒢 : Mod(𝒪))
    (S : ShortComplex (Mod(𝒪)))
    (hS : S.ShortExact)
    [IsFlat 𝒪 S.X₃] :
    (S.map (tensorRight 𝒢)).ShortExact := by
  -- Proof comment: use the local ringed-site flat-cover replay of Lemma `18.28.9`.
  exact shortExactTensorRightOfFlatQuotientKernel (J := J) (𝒪 := 𝒪) 𝒢 S hS

/-- A right-augmented exact complex of sheaves of `\mathcal O`-modules on a ringed site
`\cdots \to \mathcal F_2 \to \mathcal F_1 \to \mathcal F_0 \to \mathcal Q \to 0`,
encoded by exactness at every displayed term and surjectivity of the augmentation. -/
structure RightAugmentedExact
    (ℱ : ℕ → Mod(𝒪))
    (d : ∀ n : ℕ, ℱ (n + 1) ⟶ ℱ n)
    (𝒬 : Mod(𝒪))
    (q : ℱ 0 ⟶ 𝒬) : Prop where
  /-- Consecutive differentials in the resolution part compose to zero. -/
  d_comp_d : ∀ n : ℕ, d (n + 1) ≫ d n = 0
  /-- The last differential composes trivially with the augmentation. -/
  d_comp_q : d 0 ≫ q = 0
  /-- Exactness at every term `\mathcal F_n` with `n ≥ 1`. -/
  exact_succ :
      ∀ n : ℕ,
        (ShortComplex.mk (d (n + 1)) (d n) (d_comp_d n)).Exact
  /-- Exactness at `\mathcal F_0`. -/
  exact_zero :
      (ShortComplex.mk (d 0) q d_comp_q).Exact
  /-- Exactness at `\mathcal Q`, equivalently surjectivity of the augmentation. -/
  epi_q : Epi q

/-- Helper for Lemma 18.28.11: the image of the last differential lands in the augmentation
kernel. -/
private theorem zeroImageComp_q
    (ℱ : ℕ → Mod(𝒪))
    (d : ∀ n : ℕ, ℱ (n + 1) ⟶ ℱ n)
    {𝒬 : Mod(𝒪)}
    (q : ℱ 0 ⟶ 𝒬)
    (hExact : RightAugmentedExact ℱ d 𝒬 q) :
    CategoryTheory.Abelian.image.ι (d 0) ≫ q = 0 := by
  -- Proof comment: cancel the epi image factorization and reduce to `d₀ ≫ q = 0`.
  apply (cancel_epi (CategoryTheory.Abelian.factorThruImage (d 0))).1
  simpa [Category.assoc, CategoryTheory.Abelian.image.fac] using hExact.d_comp_q

/-- Helper for Lemma 18.28.11: each interior image inclusion factors through the next image. -/
private theorem succImageComp_factor
    (ℱ : ℕ → Mod(𝒪))
    (d : ∀ n : ℕ, ℱ (n + 1) ⟶ ℱ n)
    {𝒬 : Mod(𝒪)}
    (q : ℱ 0 ⟶ 𝒬)
    (hExact : RightAugmentedExact ℱ d 𝒬 q)
    (n : ℕ) :
    CategoryTheory.Abelian.image.ι (d (n + 1)) ≫
        CategoryTheory.Abelian.factorThruImage (d n) = 0 := by
  -- Proof comment: postcompose with the mono image inclusion of `dₙ` to recover `dₙ₊₁ ≫ dₙ`.
  apply (cancel_mono (CategoryTheory.Abelian.image.ι (d n))).1
  simpa [Category.assoc, CategoryTheory.Abelian.image.fac] using hExact.d_comp_d n

/-- Helper for Lemma 18.28.11: the sheaf augmentation row
`0 ⟶ im(d₀) ⟶ ℱ₀ ⟶ 𝒬 ⟶ 0` is short exact. -/
private abbrev zeroImageRow
    (ℱ : ℕ → Mod(𝒪))
    (d : ∀ n : ℕ, ℱ (n + 1) ⟶ ℱ n)
    {𝒬 : Mod(𝒪)}
    (q : ℱ 0 ⟶ 𝒬)
    (hExact : RightAugmentedExact ℱ d 𝒬 q) :
    ShortComplex (Mod(𝒪)) :=
  ShortComplex.mk (CategoryTheory.Abelian.image.ι (d 0)) q
    (zeroImageComp_q ℱ d q hExact)

/-- Helper for Lemma 18.28.11: the recurring interior sheaf image-factor row
`0 ⟶ im(dₙ₊₁) ⟶ ℱₙ₊₁ ⟶ im(dₙ) ⟶ 0`. -/
private abbrev succImageRow
    (ℱ : ℕ → Mod(𝒪))
    (d : ∀ n : ℕ, ℱ (n + 1) ⟶ ℱ n)
    {𝒬 : Mod(𝒪)}
    (q : ℱ 0 ⟶ 𝒬)
    (hExact : RightAugmentedExact ℱ d 𝒬 q)
    (n : ℕ) :
    ShortComplex (Mod(𝒪)) :=
  ShortComplex.mk (CategoryTheory.Abelian.image.ι (d (n + 1)))
    (CategoryTheory.Abelian.factorThruImage (d n))
    (succImageComp_factor ℱ d q hExact n)

/-- Helper for Lemma 18.28.11: the sheaf augmentation row
`0 ⟶ im(d₀) ⟶ ℱ₀ ⟶ 𝒬 ⟶ 0` is short exact. -/
private theorem zeroImageShortExact
    (ℱ : ℕ → Mod(𝒪))
    (d : ∀ n : ℕ, ℱ (n + 1) ⟶ ℱ n)
    {𝒬 : Mod(𝒪)}
    (q : ℱ 0 ⟶ 𝒬)
    (hExact : RightAugmentedExact ℱ d 𝒬 q) :
    (zeroImageRow ℱ d q hExact).ShortExact := by
  have hSExact : (zeroImageRow ℱ d q hExact).Exact := by
    -- Proof comment: exactness at `ℱ₀` is the image-formulation of the original augmentation row.
    simpa [zeroImageRow] using
      (ShortComplex.exact_iff_exact_image_ι
        (ShortComplex.mk (d 0) q (hExact.d_comp_q))).1 hExact.exact_zero
  -- Proof comment: combine exactness with the canonical mono image inclusion and the given
  -- surjectivity of the augmentation.
  exact ShortComplex.ShortExact.mk' hSExact inferInstance hExact.epi_q

/-- Helper for Lemma 18.28.11: each interior sheaf row
`0 ⟶ im(dₙ₊₁) ⟶ ℱₙ₊₁ ⟶ im(dₙ) ⟶ 0` is short exact. -/
private theorem succImageShortExact
    (ℱ : ℕ → Mod(𝒪))
    (d : ∀ n : ℕ, ℱ (n + 1) ⟶ ℱ n)
    {𝒬 : Mod(𝒪)}
    (q : ℱ 0 ⟶ 𝒬)
    (hExact : RightAugmentedExact ℱ d 𝒬 q)
    (n : ℕ) :
    (succImageRow ℱ d q hExact n).ShortExact := by
  let T : ShortComplex (Mod(𝒪)) :=
    ShortComplex.mk (d (n + 1)) (d n) (hExact.d_comp_d n)
  have hSExact : (succImageRow ℱ d q hExact n).Exact := by
    -- Proof comment: exactness of the original differential row transports to its image-factor
    -- row through the shared `ShortComplex` bridge.
    simpa [succImageRow, T] using
      CategoryTheory.ShortComplex.exactImageFactorRowOfExact T (hExact.exact_succ n)
  -- Proof comment: the image inclusion is mono and the factor-through-image map is epi, so the
  -- exact image row is short exact.
  exact ShortComplex.ShortExact.mk' hSExact inferInstance inferInstance

/-- Helper for Lemma 18.28.11: every differential image in the sheaf resolution is flat. -/
private theorem flatImage
    (ℱ : ℕ → Mod(𝒪))
    (d : ∀ n : ℕ, ℱ (n + 1) ⟶ ℱ n)
    {𝒬 : Mod(𝒪)}
    (q : ℱ 0 ⟶ 𝒬)
    (hExact : RightAugmentedExact ℱ d 𝒬 q)
    (hflat𝒬 : SheafOfModules.RingedSite.IsFlat (J := J) 𝒪 𝒬)
    (hflatℱ : ∀ n : ℕ, SheafOfModules.RingedSite.IsFlat (J := J) 𝒪 (ℱ n)) :
    ∀ n : ℕ, SheafOfModules.RingedSite.IsFlat (J := J) 𝒪 (CategoryTheory.Abelian.image (d n)) := by
  let _ : IsFlat 𝒪 𝒬 := hflat𝒬
  intro n
  induction n with
  | zero =>
      let S := zeroImageRow ℱ d q hExact
      let _ : IsFlat 𝒪 S.X₃ := by
        simpa [S, zeroImageRow] using hflat𝒬
      let _ : IsFlat 𝒪 S.X₂ := by
        simpa [S, zeroImageRow] using hflatℱ 0
      -- Proof comment: the base image row ends in the flat quotient `𝒬`, so the local
      -- flat-left lemma applies directly.
      simpa [S, zeroImageRow] using
        (flatLeftOfShortExactOfFlatMiddleRight (J := J) (𝒪 := 𝒪)
          (S := S) (zeroImageShortExact ℱ d q hExact))
  | succ n ih =>
      let S := succImageRow ℱ d q hExact n
      let _ : IsFlat 𝒪 (CategoryTheory.Abelian.image (d n)) := ih
      let _ : IsFlat 𝒪 S.X₃ := by
        simpa [S, succImageRow] using
          (inferInstance : IsFlat 𝒪 (CategoryTheory.Abelian.image (d n)))
      let _ : IsFlat 𝒪 S.X₂ := by
        simpa [S, succImageRow] using hflatℱ (n + 1)
      -- Proof comment: the successor image row has flat middle `ℱ (n + 1)` and flat quotient
      -- `im(dₙ)`, so induction propagates flatness to `im(dₙ₊₁)`.
      simpa [S, succImageRow] using
        (flatLeftOfShortExactOfFlatMiddleRight (J := J) (𝒪 := 𝒪)
          (S := S) (succImageShortExact ℱ d q hExact n))

/-- Helper for Lemma 18.28.11: tensoring preserves the vanishing of each sheaf differential
composite in the resolution. -/
private theorem tensorDCompD
    (ℱ : ℕ → Mod(𝒪))
    (d : ∀ n : ℕ, ℱ (n + 1) ⟶ ℱ n)
    {𝒬 𝒢 : Mod(𝒪)}
    (q : ℱ 0 ⟶ 𝒬)
    (hExact : RightAugmentedExact ℱ d 𝒬 q)
    (n : ℕ) :
    (tensorRight 𝒢).map (d (n + 1)) ≫ (tensorRight 𝒢).map (d n) = 0 := by
  -- Proof comment: apply the tensor-right functor to the zero differential composite.
  rw [← Functor.map_comp, hExact.d_comp_d, Functor.map_zero]

/-- Helper for Lemma 18.28.11: tensoring preserves the vanishing of the sheaf augmentation
composite. -/
private theorem tensorDCompQ
    (ℱ : ℕ → Mod(𝒪))
    (d : ∀ n : ℕ, ℱ (n + 1) ⟶ ℱ n)
    {𝒬 𝒢 : Mod(𝒪)}
    (q : ℱ 0 ⟶ 𝒬)
    (hExact : RightAugmentedExact ℱ d 𝒬 q) :
    (tensorRight 𝒢).map (d 0) ≫ (tensorRight 𝒢).map q = 0 := by
  -- Proof comment: apply the tensor-right functor to the zero composite `d₀ ≫ q`.
  rw [← Functor.map_comp, hExact.d_comp_q, Functor.map_zero]

/-- Helper for Lemma 18.28.11: after tensoring on the right, each canonical image inclusion in
the split sheaf resolution rows is still monomorphic. -/
private theorem tensorImageInclusionMono
    (ℱ : ℕ → Mod(𝒪))
    (d : ∀ n : ℕ, ℱ (n + 1) ⟶ ℱ n)
    {𝒬 𝒢 : Mod(𝒪)}
    (q : ℱ 0 ⟶ 𝒬)
    (hExact : RightAugmentedExact ℱ d 𝒬 q)
    (hflat𝒬 : SheafOfModules.RingedSite.IsFlat (J := J) 𝒪 𝒬)
    (hflatℱ : ∀ n : ℕ, SheafOfModules.RingedSite.IsFlat (J := J) 𝒪 (ℱ n))
    (n : ℕ) :
    Mono ((tensorRight 𝒢).map (CategoryTheory.Abelian.image.ι (d n))) := by
  cases n with
  | zero =>
      let _ : IsFlat 𝒪 𝒬 := hflat𝒬
      have hTensor :
          ((zeroImageRow ℱ d q hExact).map (tensorRight 𝒢)).ShortExact :=
        shortExact_tensor_right_of_flat_quotient (J := J) (𝒢 := 𝒢)
          (S := zeroImageRow ℱ d q hExact) (zeroImageShortExact ℱ d q hExact)
      -- Proof comment: tensor the augmentation image row and read off monicity of its left map.
      simpa [zeroImageRow] using hTensor.mono_f
  | succ n =>
      let _ : IsFlat 𝒪 (CategoryTheory.Abelian.image (d n)) :=
        flatImage (J := J) ℱ d q hExact hflat𝒬 hflatℱ n
      have hTensor :
          ((succImageRow ℱ d q hExact n).map (tensorRight 𝒢)).ShortExact :=
        shortExact_tensor_right_of_flat_quotient (J := J) (𝒢 := 𝒢)
          (S := succImageRow ℱ d q hExact n) (succImageShortExact ℱ d q hExact n)
      -- Proof comment: tensor the successor image row and again extract monicity from the left
      -- edge of the short exact sequence.
      simpa [succImageRow] using hTensor.mono_f

/-- Helper for Lemma 18.28.11: exactness of the mapped sheaf image row transports back to the
original tensor differential row. -/
private theorem tensorSuccExactOfMappedImageRow
    (ℱ : ℕ → Mod(𝒪))
    (d : ∀ n : ℕ, ℱ (n + 1) ⟶ ℱ n)
    {𝒬 𝒢 : Mod(𝒪)}
    (q : ℱ 0 ⟶ 𝒬)
    (hExact : RightAugmentedExact ℱ d 𝒬 q)
    (hflat𝒬 : SheafOfModules.RingedSite.IsFlat (J := J) 𝒪 𝒬)
    (hflatℱ : ∀ n : ℕ, SheafOfModules.RingedSite.IsFlat (J := J) 𝒪 (ℱ n))
    (n : ℕ) :
    (ShortComplex.mk
      ((tensorRight 𝒢).map (d (n + 1)))
      ((tensorRight 𝒢).map (d n))
      (tensorDCompD ℱ d (J := J) (𝒢 := 𝒢) q hExact n)).Exact := by
  let S : ShortComplex (Mod(𝒪)) :=
    ShortComplex.mk (d (n + 1)) (d n) (hExact.d_comp_d n)
  let U : ShortComplex (Mod(𝒪)) :=
    succImageRow ℱ d q hExact n
  have hTensorU : (U.map (tensorRight 𝒢)).ShortExact :=
    shortExact_tensor_right_of_flat_quotient (J := J) (𝒢 := 𝒢) (S := U)
      (succImageShortExact ℱ d q hExact n)
  let _ : IsFlat 𝒪 (CategoryTheory.Abelian.image (d n)) :=
    flatImage (J := J) ℱ d q hExact hflat𝒬 hflatℱ n
  let _ : Mono ((tensorRight 𝒢).map (CategoryTheory.Abelian.image.ι (d n))) :=
    tensorImageInclusionMono (J := J) ℱ d (𝒢 := 𝒢) q hExact hflat𝒬 hflatℱ n
  -- Proof comment: exactness of the tensorized image row transports back to the original
  -- tensorized differential row once the mapped image inclusion is known to be mono.
  simpa [S, U, succImageRow, tensorDCompD] using
    (CategoryTheory.ShortComplex.exactOfMappedImageFactorRow
      (F := tensorRight 𝒢) S hTensorU.exact)

/-- Helper for Lemma 18.28.11: tensoring the sheaf augmentation image row preserves exactness at
the degree-zero term. -/
private theorem tensorZeroExactOfImageRow
    (ℱ : ℕ → Mod(𝒪))
    (d : ∀ n : ℕ, ℱ (n + 1) ⟶ ℱ n)
    {𝒬 𝒢 : Mod(𝒪)}
    (q : ℱ 0 ⟶ 𝒬)
    (hExact : RightAugmentedExact ℱ d 𝒬 q)
    (hflat𝒬 : SheafOfModules.RingedSite.IsFlat (J := J) 𝒪 𝒬) :
    (ShortComplex.mk
      ((tensorRight 𝒢).map (d 0))
      ((tensorRight 𝒢).map q)
      (tensorDCompQ ℱ d (J := J) (𝒢 := 𝒢) q hExact)).Exact := by
  let _ : IsFlat 𝒪 𝒬 := hflat𝒬
  have hTensor :
      ((zeroImageRow ℱ d q hExact).map (tensorRight 𝒢)).ShortExact :=
    shortExact_tensor_right_of_flat_quotient (J := J) (𝒢 := 𝒢)
      (S := zeroImageRow ℱ d q hExact) (zeroImageShortExact ℱ d q hExact)
  -- Proof comment: tensor the zero-image row, then convert its exactness back to the original
  -- augmentation row through `exact_iff_exact_image_ι`.
  simpa [zeroImageRow, tensorDCompQ] using
    (ShortComplex.exact_iff_exact_image_ι
      (ShortComplex.mk
        ((tensorRight 𝒢).map (d 0))
        ((tensorRight 𝒢).map q)
        (tensorDCompQ ℱ d (J := J) (𝒢 := 𝒢) q hExact))).2 hTensor.exact

-- Proof sketch: repeat the presheaf argument in `Mod(\mathcal O)`, using the sheaf version of
-- Lemma `18.28.9` on each short exact subsequence and Lemma `18.28.10` to propagate flatness of
-- successive images through the augmented resolution.
/-- Lemma 18.28.11 (2): if `(\mathcal C, J)` is a site and
`\cdots \to \mathcal F_2 \to \mathcal F_1 \to \mathcal F_0 \to \mathcal Q \to 0`
is an exact complex of flat sheaves of `\mathcal O`-modules, then tensoring on the right by any
sheaf `\mathcal G` again yields an exact right-augmented complex in `\mathrm{Mod}(\mathcal O)`. -/
@[stacks 03EZ]
theorem rightAugmentedExact_tensor_right_of_flat
    (ℱ : ℕ → Mod(𝒪))
    (d : ∀ n : ℕ, ℱ (n + 1) ⟶ ℱ n)
    {𝒬 𝒢 : Mod(𝒪)}
    (q : ℱ 0 ⟶ 𝒬)
    (hExact : RightAugmentedExact ℱ d 𝒬 q)
    (hflat𝒬 : SheafOfModules.RingedSite.IsFlat (J := J) 𝒪 𝒬)
    (hflatℱ : ∀ n : ℕ, SheafOfModules.RingedSite.IsFlat (J := J) 𝒪 (ℱ n)) :
    RightAugmentedExact
      (fun n ↦ (tensorRight 𝒢).obj (ℱ n))
      (fun n ↦ (tensorRight 𝒢).map (d n))
      ((tensorRight 𝒢).obj 𝒬)
      ((tensorRight 𝒢).map q) := by
  refine
    ⟨
      tensorDCompD ℱ d (J := J) (𝒢 := 𝒢) q hExact,
      tensorDCompQ ℱ d (J := J) (𝒢 := 𝒢) q hExact,
      ?_,
      ?_,
      inferInstance
    ⟩
  · intro n
    -- Proof comment: every successor row is exact by transport from the tensorized image row.
    exact tensorSuccExactOfMappedImageRow (J := J) ℱ d (𝒢 := 𝒢) q hExact hflat𝒬 hflatℱ n
  · -- Proof comment: the degree-zero row is the augmentation specialization of the same tensor
    -- exactness argument.
    exact tensorZeroExactOfImageRow (J := J) ℱ d (𝒢 := 𝒢) q hExact hflat𝒬

end SheafOfModules.RingedSite
