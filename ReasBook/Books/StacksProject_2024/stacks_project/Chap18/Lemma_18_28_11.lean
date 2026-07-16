import Mathlib
import StacksProject_2024.stacks_project.Chap12.Lemma_12_7_2
import StacksProject_2024.stacks_project.Chap18.Definition_18_28_1
import StacksProject_2024.stacks_project.Chap18.Lemma_18_28_9

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

/-- Helper for Lemma 18.28.11: after applying a zero-morphism-preserving functor, the image-factor
row still has zero composite. -/
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
        simp only [W, D, Category.id_comp]
        rw [← F.map_comp]
        exact congrArg F.map (Abelian.image.fac S.g).symm }
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

/-- Helper for Lemma 18.28.11: if tensoring on the right by `X` preserves every short exact
sequence, then `X` is flat. -/
private theorem isFlatOfMapsShortExact
    (X : PresheafOfModules (ringPresheaf 𝒪))
    (hX : ∀ T : ShortComplex (PresheafOfModules (ringPresheaf 𝒪)),
      T.ShortExact → (T.map (tensorRight X)).ShortExact) :
    IsFlat X := by
  refine ⟨?_⟩
  -- Proof comment: apply the exact-functor criterion directly to `tensorRight X`.
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

/-- Helper for Lemma 18.28.11: if `X` is flat, then tensoring a short exact sequence on the
right by `X` stays short exact. -/
private theorem shortExactMapTensorRightOfIsFlat
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

/-- Helper for Lemma 18.28.11: right tensoring is always right exact, so a mapped short exact
sequence stays exact and keeps an epimorphic second map. -/
private theorem tensorRightMapsShortExactToExactEpi
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
  -- Proof comment: apply the right-exactness criterion to the tensor-right functor.
  exact
    (CategoryTheory.functor_rightExact_iff_maps_shortExact_to_exact_epi
      (A := PresheafOfModules (ringPresheaf 𝒪))
      (B := PresheafOfModules (ringPresheaf 𝒪))
      (F := tensorRight X)).1 hRight T hT

/-- Helper for Lemma 18.28.11: the short exactness statement from Lemma 18.28.9 can be rewritten
with left tensoring using braiding. -/
private theorem shortExactTensorLeftOfFlatQuotient
    {S : ShortComplex (PresheafOfModules (ringPresheaf 𝒪))}
    (X : PresheafOfModules (ringPresheaf 𝒪))
    (hS : S.ShortExact)
    [IsFlat S.X₃] :
    (S.map (tensorLeft X)).ShortExact := by
  let hRight : (S.map (tensorRight X)).ShortExact :=
    shortExact_tensor_right_of_flat_quotient (𝒢 := X) (S := S) hS
  -- Proof comment: transport the right-tensor short exact sequence through the braided
  -- comparison `tensorLeft X ≅ tensorRight X`.
  exact
    (CategoryTheory.shortExact_iff_of_functor_iso
      (e := CategoryTheory.BraidedCategory.tensorLeftIsoTensorRight X) S).2 hRight

/-- Helper for Lemma 18.28.11: in a short exact row with flat middle and flat quotient, the left
term is flat. -/
private theorem flatLeftOfShortExactOfFlatMiddleRight
    {S : ShortComplex (PresheafOfModules (ringPresheaf 𝒪))}
    (hS : S.ShortExact)
    [IsFlat S.X₃] [IsFlat S.X₂] :
    IsFlat S.X₁ := by
  -- Route correction: instead of importing the missing Chapter 18 flatness two-out-of-three
  -- module, re-run only the one needed direction locally via the tensor-square argument.
  exact isFlatOfMapsShortExact S.X₁ fun T hT ↦ by
    let row₁ : (S.map (tensorLeft T.X₁)).ShortExact :=
      shortExactTensorLeftOfFlatQuotient (𝒪 := 𝒪) (S := S) T.X₁ hS
    let row₂ : (S.map (tensorLeft T.X₂)).ShortExact :=
      shortExactTensorLeftOfFlatQuotient (𝒪 := 𝒪) (S := S) T.X₂ hS
    let middleCol : (T.map (tensorRight S.X₂)).ShortExact :=
      shortExactMapTensorRightOfIsFlat (𝒪 := 𝒪) S.X₂ T hT
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
    let hExactEpi := tensorRightMapsShortExactToExactEpi (𝒪 := 𝒪) S.X₁ T hT
    -- Proof comment: right exactness gives exactness and the epimorphic right map; the
    -- commuting square with the middle flat column supplies the monomorphism on the left.
    exact ShortComplex.ShortExact.mk'
      ((T.map (tensorRight S.X₁)).exact_iff_exact_toComposableArrows.2 hExactEpi.1)
      hLeftMono
      hExactEpi.2

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
private theorem zeroImageShortExact
    (ℱ : ℕ → PresheafOfModules (ringPresheaf 𝒪))
    (d : ∀ n : ℕ, ℱ (n + 1) ⟶ ℱ n)
    {𝒬 : PresheafOfModules (ringPresheaf 𝒪)}
    (q : ℱ 0 ⟶ 𝒬)
    (hExact : RightAugmentedExact ℱ d 𝒬 q) :
    let S : ShortComplex (PresheafOfModules (ringPresheaf 𝒪)) :=
      ShortComplex.mk (CategoryTheory.Abelian.image.ι (d 0)) q
        (zeroImageComp_q ℱ d q hExact)
    S.ShortExact := by
  let S : ShortComplex (PresheafOfModules (ringPresheaf 𝒪)) :=
    ShortComplex.mk (CategoryTheory.Abelian.image.ι (d 0)) q
      (by simpa using zeroImageComp_q ℱ d q hExact)
  have hSExact : S.Exact := by
    -- Proof comment: exactness at `ℱ₀` is the image-formulation of the original augmentation row.
    simpa [S] using
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
    let S : ShortComplex (PresheafOfModules (ringPresheaf 𝒪)) :=
      ShortComplex.mk (CategoryTheory.Abelian.image.ι (d (n + 1)))
        (CategoryTheory.Abelian.factorThruImage (d n))
        (succImageComp_factor ℱ d q hExact n)
    S.ShortExact := by
  let T : ShortComplex (PresheafOfModules (ringPresheaf 𝒪)) :=
    ShortComplex.mk (d (n + 1)) (d n) (hExact.d_comp_d n)
  let S : ShortComplex (PresheafOfModules (ringPresheaf 𝒪)) :=
    ShortComplex.mk (CategoryTheory.Abelian.image.ι (d (n + 1)))
      (CategoryTheory.Abelian.factorThruImage (d n))
      (succImageComp_factor ℱ d q hExact n)
  have hSExact : S.Exact := by
    -- Proof comment: exactness of the original differential row transports to its image-factor
    -- row through the shared `ShortComplex` bridge.
    simpa [S, T] using
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
    -- TODO: use `zeroImageShortExact` and `succImageShortExact` plus the already-local
    -- `flatLeftOfShortExactOfFlatMiddleRight` to run the image-flatness induction without the
    -- current heavy definitional reductions through `ShortComplex.mk`.
    sorry

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
  -- TODO: case split on `n = 0` and `n = k + 1`, tensor the corresponding image short exact row,
  -- and read monicity from the left map of the tensorized short exact sequence.
  sorry

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
  -- TODO: tensor the short exact image row from `succImageShortExact`, then feed its exact part
  -- and the mapped image-inclusion monomorphism into
  -- `CategoryTheory.ShortComplex.exactOfMappedImageFactorRow`.
  sorry

-- Proof sketch: split the augmented exact complex into the short exact sequences
-- `0 → im(d_{n+1}) → ℱ_n → im(d_n) → 0` and `0 → im(d_0) → ℱ_0 → 𝒬 → 0`. Apply Lemma
-- `18.28.9` to preserve each short exact sequence after tensoring with `𝒢`, and use Lemma
-- `18.28.10` inductively to show the successive images remain flat.
/-- Lemma 18.28.11 (1): if
`\cdots \to \mathcal F_2 \to \mathcal F_1 \to \mathcal F_0 \to \mathcal Q \to 0`
is an exact complex of flat presheaves of `\mathcal O`-modules, then tensoring on the right by
any presheaf `\mathcal G` again yields an exact right-augmented complex. -/
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
  -- TODO: assemble the tensorized right-augmented complex from `tensorDCompD`, `tensorDCompQ`,
  -- `tensorSuccExactOfMappedImageRow`, and the tensorized zero-image row.
  sorry

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
  -- TODO: the needed additive instance for `tensorLeft X` is not available from this file's
  -- current import context; restore that instance or import the canonical owner.
  sorry

omit [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Helper for Lemma 18.28.11: if tensoring on the right by `X` preserves every short exact
sequence of sheaf modules, then `X` is flat. -/
private theorem isFlatOfMapsShortExact
    (X : Mod(𝒪))
    (hX : ∀ T : ShortComplex (Mod(𝒪)),
      T.ShortExact → (T.map (tensorRight X)).ShortExact) :
    IsFlat 𝒪 X := by
  -- TODO: this mirrors the successful local helper from Lemma 18.28.10, but this file is missing
  -- the imported instance context needed to re-run that proof directly.
  sorry

omit [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Helper for Lemma 18.28.11: if `X` is flat, then tensoring a short exact sequence of sheaf
modules on the right by `X` stays short exact. -/
private theorem shortExactMapTensorRightOfIsFlat
    (X : Mod(𝒪))
    [IsFlat 𝒪 X]
    (T : ShortComplex (Mod(𝒪)))
    (hT : T.ShortExact) :
    (T.map (tensorRight X)).ShortExact := by
  -- TODO: reuse the local sheaf exactness route from Lemma 18.28.10 once the missing instance
  -- imports are restored in this file.
  sorry

omit [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Helper for Lemma 18.28.11: right tensoring in `Mod(\mathcal O)` is right exact, so a mapped
short exact sequence stays exact and keeps an epimorphic second map. -/
private theorem tensorRightMapsShortExactToExactEpi
    (X : Mod(𝒪))
    (T : ShortComplex (Mod(𝒪)))
    (hT : T.ShortExact) :
    (ComposableArrows.mk₂ ((tensorRight X).map T.f) ((tensorRight X).map T.g)).Exact ∧
      Epi ((tensorRight X).map T.g) := by
  -- TODO: re-run the sheaf-side right-exactness argument from Lemma 18.28.10 after restoring the
  -- missing finite-colimit instances for `tensorRight`.
  sorry

omit [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Helper for Lemma 18.28.11: the short exactness statement from Lemma 18.28.9 can be rewritten
with left tensoring using braiding in the sheaf category. -/
private theorem shortExactTensorLeftOfFlatQuotient
    {S : ShortComplex (Mod(𝒪))}
    (X : Mod(𝒪))
    (hS : S.ShortExact)
    [IsFlat 𝒪 S.X₃] :
    (S.map (tensorLeft X)).ShortExact := by
  -- TODO: once the local sheaf tensor-left instance issues are resolved, transport the known
  -- right-tensor short exactness across `tensorLeftIsoTensorRight`.
  sorry

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
  -- TODO: after the missing sheaf tensor instances are restored, mirror the Chapter 18.28.10
  -- tensor-square argument to recover flatness of the left term.
  sorry

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
private theorem zeroImageShortExact
    (ℱ : ℕ → Mod(𝒪))
    (d : ∀ n : ℕ, ℱ (n + 1) ⟶ ℱ n)
    {𝒬 : Mod(𝒪)}
    (q : ℱ 0 ⟶ 𝒬)
    (hExact : RightAugmentedExact ℱ d 𝒬 q) :
    let S : ShortComplex (Mod(𝒪)) :=
      ShortComplex.mk (CategoryTheory.Abelian.image.ι (d 0)) q
        (zeroImageComp_q ℱ d q hExact)
    S.ShortExact := by
  -- TODO: mirror the presheaf proof once the sheaf-side abelian/image infrastructure is available
  -- in this file's import context.
  sorry

/-- Helper for Lemma 18.28.11: each interior sheaf row
`0 ⟶ im(dₙ₊₁) ⟶ ℱₙ₊₁ ⟶ im(dₙ) ⟶ 0` is short exact. -/
private theorem succImageShortExact
    (ℱ : ℕ → Mod(𝒪))
    (d : ∀ n : ℕ, ℱ (n + 1) ⟶ ℱ n)
    {𝒬 : Mod(𝒪)}
    (q : ℱ 0 ⟶ 𝒬)
    (hExact : RightAugmentedExact ℱ d 𝒬 q)
    (n : ℕ) :
    let S : ShortComplex (Mod(𝒪)) :=
      ShortComplex.mk (CategoryTheory.Abelian.image.ι (d (n + 1)))
        (CategoryTheory.Abelian.factorThruImage (d n))
        (succImageComp_factor ℱ d q hExact n)
    S.ShortExact := by
  -- TODO: once the sheaf abelian instance is available in this file, apply the shared
  -- `ShortComplex.exactImageFactorRowOfExact` bridge exactly as on the presheaf side.
  sorry

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
  -- TODO: run the sheaf image-flatness induction after the local short exact and flat-left
  -- helpers above are restored.
  sorry

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
  -- TODO: mirror the presheaf mono extraction after the sheaf image rows and flat-image
  -- induction are restored.
  sorry

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
  -- TODO: tensor the sheaf image row and transport its exactness back through the shared
  -- `ShortComplex.exactOfMappedImageFactorRow` bridge once the local sheaf structural lemmas are
  -- available.
  sorry

-- Proof sketch: repeat the presheaf argument in `Mod(\mathcal O)`, using the sheaf version of
-- Lemma `18.28.9` on each short exact subsequence and Lemma `18.28.10` to propagate flatness of
-- successive images through the augmented resolution.
/-- Lemma 18.28.11 (2): if `(\mathcal C, J)` is a site and
`\cdots \to \mathcal F_2 \to \mathcal F_1 \to \mathcal F_0 \to \mathcal Q \to 0`
is an exact complex of flat sheaves of `\mathcal O`-modules, then tensoring on the right by any
sheaf `\mathcal G` again yields an exact right-augmented complex in `\mathrm{Mod}(\mathcal O)`. -/
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
  -- TODO: assemble the sheaf tensorized right-augmented complex once the local sheaf image-row
  -- and flatness helpers above are restored.
  sorry

end SheafOfModules.RingedSite
