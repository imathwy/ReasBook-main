import stacks_proof.stacks_project.Chap13.Lemma_13_33_4.SubsequenceCoproductData

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- Helper for Lemma 13.33.4: the left composite `u ≫ v` acts trivially on the subsequence cocone
map once the first two comparison squares commute. -/
private theorem subsequenceConeMap_leftComposite_on_cocone
    (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    [HasCoproduct K.obj] [HasCoproduct (hs.monotone.functor ⋙ K).obj]
    {Xsub Xfull : D}
    {gsub : ∐ (hs.monotone.functor ⋙ K).obj ⟶ Xsub}
    {gfull : ∐ K.obj ⟶ Xfull}
    (u : Xsub ⟶ Xfull)
    (hu : gsub ≫ u = subsequenceCoproductInclusion K s hs ≫ gfull)
    (v : Xfull ⟶ Xsub)
    (hv : gfull ≫ v = extendAlongSubsequenceCoproductDesc K s hs ≫ gsub) :
    gsub ≫ u ≫ v = gsub := by
  calc
    gsub ≫ u ≫ v = subsequenceCoproductInclusion K s hs ≫ gfull ≫ v := by
      simpa [Category.assoc] using congrArg (fun f ↦ f ≫ v) hu
    _ =
        subsequenceCoproductInclusion K s hs ≫
          (extendAlongSubsequenceCoproductDesc K s hs ≫ gsub) := by
            simpa [Category.assoc] using
              congrArg (fun f ↦ subsequenceCoproductInclusion K s hs ≫ f) hv
    _ =
        (subsequenceCoproductInclusion K s hs ≫
            extendAlongSubsequenceCoproductDesc K s hs) ≫ gsub := by
              simp [Category.assoc]
    _ = gsub := by
      simp [subsequenceCoproductInclusion_comp_extendAlongSubsequenceCoproductDesc]

/-- Helper for Lemma 13.33.4: the composite `v ≫ u` acts trivially on the full cocone map
because the correction homotopy identifies `extendAlongSubsequenceCoproductDesc ≫
subsequenceCoproductInclusion` with the identity modulo the telescope map. -/
private theorem subsequenceConeMap_rightComposite_on_cocone
    (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    [HasCoproduct K.obj] [HasCoproduct (hs.monotone.functor ⋙ K).obj]
    {Xsub Xfull : D}
    {gsub : ∐ (hs.monotone.functor ⋙ K).obj ⟶ Xsub}
    {δfull : Xfull ⟶ (∐ K.obj)⟦(1 : ℤ)⟧}
    {gfull : ∐ K.obj ⟶ Xfull}
    (hTfull :
      Triangle.mk (sequentialTelescopeMap K) gfull δfull ∈ distTriang D)
    (u : Xsub ⟶ Xfull)
    (hu : gsub ≫ u = subsequenceCoproductInclusion K s hs ≫ gfull)
    (v : Xfull ⟶ Xsub)
    (hv : gfull ≫ v = extendAlongSubsequenceCoproductDesc K s hs ≫ gsub) :
    gfull ≫ v ≫ u = gfull := by
  -- Proof comment: rewrite through `hu` and `hv`, then use the correction homotopy identity to
  -- kill the defect term by `sequentialTelescopeMap K ≫ gfull = 0`.
  have hrewrite :
      (extendAlongSubsequenceCoproductDesc K s hs ≫
          subsequenceCoproductInclusion K s hs) ≫ gfull = gfull := by
    have hdiff :
        gfull -
            (extendAlongSubsequenceCoproductDesc K s hs ≫
              subsequenceCoproductInclusion K s hs) ≫ gfull =
          0 := by
      have hzero_full : sequentialTelescopeMap K ≫ gfull = 0 := by
        simpa [Triangle.mk] using comp_distTriang_mor_zero₁₂ _ hTfull
      calc
        gfull -
            (extendAlongSubsequenceCoproductDesc K s hs ≫
              subsequenceCoproductInclusion K s hs) ≫ gfull =
          (𝟙 _ -
              extendAlongSubsequenceCoproductDesc K s hs ≫
                subsequenceCoproductInclusion K s hs) ≫ gfull := by
                  simp [Preadditive.sub_comp, Category.assoc]
        _ = subsequenceCorrectionHomotopy K s hs ≫ sequentialTelescopeMap K ≫ gfull := by
          simpa [Category.assoc] using
            congrArg
              (fun f ↦ f ≫ gfull)
              (subsequenceCorrectionHomotopy_comp_sequentialTelescopeMap K s hs).symm
        _ = 0 := by
          simpa [Category.assoc, hzero_full]
    exact (sub_eq_zero.mp hdiff).symm
  calc
    gfull ≫ v ≫ u = extendAlongSubsequenceCoproductDesc K s hs ≫ gsub ≫ u := by
      simpa [Category.assoc] using congrArg (fun f ↦ f ≫ u) hv
    _ =
        extendAlongSubsequenceCoproductDesc K s hs ≫
          (subsequenceCoproductInclusion K s hs ≫ gfull) := by
            simpa [Category.assoc] using
              congrArg (fun f ↦ extendAlongSubsequenceCoproductDesc K s hs ≫ f) hu
    _ =
        (extendAlongSubsequenceCoproductDesc K s hs ≫
            subsequenceCoproductInclusion K s hs) ≫ gfull := by
              simp [Category.assoc]
    _ = gfull := hrewrite

/-- Helper for Chap13 Lemma 13 33 4: the forward subsequence/full comparison on the first two
telescope vertices extends to a third-vertex map by the TR3 owner API. -/
private theorem forwardSubsequenceTriangleThirdMap
    (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    [HasCoproduct K.obj] [HasCoproduct (hs.monotone.functor ⋙ K).obj]
    {Xsub Xfull : D}
    {gsub : ∐ (hs.monotone.functor ⋙ K).obj ⟶ Xsub}
    {δsub : Xsub ⟶ (∐ (hs.monotone.functor ⋙ K).obj)⟦(1 : ℤ)⟧}
    {gfull : ∐ K.obj ⟶ Xfull}
    {δfull : Xfull ⟶ (∐ K.obj)⟦(1 : ℤ)⟧}
    (hTsub :
      Triangle.mk (sequentialTelescopeMap (hs.monotone.functor ⋙ K)) gsub δsub ∈ distTriang D)
    (hTfull :
      Triangle.mk (sequentialTelescopeMap K) gfull δfull ∈ distTriang D) :
    ∃ u : Xsub ⟶ Xfull,
      gsub ≫ u = subsequenceCoproductInclusion K s hs ≫ gfull ∧
      δsub ≫ (subsequenceIntervalBlockMap K s hs)⟦(1 : ℤ)⟧' = u ≫ δfull := by
  let S := hs.monotone.functor ⋙ K
  -- Proof comment: complete the explicit forward first square to a morphism of distinguished
  -- triangles, so the TR3 output already carries the needed third-vertex compatibility.
  obtain ⟨u, hu₂, hu₃⟩ :=
    complete_distinguished_triangle_morphism
      (Triangle.mk (sequentialTelescopeMap S) gsub δsub)
      (Triangle.mk (sequentialTelescopeMap K) gfull δfull)
      hTsub hTfull
      (subsequenceIntervalBlockMap K s hs)
      (subsequenceCoproductInclusion K s hs)
      (by simpa [S] using subsequence_interval_block_forward_square K s hs)
  exact ⟨u, hu₂, hu₃⟩

/-- Helper for Chap13 Lemma 13 33 4: the reverse subsequence/full comparison on the first two
telescope vertices extends directly to a third-vertex map, avoiding the old existential first-map
transfer route. -/
private theorem reverseSubsequenceTriangleThirdMap
    (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    [HasCoproduct K.obj] [HasCoproduct (hs.monotone.functor ⋙ K).obj]
    {Xsub Xfull : D}
    {gsub : ∐ (hs.monotone.functor ⋙ K).obj ⟶ Xsub}
    {δsub : Xsub ⟶ (∐ (hs.monotone.functor ⋙ K).obj)⟦(1 : ℤ)⟧}
    {gfull : ∐ K.obj ⟶ Xfull}
    {δfull : Xfull ⟶ (∐ K.obj)⟦(1 : ℤ)⟧}
    (hTsub :
      Triangle.mk (sequentialTelescopeMap (hs.monotone.functor ⋙ K)) gsub δsub ∈ distTriang D)
    (hTfull :
      Triangle.mk (sequentialTelescopeMap K) gfull δfull ∈ distTriang D) :
    ∃ v : Xfull ⟶ Xsub,
      gfull ≫ v = extendAlongSubsequenceCoproductDesc K s hs ≫ gsub ∧
      δfull ≫ (subsequenceCoproductProjection K s hs)⟦(1 : ℤ)⟧' = v ≫ δsub := by
  -- Proof comment: use the explicit reverse first square rather than transferring `comm₃`
  -- from an existential completion witness.
  obtain ⟨v, hv₂, hv₃⟩ :=
    complete_distinguished_triangle_morphism
      (Triangle.mk (sequentialTelescopeMap K) gfull δfull)
      (Triangle.mk (sequentialTelescopeMap (hs.monotone.functor ⋙ K)) gsub δsub)
      hTfull hTsub
      (subsequenceCoproductProjection K s hs)
      (extendAlongSubsequenceCoproductDesc K s hs)
      (sequentialTelescopeMap_comp_extendAlongSubsequenceCoproductDesc K s hs)
  exact ⟨v, hv₂, hv₃⟩

/-- Helper for Chap13 Lemma 13 33 4: the canonical forward third map is the TR3 completion of the
textbook first two comparison maps. -/
noncomputable def canonicalForwardSubsequenceConeMap
    (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    [HasCoproduct K.obj] [HasCoproduct (hs.monotone.functor ⋙ K).obj]
    {Xsub Xfull : D}
    {gsub : ∐ (hs.monotone.functor ⋙ K).obj ⟶ Xsub}
    {δsub : Xsub ⟶ (∐ (hs.monotone.functor ⋙ K).obj)⟦(1 : ℤ)⟧}
    {gfull : ∐ K.obj ⟶ Xfull}
    {δfull : Xfull ⟶ (∐ K.obj)⟦(1 : ℤ)⟧}
    (hTsub :
      Triangle.mk (sequentialTelescopeMap (hs.monotone.functor ⋙ K)) gsub δsub ∈ distTriang D)
    (hTfull :
      Triangle.mk (sequentialTelescopeMap K) gfull δfull ∈ distTriang D) :
    Xsub ⟶ Xfull :=
  Classical.choose (forwardSubsequenceTriangleThirdMap K s hs hTsub hTfull)

/-- Helper for Chap13 Lemma 13 33 4: the canonical forward third map has the required cocone
compatibility. -/
theorem canonicalForwardSubsequenceConeMap_comm₂
    (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    [HasCoproduct K.obj] [HasCoproduct (hs.monotone.functor ⋙ K).obj]
    {Xsub Xfull : D}
    {gsub : ∐ (hs.monotone.functor ⋙ K).obj ⟶ Xsub}
    {δsub : Xsub ⟶ (∐ (hs.monotone.functor ⋙ K).obj)⟦(1 : ℤ)⟧}
    {gfull : ∐ K.obj ⟶ Xfull}
    {δfull : Xfull ⟶ (∐ K.obj)⟦(1 : ℤ)⟧}
    (hTsub :
      Triangle.mk (sequentialTelescopeMap (hs.monotone.functor ⋙ K)) gsub δsub ∈ distTriang D)
    (hTfull :
      Triangle.mk (sequentialTelescopeMap K) gfull δfull ∈ distTriang D) :
    gsub ≫ canonicalForwardSubsequenceConeMap K s hs hTsub hTfull =
      subsequenceCoproductInclusion K s hs ≫ gfull := by
  exact (Classical.choose_spec (forwardSubsequenceTriangleThirdMap K s hs hTsub hTfull)).1

/-- Helper for Chap13 Lemma 13 33 4: the canonical forward third map also satisfies the shifted
triangle compatibility. -/
theorem canonicalForwardSubsequenceConeMap_comm₃
    (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    [HasCoproduct K.obj] [HasCoproduct (hs.monotone.functor ⋙ K).obj]
    {Xsub Xfull : D}
    {gsub : ∐ (hs.monotone.functor ⋙ K).obj ⟶ Xsub}
    {δsub : Xsub ⟶ (∐ (hs.monotone.functor ⋙ K).obj)⟦(1 : ℤ)⟧}
    {gfull : ∐ K.obj ⟶ Xfull}
    {δfull : Xfull ⟶ (∐ K.obj)⟦(1 : ℤ)⟧}
    (hTsub :
      Triangle.mk (sequentialTelescopeMap (hs.monotone.functor ⋙ K)) gsub δsub ∈ distTriang D)
    (hTfull :
      Triangle.mk (sequentialTelescopeMap K) gfull δfull ∈ distTriang D) :
    δsub ≫ (subsequenceIntervalBlockMap K s hs)⟦(1 : ℤ)⟧' =
      canonicalForwardSubsequenceConeMap K s hs hTsub hTfull ≫ δfull := by
  exact (Classical.choose_spec (forwardSubsequenceTriangleThirdMap K s hs hTsub hTfull)).2

/-- Helper for Chap13 Lemma 13 33 4: the canonical reverse third map is the TR3 completion of the
reverse textbook comparison square. -/
noncomputable def canonicalReverseSubsequenceConeMap
    (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    [HasCoproduct K.obj] [HasCoproduct (hs.monotone.functor ⋙ K).obj]
    {Xsub Xfull : D}
    {gsub : ∐ (hs.monotone.functor ⋙ K).obj ⟶ Xsub}
    {δsub : Xsub ⟶ (∐ (hs.monotone.functor ⋙ K).obj)⟦(1 : ℤ)⟧}
    {gfull : ∐ K.obj ⟶ Xfull}
    {δfull : Xfull ⟶ (∐ K.obj)⟦(1 : ℤ)⟧}
    (hTsub :
      Triangle.mk (sequentialTelescopeMap (hs.monotone.functor ⋙ K)) gsub δsub ∈ distTriang D)
    (hTfull :
      Triangle.mk (sequentialTelescopeMap K) gfull δfull ∈ distTriang D) :
    Xfull ⟶ Xsub :=
  Classical.choose (reverseSubsequenceTriangleThirdMap K s hs hTsub hTfull)

/-- Helper for Chap13 Lemma 13 33 4: the canonical reverse third map has the required cocone
compatibility. -/
theorem canonicalReverseSubsequenceConeMap_comm₂
    (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    [HasCoproduct K.obj] [HasCoproduct (hs.monotone.functor ⋙ K).obj]
    {Xsub Xfull : D}
    {gsub : ∐ (hs.monotone.functor ⋙ K).obj ⟶ Xsub}
    {δsub : Xsub ⟶ (∐ (hs.monotone.functor ⋙ K).obj)⟦(1 : ℤ)⟧}
    {gfull : ∐ K.obj ⟶ Xfull}
    {δfull : Xfull ⟶ (∐ K.obj)⟦(1 : ℤ)⟧}
    (hTsub :
      Triangle.mk (sequentialTelescopeMap (hs.monotone.functor ⋙ K)) gsub δsub ∈ distTriang D)
    (hTfull :
      Triangle.mk (sequentialTelescopeMap K) gfull δfull ∈ distTriang D) :
    gfull ≫ canonicalReverseSubsequenceConeMap K s hs hTsub hTfull =
      extendAlongSubsequenceCoproductDesc K s hs ≫ gsub := by
  exact (Classical.choose_spec (reverseSubsequenceTriangleThirdMap K s hs hTsub hTfull)).1

/-- Helper for Chap13 Lemma 13 33 4: the canonical reverse third map also satisfies the shifted
triangle compatibility. -/
theorem canonicalReverseSubsequenceConeMap_comm₃
    (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    [HasCoproduct K.obj] [HasCoproduct (hs.monotone.functor ⋙ K).obj]
    {Xsub Xfull : D}
    {gsub : ∐ (hs.monotone.functor ⋙ K).obj ⟶ Xsub}
    {δsub : Xsub ⟶ (∐ (hs.monotone.functor ⋙ K).obj)⟦(1 : ℤ)⟧}
    {gfull : ∐ K.obj ⟶ Xfull}
    {δfull : Xfull ⟶ (∐ K.obj)⟦(1 : ℤ)⟧}
    (hTsub :
      Triangle.mk (sequentialTelescopeMap (hs.monotone.functor ⋙ K)) gsub δsub ∈ distTriang D)
    (hTfull :
      Triangle.mk (sequentialTelescopeMap K) gfull δfull ∈ distTriang D) :
    δfull ≫ (subsequenceCoproductProjection K s hs)⟦(1 : ℤ)⟧' =
      canonicalReverseSubsequenceConeMap K s hs hTsub hTfull ≫ δsub := by
  exact (Classical.choose_spec (reverseSubsequenceTriangleThirdMap K s hs hTsub hTfull)).2

/-- Helper for Chap13 Lemma 13 33 4: if `ε : X ⟶ X` satisfies `ε ≫ ε = 0`, then `𝟙 X - ε` is an
isomorphism with inverse `𝟙 X + ε`. -/
private theorem sub_id_isIso_of_square_zero {X : D} (ε : X ⟶ X) (hε : ε ≫ ε = 0) :
    IsIso (𝟙 X - ε) := by
  refine IsIso.mk' ?_
  refine ⟨𝟙 X + ε, ?_, ?_⟩
  · -- Proof comment: expand the product and use the square-zero relation to cancel the defect.
    calc
      (𝟙 X - ε) ≫ (𝟙 X + ε) =
          𝟙 X ≫ 𝟙 X + 𝟙 X ≫ ε - ε ≫ 𝟙 X - ε ≫ ε := by
            simp [Preadditive.sub_comp, Preadditive.comp_add, Preadditive.comp_sub, Category.assoc]
      _ = 𝟙 X := by
        simp [hε]
        abel
  · -- Proof comment: the same expansion works on the other side because both factors are
    -- endomorphisms of the same object.
    calc
      (𝟙 X + ε) ≫ (𝟙 X - ε) =
          𝟙 X ≫ 𝟙 X - 𝟙 X ≫ ε + ε ≫ 𝟙 X - ε ≫ ε := by
            simp [Preadditive.sub_comp, Preadditive.comp_add, Preadditive.comp_sub, Category.assoc]
      _ = 𝟙 X := by
        simp [hε]
        abel

/-- Helper for Chap13 Lemma 13 33 4: the full-side comparison defect
`ε := 𝟙 Xfull - v ≫ u` already vanishes after composition with `δfull`. -/
private theorem subsequenceConeMapRightCompositeDefectCompShiftEqZero
    (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    [HasCoproduct K.obj] [HasCoproduct (hs.monotone.functor ⋙ K).obj]
    {Xsub Xfull : D}
    {gsub : ∐ (hs.monotone.functor ⋙ K).obj ⟶ Xsub}
    {δsub : Xsub ⟶ (∐ (hs.monotone.functor ⋙ K).obj)⟦(1 : ℤ)⟧}
    {gfull : ∐ K.obj ⟶ Xfull}
    {δfull : Xfull ⟶ (∐ K.obj)⟦(1 : ℤ)⟧}
    (hTfull :
      Triangle.mk (sequentialTelescopeMap K) gfull δfull ∈ distTriang D)
    {u : Xsub ⟶ Xfull}
    (huδ :
      δsub ≫ (subsequenceIntervalBlockMap K s hs)⟦(1 : ℤ)⟧' = u ≫ δfull)
    {v : Xfull ⟶ Xsub}
    (hvδ :
      δfull ≫ (subsequenceCoproductProjection K s hs)⟦(1 : ℤ)⟧' = v ≫ δsub) :
    let ε : Xfull ⟶ Xfull := 𝟙 _ - v ≫ u
    in ε ≫ δfull = 0 := by
  let Tfull := Triangle.mk (sequentialTelescopeMap K) gfull δfull
  let ε : Xfull ⟶ Xfull := 𝟙 _ - v ≫ u
  -- Proof comment: rewrite `v ≫ u ≫ δfull` through the two `comm₃` relations and then use the
  -- symmetric correction identity to factor through `sequentialTelescopeMap K`.
  have hcomposite :
      v ≫ u ≫ δfull =
        δfull ≫ (subsequenceCoproductProjection K s hs ≫
          subsequenceIntervalBlockMap K s hs)⟦(1 : ℤ)⟧' := by
    calc
      v ≫ u ≫ δfull = v ≫ (u ≫ δfull) := by simp [Category.assoc]
      _ = v ≫ (δsub ≫ (subsequenceIntervalBlockMap K s hs)⟦(1 : ℤ)⟧') := by
        rw [← huδ]
      _ = (v ≫ δsub) ≫ (subsequenceIntervalBlockMap K s hs)⟦(1 : ℤ)⟧' := by
        simp [Category.assoc]
      _ = (δfull ≫ (subsequenceCoproductProjection K s hs)⟦(1 : ℤ)⟧') ≫
            (subsequenceIntervalBlockMap K s hs)⟦(1 : ℤ)⟧' := by
              rw [← hvδ]
      _ =
          δfull ≫
            ((subsequenceCoproductProjection K s hs)⟦(1 : ℤ)⟧' ≫
              (subsequenceIntervalBlockMap K s hs)⟦(1 : ℤ)⟧') := by
                simp [Category.assoc]
      _ =
          δfull ≫ (subsequenceCoproductProjection K s hs ≫
            subsequenceIntervalBlockMap K s hs)⟦(1 : ℤ)⟧' := by
              simp [Functor.map_comp, Category.assoc]
  calc
    ε ≫ δfull = δfull - v ≫ u ≫ δfull := by
      simp [ε, Preadditive.sub_comp, Category.assoc]
    _ =
        δfull ≫
          (𝟙 _ - subsequenceCoproductProjection K s hs ≫
            subsequenceIntervalBlockMap K s hs)⟦(1 : ℤ)⟧' := by
              rw [hcomposite]
              simp [Preadditive.comp_sub, Category.assoc]
    _ =
        δfull ≫
          (sequentialTelescopeMap K ≫ subsequenceCorrectionHomotopy K s hs)⟦(1 : ℤ)⟧' := by
            rw [sequentialTelescopeMap_comp_subsequenceCorrectionHomotopy K s hs]
    _ =
        δfull ≫ (sequentialTelescopeMap K)⟦(1 : ℤ)⟧' ≫
          (subsequenceCorrectionHomotopy K s hs)⟦(1 : ℤ)⟧' := by
            simp [Functor.map_comp, Category.assoc]
    _ = 0 := by
      simp [Category.assoc, Tfull, comp_distTriang_mor_zero₃₁ _ hTfull]

/-- Helper for Chap13 Lemma 13 33 4: the full-side comparison defect
`ε := 𝟙 Xfull - v ≫ u` has square zero for the canonical forward/reverse triangle maps. -/
theorem subsequenceConeMapRightCompositeDefectSqZero
    (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    [HasCoproduct K.obj] [HasCoproduct (hs.monotone.functor ⋙ K).obj]
    {Xsub Xfull : D}
    {gsub : ∐ (hs.monotone.functor ⋙ K).obj ⟶ Xsub}
    {δsub : Xsub ⟶ (∐ (hs.monotone.functor ⋙ K).obj)⟦(1 : ℤ)⟧}
    {gfull : ∐ K.obj ⟶ Xfull}
    {δfull : Xfull ⟶ (∐ K.obj)⟦(1 : ℤ)⟧}
    (hTsub :
      Triangle.mk (sequentialTelescopeMap (hs.monotone.functor ⋙ K)) gsub δsub ∈ distTriang D)
    (hTfull :
      Triangle.mk (sequentialTelescopeMap K) gfull δfull ∈ distTriang D)
    {u : Xsub ⟶ Xfull}
    (hu : gsub ≫ u = subsequenceCoproductInclusion K s hs ≫ gfull)
    (huδ :
      δsub ≫ (subsequenceIntervalBlockMap K s hs)⟦(1 : ℤ)⟧' = u ≫ δfull)
    {v : Xfull ⟶ Xsub}
    (hv : gfull ≫ v = extendAlongSubsequenceCoproductDesc K s hs ≫ gsub)
    (hvδ :
      δfull ≫ (subsequenceCoproductProjection K s hs)⟦(1 : ℤ)⟧' = v ≫ δsub) :
    let ε : Xfull ⟶ Xfull := 𝟙 _ - v ≫ u
    in ε ≫ ε = 0 := by
  let Tfull := Triangle.mk (sequentialTelescopeMap K) gfull δfull
  let ε : Xfull ⟶ Xfull := 𝟙 _ - v ≫ u
  have hzero_left : gfull ≫ ε = 0 := by
    -- Proof comment: the right composite acts trivially on the cocone map `gfull`.
    have hcomp := subsequenceConeMap_rightComposite_on_cocone K s hs hTfull u hu v hv
    calc
      gfull ≫ ε = gfull - gfull ≫ v ≫ u := by
        simp [ε, Preadditive.comp_sub, Category.assoc]
      _ = 0 := by
        rw [hcomp]
        abel
  have hzero_right : ε ≫ δfull = 0 := by
    -- Proof comment: the shifted-boundary vanishing is the heavy half of the defect calculation,
    -- so it is isolated in a separate helper.
    simpa [ε] using
      subsequenceConeMapRightCompositeDefectCompShiftEqZero
        (K := K) (s := s) (hs := hs) hTfull huδ hvδ
  obtain ⟨α, hα⟩ := Tfull.yoneda_exact₃ hTfull ε hzero_left
  obtain ⟨β, hβ⟩ := Tfull.coyoneda_exact₃ hTfull ε hzero_right
  -- Proof comment: factor the same defect through both `δfull` and `gfull`, then the middle
  -- composite vanishes because `gfull ≫ δfull = 0`.
  calc
    ε ≫ ε = (β ≫ gfull) ≫ (δfull ≫ α) := by rw [hβ, hα]
    _ = β ≫ (gfull ≫ δfull) ≫ α := by simp [Category.assoc]
    _ = 0 := by simp [Category.assoc, Tfull, comp_distTriang_mor_zero₂₃ _ hTfull]

/-- Helper for Chap13 Lemma 13 33 4: package the canonical forward comparison data as a triangle
morphism so later proofs do not have to re-elaborate the full `Triangle.homMk` term. -/
private noncomputable def canonicalForwardSubsequenceTriangleHom
    (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    [HasCoproduct K.obj] [HasCoproduct (hs.monotone.functor ⋙ K).obj]
    {Xsub Xfull : D}
    {gsub : ∐ (hs.monotone.functor ⋙ K).obj ⟶ Xsub}
    {δsub : Xsub ⟶ (∐ (hs.monotone.functor ⋙ K).obj)⟦(1 : ℤ)⟧}
    {gfull : ∐ K.obj ⟶ Xfull}
    {δfull : Xfull ⟶ (∐ K.obj)⟦(1 : ℤ)⟧}
    (hTsub :
      Triangle.mk (sequentialTelescopeMap (hs.monotone.functor ⋙ K)) gsub δsub ∈ distTriang D)
    (hTfull :
      Triangle.mk (sequentialTelescopeMap K) gfull δfull ∈ distTriang D) :
    Triangle.mk (sequentialTelescopeMap (hs.monotone.functor ⋙ K)) gsub δsub ⟶
      Triangle.mk (sequentialTelescopeMap K) gfull δfull :=
  Triangle.homMk _ _
    (subsequenceIntervalBlockMap K s hs)
    (subsequenceCoproductInclusion K s hs)
    (canonicalForwardSubsequenceConeMap K s hs hTsub hTfull)
    (subsequence_interval_block_forward_square K s hs)
    (canonicalForwardSubsequenceConeMap_comm₂ K s hs hTsub hTfull)
    (canonicalForwardSubsequenceConeMap_comm₃ K s hs hTsub hTfull)

/-- Helper for Chap13 Lemma 13 33 4: package the canonical reverse comparison data as a triangle
morphism so later proofs can reuse the same normalized owner-level map. -/
private noncomputable def canonicalReverseSubsequenceTriangleHom
    (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    [HasCoproduct K.obj] [HasCoproduct (hs.monotone.functor ⋙ K).obj]
    {Xsub Xfull : D}
    {gsub : ∐ (hs.monotone.functor ⋙ K).obj ⟶ Xsub}
    {δsub : Xsub ⟶ (∐ (hs.monotone.functor ⋙ K).obj)⟦(1 : ℤ)⟧}
    {gfull : ∐ K.obj ⟶ Xfull}
    {δfull : Xfull ⟶ (∐ K.obj)⟦(1 : ℤ)⟧}
    (hTsub :
      Triangle.mk (sequentialTelescopeMap (hs.monotone.functor ⋙ K)) gsub δsub ∈ distTriang D)
    (hTfull :
      Triangle.mk (sequentialTelescopeMap K) gfull δfull ∈ distTriang D) :
    Triangle.mk (sequentialTelescopeMap K) gfull δfull ⟶
      Triangle.mk (sequentialTelescopeMap (hs.monotone.functor ⋙ K)) gsub δsub :=
  Triangle.homMk _ _
    (subsequenceCoproductProjection K s hs)
    (extendAlongSubsequenceCoproductDesc K s hs)
    (canonicalReverseSubsequenceConeMap K s hs hTsub hTfull)
    (sequentialTelescopeMap_comp_extendAlongSubsequenceCoproductDesc K s hs)
    (canonicalReverseSubsequenceConeMap_comm₂ K s hs hTsub hTfull)
    (canonicalReverseSubsequenceConeMap_comm₃ K s hs hTsub hTfull)

/-- Helper for Chap13 Lemma 13 33 4: the first component of the forward-then-reverse canonical
triangle composite is already the known isomorphism `b ≫ d`. -/
private noncomputable theorem canonicalForwardReverseTriangleCompositeHom1IsIso
    (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    [HasCoproduct K.obj] [HasCoproduct (hs.monotone.functor ⋙ K).obj]
    {Xsub Xfull : D}
    {gsub : ∐ (hs.monotone.functor ⋙ K).obj ⟶ Xsub}
    {δsub : Xsub ⟶ (∐ (hs.monotone.functor ⋙ K).obj)⟦(1 : ℤ)⟧}
    {gfull : ∐ K.obj ⟶ Xfull}
    {δfull : Xfull ⟶ (∐ K.obj)⟦(1 : ℤ)⟧}
    (hTsub :
      Triangle.mk (sequentialTelescopeMap (hs.monotone.functor ⋙ K)) gsub δsub ∈ distTriang D)
    (hTfull :
      Triangle.mk (sequentialTelescopeMap K) gfull δfull ∈ distTriang D) :
    IsIso
      ((canonicalForwardSubsequenceTriangleHom K s hs hTsub hTfull ≫
          canonicalReverseSubsequenceTriangleHom K s hs hTsub hTfull).hom₁) := by
  -- Proof comment: after packaging the triangle maps once, the first component is exactly the
  -- interval-block inclusion followed by the selected projection.
  simpa [canonicalForwardSubsequenceTriangleHom, canonicalReverseSubsequenceTriangleHom] using
    (show IsIso
      (subsequenceIntervalBlockMap K s hs ≫ subsequenceCoproductProjection K s hs) by
        rw [subsequenceIntervalBlockMap_comp_subsequenceCoproductProjection]
        infer_instance)

/-- Helper for Chap13 Lemma 13 33 4: the second component of the forward-then-reverse canonical
triangle composite is already the known isomorphism `a ≫ c`. -/
private noncomputable theorem canonicalForwardReverseTriangleCompositeHom2IsIso
    (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    [HasCoproduct K.obj] [HasCoproduct (hs.monotone.functor ⋙ K).obj]
    {Xsub Xfull : D}
    {gsub : ∐ (hs.monotone.functor ⋙ K).obj ⟶ Xsub}
    {δsub : Xsub ⟶ (∐ (hs.monotone.functor ⋙ K).obj)⟦(1 : ℤ)⟧}
    {gfull : ∐ K.obj ⟶ Xfull}
    {δfull : Xfull ⟶ (∐ K.obj)⟦(1 : ℤ)⟧}
    (hTsub :
      Triangle.mk (sequentialTelescopeMap (hs.monotone.functor ⋙ K)) gsub δsub ∈ distTriang D)
    (hTfull :
      Triangle.mk (sequentialTelescopeMap K) gfull δfull ∈ distTriang D) :
    IsIso
      ((canonicalForwardSubsequenceTriangleHom K s hs hTsub hTfull ≫
          canonicalReverseSubsequenceTriangleHom K s hs hTsub hTfull).hom₂) := by
  -- Proof comment: the second component of the packaged composite normalizes to the canonical
  -- inclusion followed by the extension map back to the subsequence coproduct.
  simpa [canonicalForwardSubsequenceTriangleHom, canonicalReverseSubsequenceTriangleHom] using
    (show IsIso
      (subsequenceCoproductInclusion K s hs ≫ extendAlongSubsequenceCoproductDesc K s hs) by
        rw [subsequenceCoproductInclusion_comp_extendAlongSubsequenceCoproductDesc]
        infer_instance)

/-- Helper for Chap13 Lemma 13 33 4: the third component of the packaged forward-then-reverse
triangle composite is an isomorphism by the distinguished-triangle two-out-of-three principle. -/
noncomputable theorem canonicalForwardReverseTriangleCompositeHom3IsIso
    (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    [HasCoproduct K.obj] [HasCoproduct (hs.monotone.functor ⋙ K).obj]
    {Xsub Xfull : D}
    {gsub : ∐ (hs.monotone.functor ⋙ K).obj ⟶ Xsub}
    {δsub : Xsub ⟶ (∐ (hs.monotone.functor ⋙ K).obj)⟦(1 : ℤ)⟧}
    {gfull : ∐ K.obj ⟶ Xfull}
    {δfull : Xfull ⟶ (∐ K.obj)⟦(1 : ℤ)⟧}
    (hTsub :
      Triangle.mk (sequentialTelescopeMap (hs.monotone.functor ⋙ K)) gsub δsub ∈ distTriang D)
    (hTfull :
      Triangle.mk (sequentialTelescopeMap K) gfull δfull ∈ distTriang D) :
    IsIso
      ((canonicalForwardSubsequenceTriangleHom K s hs hTsub hTfull ≫
          canonicalReverseSubsequenceTriangleHom K s hs hTsub hTfull).hom₃) := by
  let φ :=
    canonicalForwardSubsequenceTriangleHom K s hs hTsub hTfull ≫
      canonicalReverseSubsequenceTriangleHom K s hs hTsub hTfull
  -- Route correction: package the composite once and let `isIso₃_of_isIso₁₂` consume the two
  -- already-normalized component isomorphisms, rather than re-expanding the comparison maps here.
  have hIso₁ : IsIso φ.hom₁ := by
    simpa [φ] using canonicalForwardReverseTriangleCompositeHom1IsIso K s hs hTsub hTfull
  have hIso₂ : IsIso φ.hom₂ := by
    simpa [φ] using canonicalForwardReverseTriangleCompositeHom2IsIso K s hs hTsub hTfull
  exact Pretriangulated.isIso₃_of_isIso₁₂ φ hTsub hTsub hIso₁ hIso₂

/-- Helper for Chap13 Lemma 13 33 4: the canonical forward/reverse comparison maps have
invertible composite on the subsequence cone object. -/
noncomputable theorem subsequenceForwardReverseCompositeIsIso
    (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    [HasCoproduct K.obj] [HasCoproduct (hs.monotone.functor ⋙ K).obj]
    {Xsub Xfull : D}
    {gsub : ∐ (hs.monotone.functor ⋙ K).obj ⟶ Xsub}
    {δsub : Xsub ⟶ (∐ (hs.monotone.functor ⋙ K).obj)⟦(1 : ℤ)⟧}
    {gfull : ∐ K.obj ⟶ Xfull}
    {δfull : Xfull ⟶ (∐ K.obj)⟦(1 : ℤ)⟧}
    (hTsub :
      Triangle.mk (sequentialTelescopeMap (hs.monotone.functor ⋙ K)) gsub δsub ∈ distTriang D)
    (hTfull :
      Triangle.mk (sequentialTelescopeMap K) gfull δfull ∈ distTriang D) :
    IsIso
      (canonicalForwardSubsequenceConeMap K s hs hTsub hTfull ≫
        canonicalReverseSubsequenceConeMap K s hs hTsub hTfull) := by
  -- Proof comment: the cone-map composite is the third component of the packaged forward/reverse
  -- triangle morphism, so the new owner-level `hom₃` theorem closes this wrapper immediately.
  simpa [canonicalForwardSubsequenceTriangleHom, canonicalReverseSubsequenceTriangleHom] using
    canonicalForwardReverseTriangleCompositeHom3IsIso K s hs hTsub hTfull

end

end CategoryTheory
