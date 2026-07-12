import StacksProject_2024.Chap13.Lemma_13_33_4.SubsequenceCoproductData

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- Helper for Chap13 Lemma 13 33 4: transport a homotopy-colimit presentation across an
isomorphism of the cone object. -/
private theorem isHomotopyColimitOf_of_iso
    (S : ℕ ⥤ D) [HasCoproduct S.obj] {X Y : D} (e : X ≅ Y)
    (hY : IsHomotopyColimitOf S Y) :
    IsHomotopyColimitOf S X := by
  rcases hY with ⟨g, δ, hT⟩
  let TX : Triangle D := Triangle.mk (sequentialTelescopeMap S) (g ≫ e.inv) (e.hom ≫ δ)
  let TY : Triangle D := Triangle.mk (sequentialTelescopeMap S) g δ
  have hIso : TX ≅ TY := by
    -- Proof comment: only the cone object changes, so the triangle comparison is the identity on
    -- the two coproduct vertices and `e` on the third vertex.
    refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e ?_ ?_ ?_
    · simp [TX, TY]
    · simp [TX, TY, Category.assoc]
    · simp [TX, TY]
  refine ⟨g ≫ e.inv, e.hom ≫ δ, ?_⟩
  -- Proof comment: transport distinguishedness across the triangle isomorphism.
  simpa [TX, TY] using (distinguished_iff_of_iso hIso).2 hT

-- Route correction: the higher-level subsequence comparison subtree is not usable in the current
-- repo state because it imports support files with hard compile errors. This wrapper therefore
-- rebuilds only the thin TR3 comparison layer from the stable low-level subsequence coproduct data.
/-- Helper for Chap13 Lemma 13 33 4: the forward subsequence/full comparison on the first two
telescope vertices extends to a third-vertex map by TR3. -/
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
  -- Proof comment: the forward first square is already available from the low-level interval-block
  -- API, so TR3 provides the missing third map and its two compatibilities.
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
telescope vertices extends to a third-vertex map by TR3. -/
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
  -- Proof comment: the reverse first square is the direct low-level identity
  -- `(1 - f) ≫ c = d ≫ (1 - g)`, so TR3 again supplies the third component.
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
forward subsequence comparison square. -/
private noncomputable def canonicalForwardSubsequenceConeMap
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

/-- Helper for Chap13 Lemma 13 33 4: the canonical forward third map has the expected cocone
compatibility. -/
private theorem canonicalForwardSubsequenceConeMap_comm₂
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
private theorem canonicalForwardSubsequenceConeMap_comm₃
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
reverse subsequence comparison square. -/
private noncomputable def canonicalReverseSubsequenceConeMap
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

/-- Helper for Chap13 Lemma 13 33 4: the canonical reverse third map has the expected cocone
compatibility. -/
private theorem canonicalReverseSubsequenceConeMap_comm₂
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
private theorem canonicalReverseSubsequenceConeMap_comm₃
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
  · -- Proof comment: expand the left inverse and cancel the square-zero defect.
    calc
      (𝟙 X + ε) ≫ (𝟙 X - ε) =
          𝟙 X - ε ≫ ε := by
            simp [Preadditive.sub_comp, Preadditive.comp_add, Preadditive.comp_sub]
            abel
      _ = 𝟙 X := by
        simp [hε]
  · -- Proof comment: the right inverse computation is symmetric.
    calc
      (𝟙 X - ε) ≫ (𝟙 X + ε) =
          𝟙 X - ε ≫ ε := by
            simp [Preadditive.sub_comp, Preadditive.comp_add, Preadditive.comp_sub]
      _ = 𝟙 X := by
        simp [hε]

/-- Helper for Chap13 Lemma 13 33 4: the full-side composite `v ≫ u` acts trivially on the full
cocone map once the first two comparison squares commute. -/
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
  -- Proof comment: rewrite `gfull ≫ v ≫ u` using the two cocone compatibilities and then use the
  -- correction identity to collapse the resulting defect.
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

/-- Helper for Chap13 Lemma 13 33 4: the full-side defect `𝟙 - v ≫ u` kills the connecting map
once the two comparison maps satisfy the shifted triangle identities. -/
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
    (𝟙 _ - v ≫ u) ≫ δfull = 0 := by
  let Tfull := Triangle.mk (sequentialTelescopeMap K) gfull δfull
  let ε : Xfull ⟶ Xfull := 𝟙 _ - v ≫ u
  have hcomposite :
      v ≫ u ≫ δfull =
        δfull ≫ (subsequenceCoproductProjection K s hs ≫
          subsequenceIntervalBlockMap K s hs)⟦(1 : ℤ)⟧' := by
    -- Proof comment: commute `u` and `v` across the shifted structure maps using the two TR3
    -- compatibility equalities.
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
  have hεδ : ε ≫ δfull = 0 := by
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
        have hzero :
            δfull ≫ (sequentialTelescopeMap K)⟦(1 : ℤ)⟧' = 0 := by
          simpa [Tfull] using comp_distTriang_mor_zero₃₁ Tfull hTfull
        simpa [Category.assoc] using
          congrArg
            (fun f ↦ f ≫ (subsequenceCorrectionHomotopy K s hs)⟦(1 : ℤ)⟧')
            hzero
  simpa [ε] using hεδ

/-- Helper for Chap13 Lemma 13 33 4: the full-side defect `𝟙 - v ≫ u` has square zero once the
forward and reverse comparison maps satisfy the two cocone and shifted compatibilities. -/
private theorem subsequenceConeMapRightCompositeDefectSqZero
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
    (𝟙 _ - v ≫ u) ≫ (𝟙 _ - v ≫ u) = 0 := by
  let Tfull := Triangle.mk (sequentialTelescopeMap K) gfull δfull
  let ε : Xfull ⟶ Xfull := 𝟙 _ - v ≫ u
  have hzero_left : gfull ≫ ε = 0 := by
    have hcomp := subsequenceConeMap_rightComposite_on_cocone K s hs hTfull u hu v hv
    -- Proof comment: the right composite fixes the cocone map, so the defect vanishes after
    -- precomposition with `gfull`.
    calc
      gfull ≫ ε = gfull - gfull ≫ v ≫ u := by
        simp [ε, Preadditive.comp_sub, Category.assoc]
      _ = 0 := by
        rw [hcomp]
        abel
  have hzero_right : ε ≫ δfull = 0 := by
    -- Proof comment: the shifted-boundary vanishing is the hard half of the square-zero
    -- calculation, so it is isolated in the preceding helper.
    simpa [ε] using
      subsequenceConeMapRightCompositeDefectCompShiftEqZero
        (K := K) (s := s) (hs := hs)
        (gsub := gsub) (δsub := δsub) (gfull := gfull) (δfull := δfull)
        hTfull huδ hvδ
  obtain ⟨α, hα⟩ := Tfull.yoneda_exact₃ hTfull ε hzero_left
  obtain ⟨β, hβ⟩ := Tfull.coyoneda_exact₃ hTfull ε hzero_right
  have hε : ε ≫ ε = 0 := by
    -- Proof comment: factor the same defect through both `gfull` and `δfull`; the middle
    -- composite is zero in any distinguished triangle.
    have hzero : gfull ≫ δfull = 0 := by
      simpa [Tfull] using comp_distTriang_mor_zero₂₃ Tfull hTfull
    dsimp [Tfull] at hα hβ
    calc
      ε ≫ ε = (β ≫ gfull) ≫ ε := by
        nth_rewrite 1 [hβ]
        rfl
      _ = (β ≫ gfull) ≫ (δfull ≫ α) := by rw [hα]
      _ = β ≫ (gfull ≫ δfull) ≫ α := by simp [Category.assoc]
      _ = β ≫ 0 ≫ α := by
        exact congrArg (fun f ↦ β ≫ f ≫ α) hzero
      _ = 0 := by simp
  simpa [ε] using hε

/-- Helper for Chap13 Lemma 13 33 4: package the canonical forward comparison data as a triangle
morphism, so later proofs can apply `isIso₃_of_isIso₁₂` at the owner level. -/
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
morphism, again keeping the later isomorphism argument at the triangle level. -/
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

/-- Helper for Chap13 Lemma 13 33 4: the canonical forward/reverse composite is an isomorphism on
the subsequence cone object because it is the third component of a triangle endomorphism whose
first two components are identities. -/
private theorem subsequenceForwardReverseCompositeIsIso
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
  let φ :=
    canonicalForwardSubsequenceTriangleHom K s hs hTsub hTfull ≫
      canonicalReverseSubsequenceTriangleHom K s hs hTsub hTfull
  have hIso₁ : IsIso φ.hom₁ := by
    -- Proof comment: the first component normalizes to `b ≫ d = 𝟙`.
    simpa [φ, canonicalForwardSubsequenceTriangleHom, canonicalReverseSubsequenceTriangleHom] using
      (show IsIso
        (subsequenceIntervalBlockMap K s hs ≫ subsequenceCoproductProjection K s hs) by
          rw [subsequenceIntervalBlockMap_comp_subsequenceCoproductProjection]
          infer_instance)
  have hIso₂ : IsIso φ.hom₂ := by
    -- Proof comment: the second component normalizes to `a ≫ c = 𝟙`.
    simpa [φ, canonicalForwardSubsequenceTriangleHom, canonicalReverseSubsequenceTriangleHom] using
      (show IsIso
        (subsequenceCoproductInclusion K s hs ≫ extendAlongSubsequenceCoproductDesc K s hs) by
          rw [subsequenceCoproductInclusion_comp_extendAlongSubsequenceCoproductDesc]
          infer_instance)
  -- Proof comment: two-out-of-three for morphisms of distinguished triangles upgrades those two
  -- component isomorphisms to an isomorphism on the cone object.
  simpa [φ, canonicalForwardSubsequenceTriangleHom, canonicalReverseSubsequenceTriangleHom] using
    (Pretriangulated.isIso₃_of_isIso₁₂ φ hTsub hTsub hIso₁ hIso₂)

/-- Helper for Chap13 Lemma 13 33 4: if both end composites `u ≫ v` and `v ≫ u` are
isomorphisms, then `u` itself is an isomorphism. -/
private theorem isIso_of_isIso_endComposites
    {X Y : D} (u : X ⟶ Y) (v : Y ⟶ X)
    [IsIso (u ≫ v)] [IsIso (v ≫ u)] :
    IsIso u := by
  -- Proof comment: one composite makes `u` mono and the other makes `u` epi, so balancedness
  -- gives the desired isomorphism.
  letI : Mono u := mono_of_mono u v
  letI : Epi u := epi_of_epi v u
  exact isIso_of_mono_of_epi u

/-- Lemma 13.33.4: for chosen telescope-triangle presentations of the homotopy colimits of a
strictly increasing subsequence and of the original sequential diagram, there exists an
isomorphism between the cone objects compatible with the structure maps from the selected stages.
-/
@[stacks 0CRJ]
theorem exists_homotopyColimitIso_of_subsequence
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
    ∃ e : Xsub ≅ Xfull,
      gsub ≫ e.hom = subsequenceCoproductInclusion K s hs ≫ gfull := by
  let u₀ := canonicalForwardSubsequenceConeMap K s hs hTsub hTfull
  let v₀ := canonicalReverseSubsequenceConeMap K s hs hTsub hTfull
  have hRightDefectSqZero :
      (𝟙 _ - v₀ ≫ u₀) ≫ (𝟙 _ - v₀ ≫ u₀) = 0 := by
    -- Proof comment: specialize the generic square-zero defect calculation to the canonical
    -- forward and reverse comparison maps.
    simpa [u₀, v₀] using
      subsequenceConeMapRightCompositeDefectSqZero
        (K := K) (s := s) (hs := hs) hTsub hTfull
        (u := u₀)
        (by simpa [u₀] using canonicalForwardSubsequenceConeMap_comm₂ K s hs hTsub hTfull)
        (by simpa [u₀] using canonicalForwardSubsequenceConeMap_comm₃ K s hs hTsub hTfull)
        (v := v₀)
        (by simpa [v₀] using canonicalReverseSubsequenceConeMap_comm₂ K s hs hTsub hTfull)
        (by simpa [v₀] using canonicalReverseSubsequenceConeMap_comm₃ K s hs hTsub hTfull)
  haveI : IsIso (u₀ ≫ v₀) := by
    -- Proof comment: on the subsequence side the composite is the third component of a triangle
    -- endomorphism whose other two components are identities.
    simpa [u₀, v₀] using subsequenceForwardReverseCompositeIsIso K s hs hTsub hTfull
  haveI : IsIso (v₀ ≫ u₀) := by
    let ε : Xfull ⟶ Xfull := 𝟙 _ - v₀ ≫ u₀
    have hε : ε ≫ ε = 0 := by
      simpa [ε] using hRightDefectSqZero
    have hvu : v₀ ≫ u₀ = 𝟙 _ - ε := by
      dsimp [ε]
      abel
    rw [hvu]
    exact sub_id_isIso_of_square_zero ε hε
  haveI : IsIso u₀ := isIso_of_isIso_endComposites u₀ v₀
  refine ⟨asIso u₀, ?_⟩
  -- Proof comment: the canonical forward map is the required structure-map comparison.
  simpa [u₀] using canonicalForwardSubsequenceConeMap_comm₂ K s hs hTsub hTfull

/-- Helper for Chap13 Lemma 13 33 4: a homotopy colimit for the selected subsequence is also a
homotopy colimit for the original sequential diagram. -/
private theorem isHomotopyColimitOf_of_subsequence_hocolim
    (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    [HasCoproduct K.obj] [HasCoproduct (hs.monotone.functor ⋙ K).obj]
    {Khocolim : D}
    (hsub : IsHomotopyColimitOf (hs.monotone.functor ⋙ K) Khocolim) :
    IsHomotopyColimitOf K Khocolim := by
  rcases hsub with ⟨gsub, δsub, hTsub⟩
  obtain ⟨Xfull, gfull, δfull, hTfull⟩ :=
    distinguished_cocone_triangle (sequentialTelescopeMap K)
  obtain ⟨e, _⟩ := exists_homotopyColimitIso_of_subsequence K s hs hTsub hTfull
  -- Proof comment: TR1 gives a full telescope presentation, and the main comparison theorem
  -- identifies its cone object with `Khocolim`.
  exact isHomotopyColimitOf_of_iso (S := K) (e := e) ⟨gfull, δfull, hTfull⟩

/-- Helper for Chap13 Lemma 13 33 4: a homotopy colimit for the original sequential diagram is
also a homotopy colimit for any strictly increasing subsequence. -/
private theorem isHomotopyColimitOf_subsequence_of_hocolim
    (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    [HasCoproduct K.obj] [HasCoproduct (hs.monotone.functor ⋙ K).obj]
    {Khocolim : D}
    (hfull : IsHomotopyColimitOf K Khocolim) :
    IsHomotopyColimitOf (hs.monotone.functor ⋙ K) Khocolim := by
  rcases hfull with ⟨gfull, δfull, hTfull⟩
  obtain ⟨Xsub, gsub, δsub, hTsub⟩ :=
    distinguished_cocone_triangle (sequentialTelescopeMap (hs.monotone.functor ⋙ K))
  obtain ⟨e, _⟩ := exists_homotopyColimitIso_of_subsequence K s hs hTsub hTfull
  -- Proof comment: now the comparison isomorphism runs from the chosen subsequence cone to
  -- `Khocolim`, so we transport the owner predicate back along `e.symm`.
  exact isHomotopyColimitOf_of_iso (S := hs.monotone.functor ⋙ K) (e := e.symm)
    ⟨gsub, δsub, hTsub⟩

/-- Helper for Lemma 13.33.4: once the cone object is fixed, passing to a strictly increasing
subsequence does not change the owner predicate `IsHomotopyColimitOf`. -/
theorem isHomotopyColimitOf_subsequence_iff
    (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    [HasCoproduct K.obj] [HasCoproduct (hs.monotone.functor ⋙ K).obj]
    {Khocolim : D} :
    IsHomotopyColimitOf (hs.monotone.functor ⋙ K) Khocolim ↔
      IsHomotopyColimitOf K Khocolim := by
  constructor
  · -- Proof comment: compare a chosen subsequence presentation with an arbitrary full one.
    exact isHomotopyColimitOf_of_subsequence_hocolim K s hs
  · -- Proof comment: the same cone comparison works in the reverse direction.
    exact isHomotopyColimitOf_subsequence_of_hocolim K s hs

end

end CategoryTheory
