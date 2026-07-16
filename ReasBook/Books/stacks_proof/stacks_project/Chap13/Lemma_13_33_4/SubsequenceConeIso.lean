import stacks_proof.stacks_project.Chap13.Lemma_13_33_4.SubsequenceTriangleComparison

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- Helper for Chap13 Lemma 13 33 4: the canonical defect
`ε := 𝟙 - v₀ ≫ u₀` on the full cone object has square zero. -/
private theorem canonicalSubsequenceConeMapRightDefectSqZero
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
    let ε : Xfull ⟶ Xfull :=
      𝟙 _ -
        canonicalReverseSubsequenceConeMap K s hs hTsub hTfull ≫
          canonicalForwardSubsequenceConeMap K s hs hTsub hTfull
    in ε ≫ ε = 0 := by
  -- Proof comment: specialize the generic square-zero defect theorem once to the canonical
  -- forward and reverse cone comparison maps.
  simpa using
    subsequenceConeMapRightCompositeDefectSqZero
      (K := K) (s := s) (hs := hs) hTsub hTfull
      (u := canonicalForwardSubsequenceConeMap K s hs hTsub hTfull)
      (canonicalForwardSubsequenceConeMap_comm₂ K s hs hTsub hTfull)
      (canonicalForwardSubsequenceConeMap_comm₃ K s hs hTsub hTfull)
      (v := canonicalReverseSubsequenceConeMap K s hs hTsub hTfull)
      (canonicalReverseSubsequenceConeMap_comm₂ K s hs hTsub hTfull)
      (canonicalReverseSubsequenceConeMap_comm₃ K s hs hTsub hTfull)

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

/-- Helper for Chap13 Lemma 13 33 4: the canonical forward comparison map between two chosen
telescope triangles is an isomorphism. -/
private noncomputable theorem subsequenceReverseForwardCompositeIsIso
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
      (canonicalReverseSubsequenceConeMap K s hs hTsub hTfull ≫
        canonicalForwardSubsequenceConeMap K s hs hTsub hTfull) := by
  let ε : Xfull ⟶ Xfull :=
    𝟙 _ -
      canonicalReverseSubsequenceConeMap K s hs hTsub hTfull ≫
        canonicalForwardSubsequenceConeMap K s hs hTsub hTfull
  have hε :
      ε ≫ ε = 0 := by
    -- Proof comment: the canonical square-zero specialization now records the nilpotent defect
    -- once, so this theorem only assembles the inverse criterion.
    simpa [ε] using canonicalSubsequenceConeMapRightDefectSqZero K s hs hTsub hTfull
  change IsIso (𝟙 _ - ε)
  -- Proof comment: a square-zero defect makes the identity-minus-defect map invertible.
  simpa [ε] using sub_id_isIso_of_square_zero ε hε

/-- Helper for Chap13 Lemma 13 33 4: if both end composites `u ≫ v` and `v ≫ u` are isomorphisms,
then `u` itself is an isomorphism. -/
private theorem isIso_of_isIso_endComposites
    {X Y : D} (u : X ⟶ Y) (v : Y ⟶ X)
    [IsIso (u ≫ v)] [IsIso (v ≫ u)] :
    IsIso u := by
  letI : Mono u := mono_of_mono u v
  letI : Epi u := epi_of_epi v u
  exact isIso_of_mono_of_epi u

/-- Helper for Chap13 Lemma 13 33 4: the canonical forward comparison map between two chosen
telescope triangles is an isomorphism. -/
private noncomputable theorem canonicalSubsequenceConeComparisonIsIso
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
    IsIso (canonicalForwardSubsequenceConeMap K s hs hTsub hTfull) := by
  let u₀ := canonicalForwardSubsequenceConeMap K s hs hTsub hTfull
  let v₀ := canonicalReverseSubsequenceConeMap K s hs hTsub hTfull
  letI : IsIso (u₀ ≫ v₀) := by
    simpa [u₀, v₀] using subsequenceForwardReverseCompositeIsIso K s hs hTsub hTfull
  letI : IsIso (v₀ ≫ u₀) := by
    simpa [u₀, v₀] using subsequenceReverseForwardCompositeIsIso K s hs hTsub hTfull
  change IsIso u₀
  simpa [u₀, v₀] using isIso_of_isIso_endComposites u₀ v₀

/-- Helper for Chap13 Lemma 13 33 4: the canonical subsequence/full comparison data identify the
cone objects of any chosen distinguished telescope triangles. -/
noncomputable def telescopeConeIsoOfSubsequenceHomotopyEquivalence
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
    Xsub ≅ Xfull :=
  let u₀ := canonicalForwardSubsequenceConeMap K s hs hTsub hTfull
  letI : IsIso u₀ := canonicalSubsequenceConeComparisonIsIso K s hs hTsub hTfull
  asIso u₀

end

end CategoryTheory
