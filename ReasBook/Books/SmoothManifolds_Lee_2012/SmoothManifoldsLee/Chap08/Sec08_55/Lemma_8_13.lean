import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import SmoothManifolds_Lee_2012.Chap08.Sec08_55.Definition_8_55_extra_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold
open InnerProductSpace

noncomputable section

section

variable {n : ℕ}

/-- Helper for the Gram-Schmidt algorithm for frames: the orthonormalized frame associated to a
smooth local frame on an open
subset of `ℝⁿ`, obtained by applying the canonical pointwise Gram-Schmidt normalization in
Euclidean coordinates and transporting back to the tangent spaces. -/
def gramSchmidtFrame
    (X : Fin n → (x : EuclideanSpace ℝ (Fin n)) → TangentSpace (𝓡 n) x) :
    Fin n → (x : EuclideanSpace ℝ (Fin n)) → TangentSpace (𝓡 n) x :=
  fun i x ↦
    (NormedSpace.fromTangentSpace x).symm
      (gramSchmidtNormed ℝ (fun j : Fin n ↦ NormedSpace.fromTangentSpace x (X j x)) i)

/-- Helper for the Gram-Schmidt algorithm for frames: Euclidean coordinates of a tangent-space
frame on `Tℝⁿ`. -/
def frameCoordinates
    (X : Fin n → (x : EuclideanSpace ℝ (Fin n)) → TangentSpace (𝓡 n) x) :
    Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
  fun i x ↦ NormedSpace.fromTangentSpace x (X i x)

/-- Helper for the Gram-Schmidt algorithm for frames: the unnormalized pointwise Gram-Schmidt
vectors in Euclidean
coordinates. -/
def rawGramSchmidtFrame
    (X : Fin n → (x : EuclideanSpace ℝ (Fin n)) → TangentSpace (𝓡 n) x) :
    Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
  fun i x ↦ gramSchmidt ℝ (frameCoordinates X · x) i

@[simp] theorem fromTangentSpace_gramSchmidtFrame
    {X : Fin n → (x : EuclideanSpace ℝ (Fin n)) → TangentSpace (𝓡 n) x}
    (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    NormedSpace.fromTangentSpace x (gramSchmidtFrame X i x) =
      gramSchmidtNormed ℝ (fun j : Fin n ↦ NormedSpace.fromTangentSpace x (X j x)) i := by
  simp [gramSchmidtFrame]

/-- At each point of the domain, the frame produced by `gramSchmidtFrame` is pointwise
orthonormal. -/
theorem gramSchmidtFrame_pointwise_orthonormal
    {X : Fin n → (x : EuclideanSpace ℝ (Fin n)) → TangentSpace (𝓡 n) x}
    {x : EuclideanSpace ℝ (Fin n)}
    (hXx : LinearIndependent ℝ (X · x)) :
    Orthonormal ℝ
      (fun i : Fin n ↦ NormedSpace.fromTangentSpace x (gramSchmidtFrame X i x)) := by
  let Y : Fin n → EuclideanSpace ℝ (Fin n) :=
    fun j ↦ NormedSpace.fromTangentSpace x (X j x)
  have hlin :
      LinearIndependent ℝ Y := by
    simpa [Y] using
      hXx.map'
        (NormedSpace.fromTangentSpace x).toLinearMap
        (by ext v; simp)
  simpa [Y, fromTangentSpace_gramSchmidtFrame] using
    (gramSchmidtNormed_orthonormal hlin)

/-- Helper for the Gram-Schmidt algorithm for frames: transporting a local frame to Euclidean
coordinates preserves
pointwise linear independence. -/
theorem frameCoordinates_linearIndependent
    {U : Set (EuclideanSpace ℝ (Fin n))}
    {X : Fin n → (x : EuclideanSpace ℝ (Fin n)) → TangentSpace (𝓡 n) x}
    (hX : IsLocalFrameOn (𝓡 n) (EuclideanSpace ℝ (Fin n)) ∞ X U)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U) :
    LinearIndependent ℝ (frameCoordinates X · x) := by
  -- Push the pointwise tangent-space frame through the canonical tangent-space coordinates once.
  simpa [frameCoordinates] using
    (hX.linearIndependent hx).map'
      (NormedSpace.fromTangentSpace x).toLinearMap
      (by ext v; simp)

/-- Helper for the Gram-Schmidt algorithm for frames: projection onto the line spanned by a smooth
nowhere-vanishing vector
field varies smoothly. -/
theorem contDiffOn_starProjection_singleton
    {U : Set (EuclideanSpace ℝ (Fin n))}
    {v w : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hv : ContDiffOn ℝ ∞ v U) (hw : ContDiffOn ℝ ∞ w U)
    (hv_ne : ∀ x ∈ U, v x ≠ 0) :
    ContDiffOn ℝ ∞ (fun x ↦ (ℝ ∙ v x).starProjection (w x)) U := by
  -- Rewrite the projection onto a line as a smooth scalar coefficient times the spanning field.
  have hinner : ContDiffOn ℝ ∞ (fun x ↦ inner ℝ (v x) (w x)) U := by
    intro x hx
    simpa using (hv x hx).inner ℝ (hw x hx)
  have hnormSq : ContDiffOn ℝ ∞ (fun x ↦ ‖v x‖ ^ 2) U := by
    intro x hx
    simpa using (hv x hx).norm_sq ℝ
  have hcoeff :
      ContDiffOn ℝ ∞ (fun x ↦ inner ℝ (v x) (w x) / ‖v x‖ ^ 2) U := by
    intro x hx
    exact (hinner x hx).div (hnormSq x hx) (pow_ne_zero 2 (norm_ne_zero_iff.mpr (hv_ne x hx)))
  simpa [Submodule.starProjection_singleton] using hcoeff.smul hv

/-- Helper for the Gram-Schmidt algorithm for frames: the raw Gram-Schmidt vectors of a local
frame never vanish on the
domain. -/
theorem gramSchmidt_ne_zero_on
    {U : Set (EuclideanSpace ℝ (Fin n))}
    {X : Fin n → (x : EuclideanSpace ℝ (Fin n)) → TangentSpace (𝓡 n) x}
    (hX : IsLocalFrameOn (𝓡 n) (EuclideanSpace ℝ (Fin n)) ∞ X U)
    (i : Fin n) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U) :
    rawGramSchmidtFrame X i x ≠ 0 := by
  -- The nonvanishing statement is exactly the standard Euclidean Gram-Schmidt lemma in coordinates.
  simpa [rawGramSchmidtFrame] using
    gramSchmidt_ne_zero (𝕜 := ℝ) (f := fun j ↦ frameCoordinates X j x) i
      (frameCoordinates_linearIndependent hX hx)

/-- Helper for the Gram-Schmidt algorithm for frames: each projection term in the raw
Gram-Schmidt recursion is smooth once
the earlier raw vector field is known to be smooth. -/
theorem rawGramSchmidtProjection_contDiffOn
    {U : Set (EuclideanSpace ℝ (Fin n))}
    {X : Fin n → (x : EuclideanSpace ℝ (Fin n)) → TangentSpace (𝓡 n) x}
    (hX : IsLocalFrameOn (𝓡 n) (EuclideanSpace ℝ (Fin n)) ∞ X U)
    (hXsmooth : ∀ j : Fin n, ContDiffOn ℝ ∞ (frameCoordinates X j) U)
    {i j : Fin n}
    (hj_smooth : ContDiffOn ℝ ∞ (rawGramSchmidtFrame X j) U) :
    ContDiffOn ℝ ∞
      (fun x ↦ (ℝ ∙ rawGramSchmidtFrame X j x).starProjection (frameCoordinates X i x)) U := by
  -- Package the recursive projection term through the general smoothness lemma
  -- for line projections.
  exact contDiffOn_starProjection_singleton hj_smooth (hXsmooth i) fun x hx ↦
    gramSchmidt_ne_zero_on hX j hx

/-- Helper for the Gram-Schmidt algorithm for frames: the raw Gram-Schmidt frame satisfies the
usual recursive formula
pointwise. -/
theorem rawGramSchmidtFrame_def
    {X : Fin n → (x : EuclideanSpace ℝ (Fin n)) → TangentSpace (𝓡 n) x}
    (i : Fin n) :
    rawGramSchmidtFrame X i =
      fun x ↦
        frameCoordinates X i x -
          ∑ j ∈ Finset.Iio i,
            (ℝ ∙ rawGramSchmidtFrame X j x).starProjection (frameCoordinates X i x) := by
  -- Unfold the Euclidean Gram-Schmidt recursion exactly once and reuse this normal form later.
  funext x
  rw [rawGramSchmidtFrame, gramSchmidt_def]
  simp only [rawGramSchmidtFrame]

/-- Helper for the Gram-Schmidt algorithm for frames: the raw pointwise Gram-Schmidt vectors vary
smoothly on `U`. -/
theorem gramSchmidt_contDiffOn_step
    {U : Set (EuclideanSpace ℝ (Fin n))}
    {X : Fin n → (x : EuclideanSpace ℝ (Fin n)) → TangentSpace (𝓡 n) x}
    (hX : IsLocalFrameOn (𝓡 n) (EuclideanSpace ℝ (Fin n)) ∞ X U)
    (hXsmooth : ∀ j : Fin n, ContDiffOn ℝ ∞ (frameCoordinates X j) U)
    (i : Fin n)
    (hprev : ∀ j ∈ Finset.Iio i, ContDiffOn ℝ ∞ (rawGramSchmidtFrame X j) U) :
    ContDiffOn ℝ ∞ (rawGramSchmidtFrame X i) U := by
  -- Route correction: recurse only on the raw Euclidean Gram-Schmidt vectors, then normalize later.
  have hsum :
      ContDiffOn ℝ ∞
        (fun x ↦
          ∑ j ∈ Finset.Iio i,
            (ℝ ∙ rawGramSchmidtFrame X j x).starProjection (frameCoordinates X i x)) U := by
    refine ContDiffOn.sum fun j hj ↦ ?_
    exact rawGramSchmidtProjection_contDiffOn hX hXsmooth (hprev j hj)
  -- Rewrite the recursive definition once and combine the smooth input field with the smooth sum.
  rw [rawGramSchmidtFrame_def]
  exact (hXsmooth i).sub hsum

/-- Helper for the Gram-Schmidt algorithm for frames: the raw pointwise Gram-Schmidt vectors vary
smoothly on `U`. -/
theorem gramSchmidt_contDiffOn
    {U : Set (EuclideanSpace ℝ (Fin n))}
    {X : Fin n → (x : EuclideanSpace ℝ (Fin n)) → TangentSpace (𝓡 n) x}
    (hX : IsLocalFrameOn (𝓡 n) (EuclideanSpace ℝ (Fin n)) ∞ X U) :
    ∀ i : Fin n, ContDiffOn ℝ ∞ (rawGramSchmidtFrame X i) U := by
  -- First convert the original tangent-space smoothness hypotheses into Euclidean coordinates.
  have hXsmooth : ∀ j : Fin n, ContDiffOn ℝ ∞ (frameCoordinates X j) U := by
    intro j
    simpa [frameCoordinates] using
      ((contMDiffOn_vectorSpace_iff_contDiffOn).mp (hX.contMDiffOn j))
  -- Strong induction supplies exactly the earlier-index smoothness hypotheses in `gramSchmidt_def`.
  intro i
  induction i using Fin.strong_induction_on with
  | h i ih =>
      exact gramSchmidt_contDiffOn_step hX hXsmooth i fun j hj ↦ ih j (Finset.mem_Iio.mp hj)

/-- For each initial segment `Set.Iic j`, the frame `gramSchmidtFrame X` spans the same subspace
as the original frame `X` at each point. -/
theorem span_gramSchmidtFrame_initialSegment
    {X : Fin n → (x : EuclideanSpace ℝ (Fin n)) → TangentSpace (𝓡 n) x}
    (j : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    Submodule.span ℝ ((gramSchmidtFrame X · x) '' Set.Iic j) =
      Submodule.span ℝ ((X · x) '' Set.Iic j) := by
  -- Transport both spans through `NormedSpace.fromTangentSpace x` and compare them in Euclidean
  -- coordinates.
  apply Submodule.map_injective_of_injective
    (f := (NormedSpace.fromTangentSpace x).toLinearMap)
    (NormedSpace.fromTangentSpace x).injective
  rw [Submodule.map_span, Submodule.map_span]
  -- Once the two images are written in Euclidean coordinates, the standard span-preservation
  -- lemmas apply directly.
  simpa [frameCoordinates, fromTangentSpace_gramSchmidtFrame, Set.image_image] using
    (show
      Submodule.span ℝ ((gramSchmidtNormed ℝ (frameCoordinates X · x)) '' Set.Iic j) =
        Submodule.span ℝ ((frameCoordinates X · x) '' Set.Iic j) by
        rw [span_gramSchmidtNormed, span_gramSchmidt_Iic])

/-- Helper for the Gram-Schmidt algorithm for frames: the full Gram-Schmidt frame spans the same
tangent space as the
original frame at each point. -/
theorem span_gramSchmidtFrame_range
    {X : Fin n → (x : EuclideanSpace ℝ (Fin n)) → TangentSpace (𝓡 n) x}
    (x : EuclideanSpace ℝ (Fin n)) :
    Submodule.span ℝ (Set.range (gramSchmidtFrame X · x)) =
      Submodule.span ℝ (Set.range (X · x)) := by
  -- Transport the full spans to Euclidean coordinates and use the
  -- range-preservation theorems there.
  apply Submodule.map_injective_of_injective
    (f := (NormedSpace.fromTangentSpace x).toLinearMap)
    (NormedSpace.fromTangentSpace x).injective
  rw [Submodule.map_span, Submodule.map_span]
  rw [← Set.range_comp, ← Set.range_comp]
  simpa [frameCoordinates, fromTangentSpace_gramSchmidtFrame] using
    (show
      Submodule.span ℝ (Set.range (gramSchmidtNormed ℝ (frameCoordinates X · x))) =
        Submodule.span ℝ (Set.range (frameCoordinates X · x)) by
        rw [span_gramSchmidtNormed_range, span_gramSchmidt])

/-- Helper for the Gram-Schmidt algorithm for frames: in Euclidean coordinates, `gramSchmidtFrame`
is just the normalized raw
Gram-Schmidt vector field. -/
@[simp] theorem fromTangentSpace_gramSchmidtFrame_eq_normInvSmul_raw
    {X : Fin n → (x : EuclideanSpace ℝ (Fin n)) → TangentSpace (𝓡 n) x}
    (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    NormedSpace.fromTangentSpace x (gramSchmidtFrame X i x) =
      (‖rawGramSchmidtFrame X i x‖ : ℝ)⁻¹ • rawGramSchmidtFrame X i x := by
  -- Unfold the final normalization only once, after all raw recursive work has been done.
  rw [fromTangentSpace_gramSchmidtFrame (X := X) i x]
  simp [rawGramSchmidtFrame, frameCoordinates, gramSchmidtNormed]

/-- Helper for the Gram-Schmidt algorithm for frames: each section of `gramSchmidtFrame X` is
smooth on `U`. -/
theorem gramSchmidtFrame_contMDiffOn
    {U : Set (EuclideanSpace ℝ (Fin n))}
    {X : Fin n → (x : EuclideanSpace ℝ (Fin n)) → TangentSpace (𝓡 n) x}
    (hX : IsLocalFrameOn (𝓡 n) (EuclideanSpace ℝ (Fin n)) ∞ X U)
    (i : Fin n) :
    ContDiffOn ℝ ∞
      (fun x ↦ NormedSpace.fromTangentSpace x (gramSchmidtFrame X i x)) U := by
  -- Normalize the already-smooth raw Gram-Schmidt vector field by its nowhere-vanishing norm.
  have hraw : ContDiffOn ℝ ∞ (rawGramSchmidtFrame X i) U :=
    gramSchmidt_contDiffOn hX i
  have hnorm :
      ContDiffOn ℝ ∞ (fun x ↦ ‖rawGramSchmidtFrame X i x‖) U := by
    intro x hx
    simpa using (hraw x hx).norm ℝ (gramSchmidt_ne_zero_on hX i hx)
  have hnormInv :
      ContDiffOn ℝ ∞ (fun x ↦ (‖rawGramSchmidtFrame X i x‖ : ℝ)⁻¹) U := by
    intro x hx
    exact (hnorm x hx).inv (norm_ne_zero_iff.mpr (gramSchmidt_ne_zero_on hX i hx))
  simpa using hnormInv.smul hraw

/-- Helper for the Gram-Schmidt algorithm for frames: the pointwise Gram-Schmidt frame of a smooth
local frame is a smooth orthonormal
frame on the same set. -/
theorem gramSchmidtFrame_isOrthonormalFrameOn
    {U : Set (EuclideanSpace ℝ (Fin n))}
    {X : Fin n → (x : EuclideanSpace ℝ (Fin n)) → TangentSpace (𝓡 n) x}
    (hX : IsLocalFrameOn (𝓡 n) (EuclideanSpace ℝ (Fin n)) ∞ X U) :
    IsOrthonormalFrameOn U (gramSchmidtFrame X) := by
  -- Package orthonormality, linear independence, spanning, and smoothness into the owner fields.
  have hlin :
      ∀ x ∈ U, LinearIndependent ℝ (gramSchmidtFrame X · x) := by
    intro x hx
    simpa using
      ((gramSchmidtFrame_pointwise_orthonormal (hX.linearIndependent hx)).linearIndependent).map'
        ((NormedSpace.fromTangentSpace x).symm.toLinearMap)
        (by ext v; simp)
  refine
    { linearIndependent := by
        intro x hx
        exact hlin x hx
      generating := by
        intro x hx
        simpa [span_gramSchmidtFrame_range (X := X) x] using hX.generating hx
      contMDiffOn := by
        intro i
        rw [contMDiffOn_vectorSpace_iff_contDiffOn]
        simpa using gramSchmidtFrame_contMDiffOn hX i
      orthonormal := by
        intro x hx
        exact gramSchmidtFrame_pointwise_orthonormal (hX.linearIndependent hx) }

/-- Lemma 8.13 (Gram-Schmidt Algorithm for Frames): a smooth local frame on a subset of `ℝⁿ` can
be replaced by the explicit orthonormal frame `gramSchmidtFrame X`, whose values on each initial
segment `Set.Iic j` span the same subspace at each point. -/
theorem exists_orthonormalFrameOn_with_same_initial_spans
    {U : Set (EuclideanSpace ℝ (Fin n))}
    {X : Fin n → (x : EuclideanSpace ℝ (Fin n)) → TangentSpace (𝓡 n) x}
    (hX : IsLocalFrameOn (𝓡 n) (EuclideanSpace ℝ (Fin n)) ∞ X U) :
    ∃ E : Fin n → (x : EuclideanSpace ℝ (Fin n)) → TangentSpace (𝓡 n) x,
      IsOrthonormalFrameOn U E ∧
        ∀ (j : Fin n) (p : U),
          Submodule.span ℝ ((E · p) '' Set.Iic j) =
            Submodule.span ℝ ((X · p) '' Set.Iic j) := by
  -- Instantiate the explicit pointwise Gram-Schmidt frame and reuse the
  -- span comparison already proved.
  refine ⟨gramSchmidtFrame X, gramSchmidtFrame_isOrthonormalFrameOn hX, ?_⟩
  intro j p
  simpa using span_gramSchmidtFrame_initialSegment (X := X) j (p : EuclideanSpace ℝ (Fin n))

end
