import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Theorem_23_3_1

open CategoryTheory
open scoped Manifold Topology

noncomputable section

variable {n : ℕ}
variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
variable
  [TopologicalSpace
    (Bundle.TotalSpace (Fin n → ℝ) (TangentSpace (𝓡 n) : M → Type _))]
variable [FiberBundle (Fin n → ℝ) (TangentSpace (𝓡 n) : M → Type _)]
variable [VectorBundle ℝ (Fin n → ℝ) (TangentSpace (𝓡 n) : M → Type _)]

-- `TangentSpace (𝓡 n)` is the canonical tangent-bundle owner in the current Chapter 23 API.
-- Definition 23.3.3 is therefore best exposed as the thin source-facing abbreviation obtained by
-- evaluating a chosen Stiefel-Whitney family on that tangent bundle, rather than by introducing a
-- second package of tangent-bundle data.

/-- The degree-`i` tangential characteristic class of `M` associated to a characteristic class
`c`, obtained by evaluating `c` on the canonical tangent bundle `TangentSpace (𝓡 n)`. This is
the reusable bridge owner for nearby Chapter 23 constructions that specialize `c`. -/
abbrev tangentialCharacteristicClass
    {i : ℕ} {k : ℕ → TopCatᵒᵖ ⥤ AddCommGrpCat} (c : CharacteristicClass n i k) :
    (k i).obj (Opposite.op (TopCat.of M)) :=
  c.onFamily (TangentSpace (𝓡 n) : M → Type _)

/- Unfolding `tangentialCharacteristicClass c` recovers the evaluation of `c` on `τM`. -/
theorem tangentialCharacteristicClass_def
    {i : ℕ} {k : ℕ → TopCatᵒᵖ ⥤ AddCommGrpCat} (c : CharacteristicClass n i k) :
    tangentialCharacteristicClass c =
      c.onFamily (TangentSpace (𝓡 n) : M → Type _) :=
  rfl

variable [IsManifold (𝓡 n) ⊤ M]

/- Definition 23.3.3. For a smooth manifold `M`, the degree-`i` Stiefel-Whitney class `w_i(M)`
is the degree-`i` Stiefel-Whitney class of the tangent bundle `τM`. In this development, that
surface is the source-facing abbreviation obtained by evaluating the chosen
Stiefel-Whitney family on the canonical tangent bundle `TangentSpace (𝓡 n)`. -/
abbrev tangentialStiefelWhitneyClass
    (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ⊤ M]
    [TopologicalSpace
      (Bundle.TotalSpace (Fin n → ℝ) (TangentSpace (𝓡 n) : M → Type _))]
    [FiberBundle (Fin n → ℝ) (TangentSpace (𝓡 n) : M → Type _)]
    [VectorBundle ℝ (Fin n → ℝ) (TangentSpace (𝓡 n) : M → Type _)]
    (H2 : ModTwoCohomologyTheory) (w : StiefelWhitneyClassFamily H2) (i : ℕ) :
    (H2.cohomology i).obj (Opposite.op (TopCat.of M)) :=
  tangentialCharacteristicClass (w n i)

/- Unfolding `tangentialStiefelWhitneyClass n M H2 w i` recovers the tangent-bundle evaluation
`w_i(τM)`. -/
theorem tangentialStiefelWhitneyClass_def
    (H2 : ModTwoCohomologyTheory) (w : StiefelWhitneyClassFamily H2) (i : ℕ) :
    tangentialStiefelWhitneyClass n M H2 w i =
      (w n i).onFamily (TangentSpace (𝓡 n) : M → Type _) :=
  rfl

end
