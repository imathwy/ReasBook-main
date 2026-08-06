import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Geometry.Manifold.Instances.Real
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Proposition_20_1_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Definition_23_2_1

open AlgebraicTopology CategoryTheory
open scoped Manifold

noncomputable section

-- Chapter 23 already treats characteristic numbers as evaluations of characteristic classes on a
-- chosen bundle family together with a chosen fundamental class and Kronecker pairing. For normal
-- characteristic numbers, the chosen Euclidean embedding only supplies the compatibility
-- predicate identifying a chosen bundle as a normal bundle, while the scalar itself is the direct
-- evaluation `⟨c(νₑ), [M]⟩`.

section

variable {R : Type} [CommRing R]
variable {n r : ℕ}
variable {M : Type} [TopologicalSpace M]
variable {k : ℕ → TopCatᵒᵖ ⥤ AddCommGrpCat}
variable (normalBundle : M → Type _)
variable [TopologicalSpace (Bundle.TotalSpace (Fin r → ℝ) normalBundle)]
variable [∀ b, TopologicalSpace (normalBundle b)]
variable [FiberBundle (Fin r → ℝ) normalBundle]
variable [∀ b, AddCommGroup (normalBundle b)]
variable [∀ b, Module ℝ (normalBundle b)]
variable [VectorBundle ℝ (Fin r → ℝ) normalBundle]

/-- Definition 23.4.2. Once a chosen normal bundle `νₑ` of a Euclidean embedding is fixed, the
normal characteristic number associated to a degree-`n` characteristic class `c`, a chosen
`R`-fundamental class `[M]`, and a chosen degree-`n` pairing is the scalar `⟨c(νₑ), [M]⟩`. The
embedding data enters separately through the compatibility predicate
`IsNormalBundleOfEuclideanEmbedding`. -/
abbrev normalCharacteristicNumber
    (c : CharacteristicClass r n k)
    (fundamentalClass : rSingularHomology R n (TopCat.of M))
    (kroneckerPairing :
      (k n).obj (Opposite.op (TopCat.of M)) →+
        rSingularHomology R n (TopCat.of M) →+ R) : R :=
  kroneckerPairing
    (c.onFamily normalBundle)
    fundamentalClass

/-- Unfolding `normalCharacteristicNumber` recovers the evaluation of `c(νₑ)` on the
compatible fundamental class `[M]` via the chosen degree-`n` pairing. -/
theorem normalCharacteristicNumber_def
    (c : CharacteristicClass r n k)
    (fundamentalClass : rSingularHomology R n (TopCat.of M))
    (kroneckerPairing :
      (k n).obj (Opposite.op (TopCat.of M)) →+
        rSingularHomology R n (TopCat.of M) →+ R) :
    normalCharacteristicNumber normalBundle c fundamentalClass kroneckerPairing =
      kroneckerPairing
        (c.onFamily normalBundle)
        fundamentalClass := rfl

end

section

variable {n : ℕ}
variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

/-- A chosen normed real `r`-plane bundle `νₑ` over `M` is compatible with the Euclidean
embedding `e : M → ℝ^(n + r)` when each fiber complements the immersed tangent directions of `e`.
This is the source-facing normal-bundle condition needed in Definition 23.4.2. -/
def IsNormalBundleOfEuclideanEmbedding {r : ℕ}
    (e : M → EuclideanSpace ℝ (Fin (n + r)))
    (normalBundle : M → Type _)
    [∀ b, NormedAddCommGroup (normalBundle b)]
    [∀ b, NormedSpace ℝ (normalBundle b)] :
    Prop :=
  ∀ x : M,
    Manifold.IsImmersionAtOfComplement (normalBundle x) (𝓡 n)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (n + r)))) ⊤ e x

/-- A compatible chosen normal bundle gives the expected fiberwise complement condition at each
point of `M`. -/
theorem IsNormalBundleOfEuclideanEmbedding.isImmersionAtOfComplement
    {r : ℕ}
    {e : M → EuclideanSpace ℝ (Fin (n + r))}
    {normalBundle : M → Type _}
    [∀ b, NormedAddCommGroup (normalBundle b)]
    [∀ b, NormedSpace ℝ (normalBundle b)]
    (h : IsNormalBundleOfEuclideanEmbedding e normalBundle) (x : M) :
    Manifold.IsImmersionAtOfComplement (normalBundle x) (𝓡 n)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (n + r)))) ⊤ e x :=
  h x

end
