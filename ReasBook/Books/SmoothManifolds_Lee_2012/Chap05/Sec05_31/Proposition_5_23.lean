import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.Sets.Opens
import SmoothManifolds_Lee_2012.Chap05.Sec05_31.Definition_5_31_extra_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open TopologicalSpace
open scoped Manifold ContDiff

universe uE uH uM uS

namespace Manifold
namespace IsImmersion

section

variable {k : ℕ}
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners ℝ E H} [IsManifold I (⊤ : WithTop ℕ∞) M]
variable {S : Type uS} [TopologicalSpace S] [ChartedSpace (EuclideanSpace ℝ (Fin k)) S]
variable [IsManifold (𝓡 k) (⊤ : WithTop ℕ∞) S]
variable {ι : S → M}

-- Proof sketch: a chart in the maximal atlas is smooth together with its inverse, so its inverse
-- is a smooth open embedding from its target into `S`; composing with `ι` then matches the owner
-- predicate on `hι.toImmersedSubmanifold hιinj`.
/-- A smooth coordinate chart on `S` yields a smooth local parametrization of the immersed
submanifold determined by the injective immersion `ι`, over the chart's target. -/
theorem isSmoothLocalParametrization_of_mem_maximalAtlas
    (hι : IsImmersion (𝓡 k) I (⊤ : WithTop ℕ∞) ι) (hιinj : Function.Injective ι)
    {φ : OpenPartialHomeomorph S (EuclideanSpace ℝ (Fin k))}
    (hφ : φ ∈ IsManifold.maximalAtlas (𝓡 k) (⊤ : WithTop ℕ∞) S) :
    (hι.toImmersedSubmanifold hιinj).IsSmoothLocalParametrization
      ⟨φ.target, φ.open_target⟩
      (fun u : (⟨φ.target, φ.open_target⟩ : Opens (EuclideanSpace ℝ (Fin k))) ↦
        ι (φ.symm u)) := by
  refine ⟨fun u ↦ φ.symm u, rfl, ?_, ?_⟩
  · -- The inverse of a maximal-atlas chart is smooth on its target; precompose with the open-set
    -- inclusion to view it as a smooth map out of the subtype `φ.target`.
    have hsymm :
        ContMDiffOn (𝓡 k) (𝓡 k) (⊤ : WithTop ℕ∞) φ.symm φ.target :=
      contMDiffOn_symm_of_mem_maximalAtlas hφ
    have hsub :
        ContMDiff (𝓡 k) (𝓡 k) (⊤ : WithTop ℕ∞)
          (Subtype.val : (⟨φ.target, φ.open_target⟩ : Opens (EuclideanSpace ℝ (Fin k))) →
            EuclideanSpace ℝ (Fin k)) :=
      contMDiff_subtype_val
    simpa [Function.comp] using hsymm.comp_contMDiff hsub fun u ↦ u.2
  · -- As a map from the subtype `φ.target`, `φ.symm` is the restriction of the inverse partial
    -- homeomorphism, hence an open embedding.
    simpa using (φ.symm.isOpenEmbedding_restrict)

/- The reverse direction of the textbook iff would require the local parametrization predicate to
assert that the lift is a coordinate-chart inverse, or equivalently to include smoothness of the
inverse transition. The current auxiliary definition only records a smooth open embedding into
`S`, so the former helper statements deriving a chart from an arbitrary such embedding were too
strong and have been intentionally removed. -/

-- The textbook proposition is an iff because its notion of smooth local parametrization is a
-- coordinate parametrization. The local formal definition in `Definition_5_31_extra_2` is broader
-- (`smooth open embedding` into `S`), so only this chart-inverse direction is valid here.
/-- Proposition 5.23 (1), valid direction for the current formal definition: if a map from an
open subset of `ℝ^k` into `M` is `ι` composed with the inverse of a smooth coordinate chart on
`S`, then it is a smooth local parametrization of the immersed submanifold determined by `ι`. -/
theorem isSmoothLocalParametrization_iff_exists_chart
    (hι : IsImmersion (𝓡 k) I (⊤ : WithTop ℕ∞) ι) (hιinj : Function.Injective ι)
    (U : Opens (EuclideanSpace ℝ (Fin k))) (X : U → M) :
    (∃ φ : OpenPartialHomeomorph S (EuclideanSpace ℝ (Fin k)),
        φ ∈ IsManifold.maximalAtlas (𝓡 k) (⊤ : WithTop ℕ∞) S ∧
          φ.target = U ∧ X = fun u : U ↦ ι (φ.symm u)) →
      (hι.toImmersedSubmanifold hιinj).IsSmoothLocalParametrization U X := by
  rintro ⟨φ, hφ, hφU, hXeq⟩
  cases U with
  | mk U hUopen =>
    dsimp at hφU
    subst U
    subst hXeq
    exact isSmoothLocalParametrization_of_mem_maximalAtlas
      (hι := hι) (hιinj := hιinj) (φ := φ) hφ

-- Proof sketch: choose the preferred chart `chartAt (EuclideanSpace ℝ (Fin k)) p` on `S`; its
-- inverse, followed by `ι`, gives the required local parametrization and clearly contains `ι p`
-- in its image.
/-- Proposition 5.23 (2): every point of `S` lies in the image of some smooth local
parametrization of the immersed submanifold determined by `ι`. -/
theorem exists_isSmoothLocalParametrization_through
    (hι : IsImmersion (𝓡 k) I (⊤ : WithTop ℕ∞) ι) (hιinj : Function.Injective ι) (p : S) :
    ∃ U : Opens (EuclideanSpace ℝ (Fin k)), ∃ X : U → M,
      (hι.toImmersedSubmanifold hιinj).IsSmoothLocalParametrization U X ∧ ι p ∈ Set.range X := by
  let φ : OpenPartialHomeomorph S (EuclideanSpace ℝ (Fin k)) :=
    chartAt (EuclideanSpace ℝ (Fin k)) p
  let U : Opens (EuclideanSpace ℝ (Fin k)) := ⟨φ.target, φ.open_target⟩
  let X : U → M := fun u ↦ ι (φ.symm u)
  refine ⟨U, X, ?_, ?_⟩
  · -- The preferred chart through `p` is a maximal-atlas chart, so its inverse gives the
    -- required smooth local parametrization.
    exact isSmoothLocalParametrization_of_mem_maximalAtlas
      (hι := hι) (hιinj := hιinj)
      (φ := φ)
      (IsManifold.chart_mem_maximalAtlas (I := 𝓡 k) (n := (⊤ : WithTop ℕ∞)) p)
  · -- Evaluate the parametrization at the coordinate value `φ p`.
    refine ⟨⟨φ p, mem_chart_target (EuclideanSpace ℝ (Fin k)) p⟩, ?_⟩
    simp [X, φ, U, ChartedSpace.mem_chart_source, OpenPartialHomeomorph.left_inv,
      mem_chart_source]

end

end IsImmersion
end Manifold
