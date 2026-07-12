import SmoothManifolds_Lee_2012.Chap01.Sec01.Definition_1_extra_1
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.Topology.Homotopy.Affine
import SmoothManifolds_Lee_2012.Chap05.Sec05_36.Proposition_5_49
import SmoothManifolds_Lee_2012.Chap05.Sec05_32.Definition_5_32_extra_2
import SmoothManifolds_Lee_2012.Chap06.Sec06_40.Corollary_6_16
import SmoothManifolds_Lee_2012.Chap06.Sec06_41.Definition_6_41_extra_1
import SmoothManifolds_Lee_2012.Chap06.Sec06_45.Problem_6_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

noncomputable section

-- Domain sampling pass:
-- * source-facing layer: Whitney approximation relative to a closed subset, with smoothness only
--   required on the complement.
-- * core/canonical owners already present upstream in this chapter: the project predicate
--   `delta_close` together with the canonical owners `ContMDiffOn`, `Set.EqOn`, and
--   `ContinuousMap.HomotopicRel`.
-- * semantic recall: `lean_leansearch` surfaced the affine-homotopy owners
--   `ContinuousMap.Homotopy.affine` and `ContinuousMap.HomotopicRel`.
-- * relevant chapter declarations checked before refinement:
--   `exists_smooth_approximation_eqOn_of_isClosed`,
--   `exists_homotopicRel_to_smooth_map_of_isClosed`,
--   `exists_smooth_zero_on_and_positive_off_lt_of_isClosed`.
-- Primitive data vs. derived API:
-- * primitive data here is just the approximating map `ftilde`;
-- * the source-mandated conditions stay explicit in the public existential conclusion.

universe uM uN

namespace Manifold

section

variable {m n k : ℕ}
variable {M : Type uM} [TopologicalSpace M] [TopologicalManifold m M]
  [IsManifold (𝓡 m) ∞ M]
variable {N : Type uN} [TopologicalSpace N] [TopologicalManifold n N]
  [IsManifold (𝓡 n) ∞ N]

/-- A continuous Euclidean-valued approximation that is smooth off `B`, agrees with `f` on `B`,
and stays `δ`-close to `f`. -/
class ClosedSmoothApproxOnCompl {B : Set M} (δ : M → ℝ)
    (f ftilde : C(M, EuclideanSpace ℝ (Fin k))) : Prop where
  contMDiffOn_compl : ContMDiffOn (𝓡 m) (𝓡 k) ∞ ftilde Bᶜ
  eqOn : Set.EqOn ftilde f B
  delta_close : delta_close δ ftilde f

/-- Problem 6-4 (1): if `B ⊆ M` is closed, `δ : M → ℝ` is continuous and strictly positive, and
`f : M → ℝ^k` is continuous, then there exists a continuous map `f̃ : M → ℝ^k` that is smooth on
`M \ B`, agrees with `f` on `B`, and is `δ`-close to `f`. -/
theorem exists_continuous_eqOn_closed_smoothOn_compl_delta_close
    {B : Set M} (hB : IsClosed B) {δ : M → ℝ} (hδ_cont : Continuous δ)
    (hδ_pos : ∀ x : M, 0 < δ x) (f : C(M, EuclideanSpace ℝ (Fin k))) :
    ∃ ftilde : C(M, EuclideanSpace ℝ (Fin k)),
      ClosedSmoothApproxOnCompl (m := m) (k := k) (M := M) (B := B) δ f ftilde := sorry

/-- Bundle a continuous map whose image stays in `s` as a continuous map into the subtype `s`. -/
private def continuousMapCodRestrict {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (s : Set Y) (hs : ∀ x, f x ∈ s) : C(X, s) :=
  ⟨Set.codRestrict f s hs, f.continuous.codRestrict hs⟩

/-- The codomain-restricted map has the expected underlying formula. -/
@[simp] private theorem continuousMapCodRestrict_apply {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (s : Set Y) (hs : ∀ x, f x ∈ s) (x : X) :
    continuousMapCodRestrict f s hs x = ⟨f x, hs x⟩ := sorry

/-- The range of a smooth Euclidean embedding carries the needed embedded-submanifold structure. -/
private lemma smoothEmbeddingRange_isEmbeddedSubmanifold
    {N0 : ℕ} {e : N → EuclideanSpace ℝ (Fin N0)}
    (he : Manifold.IsSmoothEmbedding (𝓡 n) (𝓡 N0) (⊤ : WithTop ℕ∞) e) :
    ∃ instCharted : ChartedSpace (EuclideanSpace ℝ (Fin n)) (Set.range e),
      ∃ instManifold : IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) (Set.range e),
        let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) (Set.range e) := instCharted
        let _ : IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) (Set.range e) := instManifold
        IsEmbeddedSubmanifold (𝓡 N0) (𝓡 n) (Set.range e) := sorry

/-- If two Euclidean-valued maps agree on `B`, their affine homotopy is already relative to `B`. -/
private lemma homotopicRel_affine_of_eqOn {B : Set M} {ℓ : ℕ}
    {f g : C(M, EuclideanSpace ℝ (Fin ℓ))} (hfg : Set.EqOn f g B) :
    f.HomotopicRel g B := sorry

/-- Codomain-restricting an affine homotopy preserves relative homotopy on `B`. -/
private lemma affineHomotopyCodRestrict {B : Set M} {ℓ : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin ℓ))}
    {f g : C(M, EuclideanSpace ℝ (Fin ℓ))}
    (hfg : Set.EqOn f g B)
    (hU : ∀ t x, ContinuousMap.Homotopy.affine f g (t, x) ∈ U) :
    (continuousMapCodRestrict f U (fun x ↦ by
      simpa [ContinuousMap.Homotopy.affine_apply] using hU 0 x)).HomotopicRel
      (continuousMapCodRestrict g U (fun x ↦ by
        simpa [ContinuousMap.Homotopy.affine_apply] using hU 1 x)) B := sorry

/-- If `B ⊆ M` is closed and `F : M → N` is continuous, then `F` is homotopic relative to `B`
to a continuous map that is smooth on `M \ B`. -/
theorem exists_homotopicRel_to_continuous_smoothOn_compl
    {B : Set M} (hB : IsClosed B) (F : C(M, N)) :
    ∃ G : C(M, N),
      ContMDiffOn (𝓡 m) (𝓡 n) ∞ G (Bᶜ) ∧
      F.HomotopicRel G B := sorry

end

end Manifold
