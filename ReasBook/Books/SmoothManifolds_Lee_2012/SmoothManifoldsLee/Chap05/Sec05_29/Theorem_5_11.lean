import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_28.Definition_5_28_extra_2
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_37.Problem_5_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold

-- Semantic search note: `lean_leansearch` surfaced the general manifold-boundary and smooth
-- embedding APIs, while the local Chapter 5 owner and split-clause precedent are the imported
-- theorem `manifoldBoundary_isEmbeddedSubmanifold` and `Theorem_5_12`.

universe u

section

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
variable [SmoothManifoldWithBoundary (n + 1) M]

/-- Theorem 5.11 (1): if `M` is a smooth `(n + 1)`-manifold with boundary, then the manifold
boundary `((𝓡∂ (n + 1)).boundary M)` carries a boundaryless smooth `n`-manifold structure for
which its subtype inclusion into `M` is a smooth embedding. -/
instance manifoldBoundary_has_embedded_submanifold_structure :
    IsEmbeddedSubmanifold
      (𝓡∂ (n + 1))
      (𝓡 n)
      ((𝓡∂ (n + 1)).boundary M) :=
  manifoldBoundary_isEmbeddedSubmanifold

/-- Theorem 5.11 (2): if `M` is a smooth `(n + 1)`-manifold with boundary, then the manifold
boundary `((𝓡∂ (n + 1)).boundary M)` is properly embedded in `M`. -/
theorem manifoldBoundary_isProperlyEmbedded :
    ((𝓡∂ (n + 1)).boundary M).IsProperlyEmbedded := sorry

end
