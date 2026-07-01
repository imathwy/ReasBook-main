import Mathlib
import stacks_project.Chap10.Definition_10_47_4

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CommRingCat
open scoped RatFunc

namespace Algebra

universe u

section

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

attribute [local instance] Polynomial.algebra

-- Proof sketch: for the forward implication, identify `K(t)` with the localization of
-- `K ⊗[k] k(t)` at the nonzero polynomials and use stability of irreducibility under
-- localization. For the reverse implication, for any field extension `k' / k`, compare
-- `K ⊗[k] k'` with its localization `K(t) ⊗[k(t)] k'(t)`; injectivity together with the
-- minimal-prime comparison lemmas recovers irreducibility before localization.
/-- Lemma 10.47.10: a field extension `K / k` is geometrically irreducible if and only if the
induced extension on one-variable rational function fields `K(t) / k(t)` is geometrically
irreducible. -/
@[stacks 0G31]
theorem isGeometricallyIrreducibleOver_iff_ratFuncExtension_isGeometricallyIrreducible :
    GeometricallyIrreducible (Spec.map (ofHom (algebraMap k K))) ↔
      GeometricallyIrreducible (Spec.map (ofHom (algebraMap k⟮X⟯ K⟮X⟯))) := sorry

/-- Compatibility alias for the rational-function-field criterion for geometric irreducibility. -/
abbrev Lemma_10_47_10 :
    GeometricallyIrreducible (Spec.map (ofHom (algebraMap k K))) ↔
      GeometricallyIrreducible (Spec.map (ofHom (algebraMap k⟮X⟯ K⟮X⟯))) :=
  isGeometricallyIrreducibleOver_iff_ratFuncExtension_isGeometricallyIrreducible

end

end Algebra
