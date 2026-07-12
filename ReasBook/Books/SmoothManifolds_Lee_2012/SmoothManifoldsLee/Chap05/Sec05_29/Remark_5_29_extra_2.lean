import Mathlib.Tactic.Recall
import SmoothManifolds_Lee_2012.Chap05.Sec05_29.Theorem_5_8
import SmoothManifolds_Lee_2012.Chap05.Sec05_33.Theorem_5_31

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

section LocalSliceUniqueness

variable {n k : ℕ} {M : Type*} [TopologicalSpace M]
variable [TopologicalManifold n M]
variable [IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) M]
variable (S : Set M)

-- Semantic recall note: `lean_leansearch` was unavailable in this session, so the statement shape
-- was chosen from the local `Set.SatisfiesLocalSliceCondition`,
-- `local_slice_condition_has_embedded_submanifold_structure`, and
-- `immersed_submanifold_structure_unique_of_same_carrier` APIs.

/- Remark 5.29-extra-2 (1): `Set.SatisfiesLocalSliceCondition n S k` is already a predicate on the
subset `S ⊆ M` inside the ambient manifold `M`; it does not assume any topology or smooth
structure on the subtype `S` itself. -/
recall Set.SatisfiesLocalSliceCondition

/-- Remark 5.29-extra-2: a subset satisfying the local `k`-slice condition carries the
canonical embedded-submanifold structure from Theorem 5.8, and any immersed submanifold structure
on the same underlying subset is diffeomorphic to it through the ambient inclusion. In
particular, `S` can be regarded as an embedded submanifold of `M` in only one way. -/
theorem local_slice_condition_unique_submanifold_structure
    (hS : Set.SatisfiesLocalSliceCondition n S k) :
    ∃ tm : TopologicalManifold k S,
      let _ : TopologicalManifold k S := tm
      ∃ hs : IsManifold (𝓡 k) (⊤ : WithTop ℕ∞) S,
        let _ : IsManifold (𝓡 k) (⊤ : WithTop ℕ∞) S := hs
        ∃ hEmb : IsEmbeddedSubmanifold (𝓡 n) (𝓡 k) S,
          ∀ T : Manifold.ImmersedSubmanifold (𝓡 n) M,
            T.carrier = S →
            ∃ Φ : T ≃ₘ⟮modelWithCornersSelf ℝ T.ModelSpace, 𝓡 k⟯ S,
              ∀ x : T, (Φ x : M) = T.inclusion x := sorry

end LocalSliceUniqueness
