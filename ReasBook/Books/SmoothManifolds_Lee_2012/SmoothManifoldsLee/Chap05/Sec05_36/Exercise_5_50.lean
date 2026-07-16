import Mathlib.Tactic.Recall
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_36.Proposition_5_49

open TopologicalSpace
open scoped Manifold

-- Declarations for this item will be appended below by the statement pipeline.
-- Semantic recall note: this item is formalized as a direct reference to the four canonical
-- owners from Proposition 5.49, so the source-faithful Lean surface is a recall bundle.
/-
Exercise 5.50 is recall-only in this item-per-file formalization.
Route correction: there is no appended local theorem skeleton here, so the source-faithful Lean
surface is to recall the four components of Proposition 5.49 rather than duplicate them locally.
-/
-- The anonymous examples below are the complete certification surface for this recall bundle.
section

universe u𝕜 uE uH uM uE' uH' uN

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M]
variable {I : ModelWithCorners 𝕜 E H} [ChartedSpace H M]

-- Verify directly that the imported dependency exposes the first recalled owner with its
-- intended manifold-with-boundary statement.
example {n : WithTop ℕ∞} [IsManifold I n M] (s : Opens M) :
    Manifold.IsSmoothEmbedding I I n (Subtype.val : s → M) := by
  -- Part (1) is exactly the canonical owner theorem, reused without changing route.
  simpa using Manifold.IsSmoothEmbedding.of_opens (I := I) (n := n) s

variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {I' : ModelWithCorners 𝕜 E' H'}
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]

/-- Exercise 5.50: the four assertions of Proposition 5.49 hold for immersed and embedded
submanifolds with boundary. -/
theorem immersed_submanifold_with_boundary_basic_properties :
    (∀ [IsManifold I (⊤ : WithTop ℕ∞) M] (s : Opens M),
      Manifold.IsSmoothEmbedding I I (⊤ : WithTop ℕ∞) (Subtype.val : s → M)) ∧
    (∀ [IsManifold I (⊤ : WithTop ℕ∞) M] [IsManifold I' (⊤ : WithTop ℕ∞) N] {F : N → M},
      Manifold.IsSmoothEmbedding I' I (⊤ : WithTop ℕ∞) F →
        ∃ instCharted : ChartedSpace H' (Set.range F),
          ∃ instManifold : IsManifold I' (⊤ : WithTop ℕ∞) (Set.range F),
            let _ : ChartedSpace H' (Set.range F) := instCharted
            let _ : IsManifold I' (⊤ : WithTop ℕ∞) (Set.range F) := instManifold
            Manifold.IsSmoothEmbedding I' I (⊤ : WithTop ℕ∞)
              (Subtype.val : Set.range F → M)) ∧
    (∀ [T1Space M] {S : Set M}, S.IsProperlyEmbedded ↔ IsClosed S) ∧
    (∀ [IsManifold I (⊤ : WithTop ℕ∞) M] {S : Set M} [ChartedSpace H' S]
        [IsManifold I' (⊤ : WithTop ℕ∞) S],
      Manifold.IsImmersion I' I (⊤ : WithTop ℕ∞) (Subtype.val : S → M) →
        ∀ p : S, ∃ U : Opens S, p ∈ U ∧
          Manifold.IsSmoothEmbedding I' I (⊤ : WithTop ℕ∞) ((↑) : U → M)) := by
  constructor
  · -- Part (1) is exactly the canonical open-submanifold embedding theorem.
    intro _ s
    simpa using Manifold.IsSmoothEmbedding.of_opens (I := I) (n := (⊤ : WithTop ℕ∞)) s
  constructor
  · -- Part (2) is recalled directly from the canonical induced-range owner theorem.
    intro _ _ F hF
    simpa using
      smooth_embedding_range_has_manifold_with_boundary
        (I := I) (I' := I') (M := M) (N := N) hF
  constructor
  · -- Part (3) is the same topological closed-image criterion as in Proposition 5.49.
    intro _ S
    simpa using (Set.isProperlyEmbedded_iff_isClosed (S := S))
  · -- Part (4) is the local embedded-neighborhood statement already proved in Proposition 5.49.
    intro _ S _ _ hS p
    simpa using
      immersed_submanifold_has_embedded_neighborhood
        (I := I) (I' := I') (M := M) (S := S) hS p

/-- Helper for Exercise 5.50: a smooth embedding supplies induced manifold-with-boundary data on
its range before the final subtype-inclusion statement is recalled. -/
lemma smooth_embedding_has_range_manifold_data [IsManifold I (⊤ : WithTop ℕ∞) M]
    [IsManifold I' (⊤ : WithTop ℕ∞) N] {F : N → M}
    (hF : Manifold.IsSmoothEmbedding I' I (⊤ : WithTop ℕ∞) F) :
    ∃ instCharted : ChartedSpace H' (Set.range F),
      let _ : ChartedSpace H' (Set.range F) := instCharted
      ∃ _instManifold : IsManifold I' (⊤ : WithTop ℕ∞) (Set.range F), True := by
  -- Extract only the induced range structures from the canonical owner theorem.
  rcases smooth_embedding_range_has_manifold_with_boundary
      (I := I) (I' := I') (M := M) (N := N) hF with
    ⟨instCharted, instManifold, _⟩
  exact ⟨instCharted, instManifold, trivial⟩

-- Verify directly that the induced manifold-with-boundary theorem is still available from the
-- Proposition 5.49 dependency.
example [IsManifold I (⊤ : WithTop ℕ∞) M] [IsManifold I' (⊤ : WithTop ℕ∞) N] {F : N → M}
    (hF : Manifold.IsSmoothEmbedding I' I (⊤ : WithTop ℕ∞) F) :
    ∃ instCharted : ChartedSpace H' (Set.range F),
      ∃ instManifold : IsManifold I' (⊤ : WithTop ℕ∞) (Set.range F),
        let _ : ChartedSpace H' (Set.range F) := instCharted
        let _ : IsManifold I' (⊤ : WithTop ℕ∞) (Set.range F) := instManifold
        Manifold.IsSmoothEmbedding I' I (⊤ : WithTop ℕ∞) (Subtype.val : Set.range F → M) := by
  -- Part (2) is recalled by reusing the canonical owner from Proposition 5.49 unchanged.
  simpa using
    smooth_embedding_range_has_manifold_with_boundary
      (I := I) (I' := I') (M := M) (N := N) hF

-- Verify directly that the proper-embedding criterion is present as the third recalled owner.
example [T1Space M] {S : Set M} : S.IsProperlyEmbedded ↔ IsClosed S := by
  -- Part (3) is exactly the closed-image characterization proved in Proposition 5.49.
  simpa using (Set.isProperlyEmbedded_iff_isClosed (S := S))

-- Verify directly that the local embedded-neighborhood theorem is still available with the
-- imported canonical owner statement.
example [IsManifold I (⊤ : WithTop ℕ∞) M] {S : Set M} [ChartedSpace H' S]
    [IsManifold I' (⊤ : WithTop ℕ∞) S]
    (hS : Manifold.IsImmersion I' I (⊤ : WithTop ℕ∞) (Subtype.val : S → M)) (p : S) :
    ∃ U : Opens S, p ∈ U ∧ Manifold.IsSmoothEmbedding I' I (⊤ : WithTop ℕ∞) ((↑) : U → M) := by
  -- Part (4) is recalled by applying the canonical embedded-neighborhood owner directly.
  simpa using
    immersed_submanifold_has_embedded_neighborhood
      (I := I) (I' := I') (M := M) (S := S) hS p

end

/-
Part (1) is exactly the canonical owner `Manifold.IsSmoothEmbedding.of_opens`.
-/
recall Manifold.IsSmoothEmbedding.of_opens

/-
Part (2) remains as the boundary-language bridge extracted from Proposition 5.2's induced-image
owner theorem.
-/
recall smooth_embedding_range_has_manifold_with_boundary

/-
Part (3) is exactly the owner theorem `Set.isProperlyEmbedded_iff_isClosed`.
-/
recall Set.isProperlyEmbedded_iff_isClosed

/-
Part (4) remains as the local embedded-neighborhood statement for immersed submanifolds with
boundary.
-/
recall immersed_submanifold_has_embedded_neighborhood
