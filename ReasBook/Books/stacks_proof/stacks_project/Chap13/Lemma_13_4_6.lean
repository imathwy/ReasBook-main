import Mathlib
import stacks_proof.stacks_project.Chap13.Lemma_13_4_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Pretriangulated

universe v u

section

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/- Domain-style sampling for Lemma 13.4.6:
- primary domain: distinguished triangles and their endomorphisms in a pretriangulated category,
  together with idempotent endomorphisms of the outer terms;
- sampled owner declarations:
  `Triangle`,
  `TriangleMorphism`,
  `complete_distinguished_triangle_morphism₂`,
  `endomorphism_hom₂_comp_eq_zero`;
- best owner abstraction: triangle endomorphisms `T ⟶ T`, with outer endomorphisms expressed on the
  canonical owner `End`;
- primitive data: a distinguished triangle `T`, idempotent endomorphisms `a : End T.obj₁` and
  `c : End T.obj₃`, and the commutative square `CommSq T.mor₃ c (a⟦(1 : ℤ)⟧') T.mor₃`;
- derived API: a chosen completion of the outer square to a triangle endomorphism and the
  exactness-based vanishing statement of Lemma `13.4.5`, which forces the correction term on the
  middle object to square to zero;
- source/core/bridge triage:
  `source-facing`: existence of a triangle endomorphism with prescribed outer idempotents and
    idempotent middle component;
  `core/canonical`: `Triangle`, `TriangleMorphism`, and the distinguished-triangle completion API;
  `bridge/view`: the exactness lemma `endomorphism_hom₂_comp_eq_zero` used to correct a chosen
    middle component to an idempotent one.
-/

-- Proof sketch: use `complete_distinguished_triangle_morphism₂` to choose a triangle
-- endomorphism `φ : End T` with outer components `a` and `c`. Then `δ := φ * φ - φ` has zero
-- first and third components, so Lemma 13.4.5 forces `(δ.hom₂)^2 = 0`. Correct `φ` by the
-- polynomial `3x^2 - 2x^3` on `End T`; the outer components remain `a` and `c` because those are
-- idempotent, and the middle component becomes idempotent by the resulting quartic relation.
/-- Lemma 13.4.6: if `T` is a distinguished triangle in a pretriangulated category and
idempotent endomorphisms `a` of `T.obj₁` and `c` of `T.obj₃` commute with the third morphism of
`T`, then there exists a triangle endomorphism of `T` with outer components `a` and `c` whose
middle component is idempotent. -/
@[stacks 05QQ]
theorem exists_idempotent_triangle_endomorphism_of_outer_idempotents {T : Triangle D}
    (hT : T ∈ distTriang D) (a : End T.obj₁) (c : End T.obj₃)
    (hcomm : CommSq T.mor₃ c (a⟦(1 : ℤ)⟧') T.mor₃) (ha : a ≫ a = a) (hc : c ≫ c = c) :
    ∃ φ : End T, φ.hom₁ = a ∧ φ.hom₃ = c ∧ φ.hom₂ ≫ φ.hom₂ = φ.hom₂ := by
  -- Complete the outer commutative square to a triangle endomorphism with middle component `b₀`.
  obtain ⟨b₀, hb₁, hb₂⟩ := complete_distinguished_triangle_morphism₂ T T hT hT a c hcomm.w
  let b : End T.obj₂ := b₀
  let φ : End T := Triangle.homMk _ _ a b c hb₁ hb₂ hcomm.w
  let δ : End T := φ * φ - φ
  -- The defect `δ = φ² - φ` already vanishes on the outer terms because `a` and `c` are idempotent.
  have ha' : a * a = a := by
    simpa [End.mul_def] using ha
  have hc' : c * c = c := by
    simpa [End.mul_def] using hc
  have hδ₁ : δ.hom₁ = 0 := by
    change a * a - a = 0
    exact sub_eq_zero.mpr ha'
  have hδ₃ : δ.hom₃ = 0 := by
    change c * c - c = 0
    exact sub_eq_zero.mpr hc'
  -- Lemma 13.4.5 now forces the middle defect to be square-zero.
  have hδ₂_nil := endomorphism_hom₂_comp_eq_zero hT δ δ hδ₁ hδ₃
  have hnil : (b * b - b) * (b * b - b) = 0 := by
    simpa [δ, φ, End.mul_def, Category.assoc] using hδ₂_nil
  -- Rewrite the quartic term using the square-zero defect relation.
  have hfour : b * (b * (b * b)) = (2 : ℤ) • (b * (b * b)) - b * b := by
    calc
      b * (b * (b * b)) =
          ((b * b - b) * (b * b - b)) + ((2 : ℤ) • (b * (b * b)) - b * b) := by
            noncomm_ring
      _ = (2 : ℤ) • (b * (b * b)) - b * b := by
        rw [hnil]
        abel
  -- Correct the chosen endomorphism by the polynomial `3x² - 2x³`; its outer terms stay fixed.
  let ψ : End T := (3 : ℤ) • (φ * φ) - (2 : ℤ) • (φ * φ * φ)
  have hψ₁ : ψ.hom₁ = a := by
    change (3 : ℤ) • (a * a) - (2 : ℤ) • (a * a * a) = a
    rw [ha', ha']
    abel
  have hψ₃ : ψ.hom₃ = c := by
    change (3 : ℤ) • (c * c) - (2 : ℤ) • (c * c * c) = c
    rw [hc', hc']
    abel
  -- The same polynomial becomes idempotent once the middle defect squares to zero.
  have hψ₂ : ψ.hom₂ ≫ ψ.hom₂ = ψ.hom₂ := by
    change ((3 : ℤ) • (b * b) - (2 : ℤ) • (b * b * b)) *
        ((3 : ℤ) • (b * b) - (2 : ℤ) • (b * b * b)) =
      (3 : ℤ) • (b * b) - (2 : ℤ) • (b * b * b)
    noncomm_ring [hfour]
  exact ⟨ψ, hψ₁, hψ₃, hψ₂⟩

end
