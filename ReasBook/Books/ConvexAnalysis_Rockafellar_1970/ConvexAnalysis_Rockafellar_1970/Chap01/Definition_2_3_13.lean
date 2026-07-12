import Mathlib.LinearAlgebra.AffineSpace.Simplex.Centroid
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/-
Source/core/bridge triage:
- `source-facing`: Definition 2.3.13 names the equal-weight point of an `m`-simplex as its
  midpoint or barycenter.
- `core/canonical`: for a simplex, the owner abstraction is the simplex-specific point
  `Affine.Simplex.centroid`.
- `bridge/view`: the generic finset-level presentation is recovered by
  `Affine.Simplex.univ_centroid_eq`, while the textbook equal-coefficient affine-combination
  formula is recovered from `Affine.Simplex.centroid_eq_affineCombination` together with the
  canonical finset owner lemma `Finset.centroidWeights_eq_const`.
- Domain-style sampling used here: `Affine.Simplex.centroid`,
  `Affine.Simplex.univ_centroid_eq`, `Affine.Simplex.centroid_eq_affineCombination`, and
  `Finset.centroidWeights_eq_const`.
- Primitive data vs derived API: the barycenter itself is the canonical simplex point
  `s.centroid`; the explicit equal-coefficient affine-combination formula and its finset-level
  presentation are derived API and should stay direct recalls rather than parallel local
  definitions.
- Layer target: `core/canonical`; this item is a direct recall of the simplex centroid owner and
  its canonical bridge lemmas, so no local barycenter wrapper or duplicate affine-combination
  owner belongs here.
-/

/- Definition 2.3.13: the midpoint or barycenter of a simplex is its canonical simplex centroid
`Affine.Simplex.centroid`. -/
recall Affine.Simplex.centroid

/- The simplex-specific centroid is exactly the centroid of the full finite vertex family. -/
recall Affine.Simplex.univ_centroid_eq

/- The barycenter is the affine combination of the simplex vertices with the standard centroid
weights. -/
recall Affine.Simplex.centroid_eq_affineCombination

section

universe u v w

open Finset

namespace Affine.Simplex

variable {𝕜 : Type u} {V : Type v} {P : Type w}
variable [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P]

/-- Simplex-owner bridge to the textbook equal-coefficient surface: the barycenter of an
`n`-simplex is the affine combination of its vertices with uniform coefficient
`(n + 1 : 𝕜)⁻¹`. -/
theorem centroid_eq_affineCombination_uniform {n : ℕ} (s : Simplex 𝕜 P n) :
    s.centroid = affineCombination 𝕜 univ s.points
      (fun _ : Fin (n + 1) => ((n + 1 : 𝕜)⁻¹)) := by
  simpa [Finset.centroidWeights_eq_const, Finset.card_univ, Fintype.card_fin] using
    s.centroid_eq_affineCombination

/-- Finite-index bridge: after reindexing vertices by an arbitrary finite type equivalent to
`Fin (n + 1)`, the simplex barycenter is still the equal-coefficient affine combination. -/
theorem centroid_eq_affineCombination_uniform_comp_equiv {n : ℕ} (s : Simplex 𝕜 P n)
    {ι : Type*} [Fintype ι] (e : ι ≃ Fin (n + 1)) :
    s.centroid = affineCombination 𝕜 univ (s.points ∘ e)
      (fun _ : ι => ((n + 1 : 𝕜)⁻¹)) := by
  calc
    s.centroid = affineCombination 𝕜 (univ : Finset (Fin (n + 1))) s.points
        (fun _ : Fin (n + 1) => ((n + 1 : 𝕜)⁻¹)) := by
      simpa using s.centroid_eq_affineCombination_uniform
    _ = affineCombination 𝕜 (Finset.map e.toEmbedding (univ : Finset ι)) s.points
        (fun _ : Fin (n + 1) => ((n + 1 : 𝕜)⁻¹)) := by
      simp
    _ = affineCombination 𝕜 (univ : Finset ι) (s.points ∘ e)
        ((fun _ : Fin (n + 1) => ((n + 1 : 𝕜)⁻¹)) ∘ e) := by
      simpa using
        (Finset.affineCombination_map (k := 𝕜) (s₂ := (univ : Finset ι))
          (e := e.toEmbedding) (w := fun _ : Fin (n + 1) => ((n + 1 : 𝕜)⁻¹)) (p := s.points))
    _ = affineCombination 𝕜 (univ : Finset ι) (s.points ∘ e)
        (fun _ : ι => ((n + 1 : 𝕜)⁻¹)) := by
      rfl

end Affine.Simplex

end

/-
Abstraction checklist for this item:
- codomain/ambient layer: no ordered-extended codomain owner appears; this item is affine-geometric
  and remains at the simplex owner layer.
- scalar minimization: the reused centroid APIs (`Affine.Simplex.centroid`,
  `Affine.Simplex.centroid_eq_affineCombination`, and `Finset.centroidWeights_eq_const`) are
  already at the canonical `[DivisionRing 𝕜]` layer and do not require specialization to `ℝ`.
- owner correctness: the barycenter owner is the intrinsic simplex owner
  `Affine.Simplex.centroid`; finite-weight formulas are derived bridge theorems.
- topology axis: not applicable; no ambient/intrinsic topology owner is present here.
- notation axis: no new notation is introduced, since the canonical owner names already match the
  source-facing barycenter content without adding parser or wrapper noise.
- finite-index minimization: besides the native `Fin (n + 1)` owner bridge
  `Affine.Simplex.centroid_eq_affineCombination_uniform`, the theorem
  `Affine.Simplex.centroid_eq_affineCombination_uniform_comp_equiv` exposes the same barycenter
  formula after reindexing along an intrinsic finite index type equivalence.
-/

/- For a finite family of vertices, each centroid weight is the reciprocal of the cardinality; in
the simplex case this gives the textbook uniform coefficient `1 / (m + 1)` directly from
`Affine.Simplex.centroid_eq_affineCombination` and `Finset.centroidWeights_eq_const`, without a
parallel local owner declaration. -/
recall Finset.centroidWeights_eq_const
