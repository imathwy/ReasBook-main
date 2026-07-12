import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open SSet.stdSimplex
open scoped Simplicial

/- Domain-style sampling for Example 14.11.2:
- primary domain: simplicial sets and the standard simplex `Δ[n]`, especially the degenerate and
  nondegenerate simplices of `Δ[n]`;
- sampled owner API:
  `SSet.HasDimensionLE`,
  `SSet.degenerate_eq_top_of_hasDimensionLT`,
  `stdSimplex.nonDegenerateEquiv`,
  `stdSimplex.mem_nonDegenerate_iff_mono`,
  `SimplexCategory.eq_id_of_mono`;
- best owner abstraction: the mathlib standard-simplex owner API already organizes both dimension
  bounds and nondegeneracy for `Δ[n]`; the first source-facing sentence is the exact owner
  specialization `Δ[n].degenerate_eq_top_of_hasDimensionLT ...`, while the second is a thin
  consequence of the canonical nondegenerate-simplex owner API;
- primitive data: the canonical simplicial set `Δ[n]`, the degrees `n` and `m`, and an
  `m`-simplex `x : Δ[n] _⦋m⦌`;
- derived API: degeneracy in degrees `m > n` is the canonical owner theorem
  `Δ[n].degenerate_eq_top_of_hasDimensionLT ...`, while uniqueness of the top nondegenerate
  simplex comes from `stdSimplex.mem_nonDegenerate_iff_mono` together with
  `SimplexCategory.eq_id_of_mono`.

Source/core/bridge triage:
- `source-facing`: the Stacks example says that every simplex of `Δ[n]` in degree `> n` is
  degenerate, and that the unique nondegenerate `n`-simplex is the identity simplex;
- `core/canonical`: the owner declarations sampled above;
- `bridge/view`: none. The file should remain a thin source-facing consequence of the owner API.
-/

variable (n m : ℕ) (h : n < m)

/- Example 14.11.2 (first sentence): every `m`-simplex of `Δ[n]` with `n < m` is degenerate.
Mathlib already exposes this exactly as the owner specialization
`Δ[n].degenerate_eq_top_of_hasDimensionLT (n + 1) m h`. -/
#check (Δ[n].degenerate_eq_top_of_hasDimensionLT (n + 1) m h : Δ[n].degenerate m = ⊤)

-- Proof sketch: a nondegenerate `n`-simplex of `Δ[n]` corresponds to a mono endomorphism of
-- `⦋n⦌`, and `SimplexCategory.eq_id_of_mono` identifies every such endomorphism with the identity.
/-- Example 14.11.2: the set of nondegenerate `n`-simplices of `Δ[n]` is the singleton consisting
of the simplex corresponding to the identity morphism of `[n]`. -/
@[stacks 0176]
theorem stdSimplex_nonDegenerate_eq_singleton_identity (n : ℕ) :
    Δ[n].nonDegenerate n =
      {objEquiv.symm (𝟙 ⦋n⦌)} := by
  rw [Set.eq_singleton_iff_unique_mem]
  constructor
  · simpa using
      (objEquiv_symm_mem_nonDegenerate_iff_mono (𝟙 ⦋n⦌)).2
        (by infer_instance : Mono (𝟙 ⦋n⦌))
  · intro x hx
    rw [mem_nonDegenerate_iff_mono] at hx
    exact objEquiv.injective <| SimplexCategory.eq_id_of_mono (objEquiv x)
