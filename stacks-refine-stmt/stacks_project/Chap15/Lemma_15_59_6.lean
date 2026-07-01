import stacks_project.Chap10.Lemma_10_39_12
import stacks_project.Chap15.Definition_15_59_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u

section

variable {R : Type u} [CommRing R]
variable {S : ShortComplex (CochainComplex (ModuleCat R) ℤ)}

namespace CategoryTheory.ShortComplex.ShortExact

/- Domain-style sampling pass:
* primary domain: K-flat cochain complexes of `R`-modules in short exact sequences of complexes;
* sampled owner declarations:
  - `CochainComplex.IsKFlat`, `CochainComplex.isKFlat_iff`, and
    `CochainComplex.IsTermwiseFlat` from `Definition_15_59_1`, the owner predicate, its canonical
    eliminator, and the termwise flatness hypothesis used in the statement;
  - `ShortComplex.ShortExact.homology_exact₁`, `homology_exact₂`, and `homology_exact₃`, the
    canonical exactness owners for the long exact homology sequence of a short exact sequence of
    complexes;
  - `tensorLeft_of_flat_cokernel` from `Chap10/Lemma_10_39_12`, the termwise tensor-exactness
    bridge applied degreewise after using the termwise flatness of `S.X₃`;
  - `ShortComplex.ShortExact`, the canonical short-complex owner namespace for the source-facing
    three-term statements.

Source/core/bridge triage:
* `source-facing`: the three two-out-of-three K-flatness implications for a short exact sequence of
  cochain complexes;
* `core/canonical`: `CochainComplex.IsKFlat`, `CochainComplex.isKFlat_iff`,
  `CochainComplex.IsTermwiseFlat`, `ShortComplex.ShortExact`, and its exactness consequences
  `homology_exact₁`, `homology_exact₂`, `homology_exact₃`;
* `bridge/view`: tensoring the short exact sequence with an acyclic test complex via the degreewise
  flatness bridge `tensorLeft_of_flat_cokernel`.

Primitive data are only the short exactness proof `hS`, the termwise flatness of `S.X₃`, and the
relevant K-flatness hypotheses on two of the three terms. The tensor short exact sequence is
derived API from the Chapter 10 tensor-exactness bridge together with the canonical short-exact
homology sequence, so this file should keep only the three source-facing consequences below and
not introduce an auxiliary wrapper for the tensorized sequence.
-/

variable (hS : S.ShortExact) (hFlat₃ : S.X₃.IsTermwiseFlat)

-- Proof sketch: tensor the short exact sequence `S` on the left with an acyclic complex `M`.
-- Since each term `S.X₃.X n` is flat, the Chapter 10 tensor-exactness bridge theorem
-- `tensorLeft_of_flat_cokernel` gives degreewise short exactness after
-- tensoring. If `S.X₁` and `S.X₂` are K-flat, the first two tensor complexes are acyclic, so the
-- third is acyclic by the canonical short-exact homology sequence. Via
-- `CochainComplex.isKFlat_iff`, this is exactly the K-flatness condition for `S.X₃`.
/-- Lemma 15.59.6 (1): in a short exact sequence `0 ⟶ K₁^\bullet ⟶ K₂^\bullet ⟶ K₃^\bullet ⟶ 0`
of cochain complexes of `R`-modules, if every term of `K₃^\bullet` is flat and `K₁^\bullet` and
`K₂^\bullet` are K-flat, then `K₃^\bullet` is K-flat. -/
theorem isKFlat_X₃ (hK₁ : S.X₁.IsKFlat) (hK₂ : S.X₂.IsKFlat) :
    S.X₃.IsKFlat := sorry

-- Proof sketch: tensor the short exact sequence `S` on the left with an acyclic complex `M`.
-- Degreewise flatness of `S.X₃` preserves short exactness after tensoring by the same bridge
-- theorem, so the resulting sequence of total tensor products is short exact. If `S.X₁` and
-- `S.X₃` are K-flat, the outer tensor complexes are acyclic, forcing the middle one to be acyclic
-- by the canonical short-exact homology sequence. Unfolding with
-- `CochainComplex.isKFlat_iff` yields the desired owner-level statement.
/-- Lemma 15.59.6 (2): in a short exact sequence `0 ⟶ K₁^\bullet ⟶ K₂^\bullet ⟶ K₃^\bullet ⟶ 0`
of cochain complexes of `R`-modules, if every term of `K₃^\bullet` is flat and `K₁^\bullet` and
`K₃^\bullet` are K-flat, then `K₂^\bullet` is K-flat. -/
theorem isKFlat_X₂ (hK₁ : S.X₁.IsKFlat) (hK₃ : S.X₃.IsKFlat) :
    S.X₂.IsKFlat := sorry

-- Proof sketch: tensor the short exact sequence `S` on the left with an acyclic complex `M`.
-- Degreewise flatness of `S.X₃` keeps the tensor sequence short exact degreewise by
-- `tensorLeft_of_flat_cokernel`, so its total complexes form a short
-- exact sequence. If `S.X₂` and `S.X₃` are K-flat, then the last two tensor complexes are
-- acyclic, and the canonical short-exact homology sequence forces acyclicity of the first one.
-- This is the `S.X₁.IsKFlat` condition after rewriting with `CochainComplex.isKFlat_iff`.
/-- Lemma 15.59.6 (3): in a short exact sequence `0 ⟶ K₁^\bullet ⟶ K₂^\bullet ⟶ K₃^\bullet ⟶ 0`
of cochain complexes of `R`-modules, if every term of `K₃^\bullet` is flat and `K₂^\bullet` and
`K₃^\bullet` are K-flat, then `K₁^\bullet` is K-flat. -/
theorem isKFlat_X₁ (hK₂ : S.X₂.IsKFlat) (hK₃ : S.X₃.IsKFlat) :
    S.X₁.IsKFlat := sorry

end CategoryTheory.ShortComplex.ShortExact

end
