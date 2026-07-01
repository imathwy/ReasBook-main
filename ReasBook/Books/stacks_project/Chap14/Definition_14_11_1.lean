import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped Simplicial

universe u

section

variable (U : SSet.{u}) (n : ℕ)

/- Domain-style sampling for Definition 14.11.1:
- primary domain: simplicial sets and their canonical face/degeneracy API
- sampled owner API:
  `SSet`,
  `SimplicialObject.δ`,
  `SimplicialObject.σ`,
  `SSet.degenerate`,
  `SSet.mem_degenerate_iff`,
  `SSet.degenerate_eq_iUnion_range_σ`
- source/core/bridge triage:
  `source-facing`: textbook terminology for simplices, faces, degeneracies, and degenerate
    simplices of a simplicial set;
  `core/canonical`: the ambient owner `SSet`, whose primitive data already provide simplex types
    `U _⦋n⦌`, face maps `U.δ`, degeneracy maps `U.σ`, and the degenerate locus `U.degenerate n`;
  `bridge/view`: the explicit existential reformulation of `z ∈ U.degenerate (n + 1)` in terms of
    a chosen degeneracy map `U.σ j`.
- primitive data: none are introduced locally; all primitive simplicial-set data already live on
  the owner `SSet`
- derived API: the textbook relations “is the `j`-th face of”, “is the `j`-th degeneracy of”, and
  “is degenerate” are direct restatements of the canonical owner data, so the file should recall
  those declarations rather than repackage them as local wrapper predicates or theorems
- layer target: `core/canonical` recall for simplices, faces, degeneracies, and degenerate
  simplices, together with recall of the canonical owner theorems describing degenerate simplices.
-/

/- Definition 14.11.1: an `n`-simplex of a simplicial set `U` is simply an element of the
degree-`n` term `U _⦋n⦌`. -/
#check (U _⦋n⦌)

/- The textbook `j`-th face of a simplex is obtained by the canonical face map `U.δ j`. -/
recall SimplicialObject.δ

/- The textbook `j`-th degeneracy of a simplex is obtained by the canonical degeneracy map
`U.σ j`. -/
recall SimplicialObject.σ

/- Degenerate simplices are recorded by the canonical set `U.degenerate n`. -/
recall SSet.degenerate

/- The canonical pointwise criterion for degeneracy is `SSet.mem_degenerate_iff`. -/
recall SSet.mem_degenerate_iff

/- The textbook description “degenerate iff in the image of some degeneracy map” is the canonical
set equality `SSet.degenerate_eq_iUnion_range_σ`. -/
recall SSet.degenerate_eq_iUnion_range_σ

end
