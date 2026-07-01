import Mathlib.Tactic.Recall
import stacks_project.Chap15.Lemma_15_59_5

-- Declarations for this item will be appended below by the statement pipeline.

namespace SheafOfModules.RingedSite

/- Domain-style sampling for Lemma 21.17.6:
- primary domain: K-flat cochain complexes in distinguished triangles;
- sampled owner declarations:
  `CochainComplex.IsKFlat`,
  `CochainComplex.isKFlat_obj₃_of_distinguished_triangle`,
  `CochainComplex.isKFlat_obj₂_of_distinguished_triangle`,
  `CochainComplex.isKFlat_obj₁_of_distinguished_triangle`;
- best owner abstraction: the Chapter 15 generic distinguished-triangle two-out-of-three theorems
  for the owner predicate `CochainComplex.IsKFlat`;
- primitive vs derived: primitive data are only a distinguished triangle in the relevant homotopy
  category together with K-flatness of two of its vertices; the ringed-site formulation is derived
  API by specialization, not a second local owner.

Source/core/bridge triage:
- `source-facing`: the ringed-site two-out-of-three property for K-flat complexes in a
  distinguished triangle;
- `core/canonical`: the generic owner theorems
  `CochainComplex.isKFlat_obj₃_of_distinguished_triangle`,
  `CochainComplex.isKFlat_obj₂_of_distinguished_triangle`, and
  `CochainComplex.isKFlat_obj₁_of_distinguished_triangle`;
- `bridge/view`: this file, which should remain only a direct recall of that specialization, with
  no parallel local theorem or extra ambient scaffolding. -/

-- Proof sketch: Lemma `21.17.1` identifies totalized tensoring with a fixed complex on
-- `K(\mathrm{Mod}(\mathcal O))` as a triangulated functor, and Definition `21.17.2` says that
-- K-flatness means this functor sends acyclic complexes to acyclic complexes. Applying the generic
-- Chapter 15 distinguished-triangle two-out-of-three theorem at the owner level yields the
-- ringed-site statement directly.
/- Lemma 21.17.6 is the ringed-site specialization of the generic distinguished-triangle
two-out-of-three property for the owner predicate `CochainComplex.IsKFlat`. -/
recall CochainComplex.isKFlat_obj₃_of_distinguished_triangle
recall CochainComplex.isKFlat_obj₂_of_distinguished_triangle
recall CochainComplex.isKFlat_obj₁_of_distinguished_triangle

end SheafOfModules.RingedSite
