import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open Topology
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Semantic recall: `lean_leansearch` returned canonical scheme-morphism pullback/immersion
owners, and local Chapter 28 files use the module pullback owner `Scheme.Modules.pullback` together
with the project-local ampleness owner `Scheme.Modules.IsAmple`.  In item mode, importing
`Definition_28_26_1` to expose `IsAmple` forces Lake to rebuild upstream Chapter 17
nonvanishing-locus files before target elaboration, where the read-only Lake state currently
fails.  This file therefore records the source lemma as a labeled recall block and checks the
available dependency-closed owners instead of introducing a fake replacement for ampleness. -/

variable {X X' : Scheme.{u}}

/- Lemma 28.26.14: let `X` be a scheme, let `L` be an ample invertible
`\mathcal O_X`-module, and let `i : X' ⟶ X` be a morphism of schemes. If either `i` is a
quasi-compact immersion, `X'` is quasi-compact and `i` is an immersion, `i` is quasi-compact and
induces a homeomorphism from `X'` onto its image, or `X'` is quasi-compact and `i` induces such a
homeomorphism, then `i^* L` is ample on `X'`.

The dependency-closed pieces currently available here are the canonical scheme-morphism
conditions, the topological embedding owner for the homeomorphism-onto-image clause, and the
scheme-module pullback functor.  The intended conclusion, when the local ampleness owner is
available, is `Scheme.Modules.IsAmple ((Scheme.Modules.pullback i).obj L)`. -/
#check fun (i : X' ⟶ X) ↦ QuasiCompact i
#check fun (i : X' ⟶ X) ↦ IsImmersion i
#check fun (i : X' ⟶ X) ↦ IsEmbedding (i : X' → X)
#check fun (X' : Scheme.{u}) ↦ CompactSpace X'
#check fun (i : X' ⟶ X) ↦ Scheme.Modules.pullback i

end AlgebraicGeometry.Scheme.Modules
