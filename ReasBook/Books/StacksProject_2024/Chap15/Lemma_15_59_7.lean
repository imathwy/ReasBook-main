import StacksProject_2024.Chap13.Definition_13_8_1
import StacksProject_2024.Chap15.Definition_15_59_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {R : Type u} [CommRing R]

namespace CochainComplex

/- Domain-style sampling:
- primary domain: K-flat cochain complexes of `R`-modules and the bounded-above flat criterion;
- inspected owner declarations:
  `CochainComplex.IsKFlat`,
  `CochainComplex.IsTermwiseFlat`,
  `CochainComplex.isKFlat_iff`,
  `CochainComplex.minus`,
  `CochainComplex.minus_iff`;
- best owner abstraction: the chapter owner predicate is `P.IsKFlat` on the complex `P` itself,
  with boundedness expressed by the existing owner predicate
  `CochainComplex.minus (ModuleCat R) P` rather than by a repeated existential spelling, and with
  termwise flatness as a separate hypothesis;
- primitive data: the complex `P`, the bounded-above hypothesis
  `hbounded : CochainComplex.minus (ModuleCat R) P`, and the termwise flatness hypothesis
  `hFlat : P.IsTermwiseFlat`;
- derived API: the K-flatness conclusion `P.IsKFlat`.

Source/core/bridge triage:
- `source-facing`: the bounded-above flat criterion from the source text;
- `core/canonical`: `CochainComplex.IsKFlat` and `CochainComplex.IsTermwiseFlat`;
- `bridge/view`: `CochainComplex.isKFlat_iff`, the owner eliminator expressing K-flatness by
  preservation of acyclicity under totalized tensoring.

The theorem is already an owner-level source-facing statement, so the refine pass should keep that
statement and move only its surface to the canonical owner-style spelling.
-/

-- Proof sketch: let `L^•` be any acyclic complex. Truncate `L^•` above a degree containing a
-- representative of a given class in the total tensor product to reduce to the bounded-above
-- case, then apply the homology spectral sequence for `Tot(L^• ⊗_R P^•)`. Its `E₁`-page is zero
-- because each `P^q` is flat and `L^•` is acyclic, so the total tensor product is acyclic.
/-- Lemma 15.59.7: a bounded above cochain complex of flat `R`-modules is K-flat, expressed in
the canonical owner predicate `P.IsKFlat`. -/
theorem isKFlat_of_boundedAbove_of_flat
    (P : CochainComplex (ModuleCat R) ℤ)
    (hbounded : CochainComplex.minus (ModuleCat R) P)
    (hFlat : P.IsTermwiseFlat) :
    P.IsKFlat := sorry

end CochainComplex

end
