import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.Smooth R S] [IsReduced R]

/- Domain-style sampling pass:
* primary domain: commutative algebra of smooth ring maps and ascent of reducedness;
* sampled owner declarations of the same kind:
  - `Algebra.Smooth`, the ambient owner of the source hypothesis;
  - `Algebra.Smooth.flat`, the canonical flatness consequence used downstream;
  - `isReduced_of_flat_of_fiber`, the chapter owner for reducedness ascent from reduced fibers;
  - `Algebra.IsGeometricallyReduced`, the field-valued owner underlying the fiberwise reducedness
    step in the proof sketch.

Best owner abstraction:
* the source-facing owner here is already `isReduced_of_smooth`; the smooth structure
  `[Algebra.Smooth R S]` is primitive data, while flatness and fiberwise reducedness are derived
  API that should be supplied by canonical owners rather than by a local wrapper.

Primitive data vs. derived API:
* primitive data: the smooth `R`-algebra structure on `S` and the reducedness owner `[IsReduced R]`;
* derived API: flatness of `R → S`, smoothness or geometric reducedness of the residue-field
  fibers, and the final ascent step through `isReduced_of_flat_of_fiber`.

Source/core/bridge triage:
* `source-facing`: `isReduced_of_smooth`, the textbook reducedness ascent statement for smooth
  algebras;
* `core/canonical`: `Algebra.Smooth`, `IsReduced`, and the field-level owner
  `Algebra.IsGeometricallyReduced`;
* `bridge/view`: the canonical fiberwise reducedness consequences of smoothness together with the
  reducedness-ascent theorem `isReduced_of_flat_of_fiber`.
-/
-- Proof sketch: smooth algebras are flat by `Algebra.Smooth.flat`, and smoothness is preserved
-- under base change to residue fields. A smooth algebra over a field is geometrically reduced, so
-- every fiber `κ(𝔭) ⊗[R] S` is reduced; then Lemma `10.163.6` gives the result.
/-- Lemma 10.163.7: if `R → S` is smooth and `R` is reduced, then `S` is reduced. -/
theorem isReduced_of_smooth :
    IsReduced S := sorry

/-- Smooth algebras over reduced base rings are reduced. -/
instance : IsReduced S :=
  isReduced_of_smooth

end
