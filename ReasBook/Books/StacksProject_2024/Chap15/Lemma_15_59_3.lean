import Mathlib
import StacksProject_2024.Chap15.Definition_15_59_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape
open ModuleCat

noncomputable section

universe u

section

variable {R R' : Type u} [CommRing R] [CommRing R']

/- Domain-style sampling:
- primary domain: change of rings for module-valued cochain complexes and preservation of the
  owner predicate `CochainComplex.IsKFlat`;
- inspected owner declarations:
  `CochainComplex.IsKFlat`,
  `CochainComplex.isKFlat_iff`,
  `ModuleCat.extendScalars`,
  `Functor.mapHomologicalComplex`.
- best owner abstraction: the owner is still the predicate `K.IsKFlat` on the cochain complex
  itself; extension of scalars is bridge data, not a second owner.
- primitive data: the ring map `f`, the complex `K`, and the hypothesis `hK : K.IsKFlat`.
- derived API: K-flatness of the canonically extended complex.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma asserting that extension of scalars preserves K-flatness;
- `core/canonical`: `CochainComplex.IsKFlat`;
- `bridge/view`: the functor `extendScalars f` on module complexes.

The target complex is canonical data coming from `extendScalars f`, so the public statement should
expose only the owner predicate on that complex rather than any auxiliary wrapper.
-/

-- Proof sketch: unfold `CochainComplex.IsKFlat`. For an acyclic `R'`-complex `L`, view `L` as an
-- `R`-complex by restriction of scalars and use the canonical identification
-- `(K ⊗[R] R') ⊗[R'] L ≅ K ⊗[R] L`; then apply the K-flatness of `K`.
/-- Lemma 15.59.3: for a ring map `R → R'`, extension of scalars sends a K-flat complex of
`R`-modules to a K-flat complex of `R'`-modules. -/
theorem extendScalarsComplex_isKFlat
    (f : R →+* R') (K : CochainComplex (ModuleCat R) ℤ)
    (hK : K.IsKFlat) :
    CochainComplex.IsKFlat (((extendScalars f).mapHomologicalComplex (up ℤ)).obj K) :=
  sorry

end
