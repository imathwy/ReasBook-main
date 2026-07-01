import Mathlib
import stacks_project.Chap15.Definition_15_105_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/- Domain-style sampling:
- primary domain: commutative algebra of integrally closed extensions and flat epimorphisms of
  rings;
- sampled owner declarations:
  `IsIntegrallyClosedIn`,
  `HasWeakDimensionLE`,
  `Algebra.IsEpi`,
  `RingHom.surjective_iff_epi_and_finite`;
- best owner abstraction: this lemma is `source-facing`, but its epimorphism input should use the
  algebra-level owner `Algebra.IsEpi A B`; the category-theoretic condition
  `Epi (CommRingCat.ofHom (algebraMap A B))` is only a bridge, via `CommRingCat.epi_iff_epi`;
- primitive vs. derived:
  primitive data is the weak-dimension hypothesis on `A`, flatness of `B` over `A`, injectivity
  of `algebraMap A B`, and the owner predicate `Algebra.IsEpi A B`;
  derived API is the conclusion `IsIntegrallyClosedIn A B`, so no extra local wrapper around ring
  epimorphisms is warranted here.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma asserting integral closedness of `A` inside `B`;
- `core/canonical`: `IsIntegrallyClosedIn`, `HasWeakDimensionLE`, `Module.Flat`, `Algebra.IsEpi`;
- `bridge/view`: the category-theoretic epimorphism formulation in `CommRingCat`, used only when a
  categorical pushout/pullback argument is needed.
-/

-- Proof sketch: if `x : B` is integral over `A`, let `A' := A[x] ⊆ B`. By finite generation of
-- simple integral extensions, `A'` is finite over `A`. Since `A` has weak dimension at most `1`
-- and `B` is flat over `A`, Lemma `15.105.18` gives flatness of the finite `A`-submodule `A'`.
-- The multiplication map `A' ⊗[A] A' → A'` factors through `B`, and injectivity of `A → B`
-- together with the ring-epimorphism hypothesis forces `A → A'` to be an epimorphism. Then
-- `RingHom.surjective_iff_epi_and_finite` makes `A → A'` surjective, so `x` comes from `A`.
/-- Lemma 15.105.21: if `A` has weak dimension at most `1` and `A → B` is a flat, injective
epimorphism of commutative rings, then `A` is integrally closed in `B`. -/
theorem isIntegrallyClosedIn_of_hasWeakDimensionLEOne_of_flat_of_injective_of_epi
    [HasWeakDimensionLE A 1] [Module.Flat A B]
    (hinj : Function.Injective (algebraMap A B)) [Algebra.IsEpi A B] :
    IsIntegrallyClosedIn A B := sorry

end
