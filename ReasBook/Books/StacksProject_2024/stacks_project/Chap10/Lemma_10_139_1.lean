import Mathlib
import StacksProject_2024.Chap10.Lemma_10_138_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u

section

variable {A B C : Type u}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]

/- Domain triage:
- primary domain: the transitivity short exact sequence for Kähler differentials over a tower
  `A → B → C` under smoothness of `B → C`;
- sampled owner declarations:
  - `KaehlerDifferential.mapBaseChange`,
  - `KaehlerDifferential.map`,
  - `KaehlerDifferential.exact_mapBaseChange_map`,
  - `kaehlerDifferential_transitivity_sequence_splits_of_formallySmooth`;
- best owner abstraction: the canonical `KaehlerDifferential` maps and the canonical
  `ShortComplex.moduleCatMkOfKerLERange` built from them;
- primitive data: the tower `A → B → C`;
- derived API: exactness, injectivity, and surjectivity of the two canonical maps;
- layer triage:
  - `source-facing`: the short exactness of the transitivity sequence
    `0 → C ⊗[B] Ω[B⁄A] → Ω[C⁄A] → Ω[C⁄B] → 0`;
  - `core/canonical`: `KaehlerDifferential.mapBaseChange`, `KaehlerDifferential.map`, and the
    standard `ShortComplex` owner in `ModuleCat`;
  - `bridge/view`: the theorem below upgrading the source-facing smoothness hypothesis to
    `ShortComplex.ShortExact`.

The previous file introduced a separate public definition
`kaehlerDifferential_transitivity_shortComplex` even though the canonical owner object is already
`ShortComplex.moduleCatMkOfKerLERange`. Since that wrapper was unused downstream and added no new
mathematics, the refined file states the result directly on the canonical short complex.
-/

-- Proof sketch: smoothness implies formal smoothness, so Lemma `10.138.9` gives injectivity of the
-- left map in the transitivity sequence. Mathlib already supplies exactness in the middle via
-- `KaehlerDifferential.exact_mapBaseChange_map` and surjectivity of the right map via
-- `KaehlerDifferential.map_surjective`. These are exactly the three ingredients for
-- `ModuleCat.shortComplex_shortExact`.
/-- Lemma 10.139.1: if `B → C` is smooth, then the transitivity sequence
`0 → C ⊗[B] Ω[B⁄A] → Ω[C⁄A] → Ω[C⁄B] → 0`
is short exact. -/
theorem kaehlerDifferential_transitivity_shortExact_of_smooth [Algebra.Smooth B C] :
    (ShortComplex.moduleCatMkOfKerLERange
      (ModuleCat.ofHom (KaehlerDifferential.mapBaseChange A B C))
      (ModuleCat.ofHom (KaehlerDifferential.map A B C C))
      (LinearMap.exact_iff.mp (KaehlerDifferential.exact_mapBaseChange_map A B C)).ge).ShortExact := by
  let S : ShortComplex (ModuleCat C) :=
    ShortComplex.moduleCatMkOfKerLERange
      (ModuleCat.ofHom (KaehlerDifferential.mapBaseChange A B C))
      (ModuleCat.ofHom (KaehlerDifferential.map A B C C))
      (LinearMap.exact_iff.mp (KaehlerDifferential.exact_mapBaseChange_map A B C)).ge
  refine ModuleCat.shortComplex_shortExact S ?_ ?_ ?_
  · simpa [S] using KaehlerDifferential.exact_mapBaseChange_map A B C
  · simpa [S] using
      (show Function.Injective (KaehlerDifferential.mapBaseChange A B C) from
        (kaehlerDifferential_transitivity_sequence_splits_of_formallySmooth).1)
  · simpa [S] using KaehlerDifferential.map_surjective A B C

end
