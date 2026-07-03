import Mathlib
import StacksProject_2024.Chap10.Lemma_10_147_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory MorphismProperty
open CommRingCat

universe u₁ u₂

namespace RingHom

section

variable {R₁ : Type u₁} {Λ₁ : Type u₁} {R₂ : Type u₂} {Λ₂ : Type u₂}
variable [CommRing R₁] [CommRing Λ₁] [CommRing R₂] [CommRing Λ₂]

/- Domain sampling pass:
* primary domain: filtered colimits of smooth commutative ring maps and their stability under
  products;
* sampled owner declarations:
  - `RingHom.IsFilteredColimitOfSmooth`, the source-facing owner for PT presentations;
  - `CategoryTheory.MorphismProperty.ind`, the generic owner for filtered-colimit closure of a
    morphism property;
  - `Algebra.smooth_prod_iff`, the product criterion for smooth commutative algebras.
* best owner abstraction: the public owner here is `f.IsFilteredColimitOfSmooth`;
* primitive data: two ring homomorphisms `f₁`, `f₂`;
* derived API: any chosen filtered diagrams, cocones, and smooth stage maps witnessing PT.

Source/core/bridge triage:
* `source-facing`: PT is stable under products of ring maps;
* `core/canonical`: `f.IsFilteredColimitOfSmooth`;
* `bridge/view`: any chosen filtered diagram in `Under (CommRingCat.of _)` presenting the given
  product map.

The Noetherian and regular-map hypotheses from Situation 16.8.1 are mathematically redundant here,
so they should not remain in the public API.
-/

-- Proof sketch: choose filtered diagrams of smooth algebras presenting `f₁` and `f₂`. Their
-- product diagram is again filtered, each stage map to the product is smooth because smoothness is
-- preserved by finite products, and the product cocone presents `f₁.prodMap f₂` as the
-- corresponding filtered colimit.
/-- Lemma 16.8.2: if two ring maps satisfy PT, i.e. each is a filtered colimit of smooth algebras
over its source, then their product map also satisfies PT. -/
theorem smooth_ind_prodMap
    {f₁ : R₁ →+* Λ₁} {f₂ : R₂ →+* Λ₂}
    (hf₁ : f₁.IsFilteredColimitOfSmooth)
    (hf₂ : f₂.IsFilteredColimitOfSmooth) :
    (f₁.prodMap f₂).IsFilteredColimitOfSmooth := sorry

end

end RingHom
