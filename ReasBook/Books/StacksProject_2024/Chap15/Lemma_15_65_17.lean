import Mathlib
import stacks_project.Chap13.Situation_13_15_1
import stacks_project.Chap15.Definition_15_65_1

noncomputable section

open CategoryTheory
open DerivedCategory.TStructure

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R] [IsNoetherianRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "BoundedAbove" => (t.minus : ObjectProperty DMod)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)

/- Domain-style sampling for Lemma 15.65.17:
- primary domain: pseudo-coherence in the derived category of modules over a Noetherian ring and
  its degree-zero module specialization;
- sampled owner declarations:
  `DerivedCategory.IsMPseudoCoherent`,
  `DerivedCategory.IsPseudoCoherent`,
  `boundedAboveDerivedCategory`,
  `ModuleCat.IsPseudoCoherent`;
- best owner abstraction: the source-facing statements in parts `(1)` and `(2)` stay on the
  chapter owners `K.IsMPseudoCoherent` and `K.IsPseudoCoherent`, while the module theorem in part
  `(3)` should use the ordinary unbundled module bridge surface rather than a parallel bundled
  `ModuleCat`-only theorem;
- primitive vs. derived:
  primitive data are the derived owner predicates and the bounded-above owner subcategory from
  Lemma `15.65.10`;
  derived API is the bounded-above finite-homology characterization below, together with the
  degree-zero module bridge in part `(3)`;
- source/core/bridge triage:
  `source-facing`: the three numbered criteria of Lemma `15.65.17`;
  `core/canonical`: `K.IsMPseudoCoherent`, `K.IsPseudoCoherent`, and
    `boundedAboveDerivedCategory (ModuleCat R)`;
  `bridge/view`: the ordinary module surface `(ModuleCat.of R M).IsPseudoCoherent`.
-/

-- Proof sketch: for the forward implication, use the bounded-above finite-free approximation in
-- the definition of `m`-pseudo-coherence to see that `K` lies in `D^-(R)` and that the cohomology
-- groups in degrees `i ≥ m` are finite. For the reverse implication, combine the bounded-above
-- hypothesis with the finiteness of `H^i(K)` for `i ≥ m`, use that finite modules are
-- pseudo-coherent over a Noetherian ring, and apply Lemma `15.65.10`.
/-- Lemma 15.65.17 (1): a derived `R`-complex is `m`-pseudo-coherent exactly when it lies in
`D^-(R)` and its cohomology modules `H^i` are finite for all `i ≥ m`. -/
theorem isMPseudoCoherent_iff_boundedAbove_and_homology_finite_ge
    (K : DMod) (m : ℤ) :
    K.IsMPseudoCoherent m ↔
      BoundedAbove K ∧
        ∀ i : ℤ, m ≤ i → Module.Finite R ((H i).obj K) := sorry

-- Proof sketch: apply part `(1)` for every integer `m`. If `K` is pseudo-coherent, then it is
-- `m`-pseudo-coherent for all `m`; conversely, bounded-above together with finiteness of every
-- cohomology module makes each cohomology module pseudo-coherent over a Noetherian ring, so
-- Lemma `15.65.10` yields `m`-pseudo-coherence for every `m`, hence pseudo-coherence.
/-- Lemma 15.65.17 (2): a derived `R`-complex is pseudo-coherent exactly when it lies in `D^-(R)`
and all of its cohomology modules are finite. -/
theorem isPseudoCoherent_iff_boundedAbove_and_homology_finite
    (K : DMod) :
    K.IsPseudoCoherent ↔
      BoundedAbove K ∧
        ∀ i : ℤ, Module.Finite R ((H i).obj K) := sorry

end

section

variable {R : Type u} [Ring R] [IsNoetherianRing R]
variable {M : Type u} [AddCommGroup M] [Module R M]

-- Proof sketch: over a Noetherian ring, every finite module is pseudo-coherent and every
-- pseudo-coherent module is finite. Translate the module into the derived category concentrated in
-- degree `0` and combine these two implications with the module-level definition of
-- pseudo-coherence.
/-- Lemma 15.65.17 (3): an `R`-module is pseudo-coherent exactly when it is finite. -/
theorem _root_.Module.isPseudoCoherent_iff_finite :
    (ModuleCat.of R M).IsPseudoCoherent ↔ Module.Finite R M := sorry

end

end CategoryTheory
