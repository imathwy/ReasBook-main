import Mathlib
import stacks_project.Chap15.Lemma_15_65_15
import stacks_project.Chap15.Lemma_15_67_17
import stacks_project.Chap15.Lemma_15_75_2

noncomputable section

open CategoryTheory
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R R' : Type u} [CommRing R] [CommRing R']

/- Domain-style sampling for Lemma 15.75.13:
- primary domain: faithful-flat descent of perfect objects in derived module categories;
- sampled owner declarations:
  `DerivedCategory.IsPerfect`,
  `isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension`,
  `isPseudoCoherent_of_faithfullyFlat_baseChange`,
  `derivedTensorWithAlgebra`,
  `hasTorAmplitudeIn_of_faithfullyFlat_baseChange`;
- best owner abstraction: this item is `source-facing`, while the `core/canonical` owner is
  `DerivedCategory.IsPerfect`; the ring map itself should remain explicit in the public statement,
  and the derived scalar-extension owner should appear directly as `derivedTensorWithAlgebra f`,
  with the algebra-based tensor notation reserved for the bridge view;
- primitive vs. derived:
  primitive data are the ring map `f`, the derived object `K`, the faithfully flatness of `f`,
  and the perfectness of the derived base change;
  pseudo-coherence and tor-amplitude are derived API used to recover the owner predicate, so they
  should not be repackaged as parallel public data here;
- source/core/bridge triage:
  `source-facing`: faithful-flat descent of perfectness;
  `core/canonical`: `DerivedCategory.IsPerfect`;
  `bridge/view`: the passage from `((derivedTensorWithAlgebra f).obj K)` to the standard derived
    base-change notation `K ⊗[R]^L[R']` after passing from `f` to `f.toAlgebra`.

This file therefore stays at the `source-facing` layer but uses the chapter owner predicate and
the standard derived base-change surface, while keeping the ring map explicit instead of hiding it
in an ambient algebra instance.
-/

-- Proof sketch: use Lemma `15.75.2` to reduce perfection to pseudo-coherence plus finite tor
-- dimension. Descend pseudo-coherence from the faithfully flat base change by Lemma `15.65.15`,
-- and descend finite tor dimension from the faithfully flat base change by Lemma `15.67.17`
-- through the tor-amplitude characterization.
/-- Lemma 15.75.13: if the derived base change of `K^•` along a faithfully flat ring map
`R → R'` is perfect, then `K^•` is already perfect. -/
theorem isPerfect_of_faithfullyFlat_baseChange
    (f : R →+* R') (K : DerivedCategory (ModuleCat.{u} R)) (hff : f.FaithfullyFlat)
    (hK : ((derivedTensorWithAlgebra f).obj K).IsPerfect) :
    K.IsPerfect := by
  let K' : DerivedCategory (ModuleCat.{u} R') := (derivedTensorWithAlgebra f).obj K
  have hK' : K'.IsPerfect := by
    simpa [K'] using hK
  have hbase :
      K'.IsPseudoCoherent ∧ HasFiniteTorDimension K' :=
    (isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension K').1 hK'
  refine (isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension K).2 ?_
  refine ⟨?_, ?_⟩
  · exact isPseudoCoherent_of_faithfullyFlat_baseChange f K hff hbase.1
  · rcases (hasFiniteTorDimension_iff K').1 hbase.2 with ⟨a, b, htor⟩
    exact
      (hasTorAmplitudeIn_of_faithfullyFlat_baseChange f K a b hff
        htor).hasFiniteTorDimension

end

end CategoryTheory
