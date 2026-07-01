import Mathlib
import stacks_project.Chap15.Definition_15_65_1
import stacks_project.Chap15.Lemma_15_92_3
import stacks_project.Chap15.Lemma_15_92_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A] (I : Ideal A)

local notation "DMod" => DerivedCategory (ModuleCat A)

/- Domain-style sampling:
- primary domain: pseudo-coherent objects in `D(A)` and the chapter owner predicate
  `K.IsDerivedCompleteWithRespectTo I`;
- sampled owner-side declarations:
  `DerivedCategory.IsPseudoCoherent`,
  `ModuleCat.isDerivedCompleteWithRespectTo_of_isAdicComplete`,
  `derivedCompleteObjectProperty_isWeakSerreClass`,
  `isDerivedCompleteWithRespectTo_iff_mem_derivedCategoryCohomologyInProperty`;
- best owner abstraction: the source-facing statements below should stay on the canonical owner
  `K.IsDerivedCompleteWithRespectTo I`, with module-level adic completeness entering only through
  the bridge theorem from Lemma `15.92.3`;
- primitive data: the ideal `I`, the derived object `K`, and the ring object
  `ModuleCat.of A A`;
- derived API: the weak-Serre owner on derived-complete modules and the cohomology-in-property
  reformulation from Lemma `15.92.6`.

Layer triage:
- `source-facing`: Lemma `15.92.8` itself;
- `core/canonical`: `K.IsDerivedCompleteWithRespectTo I`;
- `bridge/view`: `ModuleCat.isDerivedCompleteWithRespectTo_of_isAdicComplete` and
  `isDerivedCompleteWithRespectTo_iff_mem_derivedCategoryCohomologyInProperty`. -/

-- Proof sketch: a pseudo-coherent object of `D(A)` is represented by a bounded-above finite-free
-- complex, so every cohomology module is a subquotient of finite free `A`-modules and hence is
-- pseudo-coherent as an `A`-module. Since `A`, viewed as an `A`-module, is derived complete,
-- pseudo-coherent modules are derived complete by the weak Serre property from Lemma `15.92.6`;
-- apply the cohomological criterion there to conclude that `K` itself is derived complete.
/-- Lemma 15.92.8: if the ring `A`, viewed as an `A`-module, is derived complete with respect to
an ideal `I`, then every pseudo-coherent object of `D(A)` is derived complete with respect to
`I`. -/
theorem isDerivedCompleteWithRespectTo_of_isPseudoCoherent
    {K : DMod} (hA : (ModuleCat.of A A).IsDerivedCompleteWithRespectTo I)
    (hK : K.IsPseudoCoherent) :
    K.IsDerivedCompleteWithRespectTo I := sorry

-- Proof sketch: by Lemma `15.92.3`, `I`-adic completeness of the `A`-module `A` implies derived
-- completeness with respect to `I`; then apply `isDerivedCompleteWithRespectTo_of_isPseudoCoherent`.
/-- If the ring `A`, viewed as an `A`-module, is `I`-adically complete, then every
pseudo-coherent object of `D(A)` is derived complete with respect to `I`. -/
theorem isDerivedCompleteWithRespectTo_of_isPseudoCoherent_of_isAdicComplete
    {K : DMod} (hA : IsAdicComplete I (ModuleCat.of A A))
    (hK : K.IsPseudoCoherent) :
    K.IsDerivedCompleteWithRespectTo I := by
  exact isDerivedCompleteWithRespectTo_of_isPseudoCoherent I
    (ModuleCat.isDerivedCompleteWithRespectTo_of_isAdicComplete (ModuleCat.of A A) hA)
    hK

end
