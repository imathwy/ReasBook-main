import Mathlib
import StacksProject_2024.Chap12.Definition_12_27_5
import StacksProject_2024.Chap19.Lemma_19_12_4

open CategoryTheory

universe w v u

namespace CochainComplex

section

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {I : Type w}

open CategoryTheory.Limits
open HomotopicalAlgebra

/-- Helper for Theorem 19.12.6: Lemma 19.12.4 already supplies the first-stage functorial
approximation used in the source transfinite tower. -/
private theorem existsAcyclicKillingApproximation [IsGrothendieckAbelian.{w} C]
    (K : I → CochainComplex C ℤ) (hK : ∀ i : I, (K i).Acyclic) :
    ∃ J : FunctorialComplexApproximation C,
      ∀ (i : I) (M : CochainComplex C ℤ) (w : K i ⟶ M),
        Nonempty (Homotopy (w ≫ J.ι.app M) 0) := by
  -- Proof comment: this is exactly the canonical owner theorem from Lemma 19.12.4.
  simpa using exists_acyclic_killing_resolution_functor (C := C) (K := K) hK

/-
Domain-style sampling for Theorem 19.12.6:
- primary domain: functorial K-injective resolutions of cochain complexes in a Grothendieck
  abelian category;
- sampled owner declarations:
  `FunctorialComplexApproximation`,
  `CochainComplex.IsKInjective`,
  `CochainComplex.InjectiveResolution`,
  `ResolutionFunctor`;
- best owner abstraction: the core owner in this chapter is already
  `FunctorialComplexApproximation C`; the injective-term and K-injective conditions in
  Theorem 19.12.6 are derived properties of the chosen target complexes, not new primitive
  structure deserving a second public wrapper;
- primitive data: a functorial complex approximation `J : FunctorialComplexApproximation C`;
- derived API: the termwise injectivity and K-injectivity of `J.toFunctor.obj M`.

Source/core/bridge triage:
- `source-facing`: the existence of a functorial K-injective replacement for every cochain
  complex;
- `core/canonical`: `FunctorialComplexApproximation C` and `I.IsKInjective`;
- `bridge/view`: the extra injective-term and K-injective properties on the chosen approximation.
-/

-- Proof sketch: start from the functorial injective-subobject approximation of Lemma 19.12.5 and
-- iterate it transfinitely as in the proof of Theorem 19.11.7. Lemma 19.12.3 upgrades the limit
-- complex to a K-injective one once the stage has sufficiently large cofinality, while AB5 keeps
-- the transition colimit quasi-isomorphic to the original complex and preserves the degreewise
-- monomorphism and injective-term properties.
/-- Theorem 19.12.6: in a Grothendieck abelian category there exists a functorial assignment
`M^\bullet ↦ I^\bullet` together with a quasi-isomorphism `M^\bullet ⟶ I^\bullet` whose degreewise
components are monomorphisms, such that every term `I^n` is injective and the target complex is
K-injective. -/
@[stacks 079P]
theorem exists_functorial_kInjective_resolution (C : Type u) [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{w} C] :
    ∃ J : FunctorialComplexApproximation C,
      (∀ (M : CochainComplex C ℤ) (n : ℤ), Injective ((J.toFunctor.obj M).X n)) ∧
        ∀ M : CochainComplex C ℤ, (J.toFunctor.obj M).IsKInjective := by
  -- Route correction: the canonical owner route is still blocked upstream. An attempted import of
  -- `stacks_project.Chap19.Lemma_19_12_5` fails with hard chain-map packaging errors around
  -- lines 261, 366, 376, 384, 389, 402, 417, 468, 510, 681, and 694, so the transfinite tower
  -- cannot yet be assembled from dependency-closed Chapter 19 owners.
  -- TODO: repair `Lemma_19_12_5`, then reuse `Lemma_19_12_4`, `Lemma_19_12_5`, and
  -- `Lemma_19_12_3` to build the large-cofinality transfinite tower and package the resulting
  -- stage as the required functorial K-injective approximation.
  sorry

end

end CochainComplex
