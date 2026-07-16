import Mathlib
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Tactic.Recall
import stacks_proof.stacks_project.Chap13.Lemma_13_33_7
import stacks_proof.stacks_project.Chap13.Lemma_13_33_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open DerivedCategory
open Opposite

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

local instance : AB5OfSize.{0, 0} (ModuleCat.{u} R) :=
  AB5OfSize_shrink (ModuleCat.{u} R)

local instance : CountableAB4 (ModuleCat.{u} R) := by
  let _ : HasFiniteBiproducts (ModuleCat.{u} R) := Abelian.hasFiniteBiproducts
  exact CountableAB4.of_countableAB5 (ModuleCat.{u} R)

local instance : HasCountableCoproducts (DerivedCategory (ModuleCat.{u} R)) :=
  derivedCategory_hasCountableCoproducts_of_exactCountableCoproducts

/- Domain-style sampling for Lemma 15.79.2:
- primary domain: canonical Hom-to-homotopy-colimit comparison maps in derived categories;
- inspected owner declarations:
  `CategoryTheory.termwise_colimit_is_homotopy_colimit`,
  `CategoryTheory.termwise_colimit_presentation_map`,
  `CategoryTheory.termwise_colimit_presentation_distinguished`,
  `CategoryTheory.homologicalFunctor_hocolim_comparison`,
  `CategoryTheory.preadditiveCoyoneda_hocolim_comparison_is_iso`,
  `CategoryTheory.homologicalFunctor_hocolim_comparison_is_iso`;
- best owner abstraction: the Chapter 13 owner
  `homologicalFunctor_hocolim_comparison`, specialized to
  `preadditiveCoyoneda.obj (op K)`, with its canonical `IsIso` theorem;
- primitive-vs-derived split:
  the primitive data are the sequential system `t` and the represented Hom functor
  `preadditiveCoyoneda.obj (op K)`;
  the actual telescope presentation of the termwise colimit is already owned upstream by
  `termwise_colimit_presentation_map`,
  `termwise_colimit_presentation_connecting`, and
  `termwise_colimit_presentation_distinguished`;
  the source-facing comparison statement here is therefore only the represented-Hom
  specialization of the Chapter 13 owners
  `preadditiveCoyoneda_hocolim_comparison_is_iso` and
  `homologicalFunctor_hocolim_comparison`.

Source/core/bridge triage:
- `source-facing`: the statement that `Hom_{D(R)}(K,-)` carries the termwise colimit complex to
  the sequential colimit of the Hom groups when it preserves countable direct sums;
- `core/canonical`: `preadditiveCoyoneda_hocolim_comparison_is_iso`;
- `bridge/view`: the Chapter 13 termwise-colimit presentation declarations specialized to
  `Functor.ofSequence t`. -/

variable {L : ℕ → CochainComplex (ModuleCat.{u} R) ℤ}

/- Lemma 15.79.2: this is exactly the Chapter 13 represented-Hom comparison theorem
`preadditiveCoyoneda_hocolim_comparison_is_iso`, specialized to the canonical termwise-colimit
presentation from `Lemma_13_33_7`. The numbered item adds no new owner beyond that specialization,
so the main entry is a direct specialized canonical use rather than a duplicate theorem shell. -/
/-
Core owner recall: the ambient represented-Hom hocolim comparison is already owned upstream by
`preadditiveCoyoneda_hocolim_comparison_is_iso`. -/
recall preadditiveCoyoneda_hocolim_comparison_is_iso

/-
Lemma 15.79.2 is the source-facing specialization of that owner to the canonical termwise-colimit
presentation attached to `Functor.ofSequence t`. -/
#check
  fun (K : DerivedCategory (ModuleCat.{u} R))
    [PreservesColimitsOfShape (Discrete ℕ) (preadditiveCoyoneda.obj (op K))]
    (t : ∀ n, L n ⟶ L (n + 1)) ↦
      let S := Functor.ofSequence t
      let T : ℕ ⥤ DerivedCategory (ModuleCat.{u} R) := S ⋙ Q
      preadditiveCoyoneda_hocolim_comparison_is_iso K
        (fun n ↦ Q.map (t n))
        (termwise_colimit_presentation_map S)
        (termwise_colimit_presentation_connecting S)
        (by
          simpa [T, S, sequentialTelescopeMap, Functor.ofSequence_map_homOfLE_succ] using
            termwise_colimit_presentation_distinguished S)

end

end CategoryTheory
