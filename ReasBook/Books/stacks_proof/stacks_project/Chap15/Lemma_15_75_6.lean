import Mathlib
import StacksProject_2024.Chap13.Definition_13_8_1
import StacksProject_2024.Chap15.Definition_15_75_1
import StacksProject_2024.Chap15.Lemma_15_65_9
import StacksProject_2024.Chap15.Lemma_15_67_8
import StacksProject_2024.Chap15.Lemma_15_75_2
import StacksProject_2024.Chap15.Lemma_15_75_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open DerivedCategory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

private abbrev Q : CochainComplex (ModuleCat.{u} R) ℤ ⥤ DerivedCategory (ModuleCat.{u} R) :=
  DerivedCategory.Q
private abbrev single₀ : ModuleCat.{u} R ⥤ DerivedCategory (ModuleCat.{u} R) :=
  DerivedCategory.singleFunctor (ModuleCat.{u} R) (0 : ℤ)

/- Domain-style sampling for Lemma 15.75.6:
- primary domain: perfect complexes in `D(R)` represented by bounded cochain complexes of
  `R`-modules, together with the chapter owners for pseudo-coherence and finite tor dimension;
- sampled owner declarations:
  `Compᵇ((ModuleCat R))`,
  `Q.obj`,
  `single₀`,
  `DerivedCategory.IsPerfect`,
  `CochainComplex.isPseudoCoherent_of_boundedAbove_of_termwise`,
  `hasFiniteTorDimension_of_bounded_of_termwise_hasFiniteTorDimension`,
  `isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension`,
  `ModuleCat.isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension`;
- best owner abstraction: the source-facing theorem should take its bounded complex through the
  chapter owner `Compᵇ(ModuleCat R)` rather than a raw cochain complex together with a separate
  boundedness witness, while the target owner remains the perfectness predicate on `D(R)`;
- primitive vs. derived:
  primitive data are the bounded representative `K : Compᵇ((ModuleCat R))` and the termwise
  perfectness hypotheses `(K.obj.X i).IsPerfect`;
  derived API is the perfectness of `Q.obj K.obj`, assembled from the canonical owners
  `IsPseudoCoherent` and `HasFiniteTorDimension`;
- source/core/bridge triage:
  `source-facing`: the textbook statement that a bounded complex with perfect terms is perfect;
  `core/canonical`: `Compᵇ(ModuleCat R)`, `DerivedCategory.IsPerfect`,
    `IsPseudoCoherent`, `HasFiniteTorDimension`;
  `bridge/view`: passage from the chosen bounded representative `K.obj` to its derived image
    `Q.obj K.obj`.

This file therefore stays `source-facing`, while rewriting the boundedness input to the canonical
bounded owner and using the chapter's perfectness characterization instead of a parallel local
induction wrapper.
-/

-- Proof sketch: use the module-level perfectness characterization from Lemma `15.75.3` to obtain
-- pseudo-coherence and finite tor dimension termwise. Then Lemmas `15.65.9` and `15.67.8` apply
-- to the bounded representative `K`, and Lemma `15.75.2` reassembles the resulting derived object
-- as perfect.
/-- Lemma 15.75.6: a bounded cochain complex of perfect `R`-modules is a perfect complex in
`D(R)`. -/
@[stacks 066T]
theorem cochainComplex_isPerfect_of_bounded_of_termwise
    (K : Compᵇ((ModuleCat R)))
    (hterm : ∀ i : ℤ, (K.obj.X i).IsPerfect) :
    (Q.obj K.obj).IsPerfect := by
  have hterm' : ∀ i : ℤ,
      (K.obj.X i).IsPseudoCoherent ∧ HasFiniteTorDimension ((single₀).obj (K.obj.X i)) := by
    intro i
    let M : ModuleCat.{u} R := K.obj.X i
    have hM : M.IsPerfect := by simpa [M] using hterm i
    have hM' : M.IsPseudoCoherent ∧ ModuleHasFiniteTorDimension M :=
      (ModuleCat.isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension M).1 hM
    simpa [M, ModuleHasFiniteTorDimension] using hM'
  have hboundedAbove : CochainComplex.minus (ModuleCat.{u} R) K.obj := K.property.2
  have hpc : ∀ i : ℤ, (K.obj.X i).IsPseudoCoherent := fun i ↦ (hterm' i).1
  refine
    (isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension (Q.obj K.obj)).2 ?_
  exact ⟨CochainComplex.isPseudoCoherent_of_boundedAbove_of_termwise K.obj hboundedAbove hpc,
    hasFiniteTorDimension_of_bounded_of_termwise_hasFiniteTorDimension K
      (fun i ↦ by
        simpa [ModuleHasFiniteTorDimension] using (hterm' i).2)⟩

end

end CategoryTheory
