import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import stacks_project.Chap10.Lemma_10_163_6
import stacks_project.Chap15.Lemma_15_105_4
import stacks_project.Chap15.Lemma_15_105_5
import stacks_project.Chap15.Lemma_15_105_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open scoped TensorProduct

variable {A : Type u} [CommRing A]
variable {B : Type v} [CommRing B] [Algebra A B]

/- Domain-style sampling:
- primary domain: commutative algebra of weakly étale ring maps, absolute flatness, and
  reducedness ascent along flat maps with reduced fibers;
- sampled owner declarations:
  `IsAbsolutelyFlatRing`,
  `Algebra.IsWeaklyEtale`,
  `hasWeakDimensionLE_of_isWeaklyEtale`,
  `isReduced_of_flat_of_fiber`,
  `Ideal.Fiber`,
  `isReduced_of_isAbsolutelyFlatRing`;
- best owner abstraction: the ambient map property is the chapter owner
  `Algebra.IsWeaklyEtale`, while absolute flatness and reducedness remain owner predicates on the
  source and target rings;
- primitive vs. derived: the primitive data are the owner classes `IsAbsolutelyFlatRing A`,
  `IsReduced A`, and `Algebra.IsWeaklyEtale A B`; the two transfer theorems below are derived API;
- source/core/bridge triage:
  `source-facing`: the two Stacks transfer lemmas below;
  `core/canonical`: `IsAbsolutelyFlatRing`, `IsReduced`, `Algebra.IsWeaklyEtale`,
    `hasWeakDimensionLE_of_isWeaklyEtale`, `Ideal.Fiber`, `isReduced_of_flat_of_fiber`, and
    `isReduced_of_isAbsolutelyFlatRing`;
  `bridge/view`: the zero-weak-dimension TFAE and weakly étale base change to residue-field
    fibers, with part `(1)` upgrading those field fibers to absolutely flat rings and hence
    reduced rings.

This file should therefore expose the source-facing consequences directly in terms of the explicit
owner input `hAB : Algebra.IsWeaklyEtale A B`, reusing the chapter ascent owners instead of
introducing parallel local reducedness or absolute-flatness wrappers. For reducedness, the
source-facing weakly étale fiber theorem below is the bridge into the general ascent owner
`isReduced_of_flat_of_fiber`.
-/

-- Proof sketch: by Lemma `15.105.5`, absolute flatness of `A` is equivalent to weak dimension at
-- most `0`. Lemma `15.105.4` transports that owner property across the weakly étale map `A → B`,
-- and Lemma `15.105.5` then turns weak dimension at most `0` back into absolute flatness of `B`.
/-- Lemma 15.105.8 (1): if `A` is absolutely flat and `A → B` is weakly étale, then `B` is
absolutely flat. -/
theorem isAbsolutelyFlatRing_of_isWeaklyEtale
    (hAB : Algebra.IsWeaklyEtale A B) [IsAbsolutelyFlatRing A] :
    IsAbsolutelyFlatRing B := by
  letI : HasWeakDimensionLE A 0 := hasWeakDimensionLEZero_of_isAbsolutelyFlatRing A
  have hB : HasWeakDimensionLE B 0 := hasWeakDimensionLE_of_isWeaklyEtale A B 0 hAB
  letI : HasWeakDimensionLE B 0 := hB
  exact isAbsolutelyFlatRing_of_hasWeakDimensionLEZero B

-- After base change to a residue field, a weakly étale map stays weakly étale. Over a field, part
-- `(1)` makes the fiber absolutely flat, and reducedness is the thin companion from
-- Lemma `15.105.5`.
/-- Every fiber ring `p.asIdeal.Fiber B = κ(p) ⊗[A] B` of a weakly étale map `A → B` is
absolutely flat. -/
theorem isAbsolutelyFlatRing_fiber_of_isWeaklyEtale
    (hAB : Algebra.IsWeaklyEtale A B) (p : PrimeSpectrum A) :
    IsAbsolutelyFlatRing (p.asIdeal.Fiber B) := by
  let hfiber : Algebra.IsWeaklyEtale p.asIdeal.ResidueField (p.asIdeal.Fiber B) := hAB.baseChange
  exact isAbsolutelyFlatRing_of_isWeaklyEtale hfiber

/-- Every fiber ring `p.asIdeal.Fiber B = κ(p) ⊗[A] B` of a weakly étale map `A → B` is
reduced. -/
theorem isReduced_fiber_of_isWeaklyEtale
    (hAB : Algebra.IsWeaklyEtale A B) (p : PrimeSpectrum A) :
    IsReduced (p.asIdeal.Fiber B) := by
  letI : IsAbsolutelyFlatRing (p.asIdeal.Fiber B) :=
    isAbsolutelyFlatRing_fiber_of_isWeaklyEtale hAB p
  exact isReduced_of_isAbsolutelyFlatRing (p.asIdeal.Fiber B)

/-- Lemma 15.105.8 (2): if `A` is reduced and `A → B` is weakly étale, then `B` is reduced. -/
theorem isReduced_of_isWeaklyEtale
    (hAB : Algebra.IsWeaklyEtale A B) [IsReduced A] :
    IsReduced B := by
  have hfiber : ∀ p : PrimeSpectrum A, IsReduced (p.asIdeal.Fiber B) :=
    isReduced_fiber_of_isWeaklyEtale hAB
  sorry

end
