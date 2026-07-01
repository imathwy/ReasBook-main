import Mathlib
import stacks_project.Chap10.Definition_10_72_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory
open HomologicalComplex

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/- Domain-style sampling:
* primary domain: bounded-above chain complexes of finite modules over a Noetherian local ring,
  with exactness organized by the owner predicate `HomologicalComplex.ExactAt`;
* sampled owner declarations in this domain: `HomologicalComplex.ExactAt`,
  `HomologicalComplex.ExactAt.iff_isZero_homology`, `moduleDepth`, and
  `CategoryTheory.ShortComplex.ShortExact.moduleDepth_middle_ge_min`;
* best owner abstraction: exactness should stay on `C.ExactAt j`, while local depth should be
  stated through the chapter owner `moduleDepth` rather than by repeating
  `Ideal.depth (IsLocalRing.maximalIdeal R)`;
* source/core/bridge triage: the acyclicity lemma below is `source-facing`, the owner notions are
  `C.ExactAt` and `moduleDepth`, and the homology-finiteness instance is only the bridge needed to
  make `moduleDepth R (C.homology i)` available;
* primitive vs. derived split: the primitive data are the chain complex `C`, the bounded-above
  index range, and the tail depth and exactness hypotheses on the truncated complex from degree
  `i` up to degree `e`. Finiteness of `C.homology j` is derived API from the termwise finiteness
  assumption, so it should not be restated as extra theorem data.
-/

namespace ChainComplex

-- Proof sketch: realize `H_i(C)` as the quotient of cycles by boundaries in degree `i`. Since
-- kernels and images of maps between finite modules over a Noetherian ring are finite, and
-- quotients of finite modules are finite, the homology module is finite.
/-- Homology of a chain complex of finite modules over a Noetherian ring is finite. -/
instance homology_finite
    (C : ChainComplex (ModuleCat R) ℕ) [∀ j, Module.Finite R (C.X j)] (j : ℕ) :
    Module.Finite R (C.homology j) := sorry

end ChainComplex

-- Proof sketch: truncate the complex to the tail starting in degree `i`, use exactness in degrees
-- `> i` and the vanishing of the terms above `e` to build the successive short exact sequences of
-- cycles and boundaries occurring in the standard proof, apply Lemma `10.72.6` repeatedly to
-- propagate the tail depth bounds downward, and finally deduce that the degree-`i` homology has
-- depth at least `1`.
/-- Lemma 10.102.8 (Acyclicity lemma): if a bounded-above chain complex of finite modules over a
Noetherian local ring has depth at least `j` in each degree `j` from `i` through `e`, and `i > 0`
is the largest degree at which the complex is not exact, then the degree-`i` homology module has
depth at least `1`. -/
theorem depth_homology_ge_one_of_largest_nonexact_index
    {C : ChainComplex (ModuleCat R) ℕ} {e i : ℕ} [∀ j, Module.Finite R (C.X j)]
    (hi : 0 < i) (hie : i ≤ e)
    (hdepth : ∀ ⦃j : ℕ⦄, i ≤ j → j ≤ e → moduleDepth R (C.X j) ≥ (j : WithTop ℕ))
    (hbounded : ∀ j, e < j → Limits.IsZero (C.X j))
    (hnotExact : ¬ C.ExactAt i)
    (hexact : ∀ ⦃j : ℕ⦄, i < j → j ≤ e → C.ExactAt j) :
    moduleDepth R (C.homology i) ≥ (1 : WithTop ℕ) := sorry

end
