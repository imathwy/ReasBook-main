import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_78_6
import StacksProject_2024.stacks_project.Chap10.Lemma_10_83_1
import StacksProject_2024.stacks_project.Chap15.Definition_15_33_2
import StacksProject_2024.stacks_project.Chap15.Lemma_15_86_2

-- Declarations for this item will be appended below by the statement pipeline.

open Algebra
open scoped TensorProduct

noncomputable section

universe u

section

variable {A A' B : Type u}
variable [CommRing A] [CommRing A'] [CommRing B]
variable [Algebra A A'] [Algebra A B]

local notation "B'" => B ⊗[A] A'

attribute [local instance] Algebra.TensorProduct.leftAlgebra
attribute [local instance] Algebra.TensorProduct.rightAlgebra

local instance :
    Module B' ↥(LinearMap.ker (H1Cotangent.baseChangeComparison A A' B)) :=
  Submodule.module (LinearMap.ker (H1Cotangent.baseChangeComparison A A' B))

/-- Helper for Lemma 15.86.5: once the comparison kernel is finitely presented and flat over the
pushout ring `B'`, the textbook last step identifies it as a finite projective `B'`-module. -/
theorem finiteProjective_ker_of_baseChangeComparison_of_finitePresentation_and_flat
    [Module.FinitePresentation B' ↥(LinearMap.ker (H1Cotangent.baseChangeComparison A A' B))]
    [Module.Flat B' ↥(LinearMap.ker (H1Cotangent.baseChangeComparison A A' B))] :
    Module.FiniteProjective B'
      ↥(LinearMap.ker (H1Cotangent.baseChangeComparison A A' B)) := by
  -- Proof comment: this is exactly the textbook last step, packaged through the chapter-level
  -- equivalence between finite projective modules and finitely presented flat modules.
  simpa [Module.FiniteProjective] using
    (module_finite_projective_iff_finitePresentation_and_flat
      (R := B')
      (M := ↥(LinearMap.ker (H1Cotangent.baseChangeComparison A A' B)))).2
      ⟨inferInstance, inferInstance⟩

/- Domain-style sampling:
- primary domain: base change for local complete intersection ring maps and the induced
  cotangent-homology comparison kernel;
- sampled owner declarations:
  `RingHom.IsLocalCompleteIntersection`,
  `RingHom.IsLocalCompleteIntersection.ofLocalizationSpanTarget`,
  `Algebra.IsRelativeGlobalCompleteIntersection.baseChange`,
  `H1Cotangent.baseChangeComparison`;
- best owner abstraction: the primitive source-facing input is only
  `RingHom.IsLocalCompleteIntersection (algebraMap A B)`;
  the pushout lci structure on `algebraMap A' B'` is derived bridge data from the complete-
  intersection base-change/locality story and should not remain a second public hypothesis;
- primitive vs. derived: the comparison kernel
  `LinearMap.ker (H1Cotangent.baseChangeComparison A A' B)` is the source-facing object of the
  lemma, while the lci property of `A' → B'` is internal proof data. -/

-- Proof sketch: by Lemma `15.86.4`, the naive cotangent complexes for `A → B` and the derived
-- base-changed local complete intersection map `A' → B'` are perfect of tor-amplitude in
-- `[-1, 0]`. Lemma `15.86.2` and the pushout
-- comparison give a distinguished triangle whose cone has only one nonzero cohomology module,
-- namely this kernel in degree `-1`. The cone is again perfect of tor-amplitude in `[-1, 1]`,
-- so Lemmas `15.65.4` and `15.67.6` make the kernel finitely presented and flat, hence finite
-- projective.
/-- Lemma 15.86.5: for a cocartesian square of commutative rings, written in the owner-facing
tensor order as the pushout `B' = B ⊗[A] A'`, if `A → B` is a local complete intersection, then
the kernel of the canonical comparison
`H^{-1}(NL_{B/A} ⊗[B] B') → H^{-1}(NL_{B'/A'})`, expressed in the library-facing form as the
kernel of `H1Cotangent.baseChangeComparison A A' B`,
is a finite projective `B'`-module.
-/
theorem ker_h1Cotangent_baseChange_comparison_finite_projective_of_isLocalCompleteIntersection
    [RingHom.IsLocalCompleteIntersection (algebraMap A B)] :
    Module.FiniteProjective B'
      ↥(LinearMap.ker (H1Cotangent.baseChangeComparison A A' B)) := by
  have hbase :
      RingHom.IsLocalCompleteIntersection (algebraMap A' B') := by
    -- TODO(Lemma 15.86.5): derive the pushout local-complete-intersection instance from the
    -- chosen lci presentation of `A → B` once the upstream base-change comparison file compiles.
    sorry
  letI := hbase
  -- TODO(Lemma 15.86.5): after the upstream `H1Cotangent.baseChangeComparison` API compiles,
  -- follow the source-faithful fiber/kernel route to prove finite projectivity of the kernel.
  sorry

end
