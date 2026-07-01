import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import stacks_project.Chap15.Definition_15_65_1
import stacks_project.Chap15.Definition_15_70_1
import stacks_project.Chap15.Definition_15_75_1
import stacks_project.Chap15.Lemma_15_74_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "Mod" => ModuleCat R
local notation "DMod" => DerivedCategory Mod
local notation "RHomPkg" => MonoidalClosed DMod

/- Domain-style sampling for 15.99.1:
- primary domain: isomorphism criteria for the tensor-right/internal-Hom comparison in `D(R)`;
- sampled owner declarations:
  `CategoryTheory.derivedInternalHom_tensor_right_comparison`,
  `DerivedCategory.IsGE`,
  `DerivedCategory.IsPerfect`,
  `DerivedCategory.IsPseudoCoherent`,
  `HasFiniteInjectiveDimension`;
- best owner abstraction:
  `source-facing`: the textbook isomorphism criterion for the canonical comparison morphism from
    Lemma `15.74.3`;
  `core/canonical`: the chosen monoidal-closed owner `H : MonoidalClosed DMod`, the comparison
    morphism `derivedInternalHom_tensor_right_comparison H K L M`, and the Chapter 15 owners
    `K.IsPerfect`, `K.IsPseudoCoherent`, and `HasFiniteInjectiveDimension M`;
  `bridge/view`: the bounded-below branch hypothesis `∃ n : ℤ, L.IsGE n`, which expresses the
    source condition without forcing a global `D⁺(R)` owner on the perfect branch.
- primitive vs. derived:
  the primitive input is the comparison owner `H`, the object `L : D(R)`, and the branch-level
  hypotheses on `K`, `L`, and `M`; a bounded-below owner object `L : D⁺(R)` is derived data, so
  it should not be built into the theorem header when only one disjunct needs it.
-/

-- Proof sketch: choose the bounded-above finite-projective representative of `K` supplied either
-- by perfectness or by pseudo-coherence, and compute the comparison on cochain complexes as in
-- Lemma `15.72.6`. In the perfect case the boundedness of the representative makes the degreewise
-- tensor-Hom comparison a finite direct-sum argument; in the pseudo-coherent case, combine the
-- bounded-above representative of `K` with a bounded-below representative of `L` and a bounded
-- injective representative of `M` coming from finite injective dimension to get the same finiteness
-- on the relevant total-complex degrees.
/-- Lemma 15.99.1: for the tensor-right comparison map
`R\mathrm{Hom}_R(L, M) \otimes_R^{\mathbf L} K \to
R\mathrm{Hom}_R(R\mathrm{Hom}_R(K, L), M)`, the morphism is an isomorphism whenever either `K`
is perfect, or `K` is pseudo-coherent, `L` is bounded below, and `M` has finite injective
dimension. -/
theorem derivedInternalHomTensorRightComparison_hom_isIso_of_isPerfect_or_of_pseudoCoherent_boundedBelow_finiteInjectiveDimension
    (H : RHomPkg)
    (K L M : DMod)
    (hcases : K.IsPerfect ∨
      K.IsPseudoCoherent ∧ (∃ n : ℤ, L.IsGE n) ∧ HasFiniteInjectiveDimension M) :
    IsIso (derivedInternalHom_tensor_right_comparison H K L M) := sorry

end

end CategoryTheory
