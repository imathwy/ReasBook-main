import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import StacksProject_2024.Chap15.Definition_15_65_1
import StacksProject_2024.Chap15.Lemma_15_67_4
import StacksProject_2024.Chap15.Definition_15_75_1
import StacksProject_2024.Chap15.Lemma_15_74_5
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "RHomPkg" => MonoidalClosed DMod

/- Domain-style sampling for 15.99.3:
- primary domain: the derived tensor/internal-Hom comparison from Lemma `15.74.5` and its
  isomorphism criteria;
- sampled owner declarations:
  `CategoryTheory.derivedInternalHom_tensor_left_comparison`,
  `CategoryTheory.derivedTensorProduct`,
  `DerivedCategory.IsPerfect`,
  `CategoryTheory.HasTorAmplitudeGE`;
- best owner abstraction:
  `source-facing`: the tor-amplitude/perfection hypotheses of Lemma `15.99.3`;
  `core/canonical`: the chosen monoidal-closed owner `H : MonoidalClosed DMod`, the upstream
    comparison map, and the chapter tor-amplitude owner `HasTorAmplitudeGE`;
  `bridge/view`: none beyond reuse of the comparison owner from `Lemma_15_74_5`;
- primitive data vs. derived API: the primitive non-perfect branch is the direct conjunction of
  pseudo-coherence of `M`, lower boundedness of `L`, and lower tor-amplitude of `K` for a chosen
  bound `a`; the two perfect branches are separate companion uses of the same upstream comparison
  owner, so the tor-amplitude index should stay local to the third branch rather than burdening
  the whole theorem header.
-/

-- Proof sketch: in the first two cases, reduce by triangulated-generation and direct-sum
-- preservation to the generator `R[n]`, where the comparison is tautological. In the third case,
-- choose a bounded-above finite-free representative of `M`, a bounded-below representative of
-- `L`, and a K-flat representative of `K` with the stated lower tor-amplitude bound, then identify
-- both sides with the two termwise equal total complexes from the textbook proof.
/-- Lemma 15.99.3, perfect source case: the canonical morphism
`K \otimes_R^{\mathbf L} R\mathrm{Hom}_R(M, L) \to
R\mathrm{Hom}_R(M, K \otimes_R^{\mathbf L} L)` from Lemma `15.74.5` is an isomorphism when the
source object `M` of the internal Hom is perfect. -/
@[stacks 0ATK]
theorem derivedInternalHomTensorLeftComparison_hom_isIso_of_source_isPerfect
    (H : RHomPkg)
    (K L M : DMod)
    (hM : M.IsPerfect) :
    IsIso (derivedInternalHom_tensor_left_comparison H K L M) := by
  -- TODO: follow the source proof route. Define the object property on `M` saying the component
  -- `derivedInternalHom_tensor_left_comparison H K L M` is an isomorphism, prove that property is
  -- triangulated and stable under retracts using
  -- `derivedInternalHom_tensor_left_comparison_natural_source`, then reduce from perfect objects
  -- to the generator `ringSingle` via
  -- `perfectObjectProperty_eq_objectGeneratedProperty_ring_single (R := R)`.
  let _ := hM
  sorry

/-- Lemma 15.99.3, perfect tensor-factor case: the canonical morphism
`K \otimes_R^{\mathbf L} R\mathrm{Hom}_R(M, L) \to
R\mathrm{Hom}_R(M, K \otimes_R^{\mathbf L} L)` is an isomorphism when the tensor factor `K` is
perfect. -/
@[stacks 0ATK]
theorem derivedInternalHomTensorLeftComparison_hom_isIso_of_tensor_isPerfect
    (H : RHomPkg)
    (K L M : DMod)
    (hK : K.IsPerfect) :
    IsIso (derivedInternalHom_tensor_left_comparison H K L M) := by
  -- TODO: mirror the previous branch in the tensor variable. The iso-locus in `K` should be
  -- shown triangulated and stable under retracts using
  -- `derivedInternalHom_tensor_left_comparison_natural_tensor`, after which the `ringSingle`
  -- base case and `perfectObjectProperty_eq_objectGeneratedProperty_ring_single` finish.
  let _ := hK
  sorry

/-- Lemma 15.99.3, tor-amplitude branch: the canonical morphism
`K \otimes_R^{\mathbf L} R\mathrm{Hom}_R(M, L) \to
R\mathrm{Hom}_R(M, K \otimes_R^{\mathbf L} L)` is an isomorphism when `M` is pseudo-coherent,
`L` lies in `D^+(R)`, and `K` has tor-amplitude in `[a, ∞]`. -/
@[stacks 0ATK]
theorem derivedInternalHomTensorLeftComparison_hom_isIso_of_isPseudoCoherent_of_boundedBelow_of_hasTorAmplitudeGE
    (H : RHomPkg)
    (K L M : DMod) (a : ℤ)
    (hM : M.IsPseudoCoherent)
    (hL : ∃ n : ℤ, L.IsGE n)
    (hK : HasTorAmplitudeGE K a) :
    IsIso (derivedInternalHom_tensor_left_comparison H K L M) := by
  -- TODO: execute the explicit-complex route from the textbook proof. Choose a bounded-above
  -- finite-free model for `M` via `exists_pseudoCoherent_representation`, a bounded-below model
  -- for `L` via `exists_boundedBelow_representation`, and a K-flat termwise-flat model for `K`
  -- via `hasTorAmplitudeGE_iff_exists_representative`; then transport the comparison to the
  -- complex-level map from `Lemma_15_72_4` and prove that map is degreewise an isomorphism.
  let _ := hM
  let _ := hL
  let _ := hK
  sorry

/-- Lemma 15.99.3: the canonical morphism
`K \otimes_R^{\mathbf L} R\mathrm{Hom}_R(M, L) \to
R\mathrm{Hom}_R(M, K \otimes_R^{\mathbf L} L)` from Lemma `15.74.5` is an isomorphism whenever
either `M` is perfect, or `K` is perfect, or for some integer `a`, `M` is pseudo-coherent, `L`
lies in `D^+(R)`, and `K` has tor-amplitude in `[a, ∞]`. -/
@[stacks 0ATK]
theorem derivedInternalHomTensorLeftComparison_hom_isIso_of_isPerfect_or_of_pseudoCoherent_boundedBelow_torAmplitudeGE
    (H : RHomPkg)
    (K L M : DMod)
    (hcases : M.IsPerfect ∨ K.IsPerfect ∨
      ∃ a : ℤ, M.IsPseudoCoherent ∧ (∃ n : ℤ, L.IsGE n) ∧ HasTorAmplitudeGE K a) :
    IsIso (derivedInternalHom_tensor_left_comparison H K L M) := by
  -- Proof comment: the statement is exactly the disjunction of the three branch theorems above,
  -- so a case split reduces immediately to the corresponding source-faithful branch.
  rcases hcases with hM | hK | ⟨a, hM, hL, hTor⟩
  · exact derivedInternalHomTensorLeftComparison_hom_isIso_of_source_isPerfect H K L M hM
  · exact derivedInternalHomTensorLeftComparison_hom_isIso_of_tensor_isPerfect H K L M hK
  · exact
      derivedInternalHomTensorLeftComparison_hom_isIso_of_isPseudoCoherent_of_boundedBelow_of_hasTorAmplitudeGE
        H K L M a hM hL hTor

end

end CategoryTheory
