import Mathlib
import StacksProject_2024.Chap15.Definition_15_59_1
import StacksProject_2024.Chap15.Definition_15_67_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory
open scoped DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ
local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "H" => homologyFunctor (ModuleCat R)
local notation "Q" => DerivedCategory.Q
local notation "single₀" => singleFunctor (ModuleCat R) (0 : ℤ)

/- Domain-style sampling for Lemma 15.67.4:
- primary domain: lower-bounded tor-amplitude in `D(R)` and representative complexes computing
  derived tensor products with degree-zero modules;
- sampled owner declarations:
  `HasTorAmplitudeIn`,
  `DerivedCategory.IsGE`,
  `DerivedCategory.isGE_iff`,
  `CochainComplex.IsKFlat`,
  `CochainComplex.IsTermwiseFlat`;
- best owner abstraction: the lower-bound condition should be phrased through the canonical
  t-structure owner `IsGE` on each derived tensor product `K ⊗[R]^L M[0]`, while the
  representative side should expose the primitive complex predicates directly instead of bundling
  them into a new wrapper class;
- primitive vs. derived:
  primitive data are a representative complex `E`, its support condition `E.IsStrictlyGE a`, its
  K-flatness and termwise flatness, and an isomorphism `K ≅ Q.obj E`;
  derived API is the lower-bounded tor-amplitude predicate on `K`, together with the equivalence
  between that predicate and the existence of such a representative;
- source/core/bridge triage:
  `source-facing`: `HasTorAmplitudeGE` and the main equivalence theorem below;
  `core/canonical`: `DerivedCategory.IsGE`, `DerivedCategory.isGE_iff`, `CochainComplex.IsKFlat`,
    `CochainComplex.IsTermwiseFlat`, and `CochainComplex.IsStrictlyGE`;
  `bridge/view`: the use of `K ⊗[R]^L M[0]` to transport the derived-category lower-bound
    condition to a concrete K-flat flat representative.
-/

/-- An object of `D(R)` has tor-amplitude in `[a, ∞]` if tensoring with any degree-zero
`R`-module produces an object of the derived category lying in degrees `≥ a`. -/
def HasTorAmplitudeGE (K : DMod) (a : ℤ) : Prop :=
  ∀ M : ModuleCat R, (K ⊗[R]^L (single₀).obj M).IsGE a

/-- Finite-interval tor-amplitude in `[a, b]` implies lower tor-amplitude in `[a, ∞]`. -/
theorem HasTorAmplitudeIn.hasTorAmplitudeGE {K : DMod} {a b : ℤ}
    (hK : HasTorAmplitudeIn K a b) :
    HasTorAmplitudeGE K a := by
  intro M
  rw [isGE_iff]
  intro i hi
  exact hK M i fun hmem ↦ (not_lt_of_ge hmem.1 hi).elim

-- Proof sketch: unfold `HasTorAmplitudeGE` and rewrite the derived-category `IsGE` condition by
-- the canonical t-structure characterization in terms of vanishing of homology below degree `a`.
/-- An object of `D(R)` has tor-amplitude in `[a, ∞]` exactly when tensoring with any degree-zero
`R`-module has vanishing homology in every degree `< a`. -/
theorem hasTorAmplitudeGE_iff
    (K : DMod) (a : ℤ) :
    HasTorAmplitudeGE K a ↔
      ∀ (M : ModuleCat R) (i : ℤ), i < a →
        IsZero ((H i).obj (K ⊗[R]^L (single₀).obj M)) := by
  simp [HasTorAmplitudeGE, isGE_iff]

-- Proof sketch: for `(→)`, choose a termwise-flat K-flat resolution of a representative of `K`,
-- use the tor-amplitude hypothesis to show the cokernel in degree `a` is flat, truncate below `a`,
-- and apply the K-flat closure lemmas to the resulting short exact sequence. For `(←)`, tensor the
-- chosen K-flat representative with any degree-zero module and compute the derived tensor product
-- on the nose; since the tensor complex is strictly supported in degrees `≥ a`, its homology
-- vanishes below `a`.
/-- Lemma 15.67.4: an object `K` of `D(R)` has tor-amplitude in `[a, ∞]` if and only if it is
quasi-isomorphic to a K-flat cochain complex of flat `R`-modules that vanishes in every degree
`< a`. -/
theorem hasTorAmplitudeGE_iff_exists_representative
    (K : DMod) (a : ℤ) :
    HasTorAmplitudeGE K a ↔
      ∃ (E : Cpx) (_ : K ≅ Q.obj E),
        E.IsStrictlyGE a ∧ E.IsKFlat ∧ E.IsTermwiseFlat := sorry

end

end CategoryTheory
