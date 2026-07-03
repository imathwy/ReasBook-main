import Mathlib.CategoryTheory.Core
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Data.List.TFAE
import Mathlib.RingTheory.PicardGroup

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_15_118_1 (from Chap15) -/
open CategoryTheory MonoidalCategory TensorProduct

universe u

namespace ModuleCat

variable {R : Type u} [CommRing R]

/- Domain sampling:
- Primary domain: invertible modules in the symmetric monoidal category `ModuleCat R`.
- Core/canonical declarations inspected:
  - `Definition_4_43_4` / `(tensorLeft M).IsEquivalence`
  - `tensorLeft_isEquivalence_iff_exists_tensor_inverse`
  - `Module.Invertible R M`
  - `Module.Invertible.right`
  - `Module.Invertible.linearEquiv`
- Best owner abstraction: the chapter-wide invertibility owner `(tensorLeft M).IsEquivalence`,
  already fixed in Definition `4.43.4`; `Module.Invertible R M` is the specialized mathlib
  bridge for modules.
- Layer triage:
  - `source-facing`: the textbook tensor-left equivalence criterion for invertibility;
  - `core/canonical`: the chapter owner `(tensorLeft M).IsEquivalence`;
  - `bridge/view`: the theorem below identifying that owner with the specialized mathlib
    declaration `Module.Invertible R M`.
- Primitive vs. derived:
  - primitive data: the invertibility owner `(tensorLeft M).IsEquivalence`;
  - derived API: the module-specific reformulation `Module.Invertible R M`. -/

variable (M : ModuleCat R)

/- Definition 15.118.1: an `R`-module is invertible exactly when tensoring on the left by it is
an equivalence of `ModuleCat R`; this is the Chapter `4` owner specialized to modules. The
specialized mathlib predicate `Module.Invertible R M` is a companion bridge, not the main owner
of the definition. -/
#check (tensorLeft M).IsEquivalence

/-- For `R`-modules, the source-facing invertibility owner `(tensorLeft M).IsEquivalence` is
equivalent to the specialized mathlib predicate `Module.Invertible R M`. -/
theorem tensorLeft_isEquivalence_iff_moduleInvertible :
    (tensorLeft M).IsEquivalence ↔ Module.Invertible R M := by
  constructor
  · rintro hM
    rcases (tensorLeft_isEquivalence_iff_exists_tensor_inverse M).1 hM with ⟨N, -, ⟨e⟩⟩
    exact Module.Invertible.right e.toLinearEquiv
  · intro hM
    letI : Module.Invertible R M := hM
    refine (tensorLeft_isEquivalence_iff_exists_tensor_inverse M).2 ?_
    refine ⟨of R (Module.Dual R M), ?_, ?_⟩
    · exact ⟨(β_ M (of R (Module.Dual R M))) ≪≫ (Module.Invertible.linearEquiv R M).toModuleIso⟩
    · exact ⟨(Module.Invertible.linearEquiv R M).toModuleIso⟩

/-- The full subcategory of invertible `R`-modules, cut out by the chapter owner
`(tensorLeft M).IsEquivalence`. -/
def InvertibleSubcategory (R : Type u) [CommRing R] : Type (u + 1) :=
  ObjectProperty.FullSubcategory
    ((fun N : ModuleCat R ↦ (tensorLeft N).IsEquivalence) : ObjectProperty (ModuleCat R))

instance invertibleSubcategoryCategory (R : Type u) [CommRing R] :
    Category (InvertibleSubcategory R) := by
  dsimp [InvertibleSubcategory]
  infer_instance

/-- The core groupoid of invertible `R`-modules. -/
def InvertibleCore (R : Type u) [CommRing R] : Type (u + 1) :=
  CategoryTheory.Core (InvertibleSubcategory R)

instance invertibleCoreCategory (R : Type u) [CommRing R] :
    Category (InvertibleCore R) := by
  dsimp [InvertibleCore]
  infer_instance

end ModuleCat

/-! ### Lemma_15_118_2 (from Chap15) -/
open CategoryTheory MonoidalCategory

universe u

namespace ModuleCat

section

variable {R : Type u} [CommRing R]
variable (M : ModuleCat R)

/- Domain-style sampling for Lemma 15.118.2:
- primary domain: invertible modules and rank-one finite local freeness in `ModuleCat R`;
- sampled owner declarations:
  `Module.FiniteLocallyFreeOfRank R M 1`,
  `(tensorLeft M).IsEquivalence`,
  `tensorLeft_isEquivalence_iff_moduleInvertible`,
  `Module.Invertible.left`,
  `tensorLeft_isEquivalence_iff_exists_tensor_inverse`;
- best owner abstraction: the chapter-wide tensor-left equivalence owner `(tensorLeft M).IsEquivalence`;
- primitive vs. derived:
  the source-facing primitive clauses are rank-one finite local freeness and the one-sided
  tensor-unit witness `∃ N, M ⊗ N ≅ 𝟙`, while the chapter owner `(tensorLeft M).IsEquivalence`
  is the canonical core abstraction tying them together; the specialized predicate
  `Module.Invertible R M` and the two-sided tensor-inverse criterion are derived bridge/view API.

Source/core/bridge triage:
- `source-facing`: the rank-one finite-locally-free / invertible / tensor-inverse TFAE;
- `core/canonical`: `(tensorLeft M).IsEquivalence`;
- `bridge/view`: the module-specific predicate `Module.Invertible R M`, the passage from the
  one-sided tensor-unit witness to invertibility via `Module.Invertible.left`, and the Chapter
  `4` two-sided tensor-inverse comparison
  `tensorLeft_isEquivalence_iff_exists_tensor_inverse`.

Definition `15.118.1` already identifies the specialized mathlib predicate `Module.Invertible R M`
with the chapter owner `(tensorLeft M).IsEquivalence`, so the present source-facing TFAE keeps the
chapter owner itself and the genuinely source-facing one-sided tensor-unit condition. -/

-- Proof sketch: if `M` is finite locally free of rank `1`, take the dual module
-- `Module.Dual R M`; the evaluation pairing becomes an isomorphism after localizing on any open
-- where `M` is free of rank `1`, and Lemma `10.23.2` descends that isomorphism globally. If
-- `M ⊗ N ≅ R`, first promote that one-sided tensor-unit witness to `Module.Invertible R M` via
-- `Module.Invertible.left`, then use Definition `15.118.1` to reach the chapter owner
-- `(tensorLeft M).IsEquivalence`. Conversely, if `tensorLeft M` is an equivalence, apply the
-- Chapter `4` owner theorem `tensorLeft_isEquivalence_iff_exists_tensor_inverse` to obtain a
-- two-sided tensor inverse and then forget the second isomorphism; the resulting local tensor
-- trivializations recover finite local freeness of rank `1` by the finite-projective local
-- criterion.
/-- Lemma 15.118.2: for an `R`-module `M`, the following are equivalent: `M` is finite locally
free of rank `1`; tensoring on the left by `M` is an equivalence of `ModuleCat R`; and there
exists an `R`-module `N` such that `M ⊗ N` is isomorphic to the tensor unit in `ModuleCat R`.
The specialized predicate `Module.Invertible R M` remains only a bridge from
Definition `15.118.1`, while the public statement keeps the chapter owner
`(tensorLeft M).IsEquivalence` and the source-facing one-sided tensor-unit witness. -/
theorem invertible_tfae_finiteLocallyFreeOfRank_one_and_tensor_unit :
    List.TFAE
      [ Module.FiniteLocallyFreeOfRank R M 1
      , (tensorLeft M).IsEquivalence
      , ∃ N : ModuleCat R, Nonempty (M ⊗ N ≅ 𝟙_ _)
      ] := sorry

end

end ModuleCat

/-! ### Lemma_15_118_3 (from Chap15) -/
universe u

variable (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]

/- Domain-style sampling:
- primary domain: commutative algebra of class groups and Picard groups for domains with
  factorization hypotheses;
- sampled owner declarations:
  `ClassGroup.equivPic`,
  `instSubsingletonPicOfIsDomainOfNonemptyNormalizedGCDMonoid`,
  `UniqueFactorizationMonoid`,
  `subsingleton_classGroup`,
  `Module.Invertible.free_iff_linearEquiv`;
- best owner abstraction: the canonical owner is `CommRing.Pic R`, with the upstream triviality
  owner `instSubsingletonPicOfIsDomainOfNonemptyNormalizedGCDMonoid`;
- primitive vs. derived:
  triviality of the Picard group is already derived upstream from the more primitive canonical
  input `[Nonempty (NormalizedGCDMonoid R)]`; the UFD specialization is therefore source-level
  motivation, not new public data for this file.

Layer triage:
- `source-facing`: the Stacks lemma for unique factorization domains;
- `core/canonical`: the upstream `Subsingleton (CommRing.Pic R)` instance for domains admitting a
  normalized gcd structure, which already covers UFDs by typeclass inference;
- `bridge/view`: the specialization from `[UniqueFactorizationMonoid R]` to the upstream normalized
  gcd Picard-triviality instance, supplied entirely by typeclass inference.
-/

/- Lemma 15.118.3: a unique factorization domain has trivial Picard group. This source-facing
specialization is discharged by the canonical upstream Picard-triviality instance for normalized
gcd domains. -/
theorem subsingleton_picardGroup_of_uniqueFactorizationMonoid :
    Subsingleton (CommRing.Pic R)
  := inferInstance
