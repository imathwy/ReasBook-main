import Mathlib
import LinearRepresentations_Serre_1977.Chap14.Proposition_14_14_1_1
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_4_3
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_3_1
import LinearRepresentations_Serre_1977.Chap15.Theorem_15_15_2_2
import LinearRepresentations_Serre_1977.Chap16.Lemma_16_16_3_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Representation

namespace Representation

section

variable {K : Type u} [Field K]
variable {G : Type u} [Group G]

/- Domain-style sampling for Proposition 16-16.3-3:
* primary domain: Grothendieck groups in modular representation theory, with actual
  finite-dimensional and finite-projective representation classes tracked through scalar extension
  and reduction;
* relevant owner declarations inspected in this domain:
  `finiteRepGrothendieckClass`,
  `projectivePositiveSubset`,
  `projectiveGrothendieckScalarExtensionHom`,
  `decompositionHom`;
* best owner abstraction: the canonical additive homomorphisms on Grothendieck groups, with this
  file owning only the source-facing actual subset `R⁺[K](G)` and condition `(R)`;
* primitive data: actual finite-dimensional `K[G]`-representations through
  `finiteRepGrothendieckClass`;
* derived API: the bridge theorem identifying the source-facing image `e '' P⁺[k](G)` with the
  canonical range owner `e.range` intersected with `R⁺[K](G)`.

Source/core/bridge triage:
* source-facing: `R⁺[K](G)` and `SatisfiesConditionR`;
* core/canonical: `projectiveGrothendieckScalarExtensionHom` and `decompositionHom`;
* bridge/view: Proposition `16-16.3-3`, which compares the source-facing positive projective image
  with the canonical scalar-extension range inside `R₀[K](G)`.
-/

section FiniteRepPositiveSubset

/-- LinearRepresentations_Serre_1977's actual positive subset `R_K^+(G)`, written here as `R⁺[K](G)`, consists of the classes
in `R_K(G)` represented by actual finite-dimensional `K[G]`-representations. -/
def finiteRepPositiveSubset
    (K : Type u) [Field K] (G : Type u) [Group G] :
    Set (R₀[K](G)) :=
  Set.range (finiteRepGrothendieckClass K G)

scoped[Representation] notation:max "R⁺[" K "](" G ")" =>
  finiteRepPositiveSubset K G

/-- Membership in `R_K^+(G)` means being the class of some actual finite-dimensional
`K[G]`-representation. -/
@[simp] theorem mem_finiteRepPositiveSubset_iff
    {x : R₀[K](G)} :
    x ∈ R⁺[K](G) ↔
      ∃ V : FDRep K G, [V]₀ = x :=
  Iff.rfl

end FiniteRepPositiveSubset

variable [Finite G]

/-- LinearRepresentations_Serre_1977's condition `(R)` for a subset `RKplus ⊆ R_K(G)` is the existence of a finite local
overring `A'` of `A` with fraction field `K'`, such that the scalar-extension map
`R_K(G) → R_K'(G)` identifies `RKplus` with the preimage of the actual positive cone in
`R_K'(G)`, and the decomposition map `R_K'(G) → R_k'(G)` sends that actual positive cone onto the
actual positive cone over the residue field `k' = IsLocalRing.ResidueField A'`. -/
def SatisfiesConditionR
    (RKplus : Set (R₀[K](G))) (A : Type u) [CommRing A] [IsLocalRing A]
    [Algebra A K] [IsFractionRing A K] : Prop :=
  ∃ (A' : Type u) (_ : CommRing A') (_ : IsLocalRing A') (_ : Algebra A A')
      (_ : Module.Finite A A') (K' : Type u) (_ : Field K') (_ : Algebra A' K')
      (_ : Algebra A K') (_ : IsFractionRing A' K') (_ : Algebra K K')
      (_ : IsScalarTower A A' K') (_ : IsScalarTower A K K')
      (_ : FiniteDimensional K K'),
    RKplus = (finiteRepGrothendieckScalarExtensionHom K K' G) ⁻¹' R⁺[K'](G) ∧
      decompositionHom A' K' G '' R⁺[K'](G) = R⁺[IsLocalRing.ResidueField A'](G)

variable {A : Type u} [CommRing A] [IsLocalRing A] [Algebra A K] [IsFractionRing A K]

local notation "k" => IsLocalRing.ResidueField A
local notation "e" =>
  (projectiveGrothendieckScalarExtensionHom A K : P₀[k](G) →+ R₀[K](G))

-- Proof sketch: use Proposition `16-16.3-2` to descend positive projective classes from a finite
-- extension satisfying condition `(R)`. Through the canonical reduction equivalence
-- `P_A(G) ≃ P_k(G)`, this identifies the image of the source-facing positive subset `P_k^+(G)`
-- under LinearRepresentations_Serre_1977's scalar-extension owner `e` with the intersection of the full scalar-extension
-- range of `e` and the actual positive subset `R⁺[K](G)`.
/-- Proposition 16-16.3-3: if condition `(R)` holds for the positive subset `R_K^+(G)`, then the
image of the source-facing positive subset `P_k^+(G)`, under LinearRepresentations_Serre_1977's canonical scalar-extension
homomorphism `e : P_k(G) → R_K(G)`, is exactly the intersection of the range of `e` with
`R_K^+(G)`. Here `k = IsLocalRing.ResidueField A`. -/
theorem SatisfiesConditionR.image_eq_range_inter_positive
    (hR : SatisfiesConditionR (R⁺[K](G)) A) :
    e '' P⁺[k](G) =
      ((e).range : Set (R₀[K](G))) ∩ R⁺[K](G) := sorry

end

end Representation
