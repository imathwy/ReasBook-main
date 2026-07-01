import Mathlib
import Serre.Chap12.Theorem_12_12_6_2
import Serre.Chap17.Corollary_17_17_2_2.ElementarySubgroupInduction

open scoped Representation

noncomputable section

universe u v

namespace Representation

section

variable {G : Type u} [Group G] [Finite G]

/-
Domain-style sampling:
* Primary domain: subgroup induction on Grothendieck groups of modular representations indexed by
  the family of `Γ_K`-elementary subgroups.
* Relevant owner declarations inspected in this domain:
  `Representation.gammaElementarySubgroupInductionOverField`,
  `Representation.gammaElementarySubgroupInductionOverField_surjective`,
  `Representation.Subgroup.finiteRepGrothendieckGroupInduction`,
  `Representation.Subgroup.finiteProjectiveGroupAlgebraGrothendieckGroupInduction`,
  and the scoped theorem-surface notation `Ind[H]` from
  `FiniteRepGrothendieckInduction` / `FiniteProjectiveGrothendieckInduction`.
* Best owner abstraction: the subgroup-level induction maps in `Representation.Subgroup`, exposed
  on the theorem surface through the scoped owner notation `Ind[H]`.
* Source/core/bridge triage:
  source-facing: Theorem `17-17.2-1`, the modular Brauer-induction existence statements for the
    arithmetic subgroup `Γ[K](G)`;
  core/canonical: the subgroup-level Grothendieck-group induction owners from
    `Serre.Chap17.Corollary_17_17_2_2`, together with the characteristic-zero owner
    `Representation.gammaElementarySubgroupInductionOverField`;
  bridge/view: no additional public bundled owner is introduced here.
* Primitive data: the subgroup induction maps on `R₀[k](H)` and `P₀[k](H)`.
* Derived API: the source-facing decomposition of an arbitrary modular class as a finite sum of
  inductions from genuine `Γ[K](G)`-elementary subgroups.
-/

local instance
    (ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ) :
    DecidableEq { H : Subgroup G // Subgroup.IsGammaElementary ΓK H } :=
  Classical.decEq _

-- Proof sketch: this is the modular Brauer-induction statement obtained by descending the
-- characteristic-zero `Γ_K`-elementary induction formula through the decomposition homomorphism.
-- The resulting image contains the unit class of `R_k(G)`, and multiplying by an arbitrary class
-- shows every element of `R_k(G)` is a finite sum of inductions from `Γ_K`-elementary subgroups.
section

variable {k : Type u} [Field k]
variable {L : Type v} [Field L] [NumberField L]
variable [IsCyclotomicExtension {Monoid.exponent G} ℚ L]
variable (k) (K : IntermediateField ℚ L)

section

open scoped FiniteRepGrothendieckInduction

/-- Theorem 17-17.2-1 (1): with `Γ_K = Γ[K](G) ⊆ (ℤ / mℤ)ˣ` attached to the intermediate field
`K ⊆ L` in a cyclotomic realization of the exponent of `G`, the
class `x ∈ R_k(G)` is a finite sum of inductions from `Γ_K`-elementary subgroups of `G`,
with coefficients in the corresponding Grothendieck groups `R_k(H)`. -/
theorem gammaElementarySubgroupFiniteRepGrothendieckInduction_surjective
    (x : R₀[k](G)) :
    ∃ (ι : Type x) (_ : Fintype ι) (H : ι → Subgroup G)
      (hH : ∀ i, Subgroup.IsGammaElementary (Γ[K](G)) (H i)),
        ∃ y : ∀ i, R₀[k](H i),
          x = ∑ i, (Ind[H i]) (y i) := sorry

end

-- Proof sketch: apply the same descent argument to the projective Grothendieck groups. The
-- decomposition map commutes with induction and multiplication, so once the unit class of
-- `P_k(G)` is written as a sum of induced projective classes, multiplying by any projective class
-- yields a decomposition of that class by inductions from `Γ_K`-elementary subgroups.
section

variable {k : Type u} [Field k]
variable {L : Type v} [Field L] [NumberField L]
variable [IsCyclotomicExtension {Monoid.exponent G} ℚ L]
variable (k) (K : IntermediateField ℚ L)

section

open scoped FiniteProjectiveGrothendieckInduction

/-- Theorem 17-17.2-1 (2): with `Γ_K = Γ[K](G) ⊆ (ℤ / mℤ)ˣ` attached to the intermediate field
`K ⊆ L` in a cyclotomic realization of the exponent of `G`, the
class `x ∈ P_k(G)` is a finite sum of inductions from `Γ_K`-elementary subgroups of `G`,
with coefficients in the corresponding projective Grothendieck groups `P_k(H)`. -/
theorem gammaElementarySubgroupFiniteProjectiveRepGrothendieckInduction_surjective
    (x : P₀[k](G)) :
    ∃ (ι : Type x) (_ : Fintype ι) (H : ι → Subgroup G)
      (hH : ∀ i, Subgroup.IsGammaElementary (Γ[K](G)) (H i)),
        ∃ y : ∀ i, P₀[k](H i),
          x = ∑ i, (Ind[H i]) (y i) := sorry

end

end

end

end

end Representation
