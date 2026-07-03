import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_17_17_2_2 (from Chap17) -/
open IsCyclotomicExtension.Rat
open scoped Representation

noncomputable section

universe u w

namespace Representation

section ModularBrauerCorollary

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {G : Type u} [Group G] [Finite G]

local notation "k" => IsLocalRing.ResidueField A
local notation "Lexp" => CyclotomicField (Monoid.exponent G) ℚ
local instance : NumberField Lexp := inferInstance
local instance : IsCyclotomicExtension {Monoid.exponent G} ℚ Lexp :=
  CyclotomicField.isCyclotomicExtension (n := Monoid.exponent G) (K := ℚ)

section

open scoped FiniteRepGrothendieckInduction

/-- Helper for Corollary 17-17.2-2: for the trivial arithmetic subgroup `Γ = ⊥`, LinearRepresentations_Serre_1977's
`Γ`-elementary subgroups are exactly the ordinary elementary subgroups. -/
theorem Subgroup.isGammaElementary_bot_iff_isElementary
    (H : Subgroup G) :
    Subgroup.IsGammaElementary (⊥ : Subgroup (ZMod (Monoid.exponent G))ˣ) H ↔
      IsElementary H := by
  constructor
  · intro hH
    rcases hH with ⟨p, hp⟩
    -- Reduce the `Γ = ⊥` notion prime by prime to the Chapter `10` elementary notion.
    exact ⟨p, (Subgroup.IsGammaPElementary.bot_iff_isPElementary p H).1 hp⟩
  · intro hH
    rcases hH with ⟨p, hp⟩
    -- Repackage the ordinary elementary witness as a trivial-`Γ` witness.
    exact ⟨p, (Subgroup.IsGammaPElementary.bot_iff_isPElementary p H).2 hp⟩

/-- Helper for Corollary 17-17.2-2: at the full cyclotomic field, LinearRepresentations_Serre_1977's arithmetic subgroup is
trivial. -/
theorem gammaSubgroup_top_eq_bot :
    Γ[(⊤ : IntermediateField ℚ Lexp)](G) =
      (⊥ : Subgroup (ZMod (Monoid.exponent G))ˣ) := by
  -- Unfold `Γ[K](G)` once; the top intermediate field has trivial fixing subgroup.
  unfold Representation.gammaSubgroup
  rw [IntermediateField.fixingSubgroup_top]
  simpa using OrderIso.map_bot (galEquivZMod (Monoid.exponent G) Lexp).mapSubgroup

-- Proof sketch: specialize Theorem `17-17.2-1` to the cyclotomic top field, where
-- `Γ[(⊤)](G) = ⊥`, and then rewrite `Γ`-elementary subgroups as ordinary elementary subgroups.
/-- Corollary 17-17.2-2 (1): if `K` is sufficiently large, every element of `R_k(G)` is a finite
sum of classes induced from elementary subgroups of `G`, where the summands lie in the
corresponding Grothendieck groups `R_k(H)`. Here `k = IsLocalRing.ResidueField A`. -/
theorem residueField_grothendieckClass_exists_sum_of_elementary_subgroup_inductions
    (K : Type w) [Field K] [CharZero K] [Algebra A K] [IsFractionRing A K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (x : R₀[k](G)) :
    ∃ (ι : Type x) (_ : Fintype ι) (H : ι → Subgroup G)
      (hH : ∀ i, IsElementary (H i)),
        ∃ y : ∀ i, R₀[k](H i),
          x = ∑ i, (Ind[H i]) (y i) := by
  -- Route correction: the source proof specializes the already-built `Γ[K](G)` statement to the
  -- top cyclotomic field and only then rewrites `Γ[(⊤)](G)` to `⊥`.
  rcases gammaElementarySubgroupFiniteRepGrothendieckInduction_surjective
      (G := G) (L := Lexp) k (⊤ : IntermediateField ℚ Lexp) x with
    ⟨ι, hι, H, hHΓ, y, hx⟩
  refine ⟨ι, hι, H, ?_, y, hx⟩
  intro i
  -- The top-field specialization makes the LinearRepresentations_Serre_1977 subgroup trivial, so the subgroup is ordinary
  -- elementary.
  exact
    (Subgroup.isGammaElementary_bot_iff_isElementary (G := G) (H i)).1 <|
      by simpa [gammaSubgroup_top_eq_bot (G := G)] using hHΓ i

end

section

open scoped FiniteProjectiveGrothendieckInduction

-- Proof sketch: the projective statement is identical to the ordinary one, using the projective
-- surjectivity theorem from Theorem `17-17.2-1`.
/-- Corollary 17-17.2-2 (2): if `K` is sufficiently large, every element of `P_k(G)` is a finite
sum of classes induced from elementary subgroups of `G`, where the summands lie in the
corresponding projective Grothendieck groups `P_k(H)`. Here `k = IsLocalRing.ResidueField A`. -/
theorem residueField_projectiveGrothendieckClass_exists_sum_of_elementary_subgroup_inductions
    (K : Type w) [Field K] [CharZero K] [Algebra A K] [IsFractionRing A K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (x : P₀[k](G)) :
    ∃ (ι : Type x) (_ : Fintype ι) (H : ι → Subgroup G)
      (hH : ∀ i, IsElementary (H i)),
        ∃ y : ∀ i, P₀[k](H i),
          x = ∑ i, (Ind[H i]) (y i) := by
  -- Route correction: reuse the same top-field specialization as in the ordinary Grothendieck
  -- case, now with the projective induction theorem.
  rcases gammaElementarySubgroupFiniteProjectiveRepGrothendieckInduction_surjective
      (G := G) (L := Lexp) k (⊤ : IntermediateField ℚ Lexp) x with
    ⟨ι, hι, H, hHΓ, y, hx⟩
  refine ⟨ι, hι, H, ?_, y, hx⟩
  intro i
  -- Again, the specialized arithmetic subgroup is trivial, so the subgroup is ordinary
  -- elementary.
  exact
    (Subgroup.isGammaElementary_bot_iff_isElementary (G := G) (H i)).1 <|
      by simpa [gammaSubgroup_top_eq_bot (G := G)] using hHΓ i

end

end ModularBrauerCorollary

end Representation

/-! ### Remark_17_17_2_3 (from Chap17) -/
/- Domain-style sampling for this item:
* primary domain: subgroup induction on Grothendieck groups of finite-dimensional and finite
  projective modular representations.
* relevant owner declarations inspected in the same domain:
  `Representation.FDRep.subgroupInduction`,
  `Representation.Subgroup.finiteRepGrothendieckGroupInduction`,
  `Representation.FiniteProjectiveGroupAlgebraModule.subgroupInduction`,
  `Representation.Subgroup.finiteProjectiveGroupAlgebraGrothendieckGroupInduction`.

Primitive data vs derived API:
* the primitive construction is subgroup induction on representations/modules;
* the Grothendieck-group induction maps are the derived owner-level API already defined upstream in
  `Corollary_17_17_2_2`;
* this remark contributes no new source-facing object, map, or proposition beyond that existing
  owner API.

Source/core/bridge triage:
* source-facing: Remark `17-17.2-3` is explanatory prose about the reach of the modular
  Brauer-induction argument;
* core/canonical: the chapter owner declarations are the two subgroup-induction homomorphisms in
  `Representation.Subgroup`;
* bridge/view: this file should therefore stay a direct recall of those owners rather than
  introducing a parallel local wrapper or alias. -/
/- Remark 17-17.2-3: the argument used in the proof of Theorem `39` applies in many other
situations and, in particular, leads to the modular analogue of Artin's theorem developed next.
For the chapter/project API, the relevant source-facing owner already is the subgroup-induction
homomorphism on finite-dimensional modular Grothendieck groups; this remark adds no new local
declaration beyond recalling that canonical map. -/
recall Representation.Subgroup.finiteRepGrothendieckGroupInduction

/- The projective induction map is likewise already owned upstream in
`Representation.Subgroup`; the following modular Artin-induction theorem uses its rationalized
direct-sum form, not a remark-specific duplicate. -/
recall Representation.Subgroup.finiteProjectiveGroupAlgebraGrothendieckGroupInduction

/-! ### Theorem_17_17_2_1 (from Chap17) -/
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
    `LinearRepresentations_Serre_1977.Chap17.Corollary_17_17_2_2`, together with the characteristic-zero owner
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
