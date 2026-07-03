import LinearRepresentations_Serre_1977.Chap18.Proposition_18_18_1_2
import LinearRepresentations_Serre_1977.Chap17.Corollary_17_17_2_2
import LinearRepresentations_Serre_1977.Chap03.Theorem_3_3_3_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators Representation

universe u v x

namespace Representation

section

variable {p : ℕ}
variable {G : Type u} [Group G]

/-- The conjugate of a `p`-regular element of `G` that lies in `H`, viewed as a `p`-regular
element of `H`. -/
def conjPRegularInSubgroup (H : Subgroup G) (s : { t : G // IsPRegular p t }) (r : G)
    (hsr : r⁻¹ * s.1 * r ∈ H) : { t : H // IsPRegular p t } :=
  ⟨⟨r⁻¹ * s.1 * r, hsr⟩, by
    rw [IsPRegular, Subgroup.orderOf_mk]
    simpa using isPRegular_conj p s.1 r⁻¹ s.2⟩

end

section

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {A : Type v} [AddCommMonoid A]
variable {G : Type u} [Group G] [Finite G]

local instance subgroupMemDecidablePred (H : Subgroup G) : DecidablePred fun g : G ↦ g ∈ H :=
  Classical.decPred _

/-
Domain-style sampling:
* primary domain: induced character formulas for subgroup induction and their Brauer-character
  specialization on `p`-regular elements;
* relevant owner declarations in this domain:
  `Representation.character_eq_sum_over_representatives_of_equiv_induced`,
  `Representation.modularCharacter`,
  `Representation.FDRep.subgroupInduction`,
  and the Chapter 18 notation `φ[lift](ρ)`;
* best owner abstraction: Chapter 3's source-facing representative-sum theorem for induced
  characters, specialized through the Chapter 18 modular-character owner;
* source/core/bridge triage:
  source-facing: the representative-sum formula below for the Brauer character of `Ind_H^G(F)`;
  core/canonical: `Representation.modularCharacter` and
    `Representation.character_eq_sum_over_representatives_of_equiv_induced`;
  bridge/view: the bundled finite-dimensional induced owner `FDRep.subgroupInduction` and the
    subgroup-valued conjugation input `conjPRegularInSubgroup`.
* primitive data: a lift `lift : PrimeToPRoot p k → A`, subgroup `H`, finite-dimensional
  `H`-representation `F`, a representative set `R`, and a `p`-regular element `s`;
* derived API: the value of the modular character of the induced representation as the standard
  sum over left-coset representatives, with the summand evaluated at
  `conjPRegularInSubgroup H s r hsr`.
-/

-- Proof sketch: apply the characteristic-zero induced-character formula to the induced
-- representation, and identify each summand with the modular character of `F` on the corresponding
-- `p`-regular conjugate in `H`, with the sum indexed by left-coset representatives of `H`.
omit [Finite G] in
/-- Helper for Exercise 18-18.2-7: for the canonical scalar-valued lift, the modular character
agrees with the ordinary character on the `p`-regular locus. -/
private theorem modularCharacter_eq_character_of_scalarLift
    {V : Type x} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ : Representation k G V) (s : { t : G // IsPRegular p t }) :
    φ[(fun x : PrimeToPRoot p k ↦ ((x : kˣ) : k))](ρ) s = ρ.character s.1 := by
  classical
  -- Expand the ordinary character as the sum of the characteristic roots of `ρ s.1`.
  rw [Representation.character]
  rw [Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)]
  -- Each packaged prime-to-`p` root in the modular-character definition coerces back to the same
  -- scalar root in `k`.
  simp [Representation.modularCharacter, charpolyRoot_primeToPRoot_coe]

/-- Helper for Exercise 18-18.2-7: with the canonical scalar lift to `k`, subgroup induction
satisfies the same representative-sum formula as the ordinary character. -/
private theorem modularCharacter_subgroupInduction_eq_sum_over_representatives_scalarLift
    (H : Subgroup G)
    (F : FDRep k H)
    (R : Finset G) (hR : Subgroup.IsComplement (R : Set G) (H : Set G))
    (s : { t : G // IsPRegular p t }) :
    φ[(fun x : PrimeToPRoot p k ↦ ((x : kˣ) : k))]((FDRep.subgroupInduction F).ρ) s =
      ∑ r ∈ R,
        if hsr : r⁻¹ * s.1 * r ∈ H then
          φ[(fun x : PrimeToPRoot p k ↦ ((x : kˣ) : k))](F.ρ)
            (conjPRegularInSubgroup H s r hsr)
        else
          0 := by
  classical
  let e : Representation.Equiv ((FDRep.subgroupInduction F).ρ) (ind H.subtype F.ρ) := by
    -- `FDRep.subgroupInduction` is just the bundled owner of the standard induced model.
    simpa [FDRep.subgroupInduction] using
      (Representation.Equiv.refl (ind H.subtype F.ρ))
  -- Route correction: first reduce the scalar-valued modular character to the ordinary character,
  -- then invoke the Chapter `3` induced-character formula.
  calc
    φ[(fun x : PrimeToPRoot p k ↦ ((x : kˣ) : k))]((FDRep.subgroupInduction F).ρ) s =
        Representation.character ((FDRep.subgroupInduction F).ρ) s.1 := by
          simpa using
            modularCharacter_eq_character_of_scalarLift (ρ := (FDRep.subgroupInduction F).ρ) s
    _ = ∑ r ∈ R,
          if hsr : r⁻¹ * s.1 * r ∈ H then
            Representation.character F.ρ ⟨r⁻¹ * s.1 * r, hsr⟩
          else
            0 := by
          simpa using
            Representation.character_eq_sum_over_representatives_of_equiv_induced
              ((FDRep.subgroupInduction F).ρ) H F.ρ e R hR s.1
    _ = ∑ r ∈ R,
          if hsr : r⁻¹ * s.1 * r ∈ H then
            φ[(fun x : PrimeToPRoot p k ↦ ((x : kˣ) : k))](F.ρ)
              (conjPRegularInSubgroup H s r hsr)
          else
            0 := by
          -- Each subgroup summand is again a scalar-lift modular-character value.
          refine Finset.sum_congr rfl ?_
          intro r hr
          by_cases hsr : r⁻¹ * s.1 * r ∈ H
          · simpa [hsr] using
              (modularCharacter_eq_character_of_scalarLift
                (ρ := F.ρ) (s := conjPRegularInSubgroup H s r hsr)).symm
          · simp [hsr]

/-- Exercise 18-18.2-7: if `E = Ind_H^G(F)`, then for any finite set `R` of representatives of
the left cosets `G / H`, the modular character of `E` at a `p`-regular element of `G` is given
by the same representative sum as in the characteristic-zero induced-character formula.  This
source-facing Lean form uses the canonical scalar-valued lift of prime-to-`p` roots to `k`; an
arbitrary function `PrimeToPRoot p k → A` is too weak for the induced-cycle cancellation used in
LinearRepresentations_Serre_1977's proof. -/
theorem modularCharacter_subgroupInduction_eq_sum_over_representatives
    (H : Subgroup G)
    (F : FDRep k H)
    (R : Finset G) (hR : Subgroup.IsComplement (R : Set G) (H : Set G))
    (s : { t : G // IsPRegular p t }) :
    φ[(fun x : PrimeToPRoot p k ↦ ((x : kˣ) : k))]((FDRep.subgroupInduction F).ρ) s =
      ∑ r ∈ R,
        if hsr : r⁻¹ * s.1 * r ∈ H then
          φ[(fun x : PrimeToPRoot p k ↦ ((x : kˣ) : k))](F.ρ)
            (conjPRegularInSubgroup H s r hsr)
        else
          0 := by
  exact modularCharacter_subgroupInduction_eq_sum_over_representatives_scalarLift H F R hR s

end

end Representation
