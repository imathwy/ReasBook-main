import Mathlib
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_2_1.CharacterGrothendieck
import LinearRepresentations_Serre_1977.Chap12.Theorem_12_12_6_2

/-!
# Characteristic-zero Brauer induction in the Grothendieck group

Serre's Theorem 27 (`gammaElementarySubgroupInductionOverField_surjective`) states that the unit of
the character ring `R[K](G)` is a sum of characters induced from `Γ_K`-elementary subgroups.  This
file transports that statement to the Grothendieck group `R₀[K](G)` over a characteristic-zero
field `K = ↥K` (an intermediate field of a cyclotomic extension), using the family-free additive
equivalence `ch : R₀[K] ≃+ R[K]` (`finiteRepGrothendieckCharacterAddEquiv'`) which commutes with
subgroup induction (`finiteRepGrothendieckCharacter_subgroupInduction`) and sends `1` to `1`.

The result `one_eq_sum_gammaElementary_finiteRepGrothendieckInduction` is step 1 of the proof of
Theorem 17-17.2-1: `1_{R₀[K]} = ∑_H Ind_H(z_H)` over `Γ_K`-elementary subgroups `H`.
-/

noncomputable section

universe u

open scoped Representation

namespace Representation

variable {G : Type u} [Group G] [Finite G]
variable {L : Type u} [Field L] [NumberField L] [IsCyclotomicExtension {Monoid.exponent G} ℚ L]
variable (K : IntermediateField ℚ L)

local instance instDecEqGammaElem_czb :
    DecidableEq { H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H } :=
  Classical.decEq _
local instance instDecNeR0K_czb (i : { H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H })
    (x : R₀[↥K](i.1)) : Decidable (x ≠ 0) := Classical.dec _

/-- Step 1 of Theorem 17-17.2-1: over the characteristic-zero field `↥K`, the unit class of
`R₀[K](G)` is a finite sum of classes induced from `Γ_K`-elementary subgroups.  This is the
Grothendieck-group form of Serre's Theorem 27, obtained by transporting the character-ring statement
through the additive equivalence `ch : R₀[↥K] ≃+ R[↥K]`. -/
theorem one_eq_sum_gammaElementary_finiteRepGrothendieckInduction :
    ∃ z : Π₀ H : {H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H}, R₀[↥K](H.1),
      (1 : R₀[↥K](G))
        = z.sum (fun H => ⇑(Representation.Subgroup.finiteRepGrothendieckGroupInduction (↥K) H.1)) := by
  classical
  obtain ⟨χ, hχ⟩ :=
    gammaElementarySubgroupInductionOverField_surjective (K := K) (G := G) (L := L) 1
  set e : ∀ H : {H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H},
      R₀[↥K](H.1) ≃+ R[↥K](H.1) := fun H => finiteRepGrothendieckCharacterAddEquiv' with he
  let Ind₀ : (Π₀ H : {H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H}, R₀[↥K](H.1))
      →+ R₀[↥K](G) :=
    DFinsupp.sumAddHom (fun H => Representation.Subgroup.finiteRepGrothendieckGroupInduction (↥K) H.1)
  -- The commuting square `ch ∘ Ind₀ = (γ-induction) ∘ (componentwise ch)`, checked on `single`s.
  have sq : (finiteRepGrothendieckCharacter (↥K) G).comp Ind₀
      = (gammaElementarySubgroupInductionOverField (K := K) (Γ[K](G))).toAddMonoidHom.comp
          (DFinsupp.mapRange.addMonoidHom (fun H => (e H).toAddMonoidHom)) := by
    refine DFinsupp.addHom_ext (fun H c => ?_)
    simp only [AddMonoidHom.comp_apply, Ind₀, DFinsupp.sumAddHom_single,
      DFinsupp.mapRange.addMonoidHom_apply, DFinsupp.mapRange_single,
      LinearMap.toAddMonoidHom_coe, gammaElementarySubgroupInductionOverField_single]
    rw [finiteRepGrothendieckCharacter_subgroupInduction]
    rfl
  refine ⟨DFinsupp.mapRange (fun H => (e H).symm) (fun H => (e H).symm.map_zero) χ, ?_⟩
  apply (finiteRepGrothendieckCharacter_bijective' (K := ↥K) (G := G)).1
  rw [finiteRepGrothendieckCharacter_one]
  rw [(DFinsupp.sumAddHom_apply _ _).symm]
  have := congrFun (congrArg (fun f : _ →+ _ => f.toFun)
    sq) (DFinsupp.mapRange (fun H => (e H).symm) (fun H => (e H).symm.map_zero) χ)
  simp only [AddMonoidHom.comp_apply] at this
  rw [show (finiteRepGrothendieckCharacter (↥K) G)
        (Ind₀ (DFinsupp.mapRange (fun H => (e H).symm) (fun H => (e H).symm.map_zero) χ))
      = gammaElementarySubgroupInductionOverField (K := K) (Γ[K](G))
          (DFinsupp.mapRange.addMonoidHom (fun H => (e H).toAddMonoidHom)
            (DFinsupp.mapRange (fun H => (e H).symm) (fun H => (e H).symm.map_zero) χ)) from this]
  rw [show DFinsupp.mapRange.addMonoidHom (fun H => (e H).toAddMonoidHom)
        (DFinsupp.mapRange (fun H => (e H).symm) (fun H => (e H).symm.map_zero) χ) = χ from ?_]
  · exact hχ.symm
  · refine DFinsupp.ext fun H => ?_
    rw [DFinsupp.mapRange.addMonoidHom_apply, DFinsupp.mapRange_apply, DFinsupp.mapRange_apply]
    exact (e H).apply_symm_apply (χ H)

end Representation
