import Mathlib
import LinearRepresentations_Serre_1977.Chap02.Corollary_2_2_4_3
import LinearRepresentations_Serre_1977.Chap02.Remark_2_2_4_4
import LinearRepresentations_Serre_1977.Chap08.Proposition_8_8_2_1.CharacterPacketCore
import LinearRepresentations_Serre_1977.Chap08.Proposition_8_8_2_1.InductionBridge
import LinearRepresentations_Serre_1977.Chap08.Proposition_8_8_2_1.RestrictionBridge
import LinearRepresentations_Serre_1977.Chap08.Proposition_8_8_2_1.MackeyWeights
import LinearRepresentations_Serre_1977.Chap08.Proposition_8_8_2_1.CharacterWeightBridge
import LinearRepresentations_Serre_1977.Chap07.Proposition_7_7_2_1
import LinearRepresentations_Serre_1977.Chap07.Proposition_7_7_4_1
import LinearRepresentations_Serre_1977.Chap07.Exercise_7_7_2_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped BigOperators Representation SubgroupInduction

universe w x

namespace Representation

noncomputable section

section SemidirectAbelian

variable {A : Type} [CommGroup A]
variable {H : Type} [Group H]
variable (φ : H →* MulAut A)

attribute [local instance] Fintype.ofFinite

namespace FDRep

/-- Helper for Exercise 8-8.2-2: bundle Serre's packet `θ[φ; χ, ρ]` as a finite-dimensional
representation so Chapter 2's complete-family API can read its degree and simplicity. -/
noncomputable abbrev theta [Finite H]
    (φ : H →* MulAut A) (χ : A →* ℂˣ) (ρ : FDRep ℂ H_[φ; χ]) :
    FDRep ℂ (A ⋊[φ] H) :=
  FDRep.of (Representation.theta φ χ (Rep.of ρ.ρ)).ρ

end FDRep

/-- Helper for Exercise 8-8.2-2: a semidirect product of finite groups is finite. -/
private theorem semidirectProduct_finite [Finite A] [Finite H] :
    Finite (A ⋊[φ] H) := by
  letI : Fintype A := Fintype.ofFinite A
  letI : Fintype H := Fintype.ofFinite H
  let eprod : A ⋊[φ] H ≃ A × H :=
    { toFun := fun x ↦ (x.1, x.2)
      invFun := fun p ↦ ⟨p.1, p.2⟩
      left_inv := by
        intro x
        cases x
        rfl
      right_inv := by
        intro p
        cases p
        rfl }
  letI : Fintype (A ⋊[φ] H) := Fintype.ofEquiv (A × H) eprod.symm
  exact inferInstance

/-- Helper for Exercise 8-8.2-2: the semidirect product cardinal is nonzero when viewed in `ℂ`. -/
private theorem semidirect_product_card_ne_zero_complex [Finite A] [Finite H] :
    NeZero (Nat.card (A ⋊[φ] H) : ℂ) := by
  let _ : Finite (A ⋊[φ] H) := semidirectProduct_finite (φ := φ)
  exact ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩

/-- Helper for Exercise 8-8.2-2: the subgroup-side packet source already satisfies the two
inputs of Serre's reverse Mackey criterion. -/
private theorem theta_reverse_mackey_hypothesis [Finite A] [Finite H]
    (χ : A →* ℂˣ) (ρ : Rep.{w} ℂ H_[φ; χ]) [ρ.ρ.IsIrreducible] :
    Representation.IsIrreducible (theta_packet_source (φ := φ) χ ρ).ρ ∧
      (∀ s ∉ character_stabilizer_subgroup (φ := φ) χ,
        ∀ f :
          localMackeyTwist (φ := φ)
              (character_stabilizer_subgroup (φ := φ) χ)
              (character_stabilizer_subgroup (φ := φ) χ)
              (theta_packet_source (φ := φ) χ ρ) s ⟶
            Rep.res
              (localMackeySubgroup (φ := φ)
                (character_stabilizer_subgroup (φ := φ) χ)
                (character_stabilizer_subgroup (φ := φ) χ) s).subtype
              (theta_packet_source (φ := φ) χ ρ),
          f = 0) := by
  constructor
  · -- The explicit subgroup model of the packet source is irreducible before induction.
    simpa [theta_packet_source] using
      character_stabilizer_subgroup_source_isIrreducible (φ := φ) χ ρ
  · intro s hs f
    -- Away from the stabilizer subgroup, the Mackey weight mismatch kills every intertwiner.
    exact theta_local_mackey_disjoint (φ := φ) (χ := χ) (ρ := ρ) hs f

/-- Helper for Exercise 8-8.2-2: the explicit induced subgroup model in Serre's proof is
irreducible by the reverse direction of Mackey's criterion. -/
private theorem theta_packet_induction_model_isIrreducible [Finite A] [Finite H]
    (χ : A →* ℂˣ) (ρ : Rep.{w} ℂ H_[φ; χ]) [ρ.ρ.IsIrreducible] :
    (Rep.ind
      (character_stabilizer_subgroup (φ := φ) χ).subtype
      (theta_packet_source (φ := φ) χ ρ)).ρ.IsIrreducible := by
  let _ : Finite (A ⋊[φ] H) := semidirectProduct_finite (φ := φ)
  let _ : NeZero (Nat.card (A ⋊[φ] H) : ℂ) :=
    semidirect_product_card_ne_zero_complex (φ := φ)
  -- Feed the packet source irreducibility and the off-subgroup Mackey vanishing into the
  -- Chapter 7 reverse Mackey criterion.
  refine
    (ind_isIrreducible_iff_isIrreducible_and_mackey_disjoint
      (k := ℂ)
      (G := A ⋊[φ] H)
      (H := character_stabilizer_subgroup (φ := φ) χ)
      (ρ := (theta_packet_source (φ := φ) χ ρ).ρ)).2 ?_
  simpa [localMackeySubgroup, localMackeyTwist] using
    theta_reverse_mackey_hypothesis (φ := φ) χ ρ

/-- Helper for Exercise 8-8.2-2: once the explicit induced packet model is irreducible, the
canonical equivalence with `θ[φ; χ, ρ]` transports irreducibility back to the packet itself. -/
private theorem theta_isIrreducible_of_induction_model_local [Finite H]
    (χ : A →* ℂˣ) (ρ : Rep.{w} ℂ H_[φ; χ])
    (hInd :
      (Rep.ind
        (character_stabilizer_subgroup (φ := φ) χ).subtype
        (theta_packet_source (φ := φ) χ ρ)).ρ.IsIrreducible) :
    (Representation.theta φ χ ρ).ρ.IsIrreducible := by
  letI :
      (Rep.ind
        (character_stabilizer_subgroup (φ := φ) χ).subtype
        (theta_packet_source (φ := φ) χ ρ)).ρ.IsIrreducible :=
    hInd
  -- Transport irreducibility across the canonical `θ ≃ Ind` comparison.
  exact
    isIrreducible_of_nonempty_equiv
      (ρ := (Rep.ind
        (character_stabilizer_subgroup (φ := φ) χ).subtype
        (theta_packet_source (φ := φ) χ ρ)).ρ)
      (σ := (Representation.theta φ χ ρ).ρ)
      ⟨(theta_equiv_ind_character_stabilizer_subgroup (φ := φ) χ ρ).symm⟩

/-- Helper for Exercise 8-8.2-2: in the finite-`A` situation of the exercise, Serre's Mackey criterion
proves that the little-groups packet `θ[φ; χ, ρ]` is irreducible. -/
theorem theta_isIrreducible [Finite A] [Finite H]
    (χ : A →* ℂˣ) (ρ : Rep.{w} ℂ H_[φ; χ]) [ρ.ρ.IsIrreducible] :
    (Representation.theta φ χ ρ).ρ.IsIrreducible := by
  -- Route correction: the compiled Chapter 7 criterion is now available, so we follow Serre's
  -- original route directly on the explicit packet subgroup instead of rebuilding a parallel API.
  have hInd :
      (Rep.ind
        (character_stabilizer_subgroup (φ := φ) χ).subtype
        (theta_packet_source (φ := φ) χ ρ)).ρ.IsIrreducible :=
    theta_packet_induction_model_isIrreducible (φ := φ) χ ρ
  -- Transport irreducibility from the induced subgroup model back to the packet `θ[φ; χ, ρ]`.
  exact theta_isIrreducible_of_induction_model_local (φ := φ) χ ρ hInd

/-- Helper for Exercise 8-8.2-2: Serre's Mackey-criterion proof already closes the packet
irreducibility statement when the normal factor `A` is finite, so the ambient semidirect product
is itself finite. -/
private theorem theta_irreducible_of_finite_normal_factor [Finite A] [Finite H]
    (χ : A →* ℂˣ) (ρ : Rep.{w} ℂ H_[φ; χ]) [ρ.ρ.IsIrreducible] :
    (Representation.theta φ χ ρ).ρ.IsIrreducible := by
  -- This local wrapper keeps the later exercise proofs on the already-established finite-group
  -- route without repeating the transport step.
  exact theta_isIrreducible (φ := φ) χ ρ

/-
Source/core/bridge triage for Exercise 8-8.2-2:
* `source-facing`: the orbit-count and square-degree identities for Serre's little-groups
  construction, and the resulting completeness of the induced family on `A ⋊[φ] H`.
* `core/canonical`: `HasCharacterOrbitRepresentatives`, `FDRep.theta`,
  `IsCompleteIrreducibleFamily`, `sum_sq_degree_eq_card_of_complete_irreducible_family`, and
  `complete_irreducible_family_iff_sum_sq_degree_eq_card`.
* `bridge/view`: `Representation.theta` is the unbundled owner, while `FDRep.theta` is the
  finite-dimensional view needed by the Chapter 2 complete-family owner API.

Primitive data versus derived API: the public input is the orbit-representative family `χ` and,
for each stabilizer, a complete pairwise nonisomorphic irreducible family `ρ`. The finite indexing
needed for the displayed sums is operational data derived from the owner hypotheses, so the theorem
surfaces should stay in the owner-style `∑'` form rather than exposing proof-only finite-sum
bookkeeping.

Sampled owner declarations in this domain:
* `HasCharacterOrbitRepresentatives.finiteIndex`
* `FDRep.theta`
* `IsCompleteIrreducibleFamily.finite_index`
* `sum_sq_degree_eq_card_of_complete_irreducible_family`
* `complete_irreducible_family_iff_sum_sq_degree_eq_card`
-/

section

variable [Finite A]
variable {ι : Type w}

-- Proof sketch: apply the class formula to the `H`-action on the linear characters of `A`, using
-- the chosen orbit representatives `χ i`; the orbit stabilizer of `χ i` is exactly
-- `H_[φ; χ i]`.
/-- Exercise 8-8.2-2 (1): if `χ : ι → (A →* ℂˣ)` is a complete set of
representatives for the `H`-orbits in the character group of `A`, then the
cardinality of that character group is the sum of the subgroup indices
`[H : H_[φ; χ_i]]`. -/
theorem card_character_eq_sum_characterStabilizer_index_of_orbit_representatives
    (χ : ι → A →* ℂˣ) (hχ : HasCharacterOrbitRepresentatives φ χ) :
    Nat.card (A →* ℂˣ) =
      ∑' i : ι, (H_[φ; χ i]).index := by
  classical
  let _ : MulAction H A := MulAction.compHom A φ
  let _ : MulDistribMulAction H A := MulDistribMulAction.compHom A φ
  let _ : MulAction Hᵈᵐᵃ (A →* ℂˣ) := inferInstance
  let _ : MulAction H (A →* ℂˣ) :=
    MulAction.compHom (A →* ℂˣ) (show H →* Hᵈᵐᵃ from (MulEquiv.inv' H).toMonoidHom)
  let _ : Finite ι := HasCharacterOrbitRepresentatives.finiteIndex φ hχ
  have hχ_bijective : Function.Bijective
      (fun i ↦ (Quotient.mk'' (χ i) : MulAction.orbitRel.Quotient H (A →* ℂˣ))) := by
    -- Unfold the orbit-representative owner to recover the quotient parametrization.
    simpa [HasCharacterOrbitRepresentatives] using hχ
  let eχ : ι ≃ MulAction.orbitRel.Quotient H (A →* ℂˣ) := Equiv.ofBijective _ hχ_bijective
  have hfiniteFiber : ∀ i : ι, Finite (H ⧸ MulAction.stabilizer H (χ i)) := by
    intro i
    -- Each stabilizer quotient is equivalent to the corresponding orbit inside the finite
    -- character group.
    exact Finite.of_equiv _ (MulAction.orbitEquivQuotientStabilizer H (χ i))
  calc
    Nat.card (A →* ℂˣ) =
        Nat.card (Σ q : MulAction.orbitRel.Quotient H (A →* ℂˣ),
          H ⧸ MulAction.stabilizer H (χ (eχ.symm q))) := by
          -- Apply the class formula using the chosen representative in each character orbit.
          refine Nat.card_congr ?_
          exact MulAction.selfEquivSigmaOrbitsQuotientStabilizer' H (A →* ℂˣ)
            (φ := fun q ↦ χ (eχ.symm q)) (by
              intro q
              exact eχ.apply_symm_apply q)
    _ = Nat.card (Σ i : ι, H ⧸ MulAction.stabilizer H (χ i)) := by
          -- Transport the sigma-indexing from orbit classes back to the chosen representatives.
          exact Nat.card_congr
            (Equiv.sigmaCongrLeft (β := fun i : ι ↦ H ⧸ MulAction.stabilizer H (χ i))
              eχ.symm)
    _ = ∑ i : ι, Nat.card (H ⧸ MulAction.stabilizer H (χ i)) := by
          -- The sigma-cardinality splits as the sum of the finite fiber cardinalities.
          exact Nat.card_sigma
    _ = ∑' i : ι, (H_[φ; χ i]).index := by
          rw [tsum_fintype]
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [Subgroup.index_eq_card]

end

section

variable {χ : A →* ℂˣ}
variable {κ : Type w}

/-- Helper for Exercise 8-8.2-2: a finite abelian group has as many complex linear characters as
elements. -/
lemma card_linearCharacter_eq_card [Finite A] :
    Nat.card (A →* ℂˣ) = Nat.card A := by
  let e₁ : (A →* ℂˣ) ≃ (A →* ℂ) :=
    (MonoidHom.toHomUnitsMulEquiv (G := A) (M := ℂ)).toEquiv.symm
  let e₂ : (A →* ℂ) ≃ AddChar (Additive A) ℂ :=
    (AddChar.toMonoidHomEquiv (A := Additive A) (M := ℂ)).symm
  let e : (A →* ℂˣ) ≃ AddChar (Additive A) ℂ := e₁.trans e₂
  have hAdditiveCard : Nat.card (Additive A) = Nat.card A := by
    -- Forgetting between multiplicative and additive presentations does not change cardinality.
    refine Nat.card_congr ?_
    exact
      { toFun := fun a ↦ a
        invFun := fun a ↦ a
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
  calc
    Nat.card (A →* ℂˣ) = Nat.card (AddChar (Additive A) ℂ) := Nat.card_congr e
    _ = Nat.card (Additive A) := by
      let _ : Fintype (Additive A) := Fintype.ofFinite (Additive A)
      let _ : Fintype (AddChar (Additive A) ℂ) := Fintype.ofFinite (AddChar (Additive A) ℂ)
      rw [Nat.card_eq_fintype_card, AddChar.card_eq, Nat.card_eq_fintype_card]
    _ = Nat.card A := hAdditiveCard

-- Route correction: this exercise now reuses the canonical induction-bridge API imported from
-- `Proposition_8_8_2_1` instead of maintaining a file-local copy of those declarations.

/-- Helper for Exercise 8-8.2-2: a finite-index induced representation has degree equal to the
subgroup index times the degree of the inducing subspace. -/
private theorem finrank_eq_index_mul_finrank_of_isInducedFromSubrepresentation_local
    {G : Type} [Group G]
    {V : Type} [AddCommGroup V] [Module ℂ V]
    {S : Subgroup G} [Finite (G ⧸ S)]
    (ρ : Representation ℂ G V) [FiniteDimensional ℂ V]
    (W : Subrepresentation (ρ.comp S.subtype))
    (hInduced : ρ.IsInducedFromSubrepresentation S W) :
    Module.finrank ℂ V = S.index * Module.finrank ℂ W.toSubmodule := by
  classical
  letI : DecidableEq (G ⧸ S) := Classical.decEq _
  letI : Fintype (G ⧸ S) := Fintype.ofFinite (G ⧸ S)
  have leftQuotientSubmodule_out_local (q : G ⧸ S) :
      ρ.leftQuotientSubmodule S W q = W.toSubmodule.map (ρ q.out) := by
    have hq := ρ.leftQuotientSubmodule_mk S W q.out
    convert hq using 1
    exact congrArg (ρ.leftQuotientSubmodule S W) (Quotient.out_eq q).symm
  have hInternal : DirectSum.IsInternal (ρ.leftQuotientSubmodule S W) := by
    -- Unpack the Chapter 3 owner predicate into the corresponding internal direct sum.
    simpa [Representation.IsInducedFromSubrepresentation] using hInduced
  letI := DirectSum.IsInternal.chooseDecomposition (ρ.leftQuotientSubmodule S W) hInternal
  letI : ∀ q : G ⧸ S, Module.Free ℂ (ρ.leftQuotientSubmodule S W q) :=
    fun q ↦ Module.Free.of_divisionRing ℂ _
  let e := (DirectSum.decomposeLinearEquiv (ρ.leftQuotientSubmodule S W)).symm
  -- Compare the ambient representation with the direct sum of its left-coset summands.
  calc
    Module.finrank ℂ V =
        Module.finrank ℂ (DirectSum (G ⧸ S) fun q ↦ ρ.leftQuotientSubmodule S W q) := by
          exact e.finrank_eq.symm
    _ = ∑ q : G ⧸ S, Module.finrank ℂ (ρ.leftQuotientSubmodule S W q) := by
          exact Module.finrank_directSum (R := ℂ) (M := fun q ↦ ρ.leftQuotientSubmodule S W q)
    _ = ∑ _q : G ⧸ S, Module.finrank ℂ W.toSubmodule := by
          refine Finset.sum_congr rfl ?_
          intro q hq
          let eW :
              W.toSubmodule ≃ₗ[ℂ] ρ.leftQuotientSubmodule S W q :=
            let eV : V ≃ₗ[ℂ] V := LinearEquiv.ofBijective (ρ q.out) (ρ.apply_bijective q.out)
            (eV.submoduleMap W.toSubmodule).trans
              (LinearEquiv.ofEq _ _ (leftQuotientSubmodule_out_local q).symm)
          simpa using eW.finrank_eq.symm
    _ = S.index * Module.finrank ℂ W.toSubmodule := by
          simp [Subgroup.index_eq_card]

/-- Helper for Exercise 8-8.2-2: ordinary induction from a finite-index subgroup multiplies the
degree by the subgroup index. -/
private theorem ind_finrank_eq_subgroup_index_mul_finrank_local
    {G : Type} [Group G]
    {S : Subgroup G} [Finite (G ⧸ S)]
    {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ S W) :
    Module.finrank ℂ (Rep.ind S.subtype (Rep.of σ)) = S.index * Module.finrank ℂ W := by
  classical
  letI : S.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  letI : DecidableEq (G ⧸ S) := Classical.decEq _
  let C : Rep ℂ G := Rep.coind S.subtype (Rep.of σ)
  let e :
      ((Rep.ind S.subtype (Rep.of σ)).ρ).Equiv C.ρ :=
    Representation.equivOfIso (Rep.indCoindIso (Rep.of σ))
  let W₀ :
      Subrepresentation (C.ρ.comp S.subtype) :=
    Representation.supportedOnSubgroupSubrepresentation S σ
  let U :
      Subrepresentation (((Rep.ind S.subtype (Rep.of σ)).ρ).comp S.subtype) :=
    transported_subrepresentation_of_equiv (comp_subtype_equiv e.symm S) W₀
  have hW₀ :
      C.ρ.IsInducedFromSubrepresentation S W₀ := by
    -- The coinduced model is already packaged as induced from the subgroup-supported copy.
    simpa [C, W₀] using
      (Representation.isInducedFrom_supportedOnSubgroupSubrepresentation (H := S) (θ := σ))
  have hU :
      ((Rep.ind S.subtype (Rep.of σ)).ρ).IsInducedFromSubrepresentation S U := by
    -- Transport the inducedness witness across the canonical `Ind ≃ Coind` comparison.
    simpa [U] using isInducedFromSubrepresentation_of_equiv e.symm S W₀ hW₀
  let eU :
      W₀.toSubmodule ≃ₗ[ℂ] U.toSubmodule :=
    Submodule.equivMapOfInjective e.symm.toLinearMap e.symm.injective W₀.toSubmodule
  have hUfinrank :
      Module.finrank ℂ U.toSubmodule = Module.finrank ℂ W₀.toSubmodule := by
    -- Transporting along the equivalence only maps the carrier, so finrank is unchanged.
    simpa [U] using eU.finrank_eq.symm
  have hW₀finrank :
      Module.finrank ℂ W₀.toSubmodule = Module.finrank ℂ W := by
    -- The subgroup-supported subrepresentation is canonically equivalent to the source.
    exact (Representation.supportedOnSubgroupEquiv S σ).toLinearEquiv.finrank_eq.symm
  letI : FiniteDimensional ℂ W₀.toSubmodule :=
    FiniteDimensional.of_injective
      (Representation.supportedOnSubgroupEquiv S σ).symm.toLinearMap
      (Representation.supportedOnSubgroupEquiv S σ).symm.injective
  letI : FiniteDimensional ℂ U.toSubmodule :=
    FiniteDimensional.of_injective eU.symm.toLinearMap eU.symm.injective
  letI : ∀ q : G ⧸ S,
      FiniteDimensional ℂ (((Rep.ind S.subtype (Rep.of σ)).ρ).leftQuotientSubmodule S U q) :=
    fun q ↦ by
      have leftQuotientSubmodule_out_local :
          ((Rep.ind S.subtype (Rep.of σ)).ρ).leftQuotientSubmodule S U q =
            U.toSubmodule.map (((Rep.ind S.subtype (Rep.of σ)).ρ) q.out) := by
        have hq :=
          ((Rep.ind S.subtype (Rep.of σ)).ρ).leftQuotientSubmodule_mk S U q.out
        convert hq using 1
        exact
          congrArg (((Rep.ind S.subtype (Rep.of σ)).ρ).leftQuotientSubmodule S U)
            (Quotient.out_eq q).symm
      let eUq :
          U.toSubmodule ≃ₗ[ℂ]
            ((Rep.ind S.subtype (Rep.of σ)).ρ).leftQuotientSubmodule S U q :=
        let eV :
            Rep.ind S.subtype (Rep.of σ) ≃ₗ[ℂ] Rep.ind S.subtype (Rep.of σ) :=
          LinearEquiv.ofBijective
            (((Rep.ind S.subtype (Rep.of σ)).ρ) q.out)
            (((Rep.ind S.subtype (Rep.of σ)).ρ).apply_bijective q.out)
        (eV.submoduleMap U.toSubmodule).trans
          (LinearEquiv.ofEq _ _ leftQuotientSubmodule_out_local.symm)
      exact FiniteDimensional.of_injective eUq.symm.toLinearMap eUq.symm.injective
  have hInternalU :
      DirectSum.IsInternal
        (((Rep.ind S.subtype (Rep.of σ)).ρ).leftQuotientSubmodule S U) := by
    simpa [Representation.IsInducedFromSubrepresentation] using hU
  letI := DirectSum.IsInternal.chooseDecomposition
    (((Rep.ind S.subtype (Rep.of σ)).ρ).leftQuotientSubmodule S U) hInternalU
  letI : FiniteDimensional ℂ
      (DirectSum (G ⧸ S)
        fun q ↦ ((Rep.ind S.subtype (Rep.of σ)).ρ).leftQuotientSubmodule S U q) := by
    infer_instance
  let eDecomp :=
    (DirectSum.decomposeLinearEquiv
      (((Rep.ind S.subtype (Rep.of σ)).ρ).leftQuotientSubmodule S U)).symm
  letI : FiniteDimensional ℂ (Rep.ind S.subtype (Rep.of σ)) :=
    FiniteDimensional.of_injective eDecomp.symm.toLinearMap eDecomp.symm.injective
  calc
    Module.finrank ℂ (Rep.ind S.subtype (Rep.of σ)) = S.index * Module.finrank ℂ U.toSubmodule := by
          exact
            finrank_eq_index_mul_finrank_of_isInducedFromSubrepresentation_local
              ((Rep.ind S.subtype (Rep.of σ)).ρ) U hU
    _ = S.index * Module.finrank ℂ W₀.toSubmodule := by rw [hUfinrank]
    _ = S.index * Module.finrank ℂ W := by rw [hW₀finrank]

/-- Helper for Exercise 8-8.2-2: the explicit packet subgroup has the same index in `A ⋊[φ] H`
as the stabilizer has in `H`. -/
private theorem character_stabilizer_subgroup_index_eq
    (χ : A →* ℂˣ) :
    (character_stabilizer_subgroup (φ := φ) χ).index = (H_[φ; χ]).index := by
  classical
  let equot :
      (A ⋊[φ] H) ⧸ character_stabilizer_subgroup (φ := φ) χ ≃ H ⧸ H_[φ; χ] := by
    simpa [character_stabilizer_subgroup_eq_comap (φ := φ) χ] using
      (comap_leftCosetEquiv_of_surjective
        (SemidirectProduct.rightHom : A ⋊[φ] H →* H)
        SemidirectProduct.rightHom_surjective
        (H_[φ; χ]))
  calc
    (character_stabilizer_subgroup (φ := φ) χ).index =
        Nat.card ((A ⋊[φ] H) ⧸ character_stabilizer_subgroup (φ := φ) χ) := by
          rw [Subgroup.index_eq_card]
    _ = Nat.card (H ⧸ H_[φ; χ]) := Nat.card_congr equot
    _ = (H_[φ; χ]).index := by
          rw [Subgroup.index_eq_card]

variable [Finite H]

/-- Helper for Exercise 8-8.2-2: the degree of a little-groups packet is the stabilizer index
times the degree of the stabilizer representation. -/
private theorem theta_finrank_eq_characterStabilizer_index_mul_finrank
    (ρ : FDRep ℂ H_[φ; χ]) :
    Module.finrank ℂ (FDRep.theta φ χ ρ) =
      (H_[φ; χ]).index * Module.finrank ℂ ρ := by
  classical
  let τ : Rep ℂ H_[φ; χ] := Rep.of ρ.ρ
  let Sχ : Subgroup (A ⋊[φ] H) := character_stabilizer_subgroup (φ := φ) χ
  let _ : Finite ((A ⋊[φ] H) ⧸ Sχ) :=
    character_stabilizer_subgroup_quotient_finite (φ := φ) χ
  letI : FiniteDimensional ℂ (stabilizerRepresentation φ χ τ) := by
    -- The imported packet source still uses the same carrier as `ρ`, so no new dimension data
    -- is needed beyond the finite-dimensionality of `ρ`.
    change FiniteDimensional ℂ τ
    infer_instance
  -- Replace `theta` by ordinary induction from the explicit subgroup model and apply the
  -- finite-index induced-dimension formula.
  calc
    Module.finrank ℂ (FDRep.theta φ χ ρ) =
        Module.finrank ℂ
          (Rep.ind Sχ.subtype
            (Rep.of
              ((stabilizerRepresentation φ χ τ).ρ.comp
                (character_stabilizer_subgroup_equiv (φ := φ) χ).symm.toMonoidHom))) := by
          simpa [FDRep.theta, τ, Sχ] using
            (theta_equiv_ind_character_stabilizer_subgroup (φ := φ) χ τ).toLinearEquiv.finrank_eq
    _ = Sχ.index * Module.finrank ℂ ρ := by
          simpa [τ, Sχ] using
            (ind_finrank_eq_subgroup_index_mul_finrank_local
              (S := Sχ)
              (σ := (stabilizerRepresentation φ χ τ).ρ.comp
                (character_stabilizer_subgroup_equiv (φ := φ) χ).symm.toMonoidHom))
    _ = (H_[φ; χ]).index * Module.finrank ℂ ρ := by
          rw [character_stabilizer_subgroup_index_eq (φ := φ) χ]

/-- Helper for Exercise 8-8.2-2: a packet isomorphism between chosen orbit representatives forces
the representatives to agree and then identifies the stabilizer-side irreducible factors. -/
private theorem theta_iso_imp_eq_and_iso_local
    {ι : Type*} (χ : ι → A →* ℂˣ) (hχ : HasCharacterOrbitRepresentatives φ χ)
    {i i' : ι}
    (ρ : Rep.{w} ℂ H_[φ; χ i]) (ρ' : Rep.{w} ℂ H_[φ; χ i'])
    [ρ.ρ.IsIrreducible] [ρ'.ρ.IsIrreducible]
    (e :
      Representation.theta φ (χ i) ρ ≅
        Representation.theta φ (χ i') ρ') :
    ∃ h : i = i', Nonempty (ρ ≅ h ▸ ρ') := by
  let eθ :
      (Representation.theta φ (χ i) ρ).ρ.Equiv
        (Representation.theta φ (χ i') ρ').ρ :=
    Representation.equivOfIso e
  let eWeight :
      (character_weight_subrepresentation
        (φ := φ) (Representation.theta φ (χ i) ρ) (χ i)).ρ.Equiv
        (character_weight_subrepresentation
          (φ := φ) (Representation.theta φ (χ i') ρ') (χ i)).ρ :=
    character_weight_subrepresentation_equiv_of_equiv (φ := φ) eθ (χ i)
  have hsource_weight_irreducible :
      ((character_weight_subrepresentation
        (φ := φ) (Representation.theta φ (χ i) ρ) (χ i)).ρ).IsIrreducible := by
    -- The distinguished `χ_i`-weight space of the source packet recovers `ρ`.
    exact theta_character_weight_subrepresentation_isIrreducible (φ := φ) (χ i) ρ
  letI :
      ((character_weight_subrepresentation
        (φ := φ) (Representation.theta φ (χ i) ρ) (χ i)).ρ).IsIrreducible :=
    hsource_weight_irreducible
  letI :
      Nontrivial
        (character_weight_subrepresentation
          (φ := φ) (Representation.theta φ (χ i) ρ) (χ i)).V :=
    nontrivial_of_isIrreducible
      ((character_weight_subrepresentation
        (φ := φ) (Representation.theta φ (χ i) ρ) (χ i)).ρ)
  obtain ⟨x, hx⟩ := exists_ne
    (0 :
      (character_weight_subrepresentation
        (φ := φ) (Representation.theta φ (χ i) ρ) (χ i)).V)
  let y :
      (character_weight_subrepresentation
        (φ := φ) (Representation.theta φ (χ i') ρ') (χ i)).V :=
    eWeight x
  have hy : y ≠ 0 := by
    intro hy
    exact hx <| eWeight.injective <| by simpa [y] using hy
  have htarget_weight_ne_bot :
      character_weight_submodule
        (φ := φ) (Representation.theta φ (χ i') ρ') (χ i) ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    refine ⟨y.1, y.2, ?_⟩
    intro hy0
    exact hy <| Subtype.ext hy0
  let _ := characterMulAction φ
  rcases theta_weight_nonzero_imp_mem_orbit
      (φ := φ) (χ := χ i') (ρ := ρ') (ψ := χ i) htarget_weight_ne_bot with
    ⟨h, hh⟩
  have horbit :
      (Quotient.mk'' (χ i) : MulAction.orbitRel.Quotient H (A →* ℂˣ)) =
        Quotient.mk'' (χ i') := by
    apply Quotient.sound
    refine ⟨h, ?_⟩
    simpa [transportedCharacter] using hh
  have hii : i = i' := hχ.injective horbit
  subst hii
  let eWeight' :
      (character_weight_subrepresentation
        (φ := φ) (Representation.theta φ (χ i) ρ) (χ i)).ρ.Equiv
        (character_weight_subrepresentation
          (φ := φ) (Representation.theta φ (χ i) ρ') (χ i)).ρ :=
    character_weight_subrepresentation_equiv_of_equiv (φ := φ)
      (Representation.equivOfIso e) (χ i)
  let eρ :
      ρ.ρ.Equiv ρ'.ρ :=
    (theta_character_weight_subrepresentation_equiv (φ := φ) (χ i) ρ).symm.trans
      (eWeight'.trans
        (theta_character_weight_subrepresentation_equiv (φ := φ) (χ i) ρ'))
  have hρ_iso : ρ ≅ ρ' := by
    exact Rep.mkIso eρ
  exact ⟨rfl, ⟨hρ_iso⟩⟩

/-- Helper for Exercise 8-8.2-2: the sigma-family of packets indexed by orbit representatives is
pairwise nonisomorphic. -/
private theorem theta_sigma_pairwise_nonisomorphic_of_orbit_representatives
    {κ : ι → Type x}
    (χ : ι → A →* ℂˣ) (hχ : HasCharacterOrbitRepresentatives φ χ)
    (ρ : ∀ i, κ i → FDRep ℂ H_[φ; χ i])
    (hρ_complete : ∀ i, IsCompleteIrreducibleFamily (ρ i))
    (hρ_pairwise : ∀ i, PairwiseNonisomorphic (ρ i)) :
    PairwiseNonisomorphic
      (fun ij : Σ i, κ i ↦ FDRep.theta φ (χ ij.1) (ρ ij.1 ij.2)) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ hij hθ
  letI : Simple (ρ i j) := (hρ_complete i).isSimple j
  letI : Simple (ρ i' j') := (hρ_complete i').isSimple j'
  letI : Representation.IsIrreducible (ρ i j).ρ :=
    FDRep.isIrreducible_of_simple (ρ i j)
  letI : Representation.IsIrreducible (ρ i' j').ρ :=
    FDRep.isIrreducible_of_simple (ρ i' j')
  rcases hθ with ⟨eθ⟩
  let eRep :
      Representation.theta φ (χ i) (Rep.of (ρ i j).ρ) ≅
        Representation.theta φ (χ i') (Rep.of (ρ i' j').ρ) :=
    (forget₂ (FDRep ℂ (A ⋊[φ] H)) (Rep ℂ (A ⋊[φ] H))).mapIso eθ
  -- Proposition `8-8.2-1 (2)` first forces equality of the orbit representative index.
  rcases theta_iso_imp_eq_and_iso_local
      (φ := φ) χ hχ (i := i) (i' := i')
      (Rep.of (ρ i j).ρ) (Rep.of (ρ i' j').ρ)
      eRep with
    ⟨hii, hijj⟩
  subst hii
  rcases hijj with ⟨eρ⟩
  have hjj : j = j' := by
    by_contra hne
    exact hρ_pairwise i hne <| by
      simpa using ⟨(Representation.equivOfIso eρ).toFDRepIso⟩
  subst hjj
  exact hij rfl

-- Proof sketch: apply Chapter 2's square-degree formula to the stabilizer `H_[φ; χ]`, then use
-- the degree formula `dim θ[φ; χ, ρ_j] = (|H| / |H_[φ; χ]|) * dim ρ_j` to factor out the
-- constant index.
/-- Part (2) of Exercise 8-8.2-2: if `ρ j` runs through a complete family of pairwise nonisomorphic
irreducible finite-dimensional complex representations of `H_[φ; χ]`, then the corresponding
induced representations `θ[φ; χ, ρ j]` satisfy
`∑_j (dim θ[φ; χ, ρ_j])^2 = |H| · [H : H_[φ; χ]]`, equivalently
`|H|^2 / |H_[φ; χ]|`. -/
theorem sum_sq_degree_theta_eq_card_mul_characterStabilizer_index
    (ρ : κ → FDRep ℂ H_[φ; χ])
    (hρ_complete : IsCompleteIrreducibleFamily ρ)
    (hρ_pairwise : PairwiseNonisomorphic ρ) :
    ∑' j : κ, Module.finrank ℂ (FDRep.theta φ χ (ρ j)) ^ 2 =
      Nat.card H * (H_[φ; χ]).index := by
  classical
  letI : NeZero (Nat.card H_[φ; χ] : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  let _ : Finite κ := IsCompleteIrreducibleFamily.finite_index ρ hρ_complete hρ_pairwise
  let _ : Fintype κ := Fintype.ofFinite κ
  -- Rewrite the packet degrees through the explicit degree formula and factor out the constant
  -- index square from the stabilizer square-degree sum.
  rw [tsum_fintype]
  calc
    ∑ j : κ, Module.finrank ℂ (FDRep.theta φ χ (ρ j)) ^ 2 =
        ∑ j : κ, ((H_[φ; χ]).index * Module.finrank ℂ (ρ j)) ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          rw [theta_finrank_eq_characterStabilizer_index_mul_finrank (φ := φ) (χ := χ) (ρ := ρ j)]
    _ = (H_[φ; χ]).index ^ 2 * ∑ j : κ, Module.finrank ℂ (ρ j) ^ 2 := by
          simp_rw [mul_pow]
          rw [Finset.mul_sum]
    _ = (H_[φ; χ]).index ^ 2 * Nat.card H_[φ; χ] := by
          rw [sum_sq_degree_eq_card_of_complete_irreducible_family ρ hρ_complete hρ_pairwise]
    _ = Nat.card H * (H_[φ; χ]).index := by
          rw [pow_two, mul_assoc, Subgroup.index_mul_card, Nat.mul_comm]

end

section

variable [Finite A] [Finite H]
variable {ι : Type w}
variable (χ : ι → A →* ℂˣ) (hχ : HasCharacterOrbitRepresentatives φ χ)
variable {κ : ι → Type x}

-- Proof sketch: for each orbit representative `χ i`, apply part (2) to a complete irreducible
-- family on `H_[φ; χ i]`; then part (1) shows that the total square-degree sum over all
-- `θ[φ; χ i, ρ]` equals `|A ⋊[φ] H|`, and
-- Remark `complete_irreducible_family_iff_sum_sq_degree_eq_card` gives completeness.
-- This recovers Proposition `8-8.2-1 (3)` by the Chapter 2 criterion.
/-- Part (3) of Exercise 8-8.2-2: let `χ : ι → (A →* ℂˣ)` be a complete set of
orbit representatives for the `H`-action on the linear characters of `A`, and
for each `i` let `ρ i` be a complete family of pairwise nonisomorphic
irreducible finite-dimensional complex representations of `H_[φ; χ i]`. Then
the bundled little-groups family `FDRep.theta φ (χ i) (ρ i j)`, corresponding
to `θ[φ; χ i, ρ]`, is complete for `A ⋊[φ] H`, giving another proof of
Proposition `8-8.2-1 (3)`. -/
theorem theta_family_isCompleteIrreducibleFamily_of_orbit_representatives
    (hχ : HasCharacterOrbitRepresentatives φ χ)
    (ρ : ∀ i, κ i → FDRep ℂ H_[φ; χ i])
    (hρ_complete : ∀ i, IsCompleteIrreducibleFamily (ρ i))
    (hρ_pairwise : ∀ i, PairwiseNonisomorphic (ρ i)) :
    IsCompleteIrreducibleFamily
      (fun ij : Σ i, κ i ↦ FDRep.theta φ (χ ij.1) (ρ ij.1 ij.2)) := by
  classical
  let _ : Finite ι := HasCharacterOrbitRepresentatives.finiteIndex φ hχ
  let _ : Fintype ι := Fintype.ofFinite ι
  let _ : ∀ i, NeZero (Nat.card H_[φ; χ i] : ℂ) := fun i ↦
    ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  let _ : ∀ i, Finite (κ i) := fun i ↦
    IsCompleteIrreducibleFamily.finite_index (ρ i) (hρ_complete i) (hρ_pairwise i)
  let π : (Σ i, κ i) → FDRep ℂ (A ⋊[φ] H) := fun ij ↦
    FDRep.theta φ (χ ij.1) (ρ ij.1 ij.2)
  have hθ_simple :
      ∀ ij : Σ i, κ i, Simple (π ij) := by
    rintro ⟨i, j⟩
    -- Each packet is simple because Proposition `8-8.2-1 (1)` makes its underlying
    -- representation irreducible.
    letI : Simple (ρ i j) := (hρ_complete i).isSimple j
    letI : Representation.IsIrreducible (ρ i j).ρ :=
      FDRep.isIrreducible_of_simple (ρ i j)
    letI : Representation.IsIrreducible (FDRep.theta φ (χ i) (ρ i j)).ρ := by
      simpa [FDRep.theta] using
        (Representation.theta_irreducible_of_finite_normal_factor
          (φ := φ) (χ := χ i) (ρ := Rep.of (ρ i j).ρ))
    simpa [π] using FDRep.simple_of_isIrreducible (FDRep.theta φ (χ i) (ρ i j))
  have hθ_pairwise : PairwiseNonisomorphic π := by
    -- Reuse the packet-separation theorem already proved above.
    simpa [π] using
      (theta_sigma_pairwise_nonisomorphic_of_orbit_representatives
        (φ := φ) χ hχ ρ hρ_complete hρ_pairwise)
  let _ : Finite (A ⋊[φ] H) := by
    exact
      Finite.of_equiv (A × H)
        (SemidirectProduct.equivProd (N := A) (G := H) (φ := φ)).symm
  letI : NeZero (Nat.card (A ⋊[φ] H) : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  -- The Chapter 2 square-degree criterion upgrades the simple pairwise family to completeness.
  have hcharacter_count :
      ∑ i : ι, (H_[φ; χ i]).index = Nat.card (A →* ℂˣ) := by
    let _ : Fintype ι := Fintype.ofFinite ι
    calc
      ∑ i : ι, (H_[φ; χ i]).index = ∑' i : ι, (H_[φ; χ i]).index := by
        rw [tsum_fintype]
      _ = Nat.card (A →* ℂˣ) := by
        simpa using
          (card_character_eq_sum_characterStabilizer_index_of_orbit_representatives
            (φ := φ) (χ := χ) hχ).symm
  have hθ_complete : IsCompleteIrreducibleFamily π := by
    refine
      (complete_irreducible_family_iff_sum_sq_degree_eq_card
        (π := π) hθ_simple hθ_pairwise).2 ?_
    let sigmaFintype : Fintype (Σ i, κ i) := Fintype.ofFinite (Σ i, κ i)
    let _ : Fintype (Σ i, κ i) := sigmaFintype
    let s : Finset (Σ i, κ i) := Finset.univ
    let _ : ∀ i, Fintype (κ i) := fun i ↦ Fintype.ofFinite (κ i)
    have hs : s = Finset.univ.sigma (fun i ↦ (Finset.univ : Finset (κ i))) := by
      ext ij
      simp [s]
    -- Reindex the sigma-family by orbit representative, evaluate each inner sum with part (2),
    -- and then use part (1) plus `|Â| = |A|`.
    have hsum_explicit :
        s.sum (fun ij : Σ i, κ i ↦ Module.finrank ℂ (π ij) ^ 2) =
          Nat.card (A ⋊[φ] H) := by
      rw [hs, Finset.sum_sigma]
      calc
        ∑ i : ι, ∑ j : κ i, Module.finrank ℂ (π ⟨i, j⟩) ^ 2 =
            ∑ i : ι, Nat.card H * (H_[φ; χ i]).index := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              calc
                ∑ j : κ i, Module.finrank ℂ (π ⟨i, j⟩) ^ 2 =
                    ∑' j : κ i, Module.finrank ℂ (π ⟨i, j⟩) ^ 2 := by
                      rw [tsum_fintype]
                _ = Nat.card H * (H_[φ; χ i]).index := by
                      simpa [π] using
                        (sum_sq_degree_theta_eq_card_mul_characterStabilizer_index
                          (φ := φ) (χ := χ i) (ρ := ρ i) (hρ_complete := hρ_complete i)
                          (hρ_pairwise := hρ_pairwise i))
        _ = Nat.card H * ∑ i : ι, (H_[φ; χ i]).index := by
              rw [← Finset.mul_sum]
        _ = Nat.card H * Nat.card (A →* ℂˣ) := by
              rw [hcharacter_count]
        _ = Nat.card H * Nat.card A := by
              rw [card_linearCharacter_eq_card (A := A)]
        _ = Nat.card (A ⋊[φ] H) := by
              rw [SemidirectProduct.card, Nat.mul_comm]
    simpa [s] using hsum_explicit
  simpa [π] using hθ_complete

end

end SemidirectAbelian

end

end Representation
