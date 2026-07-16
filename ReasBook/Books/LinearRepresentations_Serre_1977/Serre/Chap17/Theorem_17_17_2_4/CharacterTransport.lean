import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap07.Proposition_7_7_2_1
import LinearRepresentations_Serre_1977.Serre.Chap12.Theorem_12_12_5_1
import LinearRepresentations_Serre_1977.Serre.Chap14.Proposition_14_14_1_1
import LinearRepresentations_Serre_1977.Serre.Chap17.Corollary_17_17_2_2.ElementarySubgroupInduction
import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_2_1.CharacterGrothendieck

open scoped MonoidAlgebra Representation SubgroupInduction TensorProduct
open CategoryTheory

noncomputable section

universe u v w x

namespace Representation

section OrdinaryRow

variable (k : Type u) [Field k]
variable (G : Type u) [Group G] [Finite G]

private local instance ordinary_finiteRepGrothendieckAddCommMonoid
    (H : Type u) [Group H] [Finite H] : AddCommMonoid (R₀[k](H)) :=
  (QuotientAddGroup.Quotient.addCommGroup
    (finiteRepGrothendieckRelations k H)).toAddCommMonoid

private local instance ordinary_finiteRepGrothendieckAddCommGroup
    (H : Type u) [Group H] [Finite H] : AddCommGroup (R₀[k](H)) :=
  QuotientAddGroup.Quotient.addCommGroup
    (finiteRepGrothendieckRelations k H)

private local instance ordinary_finiteRepGrothendieckIntModule
    (H : Type u) [Group H] [Finite H] : Module ℤ (R₀[k](H)) :=
  AddCommGroup.toIntModule (R₀[k](H))

/-- Helper for Theorem 17-17.2-4: the normalized rationalized owner for `R₀[k](H)`. -/
private abbrev RationalizedFiniteRepGrothendieck
    (H : Type u) [Group H] [Finite H] :=
  @TensorProduct ℤ Int.instCommSemiring ℚ R₀[k](H) Rat.addCommMonoid
    (ordinary_finiteRepGrothendieckAddCommMonoid (k := k) H)
    (AddCommGroup.toIntModule ℚ)
    (ordinary_finiteRepGrothendieckIntModule (k := k) H)

local instance instDecEqCyclic_ct : DecidableEq ↥(_root_.Subgroup.cyclicSubgroups G) :=
  Classical.decEq _

/-- Helper for Theorem 17-17.2-4: choose one representative of each isomorphism class of simple
finite-dimensional `k[H]`-representations. -/
private theorem exists_complete_pairwise_nonisomorphic_simple_family_over_field
    (H : Type u) [Group H] [Finite H] :
    ∃ (ι : Type (u + 1)) (π : ι → FDRep k H),
      PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π := by
  classical
  let SimpleRep : Type (u + 1) := { τ : FDRep k H // Simple τ }
  let r : Setoid SimpleRep :=
    { r := fun a b ↦ Nonempty (a.1 ≅ b.1)
      iseqv :=
        ⟨fun a ↦ ⟨Iso.refl _⟩,
          fun {a b} hab ↦ by
            rcases hab with ⟨e⟩
            exact ⟨e.symm⟩,
          fun {a b c} hab hbc ↦ by
            rcases hab with ⟨eab⟩
            rcases hbc with ⟨ebc⟩
            exact ⟨eab.trans ebc⟩⟩ }
  let ι : Type (u + 1) := Quotient r
  let π : ι → FDRep k H := fun q ↦ (Quotient.out q).1
  have hπ_pairwise : PairwiseNonisomorphic π := by
    intro q q' hqq' hIso
    rcases hIso with ⟨e⟩
    have hclasses : (⟦Quotient.out q⟧ : ι) = (⟦Quotient.out q'⟧ : ι) := by
      apply Quotient.sound
      exact ⟨e⟩
    apply hqq'
    calc
      q = (⟦Quotient.out q⟧ : ι) := (Quotient.out_eq q).symm
      _ = (⟦Quotient.out q'⟧ : ι) := hclasses
      _ = q' := Quotient.out_eq q'
  have hπ_complete : IsCompleteIrreducibleFamily π := by
    refine ⟨?_, ?_⟩
    · intro q
      exact (Quotient.out q).2
    · intro τ hτ
      let q : ι := ⟦⟨τ, hτ⟩⟧
      refine ⟨q, ?_⟩
      have hqeq : (⟦Quotient.out q⟧ : ι) = (⟦⟨τ, hτ⟩⟧ : ι) := by
        simpa [q] using (Quotient.out_eq q)
      have hq : Nonempty (((Quotient.out q).1) ≅ τ) :=
        Quotient.exact hqeq
      rcases hq with ⟨e⟩
      exact ⟨e.symm⟩
  exact ⟨ι, π, hπ_pairwise, hπ_complete⟩

/-- Helper for Theorem 17-17.2-4: the canonical `DFinsupp` sum of the rationalized cyclic
subgroup-induction maps. -/
abbrev cyclic_rationalized_induction_lsum :
    (Π₀ H : _root_.Subgroup.cyclicSubgroups G,
      RationalizedFiniteRepGrothendieck (k := k) H.1) →ₗ[ℚ]
      RationalizedFiniteRepGrothendieck (k := k) G :=
  DFinsupp.lsum ℚ fun H : _root_.Subgroup.cyclicSubgroups G ↦
    (Subgroup.finiteRepGrothendieckGroupRationalizedInduction
      (k := k) (G := G) H.1 :
      RationalizedFiniteRepGrothendieck (k := k) H.1 →ₗ[ℚ]
        RationalizedFiniteRepGrothendieck (k := k) G)

/-- Helper for Theorem 17-17.2-4: the literal tensor owner `ℚ ⊗[ℤ] R[k](H)` is the Chapter `12`
realized scalar-extension owner `ℚ ⊗R[k](H)`. -/
private abbrev rationalized_characterRing_toOwner_linearMap
    (H : Type u) [Group H] [Finite H] [CharZero k] :
    (ℚ ⊗[ℤ] R[k](H)) →ₗ[ℚ] ℚ ⊗R[k](H) :=
  ((R[k](H)).toSubmodule).tensorToSpan ℚ

/-- Helper for Theorem 17-17.2-4: realizing a pure tensor in the literal character-ring owner
just scales the underlying virtual character. -/
@[simp] private theorem rationalized_characterRing_toOwner_linearMap_apply_tmul
    (H : Type u) [Group H] [Finite H] [CharZero k] (q : ℚ) (χ : R[k](H)) :
    (((rationalized_characterRing_toOwner_linearMap (k := k) (H := H)) (q ⊗ₜ[ℤ] χ) :
        ℚ ⊗R[k](H)) : H → k) =
      q • ((χ : R[k](H)) : H → k) := by
  rfl

/-- Helper for Theorem 17-17.2-4: the Chapter `12` owner realization is injective on the literal
tensor-product owner. -/
private theorem rationalized_characterRing_toOwner_linearMap_injective
    (H : Type u) [Group H] [Finite H] [CharZero k] :
    Function.Injective (rationalized_characterRing_toOwner_linearMap (k := k) (H := H)) := by
  simpa [rationalized_characterRing_toOwner_linearMap] using
    (((R[k](H)).toSubmodule).injective_tensorToSpan ℚ)

/-- Helper for Theorem 17-17.2-4: every realized scalar-extension class function comes from a
literal tensor in `ℚ ⊗[ℤ] R[k](H)`. -/
private theorem rationalized_characterRing_toOwner_linearMap_surjective
    (H : Type u) [Group H] [Finite H] [CharZero k] :
    Function.Surjective (rationalized_characterRing_toOwner_linearMap (k := k) (H := H)) := by
  simpa [rationalized_characterRing_toOwner_linearMap] using
    (((R[k](H)).toSubmodule).surjective_tensorToSpan ℚ)

/-- Helper for Theorem 17-17.2-4: the literal tensor owner `ℚ ⊗[ℤ] R[k](H)` is linearly
equivalent to the Chapter `12` owner `ℚ ⊗R[k](H)`. -/
noncomputable abbrev rationalizedCharacterRingTensorSpanLinearEquiv
    (H : Type u) [Group H] [Finite H] [CharZero k] :
    (ℚ ⊗[ℤ] R[k](H)) ≃ₗ[ℚ] ℚ ⊗R[k](H) :=
  LinearEquiv.ofBijective
    (rationalized_characterRing_toOwner_linearMap (k := k) (H := H))
    ⟨rationalized_characterRing_toOwner_linearMap_injective (k := k) (H := H),
      rationalized_characterRing_toOwner_linearMap_surjective (k := k) (H := H)⟩

/-- Helper for Theorem 17-17.2-4: the tensor-span equivalence acts on a pure tensor by the
obvious scalar multiple of the underlying virtual character. -/
@[simp] theorem rationalizedCharacterRingTensorSpanLinearEquiv_apply_tmul
    (H : Type u) [Group H] [Finite H] [CharZero k] (q : ℚ) (χ : R[k](H)) :
    (((rationalizedCharacterRingTensorSpanLinearEquiv (k := k) H) (q ⊗ₜ[ℤ] χ) :
        ℚ ⊗R[k](H)) : H → k) =
      q • ((χ : R[k](H)) : H → k) := by
  -- The equivalence is defined from the tensor-span realization map, so the pure-tensor formula
  -- is the same as for that underlying linear map.
  simp [rationalizedCharacterRingTensorSpanLinearEquiv,
    rationalized_characterRing_toOwner_linearMap_apply_tmul]

/-- Helper for Theorem 17-17.2-4: base change of the Grothendieck-character map from `R₀[k](H)`
to the literal tensor owner `ℚ ⊗[ℤ] R[k](H)`. -/
private abbrev rationalized_finiteRepGrothendieckCharacter_linearMap
    (H : Type u) [Group H] [Finite H] [CharZero k] :
    RationalizedFiniteRepGrothendieck (k := k) H →ₗ[ℚ] (ℚ ⊗[ℤ] R[k](H)) :=
  ((finiteRepGrothendieckCharacter k H).toIntLinearMap).baseChange ℚ

/-- Helper for Theorem 17-17.2-4: the rationalized Grothendieck-character map sends a pure tensor
to the matching pure tensor of the ordinary virtual character. -/
@[simp] private theorem rationalized_finiteRepGrothendieckCharacter_linearMap_apply_tmul
    (H : Type u) [Group H] [Finite H] [CharZero k] (q : ℚ) (x : R₀[k](H)) :
    rationalized_finiteRepGrothendieckCharacter_linearMap (k := k) H (q ⊗ₜ[ℤ] x) =
      q ⊗ₜ[ℤ] finiteRepGrothendieckCharacter k H x := by
  simpa [rationalized_finiteRepGrothendieckCharacter_linearMap] using
    (LinearMap.baseChange_tmul
      (f := (finiteRepGrothendieckCharacter k H).toIntLinearMap) (A := ℚ) q x)

/-- Helper for Theorem 17-17.2-4: the rationalized Grothendieck-character map stays injective
after tensoring with `ℚ`. -/
private theorem rationalized_finiteRepGrothendieckCharacter_linearMap_injective
    (H : Type u) [Group H] [Finite H] [CharZero k] :
    Function.Injective (rationalized_finiteRepGrothendieckCharacter_linearMap (k := k) H) := by
  -- Injectivity survives the flat base change `ℤ → ℚ`.
  simpa [rationalized_finiteRepGrothendieckCharacter_linearMap] using
    (Module.Flat.lTensor_preserves_injective_linearMap (M := ℚ)
      ((finiteRepGrothendieckCharacter k H).toIntLinearMap)
      (by
        intro x y hxy
        exact (finiteRepGrothendieckCharacter_bijective' (K := k) (G := H)).1 hxy))

/-- Helper for Theorem 17-17.2-4: in characteristic zero, every element of the literal tensor
owner `ℚ ⊗[ℤ] R[k](H)` comes from the rationalized Grothendieck group. -/
private theorem rationalized_finiteRepGrothendieckCharacter_linearMap_surjective
    (H : Type u) [Group H] [Finite H] [CharZero k] :
    Function.Surjective (rationalized_finiteRepGrothendieckCharacter_linearMap (k := k) H) := by
  classical
  obtain ⟨ι, π, hπ_pairwise, hπ_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_simple_family_over_field (k := k) H
  let b₀ : Module.Basis ι ℤ (R₀[k](H)) :=
    simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  let bR : Module.Basis ι ℤ (R[k](H)) :=
    irreducible_characters_basis_of_complete_family k π hπ_pairwise hπ_complete
  intro χ
  obtain ⟨c, hc⟩ := TensorProduct.eq_repr_basis_right (R := ℤ) (M := ℚ) (𝒞 := bR) (x := χ)
  refine ⟨c.sum fun i a ↦ a ⊗ₜ[ℤ] b₀ i, ?_⟩
  -- Expand the target in the irreducible-character basis and send the matching simple-class
  -- expansion through the tensorized Grothendieck-character map.
  calc
    rationalized_finiteRepGrothendieckCharacter_linearMap (k := k) H
        (c.sum fun i a ↦ a ⊗ₜ[ℤ] b₀ i) =
      c.sum fun i a ↦ a ⊗ₜ[ℤ] finiteRepGrothendieckCharacter k H (b₀ i) := by
        simp [Finsupp.sum, map_sum,
          rationalized_finiteRepGrothendieckCharacter_linearMap_apply_tmul]
    _ = c.sum fun i a ↦ a ⊗ₜ[ℤ] bR i := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        letI : Simple (π i) := hπ_complete.isSimple i
        have hbasis : finiteRepGrothendieckCharacter k H (b₀ i) = bR i := by
          ext g
          simpa [b₀, bR, simple_finiteRep_classes_basis_of_complete_family_apply,
            irreducible_characters_basis_of_complete_family_apply] using
            (finiteRepGrothendieckCharacter_class (K := k) (G := H) (π i) g)
        simp [hbasis]
    _ = χ := hc

/-- Helper for Theorem 17-17.2-4: the subgroupwise bridge from rationalized `R₀[k](H)` to the
Chapter `12` owner `ℚ ⊗R[k](H)`. -/
private abbrev rationalized_finiteRepGrothendieckCharacterOwnerLinearMap
    (H : Type u) [Group H] [Finite H] [CharZero k] :
    RationalizedFiniteRepGrothendieck (k := k) H →ₗ[ℚ] ℚ ⊗R[k](H) :=
  (rationalized_characterRing_toOwner_linearMap (k := k) (H := H)).comp
    (rationalized_finiteRepGrothendieckCharacter_linearMap (k := k) H)

/-- Helper for Theorem 17-17.2-4: on pure tensors, the subgroupwise owner bridge is just the
scalar multiple of the ordinary Grothendieck character. -/
@[simp] private theorem rationalized_finiteRepGrothendieckCharacterOwnerLinearMap_apply_tmul
    (H : Type u) [Group H] [Finite H] [CharZero k] (q : ℚ) (x : R₀[k](H)) :
    (((rationalized_finiteRepGrothendieckCharacterOwnerLinearMap (k := k) H)
        (q ⊗ₜ[ℤ] x) : ℚ ⊗R[k](H)) : H → k) =
      q • ((finiteRepGrothendieckCharacter k H x : R[k](H)) : H → k) := by
  simp [rationalized_finiteRepGrothendieckCharacterOwnerLinearMap,
    rationalized_finiteRepGrothendieckCharacter_linearMap_apply_tmul,
    rationalized_characterRing_toOwner_linearMap_apply_tmul]

/-- Helper for Theorem 17-17.2-4: the Grothendieck-character owner bridge is injective on each
cyclic summand. -/
private theorem rationalized_finiteRepGrothendieckCharacterOwnerLinearMap_injective
    (H : Type u) [Group H] [Finite H] [CharZero k] :
    Function.Injective (rationalized_finiteRepGrothendieckCharacterOwnerLinearMap (k := k) H) := by
  -- The owner bridge is a composition of the injective rationalized character map and the
  -- injective tensor-span realization.
  intro x y hxy
  apply rationalized_finiteRepGrothendieckCharacter_linearMap_injective (k := k) (H := H)
  exact rationalized_characterRing_toOwner_linearMap_injective (k := k) (H := H) hxy

/-- Helper for Theorem 17-17.2-4: the Grothendieck-character owner bridge is surjective on each
cyclic summand. -/
private theorem rationalized_finiteRepGrothendieckCharacterOwnerLinearMap_surjective
    (H : Type u) [Group H] [Finite H] [CharZero k] :
    Function.Surjective (rationalized_finiteRepGrothendieckCharacterOwnerLinearMap (k := k) H) := by
  intro χ
  rcases rationalized_characterRing_toOwner_linearMap_surjective (k := k) (H := H) χ with
    ⟨χ', hχ'⟩
  rcases rationalized_finiteRepGrothendieckCharacter_linearMap_surjective (k := k) (H := H) χ' with
    ⟨x, hx⟩
  refine ⟨x, ?_⟩
  -- Choose a preimage in the literal tensor owner first, then realize it in the Chapter `12`
  -- owner.
  calc
    rationalized_finiteRepGrothendieckCharacterOwnerLinearMap (k := k) H x
        = rationalized_characterRing_toOwner_linearMap (k := k) (H := H) χ' := by
            simp [rationalized_finiteRepGrothendieckCharacterOwnerLinearMap, hx]
    _ = χ := hχ'

/-- Helper for Theorem 17-17.2-4: the subgroupwise Grothendieck-character bridge packaged as a
linear equivalence into the Chapter `12` owner. -/
noncomputable abbrev rationalized_finiteRepGrothendieckCharacterOwnerLinearEquiv
    (H : Type u) [Group H] [Finite H] [CharZero k] :
    RationalizedFiniteRepGrothendieck (k := k) H ≃ₗ[ℚ] ℚ ⊗R[k](H) :=
  LinearEquiv.ofBijective
    (rationalized_finiteRepGrothendieckCharacterOwnerLinearMap (k := k) H)
    ⟨rationalized_finiteRepGrothendieckCharacterOwnerLinearMap_injective (k := k) (H := H),
      rationalized_finiteRepGrothendieckCharacterOwnerLinearMap_surjective (k := k) (H := H)⟩

/-- Helper for Theorem 17-17.2-4: on pure tensors, the subgroupwise Grothendieck-character
equivalence is the scalar multiple of the ordinary Grothendieck character. -/
@[simp] theorem rationalized_finiteRepGrothendieckCharacterOwnerLinearEquiv_apply_tmul
    (H : Type u) [Group H] [Finite H] [CharZero k] (q : ℚ) (x : R₀[k](H)) :
    (((rationalized_finiteRepGrothendieckCharacterOwnerLinearEquiv (k := k) H)
        (q ⊗ₜ[ℤ] x) : ℚ ⊗R[k](H)) : H → k) =
      q • ((finiteRepGrothendieckCharacter k H x : R[k](H)) : H → k) := by
  -- The equivalence uses the owner bridge as its underlying linear map.
  simp [rationalized_finiteRepGrothendieckCharacterOwnerLinearEquiv,
    rationalized_finiteRepGrothendieckCharacterOwnerLinearMap_apply_tmul]

/-- Helper for Theorem 17-17.2-4: the finite owner `Subgroup.cyclicSubgroups G` and Chapter `12`'s
plain cyclic-subgroup subtype carry the same cyclic subgroups. -/
private def cyclicSubgroupIndexEquiv :
    _root_.Subgroup.cyclicSubgroups G ≃ { H : Subgroup G // IsCyclic H } where
  toFun := fun H ↦ ⟨H.1, (Subgroup.mem_cyclicSubgroups : H.1 ∈ Subgroup.cyclicSubgroups G ↔
    IsCyclic H.1).mp H.2⟩
  invFun := fun H ↦ ⟨H.1, (Subgroup.mem_cyclicSubgroups : H.1 ∈ Subgroup.cyclicSubgroups G ↔
    IsCyclic H.1).mpr H.2⟩
  left_inv := by
    intro H
    ext
    rfl
  right_inv := by
    intro H
    ext
    rfl

private local instance : DecidableEq { H : Subgroup G // IsCyclic H } :=
  Classical.decEq _

/-- Helper for Theorem 17-17.2-4: first reindex the ordinary-row direct sum from the finite owner
`Subgroup.cyclicSubgroups G` to Chapter `12`'s cyclic-subgroup subtype. -/
private abbrev cyclic_rationalized_finiteRepGrothendieck_reindex_raw :
    (Π₀ H : _root_.Subgroup.cyclicSubgroups G,
      RationalizedFiniteRepGrothendieck (k := k) H.1) ≃ₗ[ℚ]
      (Π₀ H : { J : Subgroup G // IsCyclic J },
        RationalizedFiniteRepGrothendieck (k := k)
          (((cyclicSubgroupIndexEquiv (G := G)).symm H).1)) :=
  DFinsupp.domLCongr (R := ℚ)
    (M := fun H : _root_.Subgroup.cyclicSubgroups G ↦
      RationalizedFiniteRepGrothendieck (k := k) H.1)
    (cyclicSubgroupIndexEquiv (G := G))

/-- Helper for Theorem 17-17.2-4: after reindexing, the target family is definitionally
normalized back to the same subgroup owner `H.1` used by Chapter `12`. -/
private abbrev cyclic_rationalized_finiteRepGrothendieck_reindex :
    (Π₀ H : _root_.Subgroup.cyclicSubgroups G,
      RationalizedFiniteRepGrothendieck (k := k) H.1) ≃ₗ[ℚ]
      (Π₀ H : { J : Subgroup G // IsCyclic J },
        RationalizedFiniteRepGrothendieck (k := k) H.1) :=
  (cyclic_rationalized_finiteRepGrothendieck_reindex_raw (k := k) (G := G)).trans <|
    DFinsupp.mapRange.linearEquiv fun H ↦ by
      -- Both owners are the same subgroup module; only the proof witness carried by the subtype
      -- index differs.
      simpa using
        (LinearEquiv.refl ℚ
          (RationalizedFiniteRepGrothendieck (k := k) H.1))

/-- Helper for Theorem 17-17.2-4: the raw `domLCongr` reindexing sends a `single` summand to the
matching Chapter `12` index, with only the canonical dependent cast on the carried tensor. -/
private theorem cyclic_rationalized_finiteRepGrothendieck_reindex_raw_single
    (H : _root_.Subgroup.cyclicSubgroups G)
    (x : RationalizedFiniteRepGrothendieck (k := k) H.1) :
    (cyclic_rationalized_finiteRepGrothendieck_reindex_raw (k := k) (G := G))
        (DFinsupp.single H x) =
      DFinsupp.single ((cyclicSubgroupIndexEquiv (G := G)) H)
        (((congrArg
              (fun K : _root_.Subgroup.cyclicSubgroups G =>
                RationalizedFiniteRepGrothendieck (k := k) K.1)
              ((cyclicSubgroupIndexEquiv (G := G)).symm_apply_apply H)).symm) ▸ x) := by
  -- Expose `DFinsupp.domLCongr` as the underlying `comapDomain'`, then compare the resulting
  -- `single` on each Chapter `12` cyclic-subgroup index.
  ext J
  by_cases hJ : J = (cyclicSubgroupIndexEquiv (G := G)) H
  · subst hJ
    simp [cyclic_rationalized_finiteRepGrothendieck_reindex_raw]
  · have hJ' : (cyclicSubgroupIndexEquiv (G := G)).symm J ≠ H := by
      intro h
      apply hJ
      exact congrArg (cyclicSubgroupIndexEquiv (G := G)) h
    have hJ'' : H ≠ (cyclicSubgroupIndexEquiv (G := G)).symm J := by
      simpa [eq_comm] using hJ'
    have hJrev : ¬(cyclicSubgroupIndexEquiv (G := G)) H = J := by
      simpa [eq_comm] using hJ
    simp [cyclic_rationalized_finiteRepGrothendieck_reindex_raw, hJ, hJrev, hJ', hJ'',
      DFinsupp.comapDomain'_apply]

/-- Helper for Theorem 17-17.2-4: a pointwise `DFinsupp.mapRange.linearEquiv` sends a `single`
summand to the matching `single` summand. -/
private theorem dfinsupp_mapRange_linearEquiv_single
    {β₁ β₂ : { J : Subgroup G // IsCyclic J } → Type*}
    [∀ J, AddCommMonoid (β₁ J)] [∀ J, AddCommMonoid (β₂ J)]
    [∀ J, Module ℚ (β₁ J)] [∀ J, Module ℚ (β₂ J)]
    (e : ∀ J, β₁ J ≃ₗ[ℚ] β₂ J)
    (J : { J : Subgroup G // IsCyclic J }) (x : β₁ J) :
    DFinsupp.mapRange.linearEquiv e (DFinsupp.single J x) =
      DFinsupp.single J (e J x) := by
  -- The bundled `mapRange` equivalence reduces to the ordinary `single` map once its underlying
  -- `DFinsupp.mapRange` is exposed.
  rw [DFinsupp.mapRange.linearEquiv_apply, DFinsupp.mapRange_single]

/-- Helper for Theorem 17-17.2-4: reindexing the cyclic direct sum carries a `DFinsupp.single`
summand to the matching single summand in Chapter `12`'s cyclic-subgroup owner. -/
private theorem cyclic_rationalized_finiteRepGrothendieck_reindex_single
    (H : _root_.Subgroup.cyclicSubgroups G)
    (x : RationalizedFiniteRepGrothendieck (k := k) H.1) :
    (cyclic_rationalized_finiteRepGrothendieck_reindex (k := k) (G := G))
        (DFinsupp.single H x) =
      DFinsupp.single ((cyclicSubgroupIndexEquiv (G := G)) H) x := by
  -- Compose the raw `domLCongr` single formula with the pointwise identity normalization of the
  -- transported subgroup owner.
  rw [cyclic_rationalized_finiteRepGrothendieck_reindex, LinearEquiv.trans_apply]
  rw [cyclic_rationalized_finiteRepGrothendieck_reindex_raw_single]
  ext J
  by_cases hJ : J = (cyclicSubgroupIndexEquiv (G := G)) H
  · subst hJ
    rfl
  · have hJrev : ¬(cyclicSubgroupIndexEquiv (G := G)) H = J := by
      simpa [eq_comm] using hJ
    simp [DFinsupp.mapRange.linearEquiv_apply, DFinsupp.mapRange_single, hJrev]

/-- Helper for Theorem 17-17.2-4: the full source-side transport first reindexes the cyclic
subgroup owner, then applies the subgroupwise Grothendieck-character equivalences. -/
private abbrev cyclic_rationalized_finiteRepGrothendieckCharacterSourceEquiv [CharZero k] :
    (Π₀ H : _root_.Subgroup.cyclicSubgroups G,
      RationalizedFiniteRepGrothendieck (k := k) H.1) ≃ₗ[ℚ]
      (Π₀ H : { J : Subgroup G // IsCyclic J }, ℚ ⊗R[k](H.1)) :=
  (cyclic_rationalized_finiteRepGrothendieck_reindex (k := k) (G := G)).trans <|
    DFinsupp.mapRange.linearEquiv fun H ↦
      rationalized_finiteRepGrothendieckCharacterOwnerLinearEquiv (k := k) H.1

/-- Helper for Theorem 17-17.2-4: the full source-side transport sends a single cyclic summand to
the matching Chapter `12` single summand equipped with the subgroupwise Grothendieck character. -/
private theorem cyclic_rationalized_finiteRepGrothendieckCharacterSourceEquiv_single
    [CharZero k]
    (H : _root_.Subgroup.cyclicSubgroups G)
    (x : RationalizedFiniteRepGrothendieck (k := k) H.1) :
    (cyclic_rationalized_finiteRepGrothendieckCharacterSourceEquiv (k := k) (G := G))
        (DFinsupp.single H x) =
      DFinsupp.single ((cyclicSubgroupIndexEquiv (G := G)) H)
        ((rationalized_finiteRepGrothendieckCharacterOwnerLinearEquiv (k := k) H.1) x) := by
  -- First rewrite the source-side single summand through the cyclic-owner reindexing, then apply
  -- the pointwise subgroupwise Grothendieck-character equivalence on that single index.
  rw [cyclic_rationalized_finiteRepGrothendieckCharacterSourceEquiv, LinearEquiv.trans_apply]
  rw [cyclic_rationalized_finiteRepGrothendieck_reindex_single]
  exact
    dfinsupp_mapRange_linearEquiv_single
      (e := fun J ↦
        rationalized_finiteRepGrothendieckCharacterOwnerLinearEquiv (k := k) J.1)
      (J := ((cyclicSubgroupIndexEquiv (G := G)) H))
      (x := x)

/-- Helper for Theorem 17-17.2-4: surjectivity transports across a conjugating pair of linear
equivalences. -/
private theorem surjective_of_linear_equiv_conjugate
    {V : Type u} {W : Type v} {V' : Type w} {W' : Type x}
    [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W]
    [AddCommGroup V'] [Module ℚ V']
    [AddCommGroup W'] [Module ℚ W']
    (eV : V ≃ₗ[ℚ] V')
    (eW : W ≃ₗ[ℚ] W')
    (f : V →ₗ[ℚ] W)
    (g : V' →ₗ[ℚ] W')
    (hconj : eW.toLinearMap.comp f = g.comp eV.toLinearMap)
    (hg : Function.Surjective g) :
    Function.Surjective f := by
  intro w
  rcases hg (eW w) with ⟨v', hv'⟩
  refine ⟨eV.symm v', ?_⟩
  -- Apply the conjugation identity to the chosen Chapter `12` preimage and then cancel `eW`.
  apply eW.injective
  calc
    eW (f (eV.symm v')) = g (eV (eV.symm v')) := by
      simpa using LinearMap.congr_fun hconj (eV.symm v')
    _ = g v' := by
      simp
    _ = eW w := hv'

/-- Helper for Theorem 17-17.2-4: on one cyclic summand, ordinary rationalized induction
commutes with the Chapter `12` Grothendieck-character transport. -/
private theorem rationalized_finiteRepGrothendieckCharacter_cyclic_induction_commutes_on_single
    [CharZero k]
    (H : _root_.Subgroup.cyclicSubgroups G)
    (x : RationalizedFiniteRepGrothendieck (k := k) H.1) :
    (rationalized_finiteRepGrothendieckCharacterOwnerLinearEquiv (k := k) G)
        ((cyclic_rationalized_induction_lsum k G) (DFinsupp.single H x)) =
      cyclicSubgroupInduction (A := ℚ) k G
        ((cyclic_rationalized_finiteRepGrothendieckCharacterSourceEquiv (k := k) (G := G))
          (DFinsupp.single H x)) := by
  -- Route correction: the remaining work is the source-faithful pure-tensor calculation on one
  -- cyclic summand, and then tensor additivity extends that identity to all of `x`.
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · -- The zero tensor is preserved by both linear maps on the cyclic `single` summand.
    simp [cyclic_rationalized_induction_lsum,
      cyclic_rationalized_finiteRepGrothendieckCharacterSourceEquiv]
  · intro q y
    -- On a pure tensor, both sides evaluate to the same induced class function after rewriting
    -- the left side through subgroup induction on `R₀` and the right side through the normalized
    -- `single` transport into Chapter `12`'s owner.
    rw [cyclic_rationalized_finiteRepGrothendieckCharacterSourceEquiv_single]
    rw [cyclicSubgroupInduction_single]
    apply Subtype.ext
    ext g
    calc
      (((rationalized_finiteRepGrothendieckCharacterOwnerLinearEquiv (k := k) G)
          ((cyclic_rationalized_induction_lsum k G)
            (DFinsupp.single H (q ⊗ₜ[ℤ] y))) : ℚ ⊗R[k](G)) : G → k) g =
        (q •
          ((finiteRepGrothendieckCharacter k G
            (Representation.Subgroup.finiteRepGrothendieckGroupInduction k H.1 y) :
              R[k](G)) : G → k)) g := by
            simp [cyclic_rationalized_induction_lsum,
              Subgroup.finiteRepGrothendieckGroupRationalizedInduction,
              LinearMap.baseChange_tmul]
      _ =
        (q •
          ((H.1.characterRingOverFieldInduction k
            (finiteRepGrothendieckCharacter k H.1 y) : R[k](G)) : G → k)) g := by
              rw [finiteRepGrothendieckCharacter_subgroupInduction
                (K := k) (G := G) H.1 y]
      _ =
        (Ind[H.1](q • ((finiteRepGrothendieckCharacter k H.1 y : R[k](H.1)) : H.1 → k))) g := by
          rw [Subgroup.characterRingOverFieldInduction_apply]
          rw [← Subgroup.inducedClassFunction_map_smul]
      _ =
        (((H.1.characterRingOverFieldAlgebraScalarExtensionInduction
            ((rationalized_finiteRepGrothendieckCharacterOwnerLinearEquiv (k := k) H.1)
              (q ⊗ₜ[ℤ] y)) : ℚ ⊗R[k](G)) : G → k) g) := by
                rw [Subgroup.characterRingOverFieldAlgebraScalarExtensionInduction_apply]
                congr 1
  · intro x y hx hy
    -- Additivity of both linear sides lets the pure-tensor calculation extend to arbitrary
    -- rationalized classes.
    simpa [map_add] using congrArg₂ HAdd.hAdd hx hy

/-- Helper for Theorem 17-17.2-4: the single-summand transport square packages into a global
conjugation square between the ordinary-row owner and Chapter `12`'s cyclic-induction owner. -/
private theorem rationalized_finiteRepGrothendieckCharacter_cyclic_induction_commutes
    [CharZero k] :
    (rationalized_finiteRepGrothendieckCharacterOwnerLinearEquiv (k := k) G).toLinearMap.comp
        (cyclic_rationalized_induction_lsum k G) =
      (cyclicSubgroupInduction (A := ℚ) k G).comp
        (cyclic_rationalized_finiteRepGrothendieckCharacterSourceEquiv
          (k := k) (G := G)).toLinearMap := by
  -- Package the verified `single`-summand square into an equality of the full `DFinsupp` owner
  -- maps.
  apply DFinsupp.lhom_ext
  intro H x
  -- The global conjugation identity is exactly the single-summand theorem evaluated on
  -- `DFinsupp.single H x`.
  simpa [LinearMap.comp_apply] using
    rationalized_finiteRepGrothendieckCharacter_cyclic_induction_commutes_on_single
      (k := k) (G := G) H x

/-- Helper for Theorem 17-17.2-4: in characteristic zero, transport Chapter `12` surjectivity to
the rationalized Grothendieck-group cyclic induction owner. -/
theorem cyclic_rationalized_induction_lsum_surjective_of_charZero [CharZero k] :
    Function.Surjective (cyclic_rationalized_induction_lsum (k := k) (G := G)) := by
  -- Transport Chapter `12` Artin induction surjectivity across the source and target
  -- Grothendieck-character linear equivalences.
  let eV :=
    cyclic_rationalized_finiteRepGrothendieckCharacterSourceEquiv (k := k) (G := G)
  let eW :=
    rationalized_finiteRepGrothendieckCharacterOwnerLinearEquiv (k := k) G
  let g :
      (Π₀ H : { J : Subgroup G // IsCyclic J }, ℚ ⊗R[k](H.1)) →ₗ[ℚ]
        ℚ ⊗R[k](G) :=
    cyclicSubgroupInduction (A := ℚ) k G
  have hconj :
      eW.toLinearMap.comp
          (cyclic_rationalized_induction_lsum k G) =
        g.comp
          eV.toLinearMap := by
    simpa [eV, eW] using
      rationalized_finiteRepGrothendieckCharacter_cyclic_induction_commutes
        (k := k) (G := G)
  have hg : Function.Surjective g := by
    simpa [g] using cyclicSubgroupInductionOverField_surjective (K := k) (G := G)
  intro z
  rcases hg (eW z) with ⟨v, hv⟩
  refine ⟨eV.symm v, ?_⟩
  -- Apply the conjugation identity to a Chapter `12` preimage and then cancel the target-side
  -- Grothendieck-character equivalence.
  apply eW.injective
  calc
    eW ((cyclic_rationalized_induction_lsum k G) (eV.symm v)) = g (eV (eV.symm v)) := by
      simpa using LinearMap.congr_fun hconj (eV.symm v)
    _ = g v := by
      simp
    _ = eW z := hv

end OrdinaryRow

end Representation
