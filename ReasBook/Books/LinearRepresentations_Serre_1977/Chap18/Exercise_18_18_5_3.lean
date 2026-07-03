import Mathlib
import LinearRepresentations_Serre_1977.Chap08.Proposition_8_8_3_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace Representation

section

local notation "S4" => Equiv.Perm (Fin 4)
local notation "S3" => Equiv.Perm (Fin 3)

/-- Helper for Exercise 18-18.5-3: the symmetric group on four letters has order `24`. -/
lemma s4_card : Nat.card S4 = 24 := by
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]

/-- Helper for Exercise 18-18.5-3: a normal subgroup of `S₄` with quotient isomorphic to `S₃`
has order `4`, hence is a `2`-group. -/
lemma normal_subgroup_isPGroup_two_of_quotient_equiv_s3
    (N : Subgroup S4) [N.Normal] (hS3 : Nonempty (S4 ⧸ N ≃* S3)) :
    IsPGroup 2 N := by
  rcases hS3 with ⟨e⟩
  -- The quotient equivalence identifies `|S₄ / N|` with `|S₃| = 6`.
  have hquot : Nat.card (S4 ⧸ N) = 6 := by
    simpa [Nat.card_eq_fintype_card, Fintype.card_perm] using Nat.card_congr e.toEquiv
  -- The subgroup index formula then forces `|N| = 24 / 6 = 4`.
  have hmul : 24 = 6 * Nat.card N := by
    simpa [s4_card, hquot] using Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have hcard : Nat.card N = 4 := by
    omega
  exact IsPGroup.of_card (show Nat.card N = 2 ^ 2 by simpa [pow_two] using hcard)

/-- Helper for Exercise 18-18.5-3: precomposing an irreducible representation with a group
equivalence preserves irreducibility. -/
lemma isIrreducible_comp_of_mulEquiv_local
    {K : Type*} [Field K] {G : Type*} [Group G] {G₁ : Type*} [Group G₁]
    {W : Type*} [AddCommGroup W] [Module K W]
    (e : G ≃* G₁) (σ : Representation K G₁ W) [σ.IsIrreducible] :
    Representation.IsIrreducible (σ.comp e.toMonoidHom) := by
  classical
  letI : Nontrivial (Subrepresentation (σ.comp e.toMonoidHom)) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro h
    have h' : (⊥ : Subrepresentation σ) = ⊤ := by
      apply Subrepresentation.toSubmodule_injective
      simpa using congrArg Subrepresentation.toSubmodule h
    exact IsSimpleOrder.bot_ne_top h'
  refine IsSimpleOrder.of_forall_eq_top ?_
  intro W' hW'
  let W'' : Subrepresentation σ :=
    { toSubmodule := W'.toSubmodule
      apply_mem_toSubmodule := by
        intro g x hx
        simpa using W'.apply_mem_toSubmodule (e.symm g) hx }
  have hW''_ne_bot : W'' ≠ ⊥ := by
    intro hW''
    apply hW'
    apply Subrepresentation.toSubmodule_injective
    simpa [W''] using congrArg Subrepresentation.toSubmodule hW''
  have hW''_top : W'' = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top W'').resolve_left hW''_ne_bot
  apply Subrepresentation.toSubmodule_injective
  simpa [W''] using congrArg Subrepresentation.toSubmodule hW''_top

/-- Helper for Exercise 18-18.5-3: quotienting by a normal subgroup that acts trivially preserves
irreducibility because the quotient representation has the same invariant subspaces. -/
lemma isIrreducible_of_ofQuotient_of_isTrivial
    {K : Type*} [Field K] {G : Type*} [Group G] {W : Type*} [AddCommGroup W] [Module K W]
    (σ : Representation K G W) (S : Subgroup G) [S.Normal]
    [Representation.IsTrivial (σ.comp S.subtype)] [σ.IsIrreducible] :
    Representation.IsIrreducible (σ.ofQuotient S) := by
  classical
  letI : Nontrivial (Subrepresentation (σ.ofQuotient S)) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro h
    have h' : (⊥ : Subrepresentation σ) = ⊤ := by
      apply Subrepresentation.toSubmodule_injective
      simpa using congrArg Subrepresentation.toSubmodule h
    exact IsSimpleOrder.bot_ne_top h'
  refine IsSimpleOrder.of_forall_eq_top ?_
  intro W' hW'
  let W'' : Subrepresentation σ :=
    { toSubmodule := W'.toSubmodule
      apply_mem_toSubmodule := by
        intro g x hx
        simpa using W'.apply_mem_toSubmodule (g : G ⧸ S) hx }
  have hW''_ne_bot : W'' ≠ ⊥ := by
    intro hW''
    apply hW'
    apply Subrepresentation.toSubmodule_injective
    simpa [W''] using congrArg Subrepresentation.toSubmodule hW''
  have hW''_top : W'' = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top W'').resolve_left hW''_ne_bot
  apply Subrepresentation.toSubmodule_injective
  simpa [W''] using congrArg Subrepresentation.toSubmodule hW''_top

/-- Helper for Exercise 18-18.5-3: a normal `p`-subgroup acts trivially on every irreducible
representation in characteristic `p`. -/
lemma isTrivial_restrict_normal_pSubgroup_of_isIrreducible
    {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [CharP K p]
    {G : Type*} [Group G] [Finite G] {W : Type*} [AddCommGroup W] [Module K W]
    (ρ : Representation K G W) [ρ.IsIrreducible]
    (N : Subgroup G) [N.Normal] (hN : IsPGroup p N) :
    Representation.IsTrivial (ρ.comp N.subtype) := by
  classical
  let ρN : Representation K N W := ρ.comp N.subtype
  letI : Nontrivial W := by
    by_contra hW
    haveI : Subsingleton W := not_nontrivial_iff_subsingleton.mp hW
    exact (show (⊥ : Subrepresentation ρ) ≠ ⊤ from IsSimpleOrder.bot_ne_top) <| by
      apply Subrepresentation.toSubmodule_injective
      ext x
      constructor
      · intro _
        trivial
      · intro _
        simpa using (show x = 0 from Subsingleton.elim x 0)
  let U : Subrepresentation ρ :=
    { toSubmodule := ρN.invariants
      apply_mem_toSubmodule := by
        intro g x hx
        rw [ρN.mem_invariants] at hx ⊢
        intro n
        have hconj : g⁻¹ * (n : G) * g ∈ N :=
          Subgroup.Normal.conj_mem' inferInstance (n : G) n.2 g
        have hxconj : ρ (g⁻¹ * (n : G) * g) x = x := hx ⟨g⁻¹ * (n : G) * g, hconj⟩
        calc
          ρ (n : G) (ρ g x) = ρ ((n : G) * g) x := by
            simp [map_mul]
          _ = ρ (g * (g⁻¹ * (n : G) * g)) x := by
            simp [mul_assoc]
          _ = ρ g (ρ (g⁻¹ * (n : G) * g) x) := by
            simp [map_mul]
          _ = ρ g x := by rw [hxconj] }
  have hU_ne_bot : U ≠ ⊥ := by
    intro hU
    exact
      ((invariants_ne_bot_of_isPGroup_charP (ρ := ρN) hN) <|
        by simpa [U] using congrArg Subrepresentation.toSubmodule hU)
  have hU_top : U = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top U).resolve_left hU_ne_bot
  refine ⟨fun n ↦ ?_⟩
  ext x
  have hxU : x ∈ U.toSubmodule := by
    rw [hU_top]
    exact Submodule.mem_top
  have hx : x ∈ ρN.invariants := by
    simpa [U] using hxU
  exact (ρN.mem_invariants x).1 hx n

/-- Helper for Exercise 18-18.5-3: after descending along `N`, inflating back through the quotient
map and the chosen quotient equivalence recovers the original representation. -/
lemma quotient_inflation_through_equiv_eq_original
    {k : Type u} [Field k] {V : Type u} [AddCommGroup V] [Module k V]
    (N : Subgroup S4) [N.Normal] (e : S4 ⧸ N ≃* S3)
    (ρ : Representation k S4 V) [IsTrivial (ρ.comp N.subtype)] :
    ρ = (((ρ.ofQuotient N).comp e.symm.toMonoidHom).comp
      (e.toMonoidHom.comp (QuotientGroup.mk' N))) := by
  -- The quotient model acts by the class of `g`, and the chosen equivalence cancels immediately.
  ext g x
  simp [Representation.ofQuotient_coe_apply]

-- Domain-style sampling for this item:
-- * `Representation.IsTrivial` is the canonical owner for the statement that a subgroup acts
--   trivially after restriction.
-- * `Representation.ofQuotient` is the canonical owner abstraction for descending a
--   representation through a normal subgroup on which it acts trivially.
-- * `Rep.resOfQuotientIso` is the canonical bridge saying that descending along `N` and then
--   restricting back along `S₄ → S₄ ⧸ N` recovers the original representation.
-- * `Representation.IsIrreducible` is the owner property transported across the chosen quotient
--   isomorphism `S₄ ⧸ N ≃ S₃`; in part `(2)` the witness is the internal canonical transport
--   `(ρ.ofQuotient N).comp e.symm.toMonoidHom`, not a separate public owner.
--
-- Layer triage:
-- * `source-facing`: the triviality of the restricted `N`-action and the inflation description of
--   the given irreducible `S₄`-representation.
-- * `core/canonical`: `IsTrivial (ρ.comp N.subtype)` and the descended quotient representation
--   `ρ.ofQuotient N`.
-- * `bridge/view`: `Rep.resOfQuotientIso` for the quotient descent together with the internal
--   transport of `ρ.ofQuotient N` across `e : S₄ ⧸ N ≃* S₃`.
--
-- Primitive data versus derived API:
-- the primitive inputs are the irreducible representation `ρ` and the normal subgroup `N`; in
-- part `(1)` the quotient condition is intrinsic existence data `Nonempty (S₄ ⧸ N ≃* S₃)`, while
-- part `(2)` additionally uses a chosen isomorphism `e` to identify the quotient with `S₃`. The
-- transported `S₃`-representation is derived canonically from `ρ.ofQuotient N`, but that owner
-- depends on the internal triviality instance from part `(1)`, so the public theorem should stay
-- source-facing and assert existence of the irreducible inflated `S₃`-representation while
-- discharging the quotient descent internally instead of naming a one-off descended witness.
-- Because `S₄` is finite,
-- `FiniteDimensional k V` is itself derived from
-- `ρ.IsIrreducible` via `IsIrreducible.finiteDimensional_of_finite ρ`, so it should not remain
-- primitive public data.

-- Proof sketch: realize an irreducible characteristic-`2` representation of `S₄` over the prime
-- field via Exercise `18-18.5-2`, compare the resulting action of the normal subgroup `N` with the
-- known quotient existence `Nonempty (S₄ ⧸ N ≃* S₃)`, and use irreducibility to force the
-- restricted action on `N` to be trivial. Finite-dimensionality is derived internally from
-- `IsIrreducible.finiteDimensional_of_finite ρ`.
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {V : Type u} [AddCommGroup V] [Module k V]

/-- Exercise 18-18.5-3 (1): if `N` is a normal subgroup of `S₄` with quotient isomorphic to
`S₃`, then `N` acts trivially on every irreducible representation of `S₄` over an algebraically
closed field of characteristic `2`. Finite-dimensionality is automatic here. -/
theorem symmetricGroup_four_irreducible_charTwo_normalSubgroup_isTrivial
    (N : Subgroup S4) [N.Normal] (hS3 : Nonempty (S4 ⧸ N ≃* S3))
    (ρ : Representation k S4 V) [ρ.IsIrreducible] :
    IsTrivial (ρ.comp N.subtype) := by
  let _ : IsAlgClosed k := inferInstance
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- The quotient hypothesis forces `N` to be a normal `2`-subgroup of `S₄`.
  have hN : IsPGroup 2 N := normal_subgroup_isPGroup_two_of_quotient_equiv_s3 N hS3
  -- Irreducibility in characteristic `2` then makes the restricted `N`-action trivial.
  exact isTrivial_restrict_normal_pSubgroup_of_isIrreducible (ρ := ρ) N hN

-- Proof sketch: apply part `(1)` to descend `ρ` to a representation of `S₄ ⧸ N` via
-- `Representation.ofQuotient ρ N`; the canonical bridge `Rep.resOfQuotientIso` identifies the
-- resulting inflation along `S₄ → S₄ ⧸ N` with the original representation. Transport that
-- descended representation across the chosen isomorphism `e : S₄ ⧸ N ≃* S₃` and use it only
-- internally as the existential witness. Again, finite-dimensionality is derived from
-- `IsIrreducible.finiteDimensional_of_finite ρ`.

/-- Exercise 18-18.5-3 (2): every irreducible representation of `S₄` in characteristic `2` is the
inflation, along `S₄ → S₄ ⧸ N ≃ S₃`, of an irreducible representation of `S₃`. The descended
witness is the internal canonical transport of `ρ.ofQuotient N` across `e`.
Finite-dimensionality is automatic here. -/
theorem symmetricGroup_four_irreducible_charTwo_eq_inflation_of_symmetricGroup_three
    (N : Subgroup S4) [N.Normal] (e : S4 ⧸ N ≃* S3)
    (ρ : Representation k S4 V) [ρ.IsIrreducible] :
    ∃ σ : Representation k S3 V,
      σ.IsIrreducible ∧ ρ = σ.comp (e.toMonoidHom.comp (QuotientGroup.mk' N)) := by
  -- Part `(1)` gives the canonical triviality needed to descend `ρ` to `S₄ / N`.
  letI : IsTrivial (ρ.comp N.subtype) :=
    symmetricGroup_four_irreducible_charTwo_normalSubgroup_isTrivial N ⟨e⟩ ρ
  let τ : Representation k (S4 ⧸ N) V := ρ.ofQuotient N
  let σ : Representation k S3 V := τ.comp e.symm.toMonoidHom
  refine ⟨σ, ?_, ?_⟩
  · -- Irreducibility descends to the quotient and then transports across `e`.
    letI : τ.IsIrreducible := isIrreducible_of_ofQuotient_of_isTrivial ρ N
    simpa [σ, τ] using isIrreducible_comp_of_mulEquiv_local e.symm τ
  · -- Inflating the descended `S₃`-representation back along `S₄ → S₄ / N ≃ S₃` recovers `ρ`.
    simpa [σ, τ] using quotient_inflation_through_equiv_eq_original (N := N) (e := e) (ρ := ρ)

end

end Representation
