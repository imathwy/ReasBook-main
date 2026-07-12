import Mathlib
import LinearRepresentations_Serre_1977.Chap08.Corollary_8_8_3_8
import LinearRepresentations_Serre_1977.Chap07.Exercise_7_7_2_4
import LinearRepresentations_Serre_1977.Chap08.Exercise_8_8_2_3
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_5_1
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_5_2.LinearCharacters
import LinearRepresentations_Serre_1977.RepresentationTheory.RealizableOver

-- The Fong–Swan import chain (via `Serre.Chap18.Exercise_18_18_5_1`) brings the global instance
-- `Field.henselian` (every field is a Henselian local ring) into scope.  That instance makes
-- type-class search diverge — even the trivial goal `Module F F` for a field `F` loops.  The
-- upstream file `Exercise_18_18_5_1` already disables it locally, but `attribute [-instance]`
-- removals do not propagate to importers, so we must repeat it here.  This removes the divergent
-- instance; it is not a heartbeat mask.
attribute [-instance] Field.henselian

noncomputable section

universe u

namespace Representation

section

local notation "S3" => Equiv.Perm (Fin 3)
local notation "S4" => Equiv.Perm (Fin 4)
local notation "A4" => alternatingGroup (Fin 4)
local notation "V4" => alternatingGroup.kleinFour (Fin 4)
local notation "V4InS4" => Subgroup.map (Subgroup.subtype A4) V4

local instance : (V4InS4).Normal := _root_.s4DoubleTranspositionKleinFour_normal

variable {k : Type u} [Field k]
variable {V : Type u} [AddCommGroup V] [Module k V]

/-- Helper for Exercise 18-18.5-2: precomposing an irreducible representation with a group
equivalence preserves irreducibility over any field. -/
private lemma isIrreducible_comp_of_mulEquiv_local
    {F : Type*} [Field F] {G H : Type*} [Group G] [Group H]
    {W : Type*} [AddCommGroup W] [Module F W]
    (e : G ≃* H) (σ : Representation F H W) [σ.IsIrreducible] :
    Representation.IsIrreducible (σ.comp e.toMonoidHom) := by
  classical
  -- Transport subrepresentations across the group equivalence and reuse simplicity of `σ`.
  letI : Nontrivial (Subrepresentation (σ.comp e.toMonoidHom)) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro h
    have h' : (⊥ : Subrepresentation σ) = ⊤ := by
      apply Subrepresentation.toSubmodule_injective
      simpa using congrArg Subrepresentation.toSubmodule h
    exact IsSimpleOrder.bot_ne_top h'
  refine IsSimpleOrder.of_forall_eq_top ?_
  intro W hW
  let W' : Subrepresentation σ :=
    { toSubmodule := W.toSubmodule
      apply_mem_toSubmodule := by
        intro h x hx
        simpa using W.apply_mem_toSubmodule (e.symm h) hx }
  have hW'_ne_bot : W' ≠ ⊥ := by
    intro hW'
    apply hW
    apply Subrepresentation.toSubmodule_injective
    simpa [W'] using congrArg Subrepresentation.toSubmodule hW'
  have hW'_top : W' = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top W').resolve_left hW'_ne_bot
  apply Subrepresentation.toSubmodule_injective
  simpa [W'] using congrArg Subrepresentation.toSubmodule hW'_top

/-- Helper for Exercise 18-18.5-2: precomposing an irreducible representation with a surjective
group homomorphism preserves irreducibility because every invariant subspace for the pullback is
already invariant under the target group action. -/
private lemma isIrreducible_comp_of_surjective_md
    {F : Type*} [Field F] {G H : Type*} [Group G] [Group H]
    {W : Type*} [AddCommGroup W] [Module F W]
    (f : G →* H) (hf : Function.Surjective f)
    (σ : Representation F H W) [σ.IsIrreducible] :
    Representation.IsIrreducible (σ.comp f) := by
  classical
  -- A subspace is stable under `σ.comp f` iff it is stable under `σ`, because `f` is surjective.
  letI : Nontrivial (Subrepresentation (σ.comp f)) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro h
    have h' : (⊥ : Subrepresentation σ) = ⊤ := by
      apply Subrepresentation.toSubmodule_injective
      simpa using congrArg Subrepresentation.toSubmodule h
    exact IsSimpleOrder.bot_ne_top h'
  refine IsSimpleOrder.of_forall_eq_top ?_
  intro U hU
  let U' : Subrepresentation σ :=
    { toSubmodule := U.toSubmodule
      apply_mem_toSubmodule := by
        intro h x hx
        rcases hf h with ⟨g, rfl⟩
        simpa using U.apply_mem_toSubmodule g hx }
  have hU'_ne_bot : U' ≠ ⊥ := by
    intro hU'
    apply hU
    apply Subrepresentation.toSubmodule_injective
    simpa [U'] using congrArg Subrepresentation.toSubmodule hU'
  have hU'_top : U' = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top U').resolve_left hU'_ne_bot
  apply Subrepresentation.toSubmodule_injective
  simpa [U'] using congrArg Subrepresentation.toSubmodule hU'_top

/-- Helper for Exercise 18-18.5-2: quotienting by a normal subgroup that acts trivially preserves
irreducibility over an arbitrary field. -/
lemma isIrreducible_of_quotient_of_isTrivial_overField
    {F : Type*} [Field F] {G : Type*} [Group G]
    {W : Type*} [AddCommGroup W] [Module F W]
    (σ : Representation F G W) (N : Subgroup G) [N.Normal]
    [Representation.IsTrivial (σ.comp N.subtype)] [σ.IsIrreducible] :
    Representation.IsIrreducible (σ.ofQuotient N) := by
  classical
  letI : Nontrivial (Subrepresentation (σ.ofQuotient N)) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro h
    have h' : (⊥ : Subrepresentation σ) = ⊤ := by
      apply Subrepresentation.toSubmodule_injective
      simpa using congrArg Subrepresentation.toSubmodule h
    exact IsSimpleOrder.bot_ne_top h'
  refine IsSimpleOrder.of_forall_eq_top ?_
  intro W hW
  let W' : Subrepresentation σ :=
    { toSubmodule := W.toSubmodule
      apply_mem_toSubmodule := by
        intro g x hx
        simpa using W.apply_mem_toSubmodule (g : G ⧸ N) hx }
  have hW'_ne_bot : W' ≠ ⊥ := by
    intro hW'
    apply hW
    apply Subrepresentation.toSubmodule_injective
    simpa [W'] using congrArg Subrepresentation.toSubmodule hW'
  have hW'_top : W' = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top W').resolve_left hW'_ne_bot
  apply Subrepresentation.toSubmodule_injective
  simpa [W'] using congrArg Subrepresentation.toSubmodule hW'_top

/-- Helper for Exercise 18-18.5-2: a normal `p`-subgroup acts trivially on every irreducible
representation in characteristic `p`. -/
private lemma isTrivial_restrict_normal_pSubgroup_of_isIrreducible_md
    {p : ℕ} [Fact p.Prime] [CharP k p] {G : Type*} [Group G] [Finite G]
    (ρ : Representation k G V) [ρ.IsIrreducible]
    (N : Subgroup G) [N.Normal] (hN : IsPGroup p N) :
    Representation.IsTrivial (ρ.comp N.subtype) := by
  classical
  let ρN : Representation k N V := ρ.comp N.subtype
  letI : Nontrivial V := by
    by_contra hV
    haveI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
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
    -- The restricted `p`-group action has a nonzero invariant vector.
    intro hU
    exact
      ((invariants_ne_bot_of_isPGroup_charP (ρ := ρN) hN) <|
        by simpa [U] using congrArg Subrepresentation.toSubmodule hU)
  have hU_top : U = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top U).resolve_left hU_ne_bot
  -- Irreducibility forces the invariant subspace to be all of `V`.
  refine ⟨fun n ↦ ?_⟩
  ext x
  have hxU : x ∈ U.toSubmodule := by
    rw [hU_top]
    exact Submodule.mem_top
  have hx : x ∈ ρN.invariants := by
    simpa [U] using hxU
  exact (ρN.mem_invariants x).1 hx n

/-- Helper for Exercise 18-18.5-2: the normal Klein four subgroup of double transpositions has
cardinality `4`. -/
lemma s4_v4_card : Nat.card V4InS4 = 4 := by
  -- Compare with the standard Klein four subgroup inside `A₄`.
  rw [show Nat.card V4InS4 = Nat.card V4 by
    exact Nat.card_congr
      (Subgroup.equivMapOfInjective V4
        (Subgroup.subtype A4) (Subgroup.subtype_injective _)).toEquiv.symm]
  simpa using
    alternatingGroup.kleinFour_card_of_card_eq_four (show Nat.card (Fin 4) = 4 by simp)

/-- Helper for Exercise 18-18.5-2: the normal Klein four subgroup of `S₄` is a `2`-group. -/
lemma s4_v4_isPGroup_two : IsPGroup 2 V4InS4 := by
  -- The subgroup has order `4 = 2²`.
  exact IsPGroup.of_card (show Nat.card V4InS4 = 2 ^ 2 by simpa [pow_two] using s4_v4_card)

variable [IsAlgClosed k]

/-- Helper for Exercise 18-18.5-2: in characteristic `2`, every irreducible `S₄`-representation
descends along `S₄ / V₄ ≃ S₃`. -/
lemma s4_char_two_descends_to_s3
    (hchar2 : ringChar k = 2) (ρ : Representation k S4 V) [ρ.IsIrreducible] :
    ∃ σ : Representation k (Equiv.Perm (Fin 3)) V,
      σ.IsIrreducible ∧ ρ = σ.comp s4_quotient_hom_s3 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : CharP k 2 := ringChar.of_eq hchar2
  let N : Subgroup S4 := V4InS4
  letI : Representation.IsTrivial (ρ.comp N.subtype) :=
    isTrivial_restrict_normal_pSubgroup_of_isIrreducible_md
      (ρ := ρ) N s4_v4_isPGroup_two
  let τ : Representation k (S4 ⧸ V4InS4) V := ρ.ofQuotient V4InS4
  let σ : Representation k (Equiv.Perm (Fin 3)) V :=
    τ.comp s4_quotient_by_klein_four_equiv_s3.symm.toMonoidHom
  refine ⟨σ, ?_, ?_⟩
  · have hτ : τ.IsIrreducible := by
      simpa [τ] using
        (isIrreducible_of_quotient_of_isTrivial_overField (σ := ρ) (N := V4InS4))
    letI : τ.IsIrreducible := hτ
    simpa [σ] using
      (isIrreducible_comp_of_mulEquiv_local
        s4_quotient_by_klein_four_equiv_s3.symm τ)
  · -- Descending to the quotient and inflating back recovers the original action.
    ext g x
    simpa [σ, s4_quotient_hom_s3, τ] using
      (Representation.ofQuotient_coe_apply (ρ := ρ) (S := N) g x).symm

/-- Helper for Exercise 18-18.5-2: the characteristic-`2` branch reduces entirely to the
descended `S₃`-representation after the quotient-descent step. -/
lemma s4_char_two_realizable_of_descended
    (ρ : Representation k S4 V)
    {σ : Representation k (Equiv.Perm (Fin 3)) V}
    (hσ : IsRealizableOver ↥(⊥ : Subfield k) σ)
    (hρσ : ρ = σ.comp s4_quotient_hom_s3) :
    IsRealizableOver ↥(⊥ : Subfield k) ρ := by
  -- The only remaining work is the descended `S₃` realizability statement.
  subst hρσ
  rcases hσ with ⟨W₀, _, _, _, σ₀, ⟨e₀⟩⟩
  refine ⟨W₀, inferInstance, inferInstance, inferInstance, σ₀.comp s4_quotient_hom_s3, ?_⟩
  -- Precomposition with the quotient map preserves the underlying linear equivalence.
  refine ⟨Representation.Equiv.mk e₀.toLinearEquiv ?_⟩
  intro g
  simpa [Representation.scalarExtension] using e₀.isIntertwining' (s4_quotient_hom_s3 g)

/-- Helper for Exercise 18-18.5-2: on `2`-regular elements of `S₃`, the ordinary sign character
collapses to the trivial character. This is the slot identification used in the characteristic-`2`
descent. -/
lemma s3_sign_character_two_regular_eq_trivial
    (s : { t : S3 // IsPRegular 2 t }) :
    (s3_sign_representation ℂ).character s.1 =
      (Representation.trivial ℂ S3 ℂ).character s.1 := by
  rcases s with ⟨g, hg⟩
  have htrace :
      LinearMap.trace ℂ ℂ ((LinearMap.lsmul ℂ ℂ) 1) = 1 := by
    -- Scalar multiplication by `1` is the identity on the one-dimensional carrier.
    rw [show LinearMap.lsmul ℂ ℂ 1 = (1 : ℂ →ₗ[ℂ] ℂ) by
      ext x
      simp [LinearMap.lsmul_apply]]
    simpa using (LinearMap.trace_id (R := ℂ) (M := ℂ))
  -- A `2`-regular permutation has odd order, so its sign cannot have order `2`.
  have hg_regular : ¬ 2 ∣ orderOf g := by
    rw [isPRegular_iff_not_dvd_orderOf] at hg
    exact hg
  have hsign_dvd_two : orderOf (Equiv.Perm.sign g) ∣ 2 := by
    exact orderOf_dvd_of_pow_eq_one (by simp : Equiv.Perm.sign g ^ 2 = 1)
  have hsign_one : Equiv.Perm.sign g = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hsign_dvd_two with hsign_order | hsign_order
    · exact orderOf_eq_one_iff.mp hsign_order
    · exfalso
      have hmap : orderOf (Equiv.Perm.sign g) ∣ orderOf g := orderOf_map_dvd Equiv.Perm.sign g
      exact hg_regular <| by simpa [hsign_order] using hmap
  have hsign_cast : s3_sign_character ℂ g = 1 := by
    change (Units.map (Int.castRingHom ℂ).toMonoidHom) (Equiv.Perm.sign g) = 1
    simp [hsign_one]
  -- Reduce both characters to the one-dimensional trace computation at scalar `1`.
  simp [s3_sign_representation, s3_sign_character, unitCharacterRepresentation_character_apply,
    hsign_one, hsign_cast, Representation.character, Representation.trivial, htrace]

end

end Representation
