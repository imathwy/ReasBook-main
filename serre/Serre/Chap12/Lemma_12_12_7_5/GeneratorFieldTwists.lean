import Serre.Chap12.Lemma_12_12_7_5.CyclicIrreducibleBridge

open Representation
open scoped Pointwise Representation

noncomputable section

universe u v

section Representation

variable {G : Type u} [Group G] [Finite G]
variable {L : Type v} [Field L] [NumberField L]
variable [IsCyclotomicExtension {Monoid.exponent G} ℚ L]
variable (K : IntermediateField ℚ L) (x : G)

/-- Helper for Lemma 12-12.7-5: a private `Fintype` witness for the finite group `G`. -/
private def instFintypeLemma121275GeneratorFieldTwists : Fintype G :=
  Fintype.ofFinite G

attribute [local instance] instFintypeLemma121275GeneratorFieldTwists

local notation "ΓK" => Γ[K](G)
local notation "C" => Subgroup.zpowers x

/-- Helper for Lemma 12-12.7-5: the distinguished generator of the cyclic subgroup
`C = ⟨x⟩`. -/
abbrev zpowers_generator : C :=
  ⟨x, Subgroup.mem_zpowers x⟩

/-- Helper for Lemma 12-12.7-5: a linear character of `C = ⟨x⟩` is determined by its value on the
distinguished generator `x`. -/
private theorem linear_character_eq_of_generator_eq
    (β γ : C →* (AlgebraicClosure K)ˣ)
    (hgen : β (zpowers_generator (x := x)) = γ (zpowers_generator (x := x))) :
    β = γ := by
  ext c
  rcases Subgroup.mem_zpowers_iff.mp c.2 with ⟨n, hn⟩
  have hc : c = (zpowers_generator (x := x)) ^ n := by
    apply Subtype.ext
    simpa using hn.symm
  rw [hc, map_zpow, map_zpow]
  exact congrArg
    (fun z : (AlgebraicClosure K)ˣ ↦ ((z ^ n : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)) hgen

/-- Helper for Lemma 12-12.7-5: the `Γ_K`-power action on the cyclic subgroup `C = ⟨x⟩` is a
monoid endomorphism. -/
private def zpowers_powerMonoidHom (t : ΓK) : C →* C where
  toFun c := c ^ galoisPowerExponentUnit (t : (ZMod (Monoid.exponent G))ˣ)
  map_one' := by
    simp
  map_mul' c d := by
    apply Subtype.ext
    rcases Subgroup.mem_zpowers_iff.mp c.2 with ⟨m, hm⟩
    rcases Subgroup.mem_zpowers_iff.mp d.2 with ⟨n, hn⟩
    change
      (((c : G) * (d : G)) ^ galoisPowerExponentUnit (t : (ZMod (Monoid.exponent G))ˣ)) =
        ((c : G) ^ galoisPowerExponentUnit (t : (ZMod (Monoid.exponent G))ˣ)) *
          ((d : G) ^ galoisPowerExponentUnit (t : (ZMod (Monoid.exponent G))ˣ))
    rw [← hm, ← hn]
    simpa using
      (Commute.zpow_zpow_self x m n).mul_pow
        (galoisPowerExponentUnit (t : (ZMod (Monoid.exponent G))ˣ))

/-- Helper for Lemma 12-12.7-5: twisting a linear character by a `Γ_K`-power map is just
precomposition with the corresponding endomorphism of `C`. -/
def linearCharacter_twist
    (β : C →* (AlgebraicClosure K)ˣ) (t : ΓK) : C →* (AlgebraicClosure K)ˣ :=
  β.comp (zpowers_powerMonoidHom (G := G) (K := K) (x := x) t)

/-- Helper for Lemma 12-12.7-5: evaluating the twisted linear character amounts to raising the
original character value to the corresponding `Γ_K`-power exponent. -/
private theorem linearCharacter_twist_apply
    (β : C →* (AlgebraicClosure K)ˣ) (t : ΓK) (c : C) :
    linearCharacter_twist (G := G) (K := K) (x := x) β t c =
      β c ^ galoisPowerExponentUnit (t : (ZMod (Monoid.exponent G))ˣ) := by
  simp [linearCharacter_twist, zpowers_powerMonoidHom, map_pow]

/-- Helper for Lemma 12-12.7-5: the twisted character sends the distinguished generator to the
corresponding `Γ_K`-power of the original generator value. -/
private theorem linearCharacter_twist_generator
    (β : C →* (AlgebraicClosure K)ˣ) (t : ΓK) :
    linearCharacter_twist (G := G) (K := K) (x := x) β t
        (zpowers_generator (x := x)) =
      β (zpowers_generator (x := x)) ^
        galoisPowerExponentUnit (t : (ZMod (Monoid.exponent G))ˣ) := by
  simpa using linearCharacter_twist_apply (G := G) (K := K) (x := x) β t
    (zpowers_generator (x := x))

/-- Helper for Lemma 12-12.7-5: the field generated over `K` by the value of a linear character
on the distinguished generator of `C = ⟨x⟩`. -/
abbrev generatorFieldOfLinearCharacter
    (β : C →* (AlgebraicClosure K)ˣ) : IntermediateField K (AlgebraicClosure K) :=
  IntermediateField.adjoin K {(((β (zpowers_generator (x := x)) : (AlgebraicClosure K)ˣ) :
      AlgebraicClosure K))}

/-- Helper for Lemma 12-12.7-5: equal generator values give the same generator field. -/
private theorem generatorFieldOfLinearCharacter_eq_of_generator_eq
    (β γ : C →* (AlgebraicClosure K)ˣ)
    (hgen : β (zpowers_generator (x := x)) = γ (zpowers_generator (x := x))) :
    generatorFieldOfLinearCharacter (K := K) (x := x) β =
      generatorFieldOfLinearCharacter (K := K) (x := x) γ := by
  simp [generatorFieldOfLinearCharacter, hgen]

/-- Helper for Lemma 12-12.7-5: adjoining a unit or adjoining a coprime power of that unit gives
the same simple intermediate field. -/
private theorem adjoin_unit_pow_eq_of_coprime
    (α : (AlgebraicClosure K)ˣ) {n : ℕ} (hcop : Nat.Coprime (orderOf α) n) :
    IntermediateField.adjoin K
        ({(((α ^ n : (AlgebraicClosure K)ˣ) : AlgebraicClosure K))} :
          Set (AlgebraicClosure K)) =
      IntermediateField.adjoin K
        ({(((α : (AlgebraicClosure K)ˣ) : AlgebraicClosure K))} :
          Set (AlgebraicClosure K)) := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_simple_le_iff]
    have hα_mem :
        (((α : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)) ∈
          IntermediateField.adjoin K
            ({(((α : (AlgebraicClosure K)ˣ) : AlgebraicClosure K))} :
              Set (AlgebraicClosure K)) :=
      IntermediateField.mem_adjoin_simple_self K (((α : (AlgebraicClosure K)ˣ) :
        AlgebraicClosure K))
    simpa using
      (IntermediateField.adjoin K
        ({(((α : (AlgebraicClosure K)ˣ) : AlgebraicClosure K))} :
          Set (AlgebraicClosure K))).pow_mem hα_mem n
  · rw [IntermediateField.adjoin_simple_le_iff]
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop.symm
    have hαn_mem :
        (((α ^ n : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)) ∈
          IntermediateField.adjoin K
            ({(((α ^ n : (AlgebraicClosure K)ˣ) : AlgebraicClosure K))} :
              Set (AlgebraicClosure K)) :=
      IntermediateField.mem_adjoin_simple_self K ((((α ^ n : (AlgebraicClosure K)ˣ) :
        AlgebraicClosure K)))
    have hpow_mem :
        ((((α ^ n : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) ^ m)) ∈
          IntermediateField.adjoin K
            ({(((α ^ n : (AlgebraicClosure K)ˣ) : AlgebraicClosure K))} :
              Set (AlgebraicClosure K)) := by
      simpa using
        (IntermediateField.adjoin K
        ({(((α ^ n : (AlgebraicClosure K)ˣ) : AlgebraicClosure K))} :
          Set (AlgebraicClosure K))).pow_mem hαn_mem m
    have hpow :
        ((((α ^ n : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) ^ m)) =
          (((α : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)) := by
      simpa using congrArg (fun u : (AlgebraicClosure K)ˣ ↦ ((u : (AlgebraicClosure K)))) hm
    rw [← hpow]
    exact hpow_mem

/-- Helper for Lemma 12-12.7-5: twisting a linear character by a `Γ_K`-power does not change the
simple field generated by the distinguished value `β(x)`. -/
theorem generatorFieldOfLinearCharacter_twist_eq
    (β : C →* (AlgebraicClosure K)ˣ) (t : ΓK) :
    generatorFieldOfLinearCharacter (K := K) (x := x)
        (linearCharacter_twist (G := G) (K := K) (x := x) β t) =
      generatorFieldOfLinearCharacter (K := K) (x := x) β := by
  let α : (AlgebraicClosure K)ˣ := β (zpowers_generator (x := x))
  let n : ℕ := galoisPowerExponentUnit (t : (ZMod (Monoid.exponent G))ˣ)
  have hcop_x :
      Nat.Coprime (orderOf x) n :=
    (Nat.Coprime.of_dvd_right (Monoid.order_dvd_exponent x)
      (ZMod.val_coe_unit_coprime (t : (ZMod (Monoid.exponent G))ˣ))).symm
  have hα_pow : α ^ orderOf x = 1 := by
    have hxpow : (zpowers_generator (x := x)) ^ orderOf x = 1 := by
      apply Subtype.ext
      simpa using pow_orderOf_eq_one x
    rw [show α = β (zpowers_generator (x := x)) by rfl, ← map_pow, hxpow, map_one]
  have hα_cop :
      Nat.Coprime (orderOf α) n := by
    have hα_dvd : orderOf α ∣ orderOf x := orderOf_dvd_of_pow_eq_one hα_pow
    exact hcop_x.of_dvd_left hα_dvd
  dsimp [generatorFieldOfLinearCharacter]
  rw [linearCharacter_twist_generator (G := G) (K := K) (x := x) β t]
  exact adjoin_unit_pow_eq_of_coprime (K := K) α hα_cop

/-- Helper for Lemma 12-12.7-5: the underlying `K`-vector-space carrier of Serre's generator
field model attached to a linear character of `C = ⟨x⟩`. -/
abbrev generatorFieldCarrier
    (β : C →* (AlgebraicClosure K)ˣ) : Type v :=
  ↥(generatorFieldOfLinearCharacter (K := K) (x := x) β)

/-- Helper for Lemma 12-12.7-5: the equality of generator fields coming from a `Γ_K`-power twist
provides a canonical `K`-linear identification of the two carriers. -/
noncomputable def generatorField_twist_linearEquiv
    (β : C →* (AlgebraicClosure K)ˣ) (t : ΓK) :
    generatorFieldCarrier (K := K) (x := x)
        (linearCharacter_twist (G := G) (K := K) (x := x) β t) ≃ₗ[K]
      generatorFieldCarrier (K := K) (x := x) β :=
  (AlgEquiv.cast
    (R := K)
    (A := fun S : IntermediateField K (AlgebraicClosure K) => ↥S)
    (generatorFieldOfLinearCharacter_twist_eq
      (G := G) (K := K) (x := x) β t)).toLinearEquiv

/-- Helper for Lemma 12-12.7-5: the carrier identification is exactly the cast-induced algebra
equivalence coming from the twist-field equality. -/
private theorem generatorField_twist_linearEquiv_eq_cast
    (β : C →* (AlgebraicClosure K)ˣ) (t : ΓK) :
    generatorField_twist_linearEquiv (G := G) (K := K) (x := x) β t =
      (AlgEquiv.cast
        (R := K)
        (A := fun S : IntermediateField K (AlgebraicClosure K) => ↥S)
        (generatorFieldOfLinearCharacter_twist_eq
          (G := G) (K := K) (x := x) β t)).toLinearEquiv := rfl

/-- Helper for Lemma 12-12.7-5: the twist-field carrier identification is definitionally the
cast-induced linear equivalence. -/
theorem generatorField_twist_linearEquiv_eq_cast_public
    (β : C →* (AlgebraicClosure K)ˣ) (t : ΓK) :
    generatorField_twist_linearEquiv (G := G) (K := K) (x := x) β t =
      (AlgEquiv.cast
        (R := K)
        (A := fun S : IntermediateField K (AlgebraicClosure K) => ↥S)
        (generatorFieldOfLinearCharacter_twist_eq
          (G := G) (K := K) (x := x) β t)).toLinearEquiv := by
  simpa using generatorField_twist_linearEquiv_eq_cast (G := G) (K := K) (x := x) β t

/-- Helper for Lemma 12-12.7-5: if two `Γ_K`-powers agree on the distinguished generator `x`,
then they induce the same twist of any linear character of `C = ⟨x⟩`. -/
private theorem linearCharacter_twist_eq_of_generator_power_eq
    (β : C →* (AlgebraicClosure K)ˣ) {t u : ΓK}
    (hxu : (x ^ t : G) = x ^ u) :
    linearCharacter_twist (G := G) (K := K) (x := x) β t =
      linearCharacter_twist (G := G) (K := K) (x := x) β u := by
  apply linear_character_eq_of_generator_eq (K := K) (x := x)
  have hgen :
      (zpowers_powerMonoidHom (G := G) (K := K) (x := x) t)
          (zpowers_generator (x := x)) =
        (zpowers_powerMonoidHom (G := G) (K := K) (x := x) u)
          (zpowers_generator (x := x)) := by
    apply Subtype.ext
    simpa [zpowers_powerMonoidHom, pow_subgroup_eq_pow_nat] using hxu
  simpa [linearCharacter_twist] using congrArg β hgen

/-- Helper for Lemma 12-12.7-5: the simple generator field attached to a twisted linear character
depends only on the resulting `Γ_K`-power of the generator `x`. -/
private theorem generatorFieldOfLinearCharacter_twist_eq_of_generator_power_eq
    (β : C →* (AlgebraicClosure K)ˣ) {t u : ΓK}
    (hxu : (x ^ t : G) = x ^ u) :
    generatorFieldOfLinearCharacter (K := K) (x := x)
        (linearCharacter_twist (G := G) (K := K) (x := x) β t) =
      generatorFieldOfLinearCharacter (K := K) (x := x)
        (linearCharacter_twist (G := G) (K := K) (x := x) β u) := by
  rw [linearCharacter_twist_eq_of_generator_power_eq
    (G := G) (K := K) (x := x) β hxu]

/-- Helper for Lemma 12-12.7-5: if two `Γ_K`-power witnesses agree on the distinguished
generator, then they define the same twisted linear character on `C = ⟨x⟩`. -/
theorem linearCharacter_twist_eq_of_generator_power_eq_public
    (β : C →* (AlgebraicClosure K)ˣ) {t u : ΓK}
    (hxu : (x ^ t : G) = x ^ u) :
    linearCharacter_twist (G := G) (K := K) (x := x) β t =
      linearCharacter_twist (G := G) (K := K) (x := x) β u := by
  -- This exposes the witness-independence step as a reusable theorem for the later `P`-action.
  simpa using
    linearCharacter_twist_eq_of_generator_power_eq (G := G) (K := K) (x := x) β hxu

/-- Helper for Lemma 12-12.7-5: the generator field attached to a twisted linear character also
depends only on the resulting `Γ_K`-power of `x`. -/
theorem generatorFieldOfLinearCharacter_twist_eq_of_generator_power_eq_public
    (β : C →* (AlgebraicClosure K)ˣ) {t u : ΓK}
    (hxu : (x ^ t : G) = x ^ u) :
    generatorFieldOfLinearCharacter (K := K) (x := x)
        (linearCharacter_twist (G := G) (K := K) (x := x) β t) =
      generatorFieldOfLinearCharacter (K := K) (x := x)
        (linearCharacter_twist (G := G) (K := K) (x := x) β u) := by
  -- The field-level witness-independence follows from equality of the twisted characters.
  simpa using
    generatorFieldOfLinearCharacter_twist_eq_of_generator_power_eq
      (G := G) (K := K) (x := x) β hxu

/-- Helper for Lemma 12-12.7-5: every value of a linear character on `C = ⟨x⟩` lies in the field
generated by the value on the distinguished generator `x`. -/
theorem linear_character_value_mem_generatorField
    (β : C →* (AlgebraicClosure K)ˣ) (c : C) :
    (((β c : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)) ∈
      generatorFieldOfLinearCharacter (K := K) (x := x) β := by
  let xC : C := zpowers_generator (x := x)
  rcases Subgroup.mem_zpowers_iff.mp c.2 with ⟨n, hn⟩
  have hc : c = xC ^ n := by
    apply Subtype.ext
    simpa [xC] using hn.symm
  have hxC_mem :
      (((β xC : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)) ∈
        generatorFieldOfLinearCharacter (K := K) (x := x) β := by
    exact IntermediateField.subset_adjoin K _ (by simp [generatorFieldOfLinearCharacter, xC])
  have hzpow_mem :
      ((((β xC : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) ^ n)) ∈
        generatorFieldOfLinearCharacter (K := K) (x := x) β := by
    exact
      (generatorFieldOfLinearCharacter (K := K) (x := x) β).toSubfield.zpow_mem hxC_mem n
  rw [hc, map_zpow]
  simpa using hzpow_mem

/-- Helper for Lemma 12-12.7-5: every value of a `Γ_K`-power twist of a linear character still
lies in the original generator field, because the twist does not change that field. -/
theorem linearCharacter_twist_value_mem_generatorField_public
    (β : C →* (AlgebraicClosure K)ˣ) (t : ΓK) (c : C) :
    (((linearCharacter_twist (G := G) (K := K) (x := x) β t c :
        (AlgebraicClosure K)ˣ) : AlgebraicClosure K)) ∈
      generatorFieldOfLinearCharacter (K := K) (x := x) β := by
  rw [← generatorFieldOfLinearCharacter_twist_eq (G := G) (K := K) (x := x) β t]
  exact linear_character_value_mem_generatorField (K := K) (x := x)
    (linearCharacter_twist (G := G) (K := K) (x := x) β t) c

/-- Helper for Lemma 12-12.7-5: a `K`-algebra map out of Serre's simple field `K(β(x))` is
determined by the image of the distinguished generator `β(x)`. -/
theorem generatorField_algHom_ext_on_generator
    {S : Type*} [Field S] [Algebra K S]
    (β : C →* (AlgebraicClosure K)ˣ)
    {φ ψ : generatorFieldCarrier (K := K) (x := x) β →ₐ[K] S}
    (hgen :
      φ (⟨(((β (zpowers_generator (x := x)) : (AlgebraicClosure K)ˣ) :
          AlgebraicClosure K)),
        linear_character_value_mem_generatorField (K := K) (x := x) β
          (zpowers_generator (x := x))⟩ :
          generatorFieldCarrier (K := K) (x := x) β) =
        ψ (⟨(((β (zpowers_generator (x := x)) : (AlgebraicClosure K)ˣ) :
            AlgebraicClosure K)),
          linear_character_value_mem_generatorField (K := K) (x := x) β
            (zpowers_generator (x := x))⟩ :
            generatorFieldCarrier (K := K) (x := x) β)) :
    φ = ψ := by
  -- The domain is exactly the simple adjoin `K⟮β(x)⟯`, so agreement on the adjoined generator
  -- forces agreement on the whole field.
  apply IntermediateField.adjoin_algHom_ext K
  intro z hz
  simp only [Set.mem_singleton_iff] at hz
  rcases hz with rfl
  simpa using hgen

/-- Helper for Lemma 12-12.7-5: the same generator test determines `K`-algebra automorphisms of
`K(β(x))`. -/
theorem generatorField_algEquiv_eq_of_apply_generator_eq
    (β : C →* (AlgebraicClosure K)ˣ)
    {φ ψ : generatorFieldCarrier (K := K) (x := x) β ≃ₐ[K]
        generatorFieldCarrier (K := K) (x := x) β}
    (hgen :
      φ (⟨(((β (zpowers_generator (x := x)) : (AlgebraicClosure K)ˣ) :
          AlgebraicClosure K)),
        linear_character_value_mem_generatorField (K := K) (x := x) β
          (zpowers_generator (x := x))⟩ :
          generatorFieldCarrier (K := K) (x := x) β) =
        ψ (⟨(((β (zpowers_generator (x := x)) : (AlgebraicClosure K)ˣ) :
            AlgebraicClosure K)),
          linear_character_value_mem_generatorField (K := K) (x := x) β
            (zpowers_generator (x := x))⟩ :
            generatorFieldCarrier (K := K) (x := x) β)) :
    φ = ψ := by
  -- Route correction: the remaining witness-independence step for Serre's restricted `σ_t`
  -- package should now be proved by this simple-field extensionality lemma instead of repeatedly
  -- unfolding the whole adjoin construction.
  ext z
  exact congrArg Subtype.val <|
    congrArg (fun f : generatorFieldCarrier (K := K) (x := x) β →ₐ[K]
        generatorFieldCarrier (K := K) (x := x) β ↦ f z)
      (generatorField_algHom_ext_on_generator
        (G := G) (K := K) (x := x) β
        (φ := (φ : generatorFieldCarrier (K := K) (x := x) β →ₐ[K]
          generatorFieldCarrier (K := K) (x := x) β))
        (ψ := (ψ : generatorFieldCarrier (K := K) (x := x) β →ₐ[K]
          generatorFieldCarrier (K := K) (x := x) β))
        hgen)

end Representation
