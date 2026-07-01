import Serre.Chap12.Lemma_12_12_7_5.GeneratorFieldModel

open Representation
open scoped Pointwise Representation

noncomputable section

universe u v

section Representation

variable {G : Type u} [Group G] [Finite G]
variable {L : Type v} [Field L] [NumberField L]
variable [IsCyclotomicExtension {Monoid.exponent G} ℚ L]
variable (K : IntermediateField ℚ L) (p : ℕ) (x : G)

local notation "ΓK" => Γ[K](G)
local notation "C" => Subgroup.zpowers x

/-- Helper for Lemma 12-12.7-5: coercing a dependent cast between equal intermediate-field
carriers back to the ambient algebraic closure does not change the underlying scalar. -/
private theorem intermediateField_cast_coe_eq
    {S T : IntermediateField K (AlgebraicClosure K)} (h : S = T) (z : S) :
    (((cast (congrArg (fun U : IntermediateField K (AlgebraicClosure K) => ↥U) h) z : T) :
        AlgebraicClosure K)) =
      (z : AlgebraicClosure K) := by
  -- Reduce to the reflexive cast case, then read off equality on underlying subtype values.
  subst h
  simpa using congrArg Subtype.val
    (cast_eq (congrArg (fun U : IntermediateField K (AlgebraicClosure K) => ↥U) rfl) z)

/-- Helper for Lemma 12-12.7-5: applying the twist-field carrier identification to the twisted
scalar attached to `c` does not change its ambient algebraic-closure value. -/
private theorem generatorField_twist_linearEquiv_apply_twisted_value_coe
    (β : C →* (AlgebraicClosure K)ˣ) (t : ΓK) (c : C) :
    let e := generatorField_twist_linearEquiv (G := G) (K := K) (x := x) β t
    let aTw :
        generatorFieldCarrier (K := K) (x := x)
          (linearCharacter_twist (G := G) (K := K) (x := x) β t) :=
      ⟨(((linearCharacter_twist (G := G) (K := K) (x := x) β t c :
          (AlgebraicClosure K)ˣ) : AlgebraicClosure K)),
        linear_character_value_mem_generatorField (K := K) (x := x)
          (linearCharacter_twist (G := G) (K := K) (x := x) β t) c⟩
    ((e aTw : generatorFieldCarrier (K := K) (x := x) β) : AlgebraicClosure K) =
      (((linearCharacter_twist (G := G) (K := K) (x := x) β t c :
          (AlgebraicClosure K)ˣ) : AlgebraicClosure K)) := by
  -- The twist equivalence is only the dependent cast along `K(β^t(x)) = K(β(x))`.
  simp [generatorField_twist_linearEquiv, generatorFieldOfLinearCharacter_twist_eq,
    intermediateField_cast_coe_eq]

/-- Helper for Lemma 12-12.7-5: transporting a vector from `K(β(x))` to the twisted field and
back preserves its ambient algebraic-closure value. -/
private theorem generatorField_twist_linearEquiv_apply_symm_coe
    (β : C →* (AlgebraicClosure K)ˣ) (t : ΓK)
    (z : generatorFieldCarrier (K := K) (x := x) β) :
    let e := generatorField_twist_linearEquiv (G := G) (K := K) (x := x) β t
    ((e (e.symm z) : generatorFieldCarrier (K := K) (x := x) β) :
        AlgebraicClosure K) =
      (z : AlgebraicClosure K) := by
  -- Apply the inverse cast and immediately cancel it again on the fixed carrier.
  simpa using congrArg Subtype.val
    ((generatorField_twist_linearEquiv (G := G) (K := K) (x := x) β t).apply_symm_apply z)

/-- Helper for Lemma 12-12.7-5: the twisted scalar used in the fixed-carrier model really belongs
to `K(β(x))`. -/
private theorem twisted_linear_character_value_mem_generatorField_local
    (β : C →* (AlgebraicClosure K)ˣ) (t : ΓK) (c : C) :
    (((linearCharacter_twist (G := G) (K := K) (x := x) β t c :
        (AlgebraicClosure K)ˣ) : AlgebraicClosure K)) ∈
      generatorFieldOfLinearCharacter (K := K) (x := x) β := by
  -- The twist leaves the simple generator field unchanged, so the twisted value still lies there.
  rw [← generatorFieldOfLinearCharacter_twist_eq (G := G) (K := K) (x := x) β t]
  exact linear_character_value_mem_generatorField (K := K) (x := x)
    (linearCharacter_twist (G := G) (K := K) (x := x) β t) c

/-- Helper for Lemma 12-12.7-5: on one vector of the fixed carrier `K(β(x))`, transporting the
twisted generator-field model back along the twist-field equality agrees with the fixed-carrier
twisted action. -/
theorem generatorField_twist_transport_apply_eq_fixed_carrier
    (β : C →* (AlgebraicClosure K)ˣ) (t : ΓK) (c : C)
    (z : generatorFieldCarrier (K := K) (x := x) β) :
    ↑(((transportRepresentation (K := K)
            (generatorField_twist_linearEquiv (G := G) (K := K) (x := x) β t)
            (generatorField_linearCharacter_representation (K := K) (x := x)
              (linearCharacter_twist (G := G) (K := K) (x := x) β t))) c) z) =
      ↑(((generatorField_twisted_linearCharacter_representation
            (G := G) (K := K) (x := x) β t) c) z) := by
  let e := generatorField_twist_linearEquiv (G := G) (K := K) (x := x) β t
  let aTw :
      generatorFieldCarrier (K := K) (x := x)
        (linearCharacter_twist (G := G) (K := K) (x := x) β t) :=
    ⟨(((linearCharacter_twist (G := G) (K := K) (x := x) β t c :
        (AlgebraicClosure K)ˣ) : AlgebraicClosure K)),
      linear_character_value_mem_generatorField (K := K) (x := x)
        (linearCharacter_twist (G := G) (K := K) (x := x) β t) c⟩
  let aFix : generatorFieldCarrier (K := K) (x := x) β :=
    ⟨(((linearCharacter_twist (G := G) (K := K) (x := x) β t c :
        (AlgebraicClosure K)ˣ) : AlgebraicClosure K)),
      twisted_linear_character_value_mem_generatorField_local
        (G := G) (K := K) (x := x) β t c⟩
  -- Normalize the transported action to multiplication on the twisted carrier, then transport
  -- that product through the cast equivalence one factor at a time.
  rw [show
      ((generatorField_twisted_linearCharacter_representation
          (G := G) (K := K) (x := x) β t) c) z = aFix * z by
        rfl]
  rw [show
      ((transportRepresentation (K := K) e
          (generatorField_linearCharacter_representation (K := K) (x := x)
            (linearCharacter_twist (G := G) (K := K) (x := x) β t))) c) z =
        e
          (((generatorField_linearCharacter_representation (K := K) (x := x)
              (linearCharacter_twist (G := G) (K := K) (x := x) β t)) c)
            (e.symm z)) by
        change
          (e.conj
              ((generatorField_linearCharacter_representation (K := K) (x := x)
                  (linearCharacter_twist (G := G) (K := K) (x := x) β t)) c))
            z =
            e
              (((generatorField_linearCharacter_representation (K := K) (x := x)
                  (linearCharacter_twist (G := G) (K := K) (x := x) β t)) c)
                (e.symm z))
        rw [LinearEquiv.conj_apply_apply]]
  rw [show
      ((generatorField_linearCharacter_representation (K := K) (x := x)
          (linearCharacter_twist (G := G) (K := K) (x := x) β t)) c)
        (e.symm z) = aTw * e.symm z by
        rfl]
  apply Subtype.ext
  change
    (((e (aTw * e.symm z) : generatorFieldCarrier (K := K) (x := x) β) :
        AlgebraicClosure K)) =
      (((aFix * z : generatorFieldCarrier (K := K) (x := x) β) :
        AlgebraicClosure K))
  rw [generatorField_twist_linearEquiv_mul_twisted_value_public
    (G := G) (K := K) (x := x) β t c (e.symm z)]
  -- The first factor is the transported twisted scalar; the second factor is just the original
  -- vector after canceling the cast equivalence.
  have hTw :
      ((e aTw : generatorFieldCarrier (K := K) (x := x) β) :
          AlgebraicClosure K) =
        (((linearCharacter_twist (G := G) (K := K) (x := x) β t c :
            (AlgebraicClosure K)ˣ) : AlgebraicClosure K)) :=
    generatorField_twist_linearEquiv_apply_twisted_value_coe
      (G := G) (K := K) (x := x) β t c
  have hsymm :
      ((e (e.symm z) : generatorFieldCarrier (K := K) (x := x) β) :
          AlgebraicClosure K) =
        (z : AlgebraicClosure K) :=
    generatorField_twist_linearEquiv_apply_symm_coe
      (G := G) (K := K) (x := x) β t z
  -- After rewriting the two transported factors, both sides are the same ambient product.
  have hprod :
      (((e aTw : generatorFieldCarrier (K := K) (x := x) β) :
          AlgebraicClosure K) *
        ((e (e.symm z) : generatorFieldCarrier (K := K) (x := x) β) :
          AlgebraicClosure K)) =
        (((aFix : generatorFieldCarrier (K := K) (x := x) β) :
            AlgebraicClosure K) *
          (z : AlgebraicClosure K)) := by
    rw [hTw, hsymm]
  exact hprod

/-- Helper for Lemma 12-12.7-5: transporting the twisted generator-field model back along the
canonical equality `K(β^t(x)) = K(β(x))` yields the fixed-carrier twisted action. -/
theorem generatorField_twist_transport_eq_fixed_carrier_representation
    (β : C →* (AlgebraicClosure K)ˣ) (t : ΓK) :
    transportRepresentation (K := K)
        (generatorField_twist_linearEquiv (G := G) (K := K) (x := x) β t)
        (generatorField_linearCharacter_representation (K := K) (x := x)
          (linearCharacter_twist (G := G) (K := K) (x := x) β t)) =
      generatorField_twisted_linearCharacter_representation
        (G := G) (K := K) (x := x) β t := by
  ext c z
  exact congrArg Subtype.val <|
    generatorField_twist_transport_apply_eq_fixed_carrier
      (G := G) (K := K) (x := x) β t c z

end Representation
