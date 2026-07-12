import LinearRepresentations_Serre_1977.Chap12.Lemma_12_12_7_5.GeneratorFieldModel

open Representation
open scoped Pointwise Representation

noncomputable section

universe u v w

section Representation

variable {G : Type u} [Group G] [Finite G]
variable {L : Type v} [Field L] [NumberField L]
variable [IsCyclotomicExtension {Monoid.exponent G} ℚ L]
variable (K : IntermediateField ℚ L) (x : G)

/-- Helper for Lemma 12-12.7-5: a private `Fintype` witness for the finite group `G`. -/
@[reducible] private def instFintypeAssociatedGammaPElementaryGroup : Fintype G :=
  Fintype.ofFinite G

attribute [local instance] instFintypeAssociatedGammaPElementaryGroup

local notation "ΓK" => Γ[K](G)
local notation "N(" x ")" => N[ΓK](x)
local notation "C" => Subgroup.zpowers x

/-- Helper for Lemma 12-12.7-5: any subrepresentation of the generator-field model is stable
under multiplication by the distinguished generator value `β(x)`. -/
theorem generatorField_subrepresentation_mul_generator_mem_local
    (β : C →* (AlgebraicClosure K)ˣ)
    (σ : Subrepresentation (generatorField_linearCharacter_representation (K := K) (x := x) β))
    {y : generatorFieldCarrier (K := K) (x := x) β}
    (hy : y ∈ σ.toSubmodule) :
    (⟨(((β (zpowers_generator (x := x)) : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)),
      linear_character_value_mem_generatorField (K := K) (x := x) β
        (zpowers_generator (x := x))⟩ :
        generatorFieldCarrier (K := K) (x := x) β) * y ∈ σ.toSubmodule := by
  -- The cyclic action at the distinguished generator is left multiplication by `β(x)`.
  have hy' := σ.apply_mem_toSubmodule (zpowers_generator (x := x)) hy
  simpa [generatorField_linearCharacter_representation, LinearMap.mulLeft_apply] using hy'

/-- Helper for Lemma 12-12.7-5: the same stability holds for every nonnegative power of the
distinguished generator value `β(x)`. -/
theorem generatorField_subrepresentation_mul_generator_pow_mem_local
    (β : C →* (AlgebraicClosure K)ˣ)
    (σ : Subrepresentation (generatorField_linearCharacter_representation (K := K) (x := x) β))
    (n : ℕ)
    {y : generatorFieldCarrier (K := K) (x := x) β}
    (hy : y ∈ σ.toSubmodule) :
    (⟨(((β (zpowers_generator (x := x)) : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)),
      linear_character_value_mem_generatorField (K := K) (x := x) β
        (zpowers_generator (x := x))⟩ :
        generatorFieldCarrier (K := K) (x := x) β) ^ n * y ∈ σ.toSubmodule := by
  induction n with
  | zero =>
      simpa using hy
  | succ n ihn =>
      have hstep :
          (⟨(((β (zpowers_generator (x := x)) : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)),
            linear_character_value_mem_generatorField (K := K) (x := x) β
              (zpowers_generator (x := x))⟩ :
              generatorFieldCarrier (K := K) (x := x) β) *
            ((⟨(((β (zpowers_generator (x := x)) : (AlgebraicClosure K)ˣ) :
                AlgebraicClosure K)),
              linear_character_value_mem_generatorField (K := K) (x := x) β
                (zpowers_generator (x := x))⟩ :
                generatorFieldCarrier (K := K) (x := x) β) ^ n * y) ∈ σ.toSubmodule :=
        generatorField_subrepresentation_mul_generator_mem_local (K := K) (x := x) β σ ihn
      convert hstep using 1
      apply Subtype.ext
      simp [pow_succ', mul_assoc]

/-- Helper for Lemma 12-12.7-5: any subrepresentation of Serre's generator-field model is stable
under multiplication by an arbitrary element of `K(β(x))`, not just by powers of the distinguished
generator. -/
theorem generatorField_subrepresentation_mul_mem_local
    (β : C →* (AlgebraicClosure K)ˣ)
    (σ : Subrepresentation (generatorField_linearCharacter_representation (K := K) (x := x) β))
    {z y : generatorFieldCarrier (K := K) (x := x) β}
    (hy : y ∈ σ.toSubmodule) :
    z * y ∈ σ.toSubmodule := by
  let α0 : AlgebraicClosure K :=
    (((β (zpowers_generator (x := x)) : (AlgebraicClosure K)ˣ) : AlgebraicClosure K))
  let α :
      generatorFieldCarrier (K := K) (x := x) β :=
    ⟨α0,
      linear_character_value_mem_generatorField (K := K) (x := x) β
        (zpowers_generator (x := x))⟩
  have hzAdjoin :
      (z : AlgebraicClosure K) ∈
        Algebra.adjoin K ({α0} : Set (AlgebraicClosure K)) := by
    simpa [generatorField_toSubalgebra_eq_adjoin (K := K) (x := x) β, α0] using
      (show (z : AlgebraicClosure K) ∈
          (generatorFieldOfLinearCharacter (K := K) (x := x) β).toSubalgebra from z.2)
  let zAdjoin :
      Algebra.adjoin K ({α0} : Set (AlgebraicClosure K)) :=
    ⟨(z : AlgebraicClosure K), hzAdjoin⟩
  obtain ⟨f, hf⟩ := Algebra.adjoin_eq_exists_aeval
    (R := K) α0 zAdjoin
  have hpoly :
      (Polynomial.aeval α f) * y ∈ σ.toSubmodule := by
    -- Evaluate the polynomial on the distinguished generator and use stability under powers of
    -- that generator term-by-term.
    refine Polynomial.induction_on' f ?_ ?_
    · intro p q hp hq
      simpa [Polynomial.aeval_add, add_mul] using Submodule.add_mem σ.toSubmodule hp hq
    · intro n a
      have hpow :
          α ^ n * y ∈ σ.toSubmodule :=
        generatorField_subrepresentation_mul_generator_pow_mem_local
          (K := K) (x := x) β σ n hy
      -- A monomial acts by a scalar multiple of a power of the distinguished generator.
      simpa [Polynomial.aeval_monomial, α, Algebra.smul_def, mul_assoc] using
        Submodule.smul_mem σ.toSubmodule a hpow
  have hz :
      Polynomial.aeval α f = z := by
    apply Subtype.ext
    calc
      (((Polynomial.aeval α) f : generatorFieldCarrier (K := K) (x := x) β) :
          AlgebraicClosure K) =
        Polynomial.aeval α0 f := by
          simpa [α, α0] using
            (Polynomial.aeval_algHom_apply
              ((generatorFieldOfLinearCharacter (K := K) (x := x) β).val) α f).symm
      _ = (z : AlgebraicClosure K) := by
          simpa [zAdjoin] using hf
  simpa [hz] using hpoly

/-- Helper for Lemma 12-12.7-5: a nonzero subrepresentation of the generator-field model already
contains `1`, hence equals the whole field `K(β(x))`. -/
theorem generatorField_subrepresentation_eq_top_of_nonzero_local
    (β : C →* (AlgebraicClosure K)ˣ)
    (σ : Subrepresentation (generatorField_linearCharacter_representation (K := K) (x := x) β))
    (hσ : σ ≠ ⊥) :
    σ = ⊤ := by
  have hσ' : σ.toSubmodule ≠ ⊥ := by
    intro hbot
    apply hσ
    exact Subrepresentation.toSubmodule_injective hbot
  rcases (Submodule.ne_bot_iff σ.toSubmodule).mp hσ' with ⟨y, hy, hy0⟩
  have h1 :
      (1 : generatorFieldCarrier (K := K) (x := x) β) ∈ σ.toSubmodule := by
    -- Multiply the nonzero vector by its inverse inside the field `K(β(x))`.
    simpa [hy0] using
      (generatorField_subrepresentation_mul_mem_local
        (K := K) (x := x) β σ (z := y⁻¹) hy)
  -- Once `1` is inside the subrepresentation, every field element lies in it by stability under
  -- multiplication by arbitrary elements of `K(β(x))`.
  apply Subrepresentation.toSubmodule_injective
  apply Submodule.eq_top_iff'.2
  intro z
  simpa using
    (generatorField_subrepresentation_mul_mem_local
      (K := K) (x := x) β σ (z := z) (y := 1) h1)

/-- Helper for Lemma 12-12.7-5: a nonzero intertwiner out of Serre's generator-field model is
already an equivariant isomorphism once the target is irreducible. -/
theorem generatorField_model_equiv_of_nonzero_intertwiner
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (β : C →* (AlgebraicClosure K)ˣ)
    (ρ : Representation K C V) [ρ.IsIrreducible]
    (f : (generatorField_linearCharacter_representation (K := K) (x := x) β).IntertwiningMap ρ)
    (hf : f ≠ 0) :
    Nonempty ((generatorField_linearCharacter_representation (K := K) (x := x) β).Equiv ρ) := by
  -- The generator-field model is simple because every nonzero subrepresentation is already top.
  let τ := generatorField_linearCharacter_representation (K := K) (x := x) β
  have hτ_nontrivial : Nontrivial (Subrepresentation τ) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro hbot_top
    have hbot_top_submodule :
        (⊥ : Submodule K (generatorFieldCarrier (K := K) (x := x) β)) = ⊤ := by
      exact congrArg Subrepresentation.toSubmodule hbot_top
    exact bot_ne_top hbot_top_submodule
  have hτ_irr : τ.IsIrreducible := by
    refine IsSimpleOrder.of_forall_eq_top ?_
    intro σ hσ
    exact generatorField_subrepresentation_eq_top_of_nonzero_local (K := K) (x := x) β σ hσ
  letI : τ.IsIrreducible := hτ_irr
  -- With both source and target irreducible, Schur's lemma upgrades any nonzero intertwiner to
  -- an equivalence immediately.
  have hbij : Function.Bijective f :=
    (Representation.IsIrreducible.bijective_or_eq_zero f).resolve_right hf
  exact ⟨f.ofBijective hbij⟩

end Representation
