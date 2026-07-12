import Mathlib
import LinearRepresentations_Serre_1977.Chap08.Corollary_8_8_3_8
import LinearRepresentations_Serre_1977.Chap07.Exercise_7_7_2_4
import LinearRepresentations_Serre_1977.Chap08.Exercise_8_8_2_3
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_5_1
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_5_2.OrdinaryExplicitModels
import LinearRepresentations_Serre_1977.RepresentationTheory.RealizableOver

-- The Fong–Swan import chain re-introduces the global `Field.henselian` instance, which makes
-- typeclass search diverge (even trivial `Module …` goals time out). Instance removals are
-- file-local and don't propagate to importers, so re-disable it here (cf. Exercise_18_18_5_1:39,
-- LinearCharacters, OrdinaryExplicitModels, ModularDescent).
attribute [-instance] Field.henselian

noncomputable section

universe u

namespace Representation

section

local notation "S4" => Equiv.Perm (Fin 4)

variable {k : Type u} [Field k]
variable {V : Type u} [AddCommGroup V] [Module k V]

/-- Helper for Exercise 18-18.5-2: if the characteristic of `k` is neither `2` nor `3`, then it
does not divide `|S₄| = 24`. This isolates the Maschke input for the ordinary branch. -/
lemma s4_ringChar_not_dvd_card (hchar2 : ringChar k ≠ 2) (hchar3 : ringChar k ≠ 3) :
    ¬ ringChar k ∣ Nat.card S4 := by
  -- The only prime divisors of `24 = 2^3 * 3` are `2` and `3`.
  intro hdiv
  rcases CharP.char_is_prime_or_zero k (ringChar k) with hp | hzero
  · have hdiv24 : ringChar k ∣ 24 := by
      simpa [s4_card] using hdiv
    have hdiv83 : ringChar k ∣ 8 * 3 := by
      simpa using hdiv24
    rcases hp.dvd_mul.mp hdiv83 with hdiv8 | hdiv3
    · have hdiv2pow : ringChar k ∣ 2 ^ 3 := by
        simpa [pow_three] using hdiv8
      have hdiv2 : ringChar k ∣ 2 := hp.dvd_of_dvd_pow hdiv2pow
      rcases (Nat.dvd_prime Nat.prime_two).mp hdiv2 with h1 | h2
      · exact hp.ne_one h1
      · exact hchar2 h2
    · rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hdiv3 with h1 | h3
      · exact hp.ne_one h1
      · exact hchar3 h3
  · simp [hzero] at hdiv

/-- Helper for Exercise 18-18.5-2: outside characteristics `2` and `3`, the order of `S₄` is
nonzero in `k`. -/
lemma s4_card_neZero_of_char_ne_two_ne_three
    (hchar2 : ringChar k ≠ 2) (hchar3 : ringChar k ≠ 3) :
    NeZero (Nat.card S4 : k) := by
  -- Package the preceding divisibility computation into the standard nonvanishing owner.
  exact NeZero.of_not_dvd k (s4_ringChar_not_dvd_card (k := k) hchar2 hchar3)

/-- Helper for Exercise 18-18.5-2: realizability over the prime subfield is preserved by
equivariant isomorphism. This is the transport step used after identifying a representation with
an explicit prime-field model. -/
lemma isRealizableOver_prime_subfield_of_equiv
    {G : Type*} [Group G]
    {W : Type u} [AddCommGroup W] [Module k W]
    {ρ : Representation k G V} {σ : Representation k G W}
    (hσ : IsRealizableOver ↥(⊥ : Subfield k) σ) (e : ρ.Equiv σ) :
    IsRealizableOver ↥(⊥ : Subfield k) ρ := by
  -- Pull the chosen prime-subfield model for `σ` back along the equivariant equivalence.
  rcases hσ with ⟨W₀, _, _, _, σ₀, ⟨e₀⟩⟩
  refine ⟨W₀, inferInstance, inferInstance, inferInstance, σ₀, ?_⟩
  exact ⟨e₀.trans e.symm⟩

/-- Helper for Exercise 18-18.5-2: every explicit representation already written over the prime
subfield is, tautologically, realizable over that prime subfield after scalar extension. -/
lemma isRealizableOver_prime_subfield_scalarExtension
    {G : Type*} [Group G]
    {W₀ : Type u} [AddCommGroup W₀] [Module ↥(⊥ : Subfield k) W₀]
    [FiniteDimensional ↥(⊥ : Subfield k) W₀]
    (ρ₀ : Representation ↥(⊥ : Subfield k) G W₀) :
    IsRealizableOver ↥(⊥ : Subfield k)
      (Representation.scalarExtension (k := k) (G := G) ρ₀) := by
  -- Use the defining witness of `IsRealizableOver` with the identity equivariant isomorphism.
  refine ⟨W₀, inferInstance, inferInstance, inferInstance, ρ₀, ?_⟩
  exact ⟨Representation.Equiv.refl _⟩

/-- Helper for Exercise 18-18.5-2: the canonical right-unit tensor equivalence intertwines the
scalar-extended prime-field trivial `S₄`-representation with the trivial `k[S₄]`-representation. -/
lemma s4_primefield_trivial_scalarExtension_isIntertwining :
    let e := (Algebra.TensorProduct.rid ↥(⊥ : Subfield k) k k).toLinearEquiv
    ∀ g : S4,
      e.toLinearMap.comp
          ((Representation.scalarExtension (k := k) (G := S4)
            (Representation.trivial ↥(⊥ : Subfield k) S4 ↥(⊥ : Subfield k))) g) =
        (Representation.trivial k S4 k) g ∘ₗ e.toLinearMap := by
  -- The tensor factor `k ⊗[k₀] k₀` collapses to `k`, and the trivial action is preserved.
  intro e g
  ext x
  simp [Representation.scalarExtension, Representation.trivial]

/-- Helper for Exercise 18-18.5-2: scalar extension of the prime-field trivial `S₄`-representation
identifies with the trivial `k[S₄]`-representation. -/
abbrev s4_primefield_trivial_scalarExtension_equiv :
    (Representation.scalarExtension (k := k) (G := S4)
      (Representation.trivial ↥(⊥ : Subfield k) S4 ↥(⊥ : Subfield k))).Equiv
        (Representation.trivial k S4 k) :=
  Representation.Equiv.mk
    (Algebra.TensorProduct.rid ↥(⊥ : Subfield k) k k).toLinearEquiv
    s4_primefield_trivial_scalarExtension_isIntertwining

/-- Helper for Exercise 18-18.5-2: the direct sum `1 ⊕ sgn` of the trivial and sign
representations of `S₄` is reducible. -/
lemma s4_trivial_prod_sign_not_isIrreducible :
    ¬ (Representation.prod (Representation.trivial k S4 k) (s4_sign_representation k)).IsIrreducible := by
  let ρ := Representation.prod (Representation.trivial k S4 k) (s4_sign_representation k)
  let U : Subrepresentation ρ :=
    { toSubmodule := (⊤ : Submodule k k).prod (⊥ : Submodule k k)
      apply_mem_toSubmodule := by
        intro g x hx
        -- The first summand is stable because the product action is diagonal.
        rcases x with ⟨x₁, x₂⟩
        rw [Submodule.mem_prod] at hx ⊢
        constructor
        · simp
        · have hx₂ : x₂ = 0 := by
            simpa using hx.2
          simp [ρ, Representation.prod, s4_sign_representation, hx₂] }
  intro hρ
  letI : ρ.IsIrreducible := hρ
  have hU_ne_bot : U ≠ ⊥ := by
    -- The vector `(1, 0)` lies in the first summand.
    intro hU
    have hmem : ((1 : k), (0 : k)) ∈ U.toSubmodule := by
      rw [Submodule.mem_prod]
      simp
    have hbot_mem : ((1 : k), (0 : k)) ∈ (⊥ : Subrepresentation ρ).toSubmodule := by
      simpa [hU] using hmem
    change ((1 : k), (0 : k)) = 0 at hbot_mem
    norm_num at hbot_mem
  have hU_ne_top : U ≠ ⊤ := by
    -- The vector `(0, 1)` does not lie in the first summand.
    intro hU
    have hmem : ((0 : k), (1 : k)) ∈ (⊤ : Subrepresentation ρ).toSubmodule := by
      change ((0 : k), (1 : k)) ∈ (⊤ : Submodule k (k × k))
      simp
    have hU_mem : ((0 : k), (1 : k)) ∈ U.toSubmodule := by
      simpa [hU] using hmem
    rw [Submodule.mem_prod] at hU_mem
    have hU_mem₂ : (1 : k) ∈ (⊥ : Submodule k k) := by
      simpa using hU_mem.2
    change (1 : k) = 0 at hU_mem₂
    exact one_ne_zero hU_mem₂
  rcases IsSimpleOrder.eq_bot_or_eq_top U with hUbot | hUtop
  · exact hU_ne_bot hUbot
  · exact hU_ne_top hUtop

end

end Representation
