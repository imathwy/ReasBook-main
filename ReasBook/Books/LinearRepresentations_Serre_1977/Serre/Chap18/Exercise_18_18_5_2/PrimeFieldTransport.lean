import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap08.Corollary_8_8_3_8
import LinearRepresentations_Serre_1977.Serre.Chap07.Exercise_7_7_2_4
import LinearRepresentations_Serre_1977.Serre.Chap08.Exercise_8_8_2_3
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_5_1
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_5_2.OrdinaryExplicitModels
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_5_2.PrimeFieldInfrastructure
import LinearRepresentations_Serre_1977.Serre.RepresentationTheory.RealizableOver

-- The Fong–Swan import chain re-introduces the global `Field.henselian` instance, making typeclass
-- search diverge on trivial `Module …` goals. Removals are file-local, so re-disable it here
-- (cf. Exercise_18_18_5_1:39, LinearCharacters, OrdinaryExplicitModels, PrimeFieldInfrastructure).
attribute [-instance] Field.henselian

noncomputable section

universe u

namespace Representation

section

local notation "S4" => Equiv.Perm (Fin 4)

-- The `S₄`-action on `Fin 3` (via the quotient `S₄ / V₄ ≃ S₃`) is a `local instance` in
-- `LinearCharacters`, so it does not propagate to importers.  Re-declare the identical instance
-- here so the degree-`2` quotient model `s4_quotient_augmentation_representation` typechecks.
local instance s4_action_on_three_via_quotient' : MulAction S4 (Fin 3) :=
  MulAction.compHom (Fin 3) s4_quotient_hom_s3

variable {k : Type u} [Field k]

-- Over the prime subfield `↥(⊥ : Subfield k)`, reducing the lattice-defined carrier is expensive,
-- so the canonical `AddCommGroup`/`Module` structures on the augmentation submodules are slow to
-- re-synthesize (and `LinearMap.trace` inside `Representation.character` forces an `AddCommGroup`
-- whose induced `AddCommMonoid` must be reconciled with `Submodule.addCommMonoid`).  Pin the
-- canonical structures directly via the `Submodule` projections so the comparison is cheap.
local instance :
    AddCommGroup
      ↥(permutationAugmentationSubrepresentation ↥(⊥ : Subfield k) S4 (Fin 3)).toSubmodule :=
  (permutationAugmentationSubrepresentation ↥(⊥ : Subfield k) S4 (Fin 3)).toSubmodule.addCommGroup
local instance :
    Module ↥(⊥ : Subfield k)
      ↥(permutationAugmentationSubrepresentation ↥(⊥ : Subfield k) S4 (Fin 3)).toSubmodule :=
  (permutationAugmentationSubrepresentation ↥(⊥ : Subfield k) S4 (Fin 3)).toSubmodule.module
local instance :
    AddCommGroup
      ↥(permutationAugmentationSubrepresentation ↥(⊥ : Subfield k) S4 (Fin 4)).toSubmodule :=
  (permutationAugmentationSubrepresentation ↥(⊥ : Subfield k) S4 (Fin 4)).toSubmodule.addCommGroup
local instance :
    Module ↥(⊥ : Subfield k)
      ↥(permutationAugmentationSubrepresentation ↥(⊥ : Subfield k) S4 (Fin 4)).toSubmodule :=
  (permutationAugmentationSubrepresentation ↥(⊥ : Subfield k) S4 (Fin 4)).toSubmodule.module

/-- Helper for Exercise 18-18.5-2: a prime is nonzero in `k` once the characteristic differs from
it. -/
private lemma cast_prime_ne_zero {p : ℕ} (hp : p.Prime) (h : ringChar k ≠ p) :
    (p : k) ≠ 0 := by
  intro hc
  have hdvd : ringChar k ∣ p := (CharP.cast_eq_zero_iff k (ringChar k) p).mp hc
  rcases CharP.char_is_prime_or_zero k (ringChar k) with hq | hzero
  · exact h ((Nat.prime_dvd_prime_iff_eq hq hp).mp hdvd)
  · rw [hzero] at hdvd
    exact hp.ne_zero (Nat.eq_zero_of_zero_dvd hdvd)

/-- Helper for Exercise 18-18.5-2: the permutation-augmentation character is field-independent up
to the coefficient map, because both sides equal `#fixedBy - 1`. -/
lemma algebraMap_permutationAugmentationCharacter_eq
    {G : Type*} [Group G] {X : Type*} [MulAction G X] [Finite X] [Nonempty X]
    [Invertible (Nat.card X : k)] (g : G) :
    algebraMap ↥(⊥ : Subfield k) k
        (permutationAugmentationCharacter ↥(⊥ : Subfield k) G X g) =
      permutationAugmentationCharacter k G X g := by
  -- Transfer invertibility of `|X|` to the prime subfield via the injective coefficient map.
  haveI : Invertible (Nat.card X : ↥(⊥ : Subfield k)) := by
    apply invertibleOfNonzero
    intro h
    have hmap : algebraMap ↥(⊥ : Subfield k) k (Nat.card X : ↥(⊥ : Subfield k))
        = (Nat.card X : k) := by simp
    rw [h, map_zero] at hmap
    exact (isUnit_of_invertible (Nat.card X : k)).ne_zero hmap.symm
  have hbot := congrFun
    (Representation.permutation_character_eq_trivial_add_augmentation
      (k := ↥(⊥ : Subfield k)) (G := G) (X := X)) g
  have htop := congrFun
    (Representation.permutation_character_eq_trivial_add_augmentation
      (k := k) (G := G) (X := X)) g
  have htrivb :
      (Representation.trivial ↥(⊥ : Subfield k) G ↥(⊥ : Subfield k)).character g = 1 := by
    simp [Representation.character]
  have htrivt : (Representation.trivial k G k).character g = 1 := by
    simp [Representation.character]
  have eb : permutationAugmentationCharacter ↥(⊥ : Subfield k) G X g
      = (ofMulAction ↥(⊥ : Subfield k) G X).character g - 1 := by
    have h : (ofMulAction ↥(⊥ : Subfield k) G X).character g
        = 1 + permutationAugmentationCharacter ↥(⊥ : Subfield k) G X g := by
      rw [← htrivb]; simpa [Pi.add_apply] using hbot
    rw [h]; ring
  have et : permutationAugmentationCharacter k G X g
      = (ofMulAction k G X).character g - 1 := by
    have h : (ofMulAction k G X).character g
        = 1 + permutationAugmentationCharacter k G X g := by
      rw [← htrivt]; simpa [Pi.add_apply] using htop
    rw [h]; ring
  rw [eb, et, ofMulAction_character_eq_ncard_fixedBy,
    ofMulAction_character_eq_ncard_fixedBy, map_sub, map_natCast, map_one]

/-- Helper for Exercise 18-18.5-2: scalar extension transports characters by the coefficient map
over any field extension. -/
lemma scalarExtension_character_eq_map_over_field
    {G : Type*} [Group G]
    {W₀ : Type*} [AddCommGroup W₀] [Module ↥(⊥ : Subfield k) W₀]
    [FiniteDimensional ↥(⊥ : Subfield k) W₀]
    (ρ₀ : Representation ↥(⊥ : Subfield k) G W₀) :
    (Representation.scalarExtension (k := k) ρ₀).character =
      fun g ↦ algebraMap ↥(⊥ : Subfield k) k (ρ₀.character g) := by
  -- Traces commute with base change, so scalar extension keeps the same character values after
  -- applying the coefficient map.
  ext g
  exact LinearMap.trace_baseChange (ρ₀ g) k

/-- Helper for Exercise 18-18.5-2: the scalar extension of the prime-field sign character has the
same ordinary character as the native sign slot over `k`. -/
lemma s4_primefield_sign_character_map
    (g : S4) :
    algebraMap ↥(⊥ : Subfield k) k
      ((s4_sign_representation ↥(⊥ : Subfield k)).character g) =
        (s4_sign_representation k).character g := by
  -- Both characters come from the same scalar-valued sign homomorphism.
  simp [s4_sign_representation, s4_sign_character, unitCharacterRepresentation_character_apply]

/-- Helper for Exercise 18-18.5-2: the scalar extension of the prime-field quotient-augmentation
character matches the native degree-`2` slot outside characteristic `3`. -/
lemma s4_primefield_quotient_augmentation_character_map
    (hchar3 : ringChar k ≠ 3) (g : S4) :
    algebraMap ↥(⊥ : Subfield k) k
      ((s4_quotient_augmentation_representation ↥(⊥ : Subfield k)).character g) =
        (s4_quotient_augmentation_representation k).character g := by
  -- The degree-`2` quotient model is the augmentation representation of the `S₄`-action on `Fin 3`,
  -- whose character is field-independent up to the coefficient map.
  letI : Invertible (Nat.card (Fin 3) : k) := invertibleOfNonzero (by
    have h3 : Nat.card (Fin 3) = 3 := by simp
    rw [h3]; exact cast_prime_ne_zero (k := k) (by norm_num) hchar3)
  exact algebraMap_permutationAugmentationCharacter_eq (k := k) (G := S4) (X := Fin 3) g

/-- Helper for Exercise 18-18.5-2: the scalar extension of the prime-field standard
augmentation character matches the native degree-`3` slot outside characteristic `2`. -/
lemma s4_primefield_standard_augmentation_character_map
    (hchar2 : ringChar k ≠ 2) (g : S4) :
    algebraMap ↥(⊥ : Subfield k) k
      ((s4_standard_augmentation_representation ↥(⊥ : Subfield k)).character g) =
        (s4_standard_augmentation_representation k).character g := by
  -- The degree-`3` standard model is the augmentation representation of the natural `S₄`-action on
  -- `Fin 4`, whose character is field-independent up to the coefficient map.
  letI : Invertible (Nat.card (Fin 4) : k) := invertibleOfNonzero (by
    have h4 : Nat.card (Fin 4) = 4 := by simp
    rw [h4, show ((4 : ℕ) : k) = ((2 : ℕ) : k) * ((2 : ℕ) : k) by push_cast; ring]
    exact mul_ne_zero (cast_prime_ne_zero (k := k) (by norm_num) hchar2)
      (cast_prime_ne_zero (k := k) (by norm_num) hchar2))
  exact algebraMap_permutationAugmentationCharacter_eq (k := k) (G := S4) (X := Fin 4) g

/-- Helper for Exercise 18-18.5-2: the scalar extension of the prime-field `sgn ⊗ std`
character matches the native sign-twisted standard slot outside characteristic `2`. -/
lemma s4_primefield_sign_standard_tensor_character_map
    (hchar2 : ringChar k ≠ 2) (g : S4) :
    algebraMap ↥(⊥ : Subfield k) k
      ((s4_sign_standard_tensor_representation ↥(⊥ : Subfield k)).character g) =
        (s4_sign_standard_tensor_representation k).character g := by
  -- Compare the tensor slot via `char_tensor` and the already repaired factorwise prime-field
  -- bridges, rather than rebuilding the scalar-extension equivalence.
  have ebot :
      (s4_sign_standard_tensor_representation ↥(⊥ : Subfield k)).character g =
        (s4_sign_representation ↥(⊥ : Subfield k)).character g *
          (s4_standard_augmentation_representation ↥(⊥ : Subfield k)).character g := by
    have h := congrFun
      (Representation.char_tensor
        (ρ := s4_sign_representation ↥(⊥ : Subfield k))
        (σ := s4_standard_augmentation_representation ↥(⊥ : Subfield k))) g
    simpa [s4_sign_standard_tensor_representation, Pi.mul_apply] using h
  have etop :
      (s4_sign_standard_tensor_representation k).character g =
        (s4_sign_representation k).character g *
          (s4_standard_augmentation_representation k).character g := by
    have h := congrFun
      (Representation.char_tensor
        (ρ := s4_sign_representation k)
        (σ := s4_standard_augmentation_representation k)) g
    simpa [s4_sign_standard_tensor_representation, Pi.mul_apply] using h
  rw [ebot, etop, map_mul, s4_primefield_sign_character_map (k := k) g,
    s4_primefield_standard_augmentation_character_map (k := k) hchar2 g]

end

end Representation
