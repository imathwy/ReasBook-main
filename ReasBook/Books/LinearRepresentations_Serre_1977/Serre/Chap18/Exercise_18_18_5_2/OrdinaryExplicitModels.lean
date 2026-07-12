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

universe w

namespace Representation

section

open CategoryTheory

local notation "S3" => Equiv.Perm (Fin 3)
local notation "S4" => Equiv.Perm (Fin 4)
local notation "A4" => alternatingGroup (Fin 4)
local notation "V4" => alternatingGroup.kleinFour (Fin 4)
local notation "V4InS4" => Subgroup.map (Subgroup.subtype A4) V4

local instance : (V4InS4).Normal := _root_.s4DoubleTranspositionKleinFour_normal

/-- Helper for Exercise 18-18.5-2: activate the quotient action on `Fin 3` locally via the
canonical owner already defined in the linear-character support file. -/
local instance : MulAction S4 (Fin 3) :=
  Representation.s4_action_on_three_via_quotient

/-- Helper for Exercise 18-18.5-2: the ordinary augmentation constituent of the natural `S₃`-action
on three letters is irreducible. -/
lemma s3_augmentation_representation_isIrreducible :
    (permutationAugmentationRepresentation ℂ S3 (Fin 3)).IsIrreducible := by
  -- The natural `S₃`-action on three letters is doubly transitive.
  have h2 : MulAction.IsMultiplyPretransitive S3 (Fin 3) 2 :=
    Equiv.Perm.isMultiplyPretransitive (α := Fin 3) 2
  -- Convert double transitivity to the character-pairing criterion for the augmentation slot.
  have hpair :=
    (Representation.isTwoPretransitive_iff_pairActionHasDiagonalOrbits
      (G := S3) (X := Fin 3)).mp h2
  have hsq :=
    (Representation.pairActionHasDiagonalOrbits_iff_character_square_pairing_eq_two
      (G := S3) (X := Fin 3)).mp hpair
  -- The imported augmentation criterion then gives irreducibility.
  exact
    (Representation.character_square_pairing_eq_two_iff_augmentation_isIrreducible
      (G := S3) (X := Fin 3)).mp hsq

/-- Helper for Exercise 18-18.5-2: the ordinary augmentation constituent of the natural `S₃`-action
has degree `2`. -/
lemma s3_augmentation_representation_degree :
    Module.finrank ℂ (permutationAugmentationSubrepresentation ℂ S3 (Fin 3)).toSubmodule = 2 := by
  letI : Invertible (Nat.card (Fin 3) : ℂ) := by
    exact invertibleOfNonzero (by norm_num)
  -- Evaluate the permutation/augmentation character decomposition at the identity.
  have hχ :=
    permutation_character_eq_trivial_add_augmentation (k := ℂ) (G := S3) (X := Fin 3)
  have h1 : (3 : ℂ) = 1 + permutationAugmentationCharacter ℂ S3 (Fin 3) 1 := by
    simpa [Representation.char_one] using congrFun hχ 1
  have h2 := congrArg (fun z : ℂ => z - 1) h1
  norm_num at h2
  have hchar : (permutationAugmentationRepresentation ℂ S3 (Fin 3)).character 1 = 2 := by
    simpa [permutationAugmentationCharacter] using h2.symm
  -- Reinterpret the identity character value as the degree of the representation.
  have hone := Representation.char_one (ρ := permutationAugmentationRepresentation ℂ S3 (Fin 3))
  rw [hchar] at hone
  exact_mod_cast hone.symm

/-- Helper for Exercise 18-18.5-2: the quotient augmentation constituent of `S₄` has degree `2`.
This is the degree of Serre's explicit `q₂` slot. -/
lemma s4_quotient_augmentation_representation_degree :
    Module.finrank ℂ
      (permutationAugmentationSubrepresentation ℂ S4 (Fin 3)).toSubmodule = 2 := by
  letI : Invertible (Nat.card (Fin 3) : ℂ) := by
    exact invertibleOfNonzero (by norm_num)
  -- The quotient action on three letters has permutation degree `3`, so its augmentation part
  -- has character value `2` at the identity.
  have hχ :=
    permutation_character_eq_trivial_add_augmentation (k := ℂ) (G := S4) (X := Fin 3)
  have h1 : (3 : ℂ) = 1 + permutationAugmentationCharacter ℂ S4 (Fin 3) 1 := by
    simpa [Representation.char_one] using congrFun hχ 1
  have h2 := congrArg (fun z : ℂ => z - 1) h1
  norm_num at h2
  have hchar : (s4_quotient_augmentation_representation ℂ).character 1 = 2 := by
    simpa [s4_quotient_augmentation_representation, permutationAugmentationCharacter] using h2.symm
  -- Finish by the standard identity `χ(1) = dim`.
  have hone := Representation.char_one (ρ := s4_quotient_augmentation_representation ℂ)
  rw [hchar] at hone
  exact_mod_cast hone.symm

/-- Helper for Exercise 18-18.5-2: the ordinary degree-`3` augmentation constituent of the
natural `S₄`-action is irreducible. -/
lemma s4_standard_augmentation_representation_isIrreducible :
    (s4_standard_augmentation_representation ℂ).IsIrreducible := by
  -- The natural `S₄`-action on four letters is doubly transitive.
  have h2 : MulAction.IsMultiplyPretransitive S4 (Fin 4) 2 :=
    Equiv.Perm.isMultiplyPretransitive (α := Fin 4) 2
  -- Translate double transitivity into the augmentation irreducibility criterion.
  have hpair :=
    (Representation.isTwoPretransitive_iff_pairActionHasDiagonalOrbits
      (G := S4) (X := Fin 4)).mp h2
  have hsq :=
    (Representation.pairActionHasDiagonalOrbits_iff_character_square_pairing_eq_two
      (G := S4) (X := Fin 4)).mp hpair
  exact
    (Representation.character_square_pairing_eq_two_iff_augmentation_isIrreducible
      (G := S4) (X := Fin 4)).mp hsq

/-- Helper for Exercise 18-18.5-2: the ordinary degree-`3` augmentation constituent of the
natural `S₄`-action has degree `3`. -/
lemma s4_standard_augmentation_representation_degree :
    Module.finrank ℂ
      (permutationAugmentationSubrepresentation ℂ S4 (Fin 4)).toSubmodule = 3 := by
  letI : Invertible (Nat.card (Fin 4) : ℂ) := by
    exact invertibleOfNonzero (by norm_num)
  -- Evaluate the permutation/augmentation character decomposition at the identity.
  have hχ :=
    permutation_character_eq_trivial_add_augmentation (k := ℂ) (G := S4) (X := Fin 4)
  have h1 : (4 : ℂ) = 1 + permutationAugmentationCharacter ℂ S4 (Fin 4) 1 := by
    simpa [Representation.char_one] using congrFun hχ 1
  have h2 := congrArg (fun z : ℂ => z - 1) h1
  norm_num at h2
  have hchar : (s4_standard_augmentation_representation ℂ).character 1 = 3 := by
    simpa [s4_standard_augmentation_representation, permutationAugmentationCharacter] using h2.symm
  -- Convert the identity character value into the finrank statement.
  have hone := Representation.char_one (ρ := s4_standard_augmentation_representation ℂ)
  rw [hchar] at hone
  exact_mod_cast hone.symm

/-- Helper for Exercise 18-18.5-2: the fifth standard constituent is the tensor product of the
sign representation with the degree-`3` augmentation constituent. -/
abbrev s4_sign_standard_tensor_representation
    (F : Type w) [Field F] :
    Representation F S4
      (TensorProduct F F (permutationAugmentationSubrepresentation F S4 (Fin 4)).toSubmodule) :=
  (s4_sign_representation F).tprod (s4_standard_augmentation_representation F)

/-- Helper for Exercise 18-18.5-2: precomposing an irreducible representation with a surjective
group homomorphism preserves irreducibility because every invariant subspace for the pullback is
already invariant under the target group action. -/
lemma isIrreducible_comp_of_surjective_local
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

/-- Helper for Exercise 18-18.5-2: the quotient map `S₄ → S₃` is surjective. -/
lemma s4_quotient_hom_s3_surjective : Function.Surjective s4_quotient_hom_s3 := by
  -- Lift a target permutation of three letters first through the quotient equivalence and then
  -- through the quotient map.
  intro h
  rcases QuotientGroup.mk'_surjective V4InS4 (s4_quotient_by_klein_four_equiv_s3.symm h) with
    ⟨g, hg⟩
  refine ⟨g, ?_⟩
  simpa [s4_quotient_hom_s3] using congrArg s4_quotient_by_klein_four_equiv_s3 hg

/-- Helper for Exercise 18-18.5-2: the degree-`2` quotient constituent is irreducible over `ℂ`
because it is the pullback of the irreducible augmentation representation of `S₃` along the
surjective quotient map. -/
lemma s4_quotient_augmentation_representation_isIrreducible :
    (s4_quotient_augmentation_representation ℂ).IsIrreducible := by
  letI : (permutationAugmentationRepresentation ℂ S3 (Fin 3)).IsIrreducible :=
    s3_augmentation_representation_isIrreducible
  -- Route correction: treat the `q₂` slot as an inflated `S₃` augmentation constituent.
  simpa [s4_quotient_augmentation_representation] using
    (isIrreducible_comp_of_surjective_local
      s4_quotient_hom_s3 s4_quotient_hom_s3_surjective
      (permutationAugmentationRepresentation ℂ S3 (Fin 3)))

/-- Helper for Exercise 18-18.5-2: a representation equivalence induces an order isomorphism on
subrepresentations. -/
private noncomputable def subrepresentationOrderIso_oem
    {G : Type*} [Group G]
    {V' : Type*} [AddCommGroup V'] [Module ℂ V']
    {W' : Type*} [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ G V'} {σ : Representation ℂ G W'} (e : ρ.Equiv σ) :
    Subrepresentation ρ ≃o Subrepresentation σ where
  toFun U :=
    { toSubmodule := U.toSubmodule.map e.toLinearMap
      apply_mem_toSubmodule := by
        intro g x hx
        rcases hx with ⟨y, hy, rfl⟩
        -- Mapping a stable subspace along an intertwining equivalence preserves stability.
        refine ⟨ρ g y, U.apply_mem_toSubmodule g hy, ?_⟩
        simp [e.isIntertwining] }
  invFun U :=
    { toSubmodule := U.toSubmodule.map e.symm.toLinearMap
      apply_mem_toSubmodule := by
        intro g x hx
        rcases hx with ⟨y, hy, rfl⟩
        -- The inverse equivalence transports stability back to the source representation.
        refine ⟨σ g y, U.apply_mem_toSubmodule g hy, ?_⟩
        simp [e.symm.isIntertwining] }
  left_inv U := by
    -- Transporting to `σ` and back to `ρ` recovers the original subrepresentation.
    apply Subrepresentation.toSubmodule_injective
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hy, hxy⟩
      have : y = e x := by
        simpa using congrArg e hxy
      subst this
      simpa using hy
    · intro hx
      change x ∈ Submodule.map e.symm.toLinearMap (Submodule.map e.toLinearMap U.toSubmodule)
      exact ⟨e x, ⟨x, hx, rfl⟩, by simp⟩
  right_inv U := by
    -- The same two-step transport is inverse on the target side as well.
    apply Subrepresentation.toSubmodule_injective
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hy, hxy⟩
      have : y = e.symm x := by
        simpa using congrArg e.symm hxy
      subst this
      simpa using hy
    · intro hx
      change x ∈ Submodule.map e.toLinearMap (Submodule.map e.symm.toLinearMap U.toSubmodule)
      exact ⟨e.symm x, ⟨x, hx, rfl⟩, by simp⟩
  map_rel_iff' := by
    intro U U'
    constructor
    · intro h x hx
      -- Inclusion after transport descends because `e` is injective.
      have hx' : e x ∈ U.toSubmodule.map e.toLinearMap := ⟨x, hx, rfl⟩
      rcases h hx' with ⟨y, hy, hxy⟩
      have : y = x := by
        apply e.toLinearEquiv.injective
        simp [hxy]
      simpa [this] using hy
    · intro h x hx
      rcases hx with ⟨y, hy, rfl⟩
      exact ⟨y, h hy, rfl⟩

/-- Helper for Exercise 18-18.5-2: irreducibility transports across a representation
equivalence. -/
private lemma isIrreducible_of_equiv_oem
    {G : Type*} [Group G]
    {V' : Type*} [AddCommGroup V'] [Module ℂ V']
    {W' : Type*} [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ G V'} {σ : Representation ℂ G W'}
    [ρ.IsIrreducible] (e : ρ.Equiv σ) : σ.IsIrreducible := by
  -- Equivalent representations have isomorphic lattices of invariant subspaces.
  exact (subrepresentationOrderIso_oem e).isSimpleOrder_iff.mp inferInstance

/-- Helper for Exercise 18-18.5-2: precomposing a complex irreducible representation with a group
equivalence preserves irreducibility. -/
lemma isIrreducible_comp_of_mulEquiv_complex_local
    {G H : Type*} [Group G] [Group H]
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (e : G ≃* H) (σ : Representation ℂ H W) [σ.IsIrreducible] :
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
  intro U hU
  let U' : Subrepresentation σ :=
    { toSubmodule := U.toSubmodule
      apply_mem_toSubmodule := by
        intro h x hx
        simpa using U.apply_mem_toSubmodule (e.symm h) hx }
  have hU'_ne_bot : U' ≠ ⊥ := by
    intro hU'
    apply hU
    apply Subrepresentation.toSubmodule_injective
    simpa [U'] using congrArg Subrepresentation.toSubmodule hU'
  have hU'_top : U' = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top U').resolve_left hU'_ne_bot
  apply Subrepresentation.toSubmodule_injective
  simpa [U'] using congrArg Subrepresentation.toSubmodule hU'_top

/-- Helper for Exercise 18-18.5-2: twisting a complex representation by a linear character keeps
the same carrier and rescales each action map by the character value. -/
lemma unitCharacterTwistRepresentation_map_one
    {G : Type*} [Group G]
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (β : G →* ℂˣ) (σ : Representation ℂ G W) :
    ((β 1 : ℂˣ) : ℂ) • σ 1 = 1 := by
  -- At the identity, both the scalar character and the representation act trivially.
  apply LinearMap.ext
  intro x
  simp

/-- Helper for Exercise 18-18.5-2: twisting by a linear character is multiplicative in the group
variable. -/
lemma unitCharacterTwistRepresentation_map_mul
    {G : Type*} [Group G]
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (β : G →* ℂˣ) (σ : Representation ℂ G W) (g h : G) :
    ((β (g * h) : ℂˣ) : ℂ) • σ (g * h) =
      (((β g : ℂˣ) : ℂ) • σ g) * (((β h : ℂˣ) : ℂ) • σ h) := by
  -- The character and the original action multiply in parallel.
  apply LinearMap.ext
  intro x
  have hβ :
      ((β (g * h) : ℂˣ) : ℂ) = ((β g : ℂˣ) : ℂ) * ((β h : ℂˣ) : ℂ) := by
    simp
  rw [hβ]
  simp [smul_smul, mul_comm]

/-- Helper for Exercise 18-18.5-2: the same-carrier twist of a complex representation by a
linear character. -/
abbrev unitCharacterTwistRepresentation
    {G : Type*} [Group G]
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (β : G →* ℂˣ) (σ : Representation ℂ G W) :
    Representation ℂ G W where
  toFun g := ((β g : ℂˣ) : ℂ) • σ g
  map_one' := unitCharacterTwistRepresentation_map_one β σ
  map_mul' g h := unitCharacterTwistRepresentation_map_mul β σ g h

/-- Helper for Exercise 18-18.5-2: the tensor product with a degree-`1` character is equivalent
to the corresponding same-carrier scalar twist. -/
noncomputable def unitCharacterTensorTwistEquiv
    {G : Type*} [Group G]
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (β : G →* ℂˣ) (σ : Representation ℂ G W) :
    ((unitCharacterRepresentation β).tprod σ).Equiv (unitCharacterTwistRepresentation β σ) := by
  refine Representation.Equiv.mk (_root_.TensorProduct.lid ℂ W) ?_
  intro g
  -- The tensor unit sends `c ⊗ w` to `c • w`, which is exactly the twisted action.
  apply LinearMap.ext
  intro z
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro c w
    simp [TensorProduct.lid_tmul, unitCharacterRepresentation, unitCharacterTwistRepresentation,
      LinearMap.lsmul_apply, smul_smul, mul_comm]
  · intro z₁ z₂ hz₁ hz₂
    simpa [map_add] using congrArg₂ HAdd.hAdd hz₁ hz₂

/-- Helper for Exercise 18-18.5-2: the same-carrier scalar twist of an irreducible complex
representation is again irreducible. -/
lemma unitCharacterTwistRepresentation_isIrreducible
    {G : Type*} [Group G]
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (β : G →* ℂˣ) (σ : Representation ℂ G W) [σ.IsIrreducible] :
    Representation.IsIrreducible (unitCharacterTwistRepresentation β σ) := by
  letI : Nontrivial (Subrepresentation (unitCharacterTwistRepresentation β σ)) := by
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
        intro g x hx
        have hxTwist : ((unitCharacterTwistRepresentation β σ) g) x ∈ U.toSubmodule :=
          U.apply_mem_toSubmodule g hx
        -- The twist differs from `σ g` by a nonzero scalar, so the same subspace is stable.
        have hxScaled :
            (((((β g : ℂˣ) : ℂ))⁻¹) • (((unitCharacterTwistRepresentation β σ) g) x)) ∈
              U.toSubmodule :=
          U.toSubmodule.smul_mem _ hxTwist
        simpa [unitCharacterTwistRepresentation, smul_smul] using hxScaled }
  have hU'_ne_bot : U' ≠ ⊥ := by
    intro hU'
    apply hU
    apply Subrepresentation.toSubmodule_injective
    simpa [U'] using congrArg Subrepresentation.toSubmodule hU'
  have hU'_top : U' = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top U').resolve_left hU'_ne_bot
  apply Subrepresentation.toSubmodule_injective
  simpa [U'] using congrArg Subrepresentation.toSubmodule hU'_top

/-- Helper for Exercise 18-18.5-2: tensoring a complex irreducible representation with a
unit-valued character preserves irreducibility. -/
lemma tprod_unitCharacter_preserves_isIrreducible
    {G : Type*} [Group G] [Finite G]
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (β : G →* ℂˣ) (σ : Representation ℂ G W) [σ.IsIrreducible] :
    Representation.IsIrreducible ((unitCharacterRepresentation β).tprod σ) := by
  letI : Representation.IsIrreducible (unitCharacterTwistRepresentation β σ) :=
    unitCharacterTwistRepresentation_isIrreducible β σ
  -- Route correction: pass to the same-carrier twist, where invariant subspaces are unchanged.
  exact isIrreducible_of_equiv_oem
    (ρ := unitCharacterTwistRepresentation β σ)
    (σ := (unitCharacterRepresentation β).tprod σ)
    (unitCharacterTensorTwistEquiv β σ).symm

/-- Helper for Exercise 18-18.5-2: the sign twist of the degree-`3` constituent is irreducible
over `ℂ`. -/
lemma s4_sign_standard_tensor_representation_isIrreducible :
    (s4_sign_standard_tensor_representation ℂ).IsIrreducible := by
  letI : (s4_standard_augmentation_representation ℂ).IsIrreducible :=
    s4_standard_augmentation_representation_isIrreducible
  -- The fifth slot is just the sign-character twist of the standard degree-`3` constituent.
  simpa [s4_sign_standard_tensor_representation, s4_sign_representation] using
    (tprod_unitCharacter_preserves_isIrreducible
      (β := s4_sign_character ℂ) (σ := s4_standard_augmentation_representation ℂ))

/-- Helper for Exercise 18-18.5-2: lifting the carrier by `ULift` preserves the same linear
action. -/
def ulift_carrier_representation
    {F : Type w} [Field F] {G : Type*} [Monoid G]
    {W : Type w} [AddCommGroup W] [Module F W]
    (ρ : Representation F G W) :
    Representation F G (ULift.{w} W) where
  toFun g :=
    { toFun := fun x ↦ ⟨ρ g x.down⟩
      map_add' := by
        intro x y
        ext
        simp
      map_smul' := by
        intro a x
        ext
        simp }
  map_one' := by
    ext x
    simp
  map_mul' g h := by
    ext x
    simp [map_mul]

/-- Helper for Exercise 18-18.5-2: simultaneously lifting the group and carrier puts the explicit
`S₄` models into the field universe needed by `FDRep`. -/
def ulift_group_carrier_representation
    {F : Type w} [Field F] {G : Type*} [Group G]
    {W : Type w} [AddCommGroup W] [Module F W]
    (ρ : Representation F G W) :
    Representation F (ULift.{w} G) (ULift.{w} W) :=
  ulift_carrier_representation (ρ := ρ.comp (MulEquiv.ulift.toMonoidHom))

/-- Helper for Exercise 18-18.5-2: lifting only the carrier by `ULift` does not change the
character. -/
@[simp] lemma ulift_carrier_representation_character_apply
    {F : Type w} [Field F] {G : Type*} [Monoid G]
    {W : Type w} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (ρ : Representation F G W) (g : G) :
    (ulift_carrier_representation ρ).character g = ρ.character g := by
  -- `ULift.moduleEquiv` conjugates the lifted action back to the original one.
  change
    LinearMap.trace F (ULift.{w} W)
      ((ULift.moduleEquiv.symm : W ≃ₗ[F] ULift.{w} W).conj (ρ g)) =
        LinearMap.trace F W (ρ g)
  exact LinearMap.trace_conj' (ρ g) (ULift.moduleEquiv.symm : W ≃ₗ[F] ULift.{w} W)

/-- Helper for Exercise 18-18.5-2: lifting both the group and the carrier precomposes the
character with `MulEquiv.ulift`. -/
@[simp] lemma ulift_group_carrier_character_apply
    {F : Type w} [Field F] {G : Type*} [Group G]
    {W : Type w} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (ρ : Representation F G W) (g : ULift.{w} G) :
    (ulift_group_carrier_representation ρ).character g = ρ.character (MulEquiv.ulift g) := by
  let ρcomp : Representation F (ULift.{w} G) W := ρ.comp (MulEquiv.ulift.toMonoidHom)
  -- First forget the lifted carrier, then read the group element back through `MulEquiv.ulift`.
  change (ulift_carrier_representation (ρ := ρcomp)).character g = ρcomp.character g
  simp [ρcomp]

/-- Helper for Exercise 18-18.5-2: lifting the carrier by `ULift` yields an equivalent
representation on the original carrier. -/
noncomputable def ulift_carrier_representation_equiv
    {G : Type*} [Monoid G]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G W) :
    (ulift_carrier_representation ρ).Equiv ρ :=
  Representation.Equiv.mk ULift.moduleEquiv <| by
    intro g
    -- The lifted action is definitionally the original action on the underlying vector.
    ext x
    rfl

/-- Helper for Exercise 18-18.5-2: simultaneously lifting the group and carrier preserves
irreducibility over `ℂ`. -/
lemma ulift_group_carrier_representation_isIrreducible_iff
    {G : Type*} [Group G]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G W) :
    (ulift_group_carrier_representation ρ).IsIrreducible ↔ ρ.IsIrreducible := by
  constructor
  · intro hρ
    let ρcomp : Representation ℂ (ULift G) W := ρ.comp (MulEquiv.ulift.toMonoidHom)
    letI : (ulift_group_carrier_representation ρ).IsIrreducible := hρ
    have hcomp : ρcomp.IsIrreducible := by
      -- First forget the lifted carrier while keeping the same `ULift G`-action.
      exact
        isIrreducible_of_equiv_oem
          (ρ := ulift_group_carrier_representation ρ)
          (σ := ρcomp)
          (ulift_carrier_representation_equiv ρcomp)
    letI : ρcomp.IsIrreducible := hcomp
    -- Then transport irreducibility back across the group equivalence `ULift G ≃ G`.
    simpa [ρcomp] using
      (isIrreducible_comp_of_mulEquiv_complex_local (e := MulEquiv.ulift.symm) (σ := ρcomp))
  · intro hρ
    let ρcomp : Representation ℂ (ULift G) W := ρ.comp (MulEquiv.ulift.toMonoidHom)
    letI : ρ.IsIrreducible := hρ
    have hcomp : ρcomp.IsIrreducible := by
      -- Precomposition with `ULift G ≃ G` preserves the lattice of stable subspaces.
      simpa [ρcomp] using
        (isIrreducible_comp_of_mulEquiv_complex_local (e := MulEquiv.ulift) (σ := ρ))
    letI : ρcomp.IsIrreducible := hcomp
    -- Finally lift the carrier back to the same-universe `FDRep` model.
    exact
      isIrreducible_of_equiv_oem
        (ρ := ρcomp)
        (σ := ulift_group_carrier_representation ρ)
        (ulift_carrier_representation_equiv ρcomp).symm

/-- Helper for Exercise 18-18.5-2: the five standard `S₄` models used in Serre's proof,
indexed as `1`, `sgn`, `q₂`, `std`, and `sgn ⊗ std`. -/
noncomputable def s4_explicit_family
    (F : Type w) [Field F] : Fin 5 → FDRep F (ULift.{w} S4)
  | 0 =>
      FDRep.of
        (V := ULift.{w} F)
        (ulift_group_carrier_representation (Representation.trivial F S4 F))
  | 1 =>
      FDRep.of
        (V := ULift.{w} F)
        (ulift_group_carrier_representation (s4_sign_representation F))
  | 2 =>
      FDRep.of
        (V := ULift.{w}
          ((permutationAugmentationSubrepresentation F S4 (Fin 3)).toSubmodule))
        (ulift_group_carrier_representation (s4_quotient_augmentation_representation F))
  | 3 =>
      FDRep.of
        (V := ULift.{w}
          ((permutationAugmentationSubrepresentation F S4 (Fin 4)).toSubmodule))
        (ulift_group_carrier_representation (s4_standard_augmentation_representation F))
  | 4 =>
      FDRep.of
        (V := ULift.{w}
          (TensorProduct F F
            (permutationAugmentationSubrepresentation F S4 (Fin 4)).toSubmodule))
        (ulift_group_carrier_representation (s4_sign_standard_tensor_representation F))

/-- Helper for Exercise 18-18.5-2: the symmetric group `S₄` has order `24`. -/
lemma s4_card : Nat.card S4 = 24 := by
  -- Rewrite the intrinsic cardinality to the permutation count and evaluate it explicitly.
  rw [Nat.card_eq_fintype_card, Fintype.card_perm]
  norm_num

/-- Helper for Exercise 18-18.5-2: the three ordinary `S₃` models used after the
characteristic-`2` quotient descent, indexed as `1`, `sgn`, and `std`. -/
noncomputable def s3_explicit_family : Fin 3 → FDRep ℂ S3
  | 0 => FDRep.of (Representation.trivial ℂ S3 ℂ)
  | 1 => FDRep.of (s3_sign_representation ℂ)
  | 2 =>
      FDRep.of
        (V := (permutationAugmentationSubrepresentation ℂ S3 (Fin 3)).toSubmodule)
        (permutationAugmentationRepresentation ℂ S3 (Fin 3))

/-- Helper for Exercise 18-18.5-2: the trivial `S₃` character takes value `1` on a
transposition. -/
lemma s3_trivial_character_transposition :
    (Representation.trivial ℂ S3 ℂ).character (Equiv.swap (0 : Fin 3) 1) = 1 := by
  -- The trivial character is constant with value `1`.
  simp [Representation.character]

/-- Helper for Exercise 18-18.5-2: the sign character of `S₃` takes value `-1` on a
transposition. -/
lemma s3_sign_character_transposition :
    (s3_sign_representation ℂ).character (Equiv.swap (0 : Fin 3) 1) = -1 := by
  -- Reduce the one-dimensional character to the scalar value of the sign homomorphism.
  calc
    (s3_sign_representation ℂ).character (Equiv.swap (0 : Fin 3) 1)
        = ((s3_sign_character ℂ) (Equiv.swap (0 : Fin 3) 1) : ℂ) := by
            simpa [s3_sign_representation] using
              (unitCharacterRepresentation_character_apply
                (β := s3_sign_character ℂ) (Equiv.swap (0 : Fin 3) 1))
    _ = -1 := by
          simp [s3_sign_character]

/-- Helper for Exercise 18-18.5-2: the trivial `S₃` representation is irreducible over `ℂ`. -/
lemma s3_trivial_representation_isIrreducible :
    (Representation.trivial ℂ S3 ℂ).IsIrreducible := by
  letI : (unitCharacterRepresentation (1 : S3 →* ℂˣ)).IsIrreducible :=
    unitCharacterRepresentation_isIrreducible (β := (1 : S3 →* ℂˣ))
  -- The trivial slot is the constant unit-character model.
  exact
    isIrreducible_of_equiv_oem
      (ρ := unitCharacterRepresentation (1 : S3 →* ℂˣ))
      (σ := Representation.trivial ℂ S3 ℂ)
      (unitCharacterRepresentation_one_equiv_trivial (F := ℂ) (G := S3))

/-- Helper for Exercise 18-18.5-2: the sign `S₃` representation is irreducible over `ℂ`. -/
lemma s3_sign_representation_isIrreducible :
    (s3_sign_representation ℂ).IsIrreducible := by
  -- The sign slot is one-dimensional.
  simpa [s3_sign_representation] using
    (unitCharacterRepresentation_isIrreducible (β := s3_sign_character ℂ))

/-- Helper for Exercise 18-18.5-2: the explicit complex `S₃` family has degrees `1`, `1`, `2`. -/
lemma s3_explicit_family_degree (i : Fin 3) :
    Module.finrank ℂ (s3_explicit_family i) =
      match i with
      | 0 => 1
      | 1 => 1
      | 2 => 2 := by
  -- Enumerate the three slots and read off their degrees from the explicit models.
  fin_cases i <;> dsimp [s3_explicit_family]
  · exact Module.finrank_self ℂ
  · exact Module.finrank_self ℂ
  · simpa using s3_augmentation_representation_degree

/-- Helper for Exercise 18-18.5-2: the degree-`3` sign-twist slot has degree `3`. -/
lemma s4_sign_standard_tensor_representation_degree :
    Module.finrank ℂ
      (TensorProduct ℂ ℂ (permutationAugmentationSubrepresentation ℂ S4 (Fin 4)).toSubmodule) = 3 := by
  -- Tensoring with a one-dimensional character does not change the degree.
  rw [Module.finrank_tensorProduct, Module.finrank_self,
    s4_standard_augmentation_representation_degree]

/-- Helper for Exercise 18-18.5-2: the standard degree-`3` constituent takes value `1` on a
transposition. -/
lemma s4_standard_character_transposition :
    (s4_standard_augmentation_representation ℂ).character (Equiv.swap (0 : Fin 4) 1) = 1 := by
  let g : S4 := Equiv.swap (0 : Fin 4) 1
  letI : Invertible (Nat.card (Fin 4) : ℂ) := invertibleOfNonzero (by norm_num)
  have hperm_split :=
    permutation_character_eq_trivial_add_augmentation (k := ℂ) (G := S4) (X := Fin 4)
  have hfixed : (MulAction.fixedBy (Fin 4) g).ncard = 2 := by
    rw [Set.ncard_eq_toFinset_card']
    decide
  have hperm : (Representation.ofMulAction ℂ S4 (Fin 4)).character g = 2 := by
    rw [Representation.ofMulAction_character_eq_ncard_fixedBy, hfixed]
    norm_num
  have htriv : (Representation.trivial ℂ S4 ℂ).character g = 1 := by
    simp [Representation.character]
  have hvalue :
      (2 : ℂ) = 1 + permutationAugmentationCharacter ℂ S4 (Fin 4) g := by
    -- A transposition fixes two points of `Fin 4`, so the augmentation value is `1`.
    simpa [hperm, htriv] using congrFun hperm_split g
  have hvalue' := congrArg (fun z : ℂ ↦ z - 1) hvalue
  norm_num at hvalue'
  simpa [s4_standard_augmentation_representation, permutationAugmentationCharacter] using hvalue'.symm

/-- Helper for Exercise 18-18.5-2: the sign slot of `S₄` takes value `-1` on a transposition. -/
lemma s4_sign_character_transposition :
    (s4_sign_representation ℂ).character (Equiv.swap (0 : Fin 4) 1) = -1 := by
  -- Reduce the one-dimensional sign slot to the scalar value of the sign character.
  calc
    (s4_sign_representation ℂ).character (Equiv.swap (0 : Fin 4) 1)
        = ((s4_sign_character ℂ) (Equiv.swap (0 : Fin 4) 1) : ℂ) := by
            simpa [s4_sign_representation] using
              (unitCharacterRepresentation_character_apply
                (β := s4_sign_character ℂ) (Equiv.swap (0 : Fin 4) 1))
    _ = -1 := by
          simp [s4_sign_character]

/-- Helper for Exercise 18-18.5-2: the explicit complex `S₄` family has degrees
`1`, `1`, `2`, `3`, `3`. -/
lemma s4_explicit_complex_family_degree (i : Fin 5) :
    Module.finrank ℂ (s4_explicit_family ℂ i) =
      match i with
      | 0 => 1
      | 1 => 1
      | 2 => 2
      | 3 => 3
      | 4 => 3 := by
  -- Enumerate the five explicit slots and read off the carrier dimension of each one.
  fin_cases i <;> dsimp [s4_explicit_family]
  · exact
      (ULift.moduleEquiv : ULift.{0} ℂ ≃ₗ[ℂ] ℂ).finrank_eq.trans (Module.finrank_self ℂ)
  · exact
      (ULift.moduleEquiv : ULift.{0} ℂ ≃ₗ[ℂ] ℂ).finrank_eq.trans (Module.finrank_self ℂ)
  · exact
      (ULift.moduleEquiv :
        ULift.{0} ((permutationAugmentationSubrepresentation ℂ S4 (Fin 3)).toSubmodule) ≃ₗ[ℂ]
          (permutationAugmentationSubrepresentation ℂ S4 (Fin 3)).toSubmodule).finrank_eq.trans
        s4_quotient_augmentation_representation_degree
  · exact
      (ULift.moduleEquiv :
        ULift.{0} ((permutationAugmentationSubrepresentation ℂ S4 (Fin 4)).toSubmodule) ≃ₗ[ℂ]
          (permutationAugmentationSubrepresentation ℂ S4 (Fin 4)).toSubmodule).finrank_eq.trans
        s4_standard_augmentation_representation_degree
  · exact
      (ULift.moduleEquiv :
        ULift.{0}
            (TensorProduct ℂ ℂ
              (permutationAugmentationSubrepresentation ℂ S4 (Fin 4)).toSubmodule) ≃ₗ[ℂ]
          TensorProduct ℂ ℂ
            (permutationAugmentationSubrepresentation ℂ S4 (Fin 4)).toSubmodule).finrank_eq.trans
        s4_sign_standard_tensor_representation_degree

/-- Helper for Exercise 18-18.5-2: the two degree-`3` complex `S₄` slots take values `1` and
`-1` on a transposition. -/
lemma s4_degree_three_slots_character_transposition_complex :
    (s4_explicit_family ℂ 3).character (ULift.up (Equiv.swap (0 : Fin 4) 1)) = 1 ∧
      (s4_explicit_family ℂ 4).character (ULift.up (Equiv.swap (0 : Fin 4) 1)) = -1 := by
  let t : ULift S4 := ULift.up (Equiv.swap (0 : Fin 4) 1)
  constructor
  · -- The lifted standard slot keeps the same transposition value.
    simpa [t, s4_explicit_family] using
      (ulift_group_carrier_character_apply
        (ρ := s4_standard_augmentation_representation ℂ) t).trans
        s4_standard_character_transposition
  · -- The sign twist multiplies the standard value `1` by the sign value `-1`.
    calc
      (s4_explicit_family ℂ 4).character t
          = (s4_sign_standard_tensor_representation ℂ).character (Equiv.swap (0 : Fin 4) 1) := by
              simpa [t, s4_explicit_family] using
                (ulift_group_carrier_character_apply
                  (ρ := s4_sign_standard_tensor_representation ℂ) t)
      _ = (s4_sign_representation ℂ).character (Equiv.swap (0 : Fin 4) 1) *
            (s4_standard_augmentation_representation ℂ).character (Equiv.swap (0 : Fin 4) 1) := by
              simpa [s4_sign_standard_tensor_representation] using
                congrFun
                  (Representation.char_tensor
                    (ρ := s4_sign_representation ℂ)
                    (σ := s4_standard_augmentation_representation ℂ))
                  (Equiv.swap (0 : Fin 4) 1)
      _ = (-1 : ℂ) *
            (s4_standard_augmentation_representation ℂ).character (Equiv.swap (0 : Fin 4) 1) := by
            rw [s4_sign_character_transposition]
      _ = (-1 : ℂ) * 1 := by rw [s4_standard_character_transposition]
      _ = -1 := by norm_num

end

end Representation
