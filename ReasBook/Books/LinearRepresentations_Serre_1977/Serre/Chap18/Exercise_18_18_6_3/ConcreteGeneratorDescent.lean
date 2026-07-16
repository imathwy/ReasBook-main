import LinearRepresentations_Serre_1977.Serre.RepresentationTheory.RealizableOver
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_6_3.OneDimensionalTriviality
import LinearRepresentations_Serre_1977.Serre.Chap18.Definition_18_18_1_1
import LinearRepresentations_Serre_1977.Serre.Chap07.Exercise_7_7_2_4
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_6_3.A5Generators

open scoped MatrixGroups MonoidAlgebra TensorProduct

noncomputable section

universe u v

open CategoryTheory
open Representation

local notation "A5" => alternatingGroup (Fin 5)
local notation "𝔽₄" => FiniteField.Extension (ZMod 2) 2 2

namespace Representation

/-- Helper for Exercise 18-18.6-3: a non-irreducible nontrivial representation contains a proper
nonzero stable subrepresentation. -/
private theorem exists_proper_nonzero_subrepresentation_of_not_isIrreducible_local
    {K : Type*} [Field K] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) [Nontrivial V] (hρ : ¬ ρ.IsIrreducible) :
    ∃ W : Subrepresentation ρ, W ≠ ⊥ ∧ W ≠ ⊤ := by
  -- Collapse of the carrier would force the bottom and top subrepresentations to coincide.
  have hbot_top : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    have hxmem : x ∈ (⊥ : Subrepresentation ρ) := by
      have hxTop : x ∈ (⊤ : Subrepresentation ρ) := by
        change x ∈ ((⊤ : Subrepresentation ρ).toSubmodule)
        exact Submodule.mem_top
      rw [← h] at hxTop
      exact hxTop
    exact hx <| by simpa using hxmem
  letI : Nontrivial (Subrepresentation ρ) := ⟨⟨⊥, ⊤, hbot_top⟩⟩
  have hnot : ¬ ∀ W : Subrepresentation ρ, W = ⊥ ∨ W = ⊤ := by
    intro hsimple
    exact hρ ⟨hsimple⟩
  rcases not_forall.mp hnot with ⟨W, hW⟩
  refine ⟨W, ?_, ?_⟩
  · intro hWbot
    exact hW (Or.inl hWbot)
  · intro hWtop
    exact hW (Or.inr hWtop)

/-- Helper for Exercise 18-18.6-3: an irreducible degree-`2` representation cannot contain a
nonzero fixed vector. -/
private theorem irreducible_degree_two_no_nonzero_fixed_vector
    {K : Type*} [Field K] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) [ρ.IsIrreducible]
    (hV : Module.finrank K V = 2)
    {x : V} (hx : x ≠ 0)
    (hfix : ∀ g : G, ρ g x = x) :
    False := by
  let W : Subrepresentation ρ :=
    { toSubmodule := K ∙ x
      apply_mem_toSubmodule := by
        intro g y hy
        rcases Submodule.mem_span_singleton.mp hy with ⟨a, rfl⟩
        -- The fixed vector generates a stable line.
        rw [LinearMap.map_smul, hfix g]
        exact Submodule.mem_span_singleton.2 ⟨a, rfl⟩ }
  have hW_ne_bot : W ≠ ⊥ := by
    intro hW
    have hx_mem : x ∈ W.toSubmodule := Submodule.mem_span_singleton.2 ⟨1, by simp⟩
    have hx_zero : x = 0 := by
      simpa [hW] using hx_mem
    exact hx hx_zero
  have hW_ne_top : W ≠ ⊤ := by
    intro hW
    have htop : (K ∙ x) = (⊤ : Submodule K V) := by
      have : W.toSubmodule = (⊤ : Subrepresentation ρ).toSubmodule := by rw [hW]
      simpa [W] using this
    have hdim : Module.finrank K V = 1 := by
      have hspan : Module.finrank K ↥(K ∙ x) = 1 := finrank_span_singleton (K := K) hx
      rw [htop] at hspan
      simpa using hspan
    omega
  -- The invariant line is neither `⊥` nor `⊤`, contradicting irreducibility.
  exact hW_ne_top ((IsSimpleOrder.eq_bot_or_eq_top W).resolve_left hW_ne_bot)

/-- Helper for Exercise 18-18.6-3: the concrete `5`-cycle used in the fixed-vector descent
argument lies in `A₅`. -/
private theorem a5_five_cycle_mem_alternatingGroup :
    finRotate 5 ∈ alternatingGroup (Fin 5) := by
  -- The cycle `(0 1 2 3 4)` is even, so it belongs to `A₅`.
  rw [Equiv.Perm.mem_alternatingGroup]
  decide

/-- Helper for Exercise 18-18.6-3: the concrete double transposition used in the fixed-vector
descent argument lies in `A₅`. -/
private theorem a5_double_transposition_mem_alternatingGroup :
    Equiv.swap 1 2 * Equiv.swap 3 4 ∈ alternatingGroup (Fin 5) := by
  -- The product of two disjoint transpositions is even.
  rw [Equiv.Perm.mem_alternatingGroup]
  decide

/-- Helper for Exercise 18-18.6-3: the chosen `5`-cycle generator inside `A₅`. -/
private def a5_five_cycle : A5 :=
  ⟨finRotate 5, a5_five_cycle_mem_alternatingGroup⟩

/-- Helper for Exercise 18-18.6-3: the chosen double transposition generator inside `A₅`. -/
private def a5_double_transposition : A5 :=
  ⟨Equiv.swap 1 2 * Equiv.swap 3 4, a5_double_transposition_mem_alternatingGroup⟩

/-- Helper for Exercise 18-18.6-3: package the two concrete generators used to test fixed
vectors. -/
private def a5_generator_pair : Fin 2 → A5 :=
  Fin.cases a5_five_cycle fun _ ↦ a5_double_transposition

/-- Helper for Exercise 18-18.6-3: the product of the chosen `5`-cycle and double transposition
is the concrete `3`-cycle class used in the degree-`4` source branch. -/
private def a5_three_cycle : A5 :=
  a5_five_cycle * a5_double_transposition

/-- Helper for Exercise 18-18.6-3: the identity fixes all five points of the natural `A₅`-set. -/
private theorem a5_identity_fixed_points_card :
    Set.ncard (MulAction.fixedBy (Fin 5) (1 : A5)) = 5 := by
  -- This is a finite computation on the natural action of `A₅` on five letters.
  rw [Set.ncard_eq_toFinset_card']; decide

/-- Helper for Exercise 18-18.6-3: the chosen `5`-cycle fixes no point of `Fin 5`. -/
private theorem a5_five_cycle_fixed_points_card :
    Set.ncard (MulAction.fixedBy (Fin 5) a5_five_cycle) = 0 := by
  -- The explicit `5`-cycle acts transitively on the five letters.
  rw [Set.ncard_eq_toFinset_card']; decide

/-- Helper for Exercise 18-18.6-3: the inverse `5`-cycle also fixes no point of `Fin 5`. -/
private theorem a5_five_cycle_inv_fixed_points_card :
    Set.ncard (MulAction.fixedBy (Fin 5) a5_five_cycle⁻¹) = 0 := by
  -- Inversion does not change the cycle structure of the chosen `5`-cycle.
  rw [Set.ncard_eq_toFinset_card']; decide

/-- Helper for Exercise 18-18.6-3: the chosen `3`-cycle fixes exactly two points of `Fin 5`. -/
private theorem a5_three_cycle_fixed_points_card :
    Set.ncard (MulAction.fixedBy (Fin 5) a5_three_cycle) = 2 := by
  -- The explicit `3`-cycle fixes the two letters outside its support.
  rw [Set.ncard_eq_toFinset_card']; decide

/-- Helper for Exercise 18-18.6-3: over an algebraically closed characteristic-`2` field, the
canonical scalar lift identifies the Brauer character with the ordinary character on `2`-regular
elements. This is the bridge needed for the augmentation row in Serre's source route. -/
private theorem modularCharacter_eq_character_of_scalarLift_local
    {Ω : Type*} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    {V : Type*} [AddCommGroup V] [Module Ω V] [Module.Finite Ω V]
    (ρ : Representation Ω A5 V) (s : { t : A5 // IsPRegular 2 t }) :
    φ[(fun x : PrimeToPRoot 2 Ω ↦ ((x : Ωˣ) : Ω))](ρ) s = ρ.character s.1 := by
  -- Expand the ordinary character into the sum of the characteristic roots of `ρ s.1`.
  rw [Representation.character]
  rw [Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)]
  -- The scalar lift on prime-to-`2` roots simply forgets the packaging back to the same field.
  simp [Representation.modularCharacter, charpolyRoot_primeToPRoot_coe]

/-- Helper for Exercise 18-18.6-3: in characteristic `2`, the cardinality `5 = |Fin 5|` is
invertible, so the permutation-character splitting of Chapter `2` applies over `Ω`. -/
private instance a5_fin5_card_invertible_of_charTwo
    {Ω : Type*} [Field Ω] [CharP Ω 2] : Invertible (Nat.card (Fin 5) : Ω) := by
  apply invertibleOfNonzero
  have hcard : (Nat.card (Fin 5) : ℕ) = 5 := by simp
  rw [hcard]
  have h2 : (2 : Ω) = 0 := by exact_mod_cast (CharP.cast_eq_zero Ω 2)
  have h5 : ((5 : ℕ) : Ω) = 1 := by push_cast; linear_combination (2 : Ω) * h2
  rw [h5]; exact one_ne_zero

/-- Helper for Exercise 18-18.6-3: the augmentation constituent has character value `0` at the
identity in characteristic `2`. -/
private theorem a5_augmentation_character_value_one
    {Ω : Type*} [Field Ω] [CharP Ω 2] :
    permutationAugmentationCharacter Ω A5 (Fin 5) (1 : A5) = 0 := by
  have hsplit :=
    congrFun
      (Representation.permutation_character_eq_trivial_add_augmentation
        (k := Ω) (G := A5) (X := Fin 5))
      (1 : A5)
  simp only [Pi.add_apply] at hsplit
  have h2 : (2 : Ω) = 0 := by exact_mod_cast (CharP.cast_eq_zero Ω 2)
  have hperm : (Representation.ofMulAction Ω A5 (Fin 5)).character (1 : A5) = 1 := by
    -- The permutation character counts fixed points, and the identity fixes all five letters.
    rw [Representation.ofMulAction_character_eq_ncard_fixedBy, a5_identity_fixed_points_card]
    -- `(↑5 : Ω) = 1` in characteristic `2`.
    push_cast; linear_combination (2 : Ω) * h2
  have htriv : (Representation.trivial Ω A5 Ω).character (1 : A5) = 1 := by
    simp [Representation.character, Representation.trivial]
  rw [hperm, htriv] at hsplit
  -- `1 = 1 + χ` collapses to `χ = 0`.
  linear_combination -hsplit

/-- Helper for Exercise 18-18.6-3: the augmentation constituent has character value `1` on the
chosen `5`-cycle class in characteristic `2`. -/
private theorem a5_augmentation_character_value_five_cycle
    {Ω : Type*} [Field Ω] [CharP Ω 2] :
    permutationAugmentationCharacter Ω A5 (Fin 5) a5_five_cycle = 1 := by
  have hsplit :=
    congrFun
      (Representation.permutation_character_eq_trivial_add_augmentation
        (k := Ω) (G := A5) (X := Fin 5))
      a5_five_cycle
  simp only [Pi.add_apply] at hsplit
  have hperm : (Representation.ofMulAction Ω A5 (Fin 5)).character a5_five_cycle = 0 := by
    -- A `5`-cycle fixes no point in the natural action.
    rw [Representation.ofMulAction_character_eq_ncard_fixedBy]
    simpa [a5_five_cycle_fixed_points_card]
  have htriv : (Representation.trivial Ω A5 Ω).character a5_five_cycle = 1 := by
    simp [Representation.character, Representation.trivial]
  have h2 : (2 : Ω) = 0 := by exact_mod_cast (CharP.cast_eq_zero Ω 2)
  rw [hperm, htriv] at hsplit
  -- In characteristic `2`, the equality `0 = 1 + χ` forces `χ = 1`.
  linear_combination -hsplit - h2

/-- Helper for Exercise 18-18.6-3: the inverse `5`-cycle has the same augmentation-character
value `1`. -/
private theorem a5_augmentation_character_value_five_cycle_inv
    {Ω : Type*} [Field Ω] [CharP Ω 2] :
    permutationAugmentationCharacter Ω A5 (Fin 5) a5_five_cycle⁻¹ = 1 := by
  have hsplit :=
    congrFun
      (Representation.permutation_character_eq_trivial_add_augmentation
        (k := Ω) (G := A5) (X := Fin 5))
      a5_five_cycle⁻¹
  simp only [Pi.add_apply] at hsplit
  have hperm : (Representation.ofMulAction Ω A5 (Fin 5)).character a5_five_cycle⁻¹ = 0 := by
    -- The inverse `5`-cycle still acts without fixed points.
    rw [Representation.ofMulAction_character_eq_ncard_fixedBy, a5_five_cycle_inv_fixed_points_card]
    simp
  have htriv : (Representation.trivial Ω A5 Ω).character a5_five_cycle⁻¹ = 1 := by
    simp [Representation.character, Representation.trivial]
  have h2 : (2 : Ω) = 0 := by exact_mod_cast (CharP.cast_eq_zero Ω 2)
  rw [hperm, htriv] at hsplit
  -- The same characteristic-`2` cancellation gives the inverse class value.
  linear_combination -hsplit - h2

/-- Helper for Exercise 18-18.6-3: the augmentation constituent has character value `1` on the
chosen `3`-cycle class in characteristic `2`. -/
private theorem a5_augmentation_character_value_three_cycle
    {Ω : Type*} [Field Ω] [CharP Ω 2] :
    permutationAugmentationCharacter Ω A5 (Fin 5) a5_three_cycle = 1 := by
  have hsplit :=
    congrFun
      (Representation.permutation_character_eq_trivial_add_augmentation
        (k := Ω) (G := A5) (X := Fin 5))
      a5_three_cycle
  simp only [Pi.add_apply] at hsplit
  have h2 : (2 : Ω) = 0 := by exact_mod_cast (CharP.cast_eq_zero Ω 2)
  have hperm : (Representation.ofMulAction Ω A5 (Fin 5)).character a5_three_cycle = 0 := by
    -- The explicit `3`-cycle fixes exactly two points, which contributes `0` in characteristic
    -- `2`.
    rw [Representation.ofMulAction_character_eq_ncard_fixedBy, a5_three_cycle_fixed_points_card]
    -- `(↑2 : Ω) = 0` in characteristic `2`.
    push_cast; linear_combination h2
  have htriv : (Representation.trivial Ω A5 Ω).character a5_three_cycle = 1 := by
    simp [Representation.character, Representation.trivial]
  rw [hperm, htriv] at hsplit
  -- Again `0 = 1 + χ` collapses to `χ = 1` in characteristic `2`.
  linear_combination -hsplit - h2

/-- Helper for Exercise 18-18.6-3: the local `5`-cycle agrees with the canonical theorem-local
generator used in the reusable `A₅` generator API. -/
private theorem a5_five_cycle_eq_standard :
    a5_five_cycle = a5_standardFiveCycle := by
  -- Both subtype elements have the same underlying permutation, so proof irrelevance identifies
  -- them inside `A₅`.
  apply Subtype.ext
  rfl

/-- Helper for Exercise 18-18.6-3: the local double transposition agrees with the canonical
theorem-local generator used in the reusable `A₅` generator API. -/
private theorem a5_double_transposition_eq_standard :
    a5_double_transposition = a5_standardDoubleTransposition := by
  -- Again the carriers coincide definitionally, so only proof irrelevance remains.
  apply Subtype.ext
  rfl

/-- Helper for Exercise 18-18.6-3: the chosen `5`-cycle and double transposition generate all of
`A₅`. -/
private theorem a5_generator_pair_closure_eq_top :
    Subgroup.closure ({a5_five_cycle, a5_double_transposition} : Set A5) = ⊤ := by
  -- Route correction: reuse the canonical generator theorem instead of rebuilding the subgroup
  -- order computation locally.
  simpa [a5_five_cycle_eq_standard, a5_double_transposition_eq_standard] using
    (a5_standardGenerators_closure_eq_top :
      Subgroup.closure ({a5_standardFiveCycle, a5_standardDoubleTransposition} : Set A5) = ⊤)

/-- Helper for Exercise 18-18.6-3: a vector fixed by the two chosen generators is fixed by every
element of `A₅`. -/
private theorem fixed_of_fixed_generators
    {K : Type*} [Field K]
    {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K A5 V) {x : V}
    (hfive : ρ a5_five_cycle x = x)
    (htwo : ρ a5_double_transposition x = x) :
    ∀ g : A5, ρ g x = x := by
  intro g
  have hg : g ∈ Subgroup.closure ({a5_five_cycle, a5_double_transposition} : Set A5) := by
    rw [a5_generator_pair_closure_eq_top]
    simp
  -- Closure induction propagates the fixed-vector property from the two generators to all of
  -- `A₅`.
  exact Subgroup.closure_induction
    (p := fun h _ ↦ ρ h x = x)
    (fun h hh ↦ by
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
      rcases hh with rfl | rfl
      · exact hfive
      · exact htwo)
    (by simp)
    (fun a b _ _ ha hb ↦ by
      calc
        ρ (a * b) x = ρ a (ρ b x) := by simp [map_mul]
        _ = ρ a x := by rw [hb]
        _ = x := ha)
    (fun a _ ha ↦ by
      calc
        ρ a⁻¹ x = ρ a⁻¹ (ρ a x) := by rw [ha]
        _ = ρ (a⁻¹ * a) x := by simp [map_mul]
        _ = x := by simp)
    hg

/-- Helper for Exercise 18-18.6-3: record the failure of a vector to be fixed by the two concrete
generators of `A₅`. -/
private def a5_generator_defect_map
    {K : Type*} [Field K]
    {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K A5 V) :
    V →ₗ[K] Fin 2 → V :=
  LinearMap.pi fun i ↦ ρ (a5_generator_pair i) - 1

/-- Helper for Exercise 18-18.6-3: vanishing of the generator-defect map means the vector is
fixed by all of `A₅`. -/
private theorem a5_fixed_of_generator_defect_zero
    {K : Type*} [Field K]
    {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K A5 V) {x : V}
    (hzero : a5_generator_defect_map ρ x = 0) :
    ∀ g : A5, ρ g x = x := by
  have hfive : ρ a5_five_cycle x = x := by
    -- The first coordinate of the defect map measures failure to be fixed by the `5`-cycle.
    have hcoord : a5_generator_defect_map ρ x 0 = 0 := by
      simpa using congrFun hzero 0
    have := hcoord
    simp only [a5_generator_defect_map, a5_generator_pair, Fin.cases_zero,
      LinearMap.pi_apply, LinearMap.sub_apply, Module.End.one_apply] at this
    exact sub_eq_zero.mp this
  have htwo : ρ a5_double_transposition x = x := by
    -- The second coordinate records failure to be fixed by the double transposition.
    have hcoord : a5_generator_defect_map ρ x 1 = 0 := by
      simpa using congrFun hzero 1
    have := hcoord
    simp only [a5_generator_defect_map, a5_generator_pair, Fin.cases_succ,
      LinearMap.pi_apply, LinearMap.sub_apply, Module.End.one_apply] at this
    exact sub_eq_zero.mp this
  exact fixed_of_fixed_generators ρ hfive htwo

/-- Helper for Exercise 18-18.6-3: after scalar extension, the generator-defect map may be read
coordinatewise through `TensorProduct.piRight`. -/
private theorem a5_generator_defect_map_baseChange_piRight
    {K : Type*} [Field K]
    {Ω : Type*} [Field Ω] [Algebra K Ω]
    {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K A5 V) (x : Ω ⊗[K] V) :
    TensorProduct.piRight K Ω Ω (fun _ : Fin 2 ↦ V)
        (((a5_generator_defect_map ρ).baseChange Ω) x) =
      fun i ↦ (((ρ (a5_generator_pair i) - 1).baseChange Ω) x) := by
  -- Check the statement on pure tensors, then extend linearly across the tensor product.
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · ext i
    simp
  · intro z y
    ext i
    simp [a5_generator_defect_map, LinearMap.baseChange_tmul, TensorProduct.piRight_apply,
      TensorProduct.piRightHom_tmul, TensorProduct.tmul_sub]
  · intro x y hx hy
    ext i
    simp [map_add, hx, hy]

/-- Helper for Exercise 18-18.6-3: a proper nonzero subrepresentation of a two-dimensional
representation has degree `1`. -/
private theorem subrepresentation_finrank_eq_one_of_proper_nonzero_degree_two
    {K : Type*} [Field K] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K G V)
    (hV : Module.finrank K V = 2)
    (W : Subrepresentation ρ)
    (hW_ne_bot : W ≠ ⊥) (hW_ne_top : W ≠ ⊤) :
    Module.finrank K W.toSubmodule = 1 := by
  letI : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  have hW_fin_lt : Module.finrank K W.toSubmodule < 2 := by
    have hW_toSubmodule_ne_top : W.toSubmodule ≠ ⊤ := by
      intro hW_top
      exact hW_ne_top (Subrepresentation.toSubmodule_injective hW_top)
    -- A proper subrepresentation has strictly smaller dimension than the ambient degree-`2`
    -- owner.
    simpa [hV] using
      (Submodule.finrank_lt (K := K) (V := V) (s := W.toSubmodule) hW_toSubmodule_ne_top)
  have hW_fin_pos : 0 < Module.finrank K W.toSubmodule := by
    letI : Nontrivial W.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr <| by
      intro hW_bot
      exact hW_ne_bot (Subrepresentation.toSubmodule_injective hW_bot)
    -- The nonzero subrepresentation contributes positive dimension.
    exact Module.finrank_pos
  -- The only positive integer strictly below `2` is `1`.
  omega

/-- Helper for Exercise 18-18.6-3: a reducible two-dimensional `A₅`-representation already
contains a nonzero fixed vector. -/
private theorem alternatingGroup_fin5_exists_nonzero_fixed_vector_of_reducible_degree_two
    {K : Type*} [Field K]
    {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K A5 V)
    (hV : Module.finrank K V = 2)
    (hρ_not_irreducible : ¬ ρ.IsIrreducible) :
    ∃ x : V, x ≠ 0 ∧ ∀ g : A5, ρ g x = x := by
  have hV_pos : 0 < Module.finrank K V := by
    omega
  letI : FiniteDimensional K V := Module.finite_of_finrank_pos hV_pos
  letI : Nontrivial V := Module.nontrivial_of_finrank_pos hV_pos
  obtain ⟨W, hW_ne_bot, hW_ne_top⟩ :=
    exists_proper_nonzero_subrepresentation_of_not_isIrreducible_local ρ hρ_not_irreducible
  have hW_dim : Module.finrank K W.toSubmodule = 1 :=
    subrepresentation_finrank_eq_one_of_proper_nonzero_degree_two ρ hV W hW_ne_bot hW_ne_top
  letI : FiniteDimensional K W.toSubmodule := Module.finite_of_finrank_pos (by rw [hW_dim]; norm_num)
  rcases alternatingGroup_fin5_equiv_trivial_of_finrank_one W.toRepresentation hW_dim with ⟨e⟩
  let xW : W.toSubmodule := e.toLinearEquiv.symm 1
  have hxW_ne_zero : xW ≠ 0 := by
    intro hxW_zero
    have himage : e.toLinearEquiv xW = 1 := by
      simp only [xW, LinearEquiv.apply_symm_apply]
    have hone_zero : (1 : K) = 0 := by
      simpa [hxW_zero] using himage
    exact one_ne_zero hone_zero
  have hxW_fixed (g : A5) : W.toRepresentation g xW = xW := by
    apply e.toLinearEquiv.injective
    -- Evaluate the intertwining relation at the chosen generator of the trivial line.
    have hintertwine := LinearMap.congr_fun (e.isIntertwining' g) xW
    simpa [xW, Representation.trivial] using hintertwine
  refine ⟨xW.1, ?_, ?_⟩
  · intro hx_zero
    apply hxW_ne_zero
    exact Subtype.ext hx_zero
  · intro g
    -- Forgetting the subtype recovers the ambient `A₅`-fixed vector.
    exact congrArg Subtype.val (hxW_fixed g)

/-- Helper for Exercise 18-18.6-3: a degree-`2` irreducible `A₅`-representation remains
irreducible after scalar extension to any characteristic-`2` extension field. -/
theorem a5_scalarExtension_irreducible_of_irreducible_degree_two
    {K : Type u} [Field K] [Algebra 𝔽₄ K]
    {V : Type v} [AddCommGroup V] [Module K V]
    (ρ : Representation K A5 V) [ρ.IsIrreducible]
    (hV : Module.finrank K V = 2)
    {Ω : Type*} [Field Ω] [CharP Ω 2] [Algebra K Ω] :
    (Representation.scalarExtension (k := Ω) ρ).IsIrreducible := by
  -- Route correction: instead of trying to descend the whole invariant subspace abstractly, test
  -- fixed vectors against two concrete generators of `A₅` and use injectivity of the base-changed
  -- defect map.
  by_contra hρ_red
  have hVΩ :
      Module.finrank Ω (Ω ⊗[K] V) = 2 := by
    simpa [hV] using (Module.finrank_baseChange (R := Ω) (S := K) (M' := V))
  rcases alternatingGroup_fin5_exists_nonzero_fixed_vector_of_reducible_degree_two
      (ρ := Representation.scalarExtension ρ) hVΩ hρ_red with
    ⟨x, hx_ne_zero, hx_fixed⟩
  let defect : V →ₗ[K] Fin 2 → V := a5_generator_defect_map ρ
  have hdefect_zero_implies : ∀ {y : V}, defect y = 0 → y = 0 := by
    intro y hy
    by_cases hy0 : y = 0
    · exact hy0
    -- If the defect vanishes, then `y` is fixed by the generators and hence by all of `A₅`.
    have hy_fixed : ∀ g : A5, ρ g y = y :=
      a5_fixed_of_generator_defect_zero (ρ := ρ) hy
    exact False.elim <| irreducible_degree_two_no_nonzero_fixed_vector ρ hV hy0 hy_fixed
  have hdefect_inj : Function.Injective defect := by
    intro y z hyz
    apply sub_eq_zero.mp
    apply hdefect_zero_implies
    ext i
    -- Equal defects on `y` and `z` force zero defect on their difference.
    calc
      defect (y - z) i = defect y i - defect z i := by
        simp [defect, a5_generator_defect_map, map_sub]
      _ = 0 := by
        rw [congrFun hyz i, sub_self]
  have hdefect_inj_base : Function.Injective (defect.baseChange Ω) := by
    -- Injectivity is preserved by base change along the flat field extension `K → Ω`.
    simpa [defect, LinearMap.baseChange_eq_ltensor] using
      (Module.Flat.lTensor_preserves_injective_linearMap (M := Ω) defect hdefect_inj)
  have hcoord_zero :
      ∀ i : Fin 2, (((ρ (a5_generator_pair i) - 1).baseChange Ω) x) = 0 := by
    intro i
    fin_cases i
    · -- The first generator is the chosen `5`-cycle.
      simpa [Representation.scalarExtension, a5_generator_pair, LinearMap.baseChange_sub,
        LinearMap.baseChange_one, LinearMap.sub_apply] using
        sub_eq_zero.mpr (hx_fixed a5_five_cycle)
    · -- The second generator is the chosen double transposition.
      simpa [Representation.scalarExtension, a5_generator_pair, LinearMap.baseChange_sub,
        LinearMap.baseChange_one, LinearMap.sub_apply] using
        sub_eq_zero.mpr (hx_fixed a5_double_transposition)
  have hdefectΩ_zero : defect.baseChange Ω x = 0 := by
    apply (TensorProduct.piRight K Ω Ω (fun _ : Fin 2 ↦ V)).injective
    rw [a5_generator_defect_map_baseChange_piRight (ρ := ρ) (x := x)]
    ext i
    exact hcoord_zero i
  exact hx_ne_zero (hdefect_inj_base hdefectΩ_zero)

/-- Helper for Exercise 18-18.6-3: scalar extension from `𝔽₄` preserves the finrank of a
finite-dimensional `A₅`-slot. -/
theorem a5_scalarExtension_finrank_eq
    {K : Type} [Field K] [Algebra 𝔽₄ K]
    (E : FDRep 𝔽₄ A5) :
    Module.finrank K (FDRep.scalarExtension (k := K) E).V = Module.finrank 𝔽₄ E.V := by
  -- The bundled scalar extension is the usual tensor-product base change on the underlying
  -- finite-dimensional vector space.
  simpa [FDRep.scalarExtension] using
    (Module.finrank_baseChange (R := K) (S := 𝔽₄) (M' := E.V))

/-- Helper for Exercise 18-18.6-3: the scalar extension of a source degree-`2` slot is still
irreducible over any characteristic-`2` extension field. -/
theorem a5_scalarExtension_isIrreducible_of_source_slot
    {K : Type} [Field K] [Algebra 𝔽₄ K]
    (E : FDRep 𝔽₄ A5) [Simple E]
    (hE : Module.finrank 𝔽₄ E.V = 2) :
    Representation.IsIrreducible (FDRep.scalarExtension (k := K) E).ρ := by
  letI : Representation.IsIrreducible E.ρ := FDRep.isIrreducible_of_simple E
  -- `K` is an `𝔽₄`-algebra and `𝔽₄` has characteristic `2`, so `CharP K 2` is inherited.
  have hF4Char : CharP 𝔽₄ 2 := by
    rw [← Algebra.charP_iff (ZMod 2) 𝔽₄ 2]
    exact ZMod.charP 2
  letI : CharP K 2 := charP_of_injective_algebraMap (algebraMap 𝔽₄ K).injective 2
  have hEK : Module.finrank K (FDRep.scalarExtension (k := K) E).V = 2 := by
    simpa [hE] using a5_scalarExtension_finrank_eq (K := K) E
  -- Apply the degree-`2` irreducibility transport to the underlying `𝔽₄`-representation.
  simpa [FDRep.scalarExtension] using
    (a5_scalarExtension_irreducible_of_irreducible_degree_two
      (ρ := E.ρ) (Ω := K) hE)

end Representation
