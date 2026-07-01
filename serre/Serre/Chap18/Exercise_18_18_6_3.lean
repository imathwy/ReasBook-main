import Serre.RepresentationTheory.RealizableOver
import Serre.Chap16.Corollary_16_16_1_6.Bases
import Serre.Chap18.Exercise_18_18_6_3.Shared
import Serre.Chap18.Exercise_18_18_6_3.SourceCharacters
import Serre.Chap18.Exercise_18_18_6_3.ExplicitModels

-- Declarations for this item will be appended below by the statement pipeline.

open scoped MatrixGroups MonoidAlgebra TensorProduct

noncomputable section

universe u v

open CategoryTheory
open Representation

local notation "A5" => alternatingGroup (Fin 5)
local notation "𝔽₄" => FiniteField.Extension (ZMod 2) 2 2

namespace Representation

/-- Helper for Exercise 18-18.6-3: use the canonical inclusion of prime-to-`2` roots of unity in
`𝔽₄ˣ` when evaluating Brauer characters on `PRegularConjClass A₅ 2`. -/
private abbrev a5_modTwo_unitsLift_f4 : PrimeToPRoot 2 𝔽₄ →* 𝔽₄ˣ :=
  (primeToPRoots 2 𝔽₄).subtype (Subgroup.subtype_injective (primeToPRoots 2 𝔽₄))

/-- Helper for Exercise 18-18.6-3: pointwise equality of `𝔽₄`-valued functions on the
`2`-regular classes of `A₅` may be pulled back from any extension field of `𝔽₄` by injectivity of
the scalar map. -/
private theorem a5_pregular_class_function_eq_of_map_eq
    {K : Type*} [Field K] [Algebra 𝔽₄ K]
    {f g : PRegularConjClass A5 2 → 𝔽₄}
    (hfg : (fun c ↦ algebraMap 𝔽₄ K (f c)) = fun c ↦ algebraMap 𝔽₄ K (g c)) :
    f = g := by
  -- Compare the two class functions pointwise and cancel the injective coefficient map.
  funext c
  exact (algebraMap 𝔽₄ K).injective (congrFun hfg c)

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
    have hdim : Module.finrank K V = 1 := by
      simpa [W, hW] using finrank_span_singleton hx
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
    Set.ncard (MulAction.fixedBy A5 (Fin 5) (1 : A5)) = 5 := by
  -- This is a finite computation on the natural action of `A₅` on five letters.
  native_decide

/-- Helper for Exercise 18-18.6-3: the chosen `5`-cycle fixes no point of `Fin 5`. -/
private theorem a5_five_cycle_fixed_points_card :
    Set.ncard (MulAction.fixedBy A5 (Fin 5) a5_five_cycle) = 0 := by
  -- The explicit `5`-cycle acts transitively on the five letters.
  native_decide

/-- Helper for Exercise 18-18.6-3: the inverse `5`-cycle also fixes no point of `Fin 5`. -/
private theorem a5_five_cycle_inv_fixed_points_card :
    Set.ncard (MulAction.fixedBy A5 (Fin 5) a5_five_cycle⁻¹) = 0 := by
  -- Inversion does not change the cycle structure of the chosen `5`-cycle.
  native_decide

/-- Helper for Exercise 18-18.6-3: the chosen `3`-cycle fixes exactly two points of `Fin 5`. -/
private theorem a5_three_cycle_fixed_points_card :
    Set.ncard (MulAction.fixedBy A5 (Fin 5) a5_three_cycle) = 2 := by
  -- The explicit `3`-cycle fixes the two letters outside its support.
  native_decide

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

/-- Helper for Exercise 18-18.6-3: the augmentation constituent has character value `0` at the
identity in characteristic `2`. -/
private theorem a5_augmentation_character_value_one
    {Ω : Type*} [Field Ω] [CharP Ω 2] :
    (permutationAugmentationRepresentation Ω A5 (Fin 5)).character (1 : A5) = 0 := by
  have hsplit :=
    congrFun
      (Representation.permutation_character_eq_trivial_add_augmentation
        (k := Ω) (G := A5) (X := Fin 5))
      (1 : A5)
  have hperm : (Representation.ofMulAction Ω A5 (Fin 5)).character (1 : A5) = 1 := by
    -- The permutation character counts fixed points, and the identity fixes all five letters.
    rw [Representation.ofMulAction_character_eq_ncard_fixedBy]
    simpa [a5_identity_fixed_points_card]
  have htriv : (Representation.trivial Ω A5 Ω).character (1 : A5) = 1 := by
    simp [Representation.character, Representation.trivial]
  have hone : (1 : Ω) + 1 = 0 := by
    simpa [one_add_one_eq_two] using (show (2 : Ω) = 0 by simp)
  -- Subtract the trivial summand from the permutation character using `2 = 0`.
  calc
    (permutationAugmentationRepresentation Ω A5 (Fin 5)).character (1 : A5)
        =
      (permutationAugmentationRepresentation Ω A5 (Fin 5)).character (1 : A5) +
        ((1 : Ω) + 1) := by rw [hone, add_zero]
    _ =
      1 + ((Representation.trivial Ω A5 Ω).character (1 : A5) +
        (permutationAugmentationRepresentation Ω A5 (Fin 5)).character (1 : A5)) := by
          ac_rfl
    _ = 1 + (Representation.ofMulAction Ω A5 (Fin 5)).character (1 : A5) := by rw [← hsplit]
    _ = 0 := by simpa [hperm, one_add_one_eq_two] using (show (2 : Ω) = 0 by simp)

/-- Helper for Exercise 18-18.6-3: the augmentation constituent has character value `1` on the
chosen `5`-cycle class in characteristic `2`. -/
private theorem a5_augmentation_character_value_five_cycle
    {Ω : Type*} [Field Ω] [CharP Ω 2] :
    (permutationAugmentationRepresentation Ω A5 (Fin 5)).character a5_five_cycle = 1 := by
  have hsplit :=
    congrFun
      (Representation.permutation_character_eq_trivial_add_augmentation
        (k := Ω) (G := A5) (X := Fin 5))
      a5_five_cycle
  have hperm : (Representation.ofMulAction Ω A5 (Fin 5)).character a5_five_cycle = 0 := by
    -- A `5`-cycle fixes no point in the natural action.
    rw [Representation.ofMulAction_character_eq_ncard_fixedBy]
    simpa [a5_five_cycle_fixed_points_card]
  have htriv : (Representation.trivial Ω A5 Ω).character a5_five_cycle = 1 := by
    simp [Representation.character, Representation.trivial]
  have hsum :
      (Representation.trivial Ω A5 Ω).character a5_five_cycle +
          (permutationAugmentationRepresentation Ω A5 (Fin 5)).character a5_five_cycle =
        0 := by
    simpa [hperm] using hsplit.symm
  have hone : (1 : Ω) + 1 = 0 := by
    simpa [one_add_one_eq_two] using (show (2 : Ω) = 0 by simp)
  -- In characteristic `2`, the equality `1 + χ = 0` forces `χ = 1`.
  calc
    (permutationAugmentationRepresentation Ω A5 (Fin 5)).character a5_five_cycle
        =
      (permutationAugmentationRepresentation Ω A5 (Fin 5)).character a5_five_cycle +
        ((1 : Ω) + 1) := by rw [hone, add_zero]
    _ =
      ((Representation.trivial Ω A5 Ω).character a5_five_cycle +
          (permutationAugmentationRepresentation Ω A5 (Fin 5)).character a5_five_cycle) + 1 := by
            simpa [htriv] using (by ac_rfl :
              (permutationAugmentationRepresentation Ω A5 (Fin 5)).character a5_five_cycle +
                  ((1 : Ω) + 1) =
                ((1 : Ω) +
                    (permutationAugmentationRepresentation Ω A5 (Fin 5)).character
                      a5_five_cycle) +
                  1)
    _ = 1 := by simp [hsum]

/-- Helper for Exercise 18-18.6-3: the inverse `5`-cycle has the same augmentation-character
value `1`. -/
private theorem a5_augmentation_character_value_five_cycle_inv
    {Ω : Type*} [Field Ω] [CharP Ω 2] :
    (permutationAugmentationRepresentation Ω A5 (Fin 5)).character a5_five_cycle⁻¹ = 1 := by
  have hsplit :=
    congrFun
      (Representation.permutation_character_eq_trivial_add_augmentation
        (k := Ω) (G := A5) (X := Fin 5))
      a5_five_cycle⁻¹
  have hperm : (Representation.ofMulAction Ω A5 (Fin 5)).character a5_five_cycle⁻¹ = 0 := by
    -- The inverse `5`-cycle still acts without fixed points.
    rw [Representation.ofMulAction_character_eq_ncard_fixedBy]
    simpa [a5_five_cycle_inv_fixed_points_card]
  have htriv : (Representation.trivial Ω A5 Ω).character a5_five_cycle⁻¹ = 1 := by
    simp [Representation.character, Representation.trivial]
  have hsum :
      (Representation.trivial Ω A5 Ω).character a5_five_cycle⁻¹ +
          (permutationAugmentationRepresentation Ω A5 (Fin 5)).character a5_five_cycle⁻¹ =
        0 := by
    simpa [hperm] using hsplit.symm
  have hone : (1 : Ω) + 1 = 0 := by
    simpa [one_add_one_eq_two] using (show (2 : Ω) = 0 by simp)
  -- The same characteristic-`2` cancellation gives the inverse class value.
  calc
    (permutationAugmentationRepresentation Ω A5 (Fin 5)).character a5_five_cycle⁻¹
        =
      (permutationAugmentationRepresentation Ω A5 (Fin 5)).character a5_five_cycle⁻¹ +
        ((1 : Ω) + 1) := by rw [hone, add_zero]
    _ =
      ((Representation.trivial Ω A5 Ω).character a5_five_cycle⁻¹ +
          (permutationAugmentationRepresentation Ω A5 (Fin 5)).character a5_five_cycle⁻¹) + 1 := by
            simpa [htriv] using (by ac_rfl :
              (permutationAugmentationRepresentation Ω A5 (Fin 5)).character a5_five_cycle⁻¹ +
                  ((1 : Ω) + 1) =
                ((1 : Ω) +
                    (permutationAugmentationRepresentation Ω A5 (Fin 5)).character
                      a5_five_cycle⁻¹) +
                  1)
    _ = 1 := by simp [hsum]

/-- Helper for Exercise 18-18.6-3: the augmentation constituent has character value `1` on the
chosen `3`-cycle class in characteristic `2`. -/
private theorem a5_augmentation_character_value_three_cycle
    {Ω : Type*} [Field Ω] [CharP Ω 2] :
    (permutationAugmentationRepresentation Ω A5 (Fin 5)).character a5_three_cycle = 1 := by
  have hsplit :=
    congrFun
      (Representation.permutation_character_eq_trivial_add_augmentation
        (k := Ω) (G := A5) (X := Fin 5))
      a5_three_cycle
  have hperm : (Representation.ofMulAction Ω A5 (Fin 5)).character a5_three_cycle = 0 := by
    -- The explicit `3`-cycle fixes exactly two points, which contributes `0` in characteristic
    -- `2`.
    rw [Representation.ofMulAction_character_eq_ncard_fixedBy]
    simpa [a5_three_cycle_fixed_points_card]
  have htriv : (Representation.trivial Ω A5 Ω).character a5_three_cycle = 1 := by
    simp [Representation.character, Representation.trivial]
  have hsum :
      (Representation.trivial Ω A5 Ω).character a5_three_cycle +
          (permutationAugmentationRepresentation Ω A5 (Fin 5)).character a5_three_cycle =
        0 := by
    simpa [hperm] using hsplit.symm
  have hone : (1 : Ω) + 1 = 0 := by
    simpa [one_add_one_eq_two] using (show (2 : Ω) = 0 by simp)
  -- Again `1 + χ = 0` collapses to `χ = 1`.
  calc
    (permutationAugmentationRepresentation Ω A5 (Fin 5)).character a5_three_cycle
        =
      (permutationAugmentationRepresentation Ω A5 (Fin 5)).character a5_three_cycle +
        ((1 : Ω) + 1) := by rw [hone, add_zero]
    _ =
      ((Representation.trivial Ω A5 Ω).character a5_three_cycle +
          (permutationAugmentationRepresentation Ω A5 (Fin 5)).character a5_three_cycle) + 1 := by
            simpa [htriv] using (by ac_rfl :
              (permutationAugmentationRepresentation Ω A5 (Fin 5)).character a5_three_cycle +
                  ((1 : Ω) + 1) =
                ((1 : Ω) +
                    (permutationAugmentationRepresentation Ω A5 (Fin 5)).character
                      a5_three_cycle) +
                  1)
    _ = 1 := by simp [hsum]

/-- Helper for Exercise 18-18.6-3: the chosen `5`-cycle and double transposition generate all of
`A₅`. -/
private theorem a5_generator_pair_closure_eq_top :
    Subgroup.closure ({a5_five_cycle, a5_double_transposition} : Set A5) = ⊤ := by
  -- This is a finite computation on the concrete permutation group `A₅`.
  native_decide

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
    simpa [a5_generator_defect_map, a5_generator_pair] using hcoord
  have htwo : ρ a5_double_transposition x = x := by
    -- The second coordinate records failure to be fixed by the double transposition.
    have hcoord : a5_generator_defect_map ρ x 1 = 0 := by
      simpa using congrFun hzero 1
    simpa [a5_generator_defect_map, a5_generator_pair] using hcoord
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
    simp [a5_generator_defect_map, LinearMap.baseChange_tmul, TensorProduct.piRight_tmul]
  · intro x y hx hy
    ext i
    simp [map_add, hx, hy]

/-- Helper for Exercise 18-18.6-3: Serre's two source degree-`2` Brauer rows remain distinct on
the explicit `2`-regular classes of `A₅`. This records that the remaining gap is the owner-level
construction, not ambiguity in the target character functions. -/
private theorem a5_source_degree_two_character_functions_ne_modTwo :
    (fun c : PRegularConjClass A5 2 ↦
      (alternating_group_five_decomposition_matrix_mod_two
          (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
          OrdinaryIrreducible.chi3_phi_psi : 𝔽₄) -
        (alternating_group_five_decomposition_matrix_mod_two
          (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
          OrdinaryIrreducible.chi1 : 𝔽₄)) ≠
      (fun c : PRegularConjClass A5 2 ↦
        (alternating_group_five_decomposition_matrix_mod_two
            (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
            OrdinaryIrreducible.chi3_psi_phi : 𝔽₄) -
          (alternating_group_five_decomposition_matrix_mod_two
            (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
            OrdinaryIrreducible.chi1 : 𝔽₄)) := by
  intro hEq
  let cφ : PRegularConjClass A5 2 :=
    alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels.symm
      BrauerProjectiveModTwo.degreeTwo_from_chi3_phi_psi
  have hphi := congrFun a5_source_degree_two_character_function_phi_modTwo cφ
  have hpsi := congrFun a5_source_degree_two_character_function_psi_modTwo cφ
  have hvalue : ((1 : 𝔽₄) = 0) := by
    -- Evaluate both source rows on the split `5`-cycle class labeled by `φ`.
    have heval := congrFun hEq cφ
    simpa [cφ] using hphi.trans (heval.trans hpsi.symm)
  exact one_ne_zero hvalue

/-- Helper for Exercise 18-18.6-3: the reduced row `χ₃,φ,ψ - χ₁` is not the trivial Brauer
character. This is the source-faithful obstruction to a degree-`1` simple quotient in the
`φ`-branch. -/
private theorem a5_source_degree_two_character_function_phi_ne_trivial_modTwo :
    (fun c : PRegularConjClass A5 2 ↦
      (alternating_group_five_decomposition_matrix_mod_two
          (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
          OrdinaryIrreducible.chi3_phi_psi : 𝔽₄) -
        (alternating_group_five_decomposition_matrix_mod_two
          (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
          OrdinaryIrreducible.chi1 : 𝔽₄)) ≠
      fun _ : PRegularConjClass A5 2 ↦ (1 : 𝔽₄) := by
  intro hEq
  let c1 : PRegularConjClass A5 2 :=
    alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels.symm
      BrauerProjectiveModTwo.trivial
  have hphi := congrFun a5_source_degree_two_character_function_phi_modTwo c1
  have hvalue : (0 : 𝔽₄) = 1 := by
    -- Evaluate the reduced row at the identity class, where Serre's source function vanishes.
    have heval := congrFun hEq c1
    simpa [c1] using hphi.trans heval
  exact zero_ne_one hvalue

/-- Helper for Exercise 18-18.6-3: the reduced row `χ₃,ψ,φ - χ₁` is not the trivial Brauer
character. This is the symmetric degree-`1` exclusion needed in the `ψ`-branch. -/
private theorem a5_source_degree_two_character_function_psi_ne_trivial_modTwo :
    (fun c : PRegularConjClass A5 2 ↦
      (alternating_group_five_decomposition_matrix_mod_two
          (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
          OrdinaryIrreducible.chi3_psi_phi : 𝔽₄) -
        (alternating_group_five_decomposition_matrix_mod_two
          (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
          OrdinaryIrreducible.chi1 : 𝔽₄)) ≠
      fun _ : PRegularConjClass A5 2 ↦ (1 : 𝔽₄) := by
  intro hEq
  let c1 : PRegularConjClass A5 2 :=
    alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels.symm
      BrauerProjectiveModTwo.trivial
  have hpsi := congrFun a5_source_degree_two_character_function_psi_modTwo c1
  have hvalue : (0 : 𝔽₄) = 1 := by
    -- The companion reduced row also vanishes on the identity class.
    have heval := congrFun hEq c1
    simpa [c1] using hpsi.trans heval
  exact zero_ne_one hvalue

/-- Helper for Exercise 18-18.6-3: the reduced row `χ₃,φ,ψ - χ₁` is genuinely nonzero on the
explicit `φ`-labeled `5`-cycle class. This isolates the future quotient argument from any
ambiguity about whether the target Brauer row could vanish. -/
private theorem a5_source_degree_two_character_function_phi_ne_zero_modTwo :
    (fun c : PRegularConjClass A5 2 ↦
      (alternating_group_five_decomposition_matrix_mod_two
          (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
          OrdinaryIrreducible.chi3_phi_psi : 𝔽₄) -
        (alternating_group_five_decomposition_matrix_mod_two
          (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
          OrdinaryIrreducible.chi1 : 𝔽₄)) ≠
      0 := by
  intro hEq
  let cφ : PRegularConjClass A5 2 :=
    alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels.symm
      BrauerProjectiveModTwo.degreeTwo_from_chi3_phi_psi
  have hphi := congrFun a5_source_degree_two_character_function_phi_modTwo cφ
  have hvalue : (1 : 𝔽₄) = 0 := by
    -- Evaluate at the split `5`-cycle class where the `φ`-row takes the value `1`.
    have heval := congrFun hEq cφ
    simpa [Pi.zero_apply, cφ] using hphi.trans heval
  exact one_ne_zero hvalue

/-- Helper for Exercise 18-18.6-3: the companion reduced row `χ₃,ψ,φ - χ₁` is also genuinely
nonzero, now detected on the `ψ`-labeled `5`-cycle class. -/
private theorem a5_source_degree_two_character_function_psi_ne_zero_modTwo :
    (fun c : PRegularConjClass A5 2 ↦
      (alternating_group_five_decomposition_matrix_mod_two
          (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
          OrdinaryIrreducible.chi3_psi_phi : 𝔽₄) -
        (alternating_group_five_decomposition_matrix_mod_two
          (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
          OrdinaryIrreducible.chi1 : 𝔽₄)) ≠
      0 := by
  intro hEq
  let cψ : PRegularConjClass A5 2 :=
    alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels.symm
      BrauerProjectiveModTwo.degreeTwo_from_chi3_psi_phi
  have hpsi := congrFun a5_source_degree_two_character_function_psi_modTwo cψ
  have hvalue : (1 : 𝔽₄) = 0 := by
    -- Evaluate at the other split `5`-cycle class where the `ψ`-row takes the value `1`.
    have heval := congrFun hEq cψ
    simpa [Pi.zero_apply, cψ] using hpsi.trans heval
  exact one_ne_zero hvalue

/-- Helper for Exercise 18-18.6-3: Serre's reduced `φ`-row vanishes on the trivial Brauer label.
This is the concrete value that later forces the corrected owner statement to split off a trivial
constituent before reaching the degree-`2` source slot. -/
private theorem a5_source_degree_two_character_function_phi_value_at_trivial_label :
    (fun c : PRegularConjClass A5 2 ↦
      (alternating_group_five_decomposition_matrix_mod_two
          (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
          OrdinaryIrreducible.chi3_phi_psi : 𝔽₄) -
        (alternating_group_five_decomposition_matrix_mod_two
          (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
          OrdinaryIrreducible.chi1 : 𝔽₄))
      (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels.symm
        BrauerProjectiveModTwo.trivial) = 0 := by
  let c1 : PRegularConjClass A5 2 :=
    alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels.symm
      BrauerProjectiveModTwo.trivial
  -- Evaluate the explicit source row on the class singled out by the trivial Brauer label.
  have hphi := congrFun a5_source_degree_two_character_function_phi_modTwo c1
  simpa [c1] using hphi

/-- Helper for Exercise 18-18.6-3: the companion reduced `ψ`-row also vanishes on the trivial
Brauer label. This is the same obstruction to identifying a `3`-dimensional owner directly with
the reduced source row. -/
private theorem a5_source_degree_two_character_function_psi_value_at_trivial_label :
    (fun c : PRegularConjClass A5 2 ↦
      (alternating_group_five_decomposition_matrix_mod_two
          (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
          OrdinaryIrreducible.chi3_psi_phi : 𝔽₄) -
        (alternating_group_five_decomposition_matrix_mod_two
          (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
          OrdinaryIrreducible.chi1 : 𝔽₄))
      (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels.symm
        BrauerProjectiveModTwo.trivial) = 0 := by
  let c1 : PRegularConjClass A5 2 :=
    alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels.symm
      BrauerProjectiveModTwo.trivial
  -- The same explicit table computation applies to the second source row.
  have hpsi := congrFun a5_source_degree_two_character_function_psi_modTwo c1
  simpa [c1] using hpsi

/-- Helper for Exercise 18-18.6-3: Serre's reduced `φ`-row takes the value `1` on the
`φ`-labeled split `5`-cycle class. -/
private theorem a5_source_degree_two_character_function_phi_value_at_phi_label :
    (fun c : PRegularConjClass A5 2 ↦
      (alternating_group_five_decomposition_matrix_mod_two
          (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
          OrdinaryIrreducible.chi3_phi_psi : 𝔽₄) -
        (alternating_group_five_decomposition_matrix_mod_two
          (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
          OrdinaryIrreducible.chi1 : 𝔽₄))
      (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels.symm
        BrauerProjectiveModTwo.degreeTwo_from_chi3_phi_psi) = 1 := by
  let cφ : PRegularConjClass A5 2 :=
    alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels.symm
      BrauerProjectiveModTwo.degreeTwo_from_chi3_phi_psi
  -- On the `φ`-labeled split `5`-cycle class, the table isolates the first degree-`2` row.
  have hphi := congrFun a5_source_degree_two_character_function_phi_modTwo cφ
  simpa [cφ] using hphi

/-- Helper for Exercise 18-18.6-3: Serre's reduced `ψ`-row takes the value `1` on the
`ψ`-labeled split `5`-cycle class. -/
private theorem a5_source_degree_two_character_function_psi_value_at_psi_label :
    (fun c : PRegularConjClass A5 2 ↦
      (alternating_group_five_decomposition_matrix_mod_two
          (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
          OrdinaryIrreducible.chi3_psi_phi : 𝔽₄) -
        (alternating_group_five_decomposition_matrix_mod_two
          (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
          OrdinaryIrreducible.chi1 : 𝔽₄))
      (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels.symm
        BrauerProjectiveModTwo.degreeTwo_from_chi3_psi_phi) = 1 := by
  let cψ : PRegularConjClass A5 2 :=
    alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels.symm
      BrauerProjectiveModTwo.degreeTwo_from_chi3_psi_phi
  -- The companion split `5`-cycle class isolates the second degree-`2` row.
  have hpsi := congrFun a5_source_degree_two_character_function_psi_modTwo cψ
  simpa [cψ] using hpsi

/-- Helper for Exercise 18-18.6-3: every one-dimensional `A₅`-representation is equivalent to the
trivial representation, because its associated unit character must be trivial. -/
private theorem alternatingGroup_fin5_equiv_trivial_of_finrank_one
    {k : Type*} [Field k]
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k A5 V) (hV : Module.finrank k V = 1) :
    Nonempty (ρ.Equiv (Representation.trivial k A5 k)) := by
  let e : V ≃ₗ[k] k := LinearEquiv.ofFinrankEq V k (by simpa using hV)
  let ρk : Representation k A5 k :=
    { toFun := fun g ↦ e.toLinearMap.comp (ρ g) |>.comp e.symm.toLinearMap
      map_one' := by
        -- Conjugating the identity action by the chosen one-dimensional coordinate is still the
        -- identity.
        apply LinearMap.ext
        intro y
        simp [LinearMap.comp_assoc, e]
      map_mul' := by
        -- Conjugation by the fixed coordinate equivalence preserves multiplication.
        intro g h
        apply LinearMap.ext
        intro y
        simp [LinearMap.comp_assoc, e] }
  have hρk_scalar (g : A5) (x : k) : ρk g x = x * ρk g 1 := by
    -- A linear map on a one-dimensional space is determined by its value on `1`.
    calc
      ρk g x = ρk g (x • (1 : k)) := by simp
      _ = x • ρk g 1 := by rw [LinearMap.map_smul]
      _ = x * ρk g 1 := by simp [mul_comm]
  have hρk_ne_zero (g : A5) : ρk g 1 ≠ 0 := by
    -- Each group element acts invertibly, so its scalar on the one-dimensional model is nonzero.
    intro hzero
    have hzeroMap : ρk g = 0 := by
      apply LinearMap.ext
      intro y
      calc
        ρk g y = y * ρk g 1 := hρk_scalar g y
        _ = 0 := by rw [hzero, mul_zero]
    have hmul : ρk g * ρk g⁻¹ = (1 : k →ₗ[k] k) := by
      simpa using (ρk.map_mul g g⁻¹).symm
    have hidzero : (1 : k →ₗ[k] k) = 0 := by
      calc
        (1 : k →ₗ[k] k) = ρk g * ρk g⁻¹ := hmul.symm
        _ = 0 := by
              rw [hzeroMap]
              simp
    exact one_ne_zero hidzero
  let α : A5 →* kˣ :=
    { toFun := fun g ↦ Units.mk0 (ρk g 1) (hρk_ne_zero g)
      map_one' := by
        ext
        simp [ρk]
      map_mul' := by
        intro g h
        ext
        have hmul_scalar : ρk (g * h) 1 = ρk g 1 * ρk h 1 := by
          have hcomp := congrArg (fun f : k →ₗ[k] k => f 1) (ρk.map_mul g h)
          calc
            ρk (g * h) 1 = (ρk g * ρk h) 1 := by simpa using hcomp
            _ = ρk g (ρk h 1) := rfl
            _ = ρk h 1 * ρk g 1 := by
                  simpa [mul_comm] using hρk_scalar g (ρk h 1)
            _ = ρk g 1 * ρk h 1 := by ac_rfl
        exact hmul_scalar }
  have hα : α = 1 :=
    Representation.alternatingGroup_fin5_units_hom_eq_one_over_any_field α
  have hρk_trivial (g : A5) : ρk g = 1 := by
    -- After the unit-valued character collapses to `1`, the one-dimensional model is trivial.
    calc
      ρk g = oneDimensionalRepresentation α g := by
        apply LinearMap.ext
        intro y
        calc
          ρk g y = y * ρk g 1 := hρk_scalar g y
          _ = ((α g : kˣ) : k) * y := by simp [α, mul_comm]
          _ = (oneDimensionalRepresentation α g) y := by
                change ((α g : kˣ) : k) * y = ((α g : kˣ) : k) * y
                rfl
      _ = oneDimensionalRepresentation (1 : A5 →* kˣ) g := by rw [hα]
      _ = 1 := by
        ext y
        simp [oneDimensionalRepresentation]
  refine ⟨Representation.Equiv.mk e ?_⟩
  intro g
  -- Read the trivialized one-dimensional model back across the chosen coordinate change.
  simpa [ρk, LinearMap.comp_assoc] using
    congrArg (fun f : k →ₗ[k] k => f.comp e.toLinearMap) (hρk_trivial g)

/-- Helper for Exercise 18-18.6-3: a degree-`1` `A₅`-slot contributes the same Grothendieck
class as the trivial module. -/
private theorem alternatingGroup_fin5_fdRep_class_eq_trivial_of_finrank_one
    {k : Type*} [Field k] (E : FDRep k A5)
    (hE : Module.finrank k E.V = 1) :
    [E]₀ = [FDRep.of (Representation.trivial k A5 k)]₀ := by
  -- Transport the one-dimensional owner to the trivial representation and then descend to
  -- Grothendieck classes.
  rcases alternatingGroup_fin5_equiv_trivial_of_finrank_one E.ρ (by simpa using hE) with ⟨e⟩
  exact finiteRepGrothendieckClass_eq_of_nonempty_iso (L := k) (G := A5) ⟨e.toFDRepIso⟩

/-- Helper for Exercise 18-18.6-3: a nontrivial finite-dimensional `k[G]`-module admits a
nonzero quotient map onto an irreducible representation. -/
private theorem exists_irreducible_quotient_of_finiteDimensional_nontrivial_local
    {G : Type u} [Group G] {k : Type v} [Field k]
    (M : ModuleCat k[G]) [Module.Finite k[G] M] [Nontrivial M] :
    ∃ (W : Rep k G) (_ : W.ρ.IsIrreducible)
      (q : ((Rep.ofModuleMonoidAlgebra : ModuleCat k[G] ⥤ Rep k G).obj M ⟶ W)),
        q ≠ 0 := by
  let ofG : ModuleCat k[G] ⥤ Rep k G := Rep.ofModuleMonoidAlgebra
  obtain ⟨N, hN, -⟩ :=
    (eq_top_or_exists_le_coatom (⊥ : Submodule k[G] M)).resolve_left bot_ne_top
  let W : Rep k G := ofG.obj (ModuleCat.of k[G] (M ⧸ N))
  have hWirr : W.ρ.IsIrreducible := by
    -- A coatom quotient is simple on the owner-module side, hence irreducible after rebundling.
    have hSimple : IsSimpleModule k[G] (M ⧸ N) := (isSimpleModule_iff_isCoatom).2 hN
    simpa [W, Rep.ofModuleMonoidAlgebra_obj_ρ] using
      (Representation.isSimpleModule_iff_irreducible_ofModule (M ⧸ N)).mp hSimple
  let q : ofG.obj M ⟶ W := ofG.map (ModuleCat.ofHom (Submodule.mkQ N))
  have hmkQ_nonzero : Submodule.mkQ N ≠ 0 := by
    -- A proper coatom omits some vector, so the quotient map cannot vanish identically.
    obtain ⟨x, -, hx⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hN.1)
    intro hzero
    have hx0 : (Submodule.mkQ N) x = 0 := by
      simp [hzero]
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx0
    exact hx hx0
  have hq_nonzero : q ≠ 0 := by
    -- Faithfulness of `Rep.ofModuleMonoidAlgebra` reflects nonvanishing of the quotient map.
    intro hq
    apply hmkQ_nonzero
    have hmodule : ModuleCat.ofHom (Submodule.mkQ N) = 0 := ofG.map_injective hq
    ext x
    have hpoint :=
      congrArg (fun f : M ⟶ ModuleCat.of k[G] (M ⧸ N) ↦ f.hom x) hmodule
    simpa using hpoint
  exact ⟨W, hWirr, q, hq_nonzero⟩

/-- Helper for Exercise 18-18.6-3: Serre's reduced row `χ₃,φ,ψ - χ₁` should be realized by an
actual simple degree-`2` `𝔽₄[A₅]`-module. -/
private theorem a5_source_degree_two_phi_slot_over_f4 :
    ∃ E : FDRep 𝔽₄ A5,
      Simple E ∧
        Module.finrank 𝔽₄ E.V = 2 ∧
          FDRep.modularCharacterOnPRegularConjClass (p := 2) E
              (PrimeToPRoot.toFieldLift a5_modTwo_unitsLift_f4) =
            (fun c : PRegularConjClass A5 2 ↦
              (alternating_group_five_decomposition_matrix_mod_two
                  (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
                  OrdinaryIrreducible.chi3_phi_psi : 𝔽₄) -
                (alternating_group_five_decomposition_matrix_mod_two
                  (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
                  OrdinaryIrreducible.chi1 : 𝔽₄)) := by
  -- Route correction: the missing source owner cannot be a degree-`3` module whose Brauer
  -- character is already the reduced row `χ₃,φ,ψ - χ₁`, because
  -- `a5_source_degree_two_character_function_phi_value_at_trivial_label` shows that row vanishes
  -- on the trivial Brauer class. The next plan must first correct the owner statement to package
  -- a genuine degree-`3` reduction together with its trivial constituent/subquotient, and only
  -- then apply Serre's `3 = 1 + 2` quotient step.
  -- TODO for Exercise 18-18.6-3: after that corrected owner is available, take the resulting
  -- nontrivial degree-`2` quotient, rule out the degree-`1` case using
  -- `alternatingGroup_fin5_fdRep_class_eq_trivial_of_finrank_one`, and identify its Brauer
  -- character with `a5_source_degree_two_character_function_phi_modTwo`.
  sorry

/-- Helper for Exercise 18-18.6-3: Serre's reduced row `χ₃,ψ,φ - χ₁` should be realized by the
second simple degree-`2` `𝔽₄[A₅]`-module. -/
private theorem a5_source_degree_two_psi_slot_over_f4 :
    ∃ E : FDRep 𝔽₄ A5,
      Simple E ∧
        Module.finrank 𝔽₄ E.V = 2 ∧
          FDRep.modularCharacterOnPRegularConjClass (p := 2) E
              (PrimeToPRoot.toFieldLift a5_modTwo_unitsLift_f4) =
            (fun c : PRegularConjClass A5 2 ↦
              (alternating_group_five_decomposition_matrix_mod_two
                  (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
                  OrdinaryIrreducible.chi3_psi_phi : 𝔽₄) -
                (alternating_group_five_decomposition_matrix_mod_two
                  (alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels c)
                  OrdinaryIrreducible.chi1 : 𝔽₄)) := by
  -- Route correction: the same issue appears in the `ψ`-branch. The reduced row
  -- `χ₃,ψ,φ - χ₁` already vanishes on the trivial Brauer class by
  -- `a5_source_degree_two_character_function_psi_value_at_trivial_label`, so it cannot be the
  -- Brauer character of the missing degree-`3` owner itself.
  -- TODO for Exercise 18-18.6-3: once the corrected degree-`3` owner plus trivial
  -- constituent/subquotient is available, repeat the same quotient construction and identify the
  -- resulting degree-`2` Brauer character with
  -- `a5_source_degree_two_character_function_psi_modTwo`.
  sorry

/-- Helper for Exercise 18-18.6-3: a proper nonzero subrepresentation of a two-dimensional
representation has degree `1`. -/
private theorem subrepresentation_finrank_eq_one_of_proper_nonzero_degree_two
    {K : Type*} [Field K] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K G V)
    (hV : Module.finrank K V = 2)
    (W : Subrepresentation ρ)
    (hW_ne_bot : W ≠ ⊥) (hW_ne_top : W ≠ ⊤) :
    Module.finrank K W = 1 := by
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
  letI : Nontrivial V := Module.nontrivial_of_finrank_pos hV_pos
  obtain ⟨W, hW_ne_bot, hW_ne_top⟩ :=
    exists_proper_nonzero_subrepresentation_of_not_isIrreducible_local ρ hρ_not_irreducible
  have hW_dim : Module.finrank K W = 1 :=
    subrepresentation_finrank_eq_one_of_proper_nonzero_degree_two ρ hV W hW_ne_bot hW_ne_top
  rcases alternatingGroup_fin5_equiv_trivial_of_finrank_one W.toRepresentation hW_dim with ⟨e⟩
  let xW : W := e.toLinearEquiv.symm 1
  have hxW_ne_zero : xW ≠ 0 := by
    intro hxW_zero
    have himage : e.toLinearEquiv xW = 1 := by
      simp [xW]
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

/-- Helper for Exercise 18-18.6-3: a one-dimensional representation over any field is
irreducible. -/
private theorem isIrreducible_of_finrank_eq_one_local
    {k : Type*} [Field k] {G : Type*} [Monoid G]
    {V : Type*} [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (hV : Module.finrank k V = 1) :
    ρ.IsIrreducible := by
  letI : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hV
  letI : Nontrivial (Subrepresentation ρ) :=
    ⟨⊥, ⊤, fun h ↦
      bot_ne_top <| by simpa using congrArg Subrepresentation.toSubmodule h⟩
  letI : IsSimpleOrder (Submodule k V) :=
    (isSimpleModule_iff k V).1 ((isSimpleModule_iff_finrank_eq_one).2 hV)
  -- Any nonzero stable subspace of a one-dimensional representation is the whole space.
  refine IsSimpleOrder.of_forall_eq_top fun σ hσ ↦ ?_
  have hσtop : σ.toSubmodule = ⊤ := by
    rcases eq_bot_or_eq_top σ.toSubmodule with hσbot | hσtop
    · exact False.elim <| hσ <| Subrepresentation.toSubmodule_injective (by simpa using hσbot)
    · exact hσtop
  exact Subrepresentation.toSubmodule_injective (by simpa using hσtop)

/-- Helper for Exercise 18-18.6-3: the trivial `𝔽₄[A₅]`-module supplies the explicit
degree-`1` simple slot used in the final family exhaustion. -/
private theorem a5_trivial_slot_over_f4 :
    ∃ E : FDRep 𝔽₄ A5, Simple E ∧ Module.finrank 𝔽₄ E.V = 1 := by
  let E : FDRep 𝔽₄ A5 := FDRep.of (Representation.trivial 𝔽₄ A5 𝔽₄)
  have hE_finrank : Module.finrank 𝔽₄ E.V = 1 := by
    -- The bundled trivial representation keeps its one-dimensional carrier.
    simp [E]
  have hE_irreducible : E.ρ.IsIrreducible :=
    isIrreducible_of_finrank_eq_one_local E.ρ hE_finrank
  have hE_simple : Simple E := by
    -- Bundle the one-dimensional irreducibility into simplicity of the finite-dimensional owner.
    letI : E.ρ.IsIrreducible := hE_irreducible
    exact FDRep.simple_of_isIrreducible E
  exact ⟨E, hE_simple, hE_finrank⟩

/-- Helper for Exercise 18-18.6-3: two finite-dimensional `A₅`-slots with different finranks
cannot be isomorphic. This is the finrank exclusion used when separating the trivial, degree-`2`,
and degree-`4` branches inside the complete family. -/
private theorem fdRep_not_iso_of_finrank_ne_local
    {k : Type*} [Field k] {E F : FDRep k A5}
    (hfinrank : Module.finrank k E.V ≠ Module.finrank k F.V) :
    ¬ Nonempty (E ≅ F) := by
  -- An isomorphism identifies the two underlying vector spaces, so their finranks must agree.
  rintro ⟨e⟩
  exact hfinrank (FDRep.isoToLinearEquiv e).finrank_eq

/-- Helper for Exercise 18-18.6-3: over any characteristic-`2` field, Serre's degree-`4` branch
is represented by the augmentation slot for the natural action of `A₅` on five letters. -/
private abbrev a5_augmentation_slot_over
    (Ω : Type*) [Field Ω] [CharP Ω 2] : FDRep Ω A5 :=
  FDRep.of (permutationAugmentationRepresentation Ω A5 (Fin 5))

/-- Helper for Exercise 18-18.6-3: the augmentation slot for the natural action of `A₅` on five
letters still has degree `4` over every characteristic-`2` field. -/
private theorem a5_augmentation_slot_finrank
    {Ω : Type*} [Field Ω] [CharP Ω 2] :
    Module.finrank Ω (a5_augmentation_slot_over Ω).V = 4 := by
  let ε : (Fin 5 →₀ Ω) →ₗ[Ω] Ω := permutationAugmentationLinearMap Ω (Fin 5)
  have hrange : LinearMap.range ε = ⊤ := by
    -- The augmentation map is onto because a single basis vector already maps to any scalar.
    rw [LinearMap.range_eq_top]
    intro q
    refine ⟨Finsupp.single 0 q, ?_⟩
    simp [ε, permutationAugmentationLinearMap]
  have hsplit := LinearMap.finrank_range_add_finrank_ker ε
  have hrange_finrank : Module.finrank Ω (LinearMap.range ε) = 1 := by
    -- The codomain is one-dimensional, so the surjective range has finrank `1`.
    rw [hrange]
    simp
  have hdomain_finrank : Module.finrank Ω (Fin 5 →₀ Ω) = 5 := by
    -- The permutation module on five letters has the expected basis of point masses.
    simp
  have hker_finrank : Module.finrank Ω (LinearMap.ker ε) = 4 := by
    -- Rank-nullity computes the kernel dimension once the range has been identified.
    linarith [hsplit, hrange_finrank, hdomain_finrank]
  -- The bundled augmentation slot is definitionally the kernel of the augmentation map.
  simpa [a5_augmentation_slot_over, ε, permutationAugmentationSubrepresentation,
    permutationAugmentation] using hker_finrank

/-- Helper for Exercise 18-18.6-3: a degree-`2` irreducible `A₅`-representation remains
irreducible after scalar extension to any characteristic-`2` extension field. -/
private theorem a5_scalarExtension_irreducible_of_irreducible_degree_two
    {K : Type u} [Field K] [Algebra 𝔽₄ K]
    {V : Type v} [AddCommGroup V] [Module K V]
    (ρ : Representation K A5 V) [ρ.IsIrreducible]
    (hV : Module.finrank K V = 2)
    {Ω : Type*} [Field Ω] [CharP Ω 2] [Algebra K Ω] :
    (Representation.scalarExtension ρ).IsIrreducible := by
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
private theorem a5_scalarExtension_finrank_eq
    {K : Type*} [Field K] [Algebra 𝔽₄ K]
    (E : FDRep 𝔽₄ A5) :
    Module.finrank K (FDRep.scalarExtension E).V = Module.finrank 𝔽₄ E.V := by
  -- The bundled scalar extension is the usual tensor-product base change on the underlying
  -- finite-dimensional vector space.
  simpa [FDRep.scalarExtension] using
    (Module.finrank_baseChange (R := K) (S := 𝔽₄) (M' := E.V))

/-- Helper for Exercise 18-18.6-3: the scalar extension of a source degree-`2` slot is still
irreducible over any characteristic-`2` extension field. -/
private theorem a5_scalarExtension_isIrreducible_of_source_slot
    {K : Type*} [Field K] [Algebra 𝔽₄ K]
    (E : FDRep 𝔽₄ A5) [Simple E]
    (hE : Module.finrank 𝔽₄ E.V = 2) :
    (FDRep.scalarExtension E).ρ.IsIrreducible := by
  letI : E.ρ.IsIrreducible := FDRep.isIrreducible_of_simple E
  have hEK : Module.finrank K (FDRep.scalarExtension E).V = 2 := by
    simpa [hE] using a5_scalarExtension_finrank_eq (K := K) E
  -- Apply the degree-`2` irreducibility transport to the underlying `𝔽₄`-representation.
  simpa [FDRep.scalarExtension] using
    (a5_scalarExtension_irreducible_of_irreducible_degree_two
      (ρ := E.ρ) (Ω := K) hE)

/-- Helper for Exercise 18-18.6-3: once the two source degree-`2` slots over `𝔽₄` are in hand,
every irreducible degree-`2` representation over an extension of `𝔽₄` descends to `𝔽₄`. -/
private theorem a5_irreducible_degree_two_descends_to_f4
    {K : Type u} [Field K] [Algebra 𝔽₄ K]
    {V : Type v} [AddCommGroup V] [Module K V]
    (ρ : Representation K A5 V) [ρ.IsIrreducible]
    (hV : Module.finrank K V = 2) :
    Representation.IsRealizableOver 𝔽₄ ρ := by
  let Ω := AlgebraicClosure K
  letI : Field Ω := inferInstance
  letI : IsAlgClosed Ω := inferInstance
  letI : Algebra K Ω := inferInstance
  letI : IsScalarTower 𝔽₄ K Ω := inferInstance
  letI : Algebra 𝔽₄ Ω := inferInstance
  letI : CharP Ω 2 := inferInstance
  have hρΩ_irreducible : (Representation.scalarExtension ρ).IsIrreducible :=
    a5_scalarExtension_irreducible_of_irreducible_degree_two (ρ := ρ) (Ω := Ω) hV
  obtain ⟨π, hπ_pairwise, hπ_complete, φ, hφ_iso, hφ_dim⟩ :=
    a5_irreducible_degree_two_occurs_in_brauer_labeled_family_modTwo
      (Ω := Ω) (ρ := Representation.scalarExtension ρ)
      (hV := by
        simpa [hV] using (Module.finrank_baseChange (R := Ω) (S := K) (M' := V)))
  rcases a5_source_degree_two_phi_slot_over_f4 with
    ⟨Eφ, hEφ_simple, hEφ_dim, hEφ_char⟩
  rcases a5_source_degree_two_psi_slot_over_f4 with
    ⟨Eψ, hEψ_simple, hEψ_dim, hEψ_char⟩
  letI : Simple Eφ := hEφ_simple
  letI : Simple Eψ := hEψ_simple
  have hEφΩ_irreducible : (FDRep.scalarExtension Eφ).ρ.IsIrreducible :=
    a5_scalarExtension_isIrreducible_of_source_slot (K := Ω) Eφ hEφ_dim
  have hEψΩ_irreducible : (FDRep.scalarExtension Eψ).ρ.IsIrreducible :=
    a5_scalarExtension_isIrreducible_of_source_slot (K := Ω) Eψ hEψ_dim
  have hEφΩ_dim : Module.finrank Ω (FDRep.scalarExtension Eφ).V = 2 := by
    simpa [hEφ_dim] using a5_scalarExtension_finrank_eq (K := Ω) Eφ
  have hEψΩ_dim : Module.finrank Ω (FDRep.scalarExtension Eψ).V = 2 := by
    simpa [hEψ_dim] using a5_scalarExtension_finrank_eq (K := Ω) Eψ
  -- Route correction: the final family-matching argument is downstream of the corrected owner
  -- statements above. The present blocker is no longer separation of the two source rows; that
  -- distinction is already recorded by `a5_source_degree_two_character_functions_ne_modTwo`.
  -- TODO for Exercise 18-18.6-3: after replacing the false degree-`3` owner target by the
  -- corrected `1 + (χ₃,φ,ψ - χ₁)` / `1 + (χ₃,ψ,φ - χ₁)` packaging, compare the Brauer character of
  -- the slot `π φ ≅ FDRep.of (Representation.scalarExtension ρ)` with the scalar extensions of
  -- the two source slots and exclude the degree-`4` branch by finrank.
  let _ := hπ_pairwise
  let _ := hπ_complete
  let _ := hφ_iso
  let _ := hφ_dim
  let _ := hρΩ_irreducible
  let _ := hEφ_char
  let _ := hEψ_char
  let _ := hEφΩ_irreducible
  let _ := hEψΩ_irreducible
  let _ := hEφΩ_dim
  let _ := hEψΩ_dim
  sorry

/-- Helper for Exercise 18-18.6-3: Serre's source route for the two degree-`2` Brauer slots of
`A₅` in characteristic `2`. The still-open owner-level input is exactly that one gets descended
irreducible degree-`2` `𝔽₄[A₅]`-modules from the reductions of the ordinary degree-`3` rows
`χ₃,φ,ψ` and `χ₃,ψ,φ`. -/
theorem a5_degree_two_source_route_over_f4 :
    (∃ (W : Type u) (_ : AddCommGroup W) (_ : Module 𝔽₄ W) (_ : FiniteDimensional 𝔽₄ W)
        (ρ : Representation 𝔽₄ A5 W),
        ρ.IsIrreducible ∧ Module.finrank 𝔽₄ W = 2) ∧
      (∀ {K : Type u} [Field K] [Algebra 𝔽₄ K]
          {V : Type v} [AddCommGroup V] [Module K V]
          (ρ : Representation K A5 V) [ρ.IsIrreducible],
          Module.finrank K V = 2 → Representation.IsRealizableOver 𝔽₄ ρ) := by
  constructor
  · rcases a5_source_degree_two_phi_slot_over_f4 with ⟨E, hE_simple, hE_dim, -⟩
    letI : Simple E := hE_simple
    letI : E.ρ.IsIrreducible := FDRep.isIrreducible_of_simple E
    -- The existential half is now just the underlying source slot produced from the reduced
    -- `χ₃,φ,ψ` row.
    exact ⟨E.V, inferInstance, inferInstance, inferInstance, E.ρ, inferInstance, hE_dim⟩
  · intro K _ _ V _ _ ρ _ hV
    -- The descent half is isolated in the source-faithful Brauer-slot comparison helper.
    exact a5_irreducible_degree_two_descends_to_f4 ρ hV

/-- Helper for Exercise 18-18.6-3: extract one descended irreducible degree-`2` `𝔽₄[A₅]` slot
from the full source-faithful characteristic-`2` package. -/
theorem a5_degree_two_source_slot_exists_over_f4 :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module 𝔽₄ W) (_ : FiniteDimensional 𝔽₄ W)
      (ρ : Representation 𝔽₄ A5 W),
      ρ.IsIrreducible ∧ Module.finrank 𝔽₄ W = 2 := by
  -- Reuse the existential component of the full Serre source package.
  exact a5_degree_two_source_route_over_f4.1

/-- Helper for Exercise 18-18.6-3: every irreducible degree-`2` representation of `A₅` over an
extension of `𝔽₄` is realizable over `𝔽₄`. -/
theorem a5_irreducible_degree_two_realizable_over_f4
    {K : Type u} [Field K] [Algebra 𝔽₄ K]
    {V : Type v} [AddCommGroup V] [Module K V]
    (ρ : Representation K A5 V) [ρ.IsIrreducible]
    (hV : Module.finrank K V = 2) :
    Representation.IsRealizableOver 𝔽₄ ρ := by
  -- Reuse the realizability component of the same source-faithful package.
  exact a5_degree_two_source_route_over_f4.2 ρ hV

end Representation

/-- Helper for Exercise 18-18.6-3: the alternating group `A₅` has order `60`. -/
private theorem alternating_group_fin5_card_eq_sixty :
    Nat.card A5 = 60 := by
  -- Reduce to the computable `Fintype.card` of permutations on five letters.
  simpa using (show Fintype.card A5 = 60 by decide)

/-- Helper for Exercise 18-18.6-3: the chosen finite field `𝔽₄` has cardinality `4`. -/
private theorem finite_field_f4_card_eq_four :
    Nat.card 𝔽₄ = 4 := by
  -- Unfold the chosen extension field only far enough to use the generic finite-field formula.
  simpa using (FiniteField.natCard_extension (k := ZMod 2) (p := 2) (n := 2))

/-- Helper for Exercise 18-18.6-3: the special linear group `SL(2, 𝔽₄)` has order `60`. -/
private theorem specialLinearGroup_fin_two_f4_card_eq_sixty :
    Nat.card (SL(2, 𝔽₄)) = 60 := by
  letI : Fintype 𝔽₄ := Fintype.ofFinite 𝔽₄
  letI : DecidableEq 𝔽₄ := Classical.decEq 𝔽₄
  let detHom : GL (Fin 2) 𝔽₄ →* 𝔽₄ˣ := Matrix.GeneralLinearGroup.det
  have hcard_gl : Nat.card (GL (Fin 2) 𝔽₄) = 180 := by
    -- Compute `|GL(2, 𝔽₄)|` from the standard finite-field product formula.
    calc
      Nat.card (GL (Fin 2) 𝔽₄)
          = ∏ i : Fin 2, (Fintype.card 𝔽₄ ^ 2 - Fintype.card 𝔽₄ ^ (i : ℕ)) := by
            simpa using Matrix.card_GL_field (𝔽 := 𝔽₄) 2
      _ = ∏ i : Fin 2, (4 ^ 2 - 4 ^ (i : ℕ)) := by
            refine Finset.prod_congr rfl ?_
            intro i _
            rw [← Nat.card_eq_fintype_card, finite_field_f4_card_eq_four]
      _ = 180 := by decide
  have hdet_surj : Function.Surjective detHom := by
    -- Diagonal matrices `diag(u, 1)` realize every determinant value.
    intro u
    refine ⟨Matrix.GeneralLinearGroup.mk'' !![(u : 𝔽₄), 0; 0, 1] ?_, ?_⟩
    · refine ⟨u, ?_⟩
      simp
    · apply Units.ext
      simp [detHom, Matrix.det_fin_two]
  have hcard_range : Nat.card detHom.range = 3 := by
    rw [MonoidHom.range_eq_top.2 hdet_surj]
    calc
      Nat.card ((⊤ : Subgroup 𝔽₄ˣ)) = Nat.card (𝔽₄ˣ) := by
        exact Nat.card_congr Subgroup.topEquiv.toEquiv
      _ = 3 := by
        rw [Nat.card_units, finite_field_f4_card_eq_four]
  have hcard_ker :
      Nat.card detHom.ker = Nat.card (SL(2, 𝔽₄)) := by
    -- Identify `SL(2, 𝔽₄)` with the determinant kernel inside `GL(2, 𝔽₄)`.
    let e : detHom.ker ≃ SL(2, 𝔽₄) :=
      { toFun := fun g ↦
          ⟨(g.1 : Matrix (Fin 2) (Fin 2) 𝔽₄), by
            simpa [detHom] using congrArg Units.val g.2⟩
        invFun := fun g ↦
          ⟨(g : GL (Fin 2) 𝔽₄), by
            simp [detHom]⟩
        left_inv := by
          intro g
          apply Subtype.ext
          exact Matrix.GeneralLinearGroup.ext fun i j ↦ rfl
        right_inv := by
          intro g
          apply Matrix.SpecialLinearGroup.ext
          intro i j
          rfl }
    exact Nat.card_congr e
  have hker_mul_range :
      Nat.card detHom.ker * Nat.card detHom.range = Nat.card (GL (Fin 2) 𝔽₄) := by
    calc
      Nat.card detHom.ker * Nat.card detHom.range
          = Nat.card detHom.ker * detHom.ker.index := by
              rw [Subgroup.index_ker]
      _ = Nat.card (GL (Fin 2) 𝔽₄) := detHom.ker.card_mul_index
  have hcard_kernel_sixty : Nat.card detHom.ker = 60 := by
    -- Divide the general linear order by `|𝔽₄ˣ| = 3`.
    have hker_eq : Nat.card detHom.ker * 3 = 180 := by
      rw [← hcard_range, hker_mul_range, hcard_gl]
    omega
  rw [← hcard_ker]
  exact hcard_kernel_sixty

/-- Helper for Exercise 18-18.6-3: once `A₅` is embedded in `SL(2, 𝔽₄)`, the order comparison
forces the embedding to be surjective and hence an isomorphism. -/
private theorem alternatingGroup_fin5_mulEquiv_sl2_f4_of_injective
    (φ : A5 →* SL(2, 𝔽₄)) (hφ : Function.Injective φ) :
    Nonempty (A5 ≃* SL(2, 𝔽₄)) := by
  letI : Fintype 𝔽₄ := Fintype.ofFinite 𝔽₄
  letI : DecidableEq 𝔽₄ := Classical.decEq 𝔽₄
  letI : Fintype (SL(2, 𝔽₄)) := Fintype.ofFinite (SL(2, 𝔽₄))
  have hcard_dom : Fintype.card A5 = Fintype.card (SL(2, 𝔽₄)) := by
    -- Compare both groups with the shared cardinal `60`.
    rw [← Nat.card_eq_fintype_card, alternating_group_fin5_card_eq_sixty]
    rw [← Nat.card_eq_fintype_card, specialLinearGroup_fin_two_f4_card_eq_sixty]
  have hφ_surj : Function.Surjective φ := by
    exact ((Fintype.bijective_iff_injective_and_card φ).2 ⟨hφ, hcard_dom⟩).2
  exact ⟨MulEquiv.ofBijective φ ⟨hφ, hφ_surj⟩⟩

/-- Helper for Exercise 18-18.6-3: the determinant character of any `A₅ → GL(2, 𝔽₄)` hom is
trivial. -/
private theorem alternatingGroup_fin5_det_comp_gl2_eq_one
    (φ : A5 →* GL (Fin 2) 𝔽₄) :
    Matrix.GeneralLinearGroup.det.comp φ = 1 := by
  -- Compose with determinant and use that every `A₅ → 𝔽₄ˣ` character is trivial.
  exact Representation.alternatingGroup_fin5_units_hom_eq_one_over_any_field
    (L := 𝔽₄) (Matrix.GeneralLinearGroup.det.comp φ)

/-- Helper for Exercise 18-18.6-3: an injective hom `A₅ → GL(2, 𝔽₄)` already lands in
`SL(2, 𝔽₄)`, so the order comparison yields the desired group isomorphism. -/
private theorem alternatingGroup_fin5_mulEquiv_sl2_f4_of_gl2_injective
    (φ : A5 →* GL (Fin 2) 𝔽₄) (hφ : Function.Injective φ) :
    Nonempty (A5 ≃* SL(2, 𝔽₄)) := by
  let ψ : A5 →* SL(2, 𝔽₄) :=
    { toFun := fun g ↦
        ⟨(φ g : Matrix (Fin 2) (Fin 2) 𝔽₄), by
          -- The determinant side-condition is exactly the trivial determinant character.
          have hdetg : Matrix.GeneralLinearGroup.det (φ g) = 1 := by
            simpa using congrArg (fun f : A5 →* 𝔽₄ˣ => f g)
              (alternatingGroup_fin5_det_comp_gl2_eq_one φ)
          exact congrArg Units.val hdetg⟩
      map_one' := by
        -- Equality in `SL(2, 𝔽₄)` is checked entrywise on underlying matrices.
        apply Matrix.SpecialLinearGroup.ext
        intro i j
        simp
      map_mul' := by
        -- The underlying matrices multiply exactly as they do in `GL(2, 𝔽₄)`.
        intro g h
        apply Matrix.SpecialLinearGroup.ext
        intro i j
        simp }
  have hψ : Function.Injective ψ := by
    intro g h hgh
    apply hφ
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    have hmat :
        ((ψ g : SL(2, 𝔽₄)) : Matrix (Fin 2) (Fin 2) 𝔽₄) =
          ((ψ h : SL(2, 𝔽₄)) : Matrix (Fin 2) (Fin 2) 𝔽₄) := by
      -- Read the equality in `SL(2, 𝔽₄)` on the underlying matrices.
      simpa using congrArg (fun x : SL(2, 𝔽₄) => (x : Matrix (Fin 2) (Fin 2) 𝔽₄)) hgh
    simpa [ψ] using congrArg (fun A : Matrix (Fin 2) (Fin 2) 𝔽₄ => A i j) hmat
  exact alternatingGroup_fin5_mulEquiv_sl2_f4_of_injective ψ hψ

/-- Helper for Exercise 18-18.6-3: a two-dimensional trivial `A₅`-action over any field is
reducible, because the line spanned by the first basis vector is a proper stable
subrepresentation. -/
private theorem trivial_action_fin_two_not_irreducible_over_any_field
    {k : Type*} [Field k]
    (ρ : Representation k A5 (Fin 2 → k))
    (htriv : ∀ g : A5, ρ g = 1) :
    ¬ ρ.IsIrreducible := by
  letI : DecidableEq k := Classical.decEq k
  let e0 : Fin 2 → k := Pi.single 0 1
  let W : Subrepresentation ρ :=
    { toSubmodule := Submodule.span k {e0}
      apply_mem_toSubmodule := by
        -- Under the trivial action, every vector stays fixed, so the chosen line is stable.
        intro g x hx
        simpa [htriv g] using hx }
  have hW_ne_bot : W ≠ ⊥ := by
    -- The first basis vector lies in the chosen line, so that line is nonzero.
    intro hW
    have he0_mem : e0 ∈ W.toSubmodule := Submodule.subset_span (by simp [e0])
    have he0_zero : e0 = 0 := by
      simpa [hW] using he0_mem
    have : (1 : k) = 0 := by
      simpa [e0] using congrFun he0_zero 0
    exact one_ne_zero this
  have hW_ne_top : W ≠ ⊤ := by
    -- The second basis vector does not lie in the first-coordinate line, so the line is proper.
    intro hW
    let e1 : Fin 2 → k := Pi.single 1 1
    have he1_mem : e1 ∈ W.toSubmodule := by
      simpa [hW] using
        (show e1 ∈ (⊤ : Submodule k (Fin 2 → k)) by simp [e1])
    rcases Submodule.mem_span_singleton.mp he1_mem with ⟨a, ha⟩
    have h0 : a = 0 := by
      simpa [e0, e1] using congrFun ha 0
    have hone : (1 : k) = 0 := by
      simpa [e0, e1, h0] using congrFun ha 1
    exact one_ne_zero hone
  intro hρ
  -- Route correction: once the action is known to be trivial, reducibility is a pure subspace
  -- statement and no longer depends on the coefficient field.
  exact hW_ne_top ((IsSimpleOrder.eq_bot_or_eq_top W).resolve_left hW_ne_bot)

/-- Helper for Exercise 18-18.6-3: the transported standard-plane model of a two-dimensional
irreducible `𝔽₄[A₅]`-representation gives an injective hom `A₅ → GL(2, 𝔽₄)`. -/
private theorem alternatingGroup_fin5_mulEquiv_sl2_f4_of_source_witness
    (hsource :
      ∃ (W : Type) (_ : AddCommGroup W) (_ : Module 𝔽₄ W) (_ : FiniteDimensional 𝔽₄ W)
        (ρ : Representation 𝔽₄ A5 W),
        ρ.IsIrreducible ∧ Module.finrank 𝔽₄ W = 2) :
    Nonempty (A5 ≃* SL(2, 𝔽₄)) := by
  rcases hsource with ⟨W, _instAddCommGroupW, _instModuleW, _instFiniteDimensionalW,
      ρ, hρirr, hWdim⟩
  letI : ρ.IsIrreducible := hρirr
  let eFin : Fin (Module.finrank 𝔽₄ W) ≃ Fin 2 := by
    -- Reindex the canonical finite basis using the known dimension formula.
    simpa [hWdim] using (_root_.Equiv.refl (Fin 2))
  let b : Module.Basis (Fin 2) 𝔽₄ W := (Module.finBasis 𝔽₄ W).reindex eFin
  let eW : W ≃ₗ[𝔽₄] (Fin 2 → 𝔽₄) := b.equivFun
  let ρstd : Representation 𝔽₄ A5 (Fin 2 → 𝔽₄) :=
    { toFun := fun g ↦ eW.conj (ρ g)
      map_one' := by
        -- Conjugating the identity action by the basis equivalence stays the identity.
        ext x i
        simp [LinearEquiv.conj_apply_apply]
      map_mul' := by
        -- Conjugation preserves multiplication in the endomorphism ring.
        intro g h
        ext x i
        simp [LinearEquiv.conj_apply_apply] }
  have hρstd_equiv : ρ.Equiv ρstd :=
    Representation.Equiv.mk eW fun g => by
      -- The coordinate change is equivariant by construction of `ρstd`.
      ext x i
      simp [ρstd, LinearEquiv.conj_apply_apply]
  have hρstd_irreducible : ρstd.IsIrreducible := by
    -- Irreducibility is invariant under equivariant transport to the standard plane.
    exact isIrreducible_of_nonempty_equiv (ρ := ρ) (σ := ρstd) ⟨hρstd_equiv⟩
  letI : ρstd.IsIrreducible := hρstd_irreducible
  let ρGL : A5 →* LinearMap.GeneralLinearGroup 𝔽₄ (Fin 2 → 𝔽₄) :=
    { toFun := fun g ↦
        ⟨ρstd g, ρstd g⁻¹, by
          ext x i
          simp [ρstd]
        , by
          ext x i
          simp [ρstd]⟩
      map_one' := by
        -- The identity group element acts as the identity automorphism.
        apply Units.ext
        ext x i
        simp [ρstd]
      map_mul' := by
        -- Multiplication in the automorphism group matches composition of the transported action.
        intro g h
        apply Units.ext
        ext x i
        simp [ρstd, map_mul] }
  let φ : A5 →* GL (Fin 2) 𝔽₄ :=
    (Matrix.GeneralLinearGroup.toLin' (Pi.basisFun 𝔽₄ (Fin 2))).symm.toMonoidHom.comp ρGL
  have hφ_ker_ne_top : φ.ker ≠ ⊤ := by
    intro hker_top
    have htriv : ∀ g : A5, ρstd g = 1 := by
      intro g
      have hgker : g ∈ φ.ker := by
        simp [hker_top]
      have hφg : φ g = 1 := by
        simpa [MonoidHom.mem_ker] using hgker
      have hρGLg : ρGL g = 1 := by
        -- Applying the basis-dependent `GL₂ ↔ Aut` equivalence identifies `φ g` with `ρstd g`.
        simpa [φ] using congrArg
          (fun M : GL (Fin 2) 𝔽₄ =>
            Matrix.GeneralLinearGroup.toLin' (Pi.basisFun 𝔽₄ (Fin 2)) M)
          hφg
      simpa [ρGL] using congrArg
        (fun u : LinearMap.GeneralLinearGroup 𝔽₄ (Fin 2 → 𝔽₄) =>
          (u : (Fin 2 → 𝔽₄) →ₗ[𝔽₄] (Fin 2 → 𝔽₄)))
        hρGLg
    -- A top kernel would make the transported action trivial, contradicting irreducibility.
    exact (trivial_action_fin_two_not_irreducible_over_any_field (k := 𝔽₄) ρstd htriv)
      hρstd_irreducible
  have hφ_ker_eq_bot : φ.ker = ⊥ := by
    -- Simplicity of `A₅` leaves only the bottom or top kernel; the top case was excluded above.
    rcases Subgroup.Normal.eq_bot_or_eq_top (H := φ.ker)
        (inferInstance : φ.ker.Normal) with hbot | htop
    · exact hbot
    · exact False.elim (hφ_ker_ne_top htop)
  have hφ_injective : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 hφ_ker_eq_bot
  exact alternatingGroup_fin5_mulEquiv_sl2_f4_of_gl2_injective φ hφ_injective

/-- Exercise 18-18.6-3: every irreducible two-dimensional representation of `A₅` in
characteristic `2` over an extension field of `𝔽₄` is realizable over `𝔽₄`. -/
theorem alternatingGroup_fin5_irreducible_degree_two_mod_two_realizable_over_f4
    {K : Type u} [Field K] [Algebra 𝔽₄ K]
    {V : Type v} [AddCommGroup V] [Module K V]
    (ρ : Representation K A5 V) [ρ.IsIrreducible] (hV : Module.finrank K V = 2) :
    IsRealizableOver 𝔽₄ ρ := by
  -- The textbook realizability clause is exactly the second half of the local source package.
  exact Representation.a5_irreducible_degree_two_realizable_over_f4 ρ hV

/-- The alternating group `A₅` is isomorphic to the special linear group `SL(2, 𝔽₄)`. -/
theorem alternatingGroup_fin5_isomorphic_to_sl2_f4 :
    Nonempty (A5 ≃* SL(2, 𝔽₄)) := by
  -- Once one irreducible degree-`2` source model over `𝔽₄` is available, the remaining argument
  -- is the kernel-and-order comparison already isolated above.
  exact alternatingGroup_fin5_mulEquiv_sl2_f4_of_source_witness
    Representation.a5_degree_two_source_slot_exists_over_f4
