import LinearRepresentations_Serre_1977.FiniteToFintype
import LinearRepresentations_Serre_1977.Chap02.Proposition_2_2_1_2
import LinearRepresentations_Serre_1977.Chap02.Exercise_2_2_1_5
import LinearRepresentations_Serre_1977.Chap02.Theorem_2_2_3_5
import LinearRepresentations_Serre_1977.Chap06.Proposition_6_6_5_5
import LinearRepresentations_Serre_1977.Chap07.Proposition_7_7_2_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

set_option maxHeartbeats 5000000
set_option maxRecDepth 2000

universe u v w

namespace Representation

section Augmentation

variable (k : Type w) [CommSemiring k]
variable {X : Type v}

/-- Helper for Exercise 7-7.2-4: the augmentation map on the permutation module sends a finitely
supported function to the sum of its coefficients. -/
def permutationAugmentationLinearMap (X : Type v) : (X →₀ k) →ₗ[k] k :=
  Finsupp.lsum k fun _ ↦ LinearMap.id

section

variable (G : Type u) [Monoid G]
variable (X : Type v) [MulAction G X]

/-- Helper for Exercise 7-7.2-4: the augmentation map intertwines the permutation representation
with the trivial representation. -/
theorem permutationAugmentation_isIntertwining :
    ∀ g : G,
      permutationAugmentationLinearMap k X ∘ₗ (ofMulAction k G X) g =
        (trivial k G k) g ∘ₗ permutationAugmentationLinearMap k X := by
  intro g
  apply LinearMap.ext
  intro f
  induction f using Finsupp.induction_linear with
  | zero =>
      simp [permutationAugmentationLinearMap]
  | add f g hf hg =>
      simp [map_add, hf, hg]
  | single x r =>
      simp [permutationAugmentationLinearMap, Representation.ofMulAction_single]

/-- Helper for Exercise 7-7.2-4: the augmentation map as a morphism of representations. -/
def permutationAugmentation :
    IntertwiningMap (ofMulAction k G X) (trivial k G k) where
  toLinearMap := permutationAugmentationLinearMap k X
  isIntertwining' := permutationAugmentation_isIntertwining (k := k) (G := G) (X := X)

/-- Helper for Exercise 7-7.2-4: the augmentation subrepresentation is the kernel of the
augmentation map. -/
abbrev permutationAugmentationSubrepresentation :
    Subrepresentation (ofMulAction k G X) :=
  (permutationAugmentation k G X).ker

/-- Helper for Exercise 7-7.2-4: the augmentation representation is the induced action on the
augmentation kernel. -/
abbrev permutationAugmentationRepresentation [CommRing k] :
    Representation k G (permutationAugmentationSubrepresentation k G X).toSubmodule :=
  (permutationAugmentationSubrepresentation k G X).toRepresentation

end

end Augmentation

section AugmentationCharacter

variable (k : Type w) [Field k]
variable {G : Type u} [Monoid G]
variable {X : Type v} [MulAction G X] [Finite X]

/-- Helper for Exercise 7-7.2-4: the character of the augmentation representation. -/
abbrev permutationAugmentationCharacter (G : Type u) [Monoid G] (X : Type v) [MulAction G X]
    [Finite X] : G → k :=
  fun g ↦
    LinearMap.trace k (permutationAugmentationSubrepresentation k G X).toSubmodule
      ((permutationAugmentationRepresentation k G X) g)

end AugmentationCharacter

section OrbitCount

variable (k : Type w) [Field k]
variable {G : Type u} [Group G]
variable {X : Type v} [MulAction G X] [Finite X]

omit [Finite X] in
/-- Helper for Exercise 7-7.2-4: an invariant permutation vector is constant on orbits. -/
theorem ofMulAction_mem_invariants_iff_orbit_constant (f : X →₀ k) :
    f ∈ (ofMulAction k G X).invariants ↔
      ∀ x y : X, MulAction.orbitRel G X x y → f x = f y := by
  rw [Representation.mem_invariants]
  constructor
  · intro hf x y hxy
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hxy
    rcases hxy with ⟨g, hg⟩
    have hpoint := congrArg (fun z : X →₀ k => z y) (hf g⁻¹)
    simpa [hg, Representation.ofMulAction_apply] using hpoint
  · intro hconst g
    ext x
    simpa [Representation.ofMulAction_apply] using hconst (g⁻¹ • x) x <| by
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
      exact ⟨g⁻¹, rfl⟩

/-- Helper for Exercise 7-7.2-4: an invariant vector descends to a function on the orbit
quotient. -/
noncomputable def invariants_to_orbit_quotient_functions :
    (ofMulAction k G X).invariants →ₗ[k] (MulAction.orbitRel.Quotient G X → k) where
  toFun z :=
    Quotient.lift
      (fun x : X ↦ z.1 x)
      (fun x y hxy ↦
        (ofMulAction_mem_invariants_iff_orbit_constant (k := k) (G := G) (X := X) z.1).1 z.2
          x y hxy)
  map_add' z w := by
    ext q
    refine Quotient.inductionOn q fun x ↦ ?_
    rfl
  map_smul' a z := by
    ext q
    refine Quotient.inductionOn q fun x ↦ ?_
    rfl

/-- Helper for Exercise 7-7.2-4: a function on the orbit quotient pulls back to an invariant
vector. -/
noncomputable def orbit_quotient_functions_to_invariants :
    (MulAction.orbitRel.Quotient G X → k) →ₗ[k] (ofMulAction k G X).invariants where
  toFun φ := by
    refine ⟨Finsupp.equivFunOnFinite.symm (fun x : X ↦ φ ⟦x⟧), ?_⟩
    rw [Representation.mem_invariants]
    intro g
    ext x
    simp [Representation.ofMulAction_apply]
    congr 1
    apply Quotient.sound
    change g⁻¹ • x ∈ MulAction.orbit G x
    exact ⟨g⁻¹, rfl⟩
  map_add' φ ψ := by
    apply Subtype.ext
    ext x
    simp
  map_smul' a φ := by
    apply Subtype.ext
    ext x
    simp

/-- Helper for Exercise 7-7.2-4: invariant vectors on the permutation module are the same as
functions on the orbit quotient. -/
noncomputable def invariants_equiv_orbit_quotient_functions :
    (ofMulAction k G X).invariants ≃ₗ[k] (MulAction.orbitRel.Quotient G X → k) where
  toFun := invariants_to_orbit_quotient_functions (k := k) (G := G) (X := X)
  invFun := orbit_quotient_functions_to_invariants (k := k) (G := G) (X := X)
  map_add' z w := by
    ext q
    refine Quotient.inductionOn q fun x ↦ ?_
    simp [invariants_to_orbit_quotient_functions]
  map_smul' a z := by
    ext q
    refine Quotient.inductionOn q fun x ↦ ?_
    simp [invariants_to_orbit_quotient_functions]
  left_inv z := by
    apply Subtype.ext
    ext x
    simp [invariants_to_orbit_quotient_functions, orbit_quotient_functions_to_invariants]
  right_inv φ := by
    ext q
    refine Quotient.inductionOn q fun x ↦ ?_
    simp [invariants_to_orbit_quotient_functions, orbit_quotient_functions_to_invariants]

/-- Helper for Exercise 7-7.2-4: the number of orbits equals the dimension of the invariant
subspace of the permutation representation. -/
theorem orbit_count_eq_finrank_invariants :
    Nat.card (MulAction.orbitRel.Quotient G X) =
      Module.finrank k (ofMulAction k G X).invariants := by
  letI : Fintype (MulAction.orbitRel.Quotient G X) := Fintype.ofFinite _
  calc
    Nat.card (MulAction.orbitRel.Quotient G X)
      = Fintype.card (MulAction.orbitRel.Quotient G X) := by
          rw [Fintype.card_eq_nat_card]
    _ = Module.finrank k (MulAction.orbitRel.Quotient G X → k) := by
          symm
          exact Module.finrank_fintype_fun_eq_card k
    _ = Module.finrank k (ofMulAction k G X).invariants := by
          exact
            LinearEquiv.finrank_eq
              (invariants_equiv_orbit_quotient_functions (k := k) (G := G) (X := X)).symm

end OrbitCount

section FiniteGroup

variable {G : Type u} [Group G] [Finite G]
variable {X : Type v} [MulAction G X] [Finite X]

/-- Helper for Exercise 7-7.2-4: the pairing of a permutation character with the trivial
character counts the orbits of the action. -/
theorem permutation_character_pairing_with_trivial_eq_orbit_count_e7724 :
    ⟪(ofMulAction ℂ G X).character, (1 : G → ℂ)⟫ =
      Nat.card (MulAction.orbitRel.Quotient G X) := by
  letI : Fintype G := Fintype.ofFinite G
  letI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by
    exact_mod_cast Nat.card_pos.ne')
  rw [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply]
  calc
    (Nat.card G : ℂ)⁻¹ * ∑ s : G, (ofMulAction ℂ G X).character s * (1 : G → ℂ) s⁻¹
      = (Nat.card G : ℂ)⁻¹ * ∑ s : G, (ofMulAction ℂ G X).character s := by
          simp
    _ = Module.finrank ℂ (ofMulAction ℂ G X).invariants := by
          simpa using
            (Representation.card_inv_mul_sum_char_eq_finrank (ρ := ofMulAction ℂ G X))
    _ = Nat.card (MulAction.orbitRel.Quotient G X) := by
          rw [← orbit_count_eq_finrank_invariants (k := ℂ) (G := G) (X := X)]

end FiniteGroup

section SplittingCharacter

variable (k : Type w) [Field k]
variable {G : Type u} [Group G]
variable {X : Type v} [MulAction G X] [Finite X] [Nonempty X]
variable [Invertible (Nat.card X : k)]

/-- Helper for Exercise 7-7.2-4: finite permutation sets carry the canonical `Fintype`
structure. -/
local instance permutationSplittingFintype : Fintype X := Fintype.ofFinite X

/-- Helper for Exercise 7-7.2-4: the constant line inside the permutation module. -/
private def permutationConstantLinearMap :
    k →ₗ[k] (X →₀ k) where
  toFun z := Finsupp.equivFunOnFinite.symm fun _ : X ↦ ⅟(Nat.card X : k) * z
  map_add' := by
    -- The constant vector with value `⅟|X| * (z + z')` splits coordinatewise.
    intro z z'
    ext x
    simp [mul_add]
  map_smul' := by
    -- Scalar multiplication still acts pointwise on the constant vector.
    intro a z
    ext x
    simp [mul_assoc, mul_comm]

omit [Nonempty X] in
/-- Helper for Exercise 7-7.2-4: augmenting the normalized constant vector recovers the
original scalar. -/
private theorem permutationAugmentationLinearMap_comp_permutationConstantLinearMap :
    permutationAugmentationLinearMap k X ∘ₗ permutationConstantLinearMap k = LinearMap.id := by
  -- Summing the constant function `⅟|X| * z` over `X` gives back `z`.
  apply LinearMap.ext
  intro z
  have hcard : (Fintype.card X : k) ≠ 0 := by
    rw [Fintype.card_eq_nat_card]
    exact NeZero.ne (Nat.card X : k)
  simp [permutationAugmentationLinearMap, permutationConstantLinearMap, Finsupp.sum_fintype,
    nsmul_eq_mul, mul_left_comm, mul_comm]
  rw [mul_inv_cancel₀ hcard, mul_one]

omit [Nonempty X] in
/-- Helper for Exercise 7-7.2-4: subtracting the constant part leaves a vector in the
augmentation kernel. -/
private theorem permutation_residual_mem_augmentationSubrepresentation
    (f : X →₀ k) :
    f - permutationConstantLinearMap k (permutationAugmentationLinearMap k X f) ∈
      (permutationAugmentationSubrepresentation k G X).toSubmodule := by
  -- The residual has augmentation zero because the chosen constant part carries exactly the
  -- original total coefficient sum.
  change permutationAugmentationLinearMap k X
      (f - permutationConstantLinearMap k (permutationAugmentationLinearMap k X f)) = 0
  calc
    permutationAugmentationLinearMap k X
        (f - permutationConstantLinearMap k (permutationAugmentationLinearMap k X f))
      = permutationAugmentationLinearMap k X f
          - permutationAugmentationLinearMap k X
              (permutationConstantLinearMap k (permutationAugmentationLinearMap k X f)) := by
          simp
    _ = permutationAugmentationLinearMap k X f - permutationAugmentationLinearMap k X f := by
          have hconst :
              permutationAugmentationLinearMap k X
                  (permutationConstantLinearMap k (permutationAugmentationLinearMap k X f)) =
                permutationAugmentationLinearMap k X f := by
            simpa using
              LinearMap.congr_fun
                (permutationAugmentationLinearMap_comp_permutationConstantLinearMap
                  (k := k) (X := X))
                (permutationAugmentationLinearMap k X f)
          rw [hconst]
    _ = 0 := sub_self _

/-- Helper for Exercise 7-7.2-4: the permutation module splits as the constant line together
with the augmentation kernel. -/
private def permutationToTrivialProdAugmentationLinearEquiv :
    (X →₀ k) ≃ₗ[k] k × (permutationAugmentationSubrepresentation k G X).toSubmodule where
  toFun f :=
    (permutationAugmentationLinearMap k X f,
      ⟨f - permutationConstantLinearMap k (permutationAugmentationLinearMap k X f),
        permutation_residual_mem_augmentationSubrepresentation (k := k) (G := G) (X := X) f⟩)
  invFun z := permutationConstantLinearMap k z.1 + z.2.1
  left_inv := by
    intro f
    -- Adding back the extracted constant part reconstructs the original vector.
    ext x
    simp [sub_eq_add_neg, add_left_comm]
  right_inv := by
    intro z
    rcases z with ⟨z, f⟩
    -- The first coordinate stores the augmentation and the second stores the residual part.
    have hconst : permutationAugmentationLinearMap k X (permutationConstantLinearMap k z) = z := by
      simpa using
        LinearMap.congr_fun
          (permutationAugmentationLinearMap_comp_permutationConstantLinearMap
            (k := k) (X := X))
          z
    apply Prod.ext
    · simp [hconst]
    · apply Subtype.ext
      ext x
      simp [sub_eq_add_neg, add_assoc, add_comm, hconst]
  map_add' := by
    intro f g
    -- Both coordinates are linear, so the splitting map is linear coordinatewise.
    apply Prod.ext
    · change
        permutationAugmentationLinearMap k X (f + g) =
          permutationAugmentationLinearMap k X f + permutationAugmentationLinearMap k X g
      simp
    · apply Subtype.ext
      change
        f + g -
            permutationConstantLinearMap k
              (permutationAugmentationLinearMap k X (f + g)) =
          (f - permutationConstantLinearMap k (permutationAugmentationLinearMap k X f)) +
            (g - permutationConstantLinearMap k (permutationAugmentationLinearMap k X g))
      rw [map_add, map_add]
      ext x
      simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  map_smul' := by
    intro a f
    -- The same coordinatewise computation handles scalar multiplication.
    apply Prod.ext
    · change
        permutationAugmentationLinearMap k X (a • f) =
          a • permutationAugmentationLinearMap k X f
      simp
    · apply Subtype.ext
      change
        a • f -
            permutationConstantLinearMap k
              (permutationAugmentationLinearMap k X (a • f)) =
          a •
            (f - permutationConstantLinearMap k (permutationAugmentationLinearMap k X f))
      rw [map_smul, map_smul]
      ext x
      simp [sub_eq_add_neg]

/-- Helper for Exercise 7-7.2-4: the permutation action fixes constant vectors. -/
private theorem ofMulAction_constant_vector_eq_self
    (g : G) (z : k) :
    (ofMulAction k G X) g (permutationConstantLinearMap k z) =
      permutationConstantLinearMap k z := by
  -- A constant finitely supported function stays constant after permuting coordinates.
  ext x
  simp [permutationConstantLinearMap, Representation.ofMulAction_apply]

/-- Helper for Exercise 7-7.2-4: the residual term is transported to the residual of the
transported vector. -/
private theorem ofMulAction_apply_residual_eq
    (g : G) (f : X →₀ k) :
    (ofMulAction k G X) g
        (f - permutationConstantLinearMap k (permutationAugmentationLinearMap k X f)) =
      (ofMulAction k G X) g f -
        permutationConstantLinearMap k
          (permutationAugmentationLinearMap k X ((ofMulAction k G X) g f)) := by
  -- Transport subtraction through the action and then rewrite the constant term by augmentation
  -- equivariance.
  have haug :
      permutationAugmentationLinearMap k X ((ofMulAction k G X) g f) =
        permutationAugmentationLinearMap k X f := by
    simpa using
      congrArg (fun l : (X →₀ k) →ₗ[k] k ↦ l f) ((permutationAugmentation k G X).isIntertwining' g)
  calc
    (ofMulAction k G X) g
        (f - permutationConstantLinearMap k (permutationAugmentationLinearMap k X f))
      = (ofMulAction k G X) g f -
          (ofMulAction k G X) g
            (permutationConstantLinearMap k (permutationAugmentationLinearMap k X f)) := by
            simp
    _ = (ofMulAction k G X) g f -
          permutationConstantLinearMap k (permutationAugmentationLinearMap k X f) := by
            rw [ofMulAction_constant_vector_eq_self (k := k) (X := X) g]
    _ = (ofMulAction k G X) g f -
          permutationConstantLinearMap k
            (permutationAugmentationLinearMap k X ((ofMulAction k G X) g f)) := by
            rw [haug]

/-- Helper for Exercise 7-7.2-4: the augmentation subrepresentation action carries the residual
of `f` to the residual of the transported vector. -/
private theorem residual_subrepresentation_action_eq
    (g : G) (f : X →₀ k) :
    (permutationAugmentationRepresentation k G X) g
        ⟨f - permutationConstantLinearMap k (permutationAugmentationLinearMap k X f),
          permutation_residual_mem_augmentationSubrepresentation
            (k := k) (G := G) (X := X) f⟩ =
      ⟨(ofMulAction k G X) g f -
          permutationConstantLinearMap k
            (permutationAugmentationLinearMap k X ((ofMulAction k G X) g f)),
        permutation_residual_mem_augmentationSubrepresentation
          (k := k) (G := G) (X := X) ((ofMulAction k G X) g f)⟩ := by
  -- The subrepresentation action is inherited from the ambient permutation action.
  apply Subtype.ext
  exact ofMulAction_apply_residual_eq (k := k) (G := G) (X := X) g f

/-- Helper for Exercise 7-7.2-4: the permutation representation is equivalent to the product of
the trivial line and the augmentation representation. -/
private def permutation_equiv_trivial_prod_augmentation :
    (ofMulAction k G X).Equiv
      ((trivial k G k).prod
        (permutationAugmentationRepresentation k G X)) :=
  Representation.Equiv.mk (permutationToTrivialProdAugmentationLinearEquiv (k := k) (G := G)
    (X := X)) fun g ↦ by
      -- The first coordinate is augmentation equivariance, and the second is the transported
      -- residual inside the augmentation kernel.
      apply LinearMap.ext
      intro f
      apply Prod.ext
      · have hcoord :=
          congrArg
            (fun l : (X →₀ k) →ₗ[k] k ↦ l f)
            ((permutationAugmentation k G X).isIntertwining' g)
        simpa [Representation.trivial] using hcoord
      · simpa [permutationToTrivialProdAugmentationLinearEquiv] using
          (residual_subrepresentation_action_eq (g := g) (f := f)).symm

/-- Helper for Exercise 7-7.2-4: an equivalence with a product representation identifies the
character with the sum of the product characters. -/
private theorem character_eq_of_equiv_prod
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {W : Type*} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    {U : Type*} [AddCommGroup U] [Module k U] [FiniteDimensional k U]
    (ρ : Representation k G V) (σ : Representation k G W) (τ : Representation k G U)
    (e : ρ.Equiv (σ.prod τ)) :
    ρ.character = σ.character + τ.character := by
  -- Transport the character across the product equivalence and use additivity on products.
  ext g
  calc
    ρ.character g = (σ.prod τ).character g := by
      simpa using congrFun (Representation.char_iso e) g
    _ = σ.character g + τ.character g := by
      exact congrFun (Representation.char_prod σ τ) g

/-- Helper for Exercise 7-7.2-4: the permutation character splits as the sum of the trivial and
augmentation characters. -/
theorem permutation_character_eq_trivial_add_augmentation :
    (ofMulAction k G X).character =
      (trivial k G k).character + permutationAugmentationCharacter k G X := by
  -- Take characters in the owner-level splitting of the permutation module.
  letI : FiniteDimensional k (permutationAugmentationSubrepresentation k G X).toSubmodule :=
    inferInstance
  exact
    character_eq_of_equiv_prod (k := k)
      (V := X →₀ k)
      (W := k)
      (U := (permutationAugmentationSubrepresentation k G X).toSubmodule)
      (ρ := ofMulAction k G X)
      (σ := trivial k G k)
      (τ := (permutationAugmentationRepresentation k G X :
        Representation k G (permutationAugmentationSubrepresentation k G X).toSubmodule))
      (permutation_equiv_trivial_prod_augmentation (k := k) (G := G) (X := X))

end SplittingCharacter

section PairCharacter

variable (k : Type w) [Field k]
variable {G : Type u} [Group G]
variable {X : Type v} [MulAction G X] [Finite X]

/-- Helper for Exercise 7-7.2-4: the permutation character of the diagonal action on `X × X` is
the square of the permutation character of `X`. -/
theorem pair_permutation_character_eq_square :
    (ofMulAction k G (X × X)).character = (ofMulAction k G X).character ^ 2 := by
  ext g
  have hfixed :
      MulAction.fixedBy (X × X) g =
        Set.prod (MulAction.fixedBy X g) (MulAction.fixedBy X g) := by
    ext p
    rcases p with ⟨x, y⟩
    constructor
    · intro hp
      have hp' : g • (x, y) = (x, y) := by
        simpa [MulAction.mem_fixedBy] using hp
      have hx : g • x = x := congrArg Prod.fst hp'
      have hy : g • y = y := congrArg Prod.snd hp'
      have hp'' : g • x = x ∧ g • y = y := ⟨hx, hy⟩
      simpa [Set.mem_prod, MulAction.mem_fixedBy] using hp''
    · intro hp
      have hp' : g • x = x ∧ g • y = y := by
        simpa [Set.mem_prod, MulAction.mem_fixedBy] using hp
      have hpair : g • (x, y) = (x, y) := by
        rcases hp' with ⟨hx, hy⟩
        simp [Prod.smul_mk, hx, hy]
      simpa [MulAction.mem_fixedBy] using hpair
  calc
    (ofMulAction k G (X × X)).character g
      = ↑(MulAction.fixedBy (X × X) g).ncard := by
          simpa using ofMulAction_character_eq_ncard_fixedBy (k := k) (G := G) (X := X × X) g
    _ = ↑(((MulAction.fixedBy X g).prod (MulAction.fixedBy X g)).ncard) := by
          rw [hfixed]
    _ = ↑((MulAction.fixedBy X g).ncard * (MulAction.fixedBy X g).ncard) := by
          change (↑(((MulAction.fixedBy X g) ×ˢ (MulAction.fixedBy X g)).ncard) : k) = _
          simpa using congrArg (fun n : ℕ ↦ (n : k))
            (Set.ncard_prod (s := MulAction.fixedBy X g) (t := MulAction.fixedBy X g))
    _ = (↑(MulAction.fixedBy X g).ncard : k) ^ 2 := by
          simp [pow_two]
    _ = ((ofMulAction k G X).character g) ^ 2 := by
          simp [ofMulAction_character_eq_ncard_fixedBy]

end PairCharacter

section DoubleTransitiveCase

variable {G : Type u} [Group G]
variable {X : Type v} [MulAction G X]

/-- Helper for Exercise 7-7.2-4: a `2`-pretransitive action is exactly one whose pair orbits are
determined by whether the two entries are equal. -/
theorem isTwoPretransitive_iff_pairActionHasDiagonalOrbits :
    MulAction.IsMultiplyPretransitive G X 2 ↔
      ∀ x y x' y' : X, (∃ s : G, s • (x, y) = (x', y')) ↔ (x = y ↔ x' = y') := by
  constructor
  · intro h2 x y x' y'
    constructor
    · intro hpair
      rcases hpair with ⟨s, hs⟩
      rcases Prod.mk.inj hs with ⟨hx, hy⟩
      constructor
      · intro hxy
        rw [hxy] at hx hy
        exact hx.symm.trans hy
      · intro hx'y'
        exact (smul_left_cancel_iff s).mp <| hx.trans (hx'y'.trans hy.symm)
    · intro hdiag
      by_cases hxy : x = y
      · have hx'y' : x' = y' := hdiag.mp hxy
        have hpre : MulAction.IsPretransitive G X :=
          MulAction.isPretransitive_of_is_two_pretransitive (G := G) (α := X)
        rcases hpre.exists_smul_eq x x' with ⟨s, hs⟩
        refine ⟨s, ?_⟩
        refine Prod.ext hs ?_
        simpa [hxy, hx'y'] using hs
      · have hx'y' : x' ≠ y' := by
          intro h'
          exact hxy (hdiag.mpr h')
        rw [MulAction.is_two_pretransitive_iff] at h2
        rcases h2 hxy hx'y' with ⟨s, hsx, hsy⟩
        exact ⟨s, Prod.ext hsx hsy⟩
  · intro hpair
    rw [MulAction.is_two_pretransitive_iff]
    intro a b c d hab hcd
    have hdiag : a = b ↔ c = d := by
      simp [hab, hcd]
    rcases (hpair a b c d).2 hdiag with ⟨g, hg⟩
    rcases Prod.mk.inj hg with ⟨hga, hgb⟩
    exact ⟨g, hga, hgb⟩

section NontrivialCase

variable [Nontrivial X]

section FiniteGroup

variable [Finite G] [Finite X]

/-- Helper for Exercise 7-7.2-4: diagonal status is constant on pair orbits. -/
private theorem pair_orbit_diagonal_classifier_well_defined [DecidableEq X]
    (p q : X × X) (hpq : MulAction.orbitRel G (X × X) p q) :
    decide (p.1 = p.2) = decide (q.1 = q.2) := by
  rcases p with ⟨x, y⟩
  rcases q with ⟨x', y'⟩
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hpq
  rcases hpq with ⟨s, hs⟩
  rcases Prod.mk.inj hs with ⟨hx, hy⟩
  -- Equality of the two coordinates is preserved by the diagonal action.
  by_cases hx'y' : x' = y'
  · have hxy : x = y := by
      calc
        x = s • x' := hx.symm
        _ = s • y' := by rw [hx'y']
        _ = y := hy
    simp [hxy, hx'y']
  · have hxy : x ≠ y := by
      intro h
      apply hx'y'
      exact (smul_left_cancel_iff s).mp <| by
        calc
          s • x' = x := hx
          _ = y := h
          _ = s • y' := hy.symm
    simp [hxy, hx'y']

/-- Helper for Exercise 7-7.2-4: an orbit of the pair action remembers only whether it lies on
the diagonal. -/
noncomputable def pair_orbit_diagonal_classifier [DecidableEq X] :
    MulAction.orbitRel.Quotient G (X × X) → Bool :=
  Quotient.lift
    (fun p : X × X ↦ decide (p.1 = p.2))
    (fun p q hpq ↦ pair_orbit_diagonal_classifier_well_defined (G := G) (X := X) p q hpq)

/-- Helper for Exercise 7-7.2-4: the diagonal classifier hits both boolean values. -/
private theorem pair_orbit_diagonal_classifier_surjective [DecidableEq X] :
    Function.Surjective (pair_orbit_diagonal_classifier (G := G) (X := X)) := by
  intro b
  cases b with
  | false =>
      rcases exists_pair_ne X with ⟨x, y, hxy⟩
      refine ⟨⟦(x, y)⟧, ?_⟩
      -- Any off-diagonal pair is classified by `false`.
      simp [pair_orbit_diagonal_classifier, hxy]
  | true =>
      rcases exists_pair_ne X with ⟨x, y, hxy⟩
      refine ⟨⟦(x, x)⟧, ?_⟩
      -- Any diagonal pair is classified by `true`.
      simp [pair_orbit_diagonal_classifier]

/-- Helper for Exercise 7-7.2-4: the pair-orbit quotient has cardinality `2` exactly when the
diagonal classifier is bijective. -/
private theorem pair_orbit_quotient_card_two_iff_diagonal_classifier_bijective [DecidableEq X] :
    Nat.card (MulAction.orbitRel.Quotient G (X × X)) = 2 ↔
      Function.Bijective (pair_orbit_diagonal_classifier (G := G) (X := X)) := by
  letI : Fintype (MulAction.orbitRel.Quotient G (X × X)) := Fintype.ofFinite _
  -- A surjection from a two-point finite set is bijective exactly when the quotient has two
  -- elements.
  constructor
  · intro hcard
    rw [Fintype.bijective_iff_surjective_and_card]
    refine ⟨pair_orbit_diagonal_classifier_surjective (G := G) (X := X), ?_⟩
    calc
      Fintype.card (MulAction.orbitRel.Quotient G (X × X))
        = Nat.card (MulAction.orbitRel.Quotient G (X × X)) := by
            symm
            exact Nat.card_eq_fintype_card
      _ = 2 := hcard
      _ = Fintype.card Bool := by
            simp
  · intro hbij
    calc
      Nat.card (MulAction.orbitRel.Quotient G (X × X))
        = Nat.card Bool := Nat.card_eq_of_bijective _ hbij
      _ = Fintype.card Bool := by
            rw [Nat.card_eq_fintype_card]
      _ = 2 := by
            simp

/-- Helper for Exercise 7-7.2-4: the pair-orbit criterion is equivalent to the scalar-product
condition `⟪χ², 1⟫ = 2`. -/
theorem pairActionHasDiagonalOrbits_iff_character_square_pairing_eq_two :
    (∀ x y x' y' : X, (∃ s : G, s • (x, y) = (x', y')) ↔ (x = y ↔ x' = y')) ↔
      ⟪(ofMulAction ℂ G X).character ^ 2, (1 : G → ℂ)⟫ = 2 := by
  classical
  -- Route correction: identify pair orbits by their diagonal status, then apply the orbit-count
  -- formula to the pair action.
  constructor
  · intro hpair
    have hinj :
        Function.Injective (pair_orbit_diagonal_classifier (G := G) (X := X)) := by
      intro q₁ q₂ hq
      refine Quotient.inductionOn₂ q₁ q₂ (fun p q ↦ ?_) hq
      rcases p with ⟨x, y⟩
      rcases q with ⟨x', y'⟩
      intro hdiagBool
      have hdiag : x = y ↔ x' = y' := by
        by_cases hxy : x = y <;> by_cases hx'y' : x' = y' <;>
          simp [pair_orbit_diagonal_classifier, hxy, hx'y'] at hdiagBool ⊢
      rcases (hpair x y x' y').2 hdiag with ⟨s, hs⟩
      apply Quotient.sound
      refine ⟨s⁻¹, ?_⟩
      have hs' := congrArg (fun z : X × X ↦ s⁻¹ • z) hs
      simpa using hs'.symm
    have hbij :
        Function.Bijective (pair_orbit_diagonal_classifier (G := G) (X := X)) :=
      ⟨hinj, pair_orbit_diagonal_classifier_surjective (G := G) (X := X)⟩
    have hcard :
        Nat.card (MulAction.orbitRel.Quotient G (X × X)) = 2 :=
      (pair_orbit_quotient_card_two_iff_diagonal_classifier_bijective (G := G) (X := X)).2 hbij
    calc
      ⟪(ofMulAction ℂ G X).character ^ 2, (1 : G → ℂ)⟫
        = ⟪(ofMulAction ℂ G (X × X)).character, (1 : G → ℂ)⟫ := by
            rw [pair_permutation_character_eq_square (k := ℂ) (G := G) (X := X)]
      _ = Nat.card (MulAction.orbitRel.Quotient G (X × X)) := by
            exact permutation_character_pairing_with_trivial_eq_orbit_count_e7724 (G := G) (X := X × X)
      _ = 2 := by
            exact_mod_cast hcard
  · intro hchi
    have hcard :
        Nat.card (MulAction.orbitRel.Quotient G (X × X)) = 2 := by
      have hcardC :
          (Nat.card (MulAction.orbitRel.Quotient G (X × X)) : ℂ) = 2 := by
        calc
          (Nat.card (MulAction.orbitRel.Quotient G (X × X)) : ℂ)
            = ⟪(ofMulAction ℂ G (X × X)).character, (1 : G → ℂ)⟫ := by
                exact_mod_cast
                  (permutation_character_pairing_with_trivial_eq_orbit_count_e7724
                    (G := G) (X := X × X)).symm
          _ = ⟪(ofMulAction ℂ G X).character ^ 2, (1 : G → ℂ)⟫ := by
                rw [pair_permutation_character_eq_square (k := ℂ) (G := G) (X := X)]
          _ = 2 := hchi
      exact_mod_cast hcardC
    have hbij :
        Function.Bijective (pair_orbit_diagonal_classifier (G := G) (X := X)) :=
      (pair_orbit_quotient_card_two_iff_diagonal_classifier_bijective (G := G) (X := X)).1 hcard
    intro x y x' y'
    constructor
    · intro hxy
      rcases hxy with ⟨s, hs⟩
      rcases Prod.mk.inj hs with ⟨hx, hy⟩
      constructor
      · intro hxy'
        calc
          x' = s • x := by simpa using hx.symm
          _ = s • y := by simp [hxy']
          _ = y' := by simpa using hy
      · intro hx'y'
        exact (smul_left_cancel_iff s).mp <| by
          calc
            s • x = x' := by simpa using hx
            _ = y' := hx'y'
            _ = s • y := by simpa using hy.symm
    · intro hdiag
      have hdiagBool :
          pair_orbit_diagonal_classifier (G := G) (X := X) ⟦(x, y)⟧ =
            pair_orbit_diagonal_classifier (G := G) (X := X) ⟦(x', y')⟧ := by
        by_cases hxy : x = y <;> by_cases hx'y' : x' = y' <;>
          simp [pair_orbit_diagonal_classifier, hxy, hx'y'] at hdiag ⊢
      have hq :
          (⟦(x, y)⟧ : MulAction.orbitRel.Quotient G (X × X)) = ⟦(x', y')⟧ :=
        hbij.1 hdiagBool
      have horbit : MulAction.orbitRel G (X × X) (x, y) (x', y') := Quotient.exact hq
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at horbit
      rcases horbit with ⟨s, hs⟩
      refine ⟨s⁻¹, ?_⟩
      have hs' := congrArg (fun z : X × X ↦ s⁻¹ • z) hs
      simpa using hs'.symm

end FiniteGroup

section TransitiveCase

variable [Finite G] [Finite X] [MulAction.IsPretransitive G X]

/-- Helper for Exercise 7-7.2-4: a finite pretransitive permutation action contributes exactly
one copy of the unit character. -/
private theorem pretransitive_permutation_pairing_with_trivial_eq_one :
    ⟪(ofMulAction ℂ G X).character, (1 : G → ℂ)⟫ = 1 := by
  let x₀ : X := Classical.choice inferInstance
  letI : Unique (MulAction.orbitRel.Quotient G X) :=
    { default := ⟦x₀⟧
      uniq := by
        intro q
        refine Quotient.inductionOn q fun y ↦ ?_
        rcases (inferInstance : MulAction.IsPretransitive G X).exists_smul_eq x₀ y with ⟨g, hg⟩
        exact Quotient.sound ⟨g, hg⟩ }
  -- In the pretransitive case the orbit quotient has one point, so the orbit-count formula gives
  -- pairing `1`.
  calc
    ⟪(ofMulAction ℂ G X).character, (1 : G → ℂ)⟫ =
        Nat.card (MulAction.orbitRel.Quotient G X) := by
          exact permutation_character_pairing_with_trivial_eq_orbit_count_e7724 (G := G) (X := X)
    _ = 1 := by
          simp

/-- Helper for Exercise 7-7.2-4: in a transitive action, the augmentation character is orthogonal
to the trivial character. -/
theorem augmentation_character_pairing_with_trivial_eq_zero :
    ⟪permutationAugmentationCharacter ℂ G X, (1 : G → ℂ)⟫ = 0 := by
  letI : Fintype G := Fintype.ofFinite G
  letI : Invertible (Nat.card X : ℂ) := invertibleOfNonzero (by
    exact_mod_cast Nat.card_pos.ne')
  have htriv : (trivial ℂ G ℂ).character = (1 : G → ℂ) := by
    ext g
    simp [Representation.character, Representation.trivial]
  have hpair_one : ⟪(1 : G → ℂ), (1 : G → ℂ)⟫ = 1 := by
    -- The unit character has normalized self-pairing `1`.
    rw [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply]
    simp [Nat.card_eq_fintype_card]
  have hsplit :
      ⟪(ofMulAction ℂ G X).character, (1 : G → ℂ)⟫ =
        ⟪(trivial ℂ G ℂ).character, (1 : G → ℂ)⟫ +
          ⟪permutationAugmentationCharacter ℂ G X, (1 : G → ℂ)⟫ := by
    -- Pair the splitting identity with the unit character and use additivity in the first slot.
    rw [permutation_character_eq_trivial_add_augmentation (k := ℂ) (G := G) (X := X)]
    rw [Representation.groupFunctionPairing_add_left]
  have hperm : ⟪(ofMulAction ℂ G X).character, (1 : G → ℂ)⟫ = 1 :=
    pretransitive_permutation_pairing_with_trivial_eq_one (G := G) (X := X)
  -- Subtract the trivial contribution from the permutation pairing.
  rw [htriv, hpair_one] at hsplit
  rw [hperm] at hsplit
  have hsub := congrArg (fun z : ℂ ↦ z - 1) hsplit
  simpa using hsub.symm

/-- Helper for Exercise 7-7.2-4: for an inversion-invariant class function, pairing its square
with the trivial character agrees with its self-pairing. -/
private theorem groupFunctionPairing_sq_trivial_eq_self_of_inv_invariant
    (φ : G → ℂ) (hinv : ∀ g : G, φ g⁻¹ = φ g) :
    ⟪φ ^ 2, (1 : G → ℂ)⟫ = ⟪φ, φ⟫ := by
  letI : Fintype G := Fintype.ofFinite G
  rw [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply]
  rw [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  simp [pow_two, hinv g]

/-- Helper for Exercise 7-7.2-4: the augmentation character of a transitive action is invariant
under inversion. -/
private theorem permutationAugmentationCharacter_inv_invariant (g : G) :
    permutationAugmentationCharacter ℂ G X g⁻¹ = permutationAugmentationCharacter ℂ G X g := by
  letI : Fintype G := Fintype.ofFinite G
  letI : Invertible (Nat.card X : ℂ) := invertibleOfNonzero (by
    exact_mod_cast Nat.card_pos.ne')
  have htriv : (trivial ℂ G ℂ).character = (1 : G → ℂ) := by
    ext s
    simp [Representation.character, Representation.trivial]
  have hχ :
      (ofMulAction ℂ G X).character =
        (1 : G → ℂ) + permutationAugmentationCharacter ℂ G X := by
    -- Split the permutation character into the trivial line plus the augmentation character.
    simpa [htriv] using
      (permutation_character_eq_trivial_add_augmentation (k := ℂ) (G := G) (X := X))
  have hperm_inv :
      (ofMulAction ℂ G X).character g⁻¹ = (ofMulAction ℂ G X).character g := by
    -- Fixed points of `g` and `g⁻¹` have the same cardinality.
    have hcard :
        (MulAction.fixedBy X g⁻¹).ncard = (MulAction.fixedBy X g).ncard := by
      exact congrArg Set.ncard (MulAction.fixedBy_inv (G := G) (α := X) g)
    rw [ofMulAction_character_eq_ncard_fixedBy, ofMulAction_character_eq_ncard_fixedBy]
    exact congrArg (fun n : ℕ ↦ (n : ℂ)) hcard
  have hg_inv : (ofMulAction ℂ G X).character g⁻¹ =
      1 + permutationAugmentationCharacter ℂ G X g⁻¹ := by
    simpa using congrFun hχ g⁻¹
  have hg : (ofMulAction ℂ G X).character g =
      1 + permutationAugmentationCharacter ℂ G X g := by
    simpa using congrFun hχ g
  -- Cancel the trivial contribution from the equalities at `g` and `g⁻¹`.
  have hsum :
      1 + permutationAugmentationCharacter ℂ G X g⁻¹ =
        1 + permutationAugmentationCharacter ℂ G X g :=
    hg_inv.symm.trans <| hperm_inv.trans hg
  simpa using hsum

/-- Helper for Exercise 7-7.2-4: in the transitive case, the square-pairing of the permutation
character is `1` plus the self-pairing of the augmentation character. -/
private theorem permutation_square_pairing_eq_one_add_augmentation_self_pairing :
    ⟪(ofMulAction ℂ G X).character ^ 2, (1 : G → ℂ)⟫ =
      1 + ⟪permutationAugmentationCharacter ℂ G X, permutationAugmentationCharacter ℂ G X⟫ := by
  letI : Fintype G := Fintype.ofFinite G
  letI : Invertible (Nat.card X : ℂ) := invertibleOfNonzero (by
    exact_mod_cast Nat.card_pos.ne')
  let ψ : G → ℂ := permutationAugmentationCharacter ℂ G X
  have htriv : (trivial ℂ G ℂ).character = (1 : G → ℂ) := by
    ext g
    simp [Representation.character, Representation.trivial]
  have hχ : (ofMulAction ℂ G X).character = (1 : G → ℂ) + ψ := by
    -- Rewrite the permutation character as the sum of the trivial and augmentation characters.
    simpa [htriv, ψ] using
      (permutation_character_eq_trivial_add_augmentation (k := ℂ) (G := G) (X := X))
  have hpair_one : ⟪(1 : G → ℂ), (1 : G → ℂ)⟫ = 1 := by
    -- The unit character has normalized self-pairing `1`.
    rw [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply]
    simp [Nat.card_eq_fintype_card]
  have hψ_zero : ⟪ψ, (1 : G → ℂ)⟫ = 0 := by
    -- Transitivity makes the augmentation character orthogonal to the trivial character.
    simpa [ψ] using augmentation_character_pairing_with_trivial_eq_zero (G := G) (X := X)
  have hsq : ((1 : G → ℂ) + ψ) ^ 2 = (1 : G → ℂ) + (2 : ℂ) • ψ + ψ ^ 2 := by
    -- Expand `(1 + ψ)^2` pointwise.
    ext g
    simp [pow_two]
    ring
  -- Pair the expansion with the trivial character and simplify the mixed term away.
  calc
    ⟪(ofMulAction ℂ G X).character ^ 2, (1 : G → ℂ)⟫
        = ⟪((1 : G → ℂ) + ψ) ^ 2, (1 : G → ℂ)⟫ := by
            rw [hχ]
    _ = ⟪(1 : G → ℂ) + (2 : ℂ) • ψ + ψ ^ 2, (1 : G → ℂ)⟫ := by
          rw [hsq]
    _ = ⟪(1 : G → ℂ), (1 : G → ℂ)⟫ +
          ⟪(2 : ℂ) • ψ, (1 : G → ℂ)⟫ +
          ⟪ψ ^ 2, (1 : G → ℂ)⟫ := by
          rw [Representation.groupFunctionPairing_add_left]
          rw [Representation.groupFunctionPairing_add_left]
    _ = 1 + 2 * ⟪ψ, (1 : G → ℂ)⟫ + ⟪ψ ^ 2, (1 : G → ℂ)⟫ := by
          rw [hpair_one, Representation.groupFunctionPairing_smul_left]
    _ = 1 + ⟪ψ ^ 2, (1 : G → ℂ)⟫ := by
          rw [hψ_zero]
          ring
    _ = 1 + ⟪ψ, ψ⟫ := by
          have hsq_pair : ⟪ψ ^ 2, (1 : G → ℂ)⟫ = ⟪ψ, ψ⟫ := by
            exact groupFunctionPairing_sq_trivial_eq_self_of_inv_invariant ψ
              (fun g ↦ permutationAugmentationCharacter_inv_invariant (G := G) (X := X) g)
          rw [hsq_pair]

/-- Helper for Exercise 7-7.2-4: normalized character pairings are unchanged by precomposing both
entries with a group equivalence. -/
private theorem groupFunctionPairing_precomp_mulEquiv_local
    [Fintype G] {H : Type*} [Group H] [Finite H] [Fintype H]
    (e : G ≃* H) (f g : H → ℂ) :
    ⟪(fun x : G ↦ f (e x)), fun x : G ↦ g (e x)⟫ = ⟪f, g⟫ := by
  have hcard : Fintype.card G = Fintype.card H := Fintype.card_congr e.toEquiv
  rw [Representation.groupFunctionPairingOverField, Representation.groupFunctionPairingOverField, hcard]
  congr 1
  simpa [MulEquiv.map_inv] using (Equiv.sum_comp e.toEquiv (fun y : H ↦ f y⁻¹ * g y))

/-- Helper for Exercise 7-7.2-4: the self-pairing of the augmentation character detects
irreducibility of the augmentation representation. -/
private theorem augmentation_character_self_pairing_eq_one_iff_isIrreducible :
    ⟪permutationAugmentationCharacter ℂ G X, permutationAugmentationCharacter ℂ G X⟫ = 1 ↔
      (permutationAugmentationRepresentation ℂ G X).IsIrreducible := by
  let ρ : Representation ℂ G (permutationAugmentationSubrepresentation ℂ G X).toSubmodule :=
    permutationAugmentationRepresentation ℂ G X
  let ρcomp :
      Representation ℂ (Shrink.{0} G)
        (permutationAugmentationSubrepresentation ℂ G X).toSubmodule :=
    ρ.comp (Shrink.mulEquiv : Shrink.{0} G ≃* G).toMonoidHom
  let ρf :
      Representation ℂ (Shrink.{0} G)
        (FGModuleRepr.ofFinite ℂ
          (permutationAugmentationSubrepresentation ℂ G X).toSubmodule) :=
    finiteModelRep ρ
  have hρf_char :
      ρf.character = fun g : Shrink.{0} G ↦
        permutationAugmentationCharacter ℂ G X (Shrink.mulEquiv g) := by
    ext g
    have hiso := congrFun (Representation.char_iso (finiteModelRepEquivComp ρ)) g
    simpa [ρf, ρ, permutationAugmentationCharacter] using hiso
  have hpairing_finiteModel :
      ⟪ρf.character, ρf.character⟫ =
        ⟪permutationAugmentationCharacter ℂ G X, permutationAugmentationCharacter ℂ G X⟫ := by
    rw [hρf_char]
    exact
      groupFunctionPairing_precomp_mulEquiv_local
        (G := Shrink.{0} G) (e := (Shrink.mulEquiv : Shrink.{0} G ≃* G))
        (f := permutationAugmentationCharacter ℂ G X) (g := permutationAugmentationCharacter ℂ G X)
  have hρf_iff : ⟪ρf.character, ρf.character⟫ = 1 ↔ ρf.IsIrreducible := by
    exact self_character_pairing_eq_one_iff_isIrreducible ρf
  constructor
  · intro hself
    have hself_f : ⟪ρf.character, ρf.character⟫ = 1 := by
      rw [hpairing_finiteModel]
      exact hself
    have hirr_f : ρf.IsIrreducible := hρf_iff.mp hself_f
    letI : ρf.IsIrreducible := hirr_f
    have hirr_comp : ρcomp.IsIrreducible := by
      -- Transport irreducibility back from the finite model to the shrunk original action.
      exact isIrreducible_of_nonempty_equiv ⟨finiteModelRepEquivComp ρ⟩
    letI : ρcomp.IsIrreducible := hirr_comp
    let ρorig :
        Representation ℂ G (permutationAugmentationSubrepresentation ℂ G X).toSubmodule :=
      ρcomp.comp ((Shrink.mulEquiv : Shrink.{0} G ≃* G).symm.toMonoidHom)
    have hirr_orig : ρorig.IsIrreducible := by
      -- Undo the group shrink through the corresponding multiplicative equivalence.
      exact
        isIrreducible_comp_of_mulEquiv
          (e := (Shrink.mulEquiv : Shrink.{0} G ≃* G).symm) ρcomp
    have hρorig : ρorig = ρ := by
      ext g x a
      have hshrink :
          Shrink.mulEquiv ((Shrink.mulEquiv : Shrink.{0} G ≃* G).symm g) = g := by
        simp
      dsimp [ρorig, ρcomp]
      have hx :
          (ρ (Shrink.mulEquiv ((Shrink.mulEquiv : Shrink.{0} G ≃* G).symm g))) x = (ρ g) x := by
        exact congrArg (fun h : G ↦ (ρ h) x) hshrink
      exact congrArg
        (fun y : (permutationAugmentationSubrepresentation ℂ G X).toSubmodule => ((y : X →₀ ℂ) a))
        hx
    rwa [hρorig] at hirr_orig
  · intro hirr
    letI : ρ.IsIrreducible := hirr
    have hirr_f : ρf.IsIrreducible := finiteModelRep_isIrreducible (σ := ρ)
    have hself_f : ⟪ρf.character, ρf.character⟫ = 1 := hρf_iff.mpr hirr_f
    rwa [hpairing_finiteModel] at hself_f

/-- Helper for Exercise 7-7.2-4: for a transitive nontrivial action, the scalar-product
condition `⟪χ², 1⟫ = 2` is equivalent to irreducibility of the augmentation representation. -/
theorem character_square_pairing_eq_two_iff_augmentation_isIrreducible :
    (⟪(ofMulAction ℂ G X).character ^ 2, (1 : G → ℂ)⟫ = 2) ↔
      (permutationAugmentationRepresentation ℂ G X).IsIrreducible := by
  -- Route correction: package the source-proof identity `χ = 1 + ψ` and the Schur-criterion
  -- bridge separately, so the endgame is only arithmetic plus a named irreducibility test.
  constructor
  · intro hpair
    -- Subtract the trivial contribution from `⟪χ², 1⟫ = 2` to isolate `⟪ψ, ψ⟫ = 1`.
    have hself :
        ⟪permutationAugmentationCharacter ℂ G X, permutationAugmentationCharacter ℂ G X⟫ = 1 := by
      rw [permutation_square_pairing_eq_one_add_augmentation_self_pairing (G := G) (X := X)] at hpair
      have hsub := congrArg (fun z : ℂ ↦ z - 1) hpair
      norm_num at hsub
      exact hsub
    exact (augmentation_character_self_pairing_eq_one_iff_isIrreducible (G := G) (X := X)).mp hself
  · intro hirr
    -- Reinsert Schur's criterion into the packaged `χ = 1 + ψ` pairing formula.
    have hself :
        ⟪permutationAugmentationCharacter ℂ G X, permutationAugmentationCharacter ℂ G X⟫ = 1 :=
      (augmentation_character_self_pairing_eq_one_iff_isIrreducible (G := G) (X := X)).mpr hirr
    calc
      ⟪(ofMulAction ℂ G X).character ^ 2, (1 : G → ℂ)⟫
          = 1 +
              ⟪permutationAugmentationCharacter ℂ G X,
                permutationAugmentationCharacter ℂ G X⟫ := by
                  exact
                    permutation_square_pairing_eq_one_add_augmentation_self_pairing
                      (G := G) (X := X)
      _ = 2 := by
            rw [hself]
            norm_num

end TransitiveCase

end NontrivialCase

end DoubleTransitiveCase

end Representation

namespace Subgroup

section

open Representation
open scoped BigOperators Representation SubgroupInduction

variable {G : Type u} [Group G]

/-- Helper for Exercise 7-7.2-4: a left coset `rH` is fixed by left multiplication by `g`
exactly when the conjugate `r⁻¹ * g * r` lies in `H`. -/
lemma quotient_left_coset_fixed_iff_conj_mem
    (H : Subgroup G) (g r : G) :
    ((g : G) • (r : G ⧸ H) = (r : G ⧸ H)) ↔ r⁻¹ * g * r ∈ H := by
  constructor
  · intro h
    -- Rewrite fixedness in the quotient as an equality of left cosets and move the inverse
    -- back into `H`.
    have h' : ((g * r : G) : G ⧸ H) = (r : G ⧸ H) := by
      simpa using h
    rw [QuotientGroup.eq] at h'
    have h'': (r⁻¹ * g * r)⁻¹ ∈ H := by
      simpa [mul_assoc, mul_inv_rev] using h'
    simpa using H.inv_mem h''
  · intro h
    -- The subgroup condition gives the quotient equality after inverting once inside `H`.
    have h' : ((g * r : G) : G ⧸ H) = (r : G ⧸ H) := by
      apply QuotientGroup.eq.mpr
      simpa [mul_assoc] using H.inv_mem h
    simpa using h'

/-- Helper for Exercise 7-7.2-4: counting the fixed left cosets of `g` is the same as counting
the representatives `r ∈ R` with `r⁻¹ * g * r ∈ H`. -/
lemma fixed_left_cosets_ncard_eq_sum_over_left_transversal
    (H : Subgroup G) [DecidablePred fun x : G => x ∈ H]
    (R : Finset G) (hR : IsComplement (R : Set G) (H : Set G)) (g : G) :
    ↑(MulAction.fixedBy (G ⧸ H) g).ncard =
      ∑ r ∈ R, if r⁻¹ * g * r ∈ H then (1 : ℂ) else 0 := by
  classical
  let e :
      MulAction.fixedBy (G ⧸ H) g ≃
        {r : ↥(R : Set G) // (r : G)⁻¹ * g * r ∈ H} :=
    { toFun := fun q : MulAction.fixedBy (G ⧸ H) g ↦ by
        refine ⟨hR.leftQuotientEquiv q.1, ?_⟩
        -- Represent the fixed quotient point by its chosen transversal element and rewrite the
        -- fixed-point condition as a conjugacy condition in `H`.
        have hrepr :
            (((hR.leftQuotientEquiv q.1 : ↥(R : Set G)) : G) : G ⧸ H) = q.1 := by
          simpa using
            (Subgroup.IsComplement.quotientGroupMk_leftQuotientEquiv
              (hS := hR) (q := q.1))
        have hqfix : g • q.1 = q.1 := by
          exact q.2
        have hfix :
            (g : G) • ((((hR.leftQuotientEquiv q.1 : ↥(R : Set G)) : G) : G ⧸ H)) =
              ((((hR.leftQuotientEquiv q.1 : ↥(R : Set G)) : G) : G ⧸ H)) := by
          simpa [hrepr] using hqfix
        exact (quotient_left_coset_fixed_iff_conj_mem H g (hR.leftQuotientEquiv q.1 : G)).1 hfix
      invFun := fun r ↦ by
        refine ⟨((r : G) : G ⧸ H), ?_⟩
        -- Conversely, the conjugacy condition says the coset of `r` is fixed by `g`.
        exact (quotient_left_coset_fixed_iff_conj_mem H g (r : G)).2 r.2
      left_inv := by
        intro q
        apply Subtype.ext
        simpa using
          (Subgroup.IsComplement.quotientGroupMk_leftQuotientEquiv
            (hS := hR) (q := q.1))
      right_inv := by
        intro r
        apply Subtype.ext
        change hR.leftQuotientEquiv (((r : G) : G ⧸ H)) = r.1
        apply hR.leftQuotientEquiv.apply_eq_iff_eq_symm_apply.mpr
        calc
          hR.leftQuotientEquiv.symm r.1
            = (((hR.leftQuotientEquiv (hR.leftQuotientEquiv.symm r.1) : ↥(R : Set G)) : G) :
                G ⧸ H) := by
                    symm
                    simpa using
                      (Subgroup.IsComplement.quotientGroupMk_leftQuotientEquiv
                        (hS := hR) (q := hR.leftQuotientEquiv.symm r.1))
          _ = ((r : G) : G ⧸ H) := by
                simp }
  have hcard :
      (MulAction.fixedBy (G ⧸ H) g).ncard =
        Nat.card {r : ↥(R : Set G) // (r : G)⁻¹ * g * r ∈ H} := by
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_congr e
  -- Convert the cardinality of the filtered subtype into the transversal sum of indicator values.
  calc
    ↑(MulAction.fixedBy (G ⧸ H) g).ncard
      = (Nat.card {r : ↥(R : Set G) // (r : G)⁻¹ * g * r ∈ H} : ℂ) := by
          exact congrArg (fun n : ℕ ↦ (n : ℂ)) hcard
    _ = ((R.filter fun r ↦ r⁻¹ * g * r ∈ H).card : ℂ) := by
          have hfilter_card :
              Fintype.card {r : ↥(R : Set G) // (r : G)⁻¹ * g * r ∈ H} =
                (R.filter fun r ↦ r⁻¹ * g * r ∈ H).card := by
            calc
              Fintype.card {r : ↥(R : Set G) // (r : G)⁻¹ * g * r ∈ H}
                = (R.attach.filter fun r : ↥(R : Set G) ↦ (r : G)⁻¹ * g * r ∈ H).card := by
                    exact Fintype.card_ofFinset
                      (R.attach.filter fun r : ↥(R : Set G) ↦ (r : G)⁻¹ * g * r ∈ H)
                      (fun r => by
                        change
                          r ∈ R.attach.filter (fun s : ↥(R : Set G) ↦ (s : G)⁻¹ * g * s ∈ H) ↔
                            (r : G)⁻¹ * g * r ∈ H
                        simp)
              _ = (R.filter fun r ↦ r⁻¹ * g * r ∈ H).card := by
                    simpa using congrArg Finset.card
                      (Finset.filter_attach (fun r : G ↦ r⁻¹ * g * r ∈ H) R)
          rw [Nat.card_eq_fintype_card]
          exact_mod_cast hfilter_card
    _ = ∑ r ∈ R, if r⁻¹ * g * r ∈ H then (1 : ℂ) else 0 := by
          simp

/-- Helper for Exercise 7-7.2-4: the permutation character on `G ⧸ H` is computed by the standard
left-transversal sum. -/
lemma quotient_permutation_character_eq_sum_over_left_transversal
    (H : Subgroup G) [DecidablePred fun x : G => x ∈ H] [Finite G] (R : Finset G)
    (hR : IsComplement (R : Set G) (H : Set G)) (g : G) :
    (ofMulAction ℂ G (G ⧸ H)).character g =
      ∑ r ∈ R, if r⁻¹ * g * r ∈ H then (1 : ℂ) else 0 := by
  -- Rewrite the permutation character as the number of fixed left cosets.
  rw [ofMulAction_character_eq_ncard_fixedBy]
  exact fixed_left_cosets_ncard_eq_sum_over_left_transversal H R hR g

/-- Helper for Exercise 7-7.2-4: the induced trivial class function is computed by the same
left-transversal sum as the quotient permutation character. -/
lemma trivial_induced_eq_sum_over_left_transversal
    (H : Subgroup G) [DecidablePred fun x : G => x ∈ H] [Finite G] (R : Finset G)
    (hR : IsComplement (R : Set G) (H : Set G)) (g : G) :
    Ind[H](1) g =
      ∑ r ∈ R, if r⁻¹ * g * r ∈ H then (1 : ℂ) else 0 := by
  let _ : NeZero (Nat.card H : ℂ) := by
    refine ⟨?_⟩
    exact_mod_cast (Nat.card_pos : 0 < Nat.card H).ne'
  have htriv : _root_.IsClassFunction (1 : H → ℂ) := by
    -- The unit function is constant on conjugacy classes.
    refine ⟨?_⟩
    intro x y hxy
    simp
  -- Specialize Proposition `7-7.2-1` to the trivial character.
  simpa using induced_class_function_eq_sum_over_left_transversal
    (H := H) (ψ := (1 : H → ℂ)) htriv R hR g

-- Source/core/bridge triage for Exercise 7-7.2-4:
-- * source-facing: the permutation character on `G ⧸ H` and its augmentation summand.
-- * core/canonical owners: subgroup induction `ind H.subtype` from Proposition `7-7.2-1` and
--   the augmentation owner `permutationAugmentationRepresentation` from Exercise `2-2.3-7`.
-- * bridge/view: Proposition `7-7.2-1` identifies `Ind[H](θ.character)` with the character of
--   `ind H.subtype θ`.
-- Proof sketch: compute the permutation character on the coset action and identify it directly
-- with the subgroup-induced unit class function `Ind_H^G(1)`.
/-- Exercise 7-7.2-4 (1): the character of the permutation representation on `G ⧸ H` is the
subgroup-induced unit class function `Ind_H^G(1)`. -/
theorem quotientPermutationCharacter_eq_inducedClassFunction_trivial
    (H : Subgroup G) [Finite G] :
    (ofMulAction ℂ G (G ⧸ H)).character =
      Ind[H](1) := by
  classical
  obtain ⟨S, hS, _⟩ := H.exists_isComplement_left (1 : G)
  let R : Finset G := (Set.toFinite S).toFinset
  have hR : IsComplement (R : Set G) (H : Set G) := by
    simpa [R] using hS
  ext g
  -- Both characters reduce to the same source-facing sum over left-coset representatives.
  rw [quotient_permutation_character_eq_sum_over_left_transversal H R hR g,
    trivial_induced_eq_sum_over_left_transversal H R hR g]

-- Proof sketch: split the quotient permutation module into the one-dimensional constant
-- subrepresentation and the kernel of the augmentation map, so the corresponding character is
-- `χ - 1`.
/-- Exercise 7-7.2-4 (2): the augmentation representation has character `χ - 1`, where `χ` is the
character of the permutation representation on `G ⧸ H`. -/
theorem quotientPermutationAugmentationCharacter_eq
    (H : Subgroup G) [H.FiniteIndex] :
    permutationAugmentationCharacter ℂ G (G ⧸ H) =
      (ofMulAction ℂ G (G ⧸ H)).character - 1 := by
  let _ : Invertible (Nat.card (G ⧸ H) : ℂ) := by
    refine invertibleOfNonzero ?_
    have hcard : 0 < Nat.card (G ⧸ H) := Nat.card_pos
    exact_mod_cast hcard.ne'
  have htriv : (trivial ℂ G ℂ).character = (1 : G → ℂ) := by
    ext g
    simp [Representation.character, Representation.trivial]
  have hχ :
      (ofMulAction ℂ G (G ⧸ H)).character =
        (trivial ℂ G ℂ).character + permutationAugmentationCharacter ℂ G (G ⧸ H) := by
    simpa using
      (permutation_character_eq_trivial_add_augmentation
        (k := ℂ) (G := G) (X := G ⧸ H))
  exact eq_sub_iff_add_eq.mpr <| by
    simpa [htriv, add_comm] using hχ.symm

-- Proof sketch: compute the self-inner product of `χ - 1`; it equals `1` exactly when the action
-- of `G` on `G ⧸ H` is `2`-transitive, which is equivalent to irreducibility of the augmentation
-- summand.
/-- Exercise 7-7.2-4 (3): the augmentation representation is irreducible exactly when the action
of `G` on `G ⧸ H` is doubly transitive. -/
theorem quotientPermutationAugmentation_isIrreducible_iff
    (H : Subgroup G) [Finite G] [Nontrivial (G ⧸ H)] :
    (permutationAugmentationRepresentation ℂ G (G ⧸ H)).IsIrreducible ↔
      MulAction.IsMultiplyPretransitive G (G ⧸ H) 2 := by
  letI : Fintype G := Fintype.ofFinite G
  simpa using
    ((isTwoPretransitive_iff_pairActionHasDiagonalOrbits (G := G) (X := G ⧸ H)).trans
      pairActionHasDiagonalOrbits_iff_character_square_pairing_eq_two |>.trans
      character_square_pairing_eq_two_iff_augmentation_isIrreducible).symm

end

end Subgroup
