import Mathlib
import LinearRepresentations_Serre_1977.Chap02.Exercise_2_2_1_5
import LinearRepresentations_Serre_1977.Chap02.Proposition_2_2_1_2
import LinearRepresentations_Serre_1977.Chap02.Theorem_2_2_3_5
import LinearRepresentations_Serre_1977.Chap08.Corollary_8_8_1_3
import LinearRepresentations_Serre_1977.FiniteToFintype

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Representation

noncomputable section

universe u v w

namespace Representation

section Augmentation

variable (k : Type w) [CommSemiring k]
variable {X : Type v}

/-- The augmentation map on the permutation module `X →₀ k`, sending a finitely supported
function to the sum of its coefficients. -/
def permutationAugmentationLinearMap (X : Type v) : (X →₀ k) →ₗ[k] k :=
  Finsupp.lsum k fun _ ↦ LinearMap.id

section

variable (G : Type u) [Monoid G]
variable (X : Type v) [MulAction G X]

/- `source-facing`: the coefficient-sum map `permutationAugmentationLinearMap`.
`core/canonical`: the same map bundled as an intertwining map from the permutation representation
to the trivial representation, from which the kernel subrepresentation and its induced
representation/character are derived. -/
/-- The augmentation map as a morphism of representations. -/
def permutationAugmentation :
    IntertwiningMap (ofMulAction k G X) (trivial k G k) where
  toLinearMap := permutationAugmentationLinearMap k X
  isIntertwining' g := by
    apply LinearMap.ext
    intro f
    -- The augmentation depends only on the coefficients, so permuting basis vectors preserves it.
    induction f using Finsupp.induction_linear with
    | zero =>
        simp [permutationAugmentationLinearMap]
    | add f g hf hg =>
        simp [map_add, hf, hg]
    | single x r =>
        simp [permutationAugmentationLinearMap, Representation.ofMulAction_single]

/- The source's augmentation representation is the kernel of the coefficient-sum morphism. -/
abbrev permutationAugmentationSubrepresentation :
    Subrepresentation (ofMulAction k G X) :=
  (permutationAugmentation k G X).ker

/- `source-facing`: Serre's augmentation representation.
`bridge/view`: the induced representation on the canonical augmentation kernel. -/
/-- The augmentation representation attached to the permutation action of `G` on `X`. -/
abbrev permutationAugmentationRepresentation [CommRing k] :
    Representation k G (permutationAugmentationSubrepresentation k G X).toSubmodule :=
  (permutationAugmentationSubrepresentation k G X).toRepresentation

end

end Augmentation

section Statements

variable {G : Type u} [Monoid G]
variable {X : Type v} [MulAction G X] [Finite X]

local instance (k : Type w) [Semiring k] [Invertible (Nat.card X : k)] :
    Invertible (Fintype.card X : k) := by
  rw [Fintype.card_eq_nat_card]
  infer_instance

section AugmentationCharacter

variable (k : Type w) [Field k]

/- `source-facing`: Serre's augmentation character `ψ`.
`bridge/view`: the character of `permutationAugmentationRepresentation`. -/
/-- The character of the augmentation representation attached to the permutation action of `G`
on `X`. -/
abbrev permutationAugmentationCharacter
    (G : Type u) [Monoid G] (X : Type v) [MulAction G X] [Finite X] : G → k :=
  fun g ↦
    LinearMap.trace k (permutationAugmentationSubrepresentation k G X).toSubmodule
      ((permutationAugmentationRepresentation k G X) g)

end AugmentationCharacter

section OrbitCount

variable (k : Type w) [Field k]

/-- Helper for Exercise 2-2.3-7: a finitely supported function in the permutation module is
invariant exactly when it is constant on `G`-orbits. -/
theorem ofMulAction_mem_invariants_iff_orbit_constant
    (G : Type u) [Group G] (X : Type v) [MulAction G X] [Finite X] (f : X →₀ k) :
    f ∈ (ofMulAction k G X).invariants ↔
      ∀ x y : X, MulAction.orbitRel G X x y → f x = f y := by
  rw [Representation.mem_invariants]
  constructor
  · intro hf x y hxy
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hxy
    rcases hxy with ⟨g, hg⟩
    -- Evaluate the invariance equation at `y` after acting by `g⁻¹`.
    have hpoint := congrArg (fun z : X →₀ k => z y) (hf g⁻¹)
    simpa [hg, Representation.ofMulAction_apply] using hpoint
  · intro hconst g
    ext x
    -- Put the pointwise action into orbit language and then apply orbit constancy.
    simpa [Representation.ofMulAction_apply] using hconst (g⁻¹ • x) x <| by
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
      exact ⟨g⁻¹, rfl⟩

/-- Helper for Exercise 2-2.3-7: evaluation on orbit classes descends an invariant permutation
vector to a function on the orbit quotient. -/
noncomputable def invariants_to_orbit_quotient_functions
    (G : Type u) [Group G] (X : Type v) [MulAction G X] [Finite X] :
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

/-- Helper for Exercise 2-2.3-7: a function on the orbit quotient pulls back to an invariant
vector in the permutation module. -/
noncomputable def orbit_quotient_functions_to_invariants
    (G : Type u) [Group G] (X : Type v) [MulAction G X] [Finite X] :
    (MulAction.orbitRel.Quotient G X → k) →ₗ[k] (ofMulAction k G X).invariants where
  toFun φ := by
    refine ⟨Finsupp.equivFunOnFinite.symm (fun x : X ↦ φ ⟦x⟧), ?_⟩
    rw [Representation.mem_invariants]
    intro g
    ext x
    -- The pullback only depends on the orbit class, so the permutation action fixes it.
    suffices hclass : φ ⟦g⁻¹ • x⟧ = φ ⟦x⟧ by
      simpa only [ofMulAction_apply, Finsupp.equivFunOnFinite_symm_apply_apply] using hclass
    congr 1
    apply Quotient.sound
    exact ⟨g⁻¹, rfl⟩
  map_add' φ ψ := by
    apply Subtype.ext
    ext x
    simp
  map_smul' a φ := by
    apply Subtype.ext
    ext x
    simp

/-- Helper for Exercise 2-2.3-7: invariant vectors in the permutation module are exactly
functions on the orbit quotient. -/
noncomputable def invariants_equiv_orbit_quotient_functions
    (G : Type u) [Group G] (X : Type v) [MulAction G X] [Finite X] :
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
    -- Evaluating the descended orbit function back at the class of `x` recovers the original
    -- invariant vector.
    simp [invariants_to_orbit_quotient_functions, orbit_quotient_functions_to_invariants]
  right_inv φ := by
    ext q
    -- Every quotient function is recovered by evaluating the pulled-back vector on a
    -- representative.
    refine Quotient.inductionOn q fun x ↦ ?_
    simp [invariants_to_orbit_quotient_functions, orbit_quotient_functions_to_invariants]

-- Proof sketch: invariant vectors in the permutation module are exactly the finitely supported
-- functions that are constant on each orbit, so choosing one scalar per orbit identifies the
-- invariant subspace with `k^c`.
/-- Exercise 2-2.3-7 (1): in part (a), the number of orbits of `X` equals the dimension of the
invariant subspace of the permutation representation, over any field. -/
theorem orbit_count_eq_finrank_invariants
    (G : Type u) [Group G] (X : Type v) [MulAction G X] [Finite X] :
    Nat.card (MulAction.orbitRel.Quotient G X) =
      Module.finrank k (ofMulAction k G X).invariants := by
  letI : Fintype (MulAction.orbitRel.Quotient G X) := Fintype.ofFinite _
  -- Transport the invariant subspace to the full function space on the orbit quotient.
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

variable [Group G] [MulAction G X] [Finite G]

-- Proof sketch: apply `Representation.card_inv_mul_sum_char_eq_finrank` to the permutation
-- representation `ofMulAction ℂ G X`, then combine it with the orbit-count computation from
-- `orbit_count_eq_finrank_invariants`.
/-- Exercise 2-2.3-7 (2): in part (a), the scalar product `⟪χ, 1⟫` of the permutation character
with the unit character is the number of orbits of `X`. -/
theorem permutation_character_pairing_with_trivial_eq_orbit_count
    (G : Type u) [Group G] (X : Type v) [MulAction G X] [Finite X] [Finite G] :
    ⟪(ofMulAction ℂ G X).character, (1 : G → ℂ)⟫ =
      Nat.card (MulAction.orbitRel.Quotient G X) := by
  letI : Fintype G := Fintype.ofFinite G
  letI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by
    exact_mod_cast Nat.card_pos.ne')
  -- Rewrite the pairing with the trivial character as the normalized character average.
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

section Splitting

variable (k : Type w) [CommRing k]
variable [Nonempty X] [Invertible (Nat.card X : k)]

-- The constant line is the canonical trivial summand inside the finite permutation module.
private def permutationConstantLinearMap :
    k →ₗ[k] (X →₀ k) where
  toFun z := Finsupp.equivFunOnFinite.symm fun _ : X ↦ ⅟(Fintype.card X : k) * z
  map_add' := by
    -- The constant vector with value `⅟|X| * (z + z')` is the sum of the two constant vectors.
    intro z z'
    ext x
    simp [mul_add]
  map_smul' := by
    -- Scalar multiplication acts pointwise on the constant vector.
    intro a z
    ext x
    simp [mul_assoc, mul_comm]

omit [Nonempty X] in
private theorem permutationAugmentationLinearMap_comp_permutationConstantLinearMap
    : permutationAugmentationLinearMap k X ∘ₗ permutationConstantLinearMap k = LinearMap.id := by
  -- Summing the constant function `⅟|X| * z` over `X` gives back `z`.
  apply LinearMap.ext
  intro z
  simp [permutationAugmentationLinearMap, permutationConstantLinearMap, Finsupp.sum_fintype,
    nsmul_eq_mul, mul_left_comm, mul_comm]

omit [Nonempty X] in
/-- Helper for Exercise 2-2.3-7: subtracting the constant part of a permutation vector leaves a
vector in the augmentation kernel. -/
private theorem permutation_residual_mem_augmentationSubrepresentation
    (f : X →₀ k) :
    f - permutationConstantLinearMap k (permutationAugmentationLinearMap k X f) ∈
      (permutationAugmentationSubrepresentation k G X).toSubmodule := by
  -- The residual lies in the kernel because the augmentation of the chosen constant part
  -- exactly recovers the original total coefficient sum.
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

-- The finite permutation module splits as the constant line plus the augmentation kernel.
private def permutationToTrivialProdAugmentationLinearEquiv :
    (X →₀ k) ≃ₗ[k] k × (permutationAugmentationSubrepresentation k G X).toSubmodule where
  toFun f :=
    (permutationAugmentationLinearMap k X f,
      ⟨f - permutationConstantLinearMap k (permutationAugmentationLinearMap k X f),
        permutation_residual_mem_augmentationSubrepresentation (k := k) (G := G) (X := X) f⟩)
  invFun z := permutationConstantLinearMap k z.1 + z.2.1
  left_inv := by
    intro f
    -- Recover the original vector by adding back the constant part to the residual.
    ext x
    simp [sub_eq_add_neg, add_left_comm]
  right_inv := by
    intro z
    rcases z with ⟨z, f⟩
    -- The first coordinate records the augmentation and the second keeps the kernel part.
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
    -- Check linearity coordinatewise: augmentation is linear, and the residual is defined by
    -- subtracting the linear constant part.
    apply Prod.ext
    · change
        permutationAugmentationLinearMap k X (f + g) =
          permutationAugmentationLinearMap k X f + permutationAugmentationLinearMap k X g
      simp
    · apply Subtype.ext
      -- Compare the underlying residual vectors directly in the ambient permutation module.
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
    -- The same coordinatewise expansion proves compatibility with scalar multiplication.
    apply Prod.ext
    · change
        permutationAugmentationLinearMap k X (a • f) =
          a • permutationAugmentationLinearMap k X f
      simp
    · apply Subtype.ext
      -- Again work in the ambient module so linearity of the two auxiliary maps is explicit.
      change
        a • f -
            permutationConstantLinearMap k
              (permutationAugmentationLinearMap k X (a • f)) =
          a •
            (f - permutationConstantLinearMap k (permutationAugmentationLinearMap k X f))
      rw [map_smul, map_smul]
      ext x
      simp [sub_eq_add_neg]

omit [Finite X] [Nonempty X] in
/-- Helper for Exercise 2-2.3-7: the constant line in the permutation module is fixed by the
permutation action of a group. -/
private theorem ofMulAction_constant_vector_eq_self
    {G : Type u} [Group G] [MulAction G X] [Finite X]
    (g : G) (z : k) :
    (ofMulAction k G X) g (permutationConstantLinearMap k z) =
      permutationConstantLinearMap k z := by
  -- A constant finitely supported function stays constant after permuting coordinates.
  ext x
  simp [permutationConstantLinearMap, Representation.ofMulAction_apply]

omit [Finite X] [Nonempty X] in
/-- Helper for Exercise 2-2.3-7: the permutation action transports the residual term to the
residual of the transported vector. -/
private theorem ofMulAction_apply_residual_eq
    {G : Type u} [Group G] [MulAction G X] [Finite X]
    (g : G) (f : X →₀ k) :
    (ofMulAction k G X) g
        (f - permutationConstantLinearMap k (permutationAugmentationLinearMap k X f)) =
      (ofMulAction k G X) g f -
        permutationConstantLinearMap k
          (permutationAugmentationLinearMap k X ((ofMulAction k G X) g f)) := by
  -- First transport the subtraction through the action, then rewrite the constant term using
  -- augmentation equivariance.
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

omit [Finite X] [Nonempty X] in
/-- Helper for Exercise 2-2.3-7: the augmentation subrepresentation action carries the residual
term of `f` to the residual term of the transported vector. -/
private theorem residual_subrepresentation_action_eq
    {G : Type u} [Group G] [MulAction G X] [Finite X]
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
  -- The subrepresentation action is inherited from the ambient permutation action, so the
  -- underlying vectors agree by the residual transport identity proved above.
  apply Subtype.ext
  exact ofMulAction_apply_residual_eq (k := k) (X := X) g f

-- Proof sketch: split a finitely supported function into its average constant part and its
-- augmentation-zero part. This is the owner-level decomposition underlying the transitive case in
-- the source.
/-- If `X` is finite and nonempty and `|X|` is invertible in `k`, then the permutation
representation decomposes as the sum of the trivial representation and the augmentation
representation. This is the owner-level splitting underlying the transitive case. -/
def permutation_equiv_trivial_prod_augmentation
    (G : Type u) [Group G] (X : Type v) [MulAction G X] [Finite X] [Nonempty X]
    [Invertible (Nat.card X : k)] :
    (ofMulAction k G X).Equiv
      ((trivial k G k).prod
        (permutationAugmentationRepresentation k G X)) :=
  Representation.Equiv.mk (permutationToTrivialProdAugmentationLinearEquiv k)
    fun g ↦ by
      -- Route correction: the module-level split works over a monoid, but equivariance of the
      -- constant line needs the inverse formula for the genuine permutation action of a group.
      apply LinearMap.ext
      intro f
      -- The first coordinate is augmentation equivariance; the second is the residual transport
      -- packaged inside the augmentation subrepresentation.
      apply Prod.ext
      · have hcoord :=
          congrArg
            (fun l : (X →₀ k) →ₗ[k] k ↦ l f)
            ((permutationAugmentation k G X).isIntertwining' g)
        simpa [Representation.trivial] using hcoord
      · simpa [permutationToTrivialProdAugmentationLinearEquiv] using
          (residual_subrepresentation_action_eq (k := k) (G := G) (X := X) g f).symm

end Splitting

section SplittingCharacter

variable (k : Type w) [Field k]
variable [Nonempty X] [Invertible (Nat.card X : k)]

/-- Helper for Exercise 2-2.3-7: an equivalence from a representation to a product representation
transports its character to the sum of the two product characters. -/
private theorem character_eq_of_equiv_prod
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {W : Type*} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    {U : Type*} [AddCommGroup U] [Module k U] [FiniteDimensional k U]
    (ρ : Representation k G V) (σ : Representation k G W) (τ : Representation k G U)
    (e : ρ.Equiv (σ.prod τ)) :
    ρ.character = σ.character + τ.character := by
  ext g
  -- First transport the character across the product equivalence.
  calc
    ρ.character g = (σ.prod τ).character g := by
      simpa using congrFun (Representation.char_iso e) g
    _ = σ.character g + τ.character g := by
      exact congrFun (Representation.char_prod σ τ) g

-- Proof sketch: take characters in the decomposition
-- `permutation_equiv_trivial_prod_augmentation` and use additivity of characters for product
-- representations.
set_option maxHeartbeats 800000 in
/-- For any finite nonempty permutation action with `|X|` invertible in `k`, the permutation
character is the sum of the trivial character and the character of the augmentation
representation. This is the owner-level character identity attached to the splitting above. -/
theorem permutation_character_eq_trivial_add_augmentation
    (G : Type u) [Group G] (X : Type v) [MulAction G X] [Finite X] [Nonempty X]
    [Invertible (Nat.card X : k)] :
    (ofMulAction k G X).character =
      (trivial k G k).character +
        permutationAugmentationCharacter k G X := by
  -- Use the module-level splitting directly, then transport characters across the product
  -- equivalence instead of expanding the trace identities by hand.
  letI : FiniteDimensional k (permutationAugmentationSubrepresentation k G X).toSubmodule :=
    inferInstance
  exact
    character_eq_of_equiv_prod (G := G) k
      (V := X →₀ k)
      (W := k)
      (U := (permutationAugmentationSubrepresentation k G X).toSubmodule)
      (ρ := ofMulAction k G X)
      (σ := trivial k G k)
      (τ := (permutationAugmentationRepresentation k G X :
        Representation k G (permutationAugmentationSubrepresentation k G X).toSubmodule))
      (permutation_equiv_trivial_prod_augmentation (k := k) (G := G) (X := X))

end SplittingCharacter

section TransitiveCase

variable [Group G] [MulAction.IsPretransitive G X] [Nonempty X]

section FiniteGroup

variable [Finite G]

/-- Helper for Exercise 2-2.3-7: a pretransitive finite permutation action contributes exactly one
copy of the unit character. -/
private theorem pretransitive_permutation_pairing_with_trivial_eq_one :
    ∀ (G : Type u) [Group G] (X : Type v) [MulAction G X] [Finite X]
      [MulAction.IsPretransitive G X] [Nonempty X] [Finite G],
    ⟪(ofMulAction ℂ G X).character, (1 : G → ℂ)⟫ = 1 := by
  intro G _ X _ _ _ _ _
  classical
  letI : Fintype G := Fintype.ofFinite G
  let x₀ : X := Classical.choice ‹Nonempty X›
  letI : Unique (MulAction.orbitRel.Quotient G X) :=
    { default := ⟦x₀⟧
      uniq := by
        intro q
        refine Quotient.inductionOn q fun y ↦ ?_
        rcases (inferInstance : MulAction.IsPretransitive G X).exists_smul_eq x₀ y with ⟨g, hg⟩
        exact Quotient.sound ⟨g, hg⟩ }
  -- In the pretransitive case the orbit quotient has a single point, so the orbit-count formula
  -- gives pairing `1`.
  calc
    ⟪(ofMulAction ℂ G X).character, (1 : G → ℂ)⟫ =
        Nat.card (MulAction.orbitRel.Quotient G X) := by
          exact permutation_character_pairing_with_trivial_eq_orbit_count (G := G) (X := X)
    _ = 1 := by
          simp

-- Proof sketch: combine the orbit-count formula
-- `permutation_character_pairing_with_trivial_eq_orbit_count` with transitivity, so the
-- permutation character has pairing `1` with the unit character. Then subtract the trivial
-- summand using `permutation_character_eq_trivial_add_augmentation`.
/-- Exercise 2-2.3-7 (3): in the transitive case, the character `ψ` of the augmentation
representation `θ` has zero scalar product with the unit character. -/
theorem augmentation_character_pairing_with_trivial_eq_zero :
    ∀ (G : Type u) [Group G] (X : Type v) [MulAction G X] [Finite X]
      [MulAction.IsPretransitive G X] [Nonempty X] [Finite G],
    ⟪permutationAugmentationCharacter ℂ G X, (1 : G → ℂ)⟫ = 0 := by
  intro G _ X _ _ _ _ _
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

end FiniteGroup

end TransitiveCase

section PairCharacter

variable (k : Type w) [Field k]

-- Proof sketch: use the fixed-point formula for permutation characters on `X × X`, observing that
-- a pair `(x, y)` is fixed exactly when both coordinates are fixed. Equivalently, identify the
-- permutation representation on `X × X` with the tensor square of `ofMulAction k G X`.
/-- Exercise 2-2.3-7 (4): in part (b), the permutation character for the diagonal action on
`X × X` is the square `χ²` of the permutation character on `X`. -/
theorem pair_permutation_character_eq_square :
    (ofMulAction k G (X × X)).character = (ofMulAction k G X).character ^ 2 := by
  ext g
  -- A pair is fixed by the diagonal action exactly when both coordinates are fixed.
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
        cases hp' with
        | intro hx hy =>
            simp [Prod.smul_mk, hx, hy]
      simpa [MulAction.mem_fixedBy] using hpair
  calc
    (ofMulAction k G (X × X)).character g
      = ↑(MulAction.fixedBy (X × X) g).ncard := by
          exact ofMulAction_character_eq_ncard_fixedBy (k := k) (G := G) (X := X × X) g
    _ = ↑(((MulAction.fixedBy X g).prod (MulAction.fixedBy X g)).ncard) := by
          rw [hfixed]
    _ = ↑((MulAction.fixedBy X g).ncard * (MulAction.fixedBy X g).ncard) := by
          change (↑(((MulAction.fixedBy X g) ×ˢ (MulAction.fixedBy X g)).ncard) : k) = _
          exact congrArg (fun n : ℕ ↦ (n : k))
            (Set.ncard_prod (s := MulAction.fixedBy X g) (t := MulAction.fixedBy X g))
    _ = (↑(MulAction.fixedBy X g).ncard : k) ^ 2 := by
          simp [pow_two]
    _ = ((ofMulAction k G X).character g) ^ 2 := by
          simp [ofMulAction_character_eq_ncard_fixedBy]

end PairCharacter

section DoubleTransitiveCase

variable [Group G]
variable [DecidableEq X]

/-- Helper for Exercise 2-2.3-7: being on the diagonal is constant along `G`-orbits in `X × X`.
-/
private theorem pair_orbit_diagonal_classifier_well_defined
    {G : Type u} [Group G] {X : Type v} [MulAction G X] [DecidableEq X]
    (p q : X × X) (hpq : MulAction.orbitRel G (X × X) p q) :
    decide (p.1 = p.2) = decide (q.1 = q.2) := by
  rcases p with ⟨x, y⟩
  rcases q with ⟨x', y'⟩
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hpq
  rcases hpq with ⟨s, hs⟩
  rcases Prod.mk.inj hs with ⟨hx, hy⟩
  -- Equality of the two coordinates is preserved under the diagonal action.
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

/-- Helper for Exercise 2-2.3-7: an orbit of the pair action remembers only whether it is
represented by a diagonal or off-diagonal pair. -/
noncomputable def pair_orbit_diagonal_classifier
    (G : Type u) [Group G] (X : Type v) [MulAction G X] [DecidableEq X] :
    MulAction.orbitRel.Quotient G (X × X) → Bool :=
  Quotient.lift
    (fun p : X × X ↦ decide (p.1 = p.2))
    (fun p q hpq ↦ pair_orbit_diagonal_classifier_well_defined p q hpq)

/-
Clause (i) is the canonical mathlib notion `MulAction.IsMultiplyPretransitive G X 2`; theorem
`MulAction.is_two_pretransitive_iff` supplies the ordered-pair formulation from the source.
-/
/-- Exercise 2-2.3-7 (5): in part (c), clause (i) is equivalent to clause (ii). -/
theorem isTwoPretransitive_iff_pairActionHasDiagonalOrbits
    (G : Type u) [Group G] (X : Type v) [MulAction G X] :
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

-- Proof sketch: by part (a), the scalar product of a permutation character with the unit
-- character counts the number of orbits; by part (b), the character of the action on `X × X` is
-- `χ²`. Thus having exactly the diagonal and its complement as orbits is equivalent to the value
-- `2` for `(χ² | 1)`.
section FiniteGroup

variable [Finite G]

/-- Helper for Exercise 2-2.3-7: the diagonal-status classifier on pair orbits hits both boolean
values. -/
private theorem pair_orbit_diagonal_classifier_surjective :
    ∀ (G : Type u) [Group G] (X : Type v) [MulAction G X] [DecidableEq X] [Nontrivial X],
    Function.Surjective (pair_orbit_diagonal_classifier (G := G) (X := X)) := by
  intro G _ X _ _ _
  classical
  intro b
  cases b with
  | false =>
      rcases exists_pair_ne X with ⟨x, y, hxy⟩
      refine ⟨⟦(x, y)⟧, ?_⟩
      -- An off-diagonal pair is classified by `false`.
      simp [pair_orbit_diagonal_classifier, hxy]
  | true =>
      rcases exists_pair_ne X with ⟨x, y, hxy⟩
      refine ⟨⟦(x, x)⟧, ?_⟩
      -- A diagonal pair is classified by `true`.
      simp [pair_orbit_diagonal_classifier]

/-- Helper for Exercise 2-2.3-7: the pair-action orbit quotient has cardinal `2` exactly when the
diagonal-status classifier is bijective. -/
theorem pair_orbit_quotient_card_two_iff_diagonal_classifier_bijective :
    ∀ (G : Type u) [Group G] (X : Type v) [MulAction G X] [Finite X] [DecidableEq X]
      [Nontrivial X] [Finite G],
    Nat.card (MulAction.orbitRel.Quotient G (X × X)) = 2 ↔
      Function.Bijective (pair_orbit_diagonal_classifier (G := G) (X := X)) := by
  intro G _ X _ _ _ _ _
  classical
  letI : Fintype (MulAction.orbitRel.Quotient G (X × X)) := Fintype.ofFinite _
  -- Route correction: package the finite-cardinality argument separately from the orbit-geometry.
  constructor
  · intro hcard
    -- Surjectivity comes from the diagonal and off-diagonal classes, and the cardinality forces
    -- injectivity.
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
    -- A bijection with `Bool` identifies the quotient with a two-point set.
    calc
      Nat.card (MulAction.orbitRel.Quotient G (X × X))
        = Nat.card Bool := Nat.card_eq_of_bijective _ hbij
      _ = Fintype.card Bool := by
            rw [Nat.card_eq_fintype_card]
      _ = 2 := by
            simp

/-- Exercise 2-2.3-7 (6): in part (c), clause (ii) is equivalent to clause (iii), namely
`⟪χ², 1⟫ = 2`. -/
theorem pairActionHasDiagonalOrbits_iff_character_square_pairing_eq_two :
    ∀ (G : Type u) [Group G] (X : Type v) [MulAction G X] [Finite X] [Nontrivial X] [Finite G],
    (∀ x y x' y' : X, (∃ s : G, s • (x, y) = (x', y')) ↔ (x = y ↔ x' = y')) ↔
      ⟪(ofMulAction ℂ G X).character ^ 2, (1 : G → ℂ)⟫ = 2 := by
  intro G _ X _ _ _ _
  classical
  -- Route correction: clause (ii) is handled by injectivity of the diagonal-status classifier,
  -- then the orbit-count formula for the pair action turns that into the character pairing.
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
      (pair_orbit_quotient_card_two_iff_diagonal_classifier_bijective
        (G := G) (X := X)).2 hbij
    -- Rewrite the number of pair orbits as the pairing of the square character with `1`.
    calc
      ⟪(ofMulAction ℂ G X).character ^ 2, (1 : G → ℂ)⟫
        = ⟪(ofMulAction ℂ G (X × X)).character, (1 : G → ℂ)⟫ := by
            rw [pair_permutation_character_eq_square (k := ℂ) (G := G) (X := X)]
      _ = Nat.card (MulAction.orbitRel.Quotient G (X × X)) := by
            exact permutation_character_pairing_with_trivial_eq_orbit_count (G := G) (X := X × X)
      _ = 2 := by
            exact_mod_cast hcard
  · intro hchi
    have hcard :
        Nat.card (MulAction.orbitRel.Quotient G (X × X)) = 2 := by
      -- Convert the square pairing back to the orbit count for the pair action.
      have hcardC :
          (Nat.card (MulAction.orbitRel.Quotient G (X × X)) : ℂ) = 2 := by
        calc
          (Nat.card (MulAction.orbitRel.Quotient G (X × X)) : ℂ)
            = ⟪(ofMulAction ℂ G (X × X)).character, (1 : G → ℂ)⟫ := by
                exact_mod_cast
                  (permutation_character_pairing_with_trivial_eq_orbit_count
                    (G := G) (X := X × X)).symm
          _ = ⟪(ofMulAction ℂ G X).character ^ 2, (1 : G → ℂ)⟫ := by
                rw [pair_permutation_character_eq_square (k := ℂ) (G := G) (X := X)]
          _ = 2 := hchi
      exact_mod_cast hcardC
    have hbij :
        Function.Bijective (pair_orbit_diagonal_classifier (G := G) (X := X)) :=
      (pair_orbit_quotient_card_two_iff_diagonal_classifier_bijective
        (G := G) (X := X)).1 hcard
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

end NontrivialCase

end DoubleTransitiveCase

end Statements

section TransitiveCase

variable {G : Type u} [Group G] {X : Type v} [MulAction G X] [Finite X]
variable [Nontrivial X] [Finite G]
variable [MulAction.IsPretransitive G X] [Nonempty X]

/-- Helper for Exercise 2-2.3-7: `ULift` transports a representation to a larger carrier universe
without changing the underlying linear action. -/
private def uliftRepresentation_local
    {G : Type u} [Monoid G] {V : Type v} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) : Representation ℂ G (ULift.{u} V) where
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

/-- Helper for Exercise 2-2.3-7: `ULift` does not change characters. -/
private theorem character_uliftRepresentation_local_eq
    {G : Type u} [Monoid G] {V : Type v} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (g : G) :
    (uliftRepresentation_local (G := G) ρ).character g = ρ.character g := by
  change
    LinearMap.trace ℂ (ULift.{u} V)
        ((ULift.moduleEquiv.symm : V ≃ₗ[ℂ] ULift.{u} V).conj (ρ g)) =
      LinearMap.trace ℂ V (ρ g)
  exact LinearMap.trace_conj' (ρ g) (ULift.moduleEquiv.symm : V ≃ₗ[ℂ] ULift.{u} V)

/-- Helper for Exercise 2-2.3-7: lifting the carrier by `ULift` preserves the lattice of
subrepresentations. -/
private def uliftSubrepresentationOrderIso_local
    {G : Type u} [Monoid G] {V : Type v} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) :
    Subrepresentation (uliftRepresentation_local (G := G) ρ) ≃o Subrepresentation ρ where
  toFun W :=
    { toSubmodule := W.toSubmodule.map ULift.moduleEquiv.toLinearMap
      apply_mem_toSubmodule := by
        intro g y hy
        rcases hy with ⟨x, hx, rfl⟩
        exact ⟨uliftRepresentation_local (G := G) ρ g x, W.apply_mem_toSubmodule g hx, rfl⟩ }
  invFun W :=
    { toSubmodule := W.toSubmodule.comap ULift.moduleEquiv.toLinearMap
      apply_mem_toSubmodule := by
        intro g x hx
        exact W.apply_mem_toSubmodule g hx }
  left_inv W := by
    apply Subrepresentation.toSubmodule_injective
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      cases x
      cases y
      cases hxy
      simpa using hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  right_inv W := by
    apply Subrepresentation.toSubmodule_injective
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      exact ⟨⟨y⟩, hy, rfl⟩
  map_rel_iff' := by
    intro W W'
    constructor
    · intro h x hx
      rcases h ⟨x, hx, rfl⟩ with ⟨y, hy, hyx⟩
      cases x
      cases y
      cases hyx
      simpa using hy
    · intro h y hy
      rcases hy with ⟨x, hx, rfl⟩
      exact ⟨x, h hx, rfl⟩

/-- Helper for Exercise 2-2.3-7: lifting the carrier by `ULift` preserves irreducibility. -/
private theorem isIrreducible_uliftRepresentation_local_iff
    {G : Type u} [Monoid G] {V : Type v} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) :
    (uliftRepresentation_local (G := G) ρ).IsIrreducible ↔ ρ.IsIrreducible := by
  constructor
  · intro h
    letI : IsSimpleOrder (Subrepresentation (uliftRepresentation_local (G := G) ρ)) := h
    exact (uliftSubrepresentationOrderIso_local (G := G) ρ).symm.isSimpleOrder
  · intro h
    letI : IsSimpleOrder (Subrepresentation ρ) := h
    exact (uliftSubrepresentationOrderIso_local (G := G) ρ).isSimpleOrder

/-- Helper for Exercise 2-2.3-7: precomposing an irreducible representation with a group
equivalence preserves irreducibility. -/
private theorem isIrreducible_comp_of_mulEquiv_local_aux
    {G : Type u} [Group G] {H : Type v} [Group H] {V : Type w}
    [AddCommGroup V] [Module ℂ V]
    (e : G ≃* H) (σ : Representation ℂ H V) [σ.IsIrreducible] :
    Representation.IsIrreducible (σ.comp e.toMonoidHom) := by
  classical
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

/-- Helper for Exercise 2-2.3-7: simultaneously lifting the group and carrier puts a complex
representation into a common universe. -/
private def uliftGroupCarrierRepresentation
    {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) :
    Representation ℂ (ULift.{v} G) (ULift.{max u v} V) :=
  uliftRepresentation_local (G := ULift.{v} G) (ρ := ρ.comp (MulEquiv.ulift.toMonoidHom))

/-- Helper for Exercise 2-2.3-7: the character of the lifted group/carrier representation is the
original character precomposed with `MulEquiv.ulift`. -/
private theorem character_uliftGroupCarrierRepresentation_eq
    {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (g : ULift.{v} G) :
    (uliftGroupCarrierRepresentation (G := G) ρ).character g = ρ.character (MulEquiv.ulift g) := by
  simpa [uliftGroupCarrierRepresentation] using
    (character_uliftRepresentation_local_eq
      (G := ULift.{v} G) (ρ := ρ.comp (MulEquiv.ulift.toMonoidHom)) g)

/-- Helper for Exercise 2-2.3-7: the normalized pairing is invariant under simultaneous
precomposition by a group equivalence. -/
private theorem groupFunctionPairing_precomp_mulEquiv_local
    {G : Type u} [Group G] [Finite G] {H : Type v} [Group H] [Finite H]
    (e : G ≃* H) (f g : H → ℂ) :
    ⟪(fun x : G ↦ f (e x)), fun x : G ↦ g (e x)⟫ = ⟪f, g⟫ := by
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype H := Fintype.ofFinite H
  have hcard : Fintype.card G = Fintype.card H := Fintype.card_congr e.toEquiv
  rw [Representation.groupFunctionPairingOverField, Representation.groupFunctionPairingOverField, hcard]
  congr 1
  simpa [MulEquiv.map_inv] using (Equiv.sum_comp e.toEquiv (fun y : H ↦ f y⁻¹ * g y))

/-- Helper for Exercise 2-2.3-7: lifting both the group and the carrier preserves irreducibility.
-/
private theorem isIrreducible_uliftGroupCarrierRepresentation_iff
    {G : Type u} [Group G] [Finite G] {V : Type v} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) :
    (uliftGroupCarrierRepresentation (G := G) ρ).IsIrreducible ↔ ρ.IsIrreducible := by
  let ρcomp : Representation ℂ (ULift.{v} G) V := ρ.comp (MulEquiv.ulift.toMonoidHom)
  constructor
  · intro h
    have hcomp : ρcomp.IsIrreducible := by
      exact
        (isIrreducible_uliftRepresentation_local_iff
          (G := ULift.{v} G) (ρ := ρcomp)).1 h
    letI : ρcomp.IsIrreducible := hcomp
    simpa using
      (isIrreducible_comp_of_mulEquiv_local_aux
        (G := G) (e := MulEquiv.ulift.symm) (σ := ρcomp))
  · intro h
    letI : ρ.IsIrreducible := h
    have hcomp : ρcomp.IsIrreducible := by
      exact
        isIrreducible_comp_of_mulEquiv_local_aux
          (G := ULift.{v} G) (e := MulEquiv.ulift) (σ := ρ)
    exact
      (isIrreducible_uliftRepresentation_local_iff
        (G := ULift.{v} G) (ρ := ρcomp)).2 hcomp

omit [Nontrivial X] [MulAction.IsPretransitive G X] [Nonempty X] in
/-- Helper for Exercise 2-2.3-7: for an inversion-invariant class function, pairing its square
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

-- Proof sketch: in the transitive case, write `χ = 1 + ψ` using
-- `permutation_character_eq_trivial_add_augmentation`, expand the normalized self-pairing of `χ`,
-- and use `augmentation_character_pairing_with_trivial_eq_zero`. The remaining condition is the
-- self-pairing of `ψ`, which equals `1` exactly when `θ` is irreducible by
-- `self_character_pairing_eq_one_iff_isIrreducible`.
/-- Exercise 2-2.3-7 (7): in part (c), clause (iii), namely `⟪χ², 1⟫ = 2`, is equivalent to
clause (iv). -/
theorem character_square_pairing_eq_two_iff_augmentation_isIrreducible :
    (⟪(ofMulAction ℂ G X).character ^ 2, (1 : G → ℂ)⟫ = 2) ↔
      (permutationAugmentationRepresentation ℂ G X).IsIrreducible := by
  let _ := (inferInstance : Nontrivial X)
  letI : Fintype G := Fintype.ofFinite G
  letI : Invertible (Nat.card X : ℂ) := invertibleOfNonzero (by
    exact_mod_cast Nat.card_pos.ne')
  letI : FiniteDimensional ℂ (permutationAugmentationSubrepresentation ℂ G X).toSubmodule :=
    inferInstance
  let ψ : G → ℂ := permutationAugmentationCharacter ℂ G X
  have htriv : (trivial ℂ G ℂ).character = (1 : G → ℂ) := by
    ext g
    simp [Representation.character, Representation.trivial]
  have hχ : (ofMulAction ℂ G X).character = (1 : G → ℂ) + ψ := by
    simpa [htriv, ψ] using
      (permutation_character_eq_trivial_add_augmentation (k := ℂ) (G := G) (X := X))
  have hperm_inv : ∀ g : G, (ofMulAction ℂ G X).character g⁻¹ = (ofMulAction ℂ G X).character g := by
    intro g
    have hcard :
        (MulAction.fixedBy X g⁻¹).ncard = (MulAction.fixedBy X g).ncard := by
      exact congrArg Set.ncard (MulAction.fixedBy_inv (G := G) (α := X) g)
    change (ofMulAction ℂ G X).character g⁻¹ = (ofMulAction ℂ G X).character g
    rw [ofMulAction_character_eq_ncard_fixedBy, ofMulAction_character_eq_ncard_fixedBy]
    exact congrArg (fun n : ℕ ↦ (n : ℂ)) hcard
  have hψ_inv : ∀ g : G, ψ g⁻¹ = ψ g := by
    intro g
    have hg_inv : (ofMulAction ℂ G X).character g⁻¹ = 1 + ψ g⁻¹ := by
      simpa using congrFun hχ g⁻¹
    have hg : (ofMulAction ℂ G X).character g = 1 + ψ g := by
      simpa using congrFun hχ g
    have hsum : 1 + ψ g⁻¹ = 1 + ψ g := hg_inv.symm.trans <| (hperm_inv g).trans hg
    simpa using hsum
  have hpair_one : ⟪(1 : G → ℂ), (1 : G → ℂ)⟫ = 1 := by
    simp [Representation.groupFunctionPairingOverField]
  have hψ_zero : ⟪ψ, (1 : G → ℂ)⟫ = 0 := by
    simpa [ψ] using augmentation_character_pairing_with_trivial_eq_zero (G := G) (X := X)
  have hsq :
      ((1 : G → ℂ) + ψ) ^ 2 = (1 : G → ℂ) + (2 : ℂ) • ψ + ψ ^ 2 := by
    ext g
    simp [pow_two]
    ring
  have hreduce :
      ⟪(ofMulAction ℂ G X).character ^ 2, (1 : G → ℂ)⟫ = 1 + ⟪ψ, ψ⟫ := by
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
            rw [groupFunctionPairing_sq_trivial_eq_self_of_inv_invariant ψ hψ_inv]
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
    finiteModelRep_local ρ
  have hρf_char :
      ρf.character = fun g : Shrink.{0} G ↦ ψ (Shrink.mulEquiv g) := by
    ext g
    have hiso := congrFun (Representation.char_iso (finiteModelRepEquivComp_local ρ)) g
    simpa [ρf, ρ, ψ] using hiso
  have hpairing_finiteModel : ⟪ρf.character, ρf.character⟫ = ⟪ψ, ψ⟫ := by
    rw [hρf_char]
    convert
      groupFunctionPairing_precomp_mulEquiv_local
        (e := (Shrink.mulEquiv : Shrink.{0} G ≃* G)) ψ ψ using 2
  have hself_iff :
      ⟪ψ, ψ⟫ = 1 ↔ ρ.IsIrreducible := by
    have hρf_iff : ⟪ρf.character, ρf.character⟫ = 1 ↔ ρf.IsIrreducible := by
      exact self_character_pairing_eq_one_iff_isIrreducible ρf
    constructor
    · intro hself
      have hself_f : ⟪ρf.character, ρf.character⟫ = 1 := by
        rw [hpairing_finiteModel]
        exact hself
      have hirr_f : ρf.IsIrreducible := hρf_iff.mp hself_f
      letI : ρf.IsIrreducible := hirr_f
      have hirr_comp :
          ρcomp.IsIrreducible := by
        exact
          isIrreducible_of_nonempty_equiv_local
            (σ := ρf) (τ := ρcomp) ⟨finiteModelRepEquivComp_local ρ⟩
      letI : ρcomp.IsIrreducible := hirr_comp
      let ρorig :
          Representation ℂ G (permutationAugmentationSubrepresentation ℂ G X).toSubmodule :=
        ρcomp.comp ((Shrink.mulEquiv : Shrink.{0} G ≃* G).symm.toMonoidHom)
      have hirr_orig : ρorig.IsIrreducible := by
        exact
          isIrreducible_comp_of_mulEquiv_local_aux
          (G := G) (e := (Shrink.mulEquiv : Shrink.{0} G ≃* G).symm)
          (σ := ρcomp)
      have hρorig : ρorig = ρ := by
        ext g x a
        have hshrink :
            Shrink.mulEquiv ((Shrink.mulEquiv : Shrink.{0} G ≃* G).symm g) = g := by
          simp
        dsimp [ρorig, ρcomp]
        have hx :
            (ρ (Shrink.mulEquiv ((Shrink.mulEquiv : Shrink.{0} G ≃* G).symm g))) x =
              (ρ g) x := by
          exact congrArg (fun h : G ↦ (ρ h) x) hshrink
        exact congrArg
          (fun y : (permutationAugmentationSubrepresentation ℂ G X).toSubmodule =>
            ((y : X →₀ ℂ) a))
          hx
      rwa [hρorig] at hirr_orig
    · intro hirr
      letI : ρ.IsIrreducible := hirr
      have hirr_f : ρf.IsIrreducible := finiteModelRep_isIrreducible_local (σ := ρ)
      have hself_f : ⟪ρf.character, ρf.character⟫ = 1 := hρf_iff.mpr hirr_f
      rwa [hpairing_finiteModel] at hself_f
  constructor
  · intro hpair
    have hself : ⟪ψ, ψ⟫ = 1 := by
      rw [hreduce] at hpair
      have hsub := congrArg (fun z : ℂ ↦ z - 1) hpair
      norm_num at hsub
      exact hsub
    exact hself_iff.mp hself
  · intro hirr
    have hself : ⟪ψ, ψ⟫ = 1 := hself_iff.mpr hirr
    calc
      ⟪(ofMulAction ℂ G X).character ^ 2, (1 : G → ℂ)⟫ = 1 + ⟪ψ, ψ⟫ := hreduce
      _ = 2 := by
            rw [hself]
            norm_num

end TransitiveCase

end Representation
