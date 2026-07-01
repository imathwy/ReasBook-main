import Mathlib
import Serre.Chap13.Exercise_13_13_1_16.GammaActions
import Serre.Chap13.Exercise_13_13_1_15

open CategoryTheory
open IsCyclotomicExtension.Rat
open scoped MonoidAlgebra Representation
open Representation

noncomputable section

universe u w

variable {G : Type u} [Group G] [Finite G]

section ProductPoints

variable {K : Type u} [Field K] [NumberField K]
variable [IsCyclotomicExtension {Monoid.exponent G} ℚ K]
variable {A : Type w} [CommRing A] [Algebra ℚ A]
variable {B : Type w} [CommRing B] [Algebra ℚ B]

attribute [local instance] Classical.decEq

/-- Helper for Exercise 13-13.1-16: the image of the first product idempotent under a
`ℚ`-algebra homomorphism to the field `K` is itself idempotent. -/
theorem algHom_prod_fst_idempotent
    (φ : A × B →ₐ[ℚ] K) :
    IsIdempotentElem (φ (1, 0)) := by
  -- Apply `φ` to the obvious idempotent `(1,0)`.
  rw [IsIdempotentElem, ← map_mul]
  simp

/-- Helper for Exercise 13-13.1-16: if a point of `A × B` sends `(1,0)` to `1`, then it sends the
complementary idempotent `(0,1)` to `0`. -/
theorem algHom_prod_snd_idempotent_eq_zero_of_fst_eq_one
    (φ : A × B →ₐ[ℚ] K) (h : φ (1, 0) = 1) :
    φ (0, 1) = 0 := by
  -- The two product idempotents add to `1`, so once the first one survives the second vanishes.
  have hsum : φ (1, 0) + φ (0, 1) = 1 := by
    have hadd : φ (1, 0) + φ (0, 1) = φ (1 : A × B) := by
      rw [← map_add]
      congr
      ext <;> simp
    simpa using hadd.trans φ.map_one
  simpa [h] using hsum

/-- Helper for Exercise 13-13.1-16: if a point of `A × B` does not send `(1,0)` to `1`, then the
idempotent image must be `0`. -/
theorem algHom_prod_fst_idempotent_eq_zero_of_ne_one
    (φ : A × B →ₐ[ℚ] K) (h : φ (1, 0) ≠ 1) :
    φ (1, 0) = 0 := by
  -- A field has no nontrivial idempotents.
  rcases (IsIdempotentElem.iff_eq_zero_or_one.mp (algHom_prod_fst_idempotent φ)) with
    hzero | hone
  · exact hzero
  · exact False.elim (h hone)

/-- Helper for Exercise 13-13.1-16: once `(1,0)` maps to `1`, every element supported on the
second factor maps to `0`. -/
theorem algHom_prod_snd_support_eq_zero_of_fst_eq_one
    (φ : A × B →ₐ[ℚ] K) (h : φ (1, 0) = 1) (b : B) :
    φ (0, b) = 0 := by
  have h01 : φ (0, 1) = 0 :=
    algHom_prod_snd_idempotent_eq_zero_of_fst_eq_one φ h
  -- Multiply by the complementary idempotent `(0,1)` to isolate the second coordinate.
  calc
    φ (0, b) = φ ((0, 1) * (0, b)) := by simp
    _ = φ (0, 1) * φ (0, b) := by rw [map_mul]
    _ = 0 := by simp [h01]

/-- Helper for Exercise 13-13.1-16: once `(1,0)` maps to `0`, every element supported on the
first factor maps to `0`. -/
theorem algHom_prod_fst_support_eq_zero_of_fst_eq_zero
    (φ : A × B →ₐ[ℚ] K) (h : φ (1, 0) = 0) (a : A) :
    φ (a, 0) = 0 := by
  -- Multiply by `(1,0)` to isolate the first coordinate.
  calc
    φ (a, 0) = φ ((1, 0) * (a, 0)) := by simp
    _ = φ (1, 0) * φ (a, 0) := by rw [map_mul]
    _ = 0 := by simp [h]

/-- Helper for Exercise 13-13.1-16: if a point of `A × B` keeps `(1,0)`, it factors through the
first projection. -/
noncomputable def algHom_prod_factorFst
    (φ : A × B →ₐ[ℚ] K) (h : φ (1, 0) = 1) :
    A →ₐ[ℚ] K :=
  { toFun := fun a ↦ φ (a, 0)
    map_one' := by simpa [h]
    map_mul' := by
      intro a a'
      simpa using (map_mul φ (a, 0) (a', 0))
    map_zero' := by
      exact map_zero φ
    map_add' := by
      intro a a'
      simpa using (map_add φ (a, 0) (a', 0))
    commutes' := by
      intro q
      -- Rewrite `(q,0)` as the full scalar plus a killed second-factor term.
      have hzero :
          φ (0, algebraMap ℚ B q) = 0 :=
        algHom_prod_snd_support_eq_zero_of_fst_eq_one φ h (algebraMap ℚ B q)
      have hscalar :
          φ ((algebraMap ℚ A q, 0) + (0, algebraMap ℚ B q)) = algebraMap ℚ K q := by
        simpa using φ.commutes q
      calc
        φ (algebraMap ℚ A q, 0)
            = φ (algebraMap ℚ A q, 0) + φ (0, algebraMap ℚ B q) := by
                rw [hzero, add_zero]
        _ = φ ((algebraMap ℚ A q, 0) + (0, algebraMap ℚ B q)) := by
              rw [map_add]
        _ = algebraMap ℚ K q := hscalar }

/-- Helper for Exercise 13-13.1-16: if a point of `A × B` kills `(1,0)`, it factors through the
second projection. -/
noncomputable def algHom_prod_factorSnd
    (φ : A × B →ₐ[ℚ] K) (h : φ (1, 0) = 0) :
    B →ₐ[ℚ] K :=
  { toFun := fun b ↦ φ (0, b)
    map_one' := by
      have hsum : φ (1, 0) + φ (0, 1) = 1 := by
        have hadd : φ (1, 0) + φ (0, 1) = φ (1 : A × B) := by
          rw [← map_add]
          congr
          ext <;> simp
        simpa using hadd.trans φ.map_one
      simpa [h] using hsum
    map_mul' := by
      intro b b'
      simpa using (map_mul φ (0, b) (0, b'))
    map_zero' := by
      exact map_zero φ
    map_add' := by
      intro b b'
      simpa using (map_add φ (0, b) (0, b'))
    commutes' := by
      intro q
      -- Rewrite `(0,q)` as the full scalar plus a killed first-factor term.
      have hzero :
          φ (algebraMap ℚ A q, 0) = 0 :=
        algHom_prod_fst_support_eq_zero_of_fst_eq_zero φ h (algebraMap ℚ A q)
      have hscalar :
          φ ((algebraMap ℚ A q, 0) + (0, algebraMap ℚ B q)) = algebraMap ℚ K q := by
        simpa using φ.commutes q
      calc
        φ (0, algebraMap ℚ B q)
            = φ (algebraMap ℚ A q, 0) + φ (0, algebraMap ℚ B q) := by
                rw [hzero, zero_add]
        _ = φ ((algebraMap ℚ A q, 0) + (0, algebraMap ℚ B q)) := by
              rw [map_add]
        _ = algebraMap ℚ K q := hscalar }

/-- Helper for Exercise 13-13.1-16: under the hypothesis `φ (1,0) = 1`, the explicit first-factor
map reconstructs `φ`. -/
theorem algHom_prod_factorFst_comp_fst
    (φ : A × B →ₐ[ℚ] K) (h : φ (1, 0) = 1) :
    (algHom_prod_factorFst φ h).comp (AlgHom.fst ℚ A B) = φ := by
  ext z
  rcases z with ⟨a, b⟩
  have hzero : φ (0, b) = 0 :=
    algHom_prod_snd_support_eq_zero_of_fst_eq_one φ h b
  -- Split `(a,b)` into its two product coordinates and kill the second one.
  calc
    ((algHom_prod_factorFst φ h).comp (AlgHom.fst ℚ A B)) (a, b)
        = φ (a, 0) := by rfl
    _ = φ (a, 0) + φ (0, b) := by rw [hzero, add_zero]
    _ = φ ((a, 0) + (0, b)) := by rw [map_add]
    _ = φ (a, b) := by simp

/-- Helper for Exercise 13-13.1-16: under the hypothesis `φ (1,0) = 0`, the explicit second-factor
map reconstructs `φ`. -/
theorem algHom_prod_factorSnd_comp_snd
    (φ : A × B →ₐ[ℚ] K) (h : φ (1, 0) = 0) :
    (algHom_prod_factorSnd φ h).comp (AlgHom.snd ℚ A B) = φ := by
  ext z
  rcases z with ⟨a, b⟩
  have hzero : φ (a, 0) = 0 :=
    algHom_prod_fst_support_eq_zero_of_fst_eq_zero φ h a
  -- Split `(a,b)` into its two product coordinates and kill the first one.
  calc
    ((algHom_prod_factorSnd φ h).comp (AlgHom.snd ℚ A B)) (a, b)
        = φ (0, b) := by rfl
    _ = φ (a, 0) + φ (0, b) := by rw [hzero, zero_add]
    _ = φ ((a, 0) + (0, b)) := by rw [map_add]
    _ = φ (a, b) := by simp

/-- Helper for Exercise 13-13.1-16: a `K`-point of a product `ℚ`-algebra factors through exactly
one of the two projections. -/
theorem algHom_prod_factor_through_fst_or_snd
    (φ : A × B →ₐ[ℚ] K) :
    (∃ ψ : A →ₐ[ℚ] K, φ = ψ.comp (AlgHom.fst ℚ A B)) ∨
      (∃ ψ : B →ₐ[ℚ] K, φ = ψ.comp (AlgHom.snd ℚ A B)) := by
  by_cases h : φ (1, 0) = 1
  · -- If `(1,0)` survives, the whole point comes from the first factor.
    exact Or.inl ⟨algHom_prod_factorFst φ h,
      (algHom_prod_factorFst_comp_fst φ h).symm⟩
  · have hzero : φ (1, 0) = 0 :=
      algHom_prod_fst_idempotent_eq_zero_of_ne_one φ h
    -- Otherwise the field forces `(1,0)` to die, so the point comes from the second factor.
    exact Or.inr ⟨algHom_prod_factorSnd φ hzero,
      (algHom_prod_factorSnd_comp_snd φ hzero).symm⟩

/-- Helper for Exercise 13-13.1-16: the concrete product-point classifier used in the equivalence
with the disjoint union of factor point sets. -/
noncomputable def algHom_points_prod_toSum (φ : A × B →ₐ[ℚ] K) :
    (A →ₐ[ℚ] K) ⊕ (B →ₐ[ℚ] K) :=
  if h : φ (1, 0) = 1 then
    Sum.inl (algHom_prod_factorFst φ h)
  else
    Sum.inr (algHom_prod_factorSnd φ (algHom_prod_fst_idempotent_eq_zero_of_ne_one φ h))

/-- Helper for Exercise 13-13.1-16: the inverse concrete classifier from a chosen factor point
back to a product point. -/
noncomputable def algHom_points_prod_fromSum :
    ((A →ₐ[ℚ] K) ⊕ (B →ₐ[ℚ] K)) → (A × B →ₐ[ℚ] K) :=
  Sum.elim
    (fun ψ ↦ ψ.comp (AlgHom.fst ℚ A B))
    (fun ψ ↦ ψ.comp (AlgHom.snd ℚ A B))

/-- Helper for Exercise 13-13.1-16: package the product-point classification as a concrete
equivalence between product points and the disjoint union of the two factor point sets. -/
noncomputable def algHom_points_prod_equiv_sum :
    (A × B →ₐ[ℚ] K) ≃ ((A →ₐ[ℚ] K) ⊕ (B →ₐ[ℚ] K)) where
  toFun := algHom_points_prod_toSum
  invFun := algHom_points_prod_fromSum
  left_inv := by
    intro φ
    by_cases h : φ (1, 0) = 1
    · -- In the first branch we recover `φ` through the first projection.
      simp [algHom_points_prod_toSum, algHom_points_prod_fromSum, h,
        algHom_prod_factorFst_comp_fst φ h]
    · let hzero : φ (1, 0) = 0 :=
        algHom_prod_fst_idempotent_eq_zero_of_ne_one φ h
      -- In the second branch we recover `φ` through the second projection.
      simp [algHom_points_prod_toSum, algHom_points_prod_fromSum, h, hzero,
        algHom_prod_factorSnd_comp_snd φ hzero]
  right_inv := by
    intro z
    cases z with
    | inl ψ =>
        -- A point already coming from the first factor stays in the first branch.
        simp [algHom_points_prod_toSum, algHom_points_prod_fromSum, algHom_prod_factorFst]
    | inr ψ =>
        -- A point already coming from the second factor stays in the second branch.
        simp [algHom_points_prod_toSum, algHom_points_prod_fromSum, algHom_prod_factorSnd]

/-- Helper for Exercise 13-13.1-16: postcomposition by cyclotomic Galois automorphisms respects
the explicit first-factor model of a product point. -/
theorem smul_algHom_prod_factorFst
    (t : Γ_ℚ(G)) (φ : A × B →ₐ[ℚ] K) (h : φ (1, 0) = 1) :
    algHom_prod_factorFst (t • φ) (by
      change
        ((galEquivZMod (Monoid.exponent G) K).symm t).toAlgHom (φ (1, 0)) = 1
      simpa [h]) =
      t • algHom_prod_factorFst φ h := by
  ext a
  -- Both sides evaluate by first taking the first-factor coordinate, then postcomposing with the
  -- same cyclotomic automorphism.
  rfl

/-- Helper for Exercise 13-13.1-16: postcomposition by cyclotomic Galois automorphisms respects
the explicit second-factor model of a product point. -/
theorem smul_algHom_prod_factorSnd
    (t : Γ_ℚ(G)) (φ : A × B →ₐ[ℚ] K) (h : φ (1, 0) = 0) :
    algHom_prod_factorSnd (t • φ) (by
      change
        ((galEquivZMod (Monoid.exponent G) K).symm t).toAlgHom (φ (1, 0)) = 0
      simpa [h]) =
      t • algHom_prod_factorSnd φ h := by
  ext b
  -- The second-factor model behaves symmetrically.
  rfl

/-- Helper for Exercise 13-13.1-16: the cyclotomic action preserves the branch test
`φ (1, 0) = 1` used in Serre's explicit product-point classifier. -/
theorem smul_algHom_prod_fst_eq_one_iff
    (t : Γ_ℚ(G)) (φ : A × B →ₐ[ℚ] K) :
    (t • φ) (1, 0) = 1 ↔ φ (1, 0) = 1 := by
  -- The governing scalar action is an automorphism of `K`, so it fixes `1` and reflects equality.
  change
    ((galEquivZMod (Monoid.exponent G) K).symm t).toAlgHom (φ (1, 0)) = 1 ↔
      φ (1, 0) = 1
  constructor
  · intro h
    exact ((galEquivZMod (Monoid.exponent G) K).symm t).injective (by simpa using h)
  · intro h
    simpa [h]

/-- Helper for Exercise 13-13.1-16: Serre's explicit classifier from `K`-points of `A × B` to the
disjoint union of `K`-points of `A` and `B` is equivariant for the cyclotomic `Γ_ℚ(G)`-action. -/
theorem algHom_points_prod_toSum_smul
    (t : Γ_ℚ(G)) (φ : A × B →ₐ[ℚ] K) :
    algHom_points_prod_toSum (t • φ) =
      t • algHom_points_prod_toSum φ := by
  by_cases h : φ (1, 0) = 1
  · have ht : (t • φ) (1, 0) = 1 :=
      (smul_algHom_prod_fst_eq_one_iff (G := G) (K := K) (A := A) (B := B) t φ).2 h
    -- In the first branch both classifiers land in the first factor, and the explicit factor map
    -- already commutes with cyclotomic postcomposition.
    rw [algHom_points_prod_toSum, dif_pos ht, algHom_points_prod_toSum, dif_pos h]
    simpa using smul_algHom_prod_factorFst (G := G) (K := K) (A := A) (B := B) t φ h
  · have ht : ¬ (t • φ) (1, 0) = 1 := by
      intro ht
      exact h ((smul_algHom_prod_fst_eq_one_iff
        (G := G) (K := K) (A := A) (B := B) t φ).1 ht)
    have hzero : φ (1, 0) = 0 :=
      algHom_prod_fst_idempotent_eq_zero_of_ne_one φ h
    -- In the second branch the product point factors through the second projection on both sides.
    rw [algHom_points_prod_toSum, dif_neg ht, algHom_points_prod_toSum, dif_neg h]
    simpa [hzero] using
      smul_algHom_prod_factorSnd (G := G) (K := K) (A := A) (B := B) t φ hzero

/-- Helper for Exercise 13-13.1-16: the `K`-points of a product `ℚ`-algebra form the disjoint
union of the `K`-points of its two factors, equivariantly for the cyclotomic `Γ_ℚ(G)`-action. -/
theorem algHom_points_prod_isomorphic_sum
    [Finite (A →ₐ[ℚ] K)] [Finite (B →ₐ[ℚ] K)] :
    IsIsomorphic
      (Action.ofMulAction (Γ_ℚ(G)) (A × B →ₐ[ℚ] K))
      (Action.ofMulAction (Γ_ℚ(G)) ((A →ₐ[ℚ] K) ⊕ (B →ₐ[ℚ] K))) := by
  -- Route correction: package the already constructed source-faithful classifier only after
  -- proving that its branch choice commutes with the cyclotomic action, and then build the raw
  -- `Type`-valued action isomorphism directly to avoid bundled-owner transport noise.
  refine ⟨Action.mkIso algHom_points_prod_equiv_sum.toIso ?_⟩
  intro t
  ext φ
  exact algHom_points_prod_toSum_smul (G := G) (K := K) (A := A) (B := B) t φ

end ProductPoints
