import Mathlib
import StacksProject_2024.Chap10.Lemma_10_15_4_Chinese_remainder
import StacksProject_2024.Chap15.Lemma_15_111_1
import StacksProject_2024.Chap15.Lemma_15_111_2

-- Declarations for this item will be appended below by the statement pipeline.

open Ideal
open IsLocalRing
open scoped BigOperators Pointwise TensorProduct

universe u v w

noncomputable section

section B1Action

variable {B : Type v} {K : Type u} {L : Type v} {K1 : Type w}
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Field K] [Algebra B K] [IsFractionRing B K]
variable [Field L] [Algebra B L] [Algebra K L] [IsScalarTower B K L]
variable [Field K1] [Algebra K K1]

local notation "G" => Gal(K1 / K)
local notation "L10" => TensorProduct K L K1
local notation "L1" => L10 ⧸ nilradical L10
local notation "B1" => integralClosure B L1
local notation "BFix" => FixedPoints.subring B1 G

local instance l1CommRing : CommRing L1 :=
  Ideal.Quotient.commRing _

local instance b1CommRing : CommRing B1 :=
  inferInstance

local instance b1Algebra : Algebra B B1 :=
  inferInstance

/- Domain-style sampling for Lemma 15.116.6:
- primary domain: Galois actions on the reduced tensor-product base change and the induced action
  on the corresponding integral closure over a discrete valuation ring
- sampled owner declarations:
  `MulSemiringAction.compHom`,
  `quotientMulSemiringAction`,
  `AlgEquiv.mapIntegralClosure`,
  `Algebra.IsInvariant.exists_smul_of_under_eq`,
  `exists_gal_smul_eq_of_isMaximal`
- best owner abstraction: the source-facing owner layer is the canonical `Gal(K1 / K)`-action on
  `L1 = (L ⊗[K] K1) ⧸ nilradical (L ⊗[K] K1)` together with the induced action on
  `B1 = integralClosure B L1` and its invariant-extension transitivity specialization
  `exists_gal_smul_eq_of_under_eq_of_reducedTensorBaseChange`; the maximal-ideal conjugacy
  statement should then be a thin specialization of that public owner layer
- primitive data: the reduced tensor product `L1 = (L ⊗[K] K1)_red`, the integral closure
  `B1 = integralClosure B L1`, and maximal ideals `m, m' : Ideal B1`
- derived API: the descended quotient action on `L1`, the induced action on `B1`, the invariant
  owner `Algebra.IsInvariant B B1 Gal(K1 / K)`, the under-equality transitivity theorem, and the
  maximal-ideal transitivity statement

Source/core/bridge triage:
- `source-facing`: transitivity of the `Gal(K1 / K)`-action on maximal ideals of `B1`
- `core/canonical`: `MulSemiringAction Gal(K1 / K) L1`,
  `MulSemiringAction Gal(K1 / K) B1`, and
  `Algebra.IsInvariant.exists_smul_of_under_eq`
- `bridge/view`: the tensor-product automorphisms of `L ⊗[K] K1`, their quotient descendant on
  `L1`, the induced integral-closure action on `B1`, and the source-facing under-equality
  specialization
-/

/-- The `K`-algebra automorphism of `L ⊗[K] K1` induced by a `K`-automorphism of `K1`. -/
private noncomputable def reducedBaseChangeAutAux (σ : Gal(K1/K)) :
    L10 ≃ₐ[K] L10 :=
  Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[K] L) σ

/-- The `B`-algebra automorphism of `L ⊗[K] K1` induced by a `K`-automorphism of `K1`. -/
private noncomputable def reducedBaseChangeAlgEquiv (σ : G) :
    L10 ≃ₐ[B] L10 where
  toRingEquiv := (reducedBaseChangeAutAux σ).toRingEquiv
  commutes' b := by
    change
      (Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[K] L) σ)
          (algebraMap B L b ⊗ₜ[K] (1 : K1)) =
        algebraMap B L b ⊗ₜ[K] (1 : K1)
    simp

/-- Helper for Lemma 15.116.6: the tensor automorphism attached to the identity element of the
Galois group is the identity endomorphism. -/
private theorem reducedBaseChangeAction_map_one :
    (reducedBaseChangeAutAux (1 : G)).toRingHom = RingHom.id L10 := by
  -- The tensor automorphism is determined by its values on the two tensor factors.
  refine Algebra.TensorProduct.ringHom_ext ?_ ?_
  · ext x
    simp [reducedBaseChangeAutAux]
  · ext x
    simp [reducedBaseChangeAutAux]

/-- Helper for Lemma 15.116.6: composing the tensor automorphisms matches multiplication in the
Galois group. -/
private theorem reducedBaseChangeAction_map_mul (σ τ : G) :
    (reducedBaseChangeAutAux (σ * τ)).toRingHom =
      ((reducedBaseChangeAutAux σ).toRingHom : L10 →+* L10) *
        (reducedBaseChangeAutAux τ).toRingHom := by
  -- The same generator check identifies both tensor endomorphisms.
  refine Algebra.TensorProduct.ringHom_ext ?_ ?_
  · ext x
    simp [reducedBaseChangeAutAux]
  · ext x
    simp [reducedBaseChangeAutAux]

/-- Helper for Lemma 15.116.6: the tensor automorphisms form the monoid action used on the
unreduced tensor product. -/
private noncomputable def reducedBaseChangeAction :
    G →* (L10 →+* L10) where
  toFun σ := (reducedBaseChangeAutAux σ).toRingHom
  map_one' := reducedBaseChangeAction_map_one
  map_mul' := reducedBaseChangeAction_map_mul

/-- The canonical `Gal(K1 / K)`-action on `L ⊗[K] K1`, acting through the `K1`-factor. -/
private noncomputable abbrev reducedBaseChangeMulSemiringAction :
    MulSemiringAction G L10 :=
  MulSemiringAction.compHom L10 (reducedBaseChangeAction : G →* (L10 →+* L10))

/-- Helper for Lemma 15.116.6: a ring equivalence carries the nilradical onto the nilradical. -/
private theorem ideal_map_nilradical_of_ringEquiv
    {R : Type*} {S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) :
    Ideal.map e.toRingHom (nilradical R) = nilradical S := by
  -- Transport nilpotence forward and backward along the ring equivalence.
  ext y
  constructor
  · intro hy
    rw [Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective] at hy
    rcases hy with ⟨x, hx, rfl⟩
    rw [mem_nilradical] at hx ⊢
    rcases hx with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [map_pow] using congrArg e hn
  · intro hy
    have hpre : e.symm y ∈ nilradical R := by
      rw [mem_nilradical] at hy ⊢
      rcases hy with ⟨n, hn⟩
      refine ⟨n, ?_⟩
      apply e.injective
      simpa [map_pow] using hn
    simpa using Ideal.mem_map_of_mem e.toRingHom hpre

-- Proof sketch: ring automorphisms preserve nilpotent elements, so the nilradical is stable under
-- the induced action.
/-- The induced `Gal(K1 / K)`-action on `L ⊗[K] K1` preserves the nilradical. -/
private theorem reducedBaseChangeAutAux_map_nilradical (σ : G) :
    Ideal.map (reducedBaseChangeAutAux σ).toRingHom
        (nilradical L10) =
      nilradical L10 := by
  -- Reuse the generic ring-equivalence transport statement.
  exact ideal_map_nilradical_of_ringEquiv (reducedBaseChangeAutAux σ).toRingEquiv

/-- The canonical `Gal(K1 / K)`-action on
`L1 = (L ⊗[K] K1) ⧸ nilradical (L ⊗[K] K1)`. -/
noncomputable abbrev reducedTensorBaseChangeMulSemiringAction :
    MulSemiringAction G L1 :=
  let _ : MulSemiringAction G L10 := reducedBaseChangeMulSemiringAction
  quotientMulSemiringAction (nilradical L10) fun σ ↦ by
    simpa [Ideal.pointwise_smul_def, reducedBaseChangeMulSemiringAction, reducedBaseChangeAutAux]
      using reducedBaseChangeAutAux_map_nilradical σ

/-- The induced `B`-algebra automorphism of
`L1 = (L ⊗[K] K1) ⧸ nilradical (L ⊗[K] K1)`. -/
private noncomputable def reducedBaseChangeAut (σ : G) :
    L1 ≃ₐ[B] L1 :=
  let h :
      nilradical L10 =
        Ideal.map
          (reducedBaseChangeAutAux σ).toRingHom
          (nilradical L10) :=
    (reducedBaseChangeAutAux_map_nilradical σ).symm
  Ideal.quotientEquivAlg (nilradical L10) (nilradical L10) (reducedBaseChangeAlgEquiv σ) h

/-- Helper for Lemma 15.116.6: the descended quotient automorphism attached to the identity
element is the identity on `L1`. -/
@[simp] private theorem reduced_base_change_aut_one :
    reducedBaseChangeAut (1 : G) = (AlgEquiv.refl : L1 ≃ₐ[B] L1) := by
  -- Check the quotient automorphism on representatives of `L ⊗[K] K1`.
  ext x
  refine Quotient.inductionOn' x ?_
  intro y
  change
    Ideal.Quotient.mk (nilradical L10)
        (((reducedBaseChangeAlgEquiv (B := B) (K := K) (L := L) (K1 := K1) (1 : G)) :
          L10 →+* L10) y) =
      Ideal.Quotient.mk (nilradical L10) y
  have hy :
      (((reducedBaseChangeAlgEquiv (B := B) (K := K) (L := L) (K1 := K1) (1 : G)) :
          L10 →+* L10) y) = y := by
    change ((reducedBaseChangeAutAux (K := K) (L := L) (K1 := K1) (1 : G)).toRingHom y) = y
    simpa using congrArg (fun f : L10 →+* L10 => f y)
      (reducedBaseChangeAction_map_one (K := K) (L := L) (K1 := K1))
  exact congrArg (Ideal.Quotient.mk (nilradical L10)) hy

/-- Helper for Lemma 15.116.6: the descended quotient automorphisms compose according to the
group law on `G`. -/
private theorem reduced_base_change_aut_mul (σ τ : G) :
    reducedBaseChangeAut (σ * τ) =
      ((reducedBaseChangeAut τ).trans (reducedBaseChangeAut σ) : L1 ≃ₐ[B] L1) := by
  -- Check the two quotient automorphisms on representatives of `L ⊗[K] K1`.
  ext x
  refine Quotient.inductionOn' x ?_
  intro y
  change
    Ideal.Quotient.mk (nilradical L10)
        (((reducedBaseChangeAlgEquiv (B := B) (K := K) (L := L) (K1 := K1) (σ * τ)) :
          L10 →+* L10) y) =
      Ideal.Quotient.mk (nilradical L10)
        (((reducedBaseChangeAlgEquiv (B := B) (K := K) (L := L) (K1 := K1) σ) :
          L10 →+* L10)
          (((reducedBaseChangeAlgEquiv (B := B) (K := K) (L := L) (K1 := K1) τ) :
            L10 →+* L10) y))
  have hy :
      (((reducedBaseChangeAlgEquiv (B := B) (K := K) (L := L) (K1 := K1) (σ * τ)) :
          L10 →+* L10) y) =
        (((reducedBaseChangeAlgEquiv (B := B) (K := K) (L := L) (K1 := K1) σ) :
            L10 →+* L10)
          (((reducedBaseChangeAlgEquiv (B := B) (K := K) (L := L) (K1 := K1) τ) :
              L10 →+* L10) y)) := by
    change
      ((reducedBaseChangeAutAux (K := K) (L := L) (K1 := K1) (σ * τ)).toRingHom y) =
        ((((reducedBaseChangeAutAux (K := K) (L := L) (K1 := K1) σ).toRingHom :
            L10 →+* L10) *
          (reducedBaseChangeAutAux (K := K) (L := L) (K1 := K1) τ).toRingHom) y)
    simpa using congrArg (fun f : L10 →+* L10 => f y)
      (reducedBaseChangeAction_map_mul (K := K) (L := L) (K1 := K1) σ τ)
  exact congrArg (Ideal.Quotient.mk (nilradical L10)) hy

/-- The canonical `Gal(K1 / K)`-action on `B1 = integralClosure B L1`. -/
noncomputable abbrev reducedTensorBaseChangeIntegralClosureMulSemiringAction :
    MulSemiringAction G B1 :=
  { smul := fun σ x ↦
      (reducedBaseChangeAut σ).mapIntegralClosure x
    one_smul := by
      intro x
      -- Reduce the integral-closure equality to the descended quotient action on `L1`.
      apply Subtype.ext
      change reducedBaseChangeAut (1 : G) (x : L1) = x
      simpa using congrArg (fun e : L1 ≃ₐ[B] L1 => e (x : L1)) reduced_base_change_aut_one
    mul_smul := by
      intro σ τ x
      -- After pushing to `L1`, this is exactly the quotient-level composition lemma.
      apply Subtype.ext
      change reducedBaseChangeAut (σ * τ) (x : L1) =
          reducedBaseChangeAut σ (reducedBaseChangeAut τ (x : L1))
      simpa using congrArg (fun e : L1 ≃ₐ[B] L1 => e (x : L1))
        (reduced_base_change_aut_mul σ τ)
    smul_zero := by
      intro σ
      -- The descended quotient automorphism is a ring homomorphism, so it preserves zero.
      apply Subtype.ext
      change reducedBaseChangeAut σ (0 : L1) = 0
      simp
    smul_add := by
      intro σ x y
      -- The addition law is inherited from the ambient `B`-algebra automorphism of `L1`.
      apply Subtype.ext
      change reducedBaseChangeAut σ ((x : L1) + (y : L1)) =
          reducedBaseChangeAut σ (x : L1) + reducedBaseChangeAut σ (y : L1)
      simp
    smul_one := by
      intro σ
      -- The descended quotient automorphism preserves the multiplicative identity.
      apply Subtype.ext
      change reducedBaseChangeAut σ (1 : L1) = 1
      simp
    smul_mul := by
      intro σ x y
      -- The multiplicative law is inherited from the ambient `B`-algebra automorphism of `L1`.
      apply Subtype.ext
      change reducedBaseChangeAut σ ((x : L1) * (y : L1)) =
          reducedBaseChangeAut σ (x : L1) * reducedBaseChangeAut σ (y : L1)
      simp }

local instance : SMul G B1 :=
  reducedTensorBaseChangeIntegralClosureMulSemiringAction.toSMul

local instance : MulSemiringAction G B1 :=
  reducedTensorBaseChangeIntegralClosureMulSemiringAction

/-- Helper for Lemma 15.116.6: fixed elements of `B1` commute with the `Gal(K1 / K)`-action on
`B1`. -/
private instance fixed_points_subring_smulCommClass :
    SMulCommClass G (FixedPoints.subring B1 G) B1 where
  smul_comm σ x y := by
    -- Rewrite the fixed scalar into `B1` and use that it is fixed by every element of `G`.
    have hx : (MulSemiringAction.toRingHom G B1 σ) (x : B1) = (x : B1) := by
      simpa using x.2 σ
    change (MulSemiringAction.toRingHom G B1 σ) ((x : B1) * y) = (x : B1) * (σ • y)
    rw [map_mul]
    rw [hx]
    simpa

/-- The canonical `Gal(K1 / K)`-action on the reduced tensor-base-change integral closure `B1`
commutes with the scalar action of `B`. -/
theorem reducedTensorBaseChangeIntegralClosure_smulCommClass :
    SMulCommClass G B B1 := by
  -- The integral-closure transport is a `B`-algebra equivalence, so it fixes base scalars.
  refine ⟨fun σ b x ↦ ?_⟩
  change
    (reducedBaseChangeAut σ).mapIntegralClosure (b • x) =
      b • (reducedBaseChangeAut σ).mapIntegralClosure x
  simp [Algebra.smul_def, map_mul]

variable [FiniteDimensional K K1] [Normal K K1]

attribute [local instance] reducedTensorBaseChangeIntegralClosure_smulCommClass

/-- Helper for Lemma 15.116.6: a fixed element of `B1` has a positive power coming from `B`. -/
private theorem fixed_integral_closure_element_pow_mem_baseRing
    (x : BFix) :
    ∃ n : ℕ, 0 < n ∧ ∃ b : B, algebraMap B B1 b = (x : B1) ^ n := by
  -- TODO for Lemma 15.116.6: descend the fixed element through the quotient fixed-points map for
  -- `L10 → L1`, then identify `FixedPoints.subring L10 G` with `L` via
  -- `tensorBaseChangeFixedPointsEquivOfFlat`, and finally use that the DVR `B` is integrally
  -- closed in `L` to land in `B`.
  sorry

/-- Helper for Lemma 15.116.6: if two maximal ideals are not Galois-conjugate, an orbit product
produces a fixed element that lies in one and not the other. -/
private theorem exists_fixed_element_mem_not_mem_of_not_conjugate
    (m m' : Ideal B1) (hm : m.IsMaximal) (hm' : m'.IsMaximal)
    (hsep : ∀ σ : G, σ • m ≠ m') :
    ∃ x : BFix, (x : B1) ∈ m ∧ (x : B1) ∉ m' := by
  classical
  letI : m.IsPrime := hm.isPrime
  letI : m'.IsPrime := hm'.isPrime
  have hunder_ne : m.under BFix ≠ m'.under BFix := by
    -- If the contractions agreed, the invariant-theory owner theorem would already conjugate `m`
    -- to `m'`, contradicting the separation hypothesis.
    intro hunder
    obtain ⟨σ, hσ⟩ :=
      by
        simpa [eq_comm] using
          Algebra.IsInvariant.exists_smul_of_under_eq BFix B1 G m m' hunder
    exact hsep σ hσ.symm
  letI : Algebra.IsIntegral BFix B1 :=
    Algebra.IsInvariant.isIntegral BFix B1 G
  have hm_under : (m.under BFix).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m
  have hm'_under : (m'.under BFix).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m'
  have hfixed :
      ∃ x : BFix, x ∈ m.under BFix ∧ x ∉ m'.under BFix := by
    -- Distinct maximal ideals of the fixed subring are incomparable, so some fixed element lies
    -- in the first contraction and avoids the second.
    by_contra hno
    have hle : m.under BFix ≤ m'.under BFix := by
      intro x hx
      by_contra hx'
      exact hno ⟨x, hx, hx'⟩
    exact hunder_ne <|
      Ideal.IsMaximal.eq_of_le hm_under hm'_under.ne_top hle
  rcases hfixed with ⟨x, hx, hx'⟩
  refine ⟨x, ?_, ?_⟩
  · -- Membership in the contraction is exactly membership upstairs after forgetting the fixed
    -- structure.
    simpa using hx
  · -- The same contraction description turns non-membership upstairs into non-membership below.
    simpa using hx'

/-- Helper for Lemma 15.116.6: every maximal ideal of `B1` contracts to the maximal ideal of the
discrete valuation ring `B`. -/
private theorem comap_eq_maximalIdeal_of_isMaximal
    (m : Ideal B1) (hm : m.IsMaximal) :
    Ideal.comap (algebraMap B B1) m = maximalIdeal B := by
  letI : m.IsMaximal := hm
  -- The integral closure is integral over the base DVR, so a maximal ideal upstairs contracts to
  -- the unique maximal ideal downstairs.
  exact IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m)

/-- Helper for Lemma 15.116.6: a fixed element cannot lie in one maximal ideal of `B1` and avoid
another maximal ideal once a positive power descends to `B`. -/
private theorem fixed_element_mem_and_not_mem_contradiction
    (m m' : Ideal B1) (hm : m.IsMaximal) (hm' : m'.IsMaximal)
    (x : BFix) (hxm : (x : B1) ∈ m) (hxm' : (x : B1) ∉ m') :
    False := by
  letI : m.IsMaximal := hm
  letI : m'.IsMaximal := hm'
  obtain ⟨n, hn, b, hb⟩ := fixed_integral_closure_element_pow_mem_baseRing x
  have hb_mem_m : algebraMap B B1 b ∈ m := by
    -- The descended element equals a positive power of `x`, so membership in `m` is immediate.
    rw [hb]
    exact m.pow_mem_of_mem hxm n hn
  have hb_mem_max : b ∈ maximalIdeal B := by
    -- Contract membership along `B → B1` using that `m` lies over `maximalIdeal B`.
    rw [← comap_eq_maximalIdeal_of_isMaximal (m := m) hm, Ideal.mem_comap]
    exact hb_mem_m
  have hb_mem_m' : algebraMap B B1 b ∈ m' := by
    -- The same contraction computation shows the descended base element lies in every maximal
    -- ideal of `B1`.
    rw [← Ideal.mem_comap, comap_eq_maximalIdeal_of_isMaximal (m := m') hm']
    exact hb_mem_max
  have hpow_not_mem_m' : (x : B1) ^ n ∉ m' := by
    -- In a prime ideal, membership of a power forces membership of the element itself.
    intro hxpow
    exact hxm' (hm'.isPrime.mem_of_pow_mem _ hxpow)
  exact hpow_not_mem_m' (by simpa [hb] using hb_mem_m')

-- Proof sketch: argue by contradiction. If `m` and `m'` are not conjugate, the source orbit
-- product gives a fixed separator in `B1`; descending a positive power to `B` contradicts that
-- the DVR `B` has a unique maximal ideal.
/-- Lemma 15.116.6: with
`L1 = (L ⊗[K] K1) ⧸ nilradical (L ⊗[K] K1)` and `B1 = integralClosure B L1`, the canonical
`Gal(K1 / K)`-action on `B1` is transitive on the maximal ideals of `B1`. -/
@[stacks 09EU]
theorem exists_gal_smul_eq_of_isMaximal_of_reducedTensorBaseChange
    (m m' : Ideal B1) (hm : m.IsMaximal) (hm' : m'.IsMaximal) :
    ∃ σ : G, σ • m = m' := by
  -- Route correction: the old `B1^G`-local shell obscured the source proof. We now follow the
  -- textbook contradiction argument directly through an orbit separator and power descent.
  by_contra hnot
  have hsep : ∀ σ : G, σ • m ≠ m' := by
    intro σ hσ
    exact hnot ⟨σ, hσ⟩
  obtain ⟨x, hxm, hxm'⟩ :=
    exists_fixed_element_mem_not_mem_of_not_conjugate m m' hm hm' hsep
  exact fixed_element_mem_and_not_mem_contradiction m m' hm hm' x hxm hxm'

end B1Action
