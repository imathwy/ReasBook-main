import Mathlib
import Mathlib.RepresentationTheory.Intertwining
import Serre.Chap14.Corollary_14_14_4_3
import Serre.Chap14.Exercise_14_14_4_6.IdempotentLiftingBridge
import Serre.Chap14.Exercise_14_14_4_6.EquivariantEndomorphismFreeness
import Serre.Chap14.Exercise_14_14_4_6.EndomorphismReductionTransport
import Serre.Chap14.Exercise_14_14_4_6.RestrictedEndomorphismBaseChange
import Serre.Chap14.Exercise_14_14_4_6.ProjectorRangeBridge
import Serre.Chap14.Exercise_14_14_4_6.ProjectivePresentationBridge

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators MonoidAlgebra Representation TensorProduct
open CategoryTheory
open Representation
open FiniteProjectiveGroupAlgebraModule

universe u w w₁ x

noncomputable section

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {G : Type u} [Group G]

local notation "kA" => IsLocalRing.ResidueField A

variable {P : Type w} [AddCommGroup P] [Module A P] [Module A[G] P] [IsScalarTower A A[G] P]

variable {B : Type w₁} [Ring B] [Algebra A B] [Module.Free A B] [Module.Finite A B]
variable {Bbar : Type x} [Ring Bbar] [Algebra A Bbar] [Algebra (IsLocalRing.ResidueField A) Bbar]
variable [IsScalarTower A (IsLocalRing.ResidueField A) Bbar]

/- 
Domain-style sampling:
* Primary domain: residue-field reduction of finite projective `A[G]`-modules and the induced base
  change on their equivariant endomorphism algebras.
* Core/canonical owners inspected in the current chapter/project:
  `ρ.IntertwiningMap ρ`,
  `LinearMap.IsResidueFieldReduction.endAlgHom`, and
  `FiniteProjectiveGroupAlgebraModule.residueFieldReduction`.
* Related mathlib owner inspected for the same construction:
  `Representation.IntertwiningMap.equivAlgEnd` and `IsBaseChange.end`.
* Primitive data in this file: a residue-field reduction map
  `f : P →ₗ[A] Pbar` with `hf : f.IsResidueFieldReduction G`, and the owner objects
  `FiniteProjectiveGroupAlgebraModule A G`.
* Derived API here: freeness and base change for equivariant endomorphisms, lifting complete
  orthogonal idempotents through the reduction map, and existence of projective lifts in the owner
  category.
-/

section Henselian

variable [HenselianLocalRing A]

/-- Helper for Exercise 14-14.4-6: the universal idempotent polynomial `X^2 - X` is monic. -/
lemma x_sq_sub_X_monic :
    (Polynomial.X ^ 2 - Polynomial.X : Polynomial A).Monic := by
  -- Rewrite `X^2 - X` as `X (X - 1)` so monicity is immediate from the two linear factors.
  have hfactor :
      (Polynomial.X ^ 2 - Polynomial.X : Polynomial A) =
        Polynomial.X * (Polynomial.X - 1) := by
    ring
  rw [hfactor]
  simpa using (Polynomial.monic_X (R := A)).mul (Polynomial.monic_X_sub_C (1 : A))

/-- Helper for Exercise 14-14.4-6: after any coefficient extension, the universal idempotent
polynomial `X^2 - X` remains monic. -/
lemma x_sq_sub_X_map_monic
    {S : Type*} [CommRing S] [Algebra A S] :
    ((Polynomial.X ^ 2 - Polynomial.X : Polynomial A).map (algebraMap A S)).Monic := by
  -- Monicity is preserved when the coefficients are extended from `A` to `S`.
  simpa using (x_sq_sub_X_monic (A := A)).map (algebraMap A S)

/-- Helper for Exercise 14-14.4-6: localizing the quotient of `A[X]` by `X^2 - X` away from the
derivative gives a standard-etale presentation of the universal idempotent surface. -/
lemma x_sq_sub_X_derivative_standardEtale_cond :
    ∃ p₁ p₂ n,
      Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.X : Polynomial A) * p₁ +
        (Polynomial.X ^ 2 - Polynomial.X : Polynomial A) * p₂ =
          (Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.X : Polynomial A)) ^ n := by
  -- Here the standard-etale condition is tautological: we localize away from the derivative
  -- itself, so `f' * 1 + f * 0 = (f')^1`.
  refine ⟨1, 0, 1, ?_⟩
  simp

/-- Helper for Exercise 14-14.4-6: the standard-etale algebra attached to the universal
idempotent equation `X^2 - X = 0`, localized away from the derivative. -/
def x_sq_sub_X_standardEtalePair : StandardEtalePair A :=
  { f := Polynomial.X ^ 2 - Polynomial.X
    monic_f := x_sq_sub_X_monic (A := A)
    g := Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.X)
    cond := x_sq_sub_X_derivative_standardEtale_cond (A := A) }

/-- Helper for Exercise 14-14.4-6: maps out of the universal idempotent standard-etale algebra are
equivalent to choosing an idempotent element. -/
lemma x_sq_sub_X_standardEtale_hasMap_iff_isIdempotentElem
    {S : Type*} [CommRing S] [Algebra A S] (x : S) :
    (x_sq_sub_X_standardEtalePair (A := A)).HasMap x ↔ IsIdempotentElem x := by
  constructor
  · intro hx
    rcases hx with ⟨hx, -⟩
    -- The polynomial equation `x^2 - x = 0` is exactly the idempotent relation.
    simpa [x_sq_sub_X_standardEtalePair, Polynomial.aeval_def, IsIdempotentElem,
      pow_two, sub_eq_zero] using hx
  · intro hx
    -- Conversely, an idempotent is automatically a simple root of `X^2 - X`.
    refine ⟨?_, ?_⟩
    · simpa [x_sq_sub_X_standardEtalePair, Polynomial.aeval_def, IsIdempotentElem,
        pow_two, sub_eq_zero] using hx.eq
    · simpa [x_sq_sub_X_standardEtalePair] using
        (derivative_eval_X_sq_sub_X_isUnit_of_isIdempotentElem (R := S) hx)

/-- Helper for Exercise 14-14.4-6: the canonical `A`-algebra map into `A[uBar]` kills the
maximal ideal of the henselian local base. -/
lemma adjoin_singleton_algebraMap_ker_le
    {uBar : Bbar} :
    IsLocalRing.maximalIdeal A ≤
      RingHom.ker (Algebra.ofId A (Algebra.adjoin A ({uBar} : Set Bbar))) := by
  -- Elements of the maximal ideal already vanish in the residue field, hence also in `A[uBar]`.
  intro a ha
  rw [RingHom.mem_ker]
  apply Subtype.ext
  change algebraMap A Bbar a = 0
  rw [IsScalarTower.algebraMap_apply A (IsLocalRing.ResidueField A) Bbar]
  rw [← map_zero (algebraMap (IsLocalRing.ResidueField A) Bbar)]
  exact congrArg (algebraMap (IsLocalRing.ResidueField A) Bbar) <| by
    rw [IsLocalRing.ResidueField.algebraMap_eq]
    exact (IsLocalRing.residue_eq_zero_iff (R := A) a).2 ha

/-- Helper for Exercise 14-14.4-6: elements outside the maximal ideal stay units inside the
singleton-generated subalgebra `A[uBar]`. -/
lemma adjoin_singleton_algebraMap_units
    {uBar : Bbar} :
    (IsLocalRing.maximalIdeal A).primeCompl ≤
      (IsUnit.submonoid (Algebra.adjoin A ({uBar} : Set Bbar))).comap
        (Algebra.ofId A (Algebra.adjoin A ({uBar} : Set Bbar))) := by
  -- In a local ring, being outside the maximal ideal means being a unit, and units map to units.
  intro a ha
  change IsUnit (algebraMap A (Algebra.adjoin A ({uBar} : Set Bbar)) a)
  exact ((IsLocalRing.notMem_maximalIdeal (R := A)).mp ha).map
    (algebraMap A (Algebra.adjoin A ({uBar} : Set Bbar)))

/-- Helper for Exercise 14-14.4-6: the quotient residue field `A / 𝔪_A` identifies with the
prime-ideal residue field of `𝔪_A`. -/
noncomputable def localResidueFieldToMaximalIdealResidueField :
    IsLocalRing.ResidueField A →ₐ[A] (IsLocalRing.maximalIdeal A).ResidueField :=
  (AlgEquiv.ofBijective
      (IsScalarTower.toAlgHom A (IsLocalRing.ResidueField A)
        (IsLocalRing.maximalIdeal A).ResidueField)
      ((IsLocalRing.maximalIdeal A).bijective_algebraMap_quotient_residueField)).toAlgHom

/-- Helper for Exercise 14-14.4-6: the chosen identification of the two residue fields is
compatible with the original map `A → kA`. -/
lemma localResidueFieldToMaximalIdealResidueField_comp_toAlgHom :
    (localResidueFieldToMaximalIdealResidueField (A := A)).comp
        (IsScalarTower.toAlgHom A A (IsLocalRing.ResidueField A)) =
      IsScalarTower.toAlgHom A A (IsLocalRing.maximalIdeal A).ResidueField := by
  -- Both maps are induced by the same quotient map `A → A / 𝔪_A`.
  ext a <;> rfl

/-- Helper for Exercise 14-14.4-6: the residue-field action on `Bbar` restricts to the
singleton-generated subalgebra `A[uBar]`. -/
noncomputable def adjoin_singleton_residueFieldAlg
    {uBar : Bbar} :
    IsLocalRing.ResidueField A →ₐ[A] Algebra.adjoin A ({uBar} : Set Bbar) :=
  -- Lift the `A`-algebra map through the maximal ideal, then identify the two residue fields.
  (Ideal.ResidueField.liftₐ (IsLocalRing.maximalIdeal A)
    (Algebra.ofId A (Algebra.adjoin A ({uBar} : Set Bbar)))
    (adjoin_singleton_algebraMap_ker_le (A := A) (Bbar := Bbar) (uBar := uBar))
    (adjoin_singleton_algebraMap_units (A := A) (Bbar := Bbar) (uBar := uBar))).comp
      (localResidueFieldToMaximalIdealResidueField (A := A))

/-- Helper for Exercise 14-14.4-6: the lifted residue-field action on `A[uBar]` is compatible
with the original `A`-algebra structure. -/
lemma adjoin_singleton_residueFieldAlg_comp_toAlgHom
    {uBar : Bbar} :
    (adjoin_singleton_residueFieldAlg (A := A) (Bbar := Bbar) (uBar := uBar)).comp
        (IsScalarTower.toAlgHom A A (IsLocalRing.ResidueField A)) =
      Algebra.ofId A (Algebra.adjoin A ({uBar} : Set Bbar)) := by
  -- After composing back with `A → kA`, the intermediate maximal-ideal residue field disappears.
  rw [adjoin_singleton_residueFieldAlg, AlgHom.comp_assoc]
  calc
    (Ideal.ResidueField.liftₐ (IsLocalRing.maximalIdeal A)
        (Algebra.ofId A (Algebra.adjoin A ({uBar} : Set Bbar)))
        (adjoin_singleton_algebraMap_ker_le (A := A) (Bbar := Bbar) (uBar := uBar))
        (adjoin_singleton_algebraMap_units (A := A) (Bbar := Bbar) (uBar := uBar))).comp
          ((localResidueFieldToMaximalIdealResidueField (A := A)).comp
            (IsScalarTower.toAlgHom A A (IsLocalRing.ResidueField A))) =
      (Ideal.ResidueField.liftₐ (IsLocalRing.maximalIdeal A)
        (Algebra.ofId A (Algebra.adjoin A ({uBar} : Set Bbar)))
        (adjoin_singleton_algebraMap_ker_le (A := A) (Bbar := Bbar) (uBar := uBar))
        (adjoin_singleton_algebraMap_units (A := A) (Bbar := Bbar) (uBar := uBar))).comp
          (IsScalarTower.toAlgHom A A (IsLocalRing.maximalIdeal A).ResidueField) := by
            rw [localResidueFieldToMaximalIdealResidueField_comp_toAlgHom (A := A)]
    _ = Algebra.ofId A (Algebra.adjoin A ({uBar} : Set Bbar)) := by
          simpa using
            (Ideal.ResidueField.liftₐ_comp_toAlgHom (I := IsLocalRing.maximalIdeal A)
              (f := Algebra.ofId A (Algebra.adjoin A ({uBar} : Set Bbar)))
              (hf₁ := adjoin_singleton_algebraMap_ker_le
                (A := A) (Bbar := Bbar) (uBar := uBar))
              (hf₂ := adjoin_singleton_algebraMap_units
                (A := A) (Bbar := Bbar) (uBar := uBar)))

/-- Helper for Exercise 14-14.4-6: the residue-field algebra structure induced on `A[uBar]`. -/
noncomputable local instance adjoin_singleton_residueFieldAlgebra
    {uBar : Bbar} :
    Algebra (IsLocalRing.ResidueField A) (Algebra.adjoin A ({uBar} : Set Bbar)) :=
  RingHom.toAlgebra
    (adjoin_singleton_residueFieldAlg (A := A) (Bbar := Bbar) (uBar := uBar)).toRingHom

/-- Helper for Exercise 14-14.4-6: the induced residue-field action on `A[uBar]` is compatible
with the original `A`-algebra structure. -/
noncomputable local instance adjoin_singleton_residueFieldIsScalarTower
    {uBar : Bbar} :
    IsScalarTower A (IsLocalRing.ResidueField A) (Algebra.adjoin A ({uBar} : Set Bbar)) :=
  IsScalarTower.of_algebraMap_eq' <| by
    simpa using
      congrArg AlgHom.toRingHom
        (adjoin_singleton_residueFieldAlg_comp_toAlgHom
          (A := A) (Bbar := Bbar) (uBar := uBar)).symm

/-- Helper for Exercise 14-14.4-6: the ambient residue-field base-change comparison upgrades from
the linear equivalence in `IsBaseChange` to a `kA`-algebra equivalence. -/
noncomputable def residueField_baseChange_algEquiv
    (red : B →ₐ[A] Bbar)
    (hred : IsBaseChange (IsLocalRing.ResidueField A) red.toLinearMap) :
    (IsLocalRing.ResidueField A) ⊗[A] B ≃ₐ[IsLocalRing.ResidueField A] Bbar := by
  let eAlg :
      (IsLocalRing.ResidueField A) ⊗[A] B →ₐ[IsLocalRing.ResidueField A] Bbar :=
    Algebra.TensorProduct.lift
      (Algebra.ofId (IsLocalRing.ResidueField A) Bbar)
      red
      (fun x y ↦ by
        change Commute
          ((Algebra.ofId (IsLocalRing.ResidueField A) Bbar) x)
          (red y)
        exact Algebra.commutes _ _)
  have hfun : ∀ x, eAlg x = hred.equiv x := by
    -- Both maps out of the tensor product are characterized by their values on pure tensors.
    intro x
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp [eAlg]
    · intro s b
      simp [eAlg, IsBaseChange.equiv_tmul, Algebra.smul_def]
    · intro x y hx hy
      simp [hx, hy]
  refine AlgEquiv.ofBijective eAlg ⟨?_, ?_⟩
  · intro x y hxy
    apply hred.equiv.injective
    calc
      hred.equiv x = eAlg x := (hfun x).symm
      _ = eAlg y := hxy
      _ = hred.equiv y := hfun y
  · intro z
    obtain ⟨x, rfl⟩ := hred.equiv.surjective z
    exact ⟨x, hfun x⟩

/-- Helper for Exercise 14-14.4-6: under the ambient residue-field base-change equivalence, the
pure tensor of the chosen lift maps to the reduced singleton generator. -/
@[simp] lemma adjoin_singleton_ambient_baseChange_equiv_tmul_generator
    (red : B →ₐ[A] Bbar)
    (hred : IsBaseChange (IsLocalRing.ResidueField A) red.toLinearMap)
    {u0 : B} {uBar : Bbar} (hu0 : red u0 = uBar) :
    hred.equiv ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] u0) = uBar := by
  -- The ambient base-change equivalence evaluates `1 ⊗ u0` by applying the reduction map to `u0`.
  simpa [hu0] using hred.equiv_tmul (1 : IsLocalRing.ResidueField A) u0

/-- Helper for Exercise 14-14.4-6: the reduced singleton generator pulls back to the pure tensor
of the chosen lift under the ambient residue-field base-change equivalence. -/
@[simp] lemma adjoin_singleton_ambient_baseChange_equiv_symm_generator
    (red : B →ₐ[A] Bbar)
    (hred : IsBaseChange (IsLocalRing.ResidueField A) red.toLinearMap)
    {u0 : B} {uBar : Bbar} (hu0 : red u0 = uBar) :
    hred.equiv.symm uBar = (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] u0 := by
  -- Apply the explicit inverse formula for a base-change equivalence to the reduced point `uBar`.
  simpa [hu0] using hred.equiv_symm_apply u0

/-- Helper for Exercise 14-14.4-6: the ambient base-change equivalence sends an `A`-scalar in the
closed fiber back to the corresponding `kA`-scalar in the tensor product. -/
@[simp] lemma adjoin_singleton_ambient_baseChange_equiv_symm_algebraMap
    (red : B →ₐ[A] Bbar)
    (hred : IsBaseChange (IsLocalRing.ResidueField A) red.toLinearMap)
    (a : A) :
    hred.equiv.symm (algebraMap A Bbar a) =
      algebraMap (IsLocalRing.ResidueField A)
        ((IsLocalRing.ResidueField A) ⊗[A] B) (algebraMap A (IsLocalRing.ResidueField A) a) := by
  -- First identify the scalar downstairs with the reduction of the scalar upstairs.
  calc
    hred.equiv.symm (algebraMap A Bbar a) =
        (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (algebraMap A B a) := by
          simpa using hred.equiv_symm_apply (algebraMap A B a)
    _ =
        algebraMap A ((IsLocalRing.ResidueField A) ⊗[A] B) a := by
          -- Rewrite the pure tensor of a scalar as the ambient `A`-algebra map into the tensor product.
          simpa using
            (Algebra.TensorProduct.algebraMap_apply'
              (R := A) (A := IsLocalRing.ResidueField A) (B := B) a).symm
    _ =
        algebraMap (IsLocalRing.ResidueField A)
          ((IsLocalRing.ResidueField A) ⊗[A] B) (algebraMap A (IsLocalRing.ResidueField A) a) := by
          rfl

/-- Helper for Exercise 14-14.4-6: every element of the reduced singleton-adjoin algebra pulls
back under the ambient base-change equivalence to the tensor singleton-adjoin generated by
`1 ⊗ u0`. -/
lemma adjoin_singleton_ambient_baseChange_equiv_symm_mem_adjoin
    (red : B →ₐ[A] Bbar)
    (hred : IsBaseChange (IsLocalRing.ResidueField A) red.toLinearMap)
    {u0 : B} {uBar : Bbar} (hu0 : red u0 = uBar)
    (x : Algebra.adjoin A ({uBar} : Set Bbar)) :
    hred.equiv.symm x ∈
      Algebra.adjoin (IsLocalRing.ResidueField A)
        ({((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] u0)} :
          Set ((IsLocalRing.ResidueField A) ⊗[A] B)) := by
  -- Route correction: the source proof only needs a singleton-adjoin induction, not a new
  -- quotient presentation. We induct on the fact that `x` lies in `A[uBar]`.
  induction x.property using Algebra.adjoin_induction with
  | mem y hy =>
      rw [Set.mem_singleton_iff] at hy
      subst y
      simpa using
        (Algebra.subset_adjoin
          (x := (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] u0)
          (by simp : ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] u0) ∈
            ({((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] u0)} :
              Set ((IsLocalRing.ResidueField A) ⊗[A] B))))
  | algebraMap a =>
      -- Scalars come from the residue-field algebra map after transporting along the tower.
      simpa [adjoin_singleton_ambient_baseChange_equiv_symm_algebraMap]
        using
          (Subalgebra.algebraMap_mem
            (Algebra.adjoin (IsLocalRing.ResidueField A)
              ({((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] u0)} :
                Set ((IsLocalRing.ResidueField A) ⊗[A] B)))
            (algebraMap A (IsLocalRing.ResidueField A) a))
  | add y z hy hz hy_mem hz_mem =>
      exact Subalgebra.add_mem _ hy_mem hz_mem
  | mul y z hy hz hy_mem hz_mem =>
      exact Subalgebra.mul_mem _ hy_mem hz_mem

/-- Helper for Exercise 14-14.4-6: after restricting scalars to the residue field, every element
of `A[uBar]` still lies in the `kA`-subalgebra generated by the same canonical point. -/
/-- Helper for Exercise 14-14.4-6: viewed as an `A`-algebra, `A[u0]` is generated by its
canonical singleton generator. -/
lemma adjoin_singleton_source_generator_eq_top
    {u0 : B} :
    Algebra.adjoin A
      ({(⟨u0, Algebra.self_mem_adjoin_singleton A u0⟩ :
          Algebra.adjoin A ({u0} : Set B))} :
        Set (Algebra.adjoin A ({u0} : Set B))) = ⊤ := by
  let S := Algebra.adjoin A ({u0} : Set B)
  let a0 : S := ⟨u0, Algebra.self_mem_adjoin_singleton A u0⟩
  -- The ambient singleton adjoin `A[u0] ⊆ B` is the range of polynomial evaluation at `u0`,
  -- and the same polynomial evaluated at the canonical point `a0` recovers every element of `S`.
  rw [← AlgHom.range_eq_top, ← Algebra.adjoin_singleton_eq_range_aeval]
  intro x
  rw [AlgHom.mem_range]
  have hxRange :
      (x : B) ∈
        AlgHom.range
          (Polynomial.aeval u0 : Polynomial A →ₐ[A] B) := by
    rw [← Algebra.adjoin_singleton_eq_range_aeval]
    exact x.property
  obtain ⟨p, hp⟩ := hxRange
  refine ⟨p, ?_⟩
  apply Subtype.ext
  simpa [S, a0] using hp

/-- Helper for Exercise 14-14.4-6: after restricting scalars to the residue field, every element
of `A[uBar]` still lies in the `kA`-subalgebra generated by the same canonical point. -/
lemma adjoin_singleton_target_mem_residueField_adjoin
    {uBar : Bbar}
    (x : Algebra.adjoin A ({uBar} : Set Bbar)) :
    x ∈
      Algebra.adjoin (IsLocalRing.ResidueField A)
        ({(⟨uBar, Algebra.self_mem_adjoin_singleton A uBar⟩ :
            Algebra.adjoin A ({uBar} : Set Bbar))} :
          Set (Algebra.adjoin A ({uBar} : Set Bbar))) := by
  let Sbar := Algebra.adjoin A ({uBar} : Set Bbar)
  let uBar0 : Sbar := ⟨uBar, Algebra.self_mem_adjoin_singleton A uBar⟩
  have hA :
      Algebra.adjoin A ({uBar0} : Set Sbar) = ⊤ := by
    simpa [Sbar, uBar0] using
      adjoin_singleton_source_generator_eq_top (A := A) (B := Bbar) (u0 := uBar)
  have htop :
      Algebra.adjoin (IsLocalRing.ResidueField A) ({uBar0} : Set Sbar) = ⊤ := by
    calc
      Algebra.adjoin (IsLocalRing.ResidueField A) ({uBar0} : Set Sbar) =
          Algebra.adjoin (IsLocalRing.ResidueField A)
            (Algebra.adjoin A ({uBar0} : Set Sbar) : Set Sbar) := by
              rw [Algebra.adjoin_adjoin_of_tower]
      _ = ⊤ := by
            simpa [hA]
  -- Once the residue-field singleton generator is known to generate the whole reduced algebra,
  -- every element belongs to that adjoin automatically.
  simpa [Sbar, uBar0, htop] using
    (show x ∈ (⊤ : Subalgebra (IsLocalRing.ResidueField A) Sbar) from trivial)

/-- Helper for Exercise 14-14.4-6: viewed as a residue-field algebra, the reduced singleton-adjoin
is generated by its canonical singleton generator. -/
lemma adjoin_singleton_target_generator_eq_top
    {uBar : Bbar} :
    Algebra.adjoin (IsLocalRing.ResidueField A)
      ({(⟨uBar, Algebra.self_mem_adjoin_singleton A uBar⟩ :
          Algebra.adjoin A ({uBar} : Set Bbar))} :
        Set (Algebra.adjoin A ({uBar} : Set Bbar))) = ⊤ := by
  let Sbar := Algebra.adjoin A ({uBar} : Set Bbar)
  let uBar0 : Sbar := ⟨uBar, Algebra.self_mem_adjoin_singleton A uBar⟩
  have hA :
      Algebra.adjoin A ({uBar0} : Set Sbar) = ⊤ := by
    simpa [Sbar, uBar0] using
      adjoin_singleton_source_generator_eq_top (A := A) (B := Bbar) (u0 := uBar)
  -- Adjoining the same generator after restricting scalars to the residue field still gives all
  -- of `A[uBar]`.
  calc
    Algebra.adjoin (IsLocalRing.ResidueField A) ({uBar0} : Set Sbar) =
        Algebra.adjoin (IsLocalRing.ResidueField A)
          (Algebra.adjoin A ({uBar0} : Set Sbar) : Set Sbar) := by
            rw [Algebra.adjoin_adjoin_of_tower]
    _ = ⊤ := by
          simpa [hA]

/-- Helper for Exercise 14-14.4-6: polynomial evaluation at the canonical generator of `A[u0]`
is surjective. -/
lemma adjoin_singleton_source_aeval_surjective
    {u0 : B} :
    let a0 : Algebra.adjoin A ({u0} : Set B) := ⟨u0, Algebra.self_mem_adjoin_singleton A u0⟩
    Function.Surjective
      (Polynomial.aeval a0 :
        Polynomial A →ₐ[A] Algebra.adjoin A ({u0} : Set B)) := by
  dsimp
  -- Evaluation onto the range of the singleton generator becomes surjective once that range is
  -- all of `A[u0]`.
  refine (AlgHom.range_eq_top _).mp ?_
  exact
    (Algebra.adjoin_singleton_eq_range_aeval
      A
      (⟨u0, Algebra.self_mem_adjoin_singleton A u0⟩ :
        Algebra.adjoin A ({u0} : Set B))).symm.trans
      (adjoin_singleton_source_generator_eq_top
        (A := A) (B := B) (u0 := u0))

/-- Helper for Exercise 14-14.4-6: after base change to the residue field, `kA ⊗[A] A[u0]` is
generated by the pure tensor of the canonical singleton generator. -/
lemma adjoin_singleton_source_tensor_generator_eq_top
    {u0 : B} :
    let a0 : Algebra.adjoin A ({u0} : Set B) := ⟨u0, Algebra.self_mem_adjoin_singleton A u0⟩
    Algebra.adjoin (IsLocalRing.ResidueField A)
      ({((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] a0)} :
        Set ((IsLocalRing.ResidueField A) ⊗[A] Algebra.adjoin A ({u0} : Set B))) = ⊤ := by
  dsimp
  -- Tensoring with the residue field preserves singleton generation by the canonical point.
  simpa [Set.image_singleton] using
    TensorProduct.adjoin_one_tmul_image_eq_top
      (R := A)
      (A := IsLocalRing.ResidueField A)
      (B := Algebra.adjoin A ({u0} : Set B))
      ({(⟨u0, Algebra.self_mem_adjoin_singleton A u0⟩ :
          Algebra.adjoin A ({u0} : Set B))} :
        Set (Algebra.adjoin A ({u0} : Set B)))
      (adjoin_singleton_source_generator_eq_top (A := A) (B := B) (u0 := u0))

/-- Helper for Exercise 14-14.4-6: polynomial evaluation at the pure tensor generator of
`kA ⊗[A] A[u0]` is surjective. -/
lemma adjoin_singleton_source_tensor_aeval_surjective
    {u0 : B} :
    let a0 : Algebra.adjoin A ({u0} : Set B) := ⟨u0, Algebra.self_mem_adjoin_singleton A u0⟩
    Function.Surjective
      (Polynomial.aeval
        ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] a0) :
          Polynomial (IsLocalRing.ResidueField A) →ₐ[IsLocalRing.ResidueField A]
            ((IsLocalRing.ResidueField A) ⊗[A] Algebra.adjoin A ({u0} : Set B))) := by
  dsimp
  -- The tensor-model source is also singleton-generated, so evaluation at that generator is onto.
  refine (AlgHom.range_eq_top _).mp ?_
  exact
    (Algebra.adjoin_singleton_eq_range_aeval
      (IsLocalRing.ResidueField A)
      ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
        (⟨u0, Algebra.self_mem_adjoin_singleton A u0⟩ :
          Algebra.adjoin A ({u0} : Set B)))).symm.trans
      (adjoin_singleton_source_tensor_generator_eq_top
        (A := A) (B := B) (u0 := u0))

/-- Helper for Exercise 14-14.4-6: the source-side fiber comparison for the canonical generator
of `A[u0]` identifies the mapped evaluation kernel with the tensor-side evaluation kernel. -/
lemma adjoin_singleton_source_fiber_aeval_kernel_map_eq
    {u0 : B} :
    let a0 : Algebra.adjoin A ({u0} : Set B) := ⟨u0, Algebra.self_mem_adjoin_singleton A u0⟩
    Ideal.map (Polynomial.mapRingHom (algebraMap A (IsLocalRing.ResidueField A)))
      (RingHom.ker
        (Polynomial.aeval a0 :
          Polynomial A →ₐ[A] Algebra.adjoin A ({u0} : Set B)).toRingHom) =
      RingHom.ker
        (Polynomial.aeval
          ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] a0) :
            Polynomial (IsLocalRing.ResidueField A) →ₐ[IsLocalRing.ResidueField A]
              ((IsLocalRing.ResidueField A) ⊗[A] Algebra.adjoin A ({u0} : Set B))).toRingHom := by
  dsimp
  letI : CommRing (Algebra.adjoin A ({u0} : Set B)) :=
    inferInstanceAs (CommRing (Algebra.adjoin A ({u0} : Set B)))
  have hsurj :
      Function.Surjective
        (Polynomial.aeval
          (⟨u0, Algebra.self_mem_adjoin_singleton A u0⟩ :
            Algebra.adjoin A ({u0} : Set B)) :
          Polynomial A →ₐ[A] Algebra.adjoin A ({u0} : Set B)) :=
    adjoin_singleton_source_aeval_surjective (A := A) (B := B) (u0 := u0)
  let I : Ideal (Polynomial A) :=
    RingHom.ker
      (Polynomial.aeval
        (⟨u0, Algebra.self_mem_adjoin_singleton A u0⟩ :
          Algebra.adjoin A ({u0} : Set B)) :
        Polynomial A →ₐ[A] Algebra.adjoin A ({u0} : Set B)).toRingHom
  let e :
      (IsLocalRing.maximalIdeal A).Fiber (Algebra.adjoin A ({u0} : Set B)) ≃ₐ[kA]
        kA[X] ⧸ I.map (Polynomial.mapRingHom (algebraMap A kA)) :=
    Polynomial.fiberEquivQuotient
      (Polynomial.aeval
        (⟨u0, Algebra.self_mem_adjoin_singleton A u0⟩ :
          Algebra.adjoin A ({u0} : Set B)))
      hsurj (IsLocalRing.maximalIdeal A)
  -- This is the source-fiber comparison from mathlib's local-structure proof, specialized to the
  -- monogenic algebra `A[u0]`.
  rw [← RingHom.ker_comp_of_injective _ (f := e.toRingHom) e.injective]
  convert Ideal.mk_ker.symm
  ext p
  · dsimp [-TensorProduct.algebraMap_apply]
    -- Constants are preserved by the quotient-model fiber equivalence.
    rw [Polynomial.aeval_C, AlgEquiv.commutes]
    simp [← Ideal.Quotient.mk_algebraMap, I]
  · -- The distinguished tensor generator corresponds to the class of `X`.
    simpa [e] using
      Polynomial.fiberEquivQuotient_tmul
        (Polynomial.aeval
          (⟨u0, Algebra.self_mem_adjoin_singleton A u0⟩ :
            Algebra.adjoin A ({u0} : Set B)))
        hsurj (IsLocalRing.maximalIdeal A) 1 Polynomial.X

/-- Helper for Exercise 14-14.4-6: polynomial evaluation at the reduced singleton generator is
surjective over the residue field. -/
lemma adjoin_singleton_target_aeval_surjective
    {uBar : Bbar} :
    let uBar0 : Algebra.adjoin A ({uBar} : Set Bbar) :=
      ⟨uBar, Algebra.self_mem_adjoin_singleton A uBar⟩
    Function.Surjective
      (Polynomial.aeval uBar0 :
        Polynomial (IsLocalRing.ResidueField A) →ₐ[IsLocalRing.ResidueField A]
          Algebra.adjoin A ({uBar} : Set Bbar)) := by
  dsimp
  -- The reduced singleton-adjoin is generated by `uBar0` as a `kA`-algebra, so evaluation is onto.
  refine (AlgHom.range_eq_top _).mp ?_
  exact
    (Algebra.adjoin_singleton_eq_range_aeval
      (IsLocalRing.ResidueField A)
      (⟨uBar, Algebra.self_mem_adjoin_singleton A uBar⟩ :
        Algebra.adjoin A ({uBar} : Set Bbar))).symm.trans
      (adjoin_singleton_target_generator_eq_top
        (A := A) (Bbar := Bbar) (uBar := uBar))

/-- Helper for Exercise 14-14.4-6: if a polynomial in `A[X]` evaluates into the maximal-ideal
fiber of `A[u0]`, then its residue-field reduction lies in the mapped source evaluation kernel. -/
lemma adjoin_singleton_map_source_kernel_of_eval_mem_map_maximalIdeal
    {u0 : B} :
    let a0 : Algebra.adjoin A ({u0} : Set B) := ⟨u0, Algebra.self_mem_adjoin_singleton A u0⟩
    ∀ {q : Polynomial A},
      Polynomial.aeval a0 q ∈
          ((IsLocalRing.maximalIdeal A).map
            (algebraMap A (Algebra.adjoin A ({u0} : Set B)))) →
        q.map (algebraMap A (IsLocalRing.ResidueField A)) ∈
          Ideal.map (Polynomial.mapRingHom (algebraMap A (IsLocalRing.ResidueField A)))
            (RingHom.ker (Polynomial.aeval a0).toRingHom) := by
  dsimp
  intro q hq
  let S : Type _ := Algebra.adjoin A ({u0} : Set B)
  let a0 : S := ⟨u0, Algebra.self_mem_adjoin_singleton A u0⟩
  let I : Ideal (Polynomial A) :=
    RingHom.ker (Polynomial.aeval a0 : Polynomial A →ₐ[A] S).toRingHom
  letI : CommRing S := inferInstanceAs (CommRing S)
  let eQuot :
      S ⧸ ((IsLocalRing.maximalIdeal A).map (algebraMap A S)) ≃ₐ[IsLocalRing.ResidueField A]
        (IsLocalRing.ResidueField A) ⊗[A] S :=
    Algebra.TensorProduct.quotIdealMapEquivQuotTensor S (IsLocalRing.maximalIdeal A)
  have hzero_tensor :
      (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (Polynomial.aeval a0 q : S) = 0 := by
    -- Passing to the quotient model of the closed fiber turns membership in `𝔪_A S` into
    -- vanishing of the corresponding pure tensor.
    have hq0 :
        Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A).map (algebraMap A S))
          (Polynomial.aeval a0 q : S) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hq
    simpa [eQuot] using congrArg eQuot hq0
  -- Rewrite the mapped source kernel as the tensor-side evaluation kernel, then show the
  -- reduced polynomial vanishes at the pure tensor generator.
  rw [adjoin_singleton_source_fiber_aeval_kernel_map_eq (A := A) (B := B) (u0 := u0)]
  rw [RingHom.mem_ker]
  let ψ : S →+* (IsLocalRing.ResidueField A) ⊗[A] S :=
    (Algebra.TensorProduct.includeRight :
      S →ₐ[A] (IsLocalRing.ResidueField A) ⊗[A] S).toRingHom
  have hψ :
      ψ (Polynomial.aeval a0 q) =
        Polynomial.aeval
          ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] a0)
          (q.map (algebraMap A (IsLocalRing.ResidueField A))) := by
    -- Evaluation commutes with the canonical map into the tensor-model closed fiber.
    have hcomm :
        (algebraMap (IsLocalRing.ResidueField A)
            ((IsLocalRing.ResidueField A) ⊗[A] S)).comp
            (algebraMap A (IsLocalRing.ResidueField A)) =
          ψ.comp (algebraMap A S) := by
      ext a
      simp [ψ]
    simpa [ψ] using
      (Polynomial.map_aeval_eq_aeval_map
        (R := A) (S := S) (T := IsLocalRing.ResidueField A)
        (U := (IsLocalRing.ResidueField A) ⊗[A] S)
        (φ := algebraMap A (IsLocalRing.ResidueField A)) (ψ := ψ) hcomm q a0)
  rw [← hψ]
  simpa [ψ] using hzero_tensor

/-- Helper for Exercise 14-14.4-6: the forward tensor map for the restricted singleton-adjoin
reduction sends `1 ⊗ a0` to the reduced generator and has full range. -/
lemma adjoin_singleton_forward_tensor_image_eq_top
    (red : B →ₐ[A] Bbar)
    {u0 : B} {uBar : Bbar} (hu0 : red u0 = uBar) :
    let redS := adjoin_singleton_codRestrict (A := A) (B := B) (Bbar := Bbar) red hu0
    let a0 : Algebra.adjoin A ({u0} : Set B) := ⟨u0, Algebra.self_mem_adjoin_singleton A u0⟩
    let uBar0 : Algebra.adjoin A ({uBar} : Set Bbar) :=
      ⟨uBar, Algebra.self_mem_adjoin_singleton A uBar⟩
    let fwd :
        (IsLocalRing.ResidueField A) ⊗[A] Algebra.adjoin A ({u0} : Set B) →ₗ[
          IsLocalRing.ResidueField A] Algebra.adjoin A ({uBar} : Set Bbar) :=
      LinearMap.liftBaseChange
        (A := IsLocalRing.ResidueField A) redS.toLinearMap
    fwd ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] a0) = uBar0 ∧ LinearMap.range fwd = ⊤ := by
  let redS := adjoin_singleton_codRestrict (A := A) (B := B) (Bbar := Bbar) red hu0
  let a0 : Algebra.adjoin A ({u0} : Set B) := ⟨u0, Algebra.self_mem_adjoin_singleton A u0⟩
  let uBar0 : Algebra.adjoin A ({uBar} : Set Bbar) :=
    ⟨uBar, Algebra.self_mem_adjoin_singleton A uBar⟩
  let fwd :
      (IsLocalRing.ResidueField A) ⊗[A] Algebra.adjoin A ({u0} : Set B) →ₗ[
        IsLocalRing.ResidueField A] Algebra.adjoin A ({uBar} : Set Bbar) :=
    LinearMap.liftBaseChange
      (A := IsLocalRing.ResidueField A) redS.toLinearMap
  refine ⟨?_, ?_⟩
  · -- The forward tensor map carries the chosen pure tensor generator to the reduced generator.
    calc
      fwd ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] a0) = redS a0 := by
        simp [fwd]
      _ = uBar0 := by
        apply Subtype.ext
        simpa [redS, a0, uBar0] using
          adjoin_singleton_codRestrict_apply
            (A := A) (B := B) (Bbar := Bbar) red hu0 a0
  · -- Since the restricted reduction is already surjective, its lifted base-change map has full range.
    have hsurj : Function.Surjective redS := by
      simpa [redS] using
        adjoin_singleton_codRestrict_surjective
          (A := A) (B := B) (Bbar := Bbar) red hu0
    have hrange : LinearMap.range redS.toLinearMap = ⊤ :=
      LinearMap.range_eq_top.2 hsurj
    simpa [fwd, hrange] using
      (LinearMap.range_liftBaseChange
        (A := IsLocalRing.ResidueField A) redS.toLinearMap)

-- The forward tensor-product algebra map is the concrete comparison morphism used in the
-- singleton-adjoin base-change model.
/-- Helper for Exercise 14-14.4-6: the codrestricted reduction induces the canonical forward
tensor-product algebra map from the source singleton-adjoin to the target singleton-adjoin. -/
noncomputable def adjoin_singleton_forward_tensor_algHom
    (red : B →ₐ[A] Bbar)
    {u0 : B} {uBar : Bbar} (hu0 : red u0 = uBar) :
    (IsLocalRing.ResidueField A) ⊗[A] Algebra.adjoin A ({u0} : Set B) →ₐ[IsLocalRing.ResidueField A]
      Algebra.adjoin A ({uBar} : Set Bbar) :=
  Algebra.TensorProduct.lift
    (Algebra.ofId (IsLocalRing.ResidueField A) (Algebra.adjoin A ({uBar} : Set Bbar)))
    (adjoin_singleton_codRestrict (A := A) (B := B) (Bbar := Bbar) red hu0)
    (fun x y ↦ by
      change Commute
        ((Algebra.ofId (IsLocalRing.ResidueField A) (Algebra.adjoin A ({uBar} : Set Bbar))) x)
        ((adjoin_singleton_codRestrict (A := A) (B := B) (Bbar := Bbar) red hu0) y)
      exact Commute.all
        ((Algebra.ofId (IsLocalRing.ResidueField A) (Algebra.adjoin A ({uBar} : Set Bbar))) x)
        ((adjoin_singleton_codRestrict (A := A) (B := B) (Bbar := Bbar) red hu0) y))

/-- Helper for Exercise 14-14.4-6: the forward tensor-product algebra map sends the pure tensor of
the source singleton generator to the reduced singleton generator. -/
@[simp] lemma adjoin_singleton_forward_tensor_algHom_tmul_generator
    (red : B →ₐ[A] Bbar)
    {u0 : B} {uBar : Bbar} (hu0 : red u0 = uBar) :
    let a0 : Algebra.adjoin A ({u0} : Set B) := ⟨u0, Algebra.self_mem_adjoin_singleton A u0⟩
    let uBar0 : Algebra.adjoin A ({uBar} : Set Bbar) :=
      ⟨uBar, Algebra.self_mem_adjoin_singleton A uBar⟩
    adjoin_singleton_forward_tensor_algHom (A := A) (B := B) (Bbar := Bbar) red hu0
        ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] a0) = uBar0 := by
  dsimp [adjoin_singleton_forward_tensor_algHom]
  -- The universal tensor-product map acts on `1 ⊗ a0` by applying the codrestricted reduction.
  apply Subtype.ext
  simp [adjoin_singleton_codRestrict_apply, hu0]

/-- Helper for Exercise 14-14.4-6: polynomial evaluation at the source tensor generator is
transported by the forward tensor-product algebra map to evaluation at the reduced generator. -/
lemma adjoin_singleton_forward_tensor_algHom_aeval
    (red : B →ₐ[A] Bbar)
    {u0 : B} {uBar : Bbar} (hu0 : red u0 = uBar) :
    let a0 : Algebra.adjoin A ({u0} : Set B) := ⟨u0, Algebra.self_mem_adjoin_singleton A u0⟩
    let uBar0 : Algebra.adjoin A ({uBar} : Set Bbar) :=
      ⟨uBar, Algebra.self_mem_adjoin_singleton A uBar⟩
    ∀ p : Polynomial (IsLocalRing.ResidueField A),
      adjoin_singleton_forward_tensor_algHom (A := A) (B := B) (Bbar := Bbar) red hu0
          (Polynomial.aeval ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] a0) p) =
        Polynomial.aeval uBar0 p := by
  dsimp
  intro p
  let fwd :=
    adjoin_singleton_forward_tensor_algHom (A := A) (B := B) (Bbar := Bbar) red hu0
  have hcomm :
      (algebraMap (IsLocalRing.ResidueField A) (Algebra.adjoin A ({uBar} : Set Bbar))).comp
          (RingHom.id (IsLocalRing.ResidueField A)) =
        fwd.toRingHom.comp
          (algebraMap (IsLocalRing.ResidueField A)
            ((IsLocalRing.ResidueField A) ⊗[A] Algebra.adjoin A ({u0} : Set B))) := by
    -- This is exactly the scalar-compatibility of the tensor-product algebra map.
    ext c
    simp [fwd]
  -- Apply the standard `map_aeval_eq_aeval_map` transport along the forward algebra map.
  calc
    fwd (Polynomial.aeval ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
        (⟨u0, Algebra.self_mem_adjoin_singleton A u0⟩ :
          Algebra.adjoin A ({u0} : Set B))) p) =
      Polynomial.aeval
        (fwd ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
          (⟨u0, Algebra.self_mem_adjoin_singleton A u0⟩ :
            Algebra.adjoin A ({u0} : Set B))))
        (p.map (RingHom.id (IsLocalRing.ResidueField A))) := by
          simpa [fwd] using
            (Polynomial.map_aeval_eq_aeval_map
              (R := IsLocalRing.ResidueField A)
              (S := (IsLocalRing.ResidueField A) ⊗[A] Algebra.adjoin A ({u0} : Set B))
              (T := IsLocalRing.ResidueField A)
              (U := Algebra.adjoin A ({uBar} : Set Bbar))
              (φ := RingHom.id (IsLocalRing.ResidueField A))
              (ψ := fwd.toRingHom)
              hcomm
              p
              ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
                (⟨u0, Algebra.self_mem_adjoin_singleton A u0⟩ :
                  Algebra.adjoin A ({u0} : Set B))))
    _ = Polynomial.aeval
        (fwd ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
          (⟨u0, Algebra.self_mem_adjoin_singleton A u0⟩ :
            Algebra.adjoin A ({u0} : Set B)))) p := by
          simp
    _ = Polynomial.aeval
        (⟨uBar, Algebra.self_mem_adjoin_singleton A uBar⟩ :
          Algebra.adjoin A ({uBar} : Set Bbar)) p := by
          rw [adjoin_singleton_forward_tensor_algHom_tmul_generator
            (A := A) (B := B) (Bbar := Bbar) red hu0]

/-- Helper for Exercise 14-14.4-6: every polynomial relation in the tensor-model source also holds
in the reduced singleton-adjoin target after applying the forward tensor-product algebra map. -/
lemma adjoin_singleton_source_tensor_eval_kernel_le_target_eval_kernel
    (red : B →ₐ[A] Bbar)
    {u0 : B} {uBar : Bbar} (hu0 : red u0 = uBar) :
    let a0 : Algebra.adjoin A ({u0} : Set B) := ⟨u0, Algebra.self_mem_adjoin_singleton A u0⟩
    let uBar0 : Algebra.adjoin A ({uBar} : Set Bbar) :=
      ⟨uBar, Algebra.self_mem_adjoin_singleton A uBar⟩
    RingHom.ker
        (Polynomial.aeval ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] a0) :
          Polynomial (IsLocalRing.ResidueField A) →ₐ[IsLocalRing.ResidueField A]
            ((IsLocalRing.ResidueField A) ⊗[A] Algebra.adjoin A ({u0} : Set B))).toRingHom ≤
      RingHom.ker
        (Polynomial.aeval uBar0 :
          Polynomial (IsLocalRing.ResidueField A) →ₐ[IsLocalRing.ResidueField A]
            Algebra.adjoin A ({uBar} : Set Bbar)).toRingHom := by
  dsimp
  intro p hp
  rw [RingHom.mem_ker] at hp ⊢
  -- Push the tensor-side relation forward and rewrite it as the target-side evaluation.
  rw [← adjoin_singleton_forward_tensor_algHom_aeval
    (A := A) (B := B) (Bbar := Bbar) red hu0 p]
  simpa using congrArg
    (adjoin_singleton_forward_tensor_algHom (A := A) (B := B) (Bbar := Bbar) red hu0) hp

/-- Helper for Exercise 14-14.4-6: every polynomial relation in the reduced singleton-adjoin
target already comes from the tensor-model source after lifting coefficients back to `A` and
testing the resulting source evaluation modulo `𝔪_A`. -/
lemma adjoin_singleton_target_eval_kernel_le_source_tensor_eval_kernel
    (red : B →ₐ[A] Bbar)
    (hred : IsBaseChange (IsLocalRing.ResidueField A) red.toLinearMap)
    {u0 : B} {uBar : Bbar} (hu0 : red u0 = uBar) :
    let a0 : Algebra.adjoin A ({u0} : Set B) := ⟨u0, Algebra.self_mem_adjoin_singleton A u0⟩
    let uBar0 : Algebra.adjoin A ({uBar} : Set Bbar) :=
      ⟨uBar, Algebra.self_mem_adjoin_singleton A uBar⟩
    RingHom.ker
        (Polynomial.aeval uBar0 :
          Polynomial (IsLocalRing.ResidueField A) →ₐ[IsLocalRing.ResidueField A]
            Algebra.adjoin A ({uBar} : Set Bbar)).toRingHom ≤
      RingHom.ker
        (Polynomial.aeval ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] a0) :
          Polynomial (IsLocalRing.ResidueField A) →ₐ[IsLocalRing.ResidueField A]
            ((IsLocalRing.ResidueField A) ⊗[A] Algebra.adjoin A ({u0} : Set B))).toRingHom := by
  dsimp
  intro p hp
  -- Lift the residue-field polynomial relation back to a polynomial over `A`.
  obtain ⟨q, rfl⟩ :=
    Polynomial.map_surjective
      (f := algebraMap A (IsLocalRing.ResidueField A))
      (show Function.Surjective (algebraMap A (IsLocalRing.ResidueField A)) from
        IsLocalRing.residue_surjective (R := A))
      p
  let redS := adjoin_singleton_codRestrict (A := A) (B := B) (Bbar := Bbar) red hu0
  let a0 : Algebra.adjoin A ({u0} : Set B) := ⟨u0, Algebra.self_mem_adjoin_singleton A u0⟩
  let uBar0 : Algebra.adjoin A ({uBar} : Set Bbar) :=
    ⟨uBar, Algebra.self_mem_adjoin_singleton A uBar⟩
  have hEval_transport :
      redS (Polynomial.aeval a0 q) =
        Polynomial.aeval uBar0 (q.map (algebraMap A (IsLocalRing.ResidueField A))) := by
    -- Evaluating first in `A[u0]` and then reducing is the same as first reducing coefficients
    -- and then evaluating at the reduced generator.
    have hcomm :
        (algebraMap (IsLocalRing.ResidueField A)
            (Algebra.adjoin A ({uBar} : Set Bbar))).comp
            (algebraMap A (IsLocalRing.ResidueField A)) =
          redS.toRingHom.comp (algebraMap A (Algebra.adjoin A ({u0} : Set B))) := by
      ext a
      simp [redS, IsScalarTower.algebraMap_apply A (IsLocalRing.ResidueField A)
        (Algebra.adjoin A ({uBar} : Set Bbar))]
    simpa [redS] using
      (Polynomial.map_aeval_eq_aeval_map
        (R := A)
        (S := Algebra.adjoin A ({u0} : Set B))
        (T := IsLocalRing.ResidueField A)
        (U := Algebra.adjoin A ({uBar} : Set Bbar))
        (φ := algebraMap A (IsLocalRing.ResidueField A))
        (ψ := redS.toRingHom)
        hcomm
        q
        a0)
  have hEval_mem_map :
      Polynomial.aeval a0 q ∈
        (IsLocalRing.maximalIdeal A).map
          (algebraMap A (Algebra.adjoin A ({u0} : Set B))) := by
    -- The lifted source evaluation reduces to zero, so it lies in the kernel of the restricted
    -- reduction; the closed-fiber base-change comparison identifies that kernel with `𝔪_A A[u0]`.
    rw [← adjoin_singleton_codRestrict_ker_eq_map_maximalIdeal
      (A := A) (B := B) (Bbar := Bbar) red hred hu0]
    rw [RingHom.mem_ker]
    rw [hEval_transport]
    exact hp
  have hMapKernel :
      q.map (algebraMap A (IsLocalRing.ResidueField A)) ∈
        Ideal.map (Polynomial.mapRingHom (algebraMap A (IsLocalRing.ResidueField A)))
          (RingHom.ker (Polynomial.aeval a0).toRingHom) :=
    adjoin_singleton_map_source_kernel_of_eval_mem_map_maximalIdeal
      (A := A) (B := B) (u0 := u0) hEval_mem_map
  -- Rewrite the source fiber presentation back to the tensor-model evaluation kernel.
  rw [adjoin_singleton_source_fiber_aeval_kernel_map_eq (A := A) (B := B) (u0 := u0)] at hMapKernel
  exact hMapKernel

/-- Helper for Exercise 14-14.4-6: the reduced singleton-adjoin and the tensor-model source
singleton-adjoin are quotient presentations of `kA[X]` by the same evaluation kernel. -/
lemma adjoin_singleton_target_eval_kernel_eq_source_tensor_eval_kernel
    (red : B →ₐ[A] Bbar)
    (hred : IsBaseChange (IsLocalRing.ResidueField A) red.toLinearMap)
    {u0 : B} {uBar : Bbar} (hu0 : red u0 = uBar) :
    let a0 : Algebra.adjoin A ({u0} : Set B) := ⟨u0, Algebra.self_mem_adjoin_singleton A u0⟩
    let uBar0 : Algebra.adjoin A ({uBar} : Set Bbar) :=
      ⟨uBar, Algebra.self_mem_adjoin_singleton A uBar⟩
    RingHom.ker
        (Polynomial.aeval uBar0 :
          Polynomial (IsLocalRing.ResidueField A) →ₐ[IsLocalRing.ResidueField A]
            Algebra.adjoin A ({uBar} : Set Bbar)).toRingHom =
      RingHom.ker
        (Polynomial.aeval ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] a0) :
          Polynomial (IsLocalRing.ResidueField A) →ₐ[IsLocalRing.ResidueField A]
            ((IsLocalRing.ResidueField A) ⊗[A] Algebra.adjoin A ({u0} : Set B))).toRingHom := by
  refine le_antisymm ?_ ?_
  · -- Lift a target relation back to `A[X]`, detect its source evaluation modulo `𝔪_A`,
    -- and then return to the tensor-model evaluation kernel.
    exact adjoin_singleton_target_eval_kernel_le_source_tensor_eval_kernel
      (A := A) (B := B) (Bbar := Bbar) red hred hu0
  · -- The easy direction comes from the explicit forward tensor-product algebra map.
    exact adjoin_singleton_source_tensor_eval_kernel_le_target_eval_kernel
      (A := A) (B := B) (Bbar := Bbar) red hu0

/-- Helper for Exercise 14-14.4-6: the restricted singleton-adjoin reduction should admit the
residue-field base-change linear equivalence compatible with pure tensors. -/
lemma adjoin_singleton_codRestrict_baseChange_equiv_exists
    (red : B →ₐ[A] Bbar)
    (hred : IsBaseChange (IsLocalRing.ResidueField A) red.toLinearMap)
    {u0 : B} {uBar : Bbar} (hu0 : red u0 = uBar) :
    ∃ e :
        (IsLocalRing.ResidueField A) ⊗[A] Algebra.adjoin A ({u0} : Set B) ≃ₗ[
          IsLocalRing.ResidueField A] Algebra.adjoin A ({uBar} : Set Bbar),
      ∀ x : Algebra.adjoin A ({u0} : Set B),
        e ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] x) =
          adjoin_singleton_codRestrict (A := A) (B := B) (Bbar := Bbar) red hu0 x := by
  let a0 : Algebra.adjoin A ({u0} : Set B) := ⟨u0, Algebra.self_mem_adjoin_singleton A u0⟩
  let uBar0 : Algebra.adjoin A ({uBar} : Set Bbar) :=
    ⟨uBar, Algebra.self_mem_adjoin_singleton A uBar⟩
  let eSource :
      Polynomial (IsLocalRing.ResidueField A) ⧸
          RingHom.ker
            (Polynomial.aeval ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] a0) :
              Polynomial (IsLocalRing.ResidueField A) →ₐ[IsLocalRing.ResidueField A]
                ((IsLocalRing.ResidueField A) ⊗[A] Algebra.adjoin A ({u0} : Set B))).toRingHom
        ≃ₐ[IsLocalRing.ResidueField A]
          ((IsLocalRing.ResidueField A) ⊗[A] Algebra.adjoin A ({u0} : Set B)) :=
    Ideal.quotientKerAlgEquivOfSurjective
      (adjoin_singleton_source_tensor_aeval_surjective (A := A) (B := B) (u0 := u0))
  let eTarget :
      Polynomial (IsLocalRing.ResidueField A) ⧸
          RingHom.ker
            (Polynomial.aeval uBar0 :
              Polynomial (IsLocalRing.ResidueField A) →ₐ[IsLocalRing.ResidueField A]
                Algebra.adjoin A ({uBar} : Set Bbar)).toRingHom
        ≃ₐ[IsLocalRing.ResidueField A]
          Algebra.adjoin A ({uBar} : Set Bbar) :=
    Ideal.quotientKerAlgEquivOfSurjective
      (adjoin_singleton_target_aeval_surjective (A := A) (Bbar := Bbar) (uBar := uBar))
  let hker :
      RingHom.ker
          (Polynomial.aeval uBar0 :
            Polynomial (IsLocalRing.ResidueField A) →ₐ[IsLocalRing.ResidueField A]
              Algebra.adjoin A ({uBar} : Set Bbar)).toRingHom =
        RingHom.ker
          (Polynomial.aeval ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] a0) :
            Polynomial (IsLocalRing.ResidueField A) →ₐ[IsLocalRing.ResidueField A]
              ((IsLocalRing.ResidueField A) ⊗[A] Algebra.adjoin A ({u0} : Set B))).toRingHom :=
    adjoin_singleton_target_eval_kernel_eq_source_tensor_eval_kernel
      (A := A) (B := B) (Bbar := Bbar) red hred hu0
  let eQuot :
      Polynomial (IsLocalRing.ResidueField A) ⧸
          RingHom.ker
            (Polynomial.aeval ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] a0) :
              Polynomial (IsLocalRing.ResidueField A) →ₐ[IsLocalRing.ResidueField A]
                ((IsLocalRing.ResidueField A) ⊗[A] Algebra.adjoin A ({u0} : Set B))).toRingHom
        ≃ₐ[IsLocalRing.ResidueField A]
          Polynomial (IsLocalRing.ResidueField A) ⧸
            RingHom.ker
              (Polynomial.aeval uBar0 :
                Polynomial (IsLocalRing.ResidueField A) →ₐ[IsLocalRing.ResidueField A]
                  Algebra.adjoin A ({uBar} : Set Bbar)).toRingHom :=
    Ideal.quotientEquivAlg
      (R₁ := IsLocalRing.ResidueField A)
      (I := RingHom.ker
        (Polynomial.aeval ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] a0) :
          Polynomial (IsLocalRing.ResidueField A) →ₐ[IsLocalRing.ResidueField A]
            ((IsLocalRing.ResidueField A) ⊗[A] Algebra.adjoin A ({u0} : Set B))).toRingHom)
      (J := RingHom.ker
        (Polynomial.aeval uBar0 :
          Polynomial (IsLocalRing.ResidueField A) →ₐ[IsLocalRing.ResidueField A]
            Algebra.adjoin A ({uBar} : Set Bbar)).toRingHom)
      (AlgEquiv.refl _)
      (by simpa [hker])
  let eAlg :
      (IsLocalRing.ResidueField A) ⊗[A] Algebra.adjoin A ({u0} : Set B) ≃ₐ[
        IsLocalRing.ResidueField A] Algebra.adjoin A ({uBar} : Set Bbar) :=
    eSource.symm.trans (eQuot.trans eTarget)
  refine ⟨eAlg.toLinearEquiv, ?_⟩
  intro x
  -- Both candidate maps are `A`-algebra morphisms out of `A[u0]`; it suffices to compare them on
  -- the singleton generator and on scalars.
  let lhs : Algebra.adjoin A ({u0} : Set B) →ₐ[A] Algebra.adjoin A ({uBar} : Set Bbar) :=
    (eAlg.toAlgHom.restrictScalars A).comp
      (Algebra.TensorProduct.includeRight :
        Algebra.adjoin A ({u0} : Set B) →ₐ[A]
          (IsLocalRing.ResidueField A) ⊗[A] Algebra.adjoin A ({u0} : Set B))
  have hlhs :
      lhs a0 = uBar0 := by
    -- On the quotient presentations, both sides identify the class of `X` with the chosen
    -- singleton generator.
    apply eTarget.injective
    change eQuot (eSource.symm (lhs a0)) = eQuot (eSource.symm (uBar0))
    simp [lhs, eAlg, a0, uBar0, eSource, eTarget, eQuot]
  have hmaps :
      lhs = adjoin_singleton_codRestrict (A := A) (B := B) (Bbar := Bbar) red hu0 := by
    ext y
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ y.property
    · intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst z
      simpa [lhs, a0, uBar0] using hlhs
    · intro a
      -- Both maps preserve the original `A`-algebra structure.
      simp [lhs]
    · intro y z hyEq hzEq
      simpa [map_add, hyEq, hzEq]
    · intro y z hyEq hzEq
      simpa [map_mul, hyEq, hzEq]
  simpa [lhs] using congrArg (fun φ => φ x) hmaps

theorem adjoin_singleton_codRestrict_isBaseChange
    (red : B →ₐ[A] Bbar)
    (hred : IsBaseChange (IsLocalRing.ResidueField A) red.toLinearMap)
    {u0 : B} {uBar : Bbar} (hu0 : red u0 = uBar) :
    IsBaseChange (IsLocalRing.ResidueField A)
      (adjoin_singleton_codRestrict (A := A) (B := B) (Bbar := Bbar) red hu0).toLinearMap := by
  -- Route correction: the remaining work is not ambient scalar installation anymore; the new
  -- ambient generator transport lemmas above isolate the coercion-heavy step needed to package the
  -- codrestricted equivalence.
  obtain ⟨e, he⟩ :=
    adjoin_singleton_codRestrict_baseChange_equiv_exists
      (A := A) (B := B) (Bbar := Bbar) red hred hu0
  -- Once the compatible equivalence exists, the universal property is exactly
  -- `IsBaseChange.of_equiv`.
  refine IsBaseChange.of_equiv e ?_
  intro x
  simpa using he x

/-- Helper for Exercise 14-14.4-6: the canonical point of a singleton-generated subalgebra is
idempotent as soon as its ambient generator is idempotent. -/
lemma adjoin_singleton_self_isIdempotentElem
    {R : Type*} [Ring R] [Algebra A R] {u : R}
    (hu : IsIdempotentElem u) :
    IsIdempotentElem
      (⟨u, Algebra.self_mem_adjoin_singleton A u⟩ : Algebra.adjoin A ({u} : Set R)) := by
  -- Forget to the ambient algebra: the singleton-adjoin point has underlying value `u`.
  apply Subtype.ext
  simpa [IsIdempotentElem] using hu.eq

/-- Helper for Exercise 14-14.4-6: if `x0` reduces to an idempotent `xbar`, then `x0` is an
approximate root of `X^2 - X` after applying the reduction map. -/
lemma map_eval_X_sq_sub_X_eq_zero_of_isIdempotent_reduction
    {S : Type*} [CommRing S] [Algebra A S]
    {Sbar : Type*} [CommRing Sbar] [Algebra A Sbar]
    (red : S →ₐ[A] Sbar)
    {x0 : S} {xbar : Sbar} (hx0 : red x0 = xbar)
    (hxbar : IsIdempotentElem xbar) :
    red (Polynomial.aeval x0 (Polynomial.X ^ 2 - Polynomial.X : Polynomial A)) = 0 := by
  -- Push the evaluation through the reduction map and then use the idempotent relation downstairs.
  calc
    red (Polynomial.aeval x0 (Polynomial.X ^ 2 - Polynomial.X : Polynomial A)) =
        Polynomial.aeval (red x0) (Polynomial.X ^ 2 - Polynomial.X : Polynomial A) := by
          simpa using
            (Polynomial.hom_eval₂
              (p := (Polynomial.X ^ 2 - Polynomial.X : Polynomial A))
              (f := algebraMap A S) (g := red.toRingHom) x0)
    _ = 0 := by
          simpa [hx0, IsIdempotentElem, pow_two, sub_eq_zero] using hxbar.eq

/-- Helper for Exercise 14-14.4-6: if `x0` reduces to an idempotent `xbar`, then the derivative of
`X^2 - X` at `x0` becomes a unit after reduction. -/
lemma map_derivative_eval_X_sq_sub_X_isUnit_of_isIdempotent_reduction
    {S : Type*} [CommRing S] [Algebra A S]
    {Sbar : Type*} [CommRing Sbar] [Algebra A Sbar]
    (red : S →ₐ[A] Sbar)
    {x0 : S} {xbar : Sbar} (hx0 : red x0 = xbar)
    (hxbar : IsIdempotentElem xbar) :
    IsUnit
      (red (Polynomial.aeval x0 ((Polynomial.X ^ 2 - Polynomial.X : Polynomial A).derivative))) := by
  -- Again, transport the derivative evaluation downstairs and use the simple-root computation.
  have hmap :
      red (Polynomial.aeval x0 ((Polynomial.X ^ 2 - Polynomial.X : Polynomial A).derivative)) =
        Polynomial.aeval (red x0) ((Polynomial.X ^ 2 - Polynomial.X : Polynomial A).derivative) := by
    simpa using
      (Polynomial.hom_eval₂
        (p := ((Polynomial.X ^ 2 - Polynomial.X : Polynomial A).derivative))
        (f := algebraMap A S) (g := red.toRingHom) x0)
  -- The closed-fiber idempotent is a simple root of `X^2 - X`.
  rw [hmap, hx0]
  simpa using
    (derivative_eval_X_sq_sub_X_isUnit_of_isIdempotentElem (R := Sbar) hxbar)

/-- Helper for Exercise 14-14.4-6: once the image of the universal element `X` lifts to an
idempotent upstairs, the entire map from the universal standard-etale algebra lifts. -/
theorem x_sq_sub_X_standardEtale_hom_lift_of_lifted_point
    {S : Type*} [CommRing S] [Algebra A S]
    {Sbar : Type*} [CommRing Sbar] [Algebra A Sbar]
    (redS : S →ₐ[A] Sbar)
    (φbar : (x_sq_sub_X_standardEtalePair (A := A)).Ring →ₐ[A] Sbar)
    {x : S}
    (hx : IsIdempotentElem x)
    (hxred : redS x = φbar (x_sq_sub_X_standardEtalePair (A := A)).X) :
    ∃ φ : (x_sq_sub_X_standardEtalePair (A := A)).Ring →ₐ[A] S,
      redS.comp φ = φbar := by
  let P := x_sq_sub_X_standardEtalePair (A := A)
  -- Convert the chosen point into the universal mapping predicate for `P`.
  have hxMap : P.HasMap x :=
    (x_sq_sub_X_standardEtale_hasMap_iff_isIdempotentElem (A := A) x).2 hx
  let φ : P.Ring →ₐ[A] S := P.lift x hxMap
  refine ⟨φ, ?_⟩
  -- Maps out of `P.Ring` are determined by the image of `X`.
  apply P.hom_ext
  -- By construction, `φ` sends `X` to `x`, and `x` reduces to the target point downstairs.
  simpa [φ, P, StandardEtalePair.lift_X] using hxred

/-- Helper for Exercise 14-14.4-6: the canonical generator of `A[u0]` reduces to the canonical
generator of `A[uBar]` under the restricted singleton-adjoin reduction map. -/
@[simp] lemma adjoin_singleton_codRestrict_self
    (red : B →ₐ[A] Bbar)
    {u0 : B} {uBar : Bbar} (hu0 : red u0 = uBar) :
    adjoin_singleton_codRestrict (A := A) (B := B) (Bbar := Bbar) red hu0
        (⟨u0, Algebra.self_mem_adjoin_singleton A u0⟩ :
          Algebra.adjoin A ({u0} : Set B)) =
      (⟨uBar, Algebra.self_mem_adjoin_singleton A uBar⟩ :
        Algebra.adjoin A ({uBar} : Set Bbar)) := by
  -- Compare the two singleton-adjoin points by their underlying ambient values.
  apply Subtype.ext
  simpa [adjoin_singleton_codRestrict_apply, hu0]

/-- Helper for Exercise 14-14.4-6: in the singleton-generated commutative algebra `A[u0]`, the
derivative of `X^2 - X` at the canonical generator is already a unit modulo the kernel of the
restricted reduction map. -/
lemma quotientKer_adjoin_singleton_derivative_isUnit
    (red : B →ₐ[A] Bbar)
    {u0 : B} {uBar : Bbar} (hu0 : red u0 = uBar)
    (huBar : IsIdempotentElem uBar)
    [CommRing (Algebra.adjoin A ({u0} : Set B))]
    [CommRing (Algebra.adjoin A ({uBar} : Set Bbar))] :
    let redS := adjoin_singleton_codRestrict (A := A) (B := B) (Bbar := Bbar) red hu0
    let a0 : Algebra.adjoin A ({u0} : Set B) := ⟨u0, Algebra.self_mem_adjoin_singleton A u0⟩
    IsUnit
      (Ideal.Quotient.mk (RingHom.ker redS)
        (Polynomial.aeval a0
          ((Polynomial.X ^ 2 - Polynomial.X : Polynomial A).derivative))) := by
  let redS := adjoin_singleton_codRestrict (A := A) (B := B) (Bbar := Bbar) red hu0
  let a0 : Algebra.adjoin A ({u0} : Set B) := ⟨u0, Algebra.self_mem_adjoin_singleton A u0⟩
  let e :
      (Algebra.adjoin A ({u0} : Set B) ⧸ RingHom.ker redS) ≃ₐ[A]
        Algebra.adjoin A ({uBar} : Set Bbar) :=
    Ideal.quotientKerAlgEquivOfSurjective
      (adjoin_singleton_codRestrict_surjective
        (A := A) (B := B) (Bbar := Bbar) red hu0)
  have hunit_downstairs :
      IsUnit
        (redS (Polynomial.aeval a0
          ((Polynomial.X ^ 2 - Polynomial.X : Polynomial A).derivative))) := by
    -- The restricted reduction sends the canonical generator to the idempotent generator
    -- downstairs, so the derivative remains a unit after reduction.
    simpa [redS, a0] using
      map_derivative_eval_X_sq_sub_X_isUnit_of_isIdempotent_reduction
        (A := A)
        (S := Algebra.adjoin A ({u0} : Set B))
        (Sbar := Algebra.adjoin A ({uBar} : Set Bbar))
        (red := redS)
        (x0 := a0)
        (xbar := (⟨uBar, Algebra.self_mem_adjoin_singleton A uBar⟩ :
          Algebra.adjoin A ({uBar} : Set Bbar)))
        (adjoin_singleton_codRestrict_self
          (A := A) (B := B) (Bbar := Bbar) red hu0)
        (adjoin_singleton_self_isIdempotentElem (A := A) huBar)
  -- Transport the downstairs unit back through the quotient-kernel algebra equivalence.
  have hunit_quot :
      IsUnit
        (e.symm
          (redS (Polynomial.aeval a0
            ((Polynomial.X ^ 2 - Polynomial.X : Polynomial A).derivative)))) := by
    exact hunit_downstairs.map e.symm.toRingHom
  exact by
    simpa [e, redS, a0] using hunit_quot

/-- Helper for Exercise 14-14.4-6: if `x` already lies in `A[u]`, then the singleton-generated
subalgebra `A[x]` includes canonically into `A[u]`. -/
lemma adjoin_singleton_le_of_mem_adjoin_singleton
    {R : Type*} [Ring R] [Algebra A R] {u x : R}
    (hx : x ∈ Algebra.adjoin A ({u} : Set R)) :
    Algebra.adjoin A ({x} : Set R) ≤ Algebra.adjoin A ({u} : Set R) := by
  -- The target subalgebra already contains the chosen generator `x`, so it contains `A[x]`.
  refine Algebra.adjoin_le ?_
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst y
  exact hx

/-- Helper for Exercise 14-14.4-6: in an integral `A`-algebra, the pullback of the maximal ideal
of the local base lies in the Jacobson radical upstairs. -/
lemma integral_map_maximalIdeal_le_jacobson
    {S : Type*} [CommRing S] [Algebra A S] [Algebra.IsIntegral A S] :
    ((IsLocalRing.maximalIdeal A).map (algebraMap A S)) ≤ Ideal.jacobson (⊥ : Ideal S) := by
  -- Every maximal ideal of the integral algebra contracts to a maximal ideal of the local base,
  -- so the pulled-back maximal ideal is contained in each maximal ideal upstairs.
  rw [Ideal.jacobson, le_sInf_iff]
  intro J hJ
  let _ : J.IsMaximal := hJ
  refine Ideal.map_le_iff_le_comap.2 ?_
  -- The contraction of a maximal ideal along an integral map is maximal, hence equals `𝔪_A`.
  exact le_of_eq
    (IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := A) (S := S) J)).symm

/-- Helper for Exercise 14-14.4-6: any surjective residue-field base-change algebra map has kernel
equal to the pullback of the maximal ideal from the henselian local base. -/
lemma residueField_baseChange_ker_eq_map_maximalIdeal
    {S : Type*} [CommRing S] [Algebra A S]
    {Sbar : Type*} [CommRing Sbar] [Algebra A Sbar]
    [Algebra (IsLocalRing.ResidueField A) Sbar]
    [IsScalarTower A (IsLocalRing.ResidueField A) Sbar]
    (redS : S →ₐ[A] Sbar)
    (hredS : IsBaseChange (IsLocalRing.ResidueField A) redS.toLinearMap) :
    RingHom.ker redS = (IsLocalRing.maximalIdeal A).map (algebraMap A S) := by
  let I : Ideal S := (IsLocalRing.maximalIdeal A).map (algebraMap A S)
  have hI_le : I ≤ RingHom.ker redS := by
    -- Elements of the maximal ideal already vanish in the residue field, hence also after
    -- any residue-field base change.
    intro a ha
    rw [RingHom.mem_ker]
    rw [IsScalarTower.algebraMap_apply A (IsLocalRing.ResidueField A) Sbar]
    rw [← map_zero (algebraMap (IsLocalRing.ResidueField A) Sbar)]
    exact congrArg (algebraMap (IsLocalRing.ResidueField A) Sbar) <| by
      rw [IsLocalRing.ResidueField.algebraMap_eq]
      exact (IsLocalRing.residue_eq_zero_iff (R := A) a).2 ha
  let q : S ⧸ I →ₐ[A] Sbar := Ideal.Quotient.liftₐ I redS hI_le
  have hq_injective : Function.Injective q := by
    let e :
        S ⧸ I ≃ₐ[IsLocalRing.ResidueField A]
          (IsLocalRing.ResidueField A) ⊗[A] S :=
      Algebra.TensorProduct.quotIdealMapEquivQuotTensor
        (B := S) (I := IsLocalRing.maximalIdeal A)
    let l : Sbar →ₗ[A] S ⧸ I :=
      (e.symm.toLinearMap.restrictScalars A).comp (hredS.equiv.symm.restrictScalars A)
    have hl : l.comp q.toLinearMap = LinearMap.id := by
      -- Compare the quotient model `S / 𝔪_A S` with the tensor-model `kA ⊗[A] S` on quotient
      -- generators, where the ambient base-change equivalence is explicit.
      ext x
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      apply e.injective
      simp [l, q]
    exact Function.LeftInverse.injective (g := l) (LinearMap.congr_fun hl)
  have hker_le : RingHom.ker redS ≤ I := by
    -- Once the induced quotient map is injective, every element killed by `redS` already lies in
    -- `𝔪_A S`.
    intro x hx
    have hxq : q (Ideal.Quotient.mk I x) = 0 := by
      simpa [q] using hx
    have hxmk : Ideal.Quotient.mk I x = 0 := hq_injective hxq
    exact Ideal.Quotient.eq_zero_iff_mem.mp hxmk
  exact le_antisymm hker_le hI_le

/-- Helper for Exercise 14-14.4-6: the kernel of the restricted singleton-adjoin reduction is
exactly the maximal-ideal pullback from the henselian local base. -/
lemma adjoin_singleton_codRestrict_ker_eq_map_maximalIdeal
    (red : B →ₐ[A] Bbar)
    (hred : IsBaseChange (IsLocalRing.ResidueField A) red.toLinearMap)
    {u0 : B} {uBar : Bbar} (hu0 : red u0 = uBar)
    [CommRing (Algebra.adjoin A ({u0} : Set B))]
    [CommRing (Algebra.adjoin A ({uBar} : Set Bbar))] :
    RingHom.ker (adjoin_singleton_codRestrict (A := A) (B := B) (Bbar := Bbar) red hu0) =
      (IsLocalRing.maximalIdeal A).map
        (algebraMap A (Algebra.adjoin A ({u0} : Set B))) := by
  let redS := adjoin_singleton_codRestrict (A := A) (B := B) (Bbar := Bbar) red hu0
  -- Compare the restricted quotient `A[u0] / ker(redS)` with the canonical closed fiber
  -- `kA ⊗[A] A[u0]`, then apply the general kernel computation above.
  exact residueField_baseChange_ker_eq_map_maximalIdeal
    (A := A) (redS := redS)
    (adjoin_singleton_codRestrict_isBaseChange
      (A := A) (B := B) (Bbar := Bbar) red hred hu0)

/-- Helper for Exercise 14-14.4-6: the quotient of `A[u0]` by `𝔪_A A[u0]` identifies with the
reduced singleton-generated algebra `A[uBar]`. -/
noncomputable def adjoin_singleton_codRestrict_quotientAlgEquiv
    (red : B →ₐ[A] Bbar)
    (hred : IsBaseChange (IsLocalRing.ResidueField A) red.toLinearMap)
    {u0 : B} {uBar : Bbar} (hu0 : red u0 = uBar)
    [CommRing (Algebra.adjoin A ({u0} : Set B))]
    [CommRing (Algebra.adjoin A ({uBar} : Set Bbar))] :
    (Algebra.adjoin A ({u0} : Set B) ⧸
      ((IsLocalRing.maximalIdeal A).map
        (algebraMap A (Algebra.adjoin A ({u0} : Set B))))) ≃ₐ[A]
      Algebra.adjoin A ({uBar} : Set Bbar) := by
  let redS := adjoin_singleton_codRestrict (A := A) (B := B) (Bbar := Bbar) red hu0
  let eKer :
      (Algebra.adjoin A ({u0} : Set B) ⧸ RingHom.ker redS) ≃ₐ[A]
        Algebra.adjoin A ({uBar} : Set Bbar) :=
    Ideal.quotientKerAlgEquivOfSurjective
      (adjoin_singleton_codRestrict_surjective
        (A := A) (B := B) (Bbar := Bbar) red hu0)
  let eIdeal :
      (Algebra.adjoin A ({u0} : Set B) ⧸
        ((IsLocalRing.maximalIdeal A).map
          (algebraMap A (Algebra.adjoin A ({u0} : Set B))))) ≃ₐ[A]
        (Algebra.adjoin A ({u0} : Set B) ⧸ RingHom.ker redS) :=
    Ideal.quotientEquivAlgOfEq A
      (adjoin_singleton_codRestrict_ker_eq_map_maximalIdeal
        (A := A) (B := B) (Bbar := Bbar) red hred hu0).symm
  -- Replace the restricted kernel by `𝔪_A A[u0]`, then apply the first isomorphism theorem.
  exact eIdeal.trans eKer

/-- Helper for Exercise 14-14.4-6: two elements of `A[u0]` with difference in `𝔪_A A[u0]`
have the same image in the reduced singleton-generated algebra `A[uBar]`. -/
lemma adjoin_singleton_codRestrict_eq_of_sub_mem_map_maximalIdeal
    (red : B →ₐ[A] Bbar)
    (hred : IsBaseChange (IsLocalRing.ResidueField A) red.toLinearMap)
    {u0 : B} {uBar : Bbar} (hu0 : red u0 = uBar)
    [CommRing (Algebra.adjoin A ({u0} : Set B))]
    [CommRing (Algebra.adjoin A ({uBar} : Set Bbar))]
    {x y : Algebra.adjoin A ({u0} : Set B)}
    (hxy :
      x - y ∈
        (IsLocalRing.maximalIdeal A).map
          (algebraMap A (Algebra.adjoin A ({u0} : Set B)))) :
    adjoin_singleton_codRestrict (A := A) (B := B) (Bbar := Bbar) red hu0 x =
      adjoin_singleton_codRestrict (A := A) (B := B) (Bbar := Bbar) red hu0 y := by
  let redS := adjoin_singleton_codRestrict (A := A) (B := B) (Bbar := Bbar) red hu0
  have hKer :
      RingHom.ker redS =
        (IsLocalRing.maximalIdeal A).map
          (algebraMap A (Algebra.adjoin A ({u0} : Set B))) := by
    -- Normalize the kernel of the restricted reduction map to the pulled-back maximal ideal.
    simpa [redS] using
      adjoin_singleton_codRestrict_ker_eq_map_maximalIdeal
        (A := A) (B := B) (Bbar := Bbar) red hred hu0
  have hxyKer : x - y ∈ RingHom.ker redS := by
    -- Once the kernel is identified, the hypothesis is exactly a kernel-membership statement.
    simpa [hKer] using hxy
  have hsub :
      redS x - redS y = 0 := by
    -- Apply the reduction map to the difference and rewrite through `map_sub`.
    simpa [map_sub] using (RingHom.mem_ker.mp hxyKer)
  exact sub_eq_zero.mp hsub

/-- Helper for Exercise 14-14.4-6: in the singleton-generated commutative algebra `A[u0]`, the
pullback of the maximal ideal from the henselian local base still lies in the Jacobson radical. -/
lemma adjoin_singleton_map_maximalIdeal_le_jacobson
    {u0 : B}
    [CommRing (Algebra.adjoin A ({u0} : Set B))] :
    ((IsLocalRing.maximalIdeal A).map
      (algebraMap A (Algebra.adjoin A ({u0} : Set B)))) ≤
        Ideal.jacobson (⊥ : Ideal (Algebra.adjoin A ({u0} : Set B))) := by
  letI : Algebra.IsIntegral A B := inferInstance
  letI : Algebra.IsIntegral A (Algebra.adjoin A ({u0} : Set B)) :=
    Algebra.IsIntegral.adjoin (R := A) (A := B) (S := ({u0} : Set B)) <| by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      exact Algebra.IsIntegral.isIntegral u0
  -- The specialized singleton-generated algebra is integral over `A`, so the generic Jacobson
  -- containment applies directly.
  exact integral_map_maximalIdeal_le_jacobson
    (A := A) (S := Algebra.adjoin A ({u0} : Set B))

/-- Helper for Exercise 14-14.4-6: after choosing a representative of an idempotent quotient
class in `A[u0] / 𝔪_A A[u0]`, the polynomial `X^2 - X` already satisfies the exact Hensel
hypotheses at that representative. -/
lemma adjoin_singleton_representative_hensel_data
    {u0 : B}
    [CommRing (Algebra.adjoin A ({u0} : Set B))]
    {eBar :
      Algebra.adjoin A ({u0} : Set B) ⧸
        ((IsLocalRing.maximalIdeal A).map
          (algebraMap A (Algebra.adjoin A ({u0} : Set B))))}
    (heBar : IsIdempotentElem eBar)
    {e0 : Algebra.adjoin A ({u0} : Set B)}
    (he0 :
      Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal A).map
          (algebraMap A (Algebra.adjoin A ({u0} : Set B)))) e0 = eBar) :
    Polynomial.aeval e0 (Polynomial.X ^ 2 - Polynomial.X : Polynomial A) ∈
        ((IsLocalRing.maximalIdeal A).map
          (algebraMap A (Algebra.adjoin A ({u0} : Set B)))) ∧
      IsUnit
        (Ideal.Quotient.mk
          ((IsLocalRing.maximalIdeal A).map
            (algebraMap A (Algebra.adjoin A ({u0} : Set B))))
          (Polynomial.aeval e0
            ((Polynomial.X ^ 2 - Polynomial.X : Polynomial A).derivative))) := by
  let I :
      Ideal (Algebra.adjoin A ({u0} : Set B)) :=
    (IsLocalRing.maximalIdeal A).map
      (algebraMap A (Algebra.adjoin A ({u0} : Set B)))
  constructor
  · have hzero :
        (Ideal.Quotient.mk I)
            (Polynomial.aeval e0 (Polynomial.X ^ 2 - Polynomial.X : Polynomial A)) = 0 := by
      -- Reducing the representative gives the chosen idempotent quotient class, so the universal
      -- idempotent polynomial vanishes after quotienting.
      simpa [I, he0] using
        map_eval_X_sq_sub_X_eq_zero_of_isIdempotent_reduction
          (A := A)
          (S := Algebra.adjoin A ({u0} : Set B))
          (Sbar := Algebra.adjoin A ({u0} : Set B) ⧸ I)
          (red := Ideal.Quotient.mkₐ A I)
          (x0 := e0)
          (xbar := eBar)
          he0
          heBar
    exact Ideal.Quotient.eq_zero_iff_mem.mp hzero
  · -- The derivative of `X^2 - X` stays a unit in the quotient at an idempotent class.
    simpa [I, he0] using
      map_derivative_eval_X_sq_sub_X_isUnit_of_isIdempotent_reduction
        (A := A)
        (S := Algebra.adjoin A ({u0} : Set B))
        (Sbar := Algebra.adjoin A ({u0} : Set B) ⧸ I)
        (red := Ideal.Quotient.mkₐ A I)
        (x0 := e0)
        (xbar := eBar)
        he0
        heBar

/-- Helper for Exercise 14-14.4-6: in the monogenic commutative algebra `A[u0]`, the canonical
reduced generator `uBar` should lift to an actual root of `X^2 - X` upstairs. -/
lemma adjoin_singleton_generator_hensel_data_map_maximalIdeal
    (red : B →ₐ[A] Bbar)
    (hred : IsBaseChange (IsLocalRing.ResidueField A) red.toLinearMap)
    {u0 : B} {uBar : Bbar} (hu0 : red u0 = uBar)
    [CommRing (Algebra.adjoin A ({u0} : Set B))]
    [CommRing (Algebra.adjoin A ({uBar} : Set Bbar))]
    (huBar : IsIdempotentElem uBar) :
    Polynomial.aeval
        (⟨u0, Algebra.self_mem_adjoin_singleton A u0⟩ :
          Algebra.adjoin A ({u0} : Set B))
        (Polynomial.X ^ 2 - Polynomial.X : Polynomial A) ∈
      ((IsLocalRing.maximalIdeal A).map
        (algebraMap A (Algebra.adjoin A ({u0} : Set B)))) ∧
    IsUnit
      (Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal A).map
          (algebraMap A (Algebra.adjoin A ({u0} : Set B))))
        (Polynomial.aeval
          (⟨u0, Algebra.self_mem_adjoin_singleton A u0⟩ :
            Algebra.adjoin A ({u0} : Set B))
          ((Polynomial.X ^ 2 - Polynomial.X : Polynomial A).derivative))) := by
  let S := Algebra.adjoin A ({u0} : Set B)
  let redS := adjoin_singleton_codRestrict (A := A) (B := B) (Bbar := Bbar) red hu0
  let a0 : S := ⟨u0, Algebra.self_mem_adjoin_singleton A u0⟩
  have hEvalKer :
      Polynomial.aeval a0 (Polynomial.X ^ 2 - Polynomial.X : Polynomial A) ∈
        RingHom.ker redS := by
    -- The canonical generator reduces to the idempotent generator downstairs, so `X^2 - X`
    -- already vanishes after applying the restricted reduction map.
    rw [RingHom.mem_ker]
    simpa [redS, a0] using
      map_eval_X_sq_sub_X_eq_zero_of_isIdempotent_reduction
        (A := A)
        (S := S)
        (Sbar := Algebra.adjoin A ({uBar} : Set Bbar))
        (red := redS)
        (x0 := a0)
        (xbar := (⟨uBar, Algebra.self_mem_adjoin_singleton A uBar⟩ :
          Algebra.adjoin A ({uBar} : Set Bbar)))
        (adjoin_singleton_codRestrict_self
          (A := A) (B := B) (Bbar := Bbar) red hu0)
        (adjoin_singleton_self_isIdempotentElem (A := A) huBar)
  have hDerivKer :
      IsUnit
        (Ideal.Quotient.mk (RingHom.ker redS)
          (Polynomial.aeval a0
            ((Polynomial.X ^ 2 - Polynomial.X : Polynomial A).derivative))) := by
    -- The derivative is a unit in the closed fiber at the same canonical generator.
    simpa [redS, a0] using
      quotientKer_adjoin_singleton_derivative_isUnit
        (A := A) (B := B) (Bbar := Bbar) red hu0 huBar
  have hKer :
      RingHom.ker redS =
        (IsLocalRing.maximalIdeal A).map (algebraMap A S) := by
    -- Normalize the kernel once so the Hensel data is recorded over the source ideal `𝔪_A S`.
    simpa [S, redS] using
      adjoin_singleton_codRestrict_ker_eq_map_maximalIdeal
        (A := A) (B := B) (Bbar := Bbar) red hred hu0
  constructor
  · -- Rewrite the kernel membership through the normalized ideal equality.
    simpa [S, a0] using (hKer ▸ hEvalKer)
  · -- Rewrite the quotient unit statement through the same normalized ideal equality.
    simpa [S, a0] using (hKer ▸ hDerivKer)

/-- Helper for Exercise 14-14.4-6: in the singleton-generated commutative algebra `A[u0]`, a
derivative that is a unit modulo `𝔪_A A[u0]` is already a unit upstairs because that ideal lies in
the Jacobson radical. -/
lemma adjoin_singleton_generator_derivative_isUnit
    {u0 : B}
    [CommRing (Algebra.adjoin A ({u0} : Set B))] :
    let S := Algebra.adjoin A ({u0} : Set B)
    let I : Ideal S := (IsLocalRing.maximalIdeal A).map (algebraMap A S)
    ∀ {a : S},
      IsUnit
        (Ideal.Quotient.mk I
          (Polynomial.aeval a
            ((Polynomial.X ^ 2 - Polynomial.X : Polynomial A).derivative))) →
      IsUnit
        (Polynomial.aeval a
          ((Polynomial.X ^ 2 - Polynomial.X : Polynomial A).derivative)) := by
  dsimp
  intro a hDeriv
  have hJac :
      ((IsLocalRing.maximalIdeal A).map
        (algebraMap A (Algebra.adjoin A ({u0} : Set B)))) ≤
          Ideal.jacobson (⊥ : Ideal (Algebra.adjoin A ({u0} : Set B))) :=
    adjoin_singleton_map_maximalIdeal_le_jacobson (A := A) (B := B) (u0 := u0)
  haveI :
      IsLocalHom
        (Ideal.Quotient.mk
          ((IsLocalRing.maximalIdeal A).map
            (algebraMap A (Algebra.adjoin A ({u0} : Set B))))) :=
    isLocalHom_of_le_jacobson_bot _ hJac
  -- Once the quotient map is local, units modulo `𝔪_A A[u0]` lift to genuine units upstairs.
  exact IsUnit.of_map (Ideal.Quotient.mk _) hDeriv

/-- Helper for Exercise 14-14.4-6: the quotient class of an approximate root of `X^2 - X`
automatically defines a point of the universal idempotent standard-etale algebra. -/
lemma x_sq_sub_X_standardEtale_hasMap_quotient_of_hensel_data
    {S : Type*} [CommRing S] [Algebra A S]
    (I : Ideal S) {a0 : S}
    (hEval :
      let fS : Polynomial S := (Polynomial.X ^ 2 - Polynomial.X : Polynomial A).map
        (algebraMap A S)
      fS.eval a0 ∈ I) :
    (x_sq_sub_X_standardEtalePair (A := A)).HasMap
      (Ideal.Quotient.mk I a0 : S ⧸ I) := by
  dsimp at hEval
  have hEvalQuot :
      Polynomial.aeval (Ideal.Quotient.mk I a0 : S ⧸ I)
          (Polynomial.X ^ 2 - Polynomial.X : Polynomial A) = 0 := by
    -- Reduce the approximate root modulo `I`; the quotient class becomes an actual root.
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simpa [Polynomial.aeval_def, Polynomial.aeval_map_algebraMap] using hEval
  have hIdem : IsIdempotentElem (Ideal.Quotient.mk I a0 : S ⧸ I) := by
    -- For `X^2 - X`, being a root is exactly the idempotent relation.
    rw [IsIdempotentElem]
    exact sub_eq_zero.mp <| by
      simpa [Polynomial.aeval_def, pow_two] using hEvalQuot
  exact
    (x_sq_sub_X_standardEtale_hasMap_iff_isIdempotentElem
      (A := A) (x := (Ideal.Quotient.mk I a0 : S ⧸ I))).2 hIdem

/-- Helper for Exercise 14-14.4-6: once the standard-etale point over `S ⧸ I` lifts to `S`,
evaluating the lifted map at `X` gives the required root and congruence. -/
lemma root_lift_of_standard_etale_hom_lift
    {S : Type*} [CommRing S] [Algebra A S]
    (I : Ideal S) {a0 : S}
    (φbar : (x_sq_sub_X_standardEtalePair (A := A)).Ring →ₐ[A] S ⧸ I)
    (hφbarX :
      φbar (x_sq_sub_X_standardEtalePair (A := A)).X =
        (Ideal.Quotient.mk I a0 : S ⧸ I))
    (φ : (x_sq_sub_X_standardEtalePair (A := A)).Ring →ₐ[A] S)
    (hφ : (Ideal.Quotient.mkₐ A I).comp φ = φbar) :
    let fS : Polynomial S := (Polynomial.X ^ 2 - Polynomial.X : Polynomial A).map
      (algebraMap A S)
    ∃ e : S, fS.IsRoot e ∧ e - a0 ∈ I := by
  let P := x_sq_sub_X_standardEtalePair (A := A)
  let e : S := φ P.X
  have heMap : P.HasMap e := by
    -- Any algebra map out of the universal standard-etale algebra records a valid point.
    simpa [P, e] using (P.homEquiv φ).2
  have heIdem : IsIdempotentElem e := by
    -- For the universal idempotent presentation, valid points are exactly idempotents.
    exact (x_sq_sub_X_standardEtale_hasMap_iff_isIdempotentElem
      (A := A) (x := e)).1 heMap
  have heRoot :
      ((Polynomial.X ^ 2 - Polynomial.X : Polynomial A).map (algebraMap A S)).IsRoot e := by
    -- Repackage the lifted idempotent as a root of the mapped polynomial over `S`.
    simpa [e, Polynomial.IsRoot, Polynomial.eval_map_algebraMap] using
      (isRoot_X_sq_sub_X_of_isIdempotentElem heIdem)
  have hQuotX :
      Ideal.Quotient.mk I e = Ideal.Quotient.mk I a0 := by
    -- Evaluate the lifted map identity at the universal generator `X`.
    simpa [P, e, hφbarX] using congrArg (fun ψ => ψ P.X) hφ
  have hMem :
      e - a0 ∈ I := by
    -- Equality after quotienting is equivalent to the difference lying in `I`.
    have hZero : Ideal.Quotient.mk I (e - a0) = 0 := by
      simpa [map_sub] using sub_eq_zero.mpr hQuotX
    exact Ideal.Quotient.eq_zero_iff_mem.mp hZero
  exact ⟨e, heRoot, hMem⟩

/-- Helper for Exercise 14-14.4-6: the approximate root data in `A[u0] / 𝔪_A A[u0]` determines
the corresponding point of the universal idempotent standard-etale algebra. -/
lemma adjoin_singleton_standardEtale_quotient_map_of_hensel_data
    {u0 : B}
    [CommRing (Algebra.adjoin A ({u0} : Set B))] :
    let S := Algebra.adjoin A ({u0} : Set B)
    let I : Ideal S := (IsLocalRing.maximalIdeal A).map (algebraMap A S)
    let a0 : S := ⟨u0, Algebra.self_mem_adjoin_singleton A u0⟩
    ∀ (hEval :
        let fS : Polynomial S := (Polynomial.X ^ 2 - Polynomial.X : Polynomial A).map
          (algebraMap A S)
        fS.eval a0 ∈ I),
      ∃ φbar : (x_sq_sub_X_standardEtalePair (A := A)).Ring →ₐ[A] S ⧸ I,
        φbar (x_sq_sub_X_standardEtalePair (A := A)).X =
          (Ideal.Quotient.mk I a0 : S ⧸ I) := by
  dsimp
  intro hEval
  let P := x_sq_sub_X_standardEtalePair (A := A)
  have hx :
      P.HasMap (Ideal.Quotient.mk I a0 : S ⧸ I) :=
    x_sq_sub_X_standardEtale_hasMap_quotient_of_hensel_data
      (A := A) (I := I) (a0 := a0) hEval
  let φbar : P.Ring →ₐ[A] S ⧸ I := P.homEquiv.symm ⟨Ideal.Quotient.mk I a0, hx⟩
  refine ⟨φbar, ?_⟩
  -- Evaluate the universal map at `X`; by construction it records the quotient class of `a0`.
  simpa [φbar, P] using
    (StandardEtalePair.lift_X (P := P) (x := (Ideal.Quotient.mk I a0 : S ⧸ I)) hx)

/-- Helper for Exercise 14-14.4-6: the canonical idempotent generator of the reduced
singleton-adjoin algebra already defines the corresponding closed-fiber point of the universal
standard-etale algebra for `X^2 - X`. -/
lemma adjoin_singleton_standardEtale_closed_fiber_map
    {uBar : Bbar}
    [CommRing (Algebra.adjoin A ({uBar} : Set Bbar))]
    (huBar : IsIdempotentElem uBar) :
    ∃ φbar : (x_sq_sub_X_standardEtalePair (A := A)).Ring →ₐ[A]
        Algebra.adjoin A ({uBar} : Set Bbar),
      φbar (x_sq_sub_X_standardEtalePair (A := A)).X =
        (⟨uBar, Algebra.self_mem_adjoin_singleton A uBar⟩ :
          Algebra.adjoin A ({uBar} : Set Bbar)) := by
  let P := x_sq_sub_X_standardEtalePair (A := A)
  have hx :
      P.HasMap
        (⟨uBar, Algebra.self_mem_adjoin_singleton A uBar⟩ :
          Algebra.adjoin A ({uBar} : Set Bbar)) := by
    -- For `X^2 - X`, the canonical generator downstairs is a valid point exactly because it is
    -- idempotent.
    exact
      (x_sq_sub_X_standardEtale_hasMap_iff_isIdempotentElem
        (A := A)
        (x := (⟨uBar, Algebra.self_mem_adjoin_singleton A uBar⟩ :
          Algebra.adjoin A ({uBar} : Set Bbar)))).2
        (adjoin_singleton_self_isIdempotentElem (A := A) huBar)
  let φbar : P.Ring →ₐ[A] Algebra.adjoin A ({uBar} : Set Bbar) :=
    P.homEquiv.symm
      ⟨(⟨uBar, Algebra.self_mem_adjoin_singleton A uBar⟩ :
          Algebra.adjoin A ({uBar} : Set Bbar)), hx⟩
  refine ⟨φbar, ?_⟩
  -- Evaluate the universal map at `X`; by construction it records the chosen reduced generator.
  simpa [φbar, P] using
    (StandardEtalePair.lift_X
      (P := P)
      (x := (⟨uBar, Algebra.self_mem_adjoin_singleton A uBar⟩ :
        Algebra.adjoin A ({uBar} : Set Bbar))) hx)

/-- Helper for Exercise 14-14.4-6: in the singleton-generated algebra `A[u0]`, the pulled-back
maximal ideal is the Jacobson-radical ideal used by the source Hensel step. -/
lemma adjoin_singleton_hensel_ideal_le_jacobson
    {u0 : B}
    [CommRing (Algebra.adjoin A ({u0} : Set B))] :
    let S := Algebra.adjoin A ({u0} : Set B)
    let I : Ideal S := (IsLocalRing.maximalIdeal A).map (algebraMap A S)
    I ≤ Ideal.jacobson (⊥ : Ideal S) := by
  dsimp
  -- This is exactly the previously established Jacobson-radical control on `A[u0]`.
  simpa using
    adjoin_singleton_map_maximalIdeal_le_jacobson (A := A) (B := B) (u0 := u0)

/-- Helper for Exercise 14-14.4-6: a unit modulo an ideal contained in the Jacobson radical is
already a unit upstairs. -/
lemma isUnit_of_isUnit_quotient_of_le_jacobson
    {S : Type*} [CommRing S] (I : Ideal S)
    (hI : I ≤ Ideal.jacobson (⊥ : Ideal S)) {x : S}
    (hx : IsUnit (Ideal.Quotient.mk I x)) :
    IsUnit x := by
  -- The quotient map is local as soon as `I` is Jacobson-small, so unit classes lift to units.
  let _ : IsLocalHom (Ideal.Quotient.mk I) :=
    isLocalHom_of_le_jacobson_bot I hI
  exact IsUnit.of_map (Ideal.Quotient.mk I) hx

/-- Helper for Exercise 14-14.4-6: for the canonical generator of `A[u0]`, the derivative-unit
condition in the quotient already upgrades to an actual unit upstairs. -/
lemma adjoin_singleton_hensel_derivative_isUnit
    {u0 : B}
    [CommRing (Algebra.adjoin A ({u0} : Set B))] :
    let S := Algebra.adjoin A ({u0} : Set B)
    let I : Ideal S := (IsLocalRing.maximalIdeal A).map (algebraMap A S)
    let fS : Polynomial S := (Polynomial.X ^ 2 - Polynomial.X : Polynomial A).map (algebraMap A S)
    let a0 : S := ⟨u0, Algebra.self_mem_adjoin_singleton A u0⟩
    ∀ (hDeriv : IsUnit (Ideal.Quotient.mk I (fS.derivative.eval a0))),
      IsUnit (fS.derivative.eval a0) := by
  dsimp
  intro hDeriv
  -- Specialize the generic Jacobson-radical upgrade at the canonical generator `a0`.
  simpa [Polynomial.aeval_def, Polynomial.derivative_map, Polynomial.aeval_map_algebraMap] using
    (adjoin_singleton_generator_derivative_isUnit
      (A := A) (B := B) (u0 := u0) (a := a0) hDeriv)

/-- Helper for Exercise 14-14.4-6: a finite integral commutative `A`-algebra is Henselian at the
ideal obtained by extending the maximal ideal of the Henselian local base. -/
lemma henselianRing_map_maximalIdeal_of_finite_integral
    {S : Type*} [CommRing S] [Algebra A S] [Algebra.IsIntegral A S] [Module.Finite A S] :
    HenselianRing S ((IsLocalRing.maximalIdeal A).map (algebraMap A S)) := by
  let I : Ideal S := (IsLocalRing.maximalIdeal A).map (algebraMap A S)
  have hJac : I ≤ Ideal.jacobson (⊥ : Ideal S) :=
    integral_map_maximalIdeal_le_jacobson (A := A) (S := S)
  refine
    { jac := hJac
      is_henselian := ?_ }
  intro f hf a0 hEval hDeriv
  have hDerivUpstairs : IsUnit (f.derivative.eval a0) :=
    isUnit_of_isUnit_quotient_of_le_jacobson (I := I) hJac hDeriv
  -- TODO: the remaining open frontier is now the actual finite-integral Hensel transfer step:
  -- the quotient-unit hypothesis has been upgraded to an honest unit in `S`, so it remains to
  -- deduce a root lift for `f` over the finite integral `A`-algebra `S` from the henselian base.
  let _ := hDerivUpstairs
  sorry

/-- Helper for Exercise 14-14.4-6: the monogenic finite commutative algebra `A[u0]` is Henselian
at the pulled-back maximal ideal from the Henselian local base. -/
lemma adjoin_singleton_henselian_owner
    {u0 : B}
    [CommRing (Algebra.adjoin A ({u0} : Set B))] :
    let S := Algebra.adjoin A ({u0} : Set B)
    let I : Ideal S := (IsLocalRing.maximalIdeal A).map (algebraMap A S)
    HenselianRing S I := by
  dsimp
  letI : Algebra.IsIntegral A B := inferInstance
  letI : Algebra.IsIntegral A (Algebra.adjoin A ({u0} : Set B)) :=
    Algebra.IsIntegral.adjoin (R := A) (A := B) (S := ({u0} : Set B)) <| by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact Algebra.IsIntegral.isIntegral u0
  letI : Module.Finite A (Algebra.adjoin A ({u0} : Set B)) :=
    Algebra.finite_adjoin_simple_of_isIntegral (R := A)
      (A := B) (x := u0) (Algebra.IsIntegral.isIntegral u0)
  -- Route correction: the singleton owner is now just the monogenic instance of the general
  -- finite-integral henselian-transfer theorem above.
  exact henselianRing_map_maximalIdeal_of_finite_integral
    (A := A) (S := Algebra.adjoin A ({u0} : Set B))

/-- Helper for Exercise 14-14.4-6: the only remaining singleton-adjoin Hensel payload is to turn
the explicit `X^2 - X` Hensel data at the canonical generator into an actual lifted root inside
`A[u0]`. -/
lemma adjoin_singleton_idempotent_hensel_step
    {u0 : B}
    [CommRing (Algebra.adjoin A ({u0} : Set B))] :
    let S := Algebra.adjoin A ({u0} : Set B)
    let I : Ideal S := (IsLocalRing.maximalIdeal A).map (algebraMap A S)
    let fS : Polynomial S := (Polynomial.X ^ 2 - Polynomial.X : Polynomial A).map (algebraMap A S)
    let a0 : S := ⟨u0, Algebra.self_mem_adjoin_singleton A u0⟩
    ∀ (hEval : fS.eval a0 ∈ I),
      IsUnit (Ideal.Quotient.mk I (fS.derivative.eval a0)) →
      ∃ e : S, fS.IsRoot e ∧ e - a0 ∈ I := by
  dsimp
  intro hEval hDeriv
  have hMonic : fS.Monic := by
    -- The source polynomial is still monic after extending coefficients from `A` to `A[u0]`.
    simpa [fS] using x_sq_sub_X_map_monic (A := A) (S := S)
  let _ : HenselianRing S I :=
    adjoin_singleton_henselian_owner (A := A) (B := B) (u0 := u0)
  -- Route correction: with the owner theorem isolated, the remaining step is the direct Hensel
  -- lift for `fS = X^2 - X` at the canonical generator `a0`.
  exact HenselianRing.is_henselian fS hMonic a0 hEval hDeriv

/-- Helper for Exercise 14-14.4-6: the only remaining singleton-adjoin Hensel payload is to turn
the explicit `X^2 - X` Hensel data at the canonical generator into an actual lifted root inside
`A[u0]`. -/
lemma adjoin_singleton_root_lift_of_hensel_data
    {u0 : B}
    [CommRing (Algebra.adjoin A ({u0} : Set B))] :
    let S := Algebra.adjoin A ({u0} : Set B)
    let I : Ideal S := (IsLocalRing.maximalIdeal A).map (algebraMap A S)
    let fS : Polynomial S := (Polynomial.X ^ 2 - Polynomial.X : Polynomial A).map (algebraMap A S)
    let a0 : S := ⟨u0, Algebra.self_mem_adjoin_singleton A u0⟩
    ∀ (hEval : fS.eval a0 ∈ I),
      IsUnit (Ideal.Quotient.mk I (fS.derivative.eval a0)) →
      ∃ e : S, fS.IsRoot e ∧ e - a0 ∈ I := by
  dsimp
  intro hEval hDeriv
  -- The blocked singleton-adjoin step has been reduced to the exact special-purpose Hensel lift
  -- needed downstream; no global Henselian owner for `A[u0]` is used anymore.
  exact
    adjoin_singleton_idempotent_hensel_step
      (A := A) (B := B) (u0 := u0) hEval hDeriv

/-- Helper for Exercise 14-14.4-6: in the monogenic commutative algebra `A[u0]`, the canonical
reduced generator `uBar` should lift to an actual root of `X^2 - X` upstairs. -/
lemma adjoin_singleton_generator_root_lift_X_sq_sub_X
    (red : B →ₐ[A] Bbar)
    (hred : IsBaseChange (IsLocalRing.ResidueField A) red.toLinearMap)
    {u0 : B} {uBar : Bbar} (hu0 : red u0 = uBar)
    [CommRing (Algebra.adjoin A ({u0} : Set B))]
    [CommRing (Algebra.adjoin A ({uBar} : Set Bbar))]
    (huBar : IsIdempotentElem uBar) :
    ∃ e : Algebra.adjoin A ({u0} : Set B),
      (Polynomial.X ^ 2 - Polynomial.X : Polynomial A).IsRoot e ∧
        adjoin_singleton_codRestrict (A := A) (B := B) (Bbar := Bbar) red hu0 e =
          (⟨uBar, Algebra.self_mem_adjoin_singleton A uBar⟩ :
            Algebra.adjoin A ({uBar} : Set Bbar)) := by
  -- Route correction: the source proof only needs one Hensel step for the canonical reduced
  -- generator of `A[uBar]`, not a lift for an arbitrary quotient idempotent class.
  let S := Algebra.adjoin A ({u0} : Set B)
  let I : Ideal S := (IsLocalRing.maximalIdeal A).map (algebraMap A S)
  let fS : Polynomial S := (Polynomial.X ^ 2 - Polynomial.X : Polynomial A).map (algebraMap A S)
  let redS := adjoin_singleton_codRestrict (A := A) (B := B) (Bbar := Bbar) red hu0
  let a0 : S := ⟨u0, Algebra.self_mem_adjoin_singleton A u0⟩
  obtain ⟨hEval, hDeriv⟩ :=
    adjoin_singleton_generator_hensel_data_map_maximalIdeal
      (A := A) (B := B) (Bbar := Bbar) red hred hu0 huBar
  have hEval :
      fS.eval a0 ∈ I := by
    -- The new helper packages the exact Hensel membership goal over the normalized source ideal.
    simpa [S, I, fS, Polynomial.aeval_def, Polynomial.aeval_map_algebraMap] using hEval
  have hDeriv :
      IsUnit
        (Ideal.Quotient.mk
          I
          (fS.derivative.eval a0)) := by
    -- The same packaged helper records the derivative-unit hypothesis over the normalized ideal.
    simpa [S, I, fS, Polynomial.aeval_def, Polynomial.derivative_map,
      Polynomial.aeval_map_algebraMap] using hDeriv
  obtain ⟨e, he_root, he_mem⟩ :=
    adjoin_singleton_root_lift_of_hensel_data
      (A := A) (B := B) (u0 := u0)
      hEval
      hDeriv
  refine ⟨e, ?_, ?_⟩
  · -- Forgetting the coefficient extension identifies the lifted root with a root of `X^2 - X`
    -- over the original base ring `A`.
    simpa [fS, Polynomial.IsRoot, Polynomial.eval_map_algebraMap] using he_root
  · -- Rewrite the Hensel congruence modulo `𝔪_A A[u0]` as equality after reduction.
    calc
      redS e = redS a0 := by
        exact adjoin_singleton_codRestrict_eq_of_sub_mem_map_maximalIdeal
          (A := A) (B := B) (Bbar := Bbar) red hred hu0 he_mem
      _ =
          (⟨uBar, Algebra.self_mem_adjoin_singleton A uBar⟩ :
            Algebra.adjoin A ({uBar} : Set Bbar)) := by
              simpa [S, redS, a0] using
                adjoin_singleton_codRestrict_self
                  (A := A) (B := B) (Bbar := Bbar) red hu0

-- Route correction: the arbitrary quotient-idempotent detour has been removed. The remaining
-- frontier is now the single generator Hensel step in `A[u0]`, after which the singleton-adjoin
-- comparison is explicit.
/-- Helper for Exercise 14-14.4-6: the source-faithful core step is the canonical-generator case,
where the chosen downstairs generator is itself idempotent. -/
theorem adjoin_singleton_lifts_idempotent_generator
    (red : B →ₐ[A] Bbar)
    (hred : IsBaseChange (IsLocalRing.ResidueField A) red.toLinearMap)
    {u0 : B} {uBar : Bbar} (hu0 : red u0 = uBar)
    (huBar : IsIdempotentElem uBar) :
    ∃ u : Algebra.adjoin A ({u0} : Set B),
      IsIdempotentElem u ∧
        adjoin_singleton_codRestrict (A := A) (B := B) (Bbar := Bbar) red hu0 u =
          ⟨uBar, Algebra.self_mem_adjoin_singleton A uBar⟩ := by
  obtain ⟨u, hu_root, hu_red⟩ :=
    adjoin_singleton_generator_root_lift_X_sq_sub_X
      (A := A) (B := B) (Bbar := Bbar) red hred hu0 huBar
  have hu : IsIdempotentElem u := by
    -- For the universal polynomial `X^2 - X`, being a root is exactly the idempotent relation.
    rw [IsIdempotentElem]
    exact sub_eq_zero.mp <| by
      simpa [Polynomial.IsRoot, pow_two] using hu_root
  exact ⟨u, hu, hu_red⟩

/-- Helper for Exercise 14-14.4-6: an idempotent point of the residue singleton-adjoin algebra
`A[uBar]` should lift to an idempotent point of `A[u0]` along the restricted residue map. -/
theorem adjoin_singleton_lifts_idempotent_point
    (red : B →ₐ[A] Bbar)
    (hred : IsBaseChange (IsLocalRing.ResidueField A) red.toLinearMap)
    {u0 : B} {uBar : Bbar} (hu0 : red u0 = uBar) :
    ∀ xbar : Algebra.adjoin A ({uBar} : Set Bbar),
      IsIdempotentElem xbar →
        ∃ x : Algebra.adjoin A ({u0} : Set B),
          IsIdempotentElem x ∧
            adjoin_singleton_codRestrict (A := A) (B := B) (Bbar := Bbar) red hu0 x = xbar := by
  intro xbar hxbar
  obtain ⟨x0, hx0_mem, hx0_red⟩ :=
    exists_preimage_mem_adjoin_singleton_of_lift
      (A := A) (B := B) (Bbar := Bbar) red hu0 xbar.2
  have hxbar_val : IsIdempotentElem xbar.1 := by
    -- Forgetting from the singleton-adjoin algebra to `Bbar` preserves the idempotent equation.
    simpa [IsIdempotentElem] using congrArg Subtype.val hxbar.eq
  obtain ⟨xlift, hxlift, hxliftRed⟩ :=
    adjoin_singleton_lifts_idempotent_generator
      (A := A) (B := B) (Bbar := Bbar) red hred hx0_red hxbar_val
  have hle :
      Algebra.adjoin A ({x0} : Set B) ≤ Algebra.adjoin A ({u0} : Set B) :=
    adjoin_singleton_le_of_mem_adjoin_singleton (A := A) hx0_mem
  let x : Algebra.adjoin A ({u0} : Set B) := ⟨xlift.1, hle xlift.2⟩
  have hxIdem : IsIdempotentElem x := by
    -- The lifted point is idempotent before and after viewing it inside the larger subalgebra.
    simpa [x, IsIdempotentElem] using congrArg Subtype.val hxlift.eq
  have hxRed :
      adjoin_singleton_codRestrict (A := A) (B := B) (Bbar := Bbar) red hu0 x = xbar := by
    -- Both reductions have the same underlying value in `Bbar`.
    apply Subtype.ext
    simpa [x, adjoin_singleton_codRestrict_apply] using congrArg Subtype.val hxliftRed
  exact ⟨x, hxIdem, hxRed⟩

-- Route correction: the open frontier is now the source-faithful singleton-adjoin Hensel step in
-- `A[u0]`, but the reconstruction of the lifted map is now isolated in
-- `x_sq_sub_X_standardEtale_hom_lift_of_lifted_point`.
/-- Helper for Exercise 14-14.4-6: evaluating a lifted map from the universal standard-etale
algebra at `X` recovers the desired idempotent generator. -/
theorem lifted_standard_etale_X_gives_generator_lift
    (red : B →ₐ[A] Bbar)
    {u0 : B} {uBar : Bbar} (hu0 : red u0 = uBar)
    (huBar : IsIdempotentElem uBar)
    (φbar : (x_sq_sub_X_standardEtalePair (A := A)).Ring →ₐ[A]
      Algebra.adjoin A ({uBar} : Set Bbar))
    (hφbarX : φbar (x_sq_sub_X_standardEtalePair (A := A)).X =
      (⟨uBar, Algebra.self_mem_adjoin_singleton A uBar⟩ :
        Algebra.adjoin A ({uBar} : Set Bbar)))
    (φ : (x_sq_sub_X_standardEtalePair (A := A)).Ring →ₐ[A]
      Algebra.adjoin A ({u0} : Set B))
    (hφ :
      (adjoin_singleton_codRestrict (A := A) (B := B) (Bbar := Bbar) red hu0).comp φ = φbar) :
    IsIdempotentElem (φ (x_sq_sub_X_standardEtalePair (A := A)).X) ∧
      adjoin_singleton_codRestrict (A := A) (B := B) (Bbar := Bbar) red hu0
          (φ (x_sq_sub_X_standardEtalePair (A := A)).X) =
        ⟨uBar, Algebra.self_mem_adjoin_singleton A uBar⟩ := by
  let P := x_sq_sub_X_standardEtalePair (A := A)
  have hxMap : P.HasMap (φ P.X) := by
    -- A map out of the universal standard-etale algebra automatically records a valid point.
    simpa [P] using (P.homEquiv φ).2
  have hxIdem : IsIdempotentElem (φ P.X) := by
    -- For `X^2 - X`, the `HasMap` predicate is exactly the idempotent relation.
    exact
      (x_sq_sub_X_standardEtale_hasMap_iff_isIdempotentElem
        (A := A) (x := φ P.X)).1 hxMap
  have hX :
      adjoin_singleton_codRestrict (A := A) (B := B) (Bbar := Bbar) red hu0 (φ P.X) =
        ⟨uBar, Algebra.self_mem_adjoin_singleton A uBar⟩ := by
    -- Evaluate the equality of algebra maps at the universal generator `X`.
    have hφX := congrArg (fun ψ => ψ P.X) hφ
    simpa [P, hφbarX] using hφX
  exact ⟨hxIdem, hX⟩

/-- Helper for Exercise 14-14.4-6: any closed-fiber point of the universal standard-etale algebra
for `X^2 - X` should lift along the singleton-adjoin residue-field base change. -/
theorem x_sq_sub_X_standardEtale_hom_lifts_along_residueField_baseChange
    (red : B →ₐ[A] Bbar)
    (hred : IsBaseChange (IsLocalRing.ResidueField A) red.toLinearMap)
    {u0 : B} {uBar : Bbar} (hu0 : red u0 = uBar) :
    ∀ φbar : (x_sq_sub_X_standardEtalePair (A := A)).Ring →ₐ[A]
        Algebra.adjoin A ({uBar} : Set Bbar),
      ∃ φ : (x_sq_sub_X_standardEtalePair (A := A)).Ring →ₐ[A]
          Algebra.adjoin A ({u0} : Set B),
        (adjoin_singleton_codRestrict (A := A) (B := B) (Bbar := Bbar) red hu0).comp φ = φbar := by
  let P := x_sq_sub_X_standardEtalePair (A := A)
  intro φbar
  have hxbarMap : P.HasMap (φbar P.X) := by
    -- The image of `X` under any map from `P.Ring` is, by definition, a valid point of `P`.
    simpa [P] using (P.homEquiv φbar).2
  have hxbar : IsIdempotentElem (φbar P.X) := by
    -- For the universal idempotent presentation, valid points are exactly idempotents.
    exact
      (x_sq_sub_X_standardEtale_hasMap_iff_isIdempotentElem
        (A := A) (x := φbar P.X)).1 hxbarMap
  obtain ⟨x, hx, hxred⟩ :=
    adjoin_singleton_lifts_idempotent_point
      (A := A) (B := B) (Bbar := Bbar) red hred hu0 (φbar P.X) hxbar
  -- A lifted point determines a lifted algebra map by the universal property of `P`.
  exact
    x_sq_sub_X_standardEtale_hom_lift_of_lifted_point
      (A := A) (redS := adjoin_singleton_codRestrict
        (A := A) (B := B) (Bbar := Bbar) red hu0)
      (φbar := φbar) (x := x) hx hxred

-- Route correction: the ambient theorem is now reduced to one source-faithful commutative lifting
-- statement inside `A[u0] → A[uBar]`, phrased through the universal standard-etale algebra of
-- `X^2 - X`.
/-- Helper for Exercise 14-14.4-6: the closed-fiber point of the universal idempotent
standard-etale algebra determined by `uBar` should lift along the singleton-adjoin reduction map. -/
theorem standard_etale_point_lifts_along_adjoin_singleton_reduction
    (red : B →ₐ[A] Bbar)
    (hred : IsBaseChange (IsLocalRing.ResidueField A) red.toLinearMap)
    {u0 : B} {uBar : Bbar} (hu0 : red u0 = uBar) :
    ∀ xbar : Algebra.adjoin A ({uBar} : Set Bbar),
      IsIdempotentElem xbar →
        ∃ x : Algebra.adjoin A ({u0} : Set B),
          IsIdempotentElem x ∧
            adjoin_singleton_codRestrict (A := A) (B := B) (Bbar := Bbar) red hu0 x = xbar := by
  -- This is exactly the singleton-adjoin point-lifting statement proved above.
  simpa using
    adjoin_singleton_lifts_idempotent_point
      (A := A) (B := B) (Bbar := Bbar) red hred hu0

/-- Helper for Exercise 14-14.4-6: inside the singleton-generated algebra `A[u0]`, an idempotent
of the residue singleton-adjoin algebra `A[uBar]` lifts to an idempotent upstairs. -/
theorem finite_singleton_adjoin_idempotent_lift
    (red : B →ₐ[A] Bbar)
    (hred : IsBaseChange (IsLocalRing.ResidueField A) red.toLinearMap)
    {u0 : B} {uBar : Bbar} (hu0 : red u0 = uBar)
    (huBar : IsIdempotentElem uBar) :
    ∃ u : Algebra.adjoin A ({u0} : Set B),
      IsIdempotentElem u ∧
        adjoin_singleton_codRestrict (A := A) (B := B) (Bbar := Bbar) red hu0 u =
          ⟨uBar, Algebra.self_mem_adjoin_singleton A uBar⟩ := by
  -- This is just the canonical-generator lift with the singleton-adjoin finiteness hypotheses.
  simpa using
    adjoin_singleton_lifts_idempotent_generator
      (A := A) (B := B) (Bbar := Bbar) red hred hu0 huBar

/-- Helper for Exercise 14-14.4-6: the closed-fiber point of the universal idempotent
standard-etale algebra determined by `uBar` lifts along the singleton-adjoin reduction map. -/
theorem henselian_lift_idempotent_via_standard_etale_X_sq_sub_X
    (red : B →ₐ[A] Bbar)
    (hred : IsBaseChange (IsLocalRing.ResidueField A) red.toLinearMap)
    {u0 : B} {uBar : Bbar} (hu0 : red u0 = uBar)
    (huBar : IsIdempotentElem uBar) :
    ∃ u : Algebra.adjoin A ({u0} : Set B),
      IsIdempotentElem u ∧
        adjoin_singleton_codRestrict (A := A) (B := B) (Bbar := Bbar) red hu0 u =
          ⟨uBar, Algebra.self_mem_adjoin_singleton A uBar⟩ := by
  -- The standard-etale wrapper does not add new work beyond the singleton-adjoin lift.
  simpa using
    finite_singleton_adjoin_idempotent_lift
      (A := A) (B := B) (Bbar := Bbar) red hred hu0 huBar

-- Route correction: the obvious Hensel argument for `X^2 - X` only applies to commutative target
-- algebras, while the present statement is genuinely noncommutative. The remaining proof needs a
-- semiperfect/idempotent-lifting theorem for finite `A`-algebras over a henselian local ring.
-- Proof sketch: identify `Bbar` with the residue-field base change of `B`; over a henselian local
-- ring, an idempotent of the reduction satisfies a monic polynomial `X^2 - X`, and Hensel lifting
-- produces an idempotent lift in the finite free algebra `B`.
/-- Exercise 14-14.4-6 (1): source part (a). If `B` is a finite free `A`-algebra and `Bbar`
plays the role of the reduction `B / 𝔪B` via a residue-field base change map, then every
idempotent of `Bbar` lifts to an idempotent of `B`. -/
theorem idempotent_lifts_along_residueFieldReduction
    (red : B →ₐ[A] Bbar)
    (hred : IsBaseChange (IsLocalRing.ResidueField A) red.toLinearMap)
    (uBar : Bbar) (huBar : IsIdempotentElem uBar) :
    ∃ u : B, IsIdempotentElem u ∧ red u = uBar := by
  obtain ⟨u0, hu0⟩ := isBaseChange_surjective (A := A) (B := B) (Bbar := Bbar) red hred uBar
  obtain ⟨u, hu, huRed⟩ :=
    henselian_lift_idempotent_via_standard_etale_X_sq_sub_X
      (A := A) (B := B) (Bbar := Bbar) red hred hu0 huBar
  refine ⟨u.1, ?_, ?_⟩
  · -- Forgetting from `A[u0]` to `B` preserves the idempotent equation.
    simpa [IsIdempotentElem] using congrArg Subtype.val hu
  · -- Forgetting from `A[uBar]` to `Bbar` turns the restricted reduction into the ambient one.
    simpa [adjoin_singleton_codRestrict_apply] using congrArg Subtype.val huRed

end Henselian

variable [Module.Projective A[G] P] [Module.Finite A P]
variable {Pbar : Type x} [AddCommGroup Pbar] [Module (IsLocalRing.ResidueField A) Pbar]
variable [Module A Pbar] [IsScalarTower A (IsLocalRing.ResidueField A) Pbar]
variable [Module (IsLocalRing.ResidueField A)[G] Pbar]
variable [IsScalarTower (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A)[G] Pbar]

local notation "ρA" => (Representation.ofModule' P : Representation A G P)
local notation "ρkA" => (Representation.ofModule' Pbar : Representation kA G Pbar)
local notation "EndA" => Representation.IntertwiningMap ρA ρA
local notation "EndkA" => Representation.IntertwiningMap ρkA ρkA

noncomputable local instance : Algebra A EndkA :=
  Algebra.compHom EndkA (algebraMap A kA)

noncomputable local instance : IsScalarTower A kA EndkA :=
  IsScalarTower.of_algebraMap_smul fun a u ↦ by
    ext x
    rfl

-- Proof sketch: pass from equivariant endomorphisms to `A[G]`-linear endomorphisms using
-- `IntertwiningMap.equivAlgEnd (ofModule P)`, then use that a finite projective module over the
-- local ring `A` is free and that endomorphisms of a finite free module are free.
/-- Exercise 14-14.4-6 (2): source part (b). For a projective `A[G]`-module `P` of finite
`A`-rank, the equivariant endomorphism algebra `End^G(P)` is free as an `A`-module. -/
theorem equivariantEndomorphismAlgebra_free
    (P : Type w) [AddCommGroup P] [Module A P] [Module A[G] P] [IsScalarTower A A[G] P]
    [Module.Projective A[G] P] [Module.Finite A P] :
    Module.Free A
      (Representation.IntertwiningMap
        (Representation.ofModule' P : Representation A G P)
        (Representation.ofModule' P : Representation A G P)) := by
  let ρ : Representation A G P := Representation.ofModule' P
  letI : Module.Free A (P →ₗ[A[G]] P) :=
    groupAlgebra_endomorphismModule_free (A := A) (G := G) P
  obtain ⟨e⟩ := nonempty_ofModule'_asModuleLinearEquiv (G := G) A P
  let eEnd : Module.End A[G] ρ.asModule ≃ₐ[A] Module.End A[G] P :=
    LinearEquiv.conjAlgEquiv A e
  have endEquiv :
      Representation.IntertwiningMap ρ ρ ≃ₗ[A] (P →ₗ[A[G]] P) := by
    simpa [ρ] using
      ((Representation.IntertwiningMap.equivAlgEnd (ρ := ρ)).toLinearEquiv.trans
        eEnd.toLinearEquiv)
  exact Module.Free.of_equiv endEquiv.symm

namespace LinearMap.IsResidueFieldReduction

/-- Helper for Exercise 14-14.4-6: the standard finite free `A[G]`-module is finite over `A`. -/
theorem finite_free_groupAlgebra_moduleFinite
    [Finite G]
    (n : Nat) :
    Module.Finite A (Fin n → A[G]) := by
  let _ : Module.Finite A A[G] := MonoidAlgebra.moduleFinite
  let _ : Module.Finite A[G] (Fin n → A[G]) :=
    Module.Finite.of_basis (Pi.basisFun (A[G]) (Fin n))
  exact Module.Finite.trans A[G] (Fin n → A[G])

/-- Helper for Exercise 14-14.4-6: the standard finite free ambient module carries the finiteness
instance needed by the restricted endomorphism reduction API. -/
local instance finite_free_groupAlgebra_moduleFinite_inst
    [Finite G]
    (n : Nat) :
    Module.Finite A (Fin n → A[G]) :=
  finite_free_groupAlgebra_moduleFinite (A := A) (G := G) n

/-- Helper for Exercise 14-14.4-6: a range inside a reduced `kA[G]`-module inherits the scalar
tower from `A → kA`. -/
local instance range_restricted_groupAlgebra_module
    {M : Type*} [AddCommGroup M] [Module kA M] [Module kA[G] M]
    [IsScalarTower kA kA[G] M]
    (e : Module.End kA[G] M) :
    Module A (LinearMap.range e) :=
  Module.compHom (LinearMap.range e) (algebraMap A kA)

/-- Helper for Exercise 14-14.4-6: a range inside a reduced `kA[G]`-module inherits the scalar
tower from `A → kA`. -/
local instance range_restricted_groupAlgebra_isScalarTower
    {M : Type*} [AddCommGroup M] [Module kA M]
    [Module kA[G] M] [IsScalarTower kA kA[G] M]
    (e : Module.End kA[G] M) :
    IsScalarTower A kA (LinearMap.range e) :=
  IsScalarTower.of_algebraMap_smul fun a x ↦ by
    apply Subtype.ext
    rfl

/-- Exercise 14-14.4-6 (3): source part (b). The canonical reduction map on equivariant
endomorphisms exhibits `End^G(Pbar)` as the residue-field base change of `End^G(P)`. -/
theorem endAlgHom_isBaseChange
    [Finite G]
    {f : P →ₗ[A] Pbar}
    (hf : f.IsResidueFieldReduction G) :
    IsBaseChange kA hf.endAlgHom.toLinearMap := by
  exact endAlgHom_isBaseChange_of_restricted (A := A) (G := G) hf
    (restricted_groupAlgebraEnd_isBaseChange (A := A) (G := G) hf)

/-- Helper for Exercise 14-14.4-6: the range map respects the inherited `A`-scalar action on the
projector ranges after forgetting to the ambient reduced module. -/
lemma range_lifted_projector_map_smul
    {f : P →ₗ[A] Pbar}
    (hf : f.IsResidueFieldReduction G)
    {e : Module.End A[G] P}
    {eBar : Module.End kA[G] Pbar}
    (heRed : endHom_restrict_groupAlgebraLinearMap (A := A) (G := G) hf e = eBar)
    (a : A) (x : LinearMap.range e) :
    ((range_lifted_projector_map (A := A) (G := G) hf heRed (a • x) : LinearMap.range eBar) :
      Pbar) =
      ((a • range_lifted_projector_map (A := A) (G := G) hf heRed x : LinearMap.range eBar) :
        Pbar) := by
  -- Forget both range points to `Pbar`; then the statement is just `A`-linearity of the ambient
  -- residue-field reduction map.
  change f (a • x.1) =
    ((a • range_lifted_projector_map (A := A) (G := G) hf heRed x : LinearMap.range eBar) : Pbar)
  rw [f.map_smul]
  change a • f x.1 = (algebraMap A kA a) • f x.1
  symm
  simpa [IsLocalRing.ResidueField.algebraMap_eq] using
    (IsScalarTower.algebraMap_smul kA a (f x.1))

/-- Helper for Exercise 14-14.4-6: the range map also respects the distinguished
`MonoidAlgebra.of` actions after forgetting to the ambient reduced module. -/
lemma range_lifted_projector_map_monoidAlgebra_of
    {f : P →ₗ[A] Pbar}
    (hf : f.IsResidueFieldReduction G)
    {e : Module.End A[G] P}
    {eBar : Module.End kA[G] Pbar}
    (heRed : endHom_restrict_groupAlgebraLinearMap (A := A) (G := G) hf e = eBar)
    (g : G) (x : LinearMap.range e) :
    ((range_lifted_projector_map (A := A) (G := G) hf heRed
        ((MonoidAlgebra.of A G g) • x) : LinearMap.range eBar) : Pbar) =
      (((MonoidAlgebra.of kA G g) •
        range_lifted_projector_map (A := A) (G := G) hf heRed x : LinearMap.range eBar) :
        Pbar) := by
  -- Forgetting both range points to `Pbar` reduces the claim to equivariance of the ambient
  -- residue-field reduction map on the monoid generators.
  simpa [range_lifted_projector_map] using hf.map_monoidAlgebra_of g x.1

/-- Helper for Exercise 14-14.4-6: if `e` reduces to `eBar`, then the induced map from the lifted
projector range to the reduced projector range is the ambient reduction restricted to `range e`. -/
noncomputable def range_lifted_projector_linearMap
    {f : P →ₗ[A] Pbar}
    (hf : f.IsResidueFieldReduction G)
    {e : Module.End A[G] P}
    {eBar : Module.End kA[G] Pbar}
    (heRed : endHom_restrict_groupAlgebraLinearMap (A := A) (G := G) hf e = eBar) :
    LinearMap.range e →ₗ[A] LinearMap.range eBar :=
  -- Package the already-defined function on ranges as an `A`-linear map.
  { toFun := fun x ↦
      range_lifted_projector_map (A := A) (G := G) hf heRed x
    map_add' := by
      intro x y
      apply Subtype.ext
      simp [range_lifted_projector_map]
    map_smul' := by
      intro a x
      apply Subtype.ext
      simpa using
        range_lifted_projector_map_smul (A := A) (G := G) hf heRed a x }

/-- Helper for Exercise 14-14.4-6: evaluating the reduced projector on the reduction of an ambient
vector agrees with first projecting upstairs and then reducing. -/
theorem range_lifted_projector_rangeRestrict_apply
    {f : P →ₗ[A] Pbar}
    (hf : f.IsResidueFieldReduction G)
    {e : Module.End A[G] P}
    {eBar : Module.End kA[G] Pbar}
    (heRed : endHom_restrict_groupAlgebraLinearMap (A := A) (G := G) hf e = eBar)
    (x : P) :
    eBar.rangeRestrict (f x) =
      range_lifted_projector_linearMap (A := A) (G := G) hf heRed ⟨e x, ⟨x, rfl⟩⟩ := by
  -- Rewrite both range elements to their ambient values and use the commuting reduction square.
  apply Subtype.ext
  simpa [range_lifted_projector_linearMap, range_lifted_projector_map, heRed] using
    (endHom_restrict_groupAlgebraLinearMap_comp_apply (A := A) (G := G) hf e x)

/-- Helper for Exercise 14-14.4-6: the induced map on lifted projector ranges is surjective. This
is the verified prefix of the intended stronger residue-field base-change statement. -/
theorem range_lifted_projector_linearMap_surjective
    {f : P →ₗ[A] Pbar}
    (hf : f.IsResidueFieldReduction G)
    {e : Module.End A[G] P}
    {eBar : Module.End kA[G] Pbar}
    (heRed : endHom_restrict_groupAlgebraLinearMap (A := A) (G := G) hf e = eBar) :
    Function.Surjective (range_lifted_projector_linearMap (A := A) (G := G) hf heRed) := by
  -- The packaged linear map has the same underlying function as the raw range map proved
  -- surjective in the helper bridge.
  simpa [range_lifted_projector_linearMap] using
    (range_lifted_projector_map_surjective (A := A) (G := G) hf heRed)

/-- Helper for Exercise 14-14.4-6: once the lifted projector `e` is idempotent, every
`A`-linear map out of `range e` descends uniquely along the reduction map to `range eBar`. -/
theorem range_lifted_projector_lift_unique
    {f : P →ₗ[A] Pbar}
    (hf : f.IsResidueFieldReduction G)
    {e : Module.End A[G] P}
    (he : IsIdempotentElem e)
    {eBar : Module.End kA[G] Pbar}
    (heRed : endHom_restrict_groupAlgebraLinearMap (A := A) (G := G) hf e = eBar) :
    ∀ (Q : Type*) [AddCommMonoid Q] [Module A Q] [Module kA Q] [IsScalarTower A kA Q]
      (g : LinearMap.range e →ₗ[A] Q),
      ∃ g' : LinearMap.range eBar →ₗ[kA] Q,
        ∀ x, g' (range_lifted_projector_linearMap (A := A) (G := G) hf heRed x) = g x := by
  intro Q _ _ _ _ g
  let gAmbient : P →ₗ[A] Q := g.comp (e.rangeRestrict.restrictScalars A)
  let gBarAmbient : Pbar →ₗ[kA] Q := hf.1.lift gAmbient
  let gBar : LinearMap.range eBar →ₗ[kA] Q :=
    { toFun := fun x ↦ gBarAmbient x.1
      map_add' := by
        intro x y
        simp [gBarAmbient]
      map_smul' := by
        intro a x
        change gBarAmbient ((a • x : LinearMap.range eBar).1) = a • gBarAmbient x.1
        simpa using gBarAmbient.map_smul a x.1 }
  refine ⟨gBar, ?_⟩
  -- The descended map agrees with the original one on `range e`.
  intro x
  change gBarAmbient (f x.1) = g x
  rw [hf.1.lift_eq gAmbient x.1]
  simpa [gAmbient] using congrArg g (range_element_fixed_of_isIdempotentElem e he x)

/-- Helper for Exercise 14-14.4-6: reducing an idempotent projector produces an idempotent reduced
projector. -/
theorem range_lifted_projector_reduced_isIdempotentElem
    {f : P →ₗ[A] Pbar}
    (hf : f.IsResidueFieldReduction G)
    {e : Module.End A[G] P}
    (he : IsIdempotentElem e)
    {eBar : Module.End kA[G] Pbar}
    (heRed : endHom_restrict_groupAlgebraLinearMap (A := A) (G := G) hf e = eBar) :
    IsIdempotentElem eBar := by
  have heRedAlg :
      endHom_restrict_groupAlgebraAlgHom (A := A) (G := G) hf e = eBar := by
    simpa [endHom_restrict_groupAlgebraAlgHom_toLinearMap (A := A) (G := G) hf] using heRed
  rw [← heRedAlg]
  exact IsIdempotentElem.map he (endHom_restrict_groupAlgebraAlgHom (A := A) (G := G) hf)

/-- Helper for Exercise 14-14.4-6: if a lifted projector is idempotent, then the induced map on
its range is again a residue-field base change. -/
theorem range_lifted_projector_isBaseChange
    {f : P →ₗ[A] Pbar}
    (hf : f.IsResidueFieldReduction G)
    {e : Module.End A[G] P}
    (he : IsIdempotentElem e)
    {eBar : Module.End kA[G] Pbar}
    (heRed : endHom_restrict_groupAlgebraLinearMap (A := A) (G := G) hf e = eBar) :
    IsBaseChange kA (range_lifted_projector_linearMap (A := A) (G := G) hf heRed) := by
  -- The source-faithful range map is a base change because every `A`-linear map out of `range e`
  -- descends uniquely along it: existence is `range_lifted_projector_lift_unique`, and
  -- uniqueness follows from surjectivity of the range map.
  apply IsBaseChange.of_lift_unique
  intro Q _ _ _ _ g
  obtain ⟨g', hg'⟩ :=
    range_lifted_projector_lift_unique
      (A := A) (G := G) hf he heRed Q g
  refine ⟨g', ?_, ?_⟩
  · -- The descended map restricts back to the original `A`-linear map on `range e`.
    ext x
    exact hg' x
  · intro g'' hg''
    -- Surjectivity of the range map forces any two descended maps to agree on all of `range eBar`.
    ext y
    obtain ⟨x, rfl⟩ :=
      range_lifted_projector_linearMap_surjective
        (A := A) (G := G) hf heRed y
    have hg''x := LinearMap.congr_fun hg'' x
    calc
      g'' (range_lifted_projector_linearMap (A := A) (G := G) hf heRed x) = g x := hg''x
      _ = g' (range_lifted_projector_linearMap (A := A) (G := G) hf heRed x) :=
        (hg' x).symm

/-- Helper for Exercise 14-14.4-6: if a lifted projector is idempotent, then the induced map on
its range is itself a residue-field reduction of `A[G]`-modules. -/
theorem range_lifted_projector_isResidueFieldReduction
    {f : P →ₗ[A] Pbar}
    (hf : f.IsResidueFieldReduction G)
    {e : Module.End A[G] P}
    (he : IsIdempotentElem e)
    {eBar : Module.End kA[G] Pbar}
    (heRed : endHom_restrict_groupAlgebraLinearMap (A := A) (G := G) hf e = eBar) :
    (range_lifted_projector_linearMap (A := A) (G := G) hf heRed).IsResidueFieldReduction G := by
  constructor
  · -- The range map already satisfies the universal base-change property proved above.
    exact range_lifted_projector_isBaseChange (A := A) (G := G) hf he heRed
  · -- Equivariance is checked on monoid generators and then on underlying vectors of `range eBar`.
    refine Representation.IsIntertwiningMap.mk ?_
    intro g x
    -- After forgetting the range subtype, this is exactly the monoid-generator equivariance of
    -- the raw range reduction map.
    change
      (range_lifted_projector_linearMap (A := A) (G := G) hf heRed)
          ((MonoidAlgebra.of A G g) • x) =
        (MonoidAlgebra.mapRingHom G (algebraMap A kA) (MonoidAlgebra.of A G g)) •
          (range_lifted_projector_linearMap (A := A) (G := G) hf heRed x)
    apply Subtype.ext
    simpa [range_lifted_projector_linearMap, MonoidAlgebra.of_apply] using
      range_lifted_projector_map_monoidAlgebra_of (A := A) (G := G) hf heRed g x

/-- Helper for Exercise 14-14.4-6: the reduction of the lifted projector range is canonically
equivalent to the original reduced projector range. -/
theorem range_lifted_projector_reduction_nonempty_linearEquiv
    [Finite G]
    {f : P →ₗ[A] Pbar}
    (hf : f.IsResidueFieldReduction G)
    {e : Module.End A[G] P}
    (he : IsIdempotentElem e)
    {eBar : Module.End kA[G] Pbar}
    (heRed : endHom_restrict_groupAlgebraLinearMap (A := A) (G := G) hf e = eBar) :
    Nonempty (((kA ⊗[A] LinearMap.range e) ≃ₗ[kA[G]] LinearMap.range eBar)) := by
  letI : Module.Finite A (LinearMap.range e) := Module.Finite.range (e.restrictScalars A)
  have hproj :
      Module.Projective A[G] (LinearMap.range e) :=
    LinearMap.IsResidueFieldReduction.projective_range_of_idempotent_endomorphism_general e he
  have hself : Nonempty (LinearMap.range e ≃ₗ[A[G]] LinearMap.range e) :=
    ⟨LinearEquiv.refl A[G] (LinearMap.range e)⟩
  -- Compare the canonical tensor-product reduction of `range e` with the explicit reduced range
  -- map just proved to be a residue-field reduction.
  exact
    (projective_monoidAlgebra_nonempty_linearEquiv_iff_of_isResidueFieldReduction
      (Λ := A) (G := G)
      (P := LinearMap.range e)
      (Pbar := kA ⊗[A] LinearMap.range e)
      (f := TensorProduct.mk A kA (LinearMap.range e) 1)
      (hf := MonoidAlgebra.tensorProduct_mk_isResidueFieldReduction
        (Λ := A) (G := G) (P := LinearMap.range e))
      (P' := LinearMap.range e)
      (Pbar' := LinearMap.range eBar)
      (f' := range_lifted_projector_linearMap (A := A) (G := G) hf heRed)
      (hf' := range_lifted_projector_isResidueFieldReduction
        (A := A) (G := G) hf he heRed)
      hproj hproj).1 hself

section Henselian

variable [HenselianLocalRing A]

/-- Helper for Exercise 14-14.4-6: a single reduced `A[G]`-linear idempotent endomorphism lifts to
an idempotent endomorphism upstairs. -/
theorem endHom_restrict_groupAlgebraLinearMap_lifts_idempotent
    {f : P →ₗ[A] Pbar}
    (hf : f.IsResidueFieldReduction G)
    (uBar : Pbar →ₗ[kA[G]] Pbar) (huBar : IsIdempotentElem uBar) :
    ∃ u : P →ₗ[A[G]] P, IsIdempotentElem u ∧
      endHom_restrict_groupAlgebraLinearMap (A := A) (G := G) hf u = uBar := by
  letI : Module A (Pbar →ₗ[kA[G]] Pbar) :=
    Module.compHom (Pbar →ₗ[kA[G]] Pbar) (algebraMap A kA)
  letI : Algebra A (Pbar →ₗ[kA[G]] Pbar) :=
    Algebra.compHom (Pbar →ₗ[kA[G]] Pbar) (algebraMap A kA)
  letI : IsScalarTower A kA (Pbar →ₗ[kA[G]] Pbar) :=
    IsScalarTower.of_algebraMap_smul fun a u ↦ by
      ext x
      rfl
  letI : Module.Free A (P →ₗ[A[G]] P) :=
    groupAlgebra_endomorphismModule_free (A := A) (G := G) P
  letI : Module.Finite A EndA := equivariantEndomorphismAlgebra_finite (A := A) (G := G) P
  let endEquiv : EndA ≃ₗ[A] (P →ₗ[A[G]] P) :=
    (ofModule'_equivAlgEnd (G := G) A P).toLinearEquiv
  letI : Module.Finite A (P →ₗ[A[G]] P) :=
    Module.Finite.equiv endEquiv
  have hred :
      IsBaseChange kA
        (endHom_restrict_groupAlgebraAlgHom (A := A) (G := G) hf).toLinearMap := by
    simpa [endHom_restrict_groupAlgebraAlgHom_toLinearMap (A := A) (G := G) hf] using
      (LinearMap.IsResidueFieldReduction.restricted_groupAlgebraEnd_isBaseChange
        (A := A) (G := G) hf)
  -- Apply part (1) directly to the ordinary endomorphism ring and its reduction map.
  obtain ⟨u, hu, huRed⟩ :=
    idempotent_lifts_along_residueFieldReduction
      (A := A) (B := P →ₗ[A[G]] P) (Bbar := Pbar →ₗ[kA[G]] Pbar)
      (endHom_restrict_groupAlgebraAlgHom (A := A) (G := G) hf) hred uBar huBar
  refine ⟨u, hu, ?_⟩
  simpa [endHom_restrict_groupAlgebraAlgHom_toLinearMap (A := A) (G := G) hf] using huRed

/-- Helper for Exercise 14-14.4-6: after lifting the first projector in a finite complete
orthogonal family on `Fin (n + 1)`, the tail projectors stay idempotent, remain pairwise
orthogonal, sum to the complementary projector `1 - eBar 0`, and preserve the complementary range
cut out by `1 - eBar 0`. -/
theorem completeOrthogonalIdempotents_tail_on_complement_range
    {n : Nat}
    (eBar : Fin (n + 1) → Pbar →ₗ[kA[G]] Pbar)
    (heBar : CompleteOrthogonalIdempotents eBar) :
    (∀ i : Fin n, IsIdempotentElem (eBar i.succ)) ∧
      Pairwise (fun i j : Fin n => eBar i.succ * eBar j.succ = 0) ∧
      (∑ i : Fin n, eBar i.succ = 1 - eBar 0) ∧
      (∀ i : Fin n, ∀ x ∈ LinearMap.range (1 - eBar 0),
        eBar i.succ x ∈ LinearMap.range (1 - eBar 0)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Each tail term is still one of the original idempotents.
    intro i
    exact heBar.idem i.succ
  · -- Pairwise orthogonality is inherited from the original family by restricting to successor
    -- indices.
    intro i j hij
    exact heBar.ortho ((Fin.succ_injective _).ne hij)
  · -- Completeness on `Fin (n + 1)` rewrites the tail sum as the complementary projector.
    apply eq_sub_iff_add_eq.mpr
    simpa [Fin.sum_univ_succ, add_comm, add_left_comm, add_assoc] using heBar.complete
  · -- Any tail projector lands in the range of `1 - eBar 0` because it is annihilated by `eBar 0`.
    intro i x hx
    refine ⟨eBar i.succ x, ?_⟩
    change (((1 - eBar 0) * eBar i.succ) x = eBar i.succ x)
    have horth : eBar 0 * eBar i.succ = 0 :=
      heBar.ortho (Ne.symm (Fin.succ_ne_zero i))
    rw [sub_mul, one_mul, horth, sub_zero]

/-- Helper for Exercise 14-14.4-6: the successor tail of a complete orthogonal family restricts
to a complete orthogonal family on the complementary range of the head projector. -/
theorem tail_family_on_complement_range
    {n : Nat}
    (eBar : Fin (n + 1) → Pbar →ₗ[kA[G]] Pbar)
    (heBar : CompleteOrthogonalIdempotents eBar) :
    ∃ tail : Fin n → Module.End kA[G] (LinearMap.range (1 - eBar 0)),
      CompleteOrthogonalIdempotents tail ∧
        ∀ i (x : LinearMap.range (1 - eBar 0)),
          ((tail i) x : Pbar) = eBar i.succ x := by
  obtain ⟨htailIdem, htailOrtho, htailSum, htailMem⟩ :=
    completeOrthogonalIdempotents_tail_on_complement_range eBar heBar
  let tail : Fin n → Module.End kA[G] (LinearMap.range (1 - eBar 0)) := fun i ↦
    { toFun := fun x ↦ ⟨eBar i.succ x, htailMem i x x.2⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        simp
      map_smul' := by
        intro a x
        apply Subtype.ext
        simp }
  have htailApply :
      ∀ i (x : LinearMap.range (1 - eBar 0)),
        ((tail i) x : Pbar) = eBar i.succ x := by
    intro i x
    rfl
  refine ⟨tail, ?_, htailApply⟩
  -- Orthogonality and completeness are inherited from the ambient family after restricting to
  -- vectors already lying in `range (1 - eBar 0)`.
  ·
    refine ⟨?_, ?_⟩
    · constructor
      · intro i
        -- Idempotency is checked on underlying vectors and then rewrapped into the range subtype.
        rw [IsIdempotentElem, Module.End.mul_eq_comp]
        ext x
        simpa [htailApply] using congrArg (fun f : Module.End kA[G] Pbar => f x) (htailIdem i).eq
      · intro i j hij
        ext x
        simpa [htailApply] using congrArg (fun f : Module.End kA[G] Pbar => f x) (htailOrtho hij)
    · -- The restricted tail sum acts as the identity on the complementary range because the
      -- ambient tail sum is exactly `1 - eBar 0`.
      ext x
      have hfix :
          (1 - eBar 0).rangeRestrict x = x :=
        LinearMap.IsResidueFieldReduction.range_element_fixed_of_isIdempotentElem
          (1 - eBar 0) (heBar.idem 0).one_sub x
      have hfixVal : (1 - eBar 0) x = x := congrArg Subtype.val hfix
      calc
        (((∑ i, tail i) x : LinearMap.range (1 - eBar 0)) : Pbar)
            = (∑ i : Fin n, eBar i.succ) x := by
              simp [htailApply]
        _ = ((1 - eBar 0) x : Pbar) := by
              rw [htailSum]
        _ = x := hfixVal

/-- Helper for Exercise 14-14.4-6: an endomorphism of the complementary range `range (1 - e)`
extends to an ambient endomorphism by first projecting to the complementary range and then
including back into `P`. -/
noncomputable def complement_range_endomorphism_to_ambient
    (e : P →ₗ[A[G]] P)
    (u : LinearMap.range (1 - e) →ₗ[A[G]] LinearMap.range (1 - e)) :
    P →ₗ[A[G]] P :=
  (LinearMap.range (1 - e)).subtype.comp (u.comp ((1 - e).rangeRestrict))

/-- Helper for Exercise 14-14.4-6: once `e` is idempotent, the ambient extension of an
endomorphism of `range (1 - e)` agrees with the original endomorphism on vectors already lying in
that complementary range. -/
@[simp] theorem complement_range_endomorphism_to_ambient_apply_subtype
    (e : P →ₗ[A[G]] P) (he : IsIdempotentElem e)
    (u : LinearMap.range (1 - e) →ₗ[A[G]] LinearMap.range (1 - e))
    (x : LinearMap.range (1 - e)) :
    complement_range_endomorphism_to_ambient (A := A) (G := G) e u x = u x := by
  -- Idempotency of `e` makes `1 - e` the projector onto the complementary range, so the middle
  -- projector acts trivially on a vector already in that range.
  have hxrestrict : (1 - e).rangeRestrict x = x := by
    exact range_element_fixed_of_isIdempotentElem (1 - e) he.one_sub x
  -- Expand the ambient extension and rewrite the projector on the complementary-range point.
  simpa [complement_range_endomorphism_to_ambient, hxrestrict]

/-- Helper for Exercise 14-14.4-6: ambientizing the identity endomorphism of `range (1 - e)`
recovers the complementary projector `1 - e` upstairs. -/
@[simp] theorem complement_range_endomorphism_to_ambient_one
    (e : P →ₗ[A[G]] P) :
    complement_range_endomorphism_to_ambient (A := A) (G := G) e
        (1 : Module.End A[G] (LinearMap.range (1 - e))) =
      1 - e := by
  -- Expanding the definition shows that the ambient extension of the identity is exactly the
  -- projector `P → range (1 - e) → P`.
  ext x
  rfl

/-- Helper for Exercise 14-14.4-6: once `e` is idempotent, ambientization carries composition on
the complementary range to composition upstairs. -/
@[simp] theorem complement_range_endomorphism_to_ambient_mul
    (e : P →ₗ[A[G]] P) (he : IsIdempotentElem e)
    (u v : Module.End A[G] (LinearMap.range (1 - e))) :
    complement_range_endomorphism_to_ambient (A := A) (G := G) e (u * v) =
      complement_range_endomorphism_to_ambient (A := A) (G := G) e u *
        complement_range_endomorphism_to_ambient (A := A) (G := G) e v := by
  -- After one ambientization, the value already lies in `range (1 - e)`, so the second
  -- ambientization restricts to the original complementary-range endomorphism.
  ext x
  change ↑((u * v) ((1 - e).rangeRestrict x)) =
    (complement_range_endomorphism_to_ambient (A := A) (G := G) e u)
      ((complement_range_endomorphism_to_ambient (A := A) (G := G) e v) x)
  rw [Module.End.mul_eq_comp, LinearMap.comp_apply]
  rw [show
      complement_range_endomorphism_to_ambient (A := A) (G := G) e v x =
        v ((1 - e).rangeRestrict x) by
        rfl]
  rw [complement_range_endomorphism_to_ambient_apply_subtype (A := A) (G := G) e he u
    (v ((1 - e).rangeRestrict x))]

/-- Helper for Exercise 14-14.4-6: the lifted head projector annihilates every ambientized
complementary-range endomorphism on its left. -/
@[simp] theorem head_mul_complement_range_endomorphism_to_ambient
    (e : P →ₗ[A[G]] P) (he : IsIdempotentElem e)
    (u : Module.End A[G] (LinearMap.range (1 - e))) :
    e * complement_range_endomorphism_to_ambient (A := A) (G := G) e u = 0 := by
  -- Any ambientized value lies in `range (1 - e)`, and idempotency makes `e (1 - e) = 0`.
  ext x
  change e (((u ((1 - e).rangeRestrict x) : LinearMap.range (1 - e)) : P)) = 0
  rcases (u ((1 - e).rangeRestrict x)).2 with ⟨y, hy⟩
  rw [← hy]
  have hzero : e * (1 - e) = 0 := by
    ext z
    have hz : e (e z) = e z := by
      simpa [Module.End.mul_eq_comp] using congrArg (fun f : Module.End A[G] P => f z) he.eq
    simpa [sub_eq_add_neg, Module.End.mul_eq_comp, hz]
  simpa [Module.End.mul_eq_comp] using congrArg (fun f : Module.End A[G] P => f y) hzero

/-- Helper for Exercise 14-14.4-6: the lifted head projector annihilates every ambientized
complementary-range endomorphism on its right. -/
@[simp] theorem complement_range_endomorphism_to_ambient_mul_head
    (e : P →ₗ[A[G]] P) (he : IsIdempotentElem e)
    (u : Module.End A[G] (LinearMap.range (1 - e))) :
    complement_range_endomorphism_to_ambient (A := A) (G := G) e u * e = 0 := by
  -- Projecting an `e`-image onto `range (1 - e)` gives zero because `(1 - e) e = 0`.
  ext x
  change ((u ((1 - e).rangeRestrict (e x)) : LinearMap.range (1 - e)) : P) = 0
  have hzero : (1 - e) * e = 0 := by
    ext z
    have hz : e (e z) = e z := by
      simpa [Module.End.mul_eq_comp] using congrArg (fun f : Module.End A[G] P => f z) he.eq
    simpa [sub_eq_add_neg, Module.End.mul_eq_comp, hz]
  have hx : (1 - e).rangeRestrict (e x) = 0 := by
    apply Subtype.ext
    simpa [Module.End.mul_eq_comp] using congrArg (fun f : Module.End A[G] P => f x) hzero
  rw [hx]
  simp

/-- Helper for Exercise 14-14.4-6: adjoining a lifted head projector to an ambientized complete
orthogonal family on `range (1 - e)` produces a complete orthogonal family upstairs. -/
theorem cons_head_and_ambientized_tail_completeOrthogonalIdempotents
    {n : Nat}
    (e : Module.End A[G] P) (he : IsIdempotentElem e)
    (tail : Fin n → Module.End A[G] (LinearMap.range (1 - e)))
    (htail : CompleteOrthogonalIdempotents tail) :
    CompleteOrthogonalIdempotents
      (Fin.cases e
        (fun i ↦ complement_range_endomorphism_to_ambient (A := A) (G := G) e (tail i))) := by
  -- Check the three orthogonality patterns separately: head-tail, tail-head, and tail-tail.
  rw [CompleteOrthogonalIdempotents.iff_ortho_complete]
  refine ⟨?_, ?_⟩
  · intro i j hij
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
    · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
      · exact (hij rfl).elim
      · simpa using
          head_mul_complement_range_endomorphism_to_ambient
            (A := A) (G := G) e he (tail j)
    · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
      · simpa using
          complement_range_endomorphism_to_ambient_mul_head
            (A := A) (G := G) e he (tail i)
      · have hij' : i ≠ j := by
          intro h
          apply hij
          simp [h]
        simpa using
          (show
            complement_range_endomorphism_to_ambient (A := A) (G := G) e (tail i) *
                complement_range_endomorphism_to_ambient (A := A) (G := G) e (tail j) = 0 by
              rw [← complement_range_endomorphism_to_ambient_mul
                (A := A) (G := G) e he (tail i) (tail j), htail.ortho hij']
              simp [complement_range_endomorphism_to_ambient])
  · -- Rewrite the ambientized tail sum as the complementary projector `1 - e`.
    rw [Fin.sum_univ_succ]
    calc
      e + ∑ i, complement_range_endomorphism_to_ambient (A := A) (G := G) e (tail i) =
          e + complement_range_endomorphism_to_ambient (A := A) (G := G) e (∑ i, tail i) := by
            ext x
            simp [complement_range_endomorphism_to_ambient, LinearMap.comp_apply]
      _ = e + (1 - e) := by
            rw [htail.complete, complement_range_endomorphism_to_ambient_one]
      _ = 1 := by
            ext x
            simp

/-- Helper for Exercise 14-14.4-6: reducing a complementary projector is the same as taking the
complement of the reduced projector. -/
theorem endHom_restrict_groupAlgebraLinearMap_one_sub
    {f : P →ₗ[A] Pbar}
    (hf : f.IsResidueFieldReduction G)
    {e : Module.End A[G] P}
    {eBar : Module.End kA[G] Pbar}
    (heRed : endHom_restrict_groupAlgebraLinearMap (A := A) (G := G) hf e = eBar) :
    endHom_restrict_groupAlgebraLinearMap (A := A) (G := G) hf (1 - e) = 1 - eBar := by
  -- Use the transported algebra hom so subtraction and the identity are preserved definitionally.
  have hAlgRed :
      endHom_restrict_groupAlgebraAlgHom (A := A) (G := G) hf e = eBar := by
    simpa [endHom_restrict_groupAlgebraAlgHom_toLinearMap (A := A) (G := G) hf] using heRed
  have hAlg :
      endHom_restrict_groupAlgebraAlgHom (A := A) (G := G) hf (1 - e) = 1 - eBar := by
    calc
      endHom_restrict_groupAlgebraAlgHom (A := A) (G := G) hf (1 - e)
          = 1 - endHom_restrict_groupAlgebraAlgHom (A := A) (G := G) hf e := by
              simp
      _ = 1 - eBar := by rw [hAlgRed]
  -- Then forget the multiplicative structure back to the underlying `A`-linear map.
  ext x
  change endHom_restrict_groupAlgebraAlgHom (A := A) (G := G) hf (1 - e) x = (1 - eBar) x
  rw [hAlg]

/-- Helper for Exercise 14-14.4-6: on a vector already lying in `range (1 - e)`, reducing the
ambient extension of a complementary-range endomorphism agrees with applying the reduced
complementary-range endomorphism after the canonical range reduction map. -/
theorem ambientize_complement_range_endomorphism_reduction_on_subtype
    {f : P →ₗ[A] Pbar}
    (hf : f.IsResidueFieldReduction G)
    {e : Module.End A[G] P}
    (he : IsIdempotentElem e)
    {eBar : Module.End kA[G] Pbar}
    (heRed : endHom_restrict_groupAlgebraLinearMap (A := A) (G := G) hf e = eBar)
    {u : Module.End A[G] (LinearMap.range (1 - e))}
    {uBar : Module.End kA[G] (LinearMap.range (1 - eBar))}
    [Module.Projective A[G] (LinearMap.range (1 - e))]
    [Module.Finite A (LinearMap.range (1 - e))]
    (huRed :
      endHom_restrict_groupAlgebraLinearMap
        (A := A) (G := G)
        (f :=
          range_lifted_projector_linearMap (A := A) (G := G) hf
            (endHom_restrict_groupAlgebraLinearMap_one_sub
              (A := A) (G := G) hf heRed))
        (range_lifted_projector_isResidueFieldReduction
          (A := A) (G := G) hf he.one_sub
          (endHom_restrict_groupAlgebraLinearMap_one_sub
            (A := A) (G := G) hf heRed))
        u = uBar)
    (x : LinearMap.range (1 - e)) :
    endHom_restrict_groupAlgebraLinearMap (A := A) (G := G) hf
        (complement_range_endomorphism_to_ambient (A := A) (G := G) e u) (f x) =
      ((uBar
        (range_lifted_projector_linearMap (A := A) (G := G) hf
          (endHom_restrict_groupAlgebraLinearMap_one_sub
            (A := A) (G := G) hf heRed) x) :
          LinearMap.range (1 - eBar)) : Pbar) := by
  let hCompRed :
      endHom_restrict_groupAlgebraLinearMap (A := A) (G := G) hf (1 - e) = 1 - eBar :=
    endHom_restrict_groupAlgebraLinearMap_one_sub (A := A) (G := G) hf heRed
  let hfComp :
      (range_lifted_projector_linearMap (A := A) (G := G) hf hCompRed).IsResidueFieldReduction G :=
    range_lifted_projector_isResidueFieldReduction (A := A) (G := G) hf he.one_sub hCompRed
  have hRange :
      ((uBar
          (range_lifted_projector_linearMap (A := A) (G := G) hf hCompRed x) :
          LinearMap.range (1 - eBar)) : Pbar) =
        f ((u x : LinearMap.range (1 - e)) : P) := by
    -- First reduce `u` along the range reduction map, then forget the range subtype to the
    -- ambient reduced module.
    have hReducedComp :
        endHom_restrict_groupAlgebraLinearMap
            (A := A) (G := G)
            (P := LinearMap.range (1 - e))
            (Pbar := LinearMap.range (1 - eBar))
            hfComp u
            (range_lifted_projector_linearMap (A := A) (G := G) hf hCompRed x) =
          range_lifted_projector_linearMap (A := A) (G := G) hf hCompRed (u x) := by
      simpa using
        (endHom_restrict_groupAlgebraLinearMap_comp_apply
          (A := A) (G := G)
          (P := LinearMap.range (1 - e))
          (Pbar := LinearMap.range (1 - eBar))
          hfComp u x)
    -- Replace the reduced complementary-range endomorphism by the chosen `uBar`.
    have hReducedComp' :
        uBar (range_lifted_projector_linearMap (A := A) (G := G) hf hCompRed x) =
          range_lifted_projector_linearMap (A := A) (G := G) hf hCompRed (u x) := by
      simpa [hfComp, huRed] using hReducedComp
    exact congrArg Subtype.val hReducedComp'
  calc
    endHom_restrict_groupAlgebraLinearMap (A := A) (G := G) hf
        (complement_range_endomorphism_to_ambient (A := A) (G := G) e u) (f x)
        = f ((complement_range_endomorphism_to_ambient (A := A) (G := G) e u) x) := by
            exact
              endHom_restrict_groupAlgebraLinearMap_comp_apply
                (A := A) (G := G) hf
                (complement_range_endomorphism_to_ambient (A := A) (G := G) e u) x
    _ = f ((u x : LinearMap.range (1 - e)) : P) := by
          rw [complement_range_endomorphism_to_ambient_apply_subtype
            (A := A) (G := G) e he u x]
    _ = ((uBar
          (range_lifted_projector_linearMap (A := A) (G := G) hf hCompRed x) :
          LinearMap.range (1 - eBar)) : Pbar) := hRange.symm

-- Proof sketch: a finite direct-sum decomposition of `Pbar` is encoded by pairwise orthogonal
-- idempotent equivariant endomorphisms summing to `1`; lift those idempotents through the reduced
-- endomorphism algebra from the previous theorem and part (1), now using the henselian owner on
-- `A`.
/-- Helper for Exercise 14-14.4-6: a complete orthogonal family indexed by `Fin 0` forces the
reduced module, hence also the source module, to be trivial. This isolates the zero-length base
case of the lifting induction. -/
theorem source_subsingleton_of_completeOrthogonalIdempotents_fin_zero
    {f : P →ₗ[A] Pbar}
    (hf : f.IsResidueFieldReduction G)
    (eBar : Fin 0 → EndkA)
    (heBar : CompleteOrthogonalIdempotents eBar) :
    Subsingleton P := by
  have hzero : (0 : EndkA) = 1 := by
    simpa using heBar.complete
  have hsubPbar : Subsingleton Pbar := by
    refine ⟨fun x y ↦ ?_⟩
    have hx : x = 0 := by
      have hx0 := congrArg (fun T : EndkA => T x) hzero
      simpa using hx0.symm
    have hy : y = 0 := by
      have hy0 := congrArg (fun T : EndkA => T y) hzero
      simpa using hy0.symm
    simpa [hx, hy]
  have hsubTensor : Subsingleton (kA ⊗[A] P) := by
    exact (hf.1.equiv.toEquiv.subsingleton_congr).2 hsubPbar
  exact (IsLocalRing.subsingleton_tensorProduct (R := A) (M := P)).1 hsubTensor

/-- Helper for Exercise 14-14.4-6: the reduced ambientized tail endomorphism vanishes on the head
summand `range (eBar 0)` and agrees with the successor projector on the complementary summand
`range (1 - eBar 0)`. -/
theorem ambientized_tail_reduction_head_complement_split
    {n : Nat}
    {f : P →ₗ[A] Pbar}
    (hf : f.IsResidueFieldReduction G)
    (eBar : Fin (n + 1) → Module.End kA[G] Pbar)
    (heBar : CompleteOrthogonalIdempotents eBar)
    {e0 : Module.End A[G] P}
    (he0 : IsIdempotentElem e0)
    (he0Red : endHom_restrict_groupAlgebraLinearMap (A := A) (G := G) hf e0 = eBar 0)
    {tailBar : Fin n → Module.End kA[G] (LinearMap.range (1 - eBar 0))}
    (htailBarApply :
      ∀ i (x : LinearMap.range (1 - eBar 0)),
        ((tailBar i) x : Pbar) = eBar i.succ x)
    {tail : Fin n → Module.End A[G] (LinearMap.range (1 - e0))}
    [Module.Projective A[G] (LinearMap.range (1 - e0))]
    [Module.Finite A (LinearMap.range (1 - e0))]
    (htailRed :
      endHom_restrict_groupAlgebraLinearMap
          (A := A) (G := G)
          (f := range_lifted_projector_linearMap (A := A) (G := G) hf
            (endHom_restrict_groupAlgebraLinearMap_one_sub
              (A := A) (G := G) hf he0Red))
          (range_lifted_projector_isResidueFieldReduction
            (A := A) (G := G) hf he0.one_sub
            (endHom_restrict_groupAlgebraLinearMap_one_sub
              (A := A) (G := G) hf he0Red))
          ∘ tail = tailBar)
    (i : Fin n) :
    (∀ x : Pbar,
      endHom_restrict_groupAlgebraLinearMap (A := A) (G := G) hf
          (complement_range_endomorphism_to_ambient (A := A) (G := G) e0 (tail i))
          (eBar 0 x) = 0) ∧
    (∀ x : LinearMap.range (1 - eBar 0),
      endHom_restrict_groupAlgebraLinearMap (A := A) (G := G) hf
          (complement_range_endomorphism_to_ambient (A := A) (G := G) e0 (tail i)) x =
        eBar i.succ x) := by
  let hCompRed :
      endHom_restrict_groupAlgebraLinearMap (A := A) (G := G) hf (1 - e0) = 1 - eBar 0 :=
    endHom_restrict_groupAlgebraLinearMap_one_sub (A := A) (G := G) hf he0Red
  have htailRed_i :
      endHom_restrict_groupAlgebraLinearMap
          (A := A) (G := G)
          (f := range_lifted_projector_linearMap (A := A) (G := G) hf hCompRed)
          (range_lifted_projector_isResidueFieldReduction
            (A := A) (G := G) hf he0.one_sub hCompRed)
          (tail i) =
        tailBar i := by
    -- Evaluate the recursive reduction identity on the chosen successor index.
    simpa [hCompRed] using congrArg (fun h ↦ h i) htailRed
  have hright_zero :
      endHom_restrict_groupAlgebraLinearMap (A := A) (G := G) hf
          (complement_range_endomorphism_to_ambient (A := A) (G := G) e0 (tail i)) *
        eBar 0 = 0 := by
    -- Reduce the upstairs identity saying that the ambientized tail kills the head projector on
    -- the right.
    have hzero :=
      congrArg (endHom_restrict_groupAlgebraAlgHom (A := A) (G := G) hf)
        (complement_range_endomorphism_to_ambient_mul_head
          (A := A) (G := G) e0 he0 (tail i))
    simpa [he0Red, endHom_restrict_groupAlgebraAlgHom_toLinearMap (A := A) (G := G) hf] using
      hzero
  refine ⟨?_, ?_⟩
  · intro x
    -- Evaluating the reduced right-annihilation identity shows that the head summand is killed.
    simpa [Module.End.mul_eq_comp] using
      congrArg (fun T : Module.End kA[G] Pbar => T x) hright_zero
  · intro x
    -- Pull the complementary-range point back through the surjective range reduction map and then
    -- use the already-verified reduction formula on subtype inputs.
    obtain ⟨y, hy⟩ :=
      range_lifted_projector_linearMap_surjective
        (A := A) (G := G) hf hCompRed x
    calc
      endHom_restrict_groupAlgebraLinearMap (A := A) (G := G) hf
          (complement_range_endomorphism_to_ambient (A := A) (G := G) e0 (tail i)) x
          =
        endHom_restrict_groupAlgebraLinearMap (A := A) (G := G) hf
            (complement_range_endomorphism_to_ambient (A := A) (G := G) e0 (tail i))
            (range_lifted_projector_linearMap (A := A) (G := G) hf hCompRed y) := by
              rw [hy]
      _ =
        (((tailBar i)
          (range_lifted_projector_linearMap (A := A) (G := G) hf hCompRed y) :
            LinearMap.range (1 - eBar 0)) : Pbar) := by
              simpa [hCompRed] using
                ambientize_complement_range_endomorphism_reduction_on_subtype
                  (A := A) (G := G) hf he0 he0Red
                  (u := tail i) (uBar := tailBar i) htailRed_i y
      _ = eBar i.succ (range_lifted_projector_linearMap (A := A) (G := G) hf hCompRed y) := by
            simpa using
              htailBarApply i
                (range_lifted_projector_linearMap (A := A) (G := G) hf hCompRed y)
      _ = eBar i.succ x := by rw [hy]

/-- Helper for Exercise 14-14.4-6: after recursively lifting the complementary tail family on
`range (1 - e₀)`, reducing its ambientization back to `Pbar` should recover the successor
projectors of the original family. -/
theorem ambientized_tail_reduction_eq_successor
    {n : Nat}
    {f : P →ₗ[A] Pbar}
    (hf : f.IsResidueFieldReduction G)
    (eBar : Fin (n + 1) → Module.End kA[G] Pbar)
    (heBar : CompleteOrthogonalIdempotents eBar)
    {e0 : Module.End A[G] P}
    (he0 : IsIdempotentElem e0)
    (he0Red : endHom_restrict_groupAlgebraLinearMap (A := A) (G := G) hf e0 = eBar 0)
    {tailBar : Fin n → Module.End kA[G] (LinearMap.range (1 - eBar 0))}
    (htailBarApply :
      ∀ i (x : LinearMap.range (1 - eBar 0)),
        ((tailBar i) x : Pbar) = eBar i.succ x)
    {tail : Fin n → Module.End A[G] (LinearMap.range (1 - e0))}
    [Module.Projective A[G] (LinearMap.range (1 - e0))]
    [Module.Finite A (LinearMap.range (1 - e0))]
    (htailRed :
      endHom_restrict_groupAlgebraLinearMap
          (A := A) (G := G)
          (f := range_lifted_projector_linearMap (A := A) (G := G) hf
            (endHom_restrict_groupAlgebraLinearMap_one_sub
              (A := A) (G := G) hf he0Red))
          (range_lifted_projector_isResidueFieldReduction
            (A := A) (G := G) hf he0.one_sub
            (endHom_restrict_groupAlgebraLinearMap_one_sub
              (A := A) (G := G) hf he0Red))
          ∘ tail = tailBar) :
    ∀ i : Fin n,
      endHom_restrict_groupAlgebraLinearMap (A := A) (G := G) hf
          (complement_range_endomorphism_to_ambient (A := A) (G := G) e0 (tail i)) =
        eBar i.succ := by
  intro i
  -- Split the reduced ambientized tail into its head-vanishing part and its complementary action.
  obtain ⟨hhead, hcomp⟩ :=
    ambientized_tail_reduction_head_complement_split
      (A := A) (G := G) (P := P) (Pbar := Pbar)
      hf eBar heBar he0 he0Red htailBarApply htailRed i
  ext x
  -- Decompose `x` into the head image plus the complementary summand cut out by `1 - eBar 0`.
  have hx_split : x = eBar 0 x + (1 - eBar 0) x := by
    calc
      x = (1 : Module.End kA[G] Pbar) x := by simp
      _ = (eBar 0 + (1 - eBar 0)) x := by simp
      _ = eBar 0 x + (1 - eBar 0) x := by rfl
  let xComp : LinearMap.range (1 - eBar 0) := ⟨(1 - eBar 0) x, ⟨x, rfl⟩⟩
  have htail_apply :
      endHom_restrict_groupAlgebraLinearMap (A := A) (G := G) hf
          (complement_range_endomorphism_to_ambient (A := A) (G := G) e0 (tail i))
          ((1 - eBar 0) x) =
        eBar i.succ ((1 - eBar 0) x) := by
    -- The complementary summand lies in `range (1 - eBar 0)`, so the split lemma applies
    -- directly.
    simpa [xComp] using hcomp xComp
  have hsucc_mul_complement :
      eBar i.succ * (1 - eBar 0) = eBar i.succ := by
    -- Orthogonality with the head projector turns the complement into an identity on the
    -- successor projector.
    rw [mul_sub, mul_one, heBar.ortho (Fin.succ_ne_zero i), sub_zero]
  calc
    endHom_restrict_groupAlgebraLinearMap (A := A) (G := G) hf
        (complement_range_endomorphism_to_ambient (A := A) (G := G) e0 (tail i)) x
        =
      endHom_restrict_groupAlgebraLinearMap (A := A) (G := G) hf
          (complement_range_endomorphism_to_ambient (A := A) (G := G) e0 (tail i))
          (eBar 0 x + (1 - eBar 0) x) := by
            rw [hx_split]
    _ =
      endHom_restrict_groupAlgebraLinearMap (A := A) (G := G) hf
          (complement_range_endomorphism_to_ambient (A := A) (G := G) e0 (tail i))
          (eBar 0 x) +
        endHom_restrict_groupAlgebraLinearMap (A := A) (G := G) hf
          (complement_range_endomorphism_to_ambient (A := A) (G := G) e0 (tail i))
          ((1 - eBar 0) x) := by
            simp
    _ = 0 + eBar i.succ ((1 - eBar 0) x) := by rw [hhead x, htail_apply]
    _ = eBar i.succ x := by
          rw [zero_add]
          simpa [Module.End.mul_eq_comp] using
            congrArg (fun T : Module.End kA[G] Pbar => T x) hsucc_mul_complement

/-- Helper for Exercise 14-14.4-6: the induction on the number of projectors is most naturally
carried out on ordinary `A[G]`-linear endomorphisms before transporting back to equivariant
endomorphisms. -/
theorem lift_completeOrthogonalIdempotents_fin_groupAlgebraEnd
    {n : Nat}
    {f : P →ₗ[A] Pbar}
    (hf : f.IsResidueFieldReduction G)
    (eBar : Fin n → Module.End kA[G] Pbar)
    (heBar : CompleteOrthogonalIdempotents eBar) :
    ∃ e : Fin n → Module.End A[G] P,
      CompleteOrthogonalIdempotents e ∧
        endHom_restrict_groupAlgebraLinearMap (A := A) (G := G) hf ∘ e = eBar := by
  induction n generalizing P Pbar with
  | zero =>
      -- In the empty-index case the reduced completeness relation forces `Pbar = 0`, hence `P = 0`.
      have hsub : Subsingleton P :=
        source_subsingleton_of_completeOrthogonalIdempotents_fin_zero
          (A := A) (G := G) hf eBar heBar
      letI : Subsingleton (Module.End A[G] P) := inferInstance
      refine ⟨Fin.elim0, CompleteOrthogonalIdempotents.of_subsingleton, ?_⟩
      funext i
      exact Fin.elim0 i
  | succ n ih =>
      -- Lift the head idempotent, recurse on the complementary range, and then ambientize the tail.
      obtain ⟨e0, he0, he0Red⟩ :=
        endHom_restrict_groupAlgebraLinearMap_lifts_idempotent
          (A := A) (G := G) hf (eBar 0) (heBar.idem 0)
      obtain ⟨tailBar, htailBar, htailBarApply⟩ :=
        tail_family_on_complement_range (A := A) (G := G) eBar heBar
      let hCompRed :
          endHom_restrict_groupAlgebraLinearMap (A := A) (G := G) hf (1 - e0) = 1 - eBar 0 :=
        endHom_restrict_groupAlgebraLinearMap_one_sub (A := A) (G := G) hf he0Red
      let hfComp :
          (range_lifted_projector_linearMap (A := A) (G := G) hf hCompRed).IsResidueFieldReduction G :=
        range_lifted_projector_isResidueFieldReduction (A := A) (G := G) hf he0.one_sub hCompRed
      letI : Module.Projective A[G] (LinearMap.range (1 - e0)) :=
        projective_range_of_idempotent_endomorphism_general (1 - e0) he0.one_sub
      letI : Module.Finite A (LinearMap.range (1 - e0)) :=
        Module.Finite.range ((1 - e0).restrictScalars A)
      obtain ⟨tail, htail, htailRed⟩ :=
        ih hfComp tailBar htailBar
      let e : Fin (n + 1) → Module.End A[G] P :=
        Fin.cases e0
          (fun i ↦ complement_range_endomorphism_to_ambient (A := A) (G := G) e0 (tail i))
      refine ⟨e, ?_, ?_⟩
      · -- The head projector and the ambientized recursive tail form a complete orthogonal family.
        simpa [e] using
          cons_head_and_ambientized_tail_completeOrthogonalIdempotents
            (A := A) (G := G) e0 he0 tail htail
      · -- The reduction identity is the lifted head equation together with the ambientized-tail
        -- comparison on successor indices.
        funext i
        rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
        · simpa [e] using he0Red
        · simpa [e] using
            ambientized_tail_reduction_eq_successor
              (A := A) (G := G) (P := P) (Pbar := Pbar)
              hf eBar heBar he0 he0Red htailBarApply htailRed j

/-- Exercise 14-14.4-6 (4): source part (b). Equivalently to lifting each direct-sum decomposition
of `Pbar`, any finite family of pairwise orthogonal idempotent `G`-equivariant endomorphisms of
`Pbar` summing to the identity lifts to such a family on `P`. -/
theorem lift_completeOrthogonalIdempotents_fin
    {n : Nat}
    {f : P →ₗ[A] Pbar}
    (hf : f.IsResidueFieldReduction G)
    (eBar : Fin n → EndkA)
    (heBar : CompleteOrthogonalIdempotents eBar) :
    ∃ e : Fin n → EndA,
      CompleteOrthogonalIdempotents e ∧
        hf.endAlgHom ∘ e = eBar := by
  let eBarOrd : Fin n → Module.End kA[G] Pbar :=
    fun i ↦ ofModule'_equivAlgEnd (G := G) kA Pbar (eBar i)
  have heBarOrd : CompleteOrthogonalIdempotents eBarOrd := by
    -- Transport the reduced equivariant family to ordinary `kA[G]`-linear endomorphisms.
    simpa [eBarOrd] using
      heBar.map ((ofModule'_equivAlgEnd (G := G) kA Pbar).toAlgHom)
  obtain ⟨eOrd, heOrd, heOrdRed⟩ :=
    lift_completeOrthogonalIdempotents_fin_groupAlgebraEnd
      (A := A) (G := G) hf eBarOrd heBarOrd
  let e : Fin n → EndA := fun i ↦ (ofModule'_equivAlgEnd (G := G) A P).symm (eOrd i)
  refine ⟨e, ?_, ?_⟩
  · -- Pull the complete orthogonal family back across the ordinary/equivariant equivalence.
    exact
      (CompleteOrthogonalIdempotents.map_injective_iff
        (e := e)
        (f := (ofModule'_equivAlgEnd (G := G) A P).toAlgHom)
        (hf := (ofModule'_equivAlgEnd (G := G) A P).injective)).mp <| by
          simpa [e] using heOrd
  · -- After transporting both source and target families to ordinary endomorphisms, the recursive
    -- reduction identity is exactly the one proved above.
    funext i
    apply (ofModule'_equivAlgEnd (G := G) kA Pbar).injective
    calc
      ofModule'_equivAlgEnd (G := G) kA Pbar (hf.endAlgHom (e i))
          = endHom_restrict_groupAlgebraLinearMap (A := A) (G := G) hf (eOrd i) := by
              simpa [e] using
                (endHom_restrict_groupAlgebraLinearMap_eq_transport
                  (A := A) (G := G) hf (eOrd i)).symm
      _ = eBarOrd i := by
            simpa [eBarOrd] using congrArg (fun h : Fin n → Module.End kA[G] Pbar => h i) heOrdRed
      _ = ofModule'_equivAlgEnd (G := G) kA Pbar (eBar i) := rfl

/-- Exercise 14-14.4-6 (4): source part (b). Equivalently to lifting each direct-sum decomposition
of `Pbar`, any finite family of pairwise orthogonal idempotent `G`-equivariant endomorphisms of
`Pbar` summing to the identity lifts to such a family on `P`. -/
theorem lift_completeOrthogonalIdempotents
    {ι : Type x} [Fintype ι]
    {f : P →ₗ[A] Pbar}
    (hf : f.IsResidueFieldReduction G)
    (eBar : ι → EndkA)
    (heBar : CompleteOrthogonalIdempotents eBar) :
    ∃ e : ι → EndA,
      CompleteOrthogonalIdempotents e ∧
        hf.endAlgHom ∘ e = eBar := by
  -- Reindex the family along `Fintype.equivFin ι`, apply the `Fin`-indexed lifting theorem, and
  -- then transport the lifted family back to the original index type.
  let eBarFin : Fin (Fintype.card ι) → EndkA := eBar ∘ (Fintype.equivFin ι).symm
  have heBarFin : CompleteOrthogonalIdempotents eBarFin := by
    -- The completeness and orthogonality data are invariant under reindexing by an equivalence.
    simpa [eBarFin] using
      (CompleteOrthogonalIdempotents.equiv
        (e := eBar) (i := (Fintype.equivFin ι).symm)).2 heBar
  obtain ⟨eFin, heFin, heFinRed⟩ :=
    lift_completeOrthogonalIdempotents_fin (A := A) (G := G) hf eBarFin heBarFin
  let e : ι → EndA := eFin ∘ Fintype.equivFin ι
  refine ⟨e, ?_, ?_⟩
  · -- Transport the complete orthogonal family back along the inverse equivalence.
    have heIndexed : CompleteOrthogonalIdempotents (e ∘ (Fintype.equivFin ι).symm) := by
      simpa [e, Function.comp_assoc] using heFin
    exact
      (CompleteOrthogonalIdempotents.equiv
        (e := e) (i := (Fintype.equivFin ι).symm)).1 heIndexed
  · -- Evaluate the `Fin`-indexed reduction equality on `Fintype.equivFin ι i`.
    funext i
    have hi :=
      congrArg (fun h : Fin (Fintype.card ι) → EndkA => h (Fintype.equivFin ι i)) heFinRed
    simpa [eBarFin, e, Function.comp_assoc] using hi

end Henselian

end LinearMap.IsResidueFieldReduction

namespace FiniteProjectiveGroupAlgebraModule

section Henselian

variable [HenselianLocalRing A]

variable [Finite G]

variable (A G) in
/-- Helper for Exercise 14-14.4-6: once an idempotent projector on the standard free reduced
module has been lifted upstairs, the range owner of the lift reduces to any module presented by the
original reduced projector range. -/
theorem lifted_projector_range_nonempty_iso
    {n : Nat}
    {f : (Fin n → A[G]) →ₗ[A] (Fin n → kA[G])}
    (hf : f.IsResidueFieldReduction G)
    {e : Module.End A[G] (Fin n → A[G])}
    (he : IsIdempotentElem e)
    {eBar : Module.End kA[G] (Fin n → kA[G])}
    (heRed :
      LinearMap.IsResidueFieldReduction.endHom_restrict_groupAlgebraLinearMap (A := A) (G := G)
        hf e = eBar)
    (F : FiniteProjectiveGroupAlgebraModule kA G)
    (hF : Nonempty (LinearMap.range eBar ≃ₗ[kA[G]] F.V)) :
    let Q :=
      finiteProjectiveGroupAlgebraModule_of_idempotent_range (A := A) (G := G) e he
    Nonempty (Q.residueFieldReduction ≅ F) := by
  let Q :=
    finiteProjectiveGroupAlgebraModule_of_idempotent_range (A := A) (G := G) e he
  have hQRange :
      Nonempty (Q.residueFieldReduction.V ≃ₗ[kA[G]] LinearMap.range eBar) := by
    -- The reduced owner for `range e` is definitionally the tensor-product reduction of `range e`.
    change Nonempty (((kA ⊗[A] LinearMap.range e) ≃ₗ[kA[G]] LinearMap.range eBar))
    exact
      LinearMap.IsResidueFieldReduction.range_lifted_projector_reduction_nonempty_linearEquiv
        (A := A) (G := G) hf he heRed
  have hQF : Nonempty (Q.residueFieldReduction.V ≃ₗ[kA[G]] F.V) := by
    rcases hQRange with ⟨e₁⟩
    rcases hF with ⟨e₂⟩
    exact ⟨e₁.trans e₂⟩
  -- Convert the underlying linear equivalence into an isomorphism in the finite-projective owner.
  exact
    (finiteProjectiveGroupAlgebraModule_nonempty_iso_iff_nonempty_linearEquiv
      Q.residueFieldReduction F).2 hQF

-- Proof sketch: write `F` as a direct summand of a finite free `k[G]`-module, lift that free
-- module to an `A[G]`-module, and then lift the corresponding idempotent decomposition using
-- part (4); over the henselian local ring `A`, the needed `A`-freeness is derived rather than
-- exposed as public existential data, and the reduction isomorphism is exhibited in the canonical
-- owner.
/-- Exercise 14-14.4-6 (5): source part (c). Every finite projective `k[G]`-module arises as the
reduction modulo `𝔪` of a finite projective `A[G]`-module. -/
theorem exists_residueFieldReduction_iso
    [Finite G]
    (F : FiniteProjectiveGroupAlgebraModule kA G) :
    ∃ Q : FiniteProjectiveGroupAlgebraModule A G,
      Nonempty (Q.residueFieldReduction ≅ F) := by
  -- Source part (c): present `F` as a direct factor of a free `k[G]`-module, lift the free module,
  -- then lift the corresponding idempotent and compare the lifted range with the original module.
  obtain ⟨n, eBar, heBar, hF⟩ :=
    exists_free_projector_presentation_iso (A := A) (G := G) F
  letI : Module.Finite A (Fin n → A[G]) :=
    LinearMap.IsResidueFieldReduction.finite_free_groupAlgebra_moduleFinite
      (A := A) (G := G) n
  let f : (Fin n → A[G]) →ₗ[A] (Fin n → kA[G]) :=
    LinearMap.compLeft
      (((MonoidAlgebra.mapAlgHom G (Algebra.ofId A kA)).toLinearMap :
        A[G] →ₗ[A] kA[G])) (Fin n)
  let hf :
      f.IsResidueFieldReduction G :=
    LinearMap.IsResidueFieldReduction.finite_free_groupAlgebra_residueFieldReduction
      (A := A) (G := G) n
  obtain ⟨e, he, heRed⟩ :=
    LinearMap.IsResidueFieldReduction.endHom_restrict_groupAlgebraLinearMap_lifts_idempotent
      (A := A) (G := G)
      (P := Fin n → A[G]) (Pbar := Fin n → kA[G])
      (f := f) hf eBar heBar
  let Q :=
    finiteProjectiveGroupAlgebraModule_of_idempotent_range (A := A) (G := G) e he
  refine ⟨Q, ?_⟩
  -- Package the lifted projector range as the desired projective owner upstairs.
  simpa [Q] using
    lifted_projector_range_nonempty_iso (A := A) (G := G) hf he heRed F hF

end Henselian

end FiniteProjectiveGroupAlgebraModule

end
