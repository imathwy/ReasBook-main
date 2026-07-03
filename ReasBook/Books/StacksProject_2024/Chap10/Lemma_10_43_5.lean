import Mathlib
import StacksProject_2024.Chap10.Lemma_10_25_2
import StacksProject_2024.Chap10.Lemma_10_43_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra

universe u v w

/-!
Domain triage:
- `source-facing`: the statement says that tensoring a reduced `k`-algebra with a geometrically
  reduced `k`-algebra over the same field stays reduced.
- `core/canonical`: the owner abstraction on the right factor is `Algebra.IsGeometricallyReduced`.
- `bridge/view`: Lemma `10.43.4` gives the finite descent skeleton, so the remaining work is the
  finite-stage reducedness statement.
-/

section

variable {k : Type u} {R : Type v} {S : Type w}
variable [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]

/-- Helper for Lemma 10.43.5: a minimal prime carries its canonical primality instance. -/
local instance minimalPrime_isPrime (p : minimalPrimes R) : p.1.IsPrime :=
  Ideal.minimalPrimes_isPrime p.2

/-- Helper for Lemma 10.43.5: a reduced `k`-algebra has reduced `k`-subalgebras. -/
lemma isReduced_subalgebra_of_isReduced [IsReduced R] (T : Subalgebra k R) :
    IsReduced T := by
  -- Reducedness descends along the injective inclusion into the ambient reduced algebra.
  exact isReduced_of_injective T.val Subtype.val_injective

/-- Helper for Lemma 10.43.5: the left side of a finitely generated tensor stage is Noetherian. -/
lemma isNoetherianRing_left_of_fgSubalgebraPair
    (T : @FGSubalgebraPair k R S _ _ _ _ _) :
    IsNoetherianRing T.left := by
  -- Finite generation over the field `k` upgrades the left stage to a finite type algebra.
  let _ : Algebra.FiniteType k T.left := (Subalgebra.fg_iff_finiteType T.left).mp T.left_fg
  -- Finite type algebras over a Noetherian ring are Noetherian, and fields are Noetherian.
  exact Algebra.FiniteType.isNoetherianRing k T.left

/-- Helper for Lemma 10.43.5: it is enough to prove reducedness on every finitely generated tensor
stage produced by Lemma `10.43.4`. -/
lemma isReduced_tensorProduct_of_forall_fgSubalgebraPair
    [IsReduced R] [IsGeometricallyReduced k S]
    (hfg : ∀ T : @FGSubalgebraPair k R S _ _ _ _ _, IsReduced (T.left ⊗[k] T.right)) :
    IsReduced (R ⊗[k] S) := by
  -- Any nonreduced witness in the ambient tensor product descends to a finite stage.
  by_contra hnot
  obtain ⟨T, hTnot⟩ := exists_fg_subalgebras_not_isReduced_tensorProduct
    (k := k) (R := R) (S := S) hnot
  -- The assumed finite-stage reducedness contradicts that descended witness.
  exact hTnot (hfg T)

/-- Helper for Lemma 10.43.5: tensoring an injective algebra map on the right over a field stays
injective. -/
lemma tensorProduct_map_injective_of_injective_rightAlgHom
    {A : Type*} {B : Type*} {C : Type*}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra k A] [Algebra k B] [Algebra k C]
    (f : B →ₐ[k] C) (hf : Function.Injective f) :
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id k A) f) := by
  -- Over a field, both tensor factors are flat, so the tensor-product map preserves injectivity.
  simpa using
    TensorProduct.map_injective_of_flat_flat
      (LinearMap.id : A →ₗ[k] A)
      f.toLinearMap
      (fun _ _ h ↦ h)
      hf

/-- Helper for Lemma 10.43.5: if a field extension is essentially of finite type over `k`, then
tensoring a geometrically reduced `k`-algebra with it is reduced. -/
lemma essFiniteTypeField_tensor_right_reduced
    {K : Type*} [Field K] [Algebra k K] [Algebra.EssFiniteType k K]
    [IsGeometricallyReduced k S] :
    IsReduced (S ⊗[k] K) := by
  -- Route correction: the remaining gap is not a local tensor rewrite but the owner-level bridge
  -- that geometrically reduced base change stays reduced over essentially finite type field
  -- extensions. Reusing later `10.43.6`/`10.44.4` directly would create an import cycle through
  -- `Definition_10_43_1`, so the missing theorem must be moved to an earlier support owner.
  -- TODO: prove the dependency-closed support theorem
  -- `isReduced_tensorProduct_of_essFiniteTypeField :
  --    [Field K] [Algebra k K] [Algebra.EssFiniteType k K] [IsGeometricallyReduced k S] →
  --    IsReduced (S ⊗[k] K)`
  -- by combining the purely inseparable lift from `Lemma 10.42.4` with the separably generated
  -- field case, and then replace this local placeholder by a direct application of that theorem.
  sorry

/-- Helper for Lemma 10.43.5: tensoring the geometrically reduced right stage with any
minimal-prime field factor of a finite-type left stage stays reduced. -/
lemma minimalPrime_localization_tensor_right_reduced
    [IsReduced R] [Algebra.FiniteType k R] [IsGeometricallyReduced k S]
    (p : minimalPrimes R) :
    IsReduced (S ⊗[k] Localization.AtPrime p.1) := by
  let _ : Field (Localization.AtPrime p.1) :=
    (isField_localizationAtPrime_of_minimalPrime (R := R) p).toField
  let _ : Algebra.EssFiniteType R (Localization.AtPrime p.1) :=
    Algebra.EssFiniteType.of_isLocalization
      (R := R)
      (S := Localization.AtPrime p.1)
      p.1.primeCompl
  let _ : Algebra.EssFiniteType k (Localization.AtPrime p.1) :=
    Algebra.EssFiniteType.comp k R (Localization.AtPrime p.1)
  -- The minimal-prime localization is a finitely generated field extension of `k`, so this is
  -- exactly the field case isolated above.
  exact essFiniteTypeField_tensor_right_reduced (k := k) (S := S)

/-- Helper for Lemma 10.43.5: after commuting the tensor factors, tensoring the minimal-prime
product embedding of the left stage gives an injective comparison map into the product of field
factors. -/
abbrev fgStageFieldFactor
    (T : @FGSubalgebraPair k R S _ _ _ _ _)
    (p : minimalPrimes T.left) : Type _ :=
  T.right ⊗[k] Localization.AtPrime p.1

/-- Helper for Lemma 10.43.5: the product of all minimal-prime field tensor factors attached to a
finitely generated stage. -/
abbrev fgStageTensorTarget
    (T : @FGSubalgebraPair k R S _ _ _ _ _) : Type _ :=
  ∀ p : minimalPrimes T.left, fgStageFieldFactor (k := k) (R := R) (S := S) T p

/-- Helper for Lemma 10.43.5: after commuting the tensor factors, tensoring the minimal-prime
product embedding of the left stage gives an injective comparison map into the product of field
factors. -/
noncomputable abbrev fgStageTensorCompare
    (T : @FGSubalgebraPair k R S _ _ _ _ _)
    [Fintype (minimalPrimes T.left)] [DecidableEq (minimalPrimes T.left)] :
    T.left ⊗[k] T.right →ₐ[k] fgStageTensorTarget (k := k) (R := R) (S := S) T :=
  (((Algebra.TensorProduct.piRight k k T.right
      (fun p : minimalPrimes T.left ↦ Localization.AtPrime p.1)).toAlgHom).comp
      (Algebra.TensorProduct.map (AlgHom.id k T.right)
        (IsScalarTower.toAlgHom
          k
          T.left
          (∀ p : minimalPrimes T.left, Localization.AtPrime p.1)))).comp
    (Algebra.TensorProduct.comm k T.left T.right).toAlgHom

/-- Helper for Lemma 10.43.5: after commuting the tensor factors, tensoring the minimal-prime
product embedding of the left stage gives an injective comparison map into the product of field
factors. -/
lemma fg_stage_tensor_to_minimalPrime_fields_injective
    (T : @FGSubalgebraPair k R S _ _ _ _ _)
    [IsReduced T.left]
    [Fintype (minimalPrimes T.left)] [DecidableEq (minimalPrimes T.left)] :
    Function.Injective (fgStageTensorCompare (k := k) (R := R) (S := S) T) := by
  have hleft :
      Function.Injective
        (IsScalarTower.toAlgHom
          k
          T.left
          (∀ p : minimalPrimes T.left, Localization.AtPrime p.1)) :=
    (algebraMap_embedding_into_product_of_fields (R := T.left)).1
  have htensor :
      Function.Injective
        (Algebra.TensorProduct.map (AlgHom.id k T.right)
          (IsScalarTower.toAlgHom
            k
            T.left
            (∀ p : minimalPrimes T.left, Localization.AtPrime p.1))) := by
    -- Tensoring the injective product-of-fields embedding with the identity preserves injectivity.
    exact
      tensorProduct_map_injective_of_injective_rightAlgHom
        (k := k)
        (A := T.right)
        (B := T.left)
        (C := ∀ p : minimalPrimes T.left, Localization.AtPrime p.1)
        (IsScalarTower.toAlgHom
          k
          T.left
          (∀ p : minimalPrimes T.left, Localization.AtPrime p.1))
        hleft
  -- Compose the tensor comparison with the finite-product tensor equivalence.
  exact
    (Algebra.TensorProduct.piRight k k T.right
      (fun p : minimalPrimes T.left ↦ Localization.AtPrime p.1)).injective.comp
      (htensor.comp (Algebra.TensorProduct.comm k T.left T.right).injective)

/-- Helper for Lemma 10.43.5: a finitely generated tensor stage is reduced once the source proof's
product-of-fields reduction is implemented. -/
lemma fgSubalgebraPair_isReduced_tensorProduct
    [IsReduced R] [IsGeometricallyReduced k S]
    (T : @FGSubalgebraPair k R S _ _ _ _ _) :
    IsReduced (T.left ⊗[k] T.right) := by
  let _ : IsReduced T.left :=
    isReduced_subalgebra_of_isReduced (k := k) (R := R) T.left
  let _ : IsGeometricallyReduced k T.right :=
    IsGeometricallyReduced.of_injective T.right.val Subtype.val_injective
  let _ : Algebra.FiniteType k T.left :=
    (Subalgebra.fg_iff_finiteType T.left).mp T.left_fg
  let _ : IsNoetherianRing T.left :=
    isNoetherianRing_left_of_fgSubalgebraPair (k := k) (R := R) (S := S) T
  let _ : Fintype (minimalPrimes T.left) :=
    (minimalPrimes.finite_of_isNoetherianRing (R := T.left)).fintype
  let compare :
      T.left ⊗[k] T.right →ₐ[k] fgStageTensorTarget (k := k) (R := R) (S := S) T :=
    fgStageTensorCompare (k := k) (R := R) (S := S) T
  have hcompare : Function.Injective compare :=
    fg_stage_tensor_to_minimalPrime_fields_injective (k := k) (R := R) (S := S) T
  let _ : ∀ p : minimalPrimes T.left, IsReduced (fgStageFieldFactor (k := k) (R := R) (S := S) T p) :=
    fun p ↦
      minimalPrime_localization_tensor_right_reduced
        (k := k) (R := T.left) (S := T.right) p
  let _ : Pow (fgStageTensorTarget (k := k) (R := R) (S := S) T) ℕ :=
    ⟨fun x n p ↦ x p ^ n⟩
  let _ : IsReduced (fgStageTensorTarget (k := k) (R := R) (S := S) T) :=
    { eq_zero := fun x hx ↦
        let ⟨n, hn⟩ := hx
        funext fun p ↦ IsReduced.eq_zero (x p) ⟨n, congrFun hn p⟩ }
  -- The source proof now closes the finite stage by embedding it into a product of reduced field
  -- factors and reflecting reducedness across that injective comparison map.
  exact isReduced_of_injective compare.toMonoidWithZeroHom hcompare

-- Proof sketch: descend nonreducedness to a finitely generated tensor stage using Lemma `10.43.4`,
-- then prove that finite stage reduced by the source proof's embedding into a finite product of
-- fields and the field-factor case of geometric reducedness.
/-- Lemma 10.43.5 (Tag 034N): if `S` is geometrically reduced over the field `k` and `R` is a
reduced `k`-algebra, then `R ⊗[k] S` is reduced. -/
@[stacks 034N, instance]
theorem isReduced_tensorProduct_of_geometricallyReduced
    [IsReduced R] [IsGeometricallyReduced k S] :
    IsReduced (R ⊗[k] S) := by
  -- First reduce the global claim to the finite tensor stages produced by Lemma `10.43.4`.
  refine isReduced_tensorProduct_of_forall_fgSubalgebraPair
    (k := k) (R := R) (S := S) ?_
  intro T
  -- Then discharge the finite stage by the source proof's product-of-fields argument.
  exact fgSubalgebraPair_isReduced_tensorProduct (k := k) (R := R) (S := S) T

end
