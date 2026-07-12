import Mathlib
import StacksProject_2024.Chap10.Lemma_10_112_8
import StacksProject_2024.Chap10.Lemma_10_155_1
import StacksProject_2024.Chap10.Lemma_10_36_19
import StacksProject_2024.Chap10.Lemma_10_26_5
import StacksProject_2024.Chap15.Lemma_15_18_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct
open IsLocalRing

universe u

noncomputable section

section

variable (A Ah : Type u)
variable [CommRing A] [IsLocalRing A]
variable [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]

attribute [local instance] Algebra.TensorProduct.leftAlgebra Algebra.TensorProduct.rightAlgebra

-- Route correction: work file-locally with the reduced normalization to avoid the broken
-- `Definition_15_107_1` import chain while preserving the target theorem headers.
local notation:max "(" R ")" "_red" => R ⧸ nilradical R
local notation "A′" => integralClosure (A)_red (FractionRing (A)_red)
local notation "A′h" => A′ ⊗[A] Ah
local notation "κA" => ResidueField A
local notation "κAh" => ResidueField Ah

/-- Helper for Lemma 15.107.2: the reduction `(A)_red` of a local ring is again local. -/
local instance unibranchReduction_isLocalRing : IsLocalRing (A)_red := by
  let _ : Nontrivial (A ⧸ nilradical A) := Ideal.Quotient.nontrivial_iff.2 <|
    ne_top_of_le_ne_top (maximalIdeal.isMaximal A).ne_top
      (nilradical_le_prime (maximalIdeal A))
  simpa [Ideal.Quotient.algebraMap_eq] using
    (IsLocalRing.of_surjective' (Ideal.Quotient.mk (nilradical A)) Ideal.Quotient.mk_surjective :
      IsLocalRing (A ⧸ nilradical A))

/-- Helper for Lemma 15.107.2: the quotient map `A → (A)_red` is a local homomorphism. -/
local instance unibranchReduction_isLocalHom : IsLocalHom (algebraMap A (A)_red) :=
  IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective

/-- Helper for Lemma 15.107.2: the reduced normalization `A′` inherits its `A`-algebra structure
through `A → (A)_red → A′`. -/
local instance unibranchNormalization_algebra : Algebra A A′ :=
  ((algebraMap (A)_red A′).comp (algebraMap A (A)_red)).toAlgebra

/-- Helper for Lemma 15.107.2: the reduced normalization sits in the expected scalar tower over
`A → (A)_red`. -/
local instance unibranchNormalization_isScalarTower : IsScalarTower A (A)_red A′ :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- Helper for Lemma 15.107.2: the reduced normalization is integral over the original local ring.
-/
local instance unibranchNormalization_isIntegral : Algebra.IsIntegral A A′ :=
  Algebra.IsIntegral.trans (A)_red

/-- Helper for Lemma 15.107.2: every maximal ideal of the reduced normalization contracts to the
closed point of the local base ring. -/
theorem unibranchNormalization_comap_maximalIdeal
    {m : Ideal A′} (hm : m.IsMaximal) :
    Ideal.comap (algebraMap A A′) m = maximalIdeal A :=
  IsLocalRing.eq_maximalIdeal
    (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m)

/-
Domain-style sampling:
- primary domain: local commutative algebra of unibranch normalization, henselization, and prime
  spectra under tensor-product base change;
- sampled owner declarations of the same kind:
  `unibranchNormalization`,
  `IsHenselizationOf`,
  `minimalPrimes`,
  `Algebra.TensorProduct.includeRight`;
- best owner abstraction: the source-facing object is the chapter owner `A′ =
  unibranchNormalization A`, while the ideal-theoretic comparison statements are derived API on the
  canonical tensor-product base change `A′ ⊗[A] Ah`;
- primitive data: the local ring `A`, its chosen henselization `Ah`, and the owner `A′`;
- derived API: contraction along `A′ → A′h` and `Ah → A′h`, together with the canonical sets of
  maximal and minimal primes.

Source/core/bridge triage:
- `source-facing`: the four clauses of Lemma 15.107.2;
- `core/canonical`: `unibranchNormalization`, `IsHenselizationOf`, `Ideal.comap`,
  `minimalPrimes`, `Algebra.TensorProduct.includeRight`;
- `bridge/view`: the base-changed ring `A′h = A′ ⊗[A] Ah`.
-/

/-- Helper for Lemma 15.107.2: for a local ring, the quotient residue field and the maximal-ideal
residue field are canonically the same. -/
private noncomputable abbrev maximalIdealResidueFieldAlgEquiv :
    κA ≃ₐ[A] (maximalIdeal A).ResidueField :=
  .ofBijective _ (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal A))

/-- Helper for Lemma 15.107.2: the explicit source tensor model `A' ⊗[A] κ(A)` is the closed
fiber of `A → A'`. -/
-- Route correction: package the source tensor `A′ ⊗[A] κ(A)` directly through the canonical fiber
-- owner by first commuting tensor factors and then replacing `κ(A)` with the maximal-ideal
-- residue field that defines `Ideal.Fiber (maximalIdeal A) A′`.
noncomputable def unibranchNormalization_closedFiber_ringEquiv :
    (A′ ⊗[A] κA) ≃+* Ideal.Fiber (maximalIdeal A) A′ :=
  ((Algebra.TensorProduct.comm A A′ κA).trans
      (Algebra.TensorProduct.congr
        (maximalIdealResidueFieldAlgEquiv (A := A)) (.refl : A′ ≃ₐ[A] A′))).toRingEquiv

/-- Helper for Lemma 15.107.2: tensor commutativity carries the image of `maximalIdeal Ah` in the
left-ordered tensor `A′ ⊗[A] Ah` to the corresponding image in the right-ordered tensor
`Ah ⊗[A] A′`. -/
private theorem tensorComm_map_maximalIdeal :
    Ideal.map (Algebra.TensorProduct.comm A A′ Ah).toRingHom
      (Ideal.map (algebraMap Ah A′h) (maximalIdeal Ah)) =
    Ideal.map (algebraMap Ah (Ah ⊗[A] A′)) (maximalIdeal Ah) := by
  -- Proof comment: first combine the two ideal maps, then identify the composite ring map on
  -- generators of `Ah` with the right-factor algebra map after tensor commutation.
  rw [Ideal.map_map]
  refine congrArg (fun f : Ah →+* Ah ⊗[A] A′ ↦ Ideal.map f (maximalIdeal Ah)) ?_
  ext a
  change (Algebra.TensorProduct.comm A A′ Ah) ((1 : A′) ⊗ₜ[A] a) = a ⊗ₜ[A] (1 : A′)
  simpa using (Algebra.TensorProduct.comm_tmul (R := A) (a := (1 : A′)) (b := a))

/-- Helper for Lemma 15.107.2: the source tensor `A′ ⊗[A] A^h` can be rewritten in the
right-ordered form `A^h ⊗[A] A′` while keeping the `A^h`-algebra structure explicit. -/
noncomputable abbrev tensorComm_rightOrder_algEquiv :
    A′h ≃ₐ[Ah] (Ah ⊗[A] A′) := by
  -- Proof comment: `commRight` is the canonical owner-level swap that preserves the
  -- `A^h`-algebra structure on the left tensor factor.
  exact (Algebra.TensorProduct.commRight A Ah A′).symm

/-- Helper for Lemma 15.107.2: after rewriting `A′ ⊗[A] A^h` into right-ordered tensor form, the
closed fiber over `maximalIdeal Ah` is unchanged. -/
noncomputable abbrev closedFiber_tensorComm_ringEquiv :
    Ideal.Fiber (maximalIdeal Ah) A′h ≃+* Ideal.Fiber (maximalIdeal Ah) (Ah ⊗[A] A′) := by
  -- Proof comment: unfold the fiber owner once and push the ambient `Ah`-linear tensor swap
  -- through the outer tensor product.
  exact
    (Algebra.TensorProduct.congr
      (.refl :
        (maximalIdeal Ah).ResidueField ≃ₐ[(maximalIdeal Ah).ResidueField]
          (maximalIdeal Ah).ResidueField)
      (tensorComm_rightOrder_algEquiv (A := A) (Ah := Ah))).toRingEquiv

/-- Helper for Lemma 15.107.2: commuting the right-ordered closed-fiber tensor and replacing the
maximal-ideal residue field by the ordinary local residue field yields the source tensor model
`A′ ⊗[A] κ(Ah)`. -/
noncomputable abbrev rightOrder_closedFiberSourceModel_ringEquiv :
    ((maximalIdeal Ah).ResidueField ⊗[A] A′) ≃+* (A′ ⊗[A] κAh) := by
  -- Proof comment: commute the tensor factors once, then transport the residue-field factor
  -- across the canonical equivalence between the local and maximal-ideal residue fields.
  exact
    ((Algebra.TensorProduct.comm A ((maximalIdeal Ah).ResidueField) A′).toRingEquiv.trans <|
      (Algebra.TensorProduct.congr
        (.refl : A′ ≃ₐ[A′] A′)
        (AlgEquiv.restrictScalars A <|
          (maximalIdealResidueFieldAlgEquiv (A := Ah)).symm)).toRingEquiv)

/-- Helper for Lemma 15.107.2: after commuting the base-changed tensor to the right-ordered form,
the `Ah`-closed fiber of `A′ ⊗[A] Ah` is the source tensor model `A′ ⊗[A] κ(Ah)`. -/
noncomputable abbrev fiber_tensor_base_change_rightOrderRingEquiv :
    Ideal.Fiber (maximalIdeal Ah) A′h ≃+* (A′ ⊗[A] κAh) :=
  let pAh : PrimeSpectrum Ah := ⟨maximalIdeal Ah, inferInstance⟩
  let eFiber :
      Ideal.Fiber (maximalIdeal Ah) (Ah ⊗[A] A′) ≃+*
        ((maximalIdeal Ah).ResidueField ⊗[A] A′) :=
    (fiber_tensor_base_change_rightOrderAlgEquiv (R := A) (S := A′) (R' := Ah) pAh).toRingEquiv
  -- Proof comment: first rewrite the ambient tensor to the right-ordered model, then cancel the
  -- base change over the closed point, and finally commute the tensor factors back to the source
  -- model `A′ ⊗[A] κ(Ah)`.
  (closedFiber_tensorComm_ringEquiv (A := A) (Ah := Ah)).trans <|
    eFiber.trans (rightOrder_closedFiberSourceModel_ringEquiv (A := A) (Ah := Ah))

/-- Helper for Lemma 15.107.2: the henselian base change `A′ ⊗[A] A^h` remains integral over
`A^h`. -/
theorem unibranchNormalizationTensorHenselization_isIntegral :
    Algebra.IsIntegral Ah A′h := by
  have hInt : (algebraMap A A′).IsIntegral := algebraMap_isIntegral_iff.mpr inferInstance
  -- Proof comment: invoke stability of integrality under base change for the map `A → A′` along
  -- the henselization map `A → A^h`.
  exact algebraMap_isIntegral_iff.mp <|
    RingHom.isIntegral_isStableUnderBaseChange A A′ Ah A′h hInt

/-- Helper for Lemma 15.107.2: every maximal ideal of `A′ ⊗[A] A^h` contracts to the closed point
of the henselian base ring. -/
theorem unibranchNormalizationTensorHenselization_comap_maximalIdeal
    {m : Ideal A′h} (hm : m.IsMaximal) :
    Ideal.comap (algebraMap Ah A′h) m = maximalIdeal Ah := by
  -- Proof comment: the tensor base change of an integral algebra is still integral, so maximal
  -- ideals contract to maximal ideals; locality then forces the contraction to be the closed
  -- point.
  letI : Algebra.IsIntegral Ah A′h :=
    unibranchNormalizationTensorHenselization_isIntegral (A := A) (Ah := Ah)
  exact IsLocalRing.eq_maximalIdeal
    (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m)

/-- Helper for Lemma 15.107.2: maximal ideals of `A′ ⊗[A] A^h` are exactly the primes lying over
the closed point of `A^h`. -/
noncomputable def unibranchNormalizationTensorHenselization_maximalIdealEquivPrimesOver :
    {m : Ideal A′h // m.IsMaximal} ≃ ↑((maximalIdeal Ah).primesOver A′h) where
  toFun m := by
    -- Proof comment: every maximal ideal lies over the closed point because the target is local.
    exact ⟨m.1, ⟨m.2.isPrime,
      (Ideal.liesOver_iff _ _).2 <|
        (unibranchNormalizationTensorHenselization_comap_maximalIdeal (A := A) (Ah := Ah) m.2).symm⟩⟩
  invFun q := by
    -- Proof comment: integrality upgrades any prime above the closed point to a maximal ideal.
    let _ : q.1.IsPrime := q.2.1
    let _ : q.1.LiesOver (maximalIdeal Ah) := q.2.2
    letI : Algebra.IsIntegral Ah A′h :=
      unibranchNormalizationTensorHenselization_isIntegral (A := A) (Ah := Ah)
    refine ⟨q.1, ?_⟩
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap q.1 <| by
      simpa [q.1.over_def (maximalIdeal Ah)] using
        (maximalIdeal.isMaximal Ah : (maximalIdeal Ah).IsMaximal)
  left_inv m := by
    -- The equivalence forgets no ideal data; only the proof fields change.
    exact Subtype.ext rfl
  right_inv q := by
    -- The same ideal in `primesOver` is recovered after promoting it to a maximal ideal.
    exact Subtype.ext rfl

/-- Helper for Lemma 15.107.2: maximal ideals of the reduced normalization are exactly the primes
lying over the closed point of the local base ring. -/
noncomputable def unibranchNormalization_maximalIdealEquivPrimesOver :
    {m : Ideal A′ // m.IsMaximal} ≃ ↑((maximalIdeal A).primesOver A′) where
  toFun m := by
    -- Proof comment: the normalization is integral over the local base, so every maximal ideal
    -- contracts to the unique closed point.
    exact ⟨m.1, ⟨m.2.isPrime,
      (Ideal.liesOver_iff _ _).2 <|
        (unibranchNormalization_comap_maximalIdeal (A := A) m.2).symm⟩⟩
  invFun q := by
    -- Proof comment: primes of an integral algebra above a maximal ideal are maximal.
    let _ : q.1.IsPrime := q.2.1
    let _ : q.1.LiesOver (maximalIdeal A) := q.2.2
    refine ⟨q.1, ?_⟩
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap q.1 <| by
      simpa [q.1.over_def (maximalIdeal A)] using
        (maximalIdeal.isMaximal A : (maximalIdeal A).IsMaximal)
  left_inv m := by
    -- The ideal itself is unchanged; only its proof witnesses are repackaged.
    exact Subtype.ext rfl
  right_inv q := by
    -- The inverse recovers the same prime-over data from the promoted maximal ideal.
    exact Subtype.ext rfl

/-- Helper for Lemma 15.107.2: the closed fiber of `A′ → A′ ⊗[A] A^h` agrees with the closed
fiber of `A → A′` after identifying the residue fields of `A` and `A^h`. -/
noncomputable def unibranchNormalizationTensorHenselization_closedFiber_equiv :
    Ideal.Fiber (maximalIdeal Ah) A′h ≃+* Ideal.Fiber (maximalIdeal A) A′ := by
  let residueMap : κA →+* κAh := ResidueField.map (algebraMap A Ah)
  let _ : Algebra κA κAh := RingHom.toAlgebra residueMap
  let _ : Module κA κAh := (RingHom.toAlgebra residueMap).toModule
  let _ : IsScalarTower A κA κAh := IsScalarTower.of_algebraMap_eq fun a ↦ by
    change residueMap (algebraMap A κA a) = algebraMap A κAh a
    rfl
  let eResidue : κA ≃ₐ[A] κAh :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom A κA κAh)
      IsHenselizationOf.residueField_bijective
  -- Proof comment: compare the `Ah`-closed fiber with `A′ ⊗[A] κ(Ah)`, then pull the residue
  -- field back along the henselization residue-field equivalence and finish with the closed fiber
  -- comparison for `A → A′`.
  exact
    (fiber_tensor_base_change_rightOrderRingEquiv (A := A) (Ah := Ah)).trans <|
      ((Algebra.TensorProduct.congr
        (.refl : A′ ≃ₐ[A] A′) eResidue.symm).toRingEquiv.trans <|
          unibranchNormalization_closedFiber_ringEquiv (A := A))

/-- Helper for Lemma 15.107.2: the closed-fiber ring equivalence induces a homeomorphism on prime
spectra. -/
noncomputable abbrev unibranchNormalizationTensorHenselization_closedFiberPrimeSpectrumEquiv :
    PrimeSpectrum (Ideal.Fiber (maximalIdeal Ah) A′h) ≃ₜ
      PrimeSpectrum (Ideal.Fiber (maximalIdeal A) A′) :=
  PrimeSpectrum.homeomorphOfRingEquiv
    (unibranchNormalizationTensorHenselization_closedFiber_equiv (A := A) (Ah := Ah))

/-- Helper for Lemma 15.107.2: on the `A′`-branch, the inverse closed-fiber equivalence agrees
with first tensoring into `A′ ⊗[A] A^h` and then passing to the `Ah`-closed fiber. -/
private theorem unibranchNormalizationTensorHenselization_closedFiber_equiv_symm_apply_includeRight
    (x : A′) :
    (unibranchNormalizationTensorHenselization_closedFiber_equiv (A := A) (Ah := Ah)).symm
      ((includeRight : A′ →ₐ[A] Ideal.Fiber (maximalIdeal A) A′) x) =
      (includeRight : A′h →ₐ[Ah] Ideal.Fiber (maximalIdeal Ah) A′h)
        ((includeLeftRingHom : A′ →+* A′h) x) := by
  -- Proof comment: apply the forward closed-fiber equivalence and reduce the resulting composite
  -- to explicit pure-tensor formulas on the distinguished `A′`-branch.
  apply (unibranchNormalizationTensorHenselization_closedFiber_equiv (A := A) (Ah := Ah)).injective
  -- Proof comment: each stage of the composite equivalence acts explicitly on `x ⊗ 1`, so a
  -- single simplification pass normalizes the whole branch back to `includeRight x`.
  simp [unibranchNormalizationTensorHenselization_closedFiber_equiv,
    fiber_tensor_base_change_rightOrderRingEquiv,
    rightOrder_closedFiberSourceModel_ringEquiv,
    closedFiber_tensorComm_ringEquiv,
    tensorComm_rightOrder_algEquiv,
    unibranchNormalization_closedFiber_ringEquiv,
    maximalIdealResidueFieldAlgEquiv,
    Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.one_def,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
    Algebra.TensorProduct.comm_tmul,
    Algebra.TensorProduct.comm_symm_tmul]

/-- Helper for Lemma 15.107.2: the inverse closed-fiber equivalence intertwines the two
distinguished `includeRight` maps with contraction along `A′ → A′ ⊗[A] A^h`. -/
private theorem closedFiber_equiv_symm_comp_includeRight_eq_includeRight_comp_includeLeft :
    RingHom.comp
        ((unibranchNormalizationTensorHenselization_closedFiber_equiv (A := A) (Ah := Ah)).symm.toRingHom)
        ((includeRight : A′ →ₐ[A] Ideal.Fiber (maximalIdeal A) A′).toRingHom) =
      RingHom.comp
        ((includeRight : A′h →ₐ[Ah] Ideal.Fiber (maximalIdeal Ah) A′h).toRingHom)
        (includeLeftRingHom : A′ →+* A′h) := by
  -- Proof comment: equality of ring homomorphisms is checked on elements of `A′`, where the
  -- previous elementwise branch computation gives the required identity.
  ext x
  exact
    unibranchNormalizationTensorHenselization_closedFiber_equiv_symm_apply_includeRight
      (A := A) (Ah := Ah) x

/-- Helper for Lemma 15.107.2: the forward closed-fiber equivalence sends the distinguished
`A′ ⊗[A] A^h` branch back to the pure `A′` branch. -/
private theorem unibranchNormalizationTensorHenselization_closedFiber_equiv_apply_includeRight
    (x : A′) :
    (unibranchNormalizationTensorHenselization_closedFiber_equiv (A := A) (Ah := Ah))
      ((includeRight : A′h →ₐ[Ah] Ideal.Fiber (maximalIdeal Ah) A′h)
        ((includeLeftRingHom : A′ →+* A′h) x)) =
      (includeRight : A′ →ₐ[A] Ideal.Fiber (maximalIdeal A) A′) x := by
  -- Proof comment: apply the forward equivalence to the inverse-branch normalization already
  -- proved, then cancel the inverse/forward composite.
  exact
    (congrArg
      (unibranchNormalizationTensorHenselization_closedFiber_equiv (A := A) (Ah := Ah))
      (unibranchNormalizationTensorHenselization_closedFiber_equiv_symm_apply_includeRight
        (A := A) (Ah := Ah) x)).trans <|
      (unibranchNormalizationTensorHenselization_closedFiber_equiv
        (A := A) (Ah := Ah)).apply_symm_apply _

/-- Helper for Lemma 15.107.2: the source closed fiber `A′ ⊗[A] κ(A)` has totally disconnected
prime spectrum because it is integral over the field `κ(A)`. -/
private theorem sourceClosedFiber_totallyDisconnected :
    TotallyDisconnectedSpace (PrimeSpectrum (A′ ⊗[A] κA)) := by
  have hClosed :
      ∀ q : PrimeSpectrum (A′ ⊗[A] κA),
        IsClosed ({q} : Set (PrimeSpectrum (A′ ⊗[A] κA))) := by
    intro q
    rw [PrimeSpectrum.isClosed_singleton_iff_isMaximal]
    have hInt : (algebraMap A A′).IsIntegral := algebraMap_isIntegral_iff.mpr inferInstance
    let _ : Algebra.IsIntegral κA (A′ ⊗[A] κA) :=
      algebraMap_isIntegral_iff.mp <|
        RingHom.isIntegral_isStableUnderBaseChange A A′ κA (A′ ⊗[A] κA) hInt
    -- Proof comment: every prime quotient of an algebra integral over a field is a field, hence
    -- every prime ideal is maximal and therefore every spectrum point is closed.
    exact ideal_isMaximal_of_isPrime_of_integral_over_field q.asIdeal q.asIdeal.isPrime
  -- Proof comment: in `Spec`, the profinite/T2/totally-disconnected criteria are equivalent, so
  -- closedness of all points immediately yields total disconnectedness.
  exact ((primeSpectrum_profinite_tfae (R := A′ ⊗[A] κA)).out 5 2).mp hClosed

/-- Helper for Lemma 15.107.2: the closed fiber of `A → A′` is totally disconnected after
identifying it with the source tensor model `A′ ⊗[A] κ(A)`. -/
private theorem unibranchNormalization_closedFiber_totallyDisconnected :
    TotallyDisconnectedSpace (PrimeSpectrum (Ideal.Fiber (maximalIdeal A) A′)) := by
  let e :
      PrimeSpectrum (A′ ⊗[A] κA) ≃ₜ PrimeSpectrum (Ideal.Fiber (maximalIdeal A) A′) :=
    PrimeSpectrum.homeomorphOfRingEquiv (unibranchNormalization_closedFiber_ringEquiv (A := A))
  let _ : TotallyDisconnectedSpace (PrimeSpectrum (A′ ⊗[A] κA)) :=
    sourceClosedFiber_totallyDisconnected (A := A)
  -- Proof comment: total disconnectedness transports across the explicit closed-fiber
  -- homeomorphism.
  exact e.totallyDisconnectedSpace

/-- Helper for Lemma 15.107.2: the `Ah`-closed fiber of `A′ ⊗[A] A^h` is totally disconnected
because it is canonically homeomorphic to the closed fiber of `A → A′`. -/
private theorem unibranchNormalizationTensorHenselization_closedFiber_totallyDisconnected :
    TotallyDisconnectedSpace (PrimeSpectrum (Ideal.Fiber (maximalIdeal Ah) A′h)) := by
  let e :
      PrimeSpectrum (Ideal.Fiber (maximalIdeal Ah) A′h) ≃ₜ
        PrimeSpectrum (Ideal.Fiber (maximalIdeal A) A′) :=
    PrimeSpectrum.homeomorphOfRingEquiv <|
      unibranchNormalizationTensorHenselization_closedFiber_equiv (A := A) (Ah := Ah)
  let _ : TotallyDisconnectedSpace (PrimeSpectrum (Ideal.Fiber (maximalIdeal A) A′)) :=
    unibranchNormalization_closedFiber_totallyDisconnected (A := A)
  -- Proof comment: transport the totally disconnected closed fiber of `A → A′` back across the
  -- comparison homeomorphism coming from the trivial henselization residue-field extension.
  exact e.symm.totallyDisconnectedSpace

/-- Helper for Lemma 15.107.2: transporting a closed-fiber prime across the comparison
equivalence and then contracting along `includeRight` agrees with first contracting along the
`Ah`-fiber inclusion and then along `A′ → A′ ⊗[A] A^h`. -/
private theorem closedFiber_transport_comap_includeLeft
    (Q : PrimeSpectrum (Ideal.Fiber (maximalIdeal Ah) A′h)) :
    Ideal.comap ((includeRight : A′ →ₐ[A] Ideal.Fiber (maximalIdeal A) A′).toRingHom)
      ((unibranchNormalizationTensorHenselization_closedFiberPrimeSpectrumEquiv
        (A := A) (Ah := Ah) Q).asIdeal) =
    Ideal.comap (includeLeftRingHom : A′ →+* A′h)
      (Ideal.comap ((includeRight : A′h →ₐ[Ah] Ideal.Fiber (maximalIdeal Ah) A′h).toRingHom)
        Q.asIdeal) := by
  -- Proof comment: `PrimeSpectrum.homeomorphOfRingEquiv` acts by contraction along the inverse
  -- ring equivalence, so the claimed ideal identity is a direct `Ideal.comap_comap` rewrite.
  change
    Ideal.comap ((includeRight : A′ →ₐ[A] Ideal.Fiber (maximalIdeal A) A′).toRingHom)
      (Ideal.comap
        ((unibranchNormalizationTensorHenselization_closedFiber_equiv (A := A) (Ah := Ah)).symm.toRingHom)
        Q.asIdeal) =
      Ideal.comap (includeLeftRingHom : A′ →+* A′h)
        (Ideal.comap
          ((includeRight : A′h →ₐ[Ah] Ideal.Fiber (maximalIdeal Ah) A′h).toRingHom)
          Q.asIdeal)
  rw [Ideal.comap_comap, Ideal.comap_comap]
  congr 1
  exact closedFiber_equiv_symm_comp_includeRight_eq_includeRight_comp_includeLeft
    (A := A) (Ah := Ah)

/-- Helper for Lemma 15.107.2: contracting a maximal ideal of `A′ ⊗[A] A^h` along the left
tensor-factor map again yields a maximal ideal of `A′`. -/
private theorem unibranchNormalizationTensorHenselization_comap_left_isMaximal
    {m : Ideal A′h} (hm : m.IsMaximal) :
    (Ideal.comap (includeLeftRingHom : A′ →+* A′h) m).IsMaximal := by
  let pAh : PrimeSpectrum Ah := ⟨maximalIdeal Ah, inferInstance⟩
  let qh : PrimeSpectrum A′h := ⟨m, hm.isPrime⟩
  have hqh : PrimeSpectrum.comap (algebraMap Ah A′h) qh = pAh := by
    -- Proof comment: maximal ideals of the henselian base change contract to the unique closed
    -- point of `Ah`.
    apply PrimeSpectrum.ext
    simpa [qh, pAh, PrimeSpectrum.comap_asIdeal] using
      unibranchNormalizationTensorHenselization_comap_maximalIdeal
        (A := A) (Ah := Ah) hm
  let Qh : PrimeSpectrum (Ideal.Fiber (maximalIdeal Ah) A′h) :=
    PrimeSpectrum.preimageEquivFiber Ah A′h pAh ⟨qh, hqh⟩
  let QA : PrimeSpectrum (Ideal.Fiber (maximalIdeal A) A′) :=
    unibranchNormalizationTensorHenselization_closedFiberPrimeSpectrumEquiv
      (A := A) (Ah := Ah) Qh
  let pA : PrimeSpectrum A := ⟨maximalIdeal A, inferInstance⟩
  let qAData := (PrimeSpectrum.preimageEquivFiber A A′ pA).symm QA
  have hQhideal :
      Ideal.comap
        ((includeRight : A′h →ₐ[Ah] Ideal.Fiber (maximalIdeal Ah) A′h).toRingHom)
        Qh.asIdeal = m := by
    -- Proof comment: `Qh` is the fixed-fiber prime attached to the ambient prime `m`.
    simpa [Qh, qh] using
      preimageEquivFiber_asIdeal_comap
        (R := Ah) (S := A′h) pAh qh hqh
  have hQA :
      PrimeSpectrum.preimageEquivFiber A A′ pA qAData = QA := by
    -- The ambient prime over `maximalIdeal A` recovers the chosen fiber prime `QA`.
    exact (PrimeSpectrum.preimageEquivFiber A A′ pA).apply_symm_apply QA
  have hQAideal :
      Ideal.comap
        ((includeRight : A′ →ₐ[A] Ideal.Fiber (maximalIdeal A) A′).toRingHom)
        QA.asIdeal = qAData.1.asIdeal := by
    -- Proof comment: `PrimeSpectrum.preimageEquivFiber` records ambient primes by contracting
    -- back along the fiber inclusion.
    rw [← hQA]
    simpa using
      preimageEquivFiber_asIdeal_comap
        (R := A) (S := A′) pA qAData.1 qAData.2
  have htransport :
      Ideal.comap
        ((includeRight : A′ →ₐ[A] Ideal.Fiber (maximalIdeal A) A′).toRingHom)
        QA.asIdeal =
      Ideal.comap (includeLeftRingHom : A′ →+* A′h) m := by
    -- Proof comment: the closed-fiber equivalence identifies the transported fiber prime exactly
    -- with contraction along `A′ → A′ ⊗[A] A^h`.
    simpa [hQhideal] using
      closedFiber_transport_comap_includeLeft (A := A) (Ah := Ah) Qh
  have hqAeq : qAData.1.asIdeal = Ideal.comap (includeLeftRingHom : A′ →+* A′h) m := by
    exact hQAideal.symm.trans htransport
  have hqAmax : qAData.1.asIdeal.IsMaximal := by
    -- Proof comment: any prime of the integral normalization lying over the closed point of the
    -- local ring `A` is maximal.
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap qAData.1.asIdeal <| by
      simpa [qAData.1.over_def (maximalIdeal A)] using
        (maximalIdeal.isMaximal A : (maximalIdeal A).IsMaximal)
  simpa [hqAeq] using hqAmax

/-- Helper for Lemma 15.107.2: the contraction map `A′ ⊗[A] A^h → A′` sends maximal ideals to
maximal ideals. -/
private theorem unibranchNormalizationTensorHenselization_mapsTo_maximalIdeals :
    Set.MapsTo (Ideal.comap (includeLeftRingHom : A′ →+* A′h))
      {m : Ideal A′h | m.IsMaximal}
      {m : Ideal A′ | m.IsMaximal} := by
  intro m hm
  exact unibranchNormalizationTensorHenselization_comap_left_isMaximal
    (A := A) (Ah := Ah) hm

-- Proof sketch: reduce to the reduced case, identify the closed fiber of
-- `Anorm → Anormh = Anorm ⊗[A] Ah` with `Anorm ⊗[A] ResidueField A`, and use the trivial residue
-- field extension of a henselization together with integrality over the local base to show that
-- comap along `A' → (A')^h` gives a bijection on maximal ideals.
/-- Lemma 15.107.2 (1): for `A' = unibranchNormalization A` and `(A')^h = A' ⊗[A] A^h`, the map
`Spec((A')^h) → Spec(A')` is bijective on maximal ideals. -/
@[stacks 0C24]
theorem unibranchNormalizationTensorHenselization_bijOn_maximalIdeals
    (hfinite : (minimalPrimes A).Finite) :
    Set.BijOn (Ideal.comap (includeLeftRingHom : A′ →+* A′h))
      {m : Ideal A′h | m.IsMaximal}
      {m : Ideal A′ | m.IsMaximal} := by
  let _ := hfinite
  refine ⟨unibranchNormalizationTensorHenselization_mapsTo_maximalIdeals (A := A) (Ah := Ah), ?_, ?_⟩
  · intro m₁ hm₁ m₂ hm₂ hcomap
    let pAh : PrimeSpectrum Ah := ⟨maximalIdeal Ah, inferInstance⟩
    let qh₁ : PrimeSpectrum A′h := ⟨m₁, hm₁.isPrime⟩
    let qh₂ : PrimeSpectrum A′h := ⟨m₂, hm₂.isPrime⟩
    have hqh₁ : PrimeSpectrum.comap (algebraMap Ah A′h) qh₁ = pAh := by
      -- Proof comment: both maximal ideals of `A′h` lie over the closed point of `Ah`.
      apply PrimeSpectrum.ext
      simpa [qh₁, pAh, PrimeSpectrum.comap_asIdeal] using
        unibranchNormalizationTensorHenselization_comap_maximalIdeal
          (A := A) (Ah := Ah) hm₁
    have hqh₂ : PrimeSpectrum.comap (algebraMap Ah A′h) qh₂ = pAh := by
      -- The same contraction computation applies to the second maximal ideal.
      apply PrimeSpectrum.ext
      simpa [qh₂, pAh, PrimeSpectrum.comap_asIdeal] using
        unibranchNormalizationTensorHenselization_comap_maximalIdeal
          (A := A) (Ah := Ah) hm₂
    let Qh₁ : PrimeSpectrum (Ideal.Fiber (maximalIdeal Ah) A′h) :=
      PrimeSpectrum.preimageEquivFiber Ah A′h pAh ⟨qh₁, hqh₁⟩
    let Qh₂ : PrimeSpectrum (Ideal.Fiber (maximalIdeal Ah) A′h) :=
      PrimeSpectrum.preimageEquivFiber Ah A′h pAh ⟨qh₂, hqh₂⟩
    let QA₁ : PrimeSpectrum (Ideal.Fiber (maximalIdeal A) A′) :=
      unibranchNormalizationTensorHenselization_closedFiberPrimeSpectrumEquiv
        (A := A) (Ah := Ah) Qh₁
    let QA₂ : PrimeSpectrum (Ideal.Fiber (maximalIdeal A) A′) :=
      unibranchNormalizationTensorHenselization_closedFiberPrimeSpectrumEquiv
        (A := A) (Ah := Ah) Qh₂
    have hQh₁ideal :
        Ideal.comap
          ((includeRight : A′h →ₐ[Ah] Ideal.Fiber (maximalIdeal Ah) A′h).toRingHom)
          Qh₁.asIdeal = m₁ := by
      -- Proof comment: each `Qhᵢ` is the fixed-fiber prime attached to the corresponding maximal
      -- ideal `mᵢ`.
      simpa [Qh₁, qh₁] using
        preimageEquivFiber_asIdeal_comap
          (R := Ah) (S := A′h) pAh qh₁ hqh₁
    have hQh₂ideal :
        Ideal.comap
          ((includeRight : A′h →ₐ[Ah] Ideal.Fiber (maximalIdeal Ah) A′h).toRingHom)
          Qh₂.asIdeal = m₂ := by
      -- The second fixed-fiber prime has the same ambient-prime description.
      simpa [Qh₂, qh₂] using
        preimageEquivFiber_asIdeal_comap
          (R := Ah) (S := A′h) pAh qh₂ hqh₂
    have hfiberEq :
        Ideal.comap
          ((includeRight : A′ →ₐ[A] Ideal.Fiber (maximalIdeal A) A′).toRingHom)
          QA₁.asIdeal =
        Ideal.comap
          ((includeRight : A′ →ₐ[A] Ideal.Fiber (maximalIdeal A) A′).toRingHom)
          QA₂.asIdeal := by
      -- Proof comment: the closed-fiber transport identifies both contractions with the given
      -- common contraction along `includeLeftRingHom`.
      calc
        Ideal.comap
            ((includeRight : A′ →ₐ[A] Ideal.Fiber (maximalIdeal A) A′).toRingHom)
            QA₁.asIdeal =
          Ideal.comap (includeLeftRingHom : A′ →+* A′h) m₁ := by
            simpa [hQh₁ideal] using
              closedFiber_transport_comap_includeLeft (A := A) (Ah := Ah) Qh₁
        _ = Ideal.comap (includeLeftRingHom : A′ →+* A′h) m₂ := hcomap
        _ =
          Ideal.comap
            ((includeRight : A′ →ₐ[A] Ideal.Fiber (maximalIdeal A) A′).toRingHom)
            QA₂.asIdeal := by
              simpa [hQh₂ideal] using
                (closedFiber_transport_comap_includeLeft (A := A) (Ah := Ah) Qh₂).symm
    let pA : PrimeSpectrum A := ⟨maximalIdeal A, inferInstance⟩
    let qA₁Data := (PrimeSpectrum.preimageEquivFiber A A′ pA).symm QA₁
    let qA₂Data := (PrimeSpectrum.preimageEquivFiber A A′ pA).symm QA₂
    have hQA₁ :
        PrimeSpectrum.preimageEquivFiber A A′ pA qA₁Data = QA₁ := by
      -- The first ambient prime over `maximalIdeal A` recovers `QA₁`.
      exact (PrimeSpectrum.preimageEquivFiber A A′ pA).apply_symm_apply QA₁
    have hQA₂ :
        PrimeSpectrum.preimageEquivFiber A A′ pA qA₂Data = QA₂ := by
      -- The same reconstruction holds for `QA₂`.
      exact (PrimeSpectrum.preimageEquivFiber A A′ pA).apply_symm_apply QA₂
    have hqAideal :
        qA₁Data.1.asIdeal = qA₂Data.1.asIdeal := by
      -- Proof comment: equality of the contracted fiber primes forces equality of the
      -- corresponding ambient primes of `A′`.
      calc
        qA₁Data.1.asIdeal =
          Ideal.comap
            ((includeRight : A′ →ₐ[A] Ideal.Fiber (maximalIdeal A) A′).toRingHom)
            QA₁.asIdeal := by
              rw [← hQA₁]
              simpa using
                preimageEquivFiber_asIdeal_comap
                  (R := A) (S := A′) pA qA₁Data.1 qA₁Data.2
        _ =
          Ideal.comap
            ((includeRight : A′ →ₐ[A] Ideal.Fiber (maximalIdeal A) A′).toRingHom)
            QA₂.asIdeal := hfiberEq
        _ = qA₂Data.1.asIdeal := by
              rw [← hQA₂]
              simpa using
                preimageEquivFiber_asIdeal_comap
                  (R := A) (S := A′) pA qA₂Data.1 qA₂Data.2
    have hqAData :
        qA₁Data = qA₂Data := by
      -- An equality of prime ideals is an equality in the prime spectrum and hence in the
      -- corresponding fiber-preimage subtype.
      apply Subtype.ext
      exact PrimeSpectrum.ext hqAideal
    have hQAEq : QA₁ = QA₂ := by
      -- Transport the equality of ambient primes back to the fixed fiber over `maximalIdeal A`.
      simpa [qA₁Data, qA₂Data] using
        congrArg (PrimeSpectrum.preimageEquivFiber A A′ pA) hqAData
    have hQhEq : Qh₁ = Qh₂ := by
      -- The closed-fiber equivalence is injective on prime spectra.
      exact
        (unibranchNormalizationTensorHenselization_closedFiberPrimeSpectrumEquiv
          (A := A) (Ah := Ah)).injective hQAEq
    have hqhideal :
        m₁ = m₂ := by
      -- Finally pull the common fiber prime back to the ambient tensor product.
      simpa [Qh₁, Qh₂, qh₁, qh₂] using
        congrArg
          (fun q =>
            Ideal.comap
              ((includeRight : A′h →ₐ[Ah] Ideal.Fiber (maximalIdeal Ah) A′h).toRingHom)
              q.asIdeal)
          hQhEq
    exact hqhideal
  · intro m hm
    let pA : PrimeSpectrum A := ⟨maximalIdeal A, inferInstance⟩
    let qA : PrimeSpectrum A′ := ⟨m, hm.isPrime⟩
    have hqA : PrimeSpectrum.comap (algebraMap A A′) qA = pA := by
      -- Proof comment: maximal ideals of the normalization lie over the closed point of `A`.
      apply PrimeSpectrum.ext
      simpa [qA, pA, PrimeSpectrum.comap_asIdeal] using
        unibranchNormalization_comap_maximalIdeal (A := A) hm
    let QA : PrimeSpectrum (Ideal.Fiber (maximalIdeal A) A′) :=
      PrimeSpectrum.preimageEquivFiber A A′ pA ⟨qA, hqA⟩
    let Qh : PrimeSpectrum (Ideal.Fiber (maximalIdeal Ah) A′h) :=
      (unibranchNormalizationTensorHenselization_closedFiberPrimeSpectrumEquiv
        (A := A) (Ah := Ah)).symm QA
    let pAh : PrimeSpectrum Ah := ⟨maximalIdeal Ah, inferInstance⟩
    let qhData := (PrimeSpectrum.preimageEquivFiber Ah A′h pAh).symm Qh
    refine ⟨qhData.1.asIdeal, ?_, ?_⟩
    · -- Proof comment: the reconstructed ambient prime of `A′h` lies over the maximal ideal of
      -- `Ah`, so integrality of `Ah → A′h` makes it maximal.
      exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap qhData.1.asIdeal <| by
        simpa [qhData.1.over_def (maximalIdeal Ah)] using
          (maximalIdeal.isMaximal Ah : (maximalIdeal Ah).IsMaximal)
    · have hQh :
          PrimeSpectrum.preimageEquivFiber Ah A′h pAh qhData = Qh := by
        -- The ambient prime over `maximalIdeal Ah` recovers the chosen fiber prime `Qh`.
        exact (PrimeSpectrum.preimageEquivFiber Ah A′h pAh).apply_symm_apply Qh
      have hQhideal :
          Ideal.comap
            ((includeRight : A′h →ₐ[Ah] Ideal.Fiber (maximalIdeal Ah) A′h).toRingHom)
            Qh.asIdeal = qhData.1.asIdeal := by
        -- Proof comment: `preimageEquivFiber` remembers the ambient prime by contraction along
        -- the fiber inclusion.
        rw [← hQh]
        simpa using
          preimageEquivFiber_asIdeal_comap
            (R := Ah) (S := A′h) pAh qhData.1 qhData.2
      have hQA :
          (unibranchNormalizationTensorHenselization_closedFiberPrimeSpectrumEquiv
            (A := A) (Ah := Ah)) Qh = QA := by
        -- The inverse closed-fiber transport was defined to land back at `QA`.
        exact
          (unibranchNormalizationTensorHenselization_closedFiberPrimeSpectrumEquiv
            (A := A) (Ah := Ah)).apply_symm_apply QA
      have hQAideal :
          Ideal.comap
            ((includeRight : A′ →ₐ[A] Ideal.Fiber (maximalIdeal A) A′).toRingHom)
            QA.asIdeal = m := by
        -- Proof comment: `QA` is the fiber prime attached to the ambient maximal ideal `m`.
        simpa [QA, qA] using
          preimageEquivFiber_asIdeal_comap
            (R := A) (S := A′) pA qA hqA
      have htransport :
          Ideal.comap (includeLeftRingHom : A′ →+* A′h) qhData.1.asIdeal = m := by
        -- Proof comment: rewrite the transported fiber prime in terms of ambient contraction and
        -- then use the defining equality of `QA`.
        have h :=
          closedFiber_transport_comap_includeLeft (A := A) (Ah := Ah) Qh
        rw [hQA, hQhideal, hQAideal] at h
        simpa using h.symm
      simpa using htransport

/-- Helper for Lemma 15.107.2: a bijection on constrained sets transports unique existence
statements across the two sides. -/
private theorem existsUnique_mem_iff_existsUnique_mem_of_bijOn
    {α β : Type*} {s : Set α} {t : Set β} {f : α → β}
    (hbij : Set.BijOn f s t) :
    (∃! x, x ∈ s) ↔ ∃! y, y ∈ t := by
  constructor
  · rintro ⟨x, hx, hx_unique⟩
    refine ⟨f x, hbij.mapsTo hx, ?_⟩
    intro y hy
    rcases hbij.surjOn hy with ⟨z, hz, rfl⟩
    -- Proof comment: pull a target witness back to the source unique point and push it forward.
    simpa using congrArg f (hx_unique z hz)
  · rintro ⟨y, hy, hy_unique⟩
    rcases hbij.surjOn hy with ⟨x, hx, rfl⟩
    refine ⟨x, hx, ?_⟩
    intro z hz
    have hEq : f z = f x := hy_unique (f z) (hbij.mapsTo hz)
    exact hbij.injOn hz hx hEq

/-- Helper for Lemma 15.107.2: a surjection on constrained sets produces unique existence on the
target from unique existence on the source. -/
private theorem existsUnique_mem_of_surjOn
    {α β : Type*} {s : Set α} {t : Set β} {f : α → β}
    (hsurj : Set.SurjOn f s t) (huniq : ∃! x, x ∈ s) :
    ∃! y, y ∈ t := by
  rcases huniq with ⟨x, hx, hx_unique⟩
  refine ⟨f x, hsurj.1 hx, ?_⟩
  intro y hy
  rcases hsurj.2 hy with ⟨z, hz, rfl⟩
  -- Proof comment: any target witness comes from the unique source witness.
  simpa using congrArg f (hx_unique z hz)

/-- Helper for Lemma 15.107.2: under a faithfully flat algebra map, minimal primes contract to
minimal primes. -/
private theorem comap_mem_minimalPrimes_of_faithfullyFlat
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (hff : (algebraMap R S).FaithfullyFlat) {Q : Ideal S}
    (hQ : Q ∈ minimalPrimes S) :
    Ideal.comap (algebraMap R S) Q ∈ minimalPrimes R := by
  have hflat : (algebraMap R S).Flat := hff.flat
  let _ : Module.Flat R S := RingHom.flat_algebraMap_iff.mp hflat
  -- Proof comment: going down excludes any strictly smaller contracted prime.
  refine ⟨⟨Ideal.comap_isPrime (algebraMap R S) (Ideal.minimalPrimes_isPrime hQ), bot_le⟩, ?_⟩
  intro J hJ hJ_le
  by_cases hQJ : Ideal.comap (algebraMap R S) Q = J
  · exact hQJ.le
  · let _ : Algebra.HasGoingDown R S := Algebra.HasGoingDown.of_flat
    let _ : J.IsPrime := hJ.1
    let _ : Q.IsPrime := Ideal.minimalPrimes_isPrime hQ
    let _ : Q.LiesOver (Ideal.comap (algebraMap R S) Q) := ⟨rfl⟩
    have hJ_lt_Q : J < Ideal.comap (algebraMap R S) Q :=
      lt_of_le_of_ne hJ_le (Ne.symm hQJ)
    obtain ⟨Q', hQ'_lt, hQ'_prime, _⟩ :=
      Ideal.exists_ideal_lt_liesOver_of_lt (R := R) (S := S) (Q := Q) hJ_lt_Q
    have hQ_le_Q' : Q ≤ Q' :=
      hQ.2 ⟨hQ'_prime, bot_le⟩ hQ'_lt.le
    exact (hQ'_lt.not_ge hQ_le_Q').elim

/-- Helper for Lemma 15.107.2: contraction along a faithfully flat algebra map is surjective on
minimal primes. -/
private theorem surjOn_minimalPrimes_of_faithfullyFlat
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (hff : (algebraMap R S).FaithfullyFlat) :
    Set.SurjOn (Ideal.comap (algebraMap R S)) (minimalPrimes S) (minimalPrimes R) := by
  refine ⟨?_, ?_⟩
  · intro Q hQ
    -- Proof comment: the forward direction is the contraction lemma above.
    exact comap_mem_minimalPrimes_of_faithfullyFlat hff hQ
  · intro q hq
    have hinj : Function.Injective (algebraMap R S) := hff.injective
    have hker : RingHom.ker (algebraMap R S) = ⊥ := RingHom.ker_eq_bot.2 hinj
    have hqker : q ∈ (RingHom.ker (algebraMap R S)).minimalPrimes := by
      refine ⟨⟨Ideal.minimalPrimes_isPrime hq, ?_⟩, ?_⟩
      · simpa [hker]
      · intro I hI hIq
        exact hq.2 ⟨hI.1, by simpa [hker] using hI.2⟩ hIq
    -- Proof comment: injectivity makes the kernel trivial, so `exists_minimalPrimes_comap_eq`
    -- produces the required lift upstairs.
    obtain ⟨Q, hQ, hQq⟩ :=
      Ideal.exists_minimalPrimes_comap_eq (algebraMap R S) q hqker
    exact ⟨Q, hQ, hQq⟩

/-- Helper for Lemma 15.107.2: the canonical map to a chosen henselization is faithfully flat. -/
private theorem algebraMap_faithfullyFlat_of_isHenselizationOf :
    (algebraMap A Ah).FaithfullyFlat := by
  rw [RingHom.faithfullyFlat_algebraMap_iff]
  let _ : Module.Flat A Ah :=
    flat_of_isFilteredColimitOfEtale IsHenselizationOf.isFilteredColimitOfEtale
  -- Proof comment: flatness comes from the ind-étale presentation, and locality upgrades it to
  -- faithful flatness.
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- Helper for Lemma 15.107.2: tensoring the henselization map with the reduced normalization keeps
faithful flatness on the left tensor factor. -/
private theorem unibranchNormalizationTensorHenselization_includeLeft_faithfullyFlat :
    (includeLeftRingHom : A′ →+* A′h).FaithfullyFlat := by
  have hEq : (includeLeftRingHom : A′ →+* A′h) = algebraMap A′ A′h := rfl
  rw [hEq, RingHom.faithfullyFlat_algebraMap_iff]
  let _ : Module.FaithfullyFlat A Ah :=
    RingHom.faithfullyFlat_algebraMap_iff.mp <|
      algebraMap_faithfullyFlat_of_isHenselizationOf (A := A) (Ah := Ah)
  -- Proof comment: faithful flatness base-changes to the standard tensor module `A′ ⊗[A] A^h`.
  infer_instance

/-- Helper for Lemma 15.107.2: contraction along `A′ → A′ ⊗[A] A^h` is surjective on minimal
primes. -/
private theorem unibranchNormalizationTensorHenselization_surjOn_minimalPrimes_to_normalization :
    Set.SurjOn (Ideal.comap (includeLeftRingHom : A′ →+* A′h))
      (minimalPrimes A′h) (minimalPrimes A′) := by
  -- Proof comment: this is the faithfully flat base change of the henselization map.
  simpa using
    (surjOn_minimalPrimes_of_faithfullyFlat
      (R := A′) (S := A′h)
      (unibranchNormalizationTensorHenselization_includeLeft_faithfullyFlat
        (A := A) (Ah := Ah)))

/-- Helper for Lemma 15.107.2: contraction along `A → A^h` is surjective on minimal primes. -/
private theorem henselization_surjOn_minimalPrimes_from_base :
    Set.SurjOn (Ideal.comap (algebraMap A Ah))
      (minimalPrimes Ah) (minimalPrimes A) := by
  -- Proof comment: faithful flatness of the henselization map gives the standard surjection on
  -- minimal primes.
  exact
    surjOn_minimalPrimes_of_faithfullyFlat
      (R := A) (S := Ah)
      (algebraMap_faithfullyFlat_of_isHenselizationOf (A := A) (Ah := Ah))

-- Proof sketch: compare minimal primes on both sides with the fibers over the minimal primes of
-- `A`, use that `A'` becomes the total ring of fractions after inverting non-zero-divisors, and
-- identify `(A')^h ⊗[A] Q(Ared)` with `A^h ⊗[A] Q(Ared)` to match the minimal-prime sets.
/-- Lemma 15.107.2 (2): for `A' = unibranchNormalization A` and `(A')^h = A' ⊗[A] A^h`, the map
`Spec((A')^h) → Spec(A^h)` is bijective on minimal primes. -/
@[stacks 0C24]
theorem unibranchNormalizationTensorHenselization_bijOn_minimalPrimes
    (hfinite : (minimalPrimes A).Finite) :
    Set.BijOn
      (Ideal.comap ((includeRight : Ah →ₐ[A] A′h).toRingHom))
      (minimalPrimes A′h)
      (minimalPrimes Ah) := by
  let _ := hfinite
  -- Route correction: the faithfully flat contraction helpers above stabilize the ambient
  -- minimal-prime transport, but the remaining step is still the source generic-fiber comparison
  -- that identifies this contraction map with the common generic-fiber equivalence.
  -- TODO: build the generic-fiber ring equivalence over `FractionRing ((A)_red)`, identify each
  -- side with minimal primes, and prove the induced map is exactly contraction along `includeRight`.
  sorry

-- Proof sketch: `Anormh` is normal after base change to the henselization, so localizations at
-- maximal ideals are domains; combine this with henselian-pair connectivity of the closed fiber
-- to see that the connected closed subset cut out by a minimal prime meets the closed fiber in a
-- unique point, hence lies in a unique maximal ideal.
/-- Lemma 15.107.2 (3): every minimal prime of `(A')^h = A' ⊗[A] A^h` is contained in a unique
maximal ideal. -/
@[stacks 0C24]
theorem unibranchNormalizationTensorHenselization_minimalPrime_existsUnique_maximalIdeal
    (hfinite : (minimalPrimes A).Finite)
    {p : Ideal A′h} (hp : p ∈ minimalPrimes A′h) :
    ∃! m : Ideal A′h, m.IsMaximal ∧ p ≤ m := by
  -- TODO: combine the normality of `A′h` with the henselian-pair connectedness argument on the
  -- closed fiber to isolate a unique maximal ideal above the given minimal prime.
  sorry

-- Proof sketch: after the previous clause, each minimal prime determines a unique maximal ideal;
-- normality of the local rings of `Anormh` implies each maximal localization is a domain, so a
-- maximal ideal can contain only one minimal prime.
/-- Lemma 15.107.2 (4): every maximal ideal of `(A')^h = A' ⊗[A] A^h` contains exactly one
minimal prime. -/
@[stacks 0C24]
theorem unibranchNormalizationTensorHenselization_maximalIdeal_existsUnique_minimalPrime
    (hfinite : (minimalPrimes A).Finite)
    {m : Ideal A′h} (hm : m.IsMaximal) :
    ∃! p : Ideal A′h, p ∈ minimalPrimes A′h ∧ p ≤ m := by
  -- TODO: localize at `m`, use normality to see the localization is a domain, and transport the
  -- resulting unique minimal prime back to `A′h`.
  sorry

end
