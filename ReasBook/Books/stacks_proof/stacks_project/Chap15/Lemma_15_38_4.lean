import Mathlib
import StacksProject_2024.Chap10.Lemma_10_160_10
import StacksProject_2024.Chap15.Lemma_15_38_3

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

universe u v

section

variable {k : Type u} [Field k]
variable {A : Type v} [CommRing A] [Algebra k A] [IsCompleteLocalRing A]
  [IsRegularLocalRing A]

/-- Helper for Lemma 15.38.4: the residue field of a field is canonically the field itself. -/
noncomputable def residueField_ringEquiv_self (K : Type u) [Field K] :
    ResidueField K ≃+* K :=
  (Ideal.quotEquivOfEq ((maximalIdeal K).eq_bot_of_prime)).trans (RingEquiv.quotientBot K)

/-- Helper for Lemma 15.38.4: the canonical residue-field equivalence of a field sends the
residue class of an element to that element. -/
lemma residueField_ringEquiv_self_apply_algebraMap
    (K : Type u) [Field K] (a : K) :
    residueField_ringEquiv_self K (algebraMap K (ResidueField K) a) = a := by
  -- The quotient by the zero maximal ideal identifies `a` with its own residue class.
  change residueField_ringEquiv_self K (residue K a) = a
  unfold residueField_ringEquiv_self RingEquiv.quotientBot
  rfl

omit [IsRegularLocalRing A] in
/-- Helper for Lemma 15.38.4: the theorem-local `ResidueField A`-algebra structure coming from a
section `φ` has `φ` as its algebra map. -/
lemma residueField_algebraMap_eq_section
    (φ : ResidueField A →ₐ[k] A) :
    let _ : Algebra (ResidueField A) A := RingHom.toAlgebra φ.toRingHom
    (algebraMap (ResidueField A) A : ResidueField A →+* A) = φ.toRingHom := by
  -- This converts the theorem-local coefficient-field structure back to the chosen section.
  simp [RingHom.algebraMap_toAlgebra]

omit [IsRegularLocalRing A] in
/-- Helper for Lemma 15.38.4: a section of the residue map makes the induced residue-field map
identify with the canonical residue-field equivalence of the coefficient field. -/
lemma residueField_map_eq_residueField_ringEquiv_self_of_residue_section
    (φ : ResidueField A →ₐ[k] A)
    (hφ : (residue A).comp φ = RingHom.id (ResidueField A)) :
    let _ : Algebra (ResidueField A) A := RingHom.toAlgebra φ.toRingHom
    ResidueField.map (algebraMap (ResidueField A) A) =
      (residueField_ringEquiv_self (ResidueField A)).toRingHom := by
  let _ : Algebra (ResidueField A) A := RingHom.toAlgebra φ.toRingHom
  -- Compare both residue-field maps on residue classes of coefficient-field elements.
  refine Ideal.Quotient.ringHom_ext ?_
  ext a
  change
    ResidueField.map (algebraMap (ResidueField A) A) (residue (ResidueField A) a) =
      residueField_ringEquiv_self (ResidueField A) (residue (ResidueField A) a)
  rw [ResidueField.map_residue]
  rw [residueField_algebraMap_eq_section (k := k) (A := A) φ]
  -- The chosen section is a left inverse to the residue map, so both sides now evaluate to `a`.
  have hφa : residue A (φ.toRingHom a) = a := by
    simpa using DFunLike.congr_fun hφ a
  rw [hφa]
  exact (residueField_ringEquiv_self_apply_algebraMap (ResidueField A) a).symm

omit [IsRegularLocalRing A] in
/-- Helper for Lemma 15.38.4: a section of the residue map makes the induced residue-field map
bijective. -/
lemma residueField_map_bijective_of_residue_section
    (φ : ResidueField A →ₐ[k] A)
    (hφ : (residue A).comp φ = RingHom.id (ResidueField A)) :
    let _ : Algebra (ResidueField A) A := RingHom.toAlgebra φ.toRingHom
    Function.Bijective (ResidueField.map (algebraMap (ResidueField A) A)) := by
  let _ : Algebra (ResidueField A) A := RingHom.toAlgebra φ.toRingHom
  let eSource : ResidueField (ResidueField A) ≃+* ResidueField A :=
    residueField_ringEquiv_self (ResidueField A)
  have hmap :
      ResidueField.map (algebraMap (ResidueField A) A) = eSource.toRingHom :=
    residueField_map_eq_residueField_ringEquiv_self_of_residue_section
      (k := k) (A := A) φ hφ
  -- Once the induced map is identified with a ring equivalence, bijectivity is immediate.
  simpa [eSource, hmap] using eSource.bijective

/-- Helper for Lemma 15.38.4: a finite-variable power-series ring can be reindexed by `Fin d`. -/
lemma mvPowerSeries_algEquiv_fin_of_finite
    (K : Type u) [Field K] (σ : Type v) [Finite σ] :
    ∃ d : ℕ, Nonempty (MvPowerSeries (Fin d) K ≃ₐ[K] MvPowerSeries σ K) := by
  classical
  let _ : Fintype σ := Fintype.ofFinite σ
  -- Reindex along `Fintype.equivFin` to replace the abstract finite type by `Fin d`.
  refine ⟨Fintype.card σ, ⟨MvPowerSeries.renameEquiv K (Fintype.equivFin σ).symm⟩⟩

/- Domain-style sampling for Lemma 15.38.4:
- primary domain: equal-characteristic Cohen-structure presentations of complete regular local
  algebras.
- sampled owner declarations:
  `exists_residueField_section_of_isCompleteLocalRing_of_isSeparableOver`,
  `exists_algEquiv_mvPowerSeries_of_residueField_bijective`,
  `MvPowerSeries.renameEquiv`,
  `AlgEquiv.restrictScalars`.
- best owner abstraction: the canonical owner is the finite-index power-series presentation
  `MvPowerSeries σ (ResidueField A)` with `[Finite σ]` from Lemma `10.160.10 (2)`. This file is a
  `source-facing` bridge that keeps the textbook `Fin d` surface by reindexing the canonical owner
  rather than duplicating it.
- primitive data: the complete regular local `k`-algebra `A` and the separability of
  `ResidueField A / k`.
- derived API: a `k`-algebra equivalence from a finite-variable formal power series ring over the
  residue field of `A`.

Source/core/bridge triage:
- `source-facing`: the `Fin d`-indexed Stacks Project presentation below.
- `core/canonical`: `exists_algEquiv_mvPowerSeries_of_residueField_bijective`.
- `bridge/view`: the residue-field section from Lemma `15.38.3`, followed by reindexing along
  `Fintype.equivFin`.
-/

-- Proof sketch: choose a `k`-algebra section `ResidueField A →ₐ[k] A` of the residue map via
-- Lemma `15.38.3`. This gives `A` a coefficient-field structure over `ResidueField A`, and the
-- induced residue-field map is the identity. Apply the canonical finite-index presentation from
-- Lemma `10.160.10 (2)` over `ResidueField A`, then reindex the variables along
-- `Fintype.equivFin` and restrict scalars back to `k`.
/-- Lemma 15.38.4: if `A` is a complete regular local `k`-algebra and the residue field extension
`ResidueField A / k` is separable in the Stacks Project sense, then `A` is `k`-algebra
isomorphic to a finite-variable formal power series ring over its residue field. -/
@[stacks 0C35]
theorem exists_algEquiv_mvPowerSeries_residueField_of_isSeparableOver_of_isRegularLocalRing
    [Algebra.IsSeparableOver k (ResidueField A)] :
    ∃ d : ℕ, Nonempty (MvPowerSeries (Fin d) (ResidueField A) ≃ₐ[k] A) := by
  obtain ⟨φ, hφ⟩ :=
    exists_residueField_section_of_isCompleteLocalRing_of_isSeparableOver (A := A) k
  let _ : Algebra (ResidueField A) A := RingHom.toAlgebra φ.toRingHom
  let _ : IsScalarTower k (ResidueField A) A := IsScalarTower.of_algebraMap_eq fun x ↦ by
    -- The chosen section is already a `k`-algebra map, so the new coefficient-field structure
    -- is compatible with the original `k`-algebra structure on `A`.
    simpa [RingHom.algebraMap_toAlgebra] using (φ.commutes x).symm
  have hres :
      Function.Bijective (ResidueField.map (algebraMap (ResidueField A) A)) := by
    -- The section identifies the closed fiber with the coefficient field.
    simpa using residueField_map_bijective_of_residue_section
      (k := k) (A := A) φ hφ
  obtain ⟨σ, hσfinite, hσ⟩ :=
    exists_algEquiv_mvPowerSeries_of_residueField_bijective
      (R := A) (k := ResidueField A) hres
  obtain ⟨d, hd⟩ :=
    mvPowerSeries_algEquiv_fin_of_finite (K := ResidueField A) σ
  rcases hσ with ⟨eσ⟩
  rcases hd with ⟨eFin⟩
  refine ⟨d, ⟨((eFin.trans eσ).restrictScalars k)⟩⟩

end
