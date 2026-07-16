import LinearRepresentations_Serre_1977.Serre.RepresentationTheory.RealizableOver
import LinearRepresentations_Serre_1977.Serre.Chap14.Lemma_14_14_4_1
import LinearRepresentations_Serre_1977.Serre.Chap14.Lemma_14_14_4_2
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.LocalProperties.Projective
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

-- Declarations for this item will be appended below by the statement pipeline.

open scoped MonoidAlgebra TensorProduct

universe u v w

noncomputable section

variable {Λ : Type u} [CommRing Λ]
variable {G : Type v} [Group G] [Finite G]
variable {P : Type w} [AddCommGroup P] [Module Λ P] [Module Λ[G] P]
variable [IsScalarTower Λ Λ[G] P] [Module.Finite Λ P]

attribute [local instance] Fintype.ofFinite

local instance {κ : Type*} [CommRing κ] [Algebra Λ κ] :
    Module κ[G] (κ ⊗[Λ] P) :=
  let ρ : Representation κ G (κ ⊗[Λ] P) :=
    Representation.scalarExtension (show Representation Λ G P from Representation.ofModule' P)
  Module.compHom _ ρ.asAlgebraHom.toRingHom

-- Layering:
-- * source-facing: the maximal-ideal reduction criterion below
-- * core/canonical: the residue-field owner `Ideal.ResidueField` together with the local
--   projectivity owner `Module.projective_of_localization_maximal`
-- * bridge/view: Lemma `projective_monoidAlgebra_iff_projective_residueFieldReduction` and the
--   maximal-ideal quotient bridge `Ideal.bijective_algebraMap_quotient_residueField`
--
-- Proof sketch: the underlying `Λ`-module of `P` is finite projective, hence finitely presented.
-- To prove projectivity over `Λ[G]`, apply the local projectivity criterion over the localizations
-- `Λ_𝔭`; over each local ring `Λ_𝔭`, the localized module becomes free as a `Λ_𝔭`-module, and
-- Lemma `14-14.4-2` converts projectivity over `(Λ_𝔭)[G]` into projectivity of the corresponding
-- residue-field reduction over `𝔭.ResidueField[G]`; for maximal `𝔭`, this is canonically the
-- usual quotient-field reduction modulo `𝔭`.
/-- Helper for Exercise 14-14.4-5: localizing a finite projective `Λ`-module at a maximal ideal
produces a free module over the local ring `Λ_𝔭`. -/
lemma localized_tensor_free_of_projective
    (𝔭 : Ideal Λ) (h𝔭 : 𝔭.IsMaximal) (hP : Module.Projective Λ P) :
    Module.Free (Localization.AtPrime 𝔭) ((Localization.AtPrime 𝔭) ⊗[Λ] P) := by
  letI : 𝔭.IsPrime := h𝔭.isPrime
  -- Localize the underlying projective `Λ`-module and then use freeness over the local ring.
  letI : Module.Projective (Localization.AtPrime 𝔭) ((Localization.AtPrime 𝔭) ⊗[Λ] P) :=
    Module.projective_of_isLocalizedModule 𝔭.primeCompl
      ((TensorProduct.mk Λ (Localization.AtPrime 𝔭) P) 1)
  letI : Module.Flat (Localization.AtPrime 𝔭) ((Localization.AtPrime 𝔭) ⊗[Λ] P) :=
    Module.Flat.of_projective
  letI : Module.Finite (Localization.AtPrime 𝔭) ((Localization.AtPrime 𝔭) ⊗[Λ] P) := by
    infer_instance
  exact Module.free_of_flat_of_isLocalRing

/-- Helper for Exercise 14-14.4-5: residue-field reduction after localizing at `𝔭` is the same
as reducing the original module directly to `𝔭.ResidueField`. -/
noncomputable def residueField_tensor_localization_assoc
    (𝔭 : Ideal Λ) (h𝔭 : 𝔭.IsMaximal) :
    (𝔭.ResidueField ⊗[Localization.AtPrime 𝔭] ((Localization.AtPrime 𝔭) ⊗[Λ] P)) ≃ₗ[𝔭.ResidueField]
      (𝔭.ResidueField ⊗[Λ] P) := by
  letI : 𝔭.IsPrime := h𝔭.isPrime
  -- Cancel the intermediate localization base change.
  exact
    TensorProduct.AlgebraTensorModule.cancelBaseChange Λ (Localization.AtPrime 𝔭)
      𝔭.ResidueField 𝔭.ResidueField P

/-- Helper for Exercise 14-14.4-5: the direct reduction map from the localized coefficient module
to the residue-field reduction of `P`. -/
noncomputable def localized_direct_reduction
    (𝔭 : Ideal Λ) (h𝔭 : 𝔭.IsMaximal) :
    ((Localization.AtPrime 𝔭) ⊗[Λ] P) →ₗ[Localization.AtPrime 𝔭]
      (𝔭.ResidueField ⊗[Λ] P) :=
  ((residueField_tensor_localization_assoc (P := P) (𝔭 := 𝔭) h𝔭).toLinearMap.restrictScalars
      (Localization.AtPrime 𝔭)).comp
    (TensorProduct.mk (Localization.AtPrime 𝔭) 𝔭.ResidueField
      ((Localization.AtPrime 𝔭) ⊗[Λ] P) 1)

omit [Finite G] [Module.Finite Λ P] in
/-- Helper for Exercise 14-14.4-5: after scalar extension from `Λ` to `κ`, the action of
`MonoidAlgebra.of κ G g` on a pure tensor keeps the scalar in the left factor and acts on the
vector factor through the original `Λ[G]`-action. -/
lemma monoidAlgebra_of_smul_tmul
    {κ : Type*} [CommRing κ] [Algebra Λ κ]
    (g : G) (a : κ) (x : P) :
    MonoidAlgebra.of κ G g • (a ⊗ₜ[Λ] x) =
      a ⊗ₜ[Λ] (MonoidAlgebra.of Λ G g • x) := by
  -- Rewrite the scalar-extended `κ[G]`-action through `Representation.single_smul`.
  let ρ : Representation Λ G P := Representation.ofModule' P
  let ρκ : Representation κ G (κ ⊗[Λ] P) := Representation.scalarExtension ρ
  have hsingle :=
    Representation.single_smul (ρ := ρκ) (t := (1 : κ)) (g := g)
      (v := TensorProduct.mk Λ κ P a x)
  simpa [ρ, ρκ, Representation.scalarExtension, Representation.ofModule',
    MonoidAlgebra.of_apply] using hsingle

omit [Finite G] [Module.Finite Λ P] in
/-- Helper for Exercise 14-14.4-5: the direct map from the localized tensor product to the
residue-field reduction is the canonical residue-field reduction over the local ring `Λ_𝔭`. -/
lemma localized_direct_reduction_map_monoidAlgebra_of
    (𝔭 : Ideal Λ) (h𝔭 : 𝔭.IsMaximal) (g : G)
    (a : Localization.AtPrime 𝔭) (x : P) :
    localized_direct_reduction (𝔭 := 𝔭) h𝔭
      (MonoidAlgebra.of (Localization.AtPrime 𝔭) G g • (a ⊗ₜ[Λ] x)) =
      MonoidAlgebra.of 𝔭.ResidueField G g •
        localized_direct_reduction (𝔭 := 𝔭) h𝔭 (a ⊗ₜ[Λ] x) := by
  -- Rewrite the localized action on pure tensors and then cancel the intermediate base change.
  rw [localized_direct_reduction, residueField_tensor_localization_assoc, LinearMap.comp_apply,
    monoidAlgebra_of_smul_tmul (Λ := Λ) (P := P) (κ := Localization.AtPrime 𝔭) g a x]
  simp [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
  symm
  simpa using
    monoidAlgebra_of_smul_tmul
      (Λ := Λ) (P := P) (κ := 𝔭.ResidueField) g (a • (1 : 𝔭.ResidueField)) x

omit [Module.Finite Λ P] in
/-- Helper for Exercise 14-14.4-5: base change sends the averaged conjugation operator on `u`
to the tensor of the averaged conjugation action on vectors. -/
lemma baseChange_sumOfConjugates_apply_tmul
    (𝔭 : Ideal Λ) (h𝔭 : 𝔭.IsMaximal) (u : Module.End Λ P)
    (a : Localization.AtPrime 𝔭) (x : P) :
    (Module.End.baseChangeHom Λ (Localization.AtPrime 𝔭) P u).sumOfConjugates G
      (a ⊗ₜ[Λ] x) = a ⊗ₜ[Λ] (u.sumOfConjugates G x) := by
  -- Expand the average into conjugation summands and evaluate each summand on `a ⊗ x`.
  rw [LinearMap.sumOfConjugates_apply, LinearMap.sumOfConjugates_apply, TensorProduct.tmul_sum]
  -- Compare the conjugation summands termwise after rewriting base change on pure tensors.
  refine Finset.sum_congr rfl ?_
  intro g _
  rw [LinearMap.conjugate_apply, LinearMap.conjugate_apply]
  rw [show MonoidAlgebra.single g (1 : Localization.AtPrime 𝔭) • (a ⊗ₜ[Λ] x) =
      a ⊗ₜ[Λ] (MonoidAlgebra.single g (1 : Λ) • x) by
      simpa [MonoidAlgebra.of_apply] using
        monoidAlgebra_of_smul_tmul (Λ := Λ) (P := P) (κ := Localization.AtPrime 𝔭) g a x]
  rw [show ((Module.End.baseChangeHom Λ (Localization.AtPrime 𝔭) P) u)
      (a ⊗ₜ[Λ] (MonoidAlgebra.single g (1 : Λ) • x)) =
      a ⊗ₜ[Λ] u (MonoidAlgebra.single g (1 : Λ) • x) by
      simpa [Module.End.baseChangeHom] using
        (LinearMap.baseChange_tmul (f := u) (A := Localization.AtPrime 𝔭) a
          (MonoidAlgebra.single g (1 : Λ) • x))]
  rw [show MonoidAlgebra.single g⁻¹ (1 : Localization.AtPrime 𝔭) •
      (a ⊗ₜ[Λ] u (MonoidAlgebra.single g (1 : Λ) • x)) =
      MonoidAlgebra.of (Localization.AtPrime 𝔭) G g⁻¹ •
        (a ⊗ₜ[Λ] u (MonoidAlgebra.single g (1 : Λ) • x)) by rfl]
  simpa using
    monoidAlgebra_of_smul_tmul
      (Λ := Λ) (P := P) (κ := Localization.AtPrime 𝔭) g⁻¹ a
      (u (MonoidAlgebra.single g (1 : Λ) • x))

omit [Finite G] [Module.Finite Λ P] in
/-- Helper for Exercise 14-14.4-5: the direct map from the localized tensor product to the
residue-field reduction is the canonical residue-field reduction over the local ring `Λ_𝔭`. -/
lemma localized_direct_reduction_isResidueFieldReduction
    (𝔭 : Ideal Λ) (h𝔭 : 𝔭.IsMaximal) :
    ((localized_direct_reduction (𝔭 := 𝔭) h𝔭 :
        ((Localization.AtPrime 𝔭) ⊗[Λ] P) →ₗ[Localization.AtPrime 𝔭]
          (𝔭.ResidueField ⊗[Λ] P))).IsResidueFieldReduction G := by
  constructor
  · -- The map is the canonical local tensor-product reduction followed by the cancellation
    -- equivalence that removes the intermediate localization.
    refine IsBaseChange.of_equiv
      (residueField_tensor_localization_assoc (P := P) (𝔭 := 𝔭) h𝔭) ?_
    intro z
    rfl
  · -- Check equivariance on pure tensors and extend by tensor induction.
    refine Representation.IsIntertwiningMap.mk ?_
    intro g z
    induction z using TensorProduct.induction_on with
    | zero =>
        simp [localized_direct_reduction]
    | tmul a x =>
        change localized_direct_reduction (P := P) (𝔭 := 𝔭) h𝔭
            (MonoidAlgebra.of (Localization.AtPrime 𝔭) G g • (a ⊗ₜ[Λ] x)) =
          (MonoidAlgebra.mapRingHom G (algebraMap (Localization.AtPrime 𝔭) 𝔭.ResidueField)
            (MonoidAlgebra.of (Localization.AtPrime 𝔭) G g)) •
            localized_direct_reduction (P := P) (𝔭 := 𝔭) h𝔭 (a ⊗ₜ[Λ] x)
        simpa using localized_direct_reduction_map_monoidAlgebra_of
          (G := G) (P := P) (𝔭 := 𝔭) h𝔭 g a x
    | add z w hz hw =>
        simp [hz, hw]

/-- Helper for Exercise 14-14.4-5: over the local ring `Λ_𝔭`, Serre's local criterion identifies
projectivity over `(Λ_𝔭)[G]` with projectivity of the residue-field reduction over
`𝔭.ResidueField[G]`. -/
theorem localized_projective_iff_projective_residueField_reduction
    (𝔭 : Ideal Λ) (h𝔭 : 𝔭.IsMaximal) (hP : Module.Projective Λ P) :
    Module.Projective ((Localization.AtPrime 𝔭)[G]) ((Localization.AtPrime 𝔭) ⊗[Λ] P) ↔
      Module.Projective (𝔭.ResidueField[G]) (𝔭.ResidueField ⊗[Λ] P) := by
  letI : 𝔭.IsPrime := h𝔭.isPrime
  letI : Module.Free (Localization.AtPrime 𝔭) ((Localization.AtPrime 𝔭) ⊗[Λ] P) :=
    localized_tensor_free_of_projective (𝔭 := 𝔭) h𝔭 hP
  have hf :
      ((localized_direct_reduction (𝔭 := 𝔭) h𝔭 :
          ((Localization.AtPrime 𝔭) ⊗[Λ] P) →ₗ[Localization.AtPrime 𝔭]
            (𝔭.ResidueField ⊗[Λ] P))).IsResidueFieldReduction G :=
    -- Reuse the transported local residue-field reduction prepared above.
    localized_direct_reduction_isResidueFieldReduction (G := G) (P := P) (𝔭 := 𝔭) h𝔭
  -- Route correction: use the direct reduction map `f` into `𝔭.ResidueField ⊗[Λ] P`, so the
  -- local criterion applies without a separate equivariant transport lemma.
  simpa [localized_direct_reduction] using
    (projective_monoidAlgebra_iff_projective_of_isResidueFieldReduction
      (Λ := Localization.AtPrime 𝔭) (G := G) (P := (Localization.AtPrime 𝔭) ⊗[Λ] P)
      (Pbar := 𝔭.ResidueField ⊗[Λ] P)
      (localized_direct_reduction (𝔭 := 𝔭) h𝔭) hf)

omit [Module.Finite Λ P] in
/-- Helper for Exercise 14-14.4-5: base change carries a global averaging identity to the
localization `Λ_𝔭 ⊗[Λ] P`. -/
lemma localized_sumOfConjugates_eq_id
    (𝔭 : Ideal Λ) (h𝔭 : 𝔭.IsMaximal) (u : Module.End Λ P)
    (hu : u.sumOfConjugates G = LinearMap.id) :
    let A := Localization.AtPrime 𝔭
    let uA : Module.End A (A ⊗[Λ] P) := Module.End.baseChangeHom Λ A P u
    uA.sumOfConjugates G = LinearMap.id := by
  dsimp
  -- Tensor induction reduces the localized averaging equation to pure tensors.
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul a x =>
      -- On pure tensors, base change carries the average to the tensor of the averaged vector.
      calc
        (Module.End.baseChangeHom Λ (Localization.AtPrime 𝔭) P u).sumOfConjugates G
            (a ⊗ₜ[Λ] x) = a ⊗ₜ[Λ] (u.sumOfConjugates G x) := by
              simpa using baseChange_sumOfConjugates_apply_tmul
                (𝔭 := 𝔭) h𝔭 u a x
        _ = a ⊗ₜ[Λ] x := by
              simp [hu]
  | add z w hz hw =>
      simp [hz, hw]

omit [Module.Finite Λ P] in
/-- Helper for Exercise 14-14.4-5: localizing a projective `Λ[G]`-module at a maximal ideal of
`Λ` yields a projective module over the localized group algebra. -/
lemma localized_group_algebra_projective_of_projective
    (𝔭 : Ideal Λ) (h𝔭 : 𝔭.IsMaximal) (hP : Module.Projective Λ P) :
    Module.Projective Λ[G] P →
      Module.Projective ((Localization.AtPrime 𝔭)[G]) ((Localization.AtPrime 𝔭) ⊗[Λ] P) := by
  intro hproj
  letI : 𝔭.IsPrime := h𝔭.isPrime
  let A := Localization.AtPrime 𝔭
  have hPA : Module.Projective A (A ⊗[Λ] P) :=
    -- First localize the underlying projective `Λ`-module.
    Module.projective_of_isLocalizedModule 𝔭.primeCompl
      ((TensorProduct.mk Λ A P) 1)
  rcases
      (projective_groupAlgebra_iff_projective_and_exists_averaging_endomorphism
        (Λ := Λ) (G := G) (P := P)).mp hproj with ⟨_, u, hu⟩
  -- Reapply Serre's averaging criterion after base change to `Λ_𝔭`.
  refine
    (projective_groupAlgebra_iff_projective_and_exists_averaging_endomorphism
      (Λ := A) (G := G) (P := A ⊗[Λ] P)).mpr ?_
  refine ⟨hPA, Module.End.baseChangeHom Λ A P u, ?_⟩
  exact localized_sumOfConjugates_eq_id (G := G) (P := P) (𝔭 := 𝔭) h𝔭 u hu

/-
The next two helper lemmas only use the group action on `P`; they do not depend on the finiteness
assumption carried by the section.
-/
omit [Module.Finite Λ P] in
/-- Helper for Exercise 14-14.4-5: the averaged conjugation operator is additive on
`End_Λ(P)`. -/
lemma sumOfConjugates_end_add (u v : Module.End Λ P) :
    (u + v).sumOfConjugates G = u.sumOfConjugates G + v.sumOfConjugates G := by
  -- Expand the three averages pointwise and distribute the conjugation sum over addition.
  ext x
  calc
    (u + v).sumOfConjugates G x = ∑ g : G, (u + v).conjugate g x := by
      rw [LinearMap.sumOfConjugates_apply]
    _ = ∑ g : G, (u.conjugate g x + v.conjugate g x) := by
          refine Finset.sum_congr rfl fun g _ ↦ ?_
          simp [LinearMap.conjugate_apply]
    _ = ∑ g : G, u.conjugate g x + ∑ g : G, v.conjugate g x := by
          rw [Finset.sum_add_distrib]
    _ = u.sumOfConjugates G x + v.sumOfConjugates G x := by
          rw [LinearMap.sumOfConjugates_apply, LinearMap.sumOfConjugates_apply]

omit [Module.Finite Λ P] in
/-- Helper for Exercise 14-14.4-5: the averaged conjugation operator is `Λ`-linear on
`End_Λ(P)`. -/
lemma sumOfConjugates_end_smul (a : Λ) (u : Module.End Λ P) :
    (a • u).sumOfConjugates G = a • u.sumOfConjugates G := by
  -- Again compare pointwise after expanding the average into a finite sum of conjugates.
  ext x
  calc
    (a • u).sumOfConjugates G x = ∑ g : G, (a • u).conjugate g x := by
      rw [LinearMap.sumOfConjugates_apply]
    _ = ∑ g : G, a • (u.conjugate g x) := by
          refine Finset.sum_congr rfl fun g _ ↦ ?_
          simp [LinearMap.conjugate_apply, smul_comm a]
    _ = a • ∑ g : G, u.conjugate g x := by
          rw [Finset.smul_sum]
    _ = a • (u.sumOfConjugates G x) := by
          rw [LinearMap.sumOfConjugates_apply]

/-- Helper for Exercise 14-14.4-5: finite presentation identifies localized endomorphisms of `P`
with endomorphisms of the localized tensor module `Λ_𝔭 ⊗[Λ] P`. -/
noncomputable def localized_end_linearEquiv_tensor_end
    (𝔭 : Ideal Λ) (h𝔭 : 𝔭.IsMaximal) (hP : Module.Projective Λ P) :
    LocalizedModule 𝔭.primeCompl (Module.End Λ P) ≃ₗ[Localization.AtPrime 𝔭]
      Module.End (Localization.AtPrime 𝔭) ((Localization.AtPrime 𝔭) ⊗[Λ] P) := by
  letI : 𝔭.IsPrime := h𝔭.isPrime
  letI : Module.FinitePresentation Λ P := Module.finitePresentation_of_projective Λ P
  let eMap : LocalizedModule 𝔭.primeCompl (Module.End Λ P) ≃ₗ[Λ]
      (LocalizedModule 𝔭.primeCompl P →ₗ[Localization.AtPrime 𝔭]
        LocalizedModule 𝔭.primeCompl P) :=
    Module.FinitePresentation.linearEquivMapExtendScalars
      (R := Λ) (M := P) (N := P) (S := 𝔭.primeCompl)
  let eTensor :
      (LocalizedModule 𝔭.primeCompl P →ₗ[Localization.AtPrime 𝔭]
        LocalizedModule 𝔭.primeCompl P) ≃ₗ[Localization.AtPrime 𝔭]
        Module.End (Localization.AtPrime 𝔭) ((Localization.AtPrime 𝔭) ⊗[Λ] P) := by
    -- Identify endomorphisms of the localized module with endomorphisms of the tensor model.
    simpa [Localization.AtPrime] using
      ((LocalizedModule.equivTensorProduct (S := 𝔭.primeCompl) (M := P)).arrowCongr
        (LocalizedModule.equivTensorProduct (S := 𝔭.primeCompl) (M := P)))
  let e : LocalizedModule 𝔭.primeCompl (Module.End Λ P) ≃ₗ[Λ]
      Module.End (Localization.AtPrime 𝔭) ((Localization.AtPrime 𝔭) ⊗[Λ] P) :=
    -- First localize the endomorphism space, then transport along the tensor-product model.
    eMap.trans (eTensor.restrictScalars Λ)
  -- The composite is already `Λ`-linear between `Λ_𝔭`-modules, so upgrade it to `Λ_𝔭`-linearity.
  exact e.extendScalarsOfIsLocalization 𝔭.primeCompl (Localization.AtPrime 𝔭)

/-- Helper for Exercise 14-14.4-5: the averaging operator on `End_Λ(P)` is `Λ`-linear. -/
noncomputable def sumOfConjugates_end_linearMap :
    Module.End Λ P →ₗ[Λ] Module.End Λ P where
  toFun u := u.sumOfConjugates G
  map_add' u v := sumOfConjugates_end_add (G := G) u v
  map_smul' a u := sumOfConjugates_end_smul (G := G) a u

/-- Helper for Exercise 14-14.4-5: the endomorphism-localization equivalence sends a global
endomorphism generator to its tensor-base-change endomorphism. -/
lemma localized_end_linearEquiv_tensor_end_apply_mk
    (𝔭 : Ideal Λ) (h𝔭 : 𝔭.IsMaximal) (hP : Module.Projective Λ P) (u : Module.End Λ P) :
    localized_end_linearEquiv_tensor_end (P := P) (𝔭 := 𝔭) h𝔭 hP
      ((LocalizedModule.mkLinearMap 𝔭.primeCompl (Module.End Λ P)) u) =
      Module.End.baseChangeHom Λ (Localization.AtPrime 𝔭) P u := by
  letI : 𝔭.IsPrime := h𝔭.isPrime
  letI : Module.FinitePresentation Λ P := Module.finitePresentation_of_projective Λ P
  -- Unfold the localization equivalence only to the finite-presentation comparison and then
  -- identify the localized module with the tensor-product base change.
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul a x =>
      obtain ⟨r, s, hs⟩ := IsLocalization.exists_mk'_eq 𝔭.primeCompl a
      rw [← Localization.mk_eq_mk'] at hs
      rw [← hs]
      dsimp [localized_end_linearEquiv_tensor_end]
      rw [show LocalizedModule.mk u 1 =
        (LocalizedModule.mkLinearMap 𝔭.primeCompl (Module.End Λ P)) u by rfl]
      rw [Module.FinitePresentation.linearEquivMapExtendScalars_apply]
      calc
        (LocalizedModule.equivTensorProduct 𝔭.primeCompl P)
            (((IsLocalizedModule.mapExtendScalars 𝔭.primeCompl
                  (LocalizedModule.mkLinearMap 𝔭.primeCompl P)
                  (LocalizedModule.mkLinearMap 𝔭.primeCompl P)
                  (Localization.AtPrime 𝔭)) u)
                ((LocalizedModule.equivTensorProduct 𝔭.primeCompl P).symm
                  (Localization.mk r s ⊗ₜ[Λ] x))) =
          (LocalizedModule.equivTensorProduct 𝔭.primeCompl P)
            (r •
              ((IsLocalizedModule.map 𝔭.primeCompl
                  (LocalizedModule.mkLinearMap 𝔭.primeCompl P)
                  (LocalizedModule.mkLinearMap 𝔭.primeCompl P)) u)
                (LocalizedModule.mk x s)) := by
              simp [IsLocalizedModule.mapExtendScalars]
        _ =
          (LocalizedModule.equivTensorProduct 𝔭.primeCompl P) (r • LocalizedModule.mk (u x) s) := by
              congr 1
              congr 1
              simpa [IsLocalizedModule.mk_eq_mk'] using
                (IsLocalizedModule.map_mk' (S := 𝔭.primeCompl)
                  (f := LocalizedModule.mkLinearMap 𝔭.primeCompl P)
                  (g := LocalizedModule.mkLinearMap 𝔭.primeCompl P) u x s)
        _ = Localization.mk r s ⊗ₜ[Λ] u x := by
              calc
                (LocalizedModule.equivTensorProduct 𝔭.primeCompl P) (r • LocalizedModule.mk (u x) s) =
                  (LocalizedModule.equivTensorProduct 𝔭.primeCompl P)
                    (LocalizedModule.mk (r • u x) s) := by
                    simp [LocalizedModule.smul'_mk]
                _ = Localization.mk 1 s ⊗ₜ[Λ] (r • u x) := by
                    simp
                _ = (r • Localization.mk 1 s) ⊗ₜ[Λ] u x := by
                    rw [TensorProduct.smul_tmul]
                _ = Localization.mk r s ⊗ₜ[Λ] u x := by
                    apply congrArg (fun t ↦ t ⊗ₜ[Λ] u x)
                    rw [Algebra.smul_def, Localization.mk_eq_mk']
                    rw [← IsLocalization.mk'_eq_mul_mk'_one]
        _ = ((Module.End.baseChangeHom Λ (Localization.AtPrime 𝔭) P) u)
              (Localization.mk r s ⊗ₜ[Λ] x) := by
              simpa [Module.End.baseChangeHom] using
                (LinearMap.baseChange_tmul (f := u) (A := Localization.AtPrime 𝔭)
                  (Localization.mk r s) x)
  | add z w hz hw =>
      simpa [map_add] using congrArg₂ HAdd.hAdd hz hw

/-- Helper for Exercise 14-14.4-5: the endomorphism-localization equivalence sends a fraction
`u / s` to the corresponding scalar multiple of the base-changed endomorphism. -/
lemma localized_end_linearEquiv_tensor_end_apply_fraction
    (𝔭 : Ideal Λ) (h𝔭 : 𝔭.IsMaximal) (hP : Module.Projective Λ P)
    (u : Module.End Λ P) (s : 𝔭.primeCompl) :
    localized_end_linearEquiv_tensor_end (P := P) (𝔭 := 𝔭) h𝔭 hP (LocalizedModule.mk u s) =
      Localization.mk 1 s • Module.End.baseChangeHom Λ (Localization.AtPrime 𝔭) P u := by
  -- Rewrite the localized element as a scalar multiple of the denominator-one generator.
  have hmk :
      LocalizedModule.mk u s =
        Localization.mk 1 s •
          ((LocalizedModule.mkLinearMap 𝔭.primeCompl (Module.End Λ P)) u) := by
    symm
    simpa using
      (LocalizedModule.mk_smul_mk (S := 𝔭.primeCompl) (r := (1 : Λ)) (m := u)
        (s := s) (t := (1 : 𝔭.primeCompl)))
  calc
    localized_end_linearEquiv_tensor_end (P := P) (𝔭 := 𝔭) h𝔭 hP (LocalizedModule.mk u s) =
      localized_end_linearEquiv_tensor_end (P := P) (𝔭 := 𝔭) h𝔭 hP
        (Localization.mk 1 s • ((LocalizedModule.mkLinearMap 𝔭.primeCompl (Module.End Λ P)) u)) := by
          rw [hmk]
    _ = Localization.mk 1 s •
        localized_end_linearEquiv_tensor_end (P := P) (𝔭 := 𝔭) h𝔭 hP
          ((LocalizedModule.mkLinearMap 𝔭.primeCompl (Module.End Λ P)) u) := by
          exact LinearMap.map_smul_of_tower _ _ _
    _ = Localization.mk 1 s • Module.End.baseChangeHom Λ (Localization.AtPrime 𝔭) P u := by
          congr 1
          exact localized_end_linearEquiv_tensor_end_apply_mk
            (P := P) (𝔭 := 𝔭) h𝔭 hP u

omit [Module.Finite Λ P] in
/-- Helper for Exercise 14-14.4-5: base change commutes with the averaged conjugation operator on
`End_Λ(P)`. -/
lemma baseChange_sumOfConjugates_end
    (𝔭 : Ideal Λ) (h𝔭 : 𝔭.IsMaximal) (u : Module.End Λ P) :
    (Module.End.baseChangeHom Λ (Localization.AtPrime 𝔭) P u).sumOfConjugates G =
      Module.End.baseChangeHom Λ (Localization.AtPrime 𝔭) P (u.sumOfConjugates G) := by
  -- Compare both endomorphisms on pure tensors and then extend by tensor induction.
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul a x =>
      calc
        (Module.End.baseChangeHom Λ (Localization.AtPrime 𝔭) P u).sumOfConjugates G
            (a ⊗ₜ[Λ] x) = a ⊗ₜ[Λ] (u.sumOfConjugates G x) := by
              simpa using baseChange_sumOfConjugates_apply_tmul
                (G := G) (P := P) (𝔭 := 𝔭) h𝔭 u a x
        _ = (Module.End.baseChangeHom Λ (Localization.AtPrime 𝔭) P
              (u.sumOfConjugates G)) (a ⊗ₜ[Λ] x) := by
              symm
              simpa [Module.End.baseChangeHom] using
                (LinearMap.baseChange_tmul (f := u.sumOfConjugates G)
                  (A := Localization.AtPrime 𝔭) a x)
  | add z w hz hw =>
      simp [hz, hw]

/-- Helper for Exercise 14-14.4-5: under the endomorphism-localization equivalence, localizing
the global averaging operator matches the averaging operator on the localized tensor module. -/
lemma localized_sumOfConjugates_end_commutes
    (𝔭 : Ideal Λ) (h𝔭 : 𝔭.IsMaximal) (hP : Module.Projective Λ P) :
    let A := Localization.AtPrime 𝔭
    let e := localized_end_linearEquiv_tensor_end (P := P) (𝔭 := 𝔭) h𝔭 hP
    e.toLinearMap.comp
        (LocalizedModule.map 𝔭.primeCompl
          (sumOfConjugates_end_linearMap (Λ := Λ) (G := G) (P := P))) =
      (sumOfConjugates_end_linearMap (Λ := A) (G := G) (P := A ⊗[Λ] P)).comp e.toLinearMap := by
  let A := Localization.AtPrime 𝔭
  let e := localized_end_linearEquiv_tensor_end (P := P) (𝔭 := 𝔭) h𝔭 hP
  -- Since localized endomorphisms are generated by fractions `u / s`, it suffices to compare
  -- both operators on those generators.
  apply LinearMap.ext
  intro z
  refine z.induction_on ?_
  intro u s
  calc
    e (LocalizedModule.map 𝔭.primeCompl
        (sumOfConjugates_end_linearMap (Λ := Λ) (G := G) (P := P))
        (LocalizedModule.mk u s)) =
      e (LocalizedModule.mk (u.sumOfConjugates G) s) := by
        simp [sumOfConjugates_end_linearMap]
    _ = Localization.mk 1 s • Module.End.baseChangeHom Λ A P (u.sumOfConjugates G) := by
        simpa [A] using localized_end_linearEquiv_tensor_end_apply_fraction
          (P := P) (𝔭 := 𝔭) h𝔭 hP (u.sumOfConjugates G) s
    _ = Localization.mk 1 s •
        (sumOfConjugates_end_linearMap (Λ := A) (G := G) (P := A ⊗[Λ] P))
          (Module.End.baseChangeHom Λ A P u) := by
        simp [sumOfConjugates_end_linearMap, baseChange_sumOfConjugates_end, A]
    _ = (sumOfConjugates_end_linearMap (Λ := A) (G := G) (P := A ⊗[Λ] P))
        (Localization.mk 1 s • Module.End.baseChangeHom Λ A P u) := by
        simp [sumOfConjugates_end_linearMap]
    _ = (sumOfConjugates_end_linearMap (Λ := A) (G := G) (P := A ⊗[Λ] P))
        (e (LocalizedModule.mk u s)) := by
        rw [localized_end_linearEquiv_tensor_end_apply_fraction
          (P := P) (𝔭 := 𝔭) h𝔭 hP u s]

/-- Helper for Exercise 14-14.4-5: each local projective residue-field reduction puts the
localized identity endomorphism in the localized range of the global averaging operator. -/
lemma localized_id_mem_sumOfConjugates_end_range
    (𝔭 : Ideal Λ) (h𝔭 : 𝔭.IsMaximal) (hP : Module.Projective Λ P)
    (hres : Module.Projective (𝔭.ResidueField[G]) (𝔭.ResidueField ⊗[Λ] P)) :
    (LocalizedModule.mkLinearMap 𝔭.primeCompl (Module.End Λ P)) LinearMap.id ∈
      (LinearMap.range (sumOfConjugates_end_linearMap (Λ := Λ) (G := G) (P := P))).localized₀
        𝔭.primeCompl (LocalizedModule.mkLinearMap 𝔭.primeCompl (Module.End Λ P)) := by
  let A := Localization.AtPrime 𝔭
  let T := sumOfConjugates_end_linearMap (Λ := Λ) (G := G) (P := P)
  let TA := sumOfConjugates_end_linearMap (Λ := A) (G := G) (P := A ⊗[Λ] P)
  let e := localized_end_linearEquiv_tensor_end (P := P) (𝔭 := 𝔭) h𝔭 hP
  have hlocal :
      Module.Projective (A[G]) (A ⊗[Λ] P) :=
    (localized_projective_iff_projective_residueField_reduction
      (G := G) (P := P) (𝔭 := 𝔭) h𝔭 hP).mpr hres
  rcases
      (projective_groupAlgebra_iff_projective_and_exists_averaging_endomorphism
        (Λ := A) (G := G) (P := A ⊗[Λ] P)).mp hlocal with ⟨_, uA, huA⟩
  -- Rewrite localized range membership as membership in the range of the localized operator.
  have hrange :
      LinearMap.range
        (IsLocalizedModule.map 𝔭.primeCompl
          (LocalizedModule.mkLinearMap 𝔭.primeCompl (Module.End Λ P))
          (LocalizedModule.mkLinearMap 𝔭.primeCompl (Module.End Λ P)) T) =
      (LinearMap.range T).localized₀ 𝔭.primeCompl
        (LocalizedModule.mkLinearMap 𝔭.primeCompl (Module.End Λ P)) :=
    LinearMap.range_localizedMap_eq_localized₀_range
      (p := 𝔭.primeCompl)
      (f := LocalizedModule.mkLinearMap 𝔭.primeCompl (Module.End Λ P))
      (f' := LocalizedModule.mkLinearMap 𝔭.primeCompl (Module.End Λ P))
      (g := T)
  rw [← hrange]
  refine ⟨e.symm uA, ?_⟩
  apply e.injective
  -- Transport the localized equation to the tensor-endomorphism model and use the local witness.
  calc
    e ((LocalizedModule.map 𝔭.primeCompl T) (e.symm uA)) =
      TA uA := by
        simpa [T, TA, e, A] using congrArg (fun f ↦ f (e.symm uA))
          (localized_sumOfConjugates_end_commutes (G := G) (P := P) (𝔭 := 𝔭) h𝔭 hP)
    _ = LinearMap.id := huA
    _ = e ((LocalizedModule.mkLinearMap 𝔭.primeCompl (Module.End Λ P)) LinearMap.id) := by
        have hidBase :
            Module.End.baseChangeHom Λ (Localization.AtPrime 𝔭) P
              (LinearMap.id : Module.End Λ P) = LinearMap.id := by
          simpa [Module.End.one_eq_id] using
            map_one (Module.End.baseChangeHom Λ (Localization.AtPrime 𝔭) P)
        symm
        rw [localized_end_linearEquiv_tensor_end_apply_mk
          (P := P) (𝔭 := 𝔭) h𝔭 hP (LinearMap.id : Module.End Λ P)]
        exact hidBase

/-- Helper for Exercise 14-14.4-5: if every maximal residue-field reduction is projective, then
the global averaging equation already has a solution over `Λ`. -/
lemma averaging_endomorphism_exists_of_local_residue_reductions
    (hP : Module.Projective Λ P) :
    (∀ (𝔭 : Ideal Λ) (_ : 𝔭.IsMaximal),
      Module.Projective (𝔭.ResidueField[G]) (𝔭.ResidueField ⊗[Λ] P)) →
      ∃ u : Module.End Λ P, u.sumOfConjugates G = LinearMap.id := by
  intro hres
  let T := sumOfConjugates_end_linearMap (Λ := Λ) (G := G) (P := P)
  have hid : LinearMap.id ∈ LinearMap.range T := by
    -- Globalize local range membership of the identity through the maximal-local criterion.
    refine Submodule.mem_of_localization_maximal
      (Mₚ := fun 𝔭 _ ↦ LocalizedModule 𝔭.primeCompl (Module.End Λ P))
      (f := fun 𝔭 _ ↦ LocalizedModule.mkLinearMap 𝔭.primeCompl (Module.End Λ P))
      LinearMap.id (LinearMap.range T) ?_
    intro 𝔭 h𝔭
    exact localized_id_mem_sumOfConjugates_end_range
      (G := G) (P := P) (𝔭 := 𝔭) h𝔭 hP (hres 𝔭 h𝔭)
  rcases hid with ⟨u, hu⟩
  -- Unpack the range membership as the required global averaging identity.
  refine ⟨u, ?_⟩
  simpa [T, sumOfConjugates_end_linearMap] using hu

/-- Exercise 14-14.4-5: for a finite `Λ[G]`-module `P` whose underlying `Λ`-module is projective,
`P` is projective over `Λ[G]` if and only if for every maximal ideal `𝔭` of `Λ`, the reduction
of `P` modulo `𝔭` is projective over the corresponding residue-field group algebra. -/
theorem projective_monoidAlgebra_iff_projective_reduction_mod_maximal_ideals
    (hP : Module.Projective Λ P) :
    Module.Projective Λ[G] P ↔
      ∀ (𝔭 : Ideal Λ) (_ : 𝔭.IsMaximal),
        Module.Projective (𝔭.ResidueField[G]) (𝔭.ResidueField ⊗[Λ] P) := by
  constructor
  · intro hproj 𝔭 h𝔭
    letI : 𝔭.IsPrime := h𝔭.isPrime
    -- Route correction: obtain the localized group-algebra projectivity directly from the
    -- global averaging identity, then apply the local residue-field criterion.
    have hlocalized :
        Module.Projective ((Localization.AtPrime 𝔭)[G]) ((Localization.AtPrime 𝔭) ⊗[Λ] P) :=
      localized_group_algebra_projective_of_projective
        (G := G) (P := P) (𝔭 := 𝔭) h𝔭 hP hproj
    exact
      (localized_projective_iff_projective_residueField_reduction
        (𝔭 := 𝔭) h𝔭 hP).mp hlocalized
  · intro hres
    rcases
        averaging_endomorphism_exists_of_local_residue_reductions
          (G := G) (P := P) hP hres with ⟨u, hu⟩
    -- Once the averaging identity is globalized, Lemma `14-14.4-1` closes the proof.
    exact
      (projective_groupAlgebra_iff_projective_and_exists_averaging_endomorphism
        (Λ := Λ) (G := G) (P := P)).mpr ⟨hP, u, hu⟩

end
