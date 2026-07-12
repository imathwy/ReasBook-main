import Mathlib.RingTheory.FiniteStability
import StacksProject_2024.Chap15.Lemma_15_81_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

open scoped TensorProduct
open Algebra.TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section

/- Domain-style sampling:
- primary domain: relative finite presentation of modules under scalar base change;
- sampled owner declarations:
  `Module.FinitePresentationRelativeTo`,
  `Module.FinitePresentationRelativeTo.overPolynomialPresentation`,
  `Module.FinitePresentation`,
  the tensor-base-change instance for `Module.FinitePresentation`;
- best owner abstraction: the source-facing predicate
  `Module.FinitePresentationRelativeTo R A M`;
- primitive data: one surjective polynomial presentation of `A` over `R` together with finite
  presentation of `M` over that presentation ring;
- derived API: presentation-independent finite presentation over any chosen polynomial
  presentation of `A`, the tensor-base-change instance for `Module.FinitePresentation`, the
  canonical `R'`-algebra structure on `A ⊗[R] R'`, and the relative finite-presentation
  statement for the base-changed module.

Source/core/bridge triage:
- `source-facing`: the theorem below about relative finite presentation after the base change
  `R → R'`;
- `core/canonical`: `Module.FinitePresentation` and `Algebra.FiniteType`;
- `bridge/view`: `MvPolynomial.algebraTensorAlgEquiv` and the standard tensor base-change
  equivalences identifying the presentation ring and module after scalar extension, together with
  the canonical right-action `R'`-algebra structure on `A ⊗[R] R'`.

The owner is already the correct source-facing predicate, so the main theorem should live on the
`Module` namespace and reuse the chapter owner API
`Module.FinitePresentationRelativeTo.overPolynomialPresentation` beneath that owner rather than
unpack one particular witness and duplicate that bridge locally. -/

variable {R : Type u} {A : Type v} {M : Type w} {R' : Type x}
variable [CommRing R] [CommRing A] [CommRing R']
variable [Algebra R A] [Algebra R R']
variable [AddCommGroup M] [Module A M]

-- Proof sketch: choose any polynomial presentation `P → A` coming from the finite-type algebra
-- structure implicit in `hM`, obtain `Module.FinitePresentation P M` from the canonical owner API
-- `hM.overPolynomialPresentation`, base-change `P` to `R'`, rewrite that base change as a
-- polynomial ring over `R'`, and then apply the standard tensor-base-change stability of
-- `Module.FinitePresentation` to the induced presentation of `((A ⊗[R] R') ⊗[A] M)`.
/-- Helper for Lemma 15.81.5: the canonical base-changed map
`(P ⊗[R] R') → (A ⊗[R] R')` is an `R'`-algebra map. -/
noncomputable def base_change_cover_map
    {P : Type u} [CommRing P] [Algebra R P] [Algebra P A]
    [IsScalarTower R P A]
    (α : P →ₐ[R] A) :
    (P ⊗[R] R') →ₐ[R'] (A ⊗[R] R') := by
  let fR : (P ⊗[R] R') →ₐ[R] (A ⊗[R] R') :=
    Algebra.TensorProduct.map α (AlgHom.id R R')
  refine
    { toRingHom := fR.toRingHom
      commutes' := ?_ }
  -- The tensor map fixes the right tensor factor, so it respects the `R'`-algebra structure.
  intro r
  change (Algebra.TensorProduct.map α (AlgHom.id R R')) (1 ⊗ₜ[R] r) = 1 ⊗ₜ[R] r
  simp

/-- Helper for Lemma 15.81.5: base changing a surjective presentation map keeps it surjective. -/
lemma base_change_cover_map_surjective
    {P : Type u} [CommRing P] [Algebra R P] [Algebra P A]
    [IsScalarTower R P A]
    (α : P →ₐ[R] A) (hα : Function.Surjective α) :
    Function.Surjective (base_change_cover_map (R := R) (A := A) (R' := R') α) := by
  intro z
  -- Reduce surjectivity to pure tensors and lift generators through the original surjection.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · exact ⟨0, by simp [base_change_cover_map]⟩
  · intro a r
    rcases hα a with ⟨p, rfl⟩
    exact ⟨p ⊗ₜ[R] r, rfl⟩
  · intro z₁ z₂ hz₁ hz₂
    rcases hz₁ with ⟨w₁, rfl⟩
    rcases hz₂ with ⟨w₂, rfl⟩
    exact ⟨w₁ + w₂, by simp [base_change_cover_map]⟩

/-- Helper for Lemma 15.81.5: if `P` is finitely presented over `R`, then its base change
`P ⊗[R] R'` is finitely presented over `R'`. -/
lemma base_change_cover_source_finitePresentation
    {P : Type u} [CommRing P] [Algebra R P]
    (hPfp : Algebra.FinitePresentation R P) :
    Algebra.FinitePresentation R' (P ⊗[R] R') := by
  letI : Algebra.FinitePresentation R P := hPfp
  have hcomm : Algebra.FinitePresentation R' (R' ⊗[R] P) := by
    simpa using (Algebra.FinitePresentation.baseChange (R := R) (A := P) R')
  let eComm : (R' ⊗[R] P) ≃ₐ[R'] (P ⊗[R] R') := by
    refine
      { toRingEquiv := (Algebra.TensorProduct.comm R R' P).toRingEquiv
        commutes' := ?_ }
    -- The tensor symmetry also respects the canonical `R'`-algebra structure.
    intro r
    rfl
  -- Transport finite presentation across the tensor-symmetry algebra equivalence.
  exact Algebra.FinitePresentation.equiv eComm

/-- Helper for Lemma 15.81.5: the `R'`-action on the target tensor module induced from the
base-changed cover agrees with the canonical tensor-product `R'`-action. -/
lemma base_change_cover_target_scalar_tower
    {P : Type u} [CommRing P] [Algebra R P] [Algebra P A]
    [IsScalarTower R P A] [Module P A]
    [Module P M] [IsScalarTower P A M]
    (α : P →ₐ[R] A) :
    let f := base_change_cover_map (R := R) (A := A) (R' := R') α
    let _ : Module (P ⊗[R] R') ((A ⊗[R] R') ⊗[A] M) := Module.compHom _ f.toRingHom
    let _ : Module R' ((A ⊗[R] R') ⊗[A] M) := Module.compHom _ (algebraMap R' (A ⊗[R] R'))
    IsScalarTower R' (P ⊗[R] R') ((A ⊗[R] R') ⊗[A] M) := by
  let f := base_change_cover_map (R := R) (A := A) (R' := R') α
  letI : Module (P ⊗[R] R') ((A ⊗[R] R') ⊗[A] M) := Module.compHom _ f.toRingHom
  letI : Module R' ((A ⊗[R] R') ⊗[A] M) := Module.compHom _ (algebraMap R' (A ⊗[R] R'))
  -- The cover map is an `R'`-algebra map, so its induced scalar restriction matches the
  -- canonical `R'`-action on the tensor product.
  refine IsScalarTower.of_algebraMap_smul ?_
  intro r x
  change f (algebraMap R' (P ⊗[R] R') r) • x = (algebraMap R' (A ⊗[R] R') r) • x
  simp

/-- Helper for Lemma 15.81.5: the tensor map `P ⊗[R] R' → A ⊗[R] R'` agrees with the left
`P`-algebra map on elements coming from `P`. -/
lemma base_change_cover_map_algebraMap
    {P : Type u} [CommRing P] [Algebra R P]
    (α : P →ₐ[R] A) (p : P) :
    let _ : Algebra P A := α.toAlgebra
    let _ : IsScalarTower R P A := IsScalarTower.of_algebraMap_eq fun r ↦ by
      change algebraMap R A r = α (algebraMap R P r)
      exact (α.commutes r).symm
    base_change_cover_map (R := R) (A := A) (R' := R') α (algebraMap P (P ⊗[R] R') p) =
      α p ⊗ₜ[R] (1 : R') := by
  -- Both sides are the pure tensor `α p ⊗ 1`.
  letI : Algebra P A := α.toAlgebra
  letI : IsScalarTower R P A := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change algebraMap R A r = α (algebraMap R P r)
    exact (α.commutes r).symm
  rw [Algebra.TensorProduct.algebraMap_apply (R := R) (S := P) (A := P) (B := R')]
  simp [base_change_cover_map]

/-- Helper for Lemma 15.81.5: tensoring the cover map `P → A` with `R'` realizes
`A ⊗[R] R'` as the pushout of `P → A` along `P → P ⊗[R] R'`. -/
lemma base_change_cover_target_isPushout
    {P : Type u} [CommRing P] [Algebra R P]
    (α : P →ₐ[R] A) :
    let S := P ⊗[R] R'
    let _ : Algebra P A := α.toAlgebra
    let _ : IsScalarTower R P A := IsScalarTower.of_algebraMap_eq fun r ↦ by
      change algebraMap R A r = α (algebraMap R P r)
      exact (α.commutes r).symm
    let f := base_change_cover_map (R := R) (A := A) (R' := R') α
    let _ : Algebra S (A ⊗[R] R') := f.toAlgebra
    let _ : IsScalarTower P S (A ⊗[R] R') := IsScalarTower.of_algebraMap_eq fun p ↦ by
      simpa [RingHom.algebraMap_toAlgebra,
        Algebra.TensorProduct.algebraMap_apply (R := R) (S := P) (A := A) (B := R')] using
        (base_change_cover_map_algebraMap (R := R) (A := A) (R' := R') α p).symm
    let _ : IsScalarTower P A (A ⊗[R] R') := IsScalarTower.of_algebraMap_eq fun p ↦ by
      simp
    Algebra.IsPushout P S A (A ⊗[R] R') := by
  let S := P ⊗[R] R'
  letI : Algebra P A := α.toAlgebra
  letI : IsScalarTower R P A := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change algebraMap R A r = α (algebraMap R P r)
    exact (α.commutes r).symm
  let f := base_change_cover_map (R := R) (A := A) (R' := R') α
  letI : Algebra S (A ⊗[R] R') := f.toAlgebra
  letI : IsScalarTower P S (A ⊗[R] R') := IsScalarTower.of_algebraMap_eq fun p ↦ by
    simpa [RingHom.algebraMap_toAlgebra,
      Algebra.TensorProduct.algebraMap_apply (R := R) (S := P) (A := A) (B := R')] using
      (base_change_cover_map_algebraMap (R := R) (A := A) (R' := R') α p).symm
  letI : IsScalarTower P A (A ⊗[R] R') := IsScalarTower.of_algebraMap_eq fun p ↦ by
    simp
  -- The tensor product `A ⊗[R] R'` is the canonical pushout of `P → A` along `P → S`.
  have hPushoutPA :
      Algebra.IsPushout P A S (A ⊗[R] R') := by
    refine Algebra.IsPushout.tensorProduct_tensorProduct
      (R := R) (S := R') (A := P) (B := A) ?_
    ext r
    simp [f, base_change_cover_map, RingHom.algebraMap_toAlgebra]
  exact Algebra.IsPushout.symm hPushoutPA

/-- Helper for Lemma 15.81.5: the actual target tensor module is canonically the standard
base change of `M` from `P` to `P ⊗[R] R'`. -/
noncomputable def base_change_target_tensor_equiv
    {P : Type u} [CommRing P] [Algebra R P]
    (α : P →ₐ[R] A) :
    let S := P ⊗[R] R'
    let _ : Algebra P A := α.toAlgebra
    let _ : IsScalarTower R P A := IsScalarTower.of_algebraMap_eq fun r ↦ by
      change algebraMap R A r = α (algebraMap R P r)
      exact (α.commutes r).symm
    let _ : Module P A := Module.compHom A α.toRingHom
    let _ : Module P M := Module.compHom M α.toRingHom
    let _ : IsScalarTower P A M := IsScalarTower.of_compHom P A M
    let f := base_change_cover_map (R := R) (A := A) (R' := R') α
    let _ : Algebra S (A ⊗[R] R') := f.toAlgebra
    let _ : Module S ((A ⊗[R] R') ⊗[A] M) := Module.compHom _ f.toRingHom
    let _ : IsScalarTower P S (A ⊗[R] R') := IsScalarTower.of_algebraMap_eq fun p ↦ by
      simpa [RingHom.algebraMap_toAlgebra,
        Algebra.TensorProduct.algebraMap_apply (R := R) (S := P) (A := A) (B := R')] using
        (base_change_cover_map_algebraMap (R := R) (A := A) (R' := R') α p).symm
    let _ : IsScalarTower P A (A ⊗[R] R') := IsScalarTower.of_algebraMap_eq fun p ↦ by
      simp
    ((A ⊗[R] R') ⊗[A] M) ≃ₗ[S] S ⊗[P] M := by
  let S := P ⊗[R] R'
  letI : Algebra P A := α.toAlgebra
  letI : IsScalarTower R P A := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change algebraMap R A r = α (algebraMap R P r)
    exact (α.commutes r).symm
  letI : Module P A := Module.compHom A α.toRingHom
  letI : Module P M := Module.compHom M α.toRingHom
  letI : IsScalarTower P A M := IsScalarTower.of_compHom P A M
  let f := base_change_cover_map (R := R) (A := A) (R' := R') α
  letI : Algebra S (A ⊗[R] R') := f.toAlgebra
  letI : Module S ((A ⊗[R] R') ⊗[A] M) := Module.compHom _ f.toRingHom
  letI : IsScalarTower P S (A ⊗[R] R') := IsScalarTower.of_algebraMap_eq fun p ↦ by
    simpa [RingHom.algebraMap_toAlgebra,
      Algebra.TensorProduct.algebraMap_apply (R := R) (S := P) (A := A) (B := R')] using
      (base_change_cover_map_algebraMap (R := R) (A := A) (R' := R') α p).symm
  letI : IsScalarTower P A (A ⊗[R] R') := IsScalarTower.of_algebraMap_eq fun p ↦ by
    simp
  letI : Algebra.IsPushout P S A (A ⊗[R] R') :=
    base_change_cover_target_isPushout (R := R) (A := A) (R' := R') α
  -- Route correction: use the actual pushout square for `P → A` after tensoring with `R'`,
  -- so the comparison is the built-in `cancelBaseChange` on the true target ring.
  simpa [S] using
    (Algebra.IsPushout.cancelBaseChange
      (R := P) (S := S) (A := A) (B := A ⊗[R] R') M)

/-- Helper for Lemma 15.81.5: the actual target tensor module is finitely presented over the
base-changed cover ring `P ⊗[R] R'`. -/
lemma base_change_target_tensor_finitePresentation
    {P : Type u} [CommRing P] [Algebra R P]
    (α : P →ₐ[R] A)
    (hPM :
      let _ : Module P M := Module.compHom M α.toRingHom
      Module.FinitePresentation P M) :
    let S := P ⊗[R] R'
    let _ : Algebra P A := α.toAlgebra
    let _ : IsScalarTower R P A := IsScalarTower.of_algebraMap_eq fun r ↦ by
      change algebraMap R A r = α (algebraMap R P r)
      exact (α.commutes r).symm
    let _ : Module P A := Module.compHom A α.toRingHom
    let _ : Module P M := Module.compHom M α.toRingHom
    let _ : IsScalarTower P A M := IsScalarTower.of_compHom P A M
    let f := base_change_cover_map (R := R) (A := A) (R' := R') α
    let _ : Algebra S (A ⊗[R] R') := f.toAlgebra
    let _ : Module S ((A ⊗[R] R') ⊗[A] M) := Module.compHom _ f.toRingHom
    let _ : IsScalarTower P S (A ⊗[R] R') := IsScalarTower.of_algebraMap_eq fun p ↦ by
      simpa [RingHom.algebraMap_toAlgebra,
        Algebra.TensorProduct.algebraMap_apply (R := R) (S := P) (A := A) (B := R')] using
        (base_change_cover_map_algebraMap (R := R) (A := A) (R' := R') α p).symm
    let _ : IsScalarTower P A (A ⊗[R] R') := IsScalarTower.of_algebraMap_eq fun p ↦ by
      simp
    Module.FinitePresentation S ((A ⊗[R] R') ⊗[A] M) := by
  let S := P ⊗[R] R'
  letI : Algebra P A := α.toAlgebra
  letI : IsScalarTower R P A := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change algebraMap R A r = α (algebraMap R P r)
    exact (α.commutes r).symm
  letI : Module P A := Module.compHom A α.toRingHom
  letI : Module P M := Module.compHom M α.toRingHom
  letI : IsScalarTower P A M := IsScalarTower.of_compHom P A M
  let f := base_change_cover_map (R := R) (A := A) (R' := R') α
  letI : Algebra S (A ⊗[R] R') := f.toAlgebra
  letI : Module S ((A ⊗[R] R') ⊗[A] M) := Module.compHom _ f.toRingHom
  letI : IsScalarTower P S (A ⊗[R] R') := IsScalarTower.of_algebraMap_eq fun p ↦ by
    simpa [RingHom.algebraMap_toAlgebra,
      Algebra.TensorProduct.algebraMap_apply (R := R) (S := P) (A := A) (B := R')] using
      (base_change_cover_map_algebraMap (R := R) (A := A) (R' := R') α p).symm
  letI : IsScalarTower P A (A ⊗[R] R') := IsScalarTower.of_algebraMap_eq fun p ↦ by
    simp
  have hCoverTensor : Module.FinitePresentation S (S ⊗[P] M) := by
    letI : Module.FinitePresentation P M := by simpa using hPM
    infer_instance
  let e :=
    base_change_target_tensor_equiv
      (R := R) (A := A) (M := M) (R' := R') α
  -- First use the standard base-change instance on `S ⊗[P] M`, then transport back across the
  -- pushout comparison to the actual target tensor module.
  exact Module.FinitePresentation.of_equiv e.symm

/-- Helper for Lemma 15.81.5: the actual base-changed module is already finitely presented over
the actual base-changed target ring `A ⊗[R] R'`. -/
lemma base_change_target_finitePresentation_over_target
    {P : Type u} [CommRing P] [Algebra R P]
    (α : P →ₐ[R] A) (hα : Function.Surjective α)
    (hPM :
      let _ : Module P M := Module.compHom M α.toRingHom
      Module.FinitePresentation P M) :
    Module.FinitePresentation (A ⊗[R] R') ((A ⊗[R] R') ⊗[A] M) := by
  letI : Algebra P A := α.toAlgebra
  letI : Module P A := Module.compHom A α.toRingHom
  letI : Module P M := Module.compHom M α.toRingHom
  letI : IsScalarTower P A M := IsScalarTower.of_compHom P A M
  letI : Algebra.FiniteType P A := by
    have hα' : Function.Surjective (algebraMap P A) := by
      change Function.Surjective α
      simpa using hα
    rw [← RingHom.finiteType_algebraMap]
    exact RingHom.FiniteType.of_surjective (algebraMap P A) hα'
  letI : Module.FinitePresentation P M := by
    simpa using hPM
  -- First forget to the finitely generated presentation ring `P`, then recover finite
  -- presentation over `A` by the Chapter 10 finite-type scalar-restriction bridge.
  have hAM : Module.FinitePresentation A M :=
    Module.FinitePresentation.of_restrictScalars_finiteType P
  letI : Module.FinitePresentation A M := hAM
  -- Base change preserves finite presentation for the module over the actual target ring.
  infer_instance

/-- Helper for Lemma 15.81.5: after base changing a polynomial presentation `P → A` along
`R → R'`, the resulting map `(P ⊗[R] R') → (A ⊗[R] R')` is surjective, its source is a finitely
presented `R'`-algebra, and the target tensor module is finitely presented over that
base-changed presentation ring. -/
lemma exists_finitely_presented_base_change_cover
    {P : Type u} [CommRing P] [Algebra R P]
    (hPfp : Algebra.FinitePresentation R P)
    (α : P →ₐ[R] A) (hα : Function.Surjective α)
    (hPM :
      let _ : Module P M := Module.compHom M α.toRingHom
      Module.FinitePresentation P M) :
    ∃ (f : (P ⊗[R] R') →ₐ[R'] (A ⊗[R] R')),
      Function.Surjective f ∧
      Algebra.FinitePresentation R' (P ⊗[R] R') ∧
      let _ : Module (P ⊗[R] R') ((A ⊗[R] R') ⊗[A] M) := Module.compHom _ f.toRingHom
      Module.FinitePresentation (P ⊗[R] R') ((A ⊗[R] R') ⊗[A] M) := by
  letI : Algebra P A := α.toAlgebra
  letI : IsScalarTower R P A := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change algebraMap R A r = α (algebraMap R P r)
    exact (α.commutes r).symm
  letI : Module P A := Module.compHom A α.toRingHom
  letI : Module P M := Module.compHom M α.toRingHom
  letI : IsScalarTower P A M := IsScalarTower.of_compHom P A M
  let f := base_change_cover_map (R := R) (A := A) (R' := R') α
  refine ⟨f, base_change_cover_map_surjective (R := R) (A := A) (R' := R') α hα, ?_, ?_⟩
  · exact base_change_cover_source_finitePresentation (R := R) (R' := R') hPfp
  · letI : Module (P ⊗[R] R') ((A ⊗[R] R') ⊗[A] M) := Module.compHom _ f.toRingHom
    letI : Module R' ((A ⊗[R] R') ⊗[A] M) :=
      Module.compHom _ (algebraMap R' (A ⊗[R] R'))
    letI : IsScalarTower R' (P ⊗[R] R') ((A ⊗[R] R') ⊗[A] M) :=
      base_change_cover_target_scalar_tower (R := R) (A := A) (M := M) (R' := R') α
    letI : Algebra (P ⊗[R] R') (A ⊗[R] R') := f.toAlgebra
    letI : IsScalarTower P (P ⊗[R] R') (A ⊗[R] R') := IsScalarTower.of_algebraMap_eq fun p ↦ by
      simpa [RingHom.algebraMap_toAlgebra,
        Algebra.TensorProduct.algebraMap_apply (R := R) (S := P) (A := A) (B := R')] using
        (base_change_cover_map_algebraMap (R := R) (A := A) (R' := R') α p).symm
    letI : IsScalarTower P A (A ⊗[R] R') := IsScalarTower.of_algebraMap_eq fun p ↦ by
      simp
    -- The source-faithful step is the pushout comparison
    -- `((A ⊗[R] R') ⊗[A] M) ≃ₗ[P ⊗[R] R'] (P ⊗[R] R') ⊗[P] M`.
    simpa [f] using
      base_change_target_tensor_finitePresentation
        (R := R) (A := A) (M := M) (R' := R') α (by simpa using hPM)

/-- Lemma 15.81.5: if `M` is finitely presented relative to `R`, then for any base change
`R → R'` the base-changed `(A ⊗[R] R')`-module `((A ⊗[R] R') ⊗[A] M)`, canonically identified
with `M ⊗[R] R'`, is finitely presented relative to `R'`; the needed `R'`-algebra structure on
`A ⊗[R] R'` is the canonical tensor-product one, and the finite-type hypothesis on `R → A` is
already implicit in `Module.FinitePresentationRelativeTo R A M`. -/
theorem Module.finitePresentationRelativeTo_baseChange
    (hM : Module.FinitePresentationRelativeTo R A M) :
    Module.FinitePresentationRelativeTo R' (A ⊗[R] R') ((A ⊗[R] R') ⊗[A] M) := by
  rcases hM with ⟨n, α, hα, hPM⟩
  let P := MvPolynomial (Fin n) R
  letI : Algebra P A := α.toAlgebra
  letI : Module P A := Module.compHom A α.toRingHom
  letI : Module P M := Module.compHom M α.toRingHom
  letI : IsScalarTower P A M := IsScalarTower.of_compHom P A M
  -- Base change keeps the polynomial presentation ring finitely presented over the new base.
  have hPfp : Algebra.FinitePresentation R P := by
    simpa [P] using
      (Algebra.FinitePresentation.mvPolynomial_of_finitePresentation (Fin n))
  -- Route correction: isolate the pushout/tensor transport in one helper, then finish by
  -- packaging its finitely presented source ring with `Algebra.FinitePresentation.out`.
  obtain ⟨f, hf, hSfp, hSN⟩ :=
    exists_finitely_presented_base_change_cover
      (R := R) (A := A) (M := M) (R' := R') hPfp α hα (by simpa [P] using hPM)
  let S := P ⊗[R] R'
  letI : Module S ((A ⊗[R] R') ⊗[A] M) := Module.compHom _ f.toRingHom
  letI : Algebra.FinitePresentation R' S := hSfp
  letI : Module.FinitePresentation S ((A ⊗[R] R') ⊗[A] M) := by
    simpa [S] using hSN
  obtain ⟨m, β, hβ, hkerβ⟩ := (inferInstance : Algebra.FinitePresentation R' S).out
  let Q := MvPolynomial (Fin m) R'
  letI : Algebra Q S := β.toAlgebra
  letI : Module Q S := Module.compHom S β.toRingHom
  letI : Module Q ((A ⊗[R] R') ⊗[A] M) :=
    Module.compHom _ ((f.restrictScalars R').comp β).toRingHom
  letI : IsScalarTower Q S ((A ⊗[R] R') ⊗[A] M) := IsScalarTower.of_compHom Q S _
  -- Package the finitely presented intermediate `R'`-algebra `S` into the final relative witness.
  letI : Module.FinitePresentation Q S :=
    Module.finitePresentation_of_surjective
      (Algebra.linearMap Q S) hβ (by simpa using hkerβ)
  have hQN : Module.FinitePresentation Q ((A ⊗[R] R') ⊗[A] M) :=
    Module.FinitePresentation.trans Q ((A ⊗[R] R') ⊗[A] M) S
  have hcomp : Function.Surjective ((f.restrictScalars R').comp β) := by
    intro z
    rcases hf z with ⟨y, rfl⟩
    rcases hβ y with ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  refine ⟨m, (f.restrictScalars R').comp β, hcomp, ?_⟩
  simpa using hQN

end
