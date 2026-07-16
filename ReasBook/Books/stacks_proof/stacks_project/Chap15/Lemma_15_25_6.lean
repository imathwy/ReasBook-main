import Mathlib
import Mathlib.RingTheory.FiniteType
import stacks_proof.stacks_project.Chap10.Lemma_10_57_10
import stacks_proof.stacks_project.Chap10.Lemma_10_6_4
import stacks_proof.stacks_project.Chap15.Definition_15_22_1
import stacks_proof.stacks_project.Chap15.Lemma_15_22_10
import stacks_proof.stacks_project.Chap15.Lemma_15_25_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

open Module
open HomogeneousLocalization

attribute [local instance] RingHomInvPair.of_ringEquiv

/- Domain-style sampling:
- primary domain: finite-presentation descent for finite type algebras and finite modules over a
  valuation ring;
- sampled owner API:
  `exists_graded_localization_model_of_finite_module`,
  `flat_iff_isTorsionFree_of_valuationRing`,
  `graded_algebra_finitePresentation_of_flat`,
  `graded_module_finitePresentation_of_flat`,
  `primeLocalizationsDetectEquality_of_isDomain`;
- best owner abstraction: the public conclusions are already the canonical owner predicates
  `Algebra.FinitePresentation A B` and `Module.FinitePresentation B M`;
- source/core/bridge triage:
  `source-facing`: the two valuation-ring descent statements in this file;
  `core/canonical`: `Algebra.FinitePresentation` and `Module.FinitePresentation`;
  `bridge/view`: the graded localization model
  `exists_graded_localization_model_of_finite_module`, the valuation-ring flat/torsion-free bridge
  `flat_iff_isTorsionFree_of_valuationRing`, the domain detection bridge
  `primeLocalizationsDetectEquality_of_isDomain`, and the graded descent theorems
  `graded_algebra_finitePresentation_of_flat` and `graded_module_finitePresentation_of_flat`.

The only primitive public data here are the finite type / finite module hypotheses and flatness.
The module theorem should therefore stay at the `AddCommMonoid` owner level of
`Module.Finite`, `Module.Flat`, and `Module.FinitePresentation`; the graded presentation data are
derived bridge data from the sampled owner API and should not be reintroduced as public wrapper
structures or stronger ambient additive assumptions in this file.
-/

variable {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
variable {B : Type v} [CommRing B] [Algebra A B] [Algebra.FiniteType A B]

/-- Helper for Lemma 15.25.6: the `A`-torsion in an `A`-algebra is an ideal, so the source proof
can quotient the graded ring model by base torsion inside the category of algebras. -/
private def torsion_ideal_over_base
    {S : Type*} [CommRing S] [Algebra A S] :
    Ideal S where
  carrier := Submodule.torsion A S
  zero_mem' := (Submodule.torsion A S).zero_mem
  add_mem' := by
    intro x y hx hy
    exact (Submodule.torsion A S).add_mem hx hy
  smul_mem' := by
    intro s x hx
    rcases (mem_torsion_iff_exists_ne_zero_smul_eq_zero (R := A) (M := S) x).1 hx with
      ⟨a, ha0, hax⟩
    refine (mem_torsion_iff_exists_ne_zero_smul_eq_zero (R := A) (M := S) (s * x)).2 ?_
    refine ⟨a, ha0, ?_⟩
    have hsax : s * (a • x) = 0 := by
      -- Proof comment: multiplying a vanishing torsion relation by `s` preserves the relation.
      simpa [Algebra.smul_def] using congrArg (fun y ↦ s * y) hax
    calc
      a • (s * x) = s * (a • x) := by
        simp [Algebra.smul_def, mul_assoc, mul_comm]
      _ = 0 := hsax

/-- Helper for Lemma 15.25.6: after forgetting from `S` to `A`, the promoted torsion ideal is
exactly the usual `A`-torsion submodule. -/
private theorem torsion_ideal_over_base_restrictScalars
    {S : Type*} [CommRing S] [Algebra A S] :
    Submodule.restrictScalars A (torsion_ideal_over_base (A := A) (S := S) : Ideal S) =
      Submodule.torsion A S := by
  -- Proof comment: the ideal was defined with precisely the torsion carrier.
  ext x
  rfl

/-- Helper for Lemma 15.25.6: each homogeneous projection of an `A`-torsion element is again
`A`-torsion. -/
private theorem graded_component_mem_torsion_of_mem_torsion
    {P : Type*} [AddCommMonoid P] [Module A P]
    (gradingP : ℕ → Submodule A P) [DirectSum.Decomposition gradingP]
    {x : P} (hx : x ∈ Submodule.torsion A P) (n : ℕ) :
    (((DirectSum.component A ℕ (fun i ↦ gradingP i) n)
        ((DirectSum.decomposeLinearEquiv gradingP) x) : gradingP n) : P) ∈
      Submodule.torsion A P := by
  let p : P →ₗ[A] gradingP n :=
    (DirectSum.component A ℕ (fun i ↦ gradingP i) n).comp
      (DirectSum.decomposeLinearEquiv gradingP).toLinearMap
  rcases (mem_torsion_iff_exists_ne_zero_smul_eq_zero (R := A) (M := P) x).1 hx with
    ⟨a, ha0, hax⟩
  refine (mem_torsion_iff_exists_ne_zero_smul_eq_zero (R := A) (M := P) (((p x : gradingP n) : P))).2 ?_
  refine ⟨a, ha0, ?_⟩
  have hp : a • p x = 0 := by
    have hp' : p (a • x) = 0 := by
      -- Proof comment: apply the homogeneous projection to the original torsion relation.
      simpa [p, hax]
    simpa [p] using hp'
  -- Proof comment: forget the subtype membership after proving the projected component vanishes.
  simpa [p] using congrArg Subtype.val hp

/-- Helper for Lemma 15.25.6: the promoted base-torsion ideal is homogeneous for every grading on
`S`, because each homogeneous component of a torsion element is killed by the same nonzero base
scalar. -/
private theorem torsion_ideal_over_base_isHomogeneous
    {S : Type*} [CommRing S] [Algebra A S]
    (grading : ℕ → Submodule A S) [GradedAlgebra grading] :
    Ideal.IsHomogeneous grading (torsion_ideal_over_base (A := A) (S := S)) := by
  -- Proof comment: after rewriting the owner-level homogeneous predicate, apply the componentwise
  -- torsion lemma to each graded projection.
  rw [Ideal.IsHomogeneous]
  intro n x hx
  simpa [torsion_ideal_over_base] using
    graded_component_mem_torsion_of_mem_torsion (A := A) grading hx n

/-- Helper for Lemma 15.25.6: the algebra quotient by base torsion is the same `A`-module quotient
as the canonical quotient by `Submodule.torsion A S`. -/
private noncomputable abbrev torsion_ideal_over_base_quotient_equiv
    {S : Type*} [CommRing S] [Algebra A S] :
    ((S ⧸ torsion_ideal_over_base (A := A) (S := S)) : Type _) ≃ₗ[A]
      (S ⧸ Submodule.torsion A S) :=
  (Submodule.Quotient.restrictScalarsEquiv A
      (torsion_ideal_over_base (A := A) (S := S) : Ideal S)).symm.trans
    (Submodule.quotEquivOfEq
      (Submodule.restrictScalars A
        (torsion_ideal_over_base (A := A) (S := S) : Submodule S S))
      (Submodule.torsion A S)
      (torsion_ideal_over_base_restrictScalars (A := A) (S := S)))

/-- Helper for Lemma 15.25.6: quotienting a graded ring model by its base torsion produces an
`A`-torsion-free algebra, exactly as required by the source proof before invoking Lemma 15.25.4. -/
private theorem torsion_ideal_over_base_quotient_isTorsionFree
    {S : Type*} [CommRing S] [Algebra A S] :
    IsTorsionFree A (S ⧸ torsion_ideal_over_base (A := A) (S := S)) := by
  let e :
      ((S ⧸ torsion_ideal_over_base (A := A) (S := S)) : Type _) ≃ₗ[A]
        (S ⧸ Submodule.torsion A S) :=
    torsion_ideal_over_base_quotient_equiv (A := A) (S := S)
  let _ : IsTorsionFree A (S ⧸ Submodule.torsion A S) := inferInstance
  -- Proof comment: the source quotient is torsion free because it is canonically the usual
  -- quotient by `Submodule.torsion A S`.
  rw [isTorsionFree_iff_forall_mem_torsion_eq_zero]
  intro x hx
  have hx' : e x ∈ Submodule.torsion A (S ⧸ Submodule.torsion A S) := by
    rcases (mem_torsion_iff_exists_ne_zero_smul_eq_zero (R := A)
        (M := S ⧸ torsion_ideal_over_base (A := A) (S := S)) x).1 hx with
      ⟨a, ha0, hax⟩
    exact (mem_torsion_iff_exists_ne_zero_smul_eq_zero (R := A)
        (M := S ⧸ Submodule.torsion A S) (e x)).2
      ⟨a, ha0, by simpa using congrArg e hax⟩
  have hzero : e x = 0 :=
    (isTorsionFree_iff_forall_mem_torsion_eq_zero.mp inferInstance) (e x) hx'
  exact e.injective (by simpa using hzero)

/-- Helper for Lemma 15.25.6: the `A`-torsion in an `S`-module is stable under the `S`-action, so
the source proof can quotient the graded module model by base torsion inside the category of
`S`-modules. -/
private def torsion_submodule_over_base
    {S : Type*} [CommRing S] [Algebra A S]
    {P : Type*} [AddCommGroup P] [Module S P] [Module A P] [IsScalarTower A S P] :
    Submodule S P where
  carrier := Submodule.torsion A P
  zero_mem' := (Submodule.torsion A P).zero_mem
  add_mem' := by
    intro x y hx hy
    exact (Submodule.torsion A P).add_mem hx hy
  smul_mem' := by
    intro s x hx
    rcases (mem_torsion_iff_exists_ne_zero_smul_eq_zero (R := A) (M := P) x).1 hx with
      ⟨a, ha0, hax⟩
    refine (mem_torsion_iff_exists_ne_zero_smul_eq_zero (R := A) (M := P) (s • x)).2 ?_
    refine ⟨a, ha0, ?_⟩
    have hsax : s • (a • x) = 0 := by
      -- Proof comment: applying `s` to a torsion relation keeps the annihilator over the base.
      simpa using congrArg (fun y ↦ s • y) hax
    calc
      a • (s • x) = s • (a • x) := by
        simpa [smul_assoc] using (smul_comm s a x).symm
      _ = 0 := hsax

/-- Helper for Lemma 15.25.6: after restricting scalars from `S` to `A`, the promoted torsion
submodule is exactly the canonical `A`-torsion submodule. -/
private theorem torsion_submodule_over_base_restrictScalars
    {S : Type*} [CommRing S] [Algebra A S]
    {P : Type*} [AddCommGroup P] [Module S P] [Module A P] [IsScalarTower A S P] :
    Submodule.restrictScalars A
        (torsion_submodule_over_base (A := A) (S := S) (P := P)) =
      Submodule.torsion A P := by
  -- Proof comment: both submodules were defined using the same torsion carrier.
  ext x
  rfl

/-- Helper for Lemma 15.25.6: the promoted base-torsion submodule is homogeneous for every direct
sum decomposition on `P`, because the same nonzero base scalar annihilates each homogeneous
component. -/
private theorem torsion_submodule_over_base_isHomogeneous
    {S : Type*} [CommRing S] [Algebra A S]
    {P : Type*} [AddCommGroup P] [Module S P] [Module A P] [IsScalarTower A S P]
    (gradingP : ℕ → Submodule A P) [DirectSum.Decomposition gradingP] :
    (torsion_submodule_over_base (A := A) (S := S) (P := P)).IsHomogeneous gradingP := by
  -- Proof comment: the promoted torsion submodule is homogeneous because each graded component of
  -- an `A`-torsion element remains killed by the same nonzero base scalar.
  rw [Submodule.IsHomogeneous]
  intro n x hx
  simpa [torsion_submodule_over_base] using
    graded_component_mem_torsion_of_mem_torsion (A := A) gradingP hx n

/-- Helper for Lemma 15.25.6: the quotient by the promoted base-torsion `S`-submodule is the same
`A`-module quotient as the canonical quotient by `Submodule.torsion A P`. -/
private noncomputable abbrev torsion_submodule_over_base_quotient_equiv
    {S : Type*} [CommRing S] [Algebra A S]
    {P : Type*} [AddCommGroup P] [Module S P] [Module A P] [IsScalarTower A S P] :
    ((P ⧸ torsion_submodule_over_base (A := A) (S := S) (P := P)) : Type _) ≃ₗ[A]
      (P ⧸ Submodule.torsion A P) :=
  (Submodule.Quotient.restrictScalarsEquiv A
      (torsion_submodule_over_base (A := A) (S := S) (P := P))).symm.trans
    (Submodule.quotEquivOfEq
      (Submodule.restrictScalars A
        (torsion_submodule_over_base (A := A) (S := S) (P := P)))
      (Submodule.torsion A P)
      (torsion_submodule_over_base_restrictScalars (A := A) (S := S) (P := P)))

/-- Helper for Lemma 15.25.6: quotienting a graded module model by its base torsion produces an
`A`-torsion-free module, matching the source proof before the weighted-polynomial endgame. -/
private theorem torsion_submodule_over_base_quotient_isTorsionFree
    {S : Type*} [CommRing S] [Algebra A S]
    {P : Type*} [AddCommGroup P] [Module S P] [Module A P] [IsScalarTower A S P] :
    IsTorsionFree A (P ⧸ torsion_submodule_over_base (A := A) (S := S) (P := P)) := by
  let e :
      ((P ⧸ torsion_submodule_over_base (A := A) (S := S) (P := P)) : Type _) ≃ₗ[A]
        (P ⧸ Submodule.torsion A P) :=
    torsion_submodule_over_base_quotient_equiv (A := A) (S := S) (P := P)
  let _ : IsTorsionFree A (P ⧸ Submodule.torsion A P) := inferInstance
  -- Proof comment: the promoted quotient is torsion free because it agrees with the canonical
  -- torsion quotient after restricting scalars to the base.
  rw [isTorsionFree_iff_forall_mem_torsion_eq_zero]
  intro x hx
  have hx' : e x ∈ Submodule.torsion A (P ⧸ Submodule.torsion A P) := by
    rcases (mem_torsion_iff_exists_ne_zero_smul_eq_zero (R := A)
        (M := P ⧸ torsion_submodule_over_base (A := A) (S := S) (P := P)) x).1 hx with
      ⟨a, ha0, hax⟩
    exact (mem_torsion_iff_exists_ne_zero_smul_eq_zero (R := A)
        (M := P ⧸ Submodule.torsion A P) (e x)).2
      ⟨a, ha0, by simpa using congrArg e hax⟩
  have hzero : e x = 0 :=
    (isTorsionFree_iff_forall_mem_torsion_eq_zero.mp inferInstance) (e x) hx'
  exact e.injective (by simpa using hzero)

/-- Helper for Lemma 15.25.6: the image of a homogeneous component in the quotient by the
promoted base-torsion ideal is the induced graded piece on the quotient ring. -/
private def torsion_quotient_ring_grading_over_base
    {S : Type*} [CommRing S] [Algebra A S]
    (grading : ℕ → Submodule A S) [GradedAlgebra grading] :
    ℕ → Submodule A (S ⧸ torsion_ideal_over_base (A := A) (S := S))
  | n => (grading n).map
      ((Ideal.Quotient.mkₐ A (torsion_ideal_over_base (A := A) (S := S))).toLinearMap)

/-- Helper for Lemma 15.25.6: every homogeneous element maps into the corresponding quotient
graded piece. -/
private theorem torsion_quotient_ring_grading_over_base_mk_mem
    {S : Type*} [CommRing S] [Algebra A S]
    (grading : ℕ → Submodule A S) [GradedAlgebra grading]
    {n : ℕ} {x : S} (hx : x ∈ grading n) :
    Ideal.Quotient.mk (torsion_ideal_over_base (A := A) (S := S)) x ∈
      torsion_quotient_ring_grading_over_base (A := A) grading n := by
  -- Proof comment: the induced quotient piece is defined as the submodule image of `grading n`.
  exact ⟨x, hx, rfl⟩

/-- Helper for Lemma 15.25.6: the chosen degree-one generator `f` descends to the degree-one
piece of the quotient graded ring. -/
private def torsion_quotient_degree_one_over_base
    {S : Type*} [CommRing S] [Algebra A S]
    (grading : ℕ → Submodule A S) [GradedAlgebra grading]
    (f : grading 1) :
    torsion_quotient_ring_grading_over_base (A := A) grading 1 :=
  ⟨Ideal.Quotient.mk (torsion_ideal_over_base (A := A) (S := S)) (f : S),
    torsion_quotient_ring_grading_over_base_mk_mem (A := A) grading f.2⟩

/-- Helper for Lemma 15.25.6: the quotient degree-one element is represented by the ordinary
quotient class of the original homogeneous generator. -/
private theorem torsion_quotient_degree_one_over_base_val
    {S : Type*} [CommRing S] [Algebra A S]
    (grading : ℕ → Submodule A S) [GradedAlgebra grading]
    (f : grading 1) :
    ((torsion_quotient_degree_one_over_base (A := A) grading f :
        torsion_quotient_ring_grading_over_base (A := A) grading 1) :
      S ⧸ torsion_ideal_over_base (A := A) (S := S)) =
      Ideal.Quotient.mk (torsion_ideal_over_base (A := A) (S := S)) (f : S) :=
  rfl

/-- Helper for Lemma 15.25.6: the image of a homogeneous component in the quotient by the
promoted base-torsion submodule is the induced graded piece on the quotient module. -/
private def torsion_quotient_module_grading_over_base
    {S : Type*} [CommRing S] [Algebra A S]
    {P : Type*} [AddCommGroup P] [Module S P] [Module A P] [IsScalarTower A S P]
    (gradingP : ℕ → Submodule A P) [DirectSum.Decomposition gradingP] :
    ℕ → Submodule A (P ⧸ torsion_submodule_over_base (A := A) (S := S) (P := P))
  | n => (gradingP n).map
      ((Submodule.mkQ (torsion_submodule_over_base (A := A) (S := S) (P := P))).restrictScalars A)

/-- Helper for Lemma 15.25.6: every homogeneous module element maps into the corresponding
quotient graded piece. -/
private theorem torsion_quotient_module_grading_over_base_mkQ_mem
    {S : Type*} [CommRing S] [Algebra A S]
    {P : Type*} [AddCommGroup P] [Module S P] [Module A P] [IsScalarTower A S P]
    (gradingP : ℕ → Submodule A P) [DirectSum.Decomposition gradingP]
    {n : ℕ} {x : P} (hx : x ∈ gradingP n) :
    Submodule.mkQ (torsion_submodule_over_base (A := A) (S := S) (P := P)) x ∈
      torsion_quotient_module_grading_over_base (A := A) (S := S) (P := P) gradingP n := by
  -- Proof comment: the quotient graded piece is the image of `gradingP n` under the quotient map.
  exact ⟨x, hx, rfl⟩

/-- Helper for Lemma 15.25.6: localizing an `A`-torsion numerator keeps the resulting away class
`A`-torsion. -/
private theorem localized_mk'_mem_torsion_of_mem_torsion
    {S : Type*} [CommRing S] [Algebra A S]
    {P : Type*} [AddCommGroup P] [Module S P] [Module A P] [IsScalarTower A S P]
    (f : S) {m : P} (hm : m ∈ Submodule.torsion A P) (s : Submonoid.powers f) :
    IsLocalizedModule.mk' (LocalizedModule.mkLinearMap (Submonoid.powers f) P) m s ∈
      Submodule.torsion A (LocalizedModule.Away f P) := by
  rcases (mem_torsion_iff_exists_ne_zero_smul_eq_zero (R := A) (M := P) m).1 hm with
    ⟨a, ha0, ham⟩
  refine (mem_torsion_iff_exists_ne_zero_smul_eq_zero (R := A)
      (M := LocalizedModule.Away f P)
      (IsLocalizedModule.mk' (LocalizedModule.mkLinearMap (Submonoid.powers f) P) m s)).2 ?_
  refine ⟨a, ha0, ?_⟩
  -- Proof comment: the same base annihilator still kills the localized class after pushing the
  -- scalar through `IsLocalizedModule.mk'`.
  have hamS : (algebraMap A S a) • m = 0 := by
    simpa using ham
  have hloc :
      a • IsLocalizedModule.mk' (LocalizedModule.mkLinearMap (Submonoid.powers f) P) m s = 0 := by
    change (algebraMap A (Localization.Away f) a) •
        IsLocalizedModule.mk' (LocalizedModule.mkLinearMap (Submonoid.powers f) P) m s = 0
    rw [IsScalarTower.algebraMap_eq A S (Localization.Away f)]
    rw [← IsLocalizedModule.mk'_smul, hamS, IsLocalizedModule.mk'_zero]
  simpa using hloc

/-- Helper for Lemma 15.25.6: if the away-localized `S`-module is torsion free over `A`, then the
localized promoted base-torsion submodule vanishes. -/
private theorem localized_torsion_submodule_over_base_eq_bot_of_away_isTorsionFree
    {S : Type*} [CommRing S] [Algebra A S]
    {P : Type*} [AddCommGroup P] [Module S P] [Module A P] [IsScalarTower A S P]
    (f : S) (hTF : IsTorsionFree A (LocalizedModule.Away f P)) :
    Submodule.localized (p := Submonoid.powers f)
        (torsion_submodule_over_base (A := A) (S := S) (P := P)) =
      ⊥ := by
  -- Route correction: first show each localized numerator from the promoted torsion submodule is
  -- still `A`-torsion, and only then apply torsion-freeness of the away localization.
  rw [Submodule.eq_bot_iff]
  intro x hx
  rw [Submodule.mem_localized'] at hx
  rcases hx with ⟨m, hm, s, rfl⟩
  change m ∈ Submodule.torsion A P at hm
  have hx' :
      IsLocalizedModule.mk' (LocalizedModule.mkLinearMap (Submonoid.powers f) P) m s ∈
        Submodule.torsion A (LocalizedModule.Away f P) :=
    localized_mk'_mem_torsion_of_mem_torsion (A := A) (S := S) (P := P) f hm s
  exact (isTorsionFree_iff_forall_mem_torsion_eq_zero.mp hTF) _ hx'

/-- Helper for Lemma 15.25.6: for the regular `S`-module, the promoted base-torsion submodule is
exactly the promoted base-torsion ideal. -/
private theorem torsion_submodule_over_base_eq_torsion_ideal_over_base
    {S : Type*} [CommRing S] [Algebra A S] :
    torsion_submodule_over_base (A := A) (S := S) (P := S) =
      (torsion_ideal_over_base (A := A) (S := S) : Submodule S S) := by
  -- Proof comment: both promoted torsion objects were defined with the same carrier subset.
  ext x
  rfl

/-- Helper for Lemma 15.25.6: if the ordinary away-localization of `S` is torsion free over `A`,
then the localized promoted base-torsion ideal vanishes. -/
private theorem localized_torsion_ideal_over_base_eq_bot_of_away_isTorsionFree
    {S : Type*} [CommRing S] [Algebra A S]
    (f : S) (hTF : IsTorsionFree A (Localization.Away f)) :
    Ideal.map (algebraMap S (Localization.Away f))
        (torsion_ideal_over_base (A := A) (S := S)) =
      ⊥ := by
  have hTF' : IsTorsionFree A (LocalizedModule.Away f S) := by
    simpa using hTF
  have hloc :
      Submodule.localized (p := Submonoid.powers f)
          (torsion_ideal_over_base (A := A) (S := S) : Ideal S) =
        ⊥ := by
    simpa [torsion_submodule_over_base_eq_torsion_ideal_over_base]
      using
        (localized_torsion_submodule_over_base_eq_bot_of_away_isTorsionFree
          (A := A) (S := S) (P := S) f hTF')
  -- Proof comment: for the regular module, `Submodule.localized` is exactly the localized ideal,
  -- which `Ideal.localized'_eq_map` rewrites as the mapped ideal in the away ring.
  simpa [Submodule.localized, Ideal.localized'_eq_map] using hloc

/-- Helper for Lemma 15.25.6: once the away-localized module is torsion free over `A`, quotienting
the model module by base torsion does not change the ordinary away-localization. -/
private noncomputable def away_localized_torsion_quotient_linearEquiv_over_base
    {S : Type*} [CommRing S] [Algebra A S]
    {P : Type*} [AddCommGroup P] [Module S P] [Module A P] [IsScalarTower A S P]
    (f : S) (hTF : IsTorsionFree A (LocalizedModule.Away f P)) :
    LocalizedModule.Away f
        (P ⧸ torsion_submodule_over_base (A := A) (S := S) (P := P)) ≃ₗ[
          Localization.Away f] LocalizedModule.Away f P :=
  let T : Submodule S P := torsion_submodule_over_base (A := A) (S := S) (P := P)
  -- Proof comment: localize the quotient and then identify the localized torsion submodule with
  -- `⊥`, exactly as in the source torsion-quotient replacement step.
  (localizedQuotientEquiv (Submonoid.powers f) T).symm ≪≫ₗ
    (Submodule.localized (p := Submonoid.powers f) T).quotEquivOfEqBot
      (localized_torsion_submodule_over_base_eq_bot_of_away_isTorsionFree
        (A := A) (S := S) (P := P) f hTF)

/-- Helper for Lemma 15.25.6: the quotient map to the base-torsion quotient ring preserves the
grading when the quotient pieces are defined as images of the original homogeneous pieces. -/
private def torsion_quotient_ring_gradedRingHom_over_base
    {S : Type*} [CommRing S] [Algebra A S]
    (grading : ℕ → Submodule A S) [GradedAlgebra grading] :
    grading →+*ᵍ torsion_quotient_ring_grading_over_base (A := A) grading where
  __ := Ideal.Quotient.mkₐ A (torsion_ideal_over_base (A := A) (S := S))
  map_mem := by
    intro i x hx
    exact ⟨x, hx, rfl⟩

/-- Helper for Lemma 15.25.6: the quotient grading on the base-torsion quotient ring carries the
canonical graded-algebra structure descended from the original grading. -/
private noncomputable def torsion_quotient_ring_gradedAlgebra_over_base
    {S : Type*} [CommRing S] [Algebra A S]
    (grading : ℕ → Submodule A S) [GradedAlgebra grading]
    (hT_hom : Ideal.IsHomogeneous grading (torsion_ideal_over_base (A := A) (S := S))) :
    -- TODO: build the quotient direct-sum decomposition from `hT_hom`, then obtain the
    -- descended `GradedAlgebra` owner from that decomposition instead of asking typeclass search
    -- to synthesize it blindly.
    GradedAlgebra (torsion_quotient_ring_grading_over_base (A := A) grading) := sorry

/-- Helper for Lemma 15.25.6: quotienting the graded model ring by base torsion does not change
the ordinary away-localization at the chosen degree-one generator. -/
private noncomputable def torsion_quotient_away_algEquiv_over_base
    {S : Type*} [CommRing S] [Algebra A S]
    (grading : ℕ → Submodule A S) [GradedAlgebra grading]
    (f : grading 1) :
    -- TODO: first show the localized torsion ideal vanishes in `S[(f)⁻¹]`, then identify the
    -- quotient of the ordinary away-localization with the away-localization of `S / S_tors`.
    Localization.Away (f : S) ≃+*
      Localization.Away
        (Ideal.Quotient.mk (torsion_ideal_over_base (A := A) (S := S)) (f : S)) := sorry

/-- Helper for Lemma 15.25.6: the graded model ring is finite type over the valuation-ring base,
because its degree-zero piece is identified with `A` and the model is finite type over that
degree-zero piece. -/
private theorem model_ring_finiteType_over_base
    {S : Type*} [CommRing S] [Algebra A S]
    (grading : ℕ → Submodule A S) [GradedAlgebra grading]
    {N : Type*} [AddCommGroup N] [Module S N]
    (zeroIso : A ≃ₐ[A] grading 0)
    (hmodel : IsDegreeOneGeneratedFiniteTypeModel (R := A) grading N) :
    Algebra.FiniteType A S := by
  rw [← RingHom.finiteType_algebraMap]
  have h0S : (algebraMap (grading 0) S).FiniteType := by
    rw [RingHom.finiteType_algebraMap]
    exact hmodel.finiteType
  have hA0 : (algebraMap A (grading 0)).FiniteType := by
    convert RingHom.FiniteType.of_surjective zeroIso.toAlgHom.toRingHom zeroIso.surjective using 1
    ext a
    simpa using (congrArg (fun x : grading 0 ↦ (x : S)) (zeroIso.commutes a)).symm
  -- Proof comment: compose the finite-type map `A → grading 0` with the model finite-type map
  -- `grading 0 → S`.
  exact RingHom.FiniteType.comp h0S hA0

/-- Helper for Lemma 15.25.6: quotienting the graded model ring by promoted base torsion preserves
finite type over the valuation-ring base, since the quotient map is surjective. -/
private theorem torsion_quotient_ring_finiteType_over_base
    {S : Type*} [CommRing S] [Algebra A S]
    (grading : ℕ → Submodule A S) [GradedAlgebra grading]
    {N : Type*} [AddCommGroup N] [Module S N]
    (zeroIso : A ≃ₐ[A] grading 0)
    (hmodel : IsDegreeOneGeneratedFiniteTypeModel (R := A) grading N) :
    Algebra.FiniteType A (S ⧸ torsion_ideal_over_base (A := A) (S := S)) := by
  let _ : Algebra.FiniteType A S :=
    model_ring_finiteType_over_base (A := A) grading zeroIso hmodel
  -- Proof comment: finite type descends across the surjective quotient map to the torsion
  -- quotient ring.
  exact Algebra.FiniteType.of_surjective
    (Ideal.Quotient.mkₐ A (torsion_ideal_over_base (A := A) (S := S)))
    Ideal.Quotient.mk_surjective

/-- Helper for Lemma 15.25.6: the degree-zero quotient piece is finite over `A`, because it is the
image of the finite `A`-module `grading 0`. -/
private theorem torsion_quotient_degree_zero_finite_over_base
    {S : Type*} [CommRing S] [Algebra A S]
    (grading : ℕ → Submodule A S) [GradedAlgebra grading]
    (zeroIso : A ≃ₐ[A] grading 0) :
    Module.Finite A (torsion_quotient_ring_grading_over_base (A := A) grading 0) := by
  let q0 : grading 0 →ₗ[A] torsion_quotient_ring_grading_over_base (A := A) grading 0 :=
    { toFun := fun x ↦
        ⟨Ideal.Quotient.mk (torsion_ideal_over_base (A := A) (S := S)) (x : S),
          torsion_quotient_ring_grading_over_base_mk_mem (A := A) grading x.2⟩
      map_add' := by
        intro x y
        ext
        rfl
      map_smul' := by
        intro a x
        ext
        rfl }
  have hq0 : Function.Surjective q0 := by
    intro y
    rcases y.2 with ⟨x, hx, hxy⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    ext
    simpa using hxy
  let _ : Module.Finite A (grading 0) := Module.Finite.equiv zeroIso.toLinearEquiv
  -- Proof comment: the degree-zero quotient piece is the image of the finite module `grading 0`
  -- under the quotient map.
  exact Module.Finite.of_surjective q0 hq0

/-- Helper for Lemma 15.25.6: quotienting by base torsion makes the graded model ring flat over
the valuation-ring base, since the quotient is torsion free. -/
private theorem torsion_quotient_ring_flat_over_base
    {S : Type*} [CommRing S] [Algebra A S] :
    Module.Flat A (S ⧸ torsion_ideal_over_base (A := A) (S := S)) := by
  let _ : IsTorsionFree A (S ⧸ torsion_ideal_over_base (A := A) (S := S)) :=
    torsion_ideal_over_base_quotient_isTorsionFree (A := A) (S := S)
  -- Proof comment: over a valuation ring, torsion-free is equivalent to flat.
  exact (flat_iff_isTorsionFree_of_valuationRing
    (A := A) (M := S ⧸ torsion_ideal_over_base (A := A) (S := S))).mpr inferInstance

/-- Helper for Lemma 15.25.6: quotienting the graded model module by promoted base torsion makes
it flat over the valuation-ring base, again because the quotient is torsion free. -/
private theorem torsion_quotient_module_flat_over_base
    {S : Type*} [CommRing S] [Algebra A S]
    {P : Type*} [AddCommGroup P] [Module S P] [Module A P] [IsScalarTower A S P] :
    Module.Flat A (P ⧸ torsion_submodule_over_base (A := A) (S := S) (P := P)) := by
  let _ : IsTorsionFree A (P ⧸ torsion_submodule_over_base (A := A) (S := S) (P := P)) :=
    torsion_submodule_over_base_quotient_isTorsionFree (A := A) (S := S) (P := P)
  -- Proof comment: the valuation-ring flatness criterion applies verbatim to the quotient module.
  exact (flat_iff_isTorsionFree_of_valuationRing
    (A := A) (M := P ⧸ torsion_submodule_over_base (A := A) (S := S) (P := P))).mpr
    inferInstance

/-- Helper for Lemma 15.25.6: once the degree-zero homogeneous chart is finitely presented, the
model algebra isomorphism transports finite presentation back to the original algebra. -/
lemma algebra_finitePresentation_of_chart
    {S : Type*} [CommRing S] [Algebra A S]
    (grading : ℕ → Submodule A S) [GradedAlgebra grading]
    {f_degree : ℕ} (f : grading f_degree)
    (ringIso : B ≃ₐ[A] Away grading (f : S))
    [Algebra.FinitePresentation A (Away grading (f : S))] :
    Algebra.FinitePresentation A B := by
  -- Transfer the chart finite presentation back across the model algebra equivalence.
  exact Algebra.FinitePresentation.equiv ringIso.symm

/-- Helper for Lemma 15.25.6: flatness of the target algebra makes the homogeneous chart
torsion free over the valuation-ring base. -/
lemma away_chart_isTorsionFree_of_flat
    {S : Type*} [CommRing S] [Algebra A S]
    (grading : ℕ → Submodule A S) [GradedAlgebra grading]
    {f_degree : ℕ} (f : grading f_degree)
    (ringIso : B ≃ₐ[A] Away grading (f : S))
    [Flat A B] :
    IsTorsionFree A (Away grading (f : S)) := by
  have hB : IsTorsionFree A B :=
    (flat_iff_isTorsionFree_of_valuationRing (A := A) (M := B)).mp inferInstance
  -- Transport torsion-freeness across the algebra-linear chart isomorphism.
  let _ : IsTorsionFree A B := hB
  exact Function.Injective.moduleIsTorsionFree
    (f := ringIso.symm.toLinearEquiv)
    ringIso.symm.toLinearEquiv.injective
    (fun a x ↦ ringIso.symm.toLinearEquiv.map_smul a x)

/-- Helper for Lemma 15.25.6: the source-faithful graded-model argument should show that a flat
degree-zero chart of a degree-one generated finite-type model is finitely presented. -/
lemma degree_one_chart_algebra_finitePresentation_of_flat_model
    {S : Type*} [CommRing S] [Algebra A S]
    (grading : ℕ → Submodule A S) [GradedAlgebra grading]
    {N : Type*} [AddCommGroup N] [Module S N]
    (f : grading 1)
    (zeroIso : A ≃ₐ[A] grading 0)
    (ringIso : B ≃ₐ[A] Away grading (f : S))
    (hmodel : IsDegreeOneGeneratedFiniteTypeModel (R := A) grading N)
    [Flat A B] :
    Algebra.FinitePresentation A (Away grading (f : S)) := by
  -- TODO: finish the source-faithful torsion-quotient reduction:
  -- 1. build the quotient graded-ring owners on `Sbar`;
  -- 2. compare the homogeneous chart with its torsion-quotient chart;
  -- 3. apply Lemma `15.25.4` to the torsion-free quotient model and transport back.
  sorry

-- Proof sketch: represent the finite type `A`-algebra `B` as the degree-zero localization of a
-- finite graded algebra over `A` via
-- `exists_graded_localization_model_of_finite_module`, replace the graded algebra by its
-- torsion-free quotient using `flat_iff_isTorsionFree_of_valuationRing`, apply
-- `graded_algebra_finitePresentation_of_flat` together with
-- `primeLocalizationsDetectEquality_of_isDomain`, and then localize the resulting finite
-- presentation.
/-- Lemma 15.25.6 (1): if `A` is a valuation ring, `A → B` is a finite type ring map, and `B` is
flat over `A`, then `B` is a finitely presented `A`-algebra. -/
@[stacks 053E]
theorem algebra_finitePresentation_of_finiteType_flat_over_valuationRing [Flat A B] :
    Algebra.FinitePresentation A B := by
  -- TODO: combine the graded localization model, the torsion-quotient chart comparison, and
  -- Lemma `15.25.4` to transport finite presentation from the model chart back to `B`.
  sorry

variable {M : Type w} [AddCommMonoid M] [Module B M] [Module.Finite B M]
variable [Module A M] [IsScalarTower A B M]

/-- Helper for Lemma 15.25.6: finite presentation transports from the homogeneous chart back to
the original module along the graded-localization semilinear equivalence. -/
lemma module_finitePresentation_of_chart_equiv
    [AddCommGroup M]
    {C : Type*} [CommRing C] [Algebra A C]
    {N : Type*} [AddCommGroup N] [Module C N]
    (ringIso : B ≃ₐ[A] C)
    (moduleIso : M ≃ₛₗ[(ringIso.toRingEquiv : B →+* C)] N)
    [Module.FinitePresentation C N] :
    Module.FinitePresentation B M := by
  -- TODO: endow `C` with the transported `B`-algebra structure from `ringIso`, restrict scalars
  -- along the resulting finite-type map `B → C`, and transport finite presentation back through
  -- the semilinear equivalence `moduleIso`.
  sorry

/-- Helper for Lemma 15.25.6: restricting scalars along `A → S_(f)` makes the ordinary
localized module an `A`-module. -/
private noncomputable instance away_localized_module_over_base
    {S : Type*} [CommRing S] [Algebra A S]
    {N : Type*} [AddCommGroup N] [Module S N] [Module A N] [IsScalarTower A S N]
    (grading : ℕ → Submodule A S) [GradedAlgebra grading]
    (f : grading 1) :
    Module A (LocalizedModule.Away (f : S) N) :=
  Module.compHom (LocalizedModule.Away (f : S) N) (algebraMap A (Away grading (f : S)))

/-- Helper for Lemma 15.25.6: restricting scalars along `A → S_(f)` makes the degree-zero chart
an `A`-module. -/
private noncomputable instance away_degree_zero_part_module_over_base
    {S : Type*} [CommRing S] [Algebra A S]
    {N : Type*} [AddCommGroup N] [Module S N] [Module A N] [IsScalarTower A S N]
    (grading : ℕ → Submodule A S) [GradedAlgebra grading]
    (gradingN : ℕ → Submodule A N) [DirectSum.Decomposition gradingN]
    [SetLike.GradedSMul grading gradingN]
    (f : grading 1) :
    Module A (awayDegreeZeroPart grading gradingN f) :=
  Module.compHom (awayDegreeZeroPart grading gradingN f) (algebraMap A (Away grading (f : S)))

/-- Helper for Lemma 15.25.6: flatness of the original finite module makes the localized
degree-zero chart torsion free over the valuation-ring base. -/
lemma awayDegreeZeroPart_isTorsionFree_of_flat
    [AddCommGroup M]
    {S : Type*} [CommRing S] [Algebra A S]
    (grading : ℕ → Submodule A S) [GradedAlgebra grading]
    {N : Type*} [AddCommGroup N] [Module S N] [Module A N] [IsScalarTower A S N]
    (gradingN : ℕ → Submodule A N) [DirectSum.Decomposition gradingN]
    [SetLike.GradedSMul grading gradingN]
    (f : grading 1)
    (ringIso : B ≃ₐ[A] Away grading (f : S))
    (moduleIso :
      M ≃ₛₗ[(ringIso.toRingEquiv : B →+* Away grading (f : S))]
        awayDegreeZeroPart grading gradingN f)
    [Flat A M] :
    IsTorsionFree A (awayDegreeZeroPart grading gradingN f) := by
  -- TODO: obtain `A`-torsion-freeness of `M` from flatness, then transport it across the
  -- semilinear chart by rewriting the scalar action through `ringIso`.
  sorry

/-- Helper for Lemma 15.25.6: the source-faithful graded-module argument should show that the
degree-zero homogeneous chart of a flat finite module model is finitely presented. -/
lemma degree_zero_chart_module_finitePresentation_of_flat_model
    [AddCommGroup M]
    {S : Type*} [CommRing S] [Algebra A S]
    (grading : ℕ → Submodule A S) [GradedAlgebra grading]
    {N : Type*} [AddCommGroup N] [Module S N] [Module A N] [IsScalarTower A S N]
    (gradingN : ℕ → Submodule A N) [DirectSum.Decomposition gradingN]
    [SetLike.GradedSMul grading gradingN]
    (f : grading 1)
    (zeroIso : A ≃ₐ[A] grading 0)
    (ringIso : B ≃ₐ[A] Away grading (f : S))
    (moduleIso :
      M ≃ₛₗ[(ringIso.toRingEquiv : B →+* Away grading (f : S))]
        awayDegreeZeroPart grading gradingN f)
    (hmodel : IsDegreeOneGeneratedFiniteTypeModel (R := A) grading N)
    [Flat A M] :
    Module.FinitePresentation (Away grading (f : S)) (awayDegreeZeroPart grading gradingN f) := by
  have hchart_torsion_free : IsTorsionFree A (awayDegreeZeroPart grading gradingN f) :=
    awayDegreeZeroPart_isTorsionFree_of_flat
      (A := A) (B := B) (M := M) grading gradingN f ringIso moduleIso
  let T : Submodule S N := torsion_submodule_over_base (A := A) (S := S) (P := N)
  let Nbar := N ⧸ T
  let _ : Module A Nbar := inferInstance
  let _ : IsTorsionFree A Nbar :=
    torsion_submodule_over_base_quotient_isTorsionFree (A := A) (S := S) (P := N)
  let _ : Module.Flat A Nbar :=
    torsion_quotient_module_flat_over_base (A := A) (S := S) (P := N)
  -- Route correction: the module endgame should now pivot through the weighted-polynomial local
  -- criterion from the source proof, but only after the `A`-torsion quotient is shown not to alter
  -- the localized degree-zero chart. The promoted torsion `S`-submodule, torsion-free quotient,
  -- its homogeneity, and the ambient away-localization comparison are now available; what remains
  -- is to restrict that comparison to the homogeneous degree-zero chart after constructing the
  -- quotient grading data.
  have hT_hom : T.IsHomogeneous gradingN :=
    torsion_submodule_over_base_isHomogeneous (A := A) (S := S) (P := N) gradingN
  -- TODO: after constructing `[DirectSum.Decomposition gradingNbar]` and the quotient graded
  -- scalar action from `hT_hom`, restrict `away_localized_torsion_quotient_linearEquiv_over_base`
  -- to a linear equivalence of degree-zero charts using `mem_awayDegreeZeroPart_iff`. That chart
  -- restriction is the only missing bridge before `graded_module_finitePresentation_of_flat`
  -- applies to the torsion-free quotient model.
  sorry

-- Proof sketch: choose a graded presentation `M ≅ N_(f)` over a graded finite type algebra `S`
-- using `exists_graded_localization_model_of_finite_module`, replace `N` by its torsion-free
-- quotient using the quotient owner from Lemma `15.22.2` and
-- `flat_iff_isTorsionFree_of_valuationRing`, apply
-- `graded_module_finitePresentation_of_flat` over the graded model using
-- `primeLocalizationsDetectEquality_of_isDomain`, and then localize the resulting finite
-- presentation to `B`.
/-- Lemma 15.25.6 (2): if `A` is a valuation ring, `A → B` is a finite type ring map, `M` is a
finite `B`-module, and `M` is flat as an `A`-module, then `M` is finitely presented as a
`B`-module. -/
@[stacks 053E]
theorem module_finitePresentation_of_finite_flat_over_valuationRing [Flat A M] :
    Module.FinitePresentation B M := by
  -- TODO: repeat the torsion-quotient replacement on the graded module model, prove finite
  -- presentation on the degree-zero chart, and transport it back across the semilinear chart.
  sorry

end
