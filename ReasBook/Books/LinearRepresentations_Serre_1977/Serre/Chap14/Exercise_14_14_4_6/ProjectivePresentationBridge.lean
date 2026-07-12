import LinearRepresentations_Serre_1977.Chap14.Exercise_14_14_4_6.ProjectorRangeBridge

open scoped BigOperators MonoidAlgebra Representation TensorProduct
open CategoryTheory
open Representation
open FiniteProjectiveGroupAlgebraModule

universe u v

noncomputable section

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {G : Type v} [Group G]

local notation "kA" => IsLocalRing.ResidueField A

namespace FiniteProjectiveGroupAlgebraModule

section Henselian

variable [HenselianLocalRing A]

/-- Helper for Exercise 14-14.4-6: a split retract identifies the range of its associated
projector with the retracted module. -/
theorem range_retract_projector_linearEquiv
    {R : Type*} [Semiring R]
    {M : Type*} [AddCommMonoid M] [Module R M]
    {N : Type*} [AddCommMonoid N] [Module R N]
    (i : M →ₗ[R] N) (s : N →ₗ[R] M)
    (hs : s.comp i = LinearMap.id) :
    Nonempty (LinearMap.range (i.comp s) ≃ₗ[R] M) := by
  let toFun : LinearMap.range (i.comp s) →ₗ[R] M :=
    { toFun := fun y ↦ s y
      map_add' := by
        intro x y
        simp
      map_smul' := by
        intro a x
        simp }
  let invFun : M →ₗ[R] LinearMap.range (i.comp s) :=
    { toFun := fun x ↦
        ⟨i x, ⟨i x, by
          change i (s (i x)) = i x
          simpa [LinearMap.comp_apply] using congrArg (fun f : M →ₗ[R] M => i (f x)) hs⟩⟩
      map_add' := by
        intro x y
        ext
        simp
      map_smul' := by
        intro a x
        ext
        simp }
  refine ⟨
    { toFun := toFun
      invFun := invFun
      left_inv := ?_
      right_inv := ?_
      map_add' := toFun.map_add
      map_smul' := toFun.map_smul }⟩
  · intro y
    rcases y with ⟨y, ⟨x, rfl⟩⟩
    apply Subtype.ext
    have hs_eval : s (i (s x)) = s x := by
      simpa [LinearMap.comp_apply] using congrArg (fun f : M →ₗ[R] M => f (s x)) hs
    simpa [LinearMap.comp_apply] using congrArg i hs_eval
  · intro x
    change s (i x) = x
    simpa using congrArg (fun f : M →ₗ[R] M => f x) hs

/-- Helper for Exercise 14-14.4-6: a finite projective `kA[G]`-module is the range of an
idempotent on a finite free `kA[G]`-module. -/
theorem projective_retract_idempotent_on_free_module
    [Finite G]
    (F : FiniteProjectiveGroupAlgebraModule kA G) :
    ∃ n : Nat,
      ∃ s : (Fin n → kA[G]) →ₗ[kA[G]] F.V,
        ∃ i : F.V →ₗ[kA[G]] (Fin n → kA[G]),
          s.comp i = LinearMap.id ∧
            IsIdempotentElem (i.comp s) ∧
            Nonempty (LinearMap.range (i.comp s) ≃ₗ[kA[G]] F.V) := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin' (kA[G]) F.V
  letI : Module.Free kA[G] (Fin n → kA[G]) :=
    Module.Free.of_basis (Pi.basisFun (kA[G]) (Fin n))
  obtain ⟨i, hi⟩ := (Module.Projective.iff_split_of_projective s hs).1
    (inferInstance : Module.Projective kA[G] F.V)
  refine ⟨n, s, i, hi, ?_, ?_⟩
  · change (i.comp s).comp (i.comp s) = i.comp s
    refine LinearMap.ext ?_
    intro x
    have hs_eval : s (i (s x)) = s x := by
      simpa [LinearMap.comp_apply] using congrArg (fun f : F.V →ₗ[kA[G]] F.V => f (s x)) hi
    simpa [LinearMap.comp_apply] using congrArg i hs_eval
  · exact range_retract_projector_linearEquiv i s hi

/-- Helper for Exercise 14-14.4-6: a single idempotent gives the standard two-term complete
orthogonal idempotent family. -/
theorem completeOrthogonalIdempotents_pair_of_isIdempotentElem
    {R : Type*} [Ring R] {e : R} (he : IsIdempotentElem e) :
    CompleteOrthogonalIdempotents (![e, 1 - e] : Fin 2 → R) := by
  simpa using CompleteOrthogonalIdempotents.of_isIdempotentElem he

/-- Helper for Exercise 14-14.4-6: an idempotent endomorphism splits its ambient module as the
product of its image and the image of its complementary projector. -/
theorem idempotent_range_prod_linearEquiv
    {R : Type*} [Ring R]
    {M : Type*} [AddCommGroup M] [Module R M]
    (e : Module.End R M) (he : IsIdempotentElem e) :
    Nonempty (M ≃ₗ[R] LinearMap.range e × LinearMap.range (1 - e)) := by
  have hcompl : IsCompl (LinearMap.range e) (LinearMap.range (1 - e)) := by
    simpa [LinearMap.IsIdempotentElem.ker_eq_range_one_sub (p := e) he] using
      (LinearMap.IsIdempotentElem.isCompl he :
        IsCompl (LinearMap.range e) (LinearMap.ker e))
  exact ⟨((LinearMap.range e).prodEquivOfIsCompl (LinearMap.range (1 - e)) hcompl).symm⟩

/-- Helper for Exercise 14-14.4-6: the range of an idempotent endomorphism of a finite free
ambient module is projective over the group algebra. -/
theorem projective_range_of_idempotent_endomorphism
    [Finite G] {n : Nat}
    (e : Module.End A[G] (Fin n → A[G])) (he : IsIdempotentElem e) :
    Module.Projective A[G] (LinearMap.range e) := by
  exact
    LinearMap.IsResidueFieldReduction.projective_range_of_idempotent_endomorphism_general e he

/-- Helper for Exercise 14-14.4-6: the range of an idempotent on a finite free ambient module
defines a finite projective owner object. -/
noncomputable def finiteProjectiveGroupAlgebraModule_of_idempotent_range
    [Finite G] {n : Nat}
    (e : Module.End A[G] (Fin n → A[G])) (he : IsIdempotentElem e) :
    FiniteProjectiveGroupAlgebraModule A G := by
  let W0 : ModuleCat A[G] := ModuleCat.of A[G] (LinearMap.range e)
  have hfinite : Module.Finite A[G] W0 := by
    change Module.Finite A[G] (LinearMap.range e)
    infer_instance
  let Wfg : FGModuleCat A[G] := ⟨W0, hfinite⟩
  have hproj : Module.Projective A[G] Wfg := by
    change Module.Projective A[G] (LinearMap.range e)
    exact projective_range_of_idempotent_endomorphism (A := A) (G := G) e he
  exact ⟨Wfg, hproj⟩

/-- Helper for Exercise 14-14.4-6: every finite projective `kA[G]`-module is the underlying
module of the range of an idempotent on a finite free module. -/
theorem exists_free_projector_presentation_iso
    [Finite G]
    (F : FiniteProjectiveGroupAlgebraModule kA G) :
    ∃ n : Nat,
      ∃ eBar : Module.End kA[G] (Fin n → kA[G]),
        ∃ heBar : IsIdempotentElem eBar,
          Nonempty
            (LinearMap.range eBar ≃ₗ[kA[G]] F.V) := by
  obtain ⟨n, s, i, hi, heBar, hRangeEquiv⟩ :=
    projective_retract_idempotent_on_free_module (A := A) (G := G) F
  exact ⟨n, i.comp s, heBar, hRangeEquiv⟩

end Henselian

end FiniteProjectiveGroupAlgebraModule

end
