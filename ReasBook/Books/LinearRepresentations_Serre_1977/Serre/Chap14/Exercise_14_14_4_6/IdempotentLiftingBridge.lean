import Mathlib
import Mathlib.RepresentationTheory.Intertwining
import LinearRepresentations_Serre_1977.Serre.Chap14.Corollary_14_14_4_3

open scoped BigOperators MonoidAlgebra Representation TensorProduct
open CategoryTheory
open Representation
open FiniteProjectiveGroupAlgebraModule

universe u w₁ x

noncomputable section

variable {A : Type u} [CommRing A] [IsLocalRing A]

variable {B : Type w₁} [Ring B] [Algebra A B] [Module.Free A B] [Module.Finite A B]
variable {Bbar : Type x} [Ring Bbar] [Algebra A Bbar] [Algebra (IsLocalRing.ResidueField A) Bbar]
variable [IsScalarTower A (IsLocalRing.ResidueField A) Bbar]

/-- Helper for Exercise 14-14.4-6: if a ring homomorphism has nilpotent kernel, then every
idempotent in its range lifts. -/
theorem exists_idempotent_lift_of_ker_isNilpotent
    (red : B →+* Bbar)
    (hker : ∀ x ∈ RingHom.ker red, IsNilpotent x)
    (uBar : Bbar) (huBar : uBar ∈ Set.range red)
    (huBarIdem : IsIdempotentElem uBar) :
    ∃ u : B, IsIdempotentElem u ∧ red u = uBar := by
  simpa [Set.mem_range] using
    (exists_isIdempotentElem_eq_of_ker_isNilpotent
      (f := red) hker uBar huBar huBarIdem)

/-- Helper for Exercise 14-14.4-6: if a ring homomorphism has nilpotent kernel, then any complete
orthogonal idempotent family in its range lifts. -/
theorem exists_completeOrthogonalIdempotents_lift_of_ker_isNilpotent
    {ι : Type*} [Fintype ι]
    (red : B →+* Bbar)
    (hker : ∀ x ∈ RingHom.ker red, IsNilpotent x)
    (eBar : ι → Bbar)
    (heBar : CompleteOrthogonalIdempotents eBar)
    (heBar_mem : ∀ i, eBar i ∈ Set.range red) :
    ∃ e : ι → B, CompleteOrthogonalIdempotents e ∧ red ∘ e = eBar := by
  simpa [Function.comp_apply, Set.mem_range] using
    (CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker
      (f := red) hker heBar heBar_mem)

/-- Helper for Exercise 14-14.4-6: an idempotent is a root of `X^2 - X` in any ring. -/
theorem isRoot_X_sq_sub_X_of_isIdempotentElem
    {R : Type*} [Ring R] {e : R} (he : IsIdempotentElem e) :
    (Polynomial.X ^ 2 - Polynomial.X : Polynomial R).IsRoot e := by
  simp [Polynomial.IsRoot, pow_two, he.eq]

/-- Helper for Exercise 14-14.4-6: in a commutative ring, an idempotent is a simple root of
`X^2 - X`. -/
theorem derivative_eval_X_sq_sub_X_isUnit_of_isIdempotentElem
    {R : Type*} [CommRing R] {e : R} (he : IsIdempotentElem e) :
    IsUnit (((Polynomial.X ^ 2 - Polynomial.X : Polynomial R).derivative).eval e) := by
  let u := (((Polynomial.X ^ 2 - Polynomial.X : Polynomial R).derivative).eval e)
  have hsquare : u * u = 1 := by
    calc
      u * u = (((1 + 1) * e - 1) * (((1 + 1) * e - 1))) := by
        simp [u]
      _ = 4 * (e * e) - 4 * e + 1 := by ring
      _ = 4 * e - 4 * e + 1 := by simp [he.eq]
      _ = 1 := by ring
  exact IsUnit.of_mul_eq_one u hsquare

/-- Helper for Exercise 14-14.4-6: if `u : B` lifts `uBar`, then reduction identifies the
singleton-generated `A`-subalgebra upstairs with the singleton-generated `A`-subalgebra
downstairs. -/
theorem adjoin_singleton_map_eq_of_lift
    (red : B →ₐ[A] Bbar) {u : B} {uBar : Bbar} (hu : red u = uBar) :
    (Algebra.adjoin A ({u} : Set B)).map red = Algebra.adjoin A ({uBar} : Set Bbar) := by
  simpa [hu] using Algebra.map_adjoin_singleton (R := A) red u

/-- Helper for Exercise 14-14.4-6: every element of the singleton-generated subalgebra downstairs
has a lift in the corresponding singleton-generated subalgebra upstairs. -/
theorem exists_preimage_mem_adjoin_singleton_of_lift
    (red : B →ₐ[A] Bbar) {u : B} {uBar : Bbar} (hu : red u = uBar)
    {x : Bbar} (hx : x ∈ Algebra.adjoin A ({uBar} : Set Bbar)) :
    ∃ y : B, y ∈ Algebra.adjoin A ({u} : Set B) ∧ red y = x := by
  have hx' : x ∈ (Algebra.adjoin A ({u} : Set B)).map red := by
    simpa [adjoin_singleton_map_eq_of_lift (A := A) (B := B) (Bbar := Bbar) red hu] using hx
  rcases (Subalgebra.mem_map.mp hx') with ⟨y, hy, rfl⟩
  exact ⟨y, hy, rfl⟩

/-- Helper for Exercise 14-14.4-6: after restricting to the singleton-generated commutative
subalgebra of an idempotent, the polynomial `X^2 - X` still has a simple root. -/
theorem adjoin_singleton_root_and_simple_root_of_isIdempotentElem
    {uBar : Bbar} (huBar : IsIdempotentElem uBar) :
    let Sbar := Algebra.adjoin A ({uBar} : Set Bbar)
    let uSbar : Sbar := ⟨uBar, Algebra.self_mem_adjoin_singleton A uBar⟩
    (Polynomial.X ^ 2 - Polynomial.X : Polynomial Sbar).IsRoot uSbar ∧
      IsUnit (((Polynomial.X ^ 2 - Polynomial.X : Polynomial Sbar).derivative).eval uSbar) := by
  dsimp
  have huSbar :
      IsIdempotentElem
        (⟨uBar, Algebra.self_mem_adjoin_singleton A uBar⟩ :
          Algebra.adjoin A ({uBar} : Set Bbar)) := by
    ext
    exact huBar.eq
  exact ⟨isRoot_X_sq_sub_X_of_isIdempotentElem huSbar,
    derivative_eval_X_sq_sub_X_isUnit_of_isIdempotentElem huSbar⟩

/-- Helper for Exercise 14-14.4-6: a chosen lift `u` of `uBar` induces the canonical reduction map
from `A[u]` to `A[uBar]`. -/
noncomputable def adjoin_singleton_codRestrict
    (red : B →ₐ[A] Bbar) {u : B} {uBar : Bbar} (hu : red u = uBar) :
    Algebra.adjoin A ({u} : Set B) →ₐ[A] Algebra.adjoin A ({uBar} : Set Bbar) :=
  ((red.comp (Algebra.adjoin A ({u} : Set B)).val).codRestrict
    (Algebra.adjoin A ({uBar} : Set Bbar))
    (fun x ↦ by
      rcases x with ⟨x, hx⟩
      change red x ∈ Algebra.adjoin A ({uBar} : Set Bbar)
      have hx' : red x ∈ (Algebra.adjoin A ({u} : Set B)).map red := by
        exact Subalgebra.mem_map.2 ⟨x, hx, rfl⟩
      simpa [adjoin_singleton_map_eq_of_lift (A := A) (B := B) (Bbar := Bbar) red hu] using hx'))

/-- Helper for Exercise 14-14.4-6: the restricted singleton-adjoin reduction map evaluates by
applying the ambient reduction map. -/
@[simp] theorem adjoin_singleton_codRestrict_apply
    (red : B →ₐ[A] Bbar) {u : B} {uBar : Bbar} (hu : red u = uBar)
    (x : Algebra.adjoin A ({u} : Set B)) :
    ((adjoin_singleton_codRestrict (A := A) (B := B) (Bbar := Bbar) red hu) x : Bbar) = red x := by
  rfl

/-- Helper for Exercise 14-14.4-6: every element of `A[uBar]` has a preimage in `A[u]` under the
restricted reduction map. -/
theorem adjoin_singleton_codRestrict_surjective
    (red : B →ₐ[A] Bbar) {u : B} {uBar : Bbar} (hu : red u = uBar) :
    Function.Surjective
      (adjoin_singleton_codRestrict (A := A) (B := B) (Bbar := Bbar) red hu) := by
  intro x
  rcases x with ⟨x, hx⟩
  obtain ⟨y, hy, hyx⟩ :=
    exists_preimage_mem_adjoin_singleton_of_lift
      (A := A) (B := B) (Bbar := Bbar) red hu hx
  refine ⟨⟨y, hy⟩, ?_⟩
  apply Subtype.ext
  simpa [adjoin_singleton_codRestrict] using hyx

section Henselian

variable [HenselianLocalRing A]

/-- Helper for Exercise 14-14.4-6: any realization of a residue-field base change is surjective on
the underlying `A`-modules. -/
theorem isBaseChange_surjective
    (red : B →ₐ[A] Bbar)
    (hred : IsBaseChange (IsLocalRing.ResidueField A) red.toLinearMap) :
    Function.Surjective red := by
  intro x
  obtain ⟨t, rfl⟩ := hred.equiv.surjective x
  have hres :
      Function.Surjective (algebraMap A (IsLocalRing.ResidueField A)) := by
    simpa [IsLocalRing.ResidueField.algebraMap_eq] using IsLocalRing.residue_surjective
  obtain ⟨y, hy⟩ := TensorProduct.mk_surjective
    (R := A) (S := IsLocalRing.ResidueField A) (M := B) hres t
  refine ⟨y, ?_⟩
  calc
    red y = (1 : IsLocalRing.ResidueField A) • red y := by simp
    _ = hred.equiv ((TensorProduct.mk A (IsLocalRing.ResidueField A) B 1) y) := by
          symm
          simpa using hred.equiv_tmul (1 : IsLocalRing.ResidueField A) y
    _ = hred.equiv t := by exact congrArg hred.equiv hy

end Henselian

end
