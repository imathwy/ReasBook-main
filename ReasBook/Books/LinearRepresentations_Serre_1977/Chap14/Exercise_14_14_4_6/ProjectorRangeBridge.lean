import Serre.Chap14.Exercise_14_14_4_6.RestrictedEndomorphismBaseChange

open scoped BigOperators MonoidAlgebra Representation TensorProduct
open CategoryTheory
open Representation
open FiniteProjectiveGroupAlgebraModule

universe u w x

noncomputable section

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {G : Type u} [Group G]
variable {P : Type w} [AddCommGroup P] [Module A P] [Module A[G] P] [IsScalarTower A A[G] P]
variable [Module.Projective A[G] P] [Module.Finite A P]
variable {Pbar : Type x} [AddCommGroup Pbar] [Module (IsLocalRing.ResidueField A) Pbar]
variable [Module A Pbar] [IsScalarTower A (IsLocalRing.ResidueField A) Pbar]
variable [Module (IsLocalRing.ResidueField A)[G] Pbar]
variable [IsScalarTower (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A)[G] Pbar]

local notation "kA" => IsLocalRing.ResidueField A

namespace LinearMap.IsResidueFieldReduction

/-- Helper for Exercise 14-14.4-6: an idempotent projector fixes each point of its range. -/
theorem range_element_fixed_of_isIdempotentElem
    {R : Type*} [Ring R]
    {M : Type*} [AddCommGroup M] [Module R M]
    (e : Module.End R M) (he : IsIdempotentElem e)
    (x : LinearMap.range e) :
    e.rangeRestrict x = x := by
  apply Subtype.ext
  rcases x with ⟨x, ⟨y, rfl⟩⟩
  change e (e y) = e y
  simpa [Module.End.mul_eq_comp, LinearMap.comp_apply] using
    congrArg (fun f : Module.End R M => f y) he.eq

/-- Helper for Exercise 14-14.4-6: the range of an idempotent endomorphism of a projective module
is again projective. -/
theorem projective_range_of_idempotent_endomorphism_general
    {R : Type*} [Ring R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Projective R M]
    (e : Module.End R M) (he : IsIdempotentElem e) :
    Module.Projective R (LinearMap.range e) := by
  let i : LinearMap.range e →ₗ[R] M := (LinearMap.range e).subtype
  let s : M →ₗ[R] LinearMap.range e := e.rangeRestrict
  have hs : s.comp i = LinearMap.id := by
    ext x
    exact congrArg Subtype.val (range_element_fixed_of_isIdempotentElem e he x)
  exact Module.Projective.of_split i s hs

/-- Helper for Exercise 14-14.4-6: if an ambient endomorphism `e` reduces to `eBar`, then
reducing a point in `range e` lands in `range eBar`. -/
theorem mem_range_lifted_projector_of_reduction
    {f : P →ₗ[A] Pbar}
    (hf : f.IsResidueFieldReduction G)
    {e : Module.End A[G] P}
    {eBar : Module.End kA[G] Pbar}
    (heRed : endHom_restrict_groupAlgebraLinearMap (A := A) (G := G) hf e = eBar)
    (x : LinearMap.range e) :
    f x.1 ∈ LinearMap.range eBar := by
  rcases x with ⟨x, ⟨y, rfl⟩⟩
  refine ⟨f y, ?_⟩
  simpa [heRed] using
    (endHom_restrict_groupAlgebraLinearMap_comp_apply (A := A) (G := G) hf e y)

/-- Helper for Exercise 14-14.4-6: a lifted projector induces a canonical map from the lifted
range to the reduced range. -/
noncomputable def range_lifted_projector_map
    {f : P →ₗ[A] Pbar}
    (hf : f.IsResidueFieldReduction G)
    {e : Module.End A[G] P}
    {eBar : Module.End kA[G] Pbar}
    (heRed : endHom_restrict_groupAlgebraLinearMap (A := A) (G := G) hf e = eBar) :
    LinearMap.range e → LinearMap.range eBar :=
  fun x ↦ ⟨f x.1, mem_range_lifted_projector_of_reduction (A := A) (G := G) hf heRed x⟩

/-- Helper for Exercise 14-14.4-6: the induced map on projector ranges is surjective. -/
theorem range_lifted_projector_map_surjective
    {f : P →ₗ[A] Pbar}
    (hf : f.IsResidueFieldReduction G)
    {e : Module.End A[G] P}
    {eBar : Module.End kA[G] Pbar}
    (heRed : endHom_restrict_groupAlgebraLinearMap (A := A) (G := G) hf e = eBar) :
    Function.Surjective (range_lifted_projector_map (A := A) (G := G) hf heRed) := by
  intro y
  rcases y with ⟨y, ⟨x, rfl⟩⟩
  obtain ⟨x, rfl⟩ := hf.surjective x
  refine ⟨⟨e x, ⟨x, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  simpa [range_lifted_projector_map, heRed] using
    (endHom_restrict_groupAlgebraLinearMap_comp_apply (A := A) (G := G) hf e x).symm

end LinearMap.IsResidueFieldReduction

end
