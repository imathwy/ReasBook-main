import Mathlib
import StacksProject_2024.Chap10.Lemma_10_105_9
import StacksProject_2024.Chap28.Definition_28_8_1
import StacksProject_2024.Chap28.Lemma_28_8_3
import StacksProject_2024.Chap29.Lemma_29_17_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Semantic recall / local analogue check:
- `lean_leansearch` confirmed the canonical scheme owners `LocallyOfFiniteType`,
  `IsLocallyNoetherian`, and `Spec`;
- local Chapter 29 owns scheme universal catenarity as `UniversallyCatenary`;
- local Chapter 28 keeps the Cohen-Macaulay scheme condition as the affine-local specialization
  `S.HasRingPropertyLocally (fun A ↦ CohenMacaulayRing A)`, while Chapter 10 supplies the ring-level
  bridge from Cohen-Macaulay rings to `UniversallyCatenaryRing`.
-/

section

variable (S : Scheme.{u})

/-- A Cohen-Macaulay scheme is universally catenary. -/
instance instUniversallyCatenaryOfHasRingPropertyLocallyCohenMacaulayRing
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ CohenMacaulayRing A)] :
    UniversallyCatenary S := by
  rw [universallyCatenary_iff_forall_affineOpen_sectionsRing_universallyCatenaryRing]
  intro U
  have hU : CohenMacaulayRing (Γ(S, (U : S.Opens))) :=
    (Scheme.cohenMacaulay_iff_forall_affineOpen_sectionsRing_cohenMacaulayRing S).1 inferInstance U
  exact universallyCatenaryRing_of_cohenMacaulayRing hU

/-- A Cohen-Macaulay scheme is universally catenary. -/
theorem universallyCatenary_of_cohenMacaulay
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ CohenMacaulayRing A)] :
    UniversallyCatenary S :=
  inferInstance

end

/-- Lemma 29.17.5 (1): any scheme locally of finite type over a field is universally catenary. -/
@[stacks 02JB]
theorem universallyCatenary_of_locallyOfFiniteType_over_field
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] :
    UniversallyCatenary X := sorry

/-- Lemma 29.17.5 (2): any scheme locally of finite type over a Cohen-Macaulay scheme is
universally catenary. -/
@[stacks 02JB]
theorem universallyCatenary_of_locallyOfFiniteType_over_cohenMacaulay
    {S X : Scheme.{u}}
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ CohenMacaulayRing A)]
    (f : X ⟶ S) [LocallyOfFiniteType f] :
    UniversallyCatenary X := by
  let _ : UniversallyCatenary S := universallyCatenary_of_cohenMacaulay S
  exact universallyCatenary_of_locallyOfFiniteType f

/-- Lemma 29.17.5 (3): any scheme locally of finite type over `Spec(ℤ)` is universally
catenary. -/
@[stacks 02JB]
theorem universallyCatenary_of_locallyOfFiniteType_over_specInt
    {X : Scheme} (f : X ⟶ Spec (CommRingCat.of ℤ)) [LocallyOfFiniteType f] :
    UniversallyCatenary X := sorry

/-- Lemma 29.17.5 (4): any scheme locally of finite type over the spectrum of a
1-dimensional Noetherian domain is universally catenary. -/
@[stacks 02JB]
theorem universallyCatenary_of_locallyOfFiniteType_over_spec_of_ringKrullDim_eq_one
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (hdim : ringKrullDim R = 1)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] :
    UniversallyCatenary X := sorry

end AlgebraicGeometry
