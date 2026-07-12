import StacksProject_2024.Chap10.Definition_10_160_1
import StacksProject_2024.Chap10.Definition_10_162_1
import StacksProject_2024.Chap15.Proposition_15_48_7
import StacksProject_2024.Chap29.Lemma_29_19_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall / local analogue check:
-- `LocallyOfFiniteType` is the canonical morphism owner, `IsJ2Ring` is the ring-side owner from
-- Chapter 15, and Lemma 29.19.2 supplies the scheme-side permanence theorem. This file keeps the
-- source-facing scheme statements as bridges from affine-base `IsJ2Ring` hypotheses.

section

variable (R : Type u) [CommRing R]

/-- The affine scheme `Spec R` is `J-2` whenever the base ring `R` is `J-2`. -/
instance isJ2_spec [IsJ2Ring.{u, u} R] : IsJ2 (Spec (CommRingCat.of R)) where
  toIsLocallyNoetherian := inferInstance
  regularLocus_isOpen_of_locallyOfFiniteType := by
    intro Y f
    sorry

/-- A scheme locally of finite type over `Spec R` is `J-2` whenever the base ring `R` is `J-2`.
This is the affine-base bridge from the ring owner `IsJ2Ring R` to the scheme owner `IsJ2`. -/
theorem isJ2_of_locallyOfFiniteType_over_spec [IsJ2Ring.{u, u} R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] :
    IsJ2 X :=
  isJ2_of_locallyOfFiniteType f

end

section

variable {k : Type u} [Field k]

/-- Lemma 29.19.3 (1): any scheme locally of finite type over a field is `J-2`. -/
@[stacks 07R5]
theorem isJ2_of_locallyOfFiniteType_over_field
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] :
    IsJ2 X :=
  isJ2_of_locallyOfFiniteType_over_spec k f

end

/-- Lemma 29.19.3 (2): any scheme locally of finite type over a Noetherian complete local ring is
`J-2`. -/
@[stacks 07R5]
theorem isJ2_of_locallyOfFiniteType_over_noetherian_completeLocalRing
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsCompleteLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] :
    IsJ2 X :=
  isJ2_of_locallyOfFiniteType_over_spec R f

section

/-- Lemma 29.19.3 (3): any scheme locally of finite type over `Spec ℤ` is `J-2`. -/
@[stacks 07R5]
theorem isJ2_of_locallyOfFiniteType_over_integers
    {X : Scheme} (f : X ⟶ Spec (CommRingCat.of ℤ)) [LocallyOfFiniteType f] :
    IsJ2 X :=
  isJ2_of_locallyOfFiniteType_over_spec ℤ f

end

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- Lemma 29.19.3 (4): any scheme locally of finite type over a Noetherian local ring of Krull
dimension `1` is `J-2`. -/
@[stacks 07R5]
theorem isJ2_of_locallyOfFiniteType_over_noetherian_local_ring_dimension_one
    (hdim : ringKrullDim R = 1)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] :
    IsJ2 X := by
  letI : IsJ2Ring R := isJ2Ring_of_noetherian_local_ring_dimension_one R hdim
  exact isJ2_of_locallyOfFiniteType_over_spec R f

end

section

variable {R : Type u} [CommRing R] [NagataRing R]

/-- Lemma 29.19.3 (5): any scheme locally of finite type over a Nagata ring of Krull dimension
`1` is `J-2`. -/
@[stacks 07R5]
theorem isJ2_of_locallyOfFiniteType_over_nagataRing_dimension_one
    (hdim : ringKrullDim R = 1)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] :
    IsJ2 X := by
  letI : IsJ2Ring R := isJ2Ring_of_nagataRing_dimension_one R hdim
  exact isJ2_of_locallyOfFiniteType_over_spec R f

end

/-- Lemma 29.19.3 (6): any scheme locally of finite type over a Dedekind ring of characteristic
zero is `J-2`. -/
@[stacks 07R5]
theorem isJ2_of_locallyOfFiniteType_over_dedekindDomain_charZero
    {R : Type u} [CommRing R] [IsDedekindDomain R] [CharZero (FractionRing R)]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] :
    IsJ2 X :=
  isJ2_of_locallyOfFiniteType_over_spec R f

end AlgebraicGeometry.Scheme
