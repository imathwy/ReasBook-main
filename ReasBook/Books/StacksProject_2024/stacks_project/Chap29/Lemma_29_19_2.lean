import Mathlib
import StacksProject_2024.Chap15.Definition_15_47_1
import StacksProject_2024.Chap29.Definition_29_19_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme

-- Semantic recall / local analogue check:
-- `lean_leansearch` surfaced the affine-open-cover scheme API (`Scheme.affineCover`,
-- `Scheme.affineOpenCover`). Local precedent then fixes the relevant owners as
-- `Scheme.IsJ2` for schemes, `IsJ2Ring` for coordinate rings, `X.affineOpens` for affine opens,
-- and `LocallyOfFiniteType` for the final permanence clause.

variable (X : Scheme.{u})

/-- Lemma 29.19.2 (1): for a locally Noetherian scheme `X`, the following are equivalent:
`X` is `J-2`; `X` admits an open covering by `J-2` open subschemes; every affine open of `X`
has `J-2` coordinate ring; and `X` admits an affine open cover whose coordinate rings are `J-2`. -/
@[stacks 07R4]
theorem isJ2_tfae_openCover_affineOpen_sectionsRing [IsLocallyNoetherian X] :
    List.TFAE [
      IsJ2 X,
      ∃ 𝒰 : X.OpenCover, ∀ i : 𝒰.I₀, IsJ2 (𝒰.X i),
      ∀ U : X.affineOpens, IsJ2Ring.{u, u} (Γ(X, (U : X.Opens))),
      ∃ 𝒰 : X.AffineOpenCover, ∀ i : 𝒰.I₀, IsJ2Ring.{u, u} (Γ(X, (𝒰.f i).opensRange))
    ] := sorry

/-- Lemma 29.19.2 (1): a locally Noetherian scheme is `J-2` if and only if it admits an open
covering by `J-2` open subschemes. -/
@[stacks 07R4]
theorem isJ2_iff_exists_openCover
    [IsLocallyNoetherian X] :
    IsJ2 X ↔
      ∃ 𝒰 : X.OpenCover, ∀ i : 𝒰.I₀, IsJ2 (𝒰.X i) := sorry

/-- Lemma 29.19.2 (1): a locally Noetherian scheme is `J-2` if and only if every affine open has
`J-2` coordinate ring. -/
@[stacks 07R4]
theorem isJ2_iff_forall_affineOpen_sectionsRing
    [IsLocallyNoetherian X] :
    IsJ2 X ↔
      ∀ U : X.affineOpens, IsJ2Ring.{u, u} (Γ(X, (U : X.Opens))) := sorry

/-- Lemma 29.19.2 (1): a locally Noetherian scheme is `J-2` if and only if it admits an affine
open cover whose coordinate rings are `J-2`. -/
@[stacks 07R4]
theorem isJ2_iff_exists_affineOpenCover_sectionsRing
    [IsLocallyNoetherian X] :
    IsJ2 X ↔
      ∃ 𝒰 : X.AffineOpenCover, ∀ i : 𝒰.I₀, IsJ2Ring.{u, u} (Γ(X, (𝒰.f i).opensRange)) := sorry

/-- Lemma 29.19.2 (2): if `X` is `J-2`, then every scheme locally of finite type over `X` is
`J-2`. -/
@[stacks 07R4]
theorem isJ2_of_locallyOfFiniteType
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsJ2 X] [LocallyOfFiniteType f] :
    IsJ2 Y := sorry

end AlgebraicGeometry.Scheme
