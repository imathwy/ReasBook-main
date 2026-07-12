import Mathlib.CategoryTheory.Preadditive.Biproducts
import StacksProject_2024.Chap22.Definition_22_26_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open CategoryTheory
open CategoryTheory.Limits

variable {R : Type u} [CommRing R]
variable {A : Type v} [D : DifferentialGradedCategory R A]

namespace DifferentialGradedCategory

open scoped DifferentialGradedCategory

/- Source/core/bridge triage for Definition 22.26.4:
- source-facing: the four structure morphisms of a direct sum in a differential graded category,
  now expressed as closed degree-`0` morphisms via the Chapter 22 owner `CompHom`;
- core/canonical: the binary bicone and bilimit structure of the corresponding split direct sum in
  `Comp(𝒜)`;
- bridge/view: closedness is already built into `CompHom`, so the source-facing owner keeps the
  split direct-sum identities and exposes the induced binary-biproduct API on `Comp(𝒜)`. -/

/-- Definition 22.26.4: for a direct sum `(x, y, z, i, j, p, q)` in a differential graded
category over `R`, the direct sum is differential graded when the structure maps are homogeneous of
degree `0` and closed. In the current owner, those closed degree-`0` structure maps are the
Chapter 22 morphisms `CompHom`, so the remaining data are exactly the split direct-sum identities
in `Comp(𝒜)`. -/
@[stacks 09P4]
class IsDifferentialGradedDirectSum
    {x y : Comp R A}
    {z : outParam (Comp R A)}
    (i : outParam (x ⟶ z))
    (j : outParam (y ⟶ z))
    (p : outParam (z ⟶ x))
    (q : outParam (z ⟶ y)) : Prop where
  i_comp_p : i ≫ p = 𝟙 x
  i_comp_q : i ≫ q = 0
  j_comp_p : j ≫ p = 0
  j_comp_q : j ≫ q = 𝟙 y
  total : p ≫ i + q ≫ j = 𝟙 z

namespace IsDifferentialGradedDirectSum

variable {x y z : Comp R A} {i : x ⟶ z} {j : y ⟶ z} {p : z ⟶ x} {q : z ⟶ y}

/-- The binary bicone underlying a differential graded direct sum in `Comp(𝒜)`. -/
def bicone (hds : IsDifferentialGradedDirectSum i j p q) :
    BinaryBicone x y where
  pt := z
  fst := p
  snd := q
  inl := i
  inr := j
  inl_fst := hds.i_comp_p
  inl_snd := hds.i_comp_q
  inr_fst := hds.j_comp_p
  inr_snd := hds.j_comp_q

@[simp] theorem bicone_fst
    (hds : IsDifferentialGradedDirectSum i j p q) :
    (bicone hds).fst = p :=
  rfl

@[simp] theorem bicone_snd
    (hds : IsDifferentialGradedDirectSum i j p q) :
    (bicone hds).snd = q :=
  rfl

@[simp] theorem bicone_inl
    (hds : IsDifferentialGradedDirectSum i j p q) :
    (bicone hds).inl = i :=
  rfl

@[simp] theorem bicone_inr
    (hds : IsDifferentialGradedDirectSum i j p q) :
    (bicone hds).inr = j :=
  rfl

/-- The underlying bicone of a differential graded direct sum is a binary bilimit in `Comp(𝒜)`. -/
def isBilimit (hds : IsDifferentialGradedDirectSum i j p q) :
    (bicone hds).IsBilimit :=
  isBinaryBilimitOfTotal (bicone hds) (by simpa using hds.total)

/-- A differential graded direct sum supplies the product-side universal property of its
underlying binary bicone in `Comp(𝒜)`. -/
instance instIsLimitBicone
    [hds : IsDifferentialGradedDirectSum i j p q] :
    IsLimit (bicone hds).toCone :=
  (isBilimit hds).isLimit

/-- A differential graded direct sum supplies the coproduct-side universal property of its
underlying binary bicone in `Comp(𝒜)`. -/
instance instIsColimitBicone
    [hds : IsDifferentialGradedDirectSum i j p q] :
    IsColimit (bicone hds).toCocone :=
  (isBilimit hds).isColimit

/-- A differential graded direct sum canonically equips its two summands with a binary biproduct
in `Comp(𝒜)`. -/
instance instHasBinaryBiproduct
    [hds : IsDifferentialGradedDirectSum i j p q] :
    HasBinaryBiproduct x y :=
  HasBinaryBiproduct.mk
    { bicone := bicone hds
      isBilimit := isBilimit hds }

end IsDifferentialGradedDirectSum

end DifferentialGradedCategory

end
