import Mathlib.CategoryTheory.Shift.Basic
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import StacksProject_2024.Chap22.Lemma_22_26_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open DifferentialGradedCategory

universe u v w

section

variable {R : Type u} [CommRing R]
variable {A : Type v} [D : DifferentialGradedCategory.{u, v, w} R A]

-- Semantic recall hits: `ShortComplex` and `ShortComplex.Splitting` are the canonical owners for
-- split short sequences, while `CochainComplex.homOfDegreewiseSplit` supplies the corresponding
-- boundary morphism. This file therefore exposes the source-facing cone data by bridging directly
-- to the short-complex owner rather than packaging a second split-sequence structure.

section

variable [HasShift (Comp R A) ℤ]

/-- A choice of the connecting morphism produced by Lemma `22.27.1` for split short exact
complexes in `Comp(𝒜)`. -/
class CompBoundaryMap
    (R : Type u) [CommRing R]
    (A : Type v) [DifferentialGradedCategory.{u, v, w} R A]
    [HasShift (Comp R A) ℤ] : Type (max u v w + 1) where
  /-- The connecting morphism `z ⟶ x[1]` attached to the split short exact sequence
  `x ⟶ y ⟶ z`. -/
  boundary {S : ShortComplex (Comp R A)} (σ : S.Splitting) :
    S.X₃ ⟶ S.X₁⟦(1 : ℤ)⟧

namespace CompBoundaryMap

/-- The connecting morphism attached to an explicitly displayed split short exact sequence in
`Comp(𝒜)`. -/
abbrev boundaryMk
    [CompBoundaryMap R A]
    {x y z : Comp R A}
    {f : x ⟶ y}
    {g : y ⟶ z}
    (w : f ≫ g = 0)
    (σ : (ShortComplex.mk f g w).Splitting) :
    z ⟶ x⟦(1 : ℤ)⟧ :=
  CompBoundaryMap.boundary σ

end CompBoundaryMap

/-- The explicit cone data for a closed degree-`0` morphism in `Comp(𝒜)`. -/
structure AdmissibleCone
    {x y : Comp R A}
    [B : CompBoundaryMap R A]
    (f : x ⟶ y) where
  /-- The cone object `c(f)`. -/
  obj : Comp R A
  /-- The map `y ⟶ c(f)`. -/
  toCone : y ⟶ obj
  /-- The map `c(f) ⟶ x[1]`. -/
  toShift : obj ⟶ x⟦(1 : ℤ)⟧
  /-- The two displayed maps form a short complex. -/
  toCone_toShift :
    toCone ≫ toShift = 0
  /-- The split short complex `y ⟶ c(f) ⟶ x[1]`. -/
  splitting :
    (ShortComplex.mk toCone toShift toCone_toShift).Splitting
  /-- The connecting morphism of Lemma `22.27.1` for `y ⟶ c(f) ⟶ x[1]` is `f[1]`. -/
  boundary_eq :
    B.boundary splitting =
      f⟦(1 : ℤ)⟧'

namespace AdmissibleCone

/-- The canonical short complex underlying an admissible cone. -/
abbrev shortComplex
    {x y : Comp R A}
    [CompBoundaryMap R A]
    {f : x ⟶ y}
    (C : AdmissibleCone f) :
    ShortComplex (Comp R A) :=
  ShortComplex.mk C.toCone C.toShift C.toCone_toShift

@[simp] theorem shortComplex_f
    {x y : Comp R A}
    [CompBoundaryMap R A]
    {f : x ⟶ y}
    (C : AdmissibleCone f) :
    C.shortComplex.f = C.toCone :=
  rfl

@[simp] theorem shortComplex_g
    {x y : Comp R A}
    [CompBoundaryMap R A]
    {f : x ⟶ y}
    (C : AdmissibleCone f) :
    C.shortComplex.g = C.toShift :=
  rfl

end AdmissibleCone

end

/-- Situation 22.27.2: assuming the shift functor on `Comp(𝒜)` and the boundary-map assignment of
Lemma `22.27.1`, every closed degree-`0` morphism `f : x ⟶ y` in `Comp(𝒜)` admits a cone object
`c(f)` fitting into an admissible short exact sequence `y ⟶ c(f) ⟶ x[1]` whose connecting
morphism is `f[1]`. -/
@[stacks 09QJ]
class HasAdmissibleCones
    (R : Type u) [CommRing R]
    (A : Type v) [DifferentialGradedCategory.{u, v, w} R A]
    : Type (max u v w + 1) extends HasShift (Comp R A) ℤ, CompBoundaryMap R A where
  /-- The chosen cone short exact sequence with boundary `f[1]` attached to a closed degree-`0`
  morphism. -/
  admissibleCone {x y : Comp R A} (f : x ⟶ y) :
    AdmissibleCone f

namespace HasAdmissibleCones

/-- The short complex underlying the cone chosen by Situation `22.27.2`. -/
abbrev shortComplex
    [HasAdmissibleCones R A]
    {x y : Comp R A}
    (f : x ⟶ y) :
    ShortComplex (Comp R A) :=
  (admissibleCone f).shortComplex

/-- The split short complex underlying the cone chosen by Situation `22.27.2`. -/
abbrev splitting
    [HasAdmissibleCones R A]
    {x y : Comp R A}
    (f : x ⟶ y) :
    (shortComplex f).Splitting :=
  (admissibleCone f).splitting

/-- The connecting morphism of the short complex chosen by Situation `22.27.2` is `f[1]`. -/
@[simp] theorem boundary_eq
    [HasAdmissibleCones R A]
    {x y : Comp R A}
    (f : x ⟶ y) :
    CompBoundaryMap.boundary (splitting f) = f⟦(1 : ℤ)⟧' :=
  (admissibleCone f).boundary_eq

@[simp] theorem shortComplex_f
    [HasAdmissibleCones R A]
    {x y : Comp R A}
    (f : x ⟶ y) :
    (shortComplex f).f = (admissibleCone f).toCone :=
  rfl

@[simp] theorem shortComplex_g
    [HasAdmissibleCones R A]
    {x y : Comp R A}
    (f : x ⟶ y) :
    (shortComplex f).g = (admissibleCone f).toShift :=
  rfl

end HasAdmissibleCones

end
