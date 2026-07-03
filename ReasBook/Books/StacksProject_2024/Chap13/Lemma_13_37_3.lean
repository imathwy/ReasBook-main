import Mathlib
import StacksProject_2024.Chap13.Definition_13_36_3
import StacksProject_2024.Chap13.Definition_13_33_1
import StacksProject_2024.Chap13.Definition_13_37_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open Opposite

noncomputable section

universe w v u

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
  [HasCoproducts.{max u v w} D]
variable {I : Type w} (E : I → D)

/-- The object property of objects that are isomorphic to a coproduct of shifts of the family
`E : I → D`. -/
def IsDirectSumOfShifts : ObjectProperty D := fun A ↦
  ∃ (J : Type (max u v w)) (ι : J → I) (shift : J → ℤ),
    Nonempty ((∐ fun j : J ↦ E (ι j)⟦shift j⟧) ≅ A)

instance isDirectSumOfShifts_isClosedUnderIsomorphisms :
    (IsDirectSumOfShifts E).IsClosedUnderIsomorphisms where
  of_iso e hA := by
    rcases hA with ⟨J, ι, shift, ⟨h⟩⟩
    exact ⟨J, ι, shift, ⟨h.trans e⟩⟩

/-- A recursive generating-family approximation tower by direct sums of shifts of the family `E`.
The natural-number index `0` corresponds to the textbook term `X₁`. -/
def IsGeneratingFamilyApproximation
    (X : ℕ → D) (map : ∀ n : ℕ, X n ⟶ X (n + 1))
    (Y : ℕ → D) (triangleHom : ∀ n : ℕ, Y n ⟶ X n)
    (triangleConnecting : ∀ n : ℕ, X (n + 1) ⟶ (Y n)⟦(1 : ℤ)⟧) : Prop :=
  IsDirectSumOfShifts E (X 0) ∧
    (∀ n : ℕ, IsDirectSumOfShifts E (Y n)) ∧
    (∀ n : ℕ, Triangle.mk (triangleHom n) (map n) (triangleConnecting n) ∈ distTriang D)

namespace IsGeneratingFamilyApproximation

omit [IsTriangulated D] in
theorem initial {X : ℕ → D} {map : ∀ n : ℕ, X n ⟶ X (n + 1)} {Y : ℕ → D}
    {triangleHom : ∀ n : ℕ, Y n ⟶ X n}
    {triangleConnecting : ∀ n : ℕ, X (n + 1) ⟶ (Y n)⟦(1 : ℤ)⟧}
    (h :
      IsGeneratingFamilyApproximation E X map Y triangleHom triangleConnecting) :
    IsDirectSumOfShifts E (X 0) :=
  h.1

omit [IsTriangulated D] in
theorem pieces {X : ℕ → D} {map : ∀ n : ℕ, X n ⟶ X (n + 1)} {Y : ℕ → D}
    {triangleHom : ∀ n : ℕ, Y n ⟶ X n}
    {triangleConnecting : ∀ n : ℕ, X (n + 1) ⟶ (Y n)⟦(1 : ℤ)⟧}
    (h :
      IsGeneratingFamilyApproximation E X map Y triangleHom triangleConnecting) (n : ℕ) :
    IsDirectSumOfShifts E (Y n) :=
  h.2.1 n

omit [IsTriangulated D] in
theorem triangleDistinguished {X : ℕ → D} {map : ∀ n : ℕ, X n ⟶ X (n + 1)} {Y : ℕ → D}
    {triangleHom : ∀ n : ℕ, Y n ⟶ X n}
    {triangleConnecting : ∀ n : ℕ, X (n + 1) ⟶ (Y n)⟦(1 : ℤ)⟧}
    (h :
      IsGeneratingFamilyApproximation E X map Y triangleHom triangleConnecting) (n : ℕ) :
    Triangle.mk (triangleHom n) (map n) (triangleConnecting n) ∈ distTriang D :=
  h.2.2 n

end IsGeneratingFamilyApproximation

-- Proof sketch: choose the canonical approximation tower built from all maps from shifts of the
-- compact generators into `X` and into the successive kernels of the maps to `X`. Lemma 13.33.9
-- identifies maps from each compact generator into the homotopy colimit with the colimit of maps
-- into the stages, so the cone of the comparison map to `X` is right-orthogonal to all shifts of
-- the family. The generating hypothesis then forces that cone to be zero.
/-- Lemma 13.37.3: if each `E i` is compact and the shifts of the family `E` generate `D`, then
every object `X` admits a sequential resolution whose initial term and successive cones are direct
sums of shifts of the `E i`, and whose chosen homotopy colimit is equipped with an isomorphism to
`X`. The index `0` of the resolution corresponds to the textbook term `X₁`. -/
theorem exists_generating_family_resolution
    (hcompact : ∀ i : I, IsCompactObject (E i)) (hgenerate : IsGeneratingFamily E) (A : D) :
    ∃ (X : ℕ → D) (map : ∀ n : ℕ, X n ⟶ X (n + 1))
      (Y : ℕ → D) (triangleHom : ∀ n : ℕ, Y n ⟶ X n)
      (triangleConnecting : ∀ n : ℕ, X (n + 1) ⟶ (Y n)⟦(1 : ℤ)⟧) (Khocolim : D)
      (e : Khocolim ≅ A),
        IsGeneratingFamilyApproximation E X map Y triangleHom triangleConnecting ∧
          IsHomotopyColimitOf (Functor.ofSequence map) Khocolim := sorry

end
