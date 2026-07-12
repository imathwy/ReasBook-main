import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall note: the current project does not yet expose the explicit associated-graded
-- ideal-sheaf construction for an immersion. This file therefore keeps the source-facing
-- scheme-level conormal-algebra owner directly in terms of graded `𝒪_Z`-module sheaves.

variable {X Z : Scheme.{u}} (f : Z ⟶ X) [IsImmersion f]

local notation "𝒪Z" => (SheafOfModules.unit Z.ringCatSheaf : Z.Modules)

/-- Definition 31.19.1: a conormal algebra of an immersion `f : Z ⟶ X` is a quasi-coherent sheaf
of `ℕ`-graded `\mathcal O_Z`-algebras representing the successive quotients
`\bigoplus_{n \ge 0} \mathcal I^n / \mathcal I^{n + 1}` described above.

This source-facing owner records the degreewise `\mathcal O_Z`-module sheaves, the local unit and
multiplication maps with their graded-algebra axioms, the degree-zero identification with
`\mathcal O_Z`, and the quasi-coherence of the graded pieces. The source's nonnegative-degree
condition is encoded directly by grading over `ℕ`. The explicit ideal-power quotient realization is
left for a later companion construction once that owner exists in the current project. -/
structure ConormalAlgebra (f : Z ⟶ X) [IsImmersion f]
    where
  /-- The degree-`n` `\mathcal O_Z`-module sheaf. -/
  degree : ℕ → Z.Modules
  /-- The degree-zero unit section. -/
  one : ∀ U : (Opens Z)ᵒᵖ, (degree 0).val.obj U
  /-- The multiplication on local sections of graded pieces. -/
  mul :
    ∀ (U : (Opens Z)ᵒᵖ) (n m : ℕ),
      (degree n).val.obj U →ₗ[Z.presheaf.obj U]
        (degree m).val.obj U →ₗ[Z.presheaf.obj U] (degree (n + m)).val.obj U
  /-- The unit section commutes with restriction maps. -/
  map_one :
    ∀ {U V : (Opens Z)ᵒᵖ} (i : U ⟶ V),
      ((degree 0).val.map i).hom (one U) = one V
  /-- The multiplication maps commute with restriction maps. -/
  map_mul :
    ∀ {U V : (Opens Z)ᵒᵖ} (i : U ⟶ V) (n m : ℕ)
      (a : (degree n).val.obj U) (b : (degree m).val.obj U),
      ((degree (n + m)).val.map i).hom (mul U n m a b) =
        mul V n m (((degree n).val.map i).hom a) (((degree m).val.map i).hom b)
  /-- Multiplication is associative on local sections. -/
  mul_assoc :
    ∀ (U : (Opens Z)ᵒᵖ) (i j k : ℕ)
      (a : (degree i).val.obj U) (b : (degree j).val.obj U) (c : (degree k).val.obj U),
      HEq (mul U (i + j) k (mul U i j a b) c)
        (mul U i (j + k) a (mul U j k b c))
  /-- The unit acts as a left identity. -/
  one_mul :
    ∀ (U : (Opens Z)ᵒᵖ) (n : ℕ) (a : (degree n).val.obj U),
      HEq (mul U 0 n (one U) a) a
  /-- The unit acts as a right identity. -/
  mul_one :
    ∀ (U : (Opens Z)ᵒᵖ) (n : ℕ) (a : (degree n).val.obj U),
      HEq (mul U n 0 a (one U)) a
  /-- The degree-zero piece is the structure sheaf `\mathcal O_Z`. -/
  degreeZeroIso : degree 0 ≅ 𝒪Z
  /-- Each graded piece is quasi-coherent. -/
  isQuasicoherent : ∀ n : ℕ, ((degree n) : Z.Modules).IsQuasicoherent

/-- Every degree piece of a conormal algebra is quasi-coherent. -/
instance instIsQuasicoherentConormalAlgebraDegree
    (𝒞 : AlgebraicGeometry.Scheme.ConormalAlgebra f) (n : ℕ) :
    (𝒞.degree n).IsQuasicoherent :=
  𝒞.isQuasicoherent n

end AlgebraicGeometry.Scheme
