import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.CategoryTheory.Preadditive.Biproducts
import StacksProject_2024.stacks_project.Chap22.Definition_22_26_1
import StacksProject_2024.stacks_project.Chap22.Lemma_22_26_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CochainComplex.HomComplex
open CochainComplex.HomComplex.Cocycle
open CochainComplex.HomComplex.CohomologyClass
open DifferentialGradedCategory
open scoped DifferentialGradedCategory

noncomputable section

universe u v

section

-- Semantic search hits: mathlib's `HomotopyCategory` and `CochainComplex.HomComplex`; the final
-- owner/API choice below was then checked against the local Chapter 22 `Comp` / `K` interface in
-- `Lemma_22_26_5`.

variable (𝒝 : Type u) [Category.{v} 𝒝] [Preadditive 𝒝] [HasFiniteBiproducts 𝒝]

/-- The Hom-complex differential squares to zero. -/
private theorem complexesDgDifferential_sq {A B : CochainComplex 𝒝 ℤ}
    (n : ℤ) (f : Cochain A B n) :
    δ (n + 1) (n + 1 + 1) (δ n (n + 1) f) = 0 := sorry

/-- The identity cochain is closed for the Hom-complex differential. -/
private theorem complexesDgId_closed (A : CochainComplex 𝒝 ℤ) :
    δ 0 1 ((((Cocycle.equivHom A A) (𝟙 A) : Cocycle A A 0) : Cochain A A 0)) = 0 := sorry

/-- Left unit for homogeneous composition of cochains. -/
private theorem complexesDgComp_id_left {A B : CochainComplex 𝒝 ℤ}
    {n : ℤ} (f : Cochain A B n) :
    castHom (add_zero n) (Cochain.comp f (((Cocycle.equivHom B B) (𝟙 B) : Cocycle B B 0)) rfl) =
      f := sorry

/-- Right unit for homogeneous composition of cochains. -/
private theorem complexesDgComp_id_right {A B : CochainComplex 𝒝 ℤ}
    {n : ℤ} (f : Cochain A B n) :
    castHom (zero_add n) (Cochain.comp (((Cocycle.equivHom A A) (𝟙 A) : Cocycle A A 0)) f rfl) =
      f := sorry

/-- Associativity of homogeneous composition of cochains. -/
private theorem complexesDgComp_assoc {W X Y Z : CochainComplex 𝒝 ℤ}
    {i j k : ℤ}
    (h : Cochain Y Z k) (g : Cochain X Y j) (f : Cochain W X i) :
    castHom (add_assoc i j k) (Cochain.comp (Cochain.comp f g rfl) h rfl) =
      Cochain.comp f (Cochain.comp g h rfl) rfl := sorry

/-- Composition is additive in the left variable. -/
private theorem complexesDgComp_add_left {A B C : CochainComplex 𝒝 ℤ} {i j : ℤ}
    (g₁ g₂ : Cochain B C j) (f : Cochain A B i) :
    Cochain.comp f (g₁ + g₂) rfl = Cochain.comp f g₁ rfl + Cochain.comp f g₂ rfl := sorry

/-- Composition is additive in the right variable. -/
private theorem complexesDgComp_add_right {A B C : CochainComplex 𝒝 ℤ} {i j : ℤ}
    (g : Cochain B C j) (f₁ f₂ : Cochain A B i) :
    Cochain.comp (f₁ + f₂) g rfl = Cochain.comp f₁ g rfl + Cochain.comp f₂ g rfl := sorry

/-- Composition is `ℤ`-linear in the left variable. -/
private theorem complexesDgComp_zsmul_left {A B C : CochainComplex 𝒝 ℤ} {i j : ℤ}
    (r : ℤ) (g : Cochain B C j) (f : Cochain A B i) :
    Cochain.comp f (r • g) rfl = r • Cochain.comp f g rfl := sorry

/-- Composition is `ℤ`-linear in the right variable. -/
private theorem complexesDgComp_zsmul_right {A B C : CochainComplex 𝒝 ℤ} {i j : ℤ}
    (r : ℤ) (g : Cochain B C j) (f : Cochain A B i) :
    Cochain.comp (r • f) g rfl = r • Cochain.comp f g rfl := sorry

/-- The Hom-complex differential satisfies the graded Leibniz rule on homogeneous cochains. -/
private theorem complexesDgDifferential_comp {A B C : CochainComplex 𝒝 ℤ}
    {i j : ℤ} (g : Cochain B C j) (f : Cochain A B i) :
    δ (i + j) (i + j + 1) (Cochain.comp f g rfl) =
      @castHom ℤ (fun n : ℤ ↦ Cochain A C n) _ _ (d_comp_left_index i j)
          (Cochain.comp f (δ j (j + 1) g) rfl) +
        (j.negOnePow : ℤ) •
          @castHom ℤ (fun n : ℤ ↦ Cochain A C n) _ _ (d_comp_right_index i j)
            (Cochain.comp (δ i (i + 1) f) g rfl) := sorry

/-- Example 22.26.6 (Differential graded category of complexes) (1): for an additive category
`𝒝`, the cochain complexes in `𝒝` form a differential graded category over `ℤ`. The graded Hom
object is the canonical Hom complex `CochainComplex.HomComplex`, the
differential is `δ`, identities are the degree-`0` cocycles corresponding to identity maps of
complexes, and composition is the usual graded composition of cochains. -/
@[stacks 09L9, reducible]
instance complexesDifferentialGradedCategory :
    DifferentialGradedCategory ℤ (CochainComplex 𝒝 ℤ) where
  Hom := fun A B n ↦ Cochain A B n
  homAddCommGroup := fun _ _ _ ↦ inferInstance
  homModule := fun _ _ _ ↦ inferInstance
  d := fun n f ↦ δ n (n + 1) f
  id := fun A ↦ ((Cocycle.equivHom A A) (𝟙 A) : Cocycle A A 0)
  comp := fun g f ↦ Cochain.comp f g rfl
  d_sq := fun n f ↦ complexesDgDifferential_sq 𝒝 n f
  d_id := fun A ↦ complexesDgId_closed 𝒝 A
  id_comp_hom := fun f ↦ complexesDgComp_id_left 𝒝 f
  comp_id_hom := fun f ↦ complexesDgComp_id_right 𝒝 f
  comp_assoc := fun h g f ↦ complexesDgComp_assoc 𝒝 h g f
  comp_add_left := fun g₁ g₂ f ↦ complexesDgComp_add_left 𝒝 g₁ g₂ f
  comp_add_right := fun g f₁ f₂ ↦ complexesDgComp_add_right 𝒝 g f₁ f₂
  comp_smul_left := fun r g f ↦ complexesDgComp_zsmul_left 𝒝 r g f
  comp_smul_right := fun r g f ↦ complexesDgComp_zsmul_right 𝒝 r g f
  d_add := by
    intro A B n f g
    sorry
  d_smul := by
    intro A B n r f
    sorry
  d_comp := fun g f ↦ complexesDgDifferential_comp 𝒝 g f

/-- Example 22.26.6 (Differential graded category of complexes) (2): the Hom object in
`complexesDifferentialGradedCategory` is the graded group of cochains between complexes. -/
@[simp] theorem complexesDifferentialGradedCategory_hom
    (A B : CochainComplex 𝒝 ℤ) (n : ℤ) :
    (A ⟶[n] B) = Cochain A B n := rfl

variable (A B : CochainComplex 𝒝 ℤ) (n : ℤ)

/- Closed degree-`0` elements of the Hom complex are identified with maps of complexes by the
canonical equivalence `Cocycle.equivHom`. -/
#check (Cocycle.equivHom A B)

/- Cohomology classes of the Hom complex are identified with morphisms in the homotopy category
into the corresponding shift by the canonical composite below. -/
#check (homologyAddEquiv A B n).trans homAddEquiv

end
