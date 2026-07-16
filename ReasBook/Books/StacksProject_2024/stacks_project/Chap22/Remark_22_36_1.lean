import Mathlib
import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
import Mathlib.CategoryTheory.ObjectProperty.Retract
import Mathlib.CategoryTheory.Triangulated.Orthogonal
import StacksProject_2024.stacks_project.Chap13.Lemma_13_11_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory ComplexShape DerivedCategory HomotopyCategory
open CategoryTheory.ObjectProperty
open scoped ZeroObject

noncomputable section

universe w v u

namespace CochainComplex

attribute [local instance] HasDerivedCategory.standard

-- `lean_leansearch` was unavailable in this environment; the owner choice was verified against the
-- local Chapter 13 K-projective API.

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

local notation "KQ" => quotient 𝒜 (up ℤ)
local notation "KHom" => HomotopyCategory 𝒜 (up ℤ)
local notation "Ac" => HomotopyCategory.subcategoryAcyclic 𝒜

/-- Remark 22.36.1 (1): the full subcategory `𝒟 ⊆ K(𝒜)` on the objects `P` for which the
canonical map `Hom_{K(𝒜)}(P, M) ⟶ Hom_{D(𝒜)}(P, M)` is bijective for every target `M`. -/
@[stacks 09R0]
abbrev homotopyToDerivedBijective (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :
    ObjectProperty KHom :=
  fun P ↦
    ∀ M : KHom,
      Function.Bijective
        (Qh.map : (P ⟶ M) → (Qh.obj P ⟶ Qh.obj M))

/-- Helper for Remark 22.36.1: a cochain complex is K-projective exactly when every morphism from
it to an acyclic target vanishes in the homotopy category. -/
theorem isKProjective_iff_homotopyCategory_to_acyclic_eq_zero
    (P : CochainComplex 𝒜 ℤ) :
    P.IsKProjective ↔
      ∀ (M : CochainComplex 𝒜 ℤ) (_ : M.Acyclic) (f : (KQ).obj P ⟶ (KQ).obj M), f = 0 := by
  -- Rewrite K-projectivity into the canonical left-orthogonality formulation.
  rw [isKProjective_iff_leftOrthogonal]
  constructor
  · intro h M hM f
    -- An acyclic representative gives an object of the acyclic full subcategory.
    exact h f ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic M).2 hM)
  · intro h X f hX
    -- Every acyclic object of the homotopy category is represented by an acyclic complex.
    obtain ⟨M, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    exact h M ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic M).1 hX) f

/-- A representative cochain complex lies in the source-defined full subcategory exactly when it is
K-projective. -/
theorem homotopyToDerivedBijective_iff_isKProjective
    (P : CochainComplex 𝒜 ℤ) :
    homotopyToDerivedBijective 𝒜 ((KQ).obj P) ↔ P.IsKProjective := by
  constructor
  · intro h
    -- An acyclic target becomes zero in the derived category, so injectivity of the comparison
    -- map forces every homotopy-class map to it to vanish.
    refine (isKProjective_iff_homotopyCategory_to_acyclic_eq_zero (𝒜 := 𝒜) P).2 ?_
    intro M hM f
    have hZero : CategoryTheory.Limits.IsZero (Qh.obj ((KQ).obj M)) := by
      have hkernel :
          Functor.kernel (Qh : KHom ⥤ DerivedCategory 𝒜) ((KQ).obj M) := by
        rw [subcategoryAcyclic_kernel_Qh (A := 𝒜)]
        exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
          (C := 𝒜) M).2 hM
      simpa [Functor.kernel, ObjectProperty.prop_inverseImage_iff] using hkernel
    have hQh : Qh.map f = Qh.map 0 := by
      simpa using hZero.eq_of_tgt (Qh.map f) (Qh.map 0)
    exact (h ((KQ).obj M)).injective hQh
  · intro hP
    -- The canonical K-projective comparison theorem gives the required bijection on morphisms.
    letI : P.IsKProjective := hP
    intro M
    simpa using IsKProjective.Qh_map_bijective (P : CochainComplex 𝒜 ℤ) M

/-- Remark 22.36.1 companion: the source-defined full subcategory is the canonical left
orthogonal to the acyclic complexes in `K(𝒜)`. -/
@[stacks 09R0]
theorem homotopyToDerivedBijective_eq_leftOrthogonal :
    homotopyToDerivedBijective 𝒜 = (HomotopyCategory.subcategoryAcyclic 𝒜).leftOrthogonal := by
  funext P
  apply propext
  obtain ⟨M, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  -- Every homotopy-category object is represented by a cochain complex, so both object
  -- properties reduce to the canonical K-projective criterion on that representative.
  exact (homotopyToDerivedBijective_iff_isKProjective (𝒜 := 𝒜) M).trans
    (isKProjective_iff_leftOrthogonal M)

/-- Companion bridge: the source-defined Hom-comparison property is exactly vanishing of all
morphisms in `K(𝒜)` from the complex to acyclic targets. -/
theorem homotopyToDerivedBijective_iff_homotopyToAcyclic_eq_zero
    (P : CochainComplex 𝒜 ℤ) :
    homotopyToDerivedBijective 𝒜 ((KQ).obj P) ↔
      ∀ (M : CochainComplex 𝒜 ℤ) (_ : M.Acyclic) (f : (KQ).obj P ⟶ (KQ).obj M), f = 0 := by
  exact (homotopyToDerivedBijective_iff_isKProjective (𝒜 := 𝒜) P).trans
    (isKProjective_iff_homotopyCategory_to_acyclic_eq_zero (𝒜 := 𝒜) P)

/-- Helper for Remark 22.36.1: every K-projective representative satisfies the source-defined
Hom-comparison property. -/
theorem homotopyToDerivedBijective_of_isKProjective
    (P : CochainComplex 𝒜 ℤ) (hP : P.IsKProjective) :
    homotopyToDerivedBijective 𝒜 ((KQ).obj P) := by
  -- Use the main equivalence to pass from the canonical K-projective criterion back to the
  -- source-defined comparison property.
  exact (homotopyToDerivedBijective_iff_isKProjective P).2 hP

/-- Helper for Remark 22.36.1: the source-defined Hom-comparison property forces the
representative to be K-projective. -/
theorem isKProjective_of_homotopyToDerivedBijective
    (P : CochainComplex 𝒜 ℤ)
    (hP : homotopyToDerivedBijective 𝒜 ((KQ).obj P)) :
    P.IsKProjective := by
  -- Read the comparison property through the same equivalence in the reverse direction.
  exact (homotopyToDerivedBijective_iff_isKProjective P).1 hP

/-- Pointwise bridge: the source-defined Hom-comparison property is membership in the canonical
left orthogonal to the acyclic complexes. -/
theorem homotopyToDerivedBijective_iff_leftOrthogonal (P : KHom) :
    homotopyToDerivedBijective 𝒜 P ↔
      (HomotopyCategory.subcategoryAcyclic 𝒜).leftOrthogonal P := by
  rw [homotopyToDerivedBijective_eq_leftOrthogonal]

/-- Remark 22.36.1 (2): the source-defined full subcategory is strictly full. -/
@[stacks 09R0]
instance instIsClosedUnderIsomorphisms_homotopyToDerivedBijective :
    ObjectProperty.IsClosedUnderIsomorphisms
      (homotopyToDerivedBijective 𝒜 : ObjectProperty KHom) := by
  simpa [homotopyToDerivedBijective_eq_leftOrthogonal] using
    (inferInstance :
      ObjectProperty.IsClosedUnderIsomorphisms
        (HomotopyCategory.subcategoryAcyclic 𝒜).leftOrthogonal)

/-- Remark 22.36.1 (3): the source-defined full subcategory is saturated, i.e. stable under
retracts. -/
@[stacks 09R0]
instance instIsStableUnderRetracts_homotopyToDerivedBijective :
    ObjectProperty.IsStableUnderRetracts
      (homotopyToDerivedBijective 𝒜 : ObjectProperty KHom) := by
  refine ⟨?_⟩
  intro X Y r hY
  rw [homotopyToDerivedBijective_eq_leftOrthogonal] at hY ⊢
  intro Z f hZ
  have h : r.r ≫ f = 0 := hY (r.r ≫ f) hZ
  simpa [Category.assoc, r.retract] using congrArg (fun k => r.i ≫ k) h

/-- Remark 22.36.1 (4): the source-defined full subcategory is triangulated. -/
@[stacks 09R0]
instance instIsTriangulated_homotopyToDerivedBijective :
    ObjectProperty.IsTriangulated
      (homotopyToDerivedBijective 𝒜 : ObjectProperty KHom) := by
  simpa [homotopyToDerivedBijective_eq_leftOrthogonal] using
    (inferInstance :
      ObjectProperty.IsTriangulated
        (HomotopyCategory.subcategoryAcyclic 𝒜).leftOrthogonal)

/-- Remark 22.36.1 (5): to prove the source-defined Hom-comparison property, it is enough to
check that every morphism from the complex in `K(𝒜)` to an acyclic complex is
zero. -/
@[stacks 09R0]
theorem homotopyToDerivedBijective_of_homotopyToAcyclicVanishes
    (P : CochainComplex 𝒜 ℤ)
    (hacyclic :
      ∀ (M : CochainComplex 𝒜 ℤ) (_ : M.Acyclic) (f : (KQ).obj P ⟶ (KQ).obj M), f = 0) :
    homotopyToDerivedBijective 𝒜 ((KQ).obj P) := by
  exact (homotopyToDerivedBijective_iff_homotopyToAcyclic_eq_zero P).2 hacyclic

end CochainComplex
