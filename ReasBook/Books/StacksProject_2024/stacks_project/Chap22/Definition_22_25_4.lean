import Mathlib.CategoryTheory.Preadditive.Biproducts
import StacksProject_2024.Chap22.Definition_22_25_3

-- Declarations for this item will be appended below by the statement pipeline.

namespace CategoryTheory

open Limits

universe w v u

namespace GradedCategory

/- Source/core/bridge triage for Definition 22.25.4:
- source-facing: the four structure morphisms of a direct sum in a graded category, together with
  the direct-sum identities of Remark `12.3.6` and the requirement that each map has degree `0`;
- core/canonical: the corresponding `BinaryBicone` and binary biproduct in the degree-zero
  category `𝒜^0 = GradedCategory.DegreeZero 𝒜`;
- bridge/view: forgetting `𝒜^0 ⥤ 𝒜` recovers the ambient `BinaryBicone` and binary biproduct in
  `𝒜`. -/

section

variable {R : Type w} [Semiring R] {C : Type u} [Category.{v} C] [Preadditive C]
variable [GradedCategory R C]

open scoped GradedCategory

/-- Definition 22.25.4: a direct sum in a graded category over `R` is a graded direct sum if,
the structure maps `i`, `j`, `p`, and `q` satisfy the direct-sum identities of Remark `12.3.6`
and are homogeneous of degree `0`. -/
@[stacks 09P2]
class IsGradedDirectSum {x y z : C} (i : x ⟶ z) (j : y ⟶ z) (p : z ⟶ x) (q : z ⟶ y) :
    Prop where
  i_comp_p :
    i ≫ p = 𝟙 x
  i_comp_q :
    i ≫ q = 0
  j_comp_p :
    j ≫ p = 0
  j_comp_q :
    j ≫ q = 𝟙 y
  total :
    p ≫ i + q ≫ j = 𝟙 z
  i_mem_homDegree_zero :
    i ∈ Hom^0(x, z)
  j_mem_homDegree_zero :
    j ∈ Hom^0(y, z)
  p_mem_homDegree_zero :
    p ∈ Hom^0(z, x)
  q_mem_homDegree_zero :
    q ∈ Hom^0(z, y)

namespace IsGradedDirectSum

variable {x y z : C} {i : x ⟶ z} {j : y ⟶ z} {p : z ⟶ x} {q : z ⟶ y}

/-- The degree-`0` bicone in `𝒜^0` determined by graded direct-sum data. -/
def degreeZeroBicone (hds : IsGradedDirectSum i j p q) :
    BinaryBicone (⟨x⟩ : C^0) (⟨y⟩ : C^0) where
  pt := ⟨z⟩
  fst := ⟨p, by simpa using hds.p_mem_homDegree_zero⟩
  snd := ⟨q, by simpa using hds.q_mem_homDegree_zero⟩
  inl := ⟨i, by simpa using hds.i_mem_homDegree_zero⟩
  inr := ⟨j, by simpa using hds.j_mem_homDegree_zero⟩
  inl_fst := by
    apply WideSubcategory.hom_ext
    simpa [WideSubcategory.comp_def] using hds.i_comp_p
  inl_snd := by
    apply WideSubcategory.hom_ext
    simpa [WideSubcategory.comp_def] using hds.i_comp_q
  inr_fst := by
    apply WideSubcategory.hom_ext
    simpa [WideSubcategory.comp_def] using hds.j_comp_p
  inr_snd := by
    apply WideSubcategory.hom_ext
    simpa [WideSubcategory.comp_def] using hds.j_comp_q

@[simp] theorem degreeZeroBicone_fst (hds : IsGradedDirectSum i j p q) :
    (degreeZeroBicone hds).fst.hom = p :=
  rfl

@[simp] theorem degreeZeroBicone_snd (hds : IsGradedDirectSum i j p q) :
    (degreeZeroBicone hds).snd.hom = q :=
  rfl

@[simp] theorem degreeZeroBicone_inl (hds : IsGradedDirectSum i j p q) :
    (degreeZeroBicone hds).inl.hom = i :=
  rfl

@[simp] theorem degreeZeroBicone_inr (hds : IsGradedDirectSum i j p q) :
    (degreeZeroBicone hds).inr.hom = j :=
  rfl

/-- The degree-`0` bicone of a graded direct sum is a binary bilimit in `𝒜^0`. -/
def degreeZeroIsBilimit (hds : IsGradedDirectSum i j p q) :
    (degreeZeroBicone hds).IsBilimit where
  isLimit := by
    change IsLimit (BinaryFan.mk (degreeZeroBicone hds).fst (degreeZeroBicone hds).snd)
    refine BinaryFan.isLimitMk ?_ ?_ ?_ ?_
    · intro s
      let fstHom : s.pt.obj ⟶ x := s.fst.hom
      let sndHom : s.pt.obj ⟶ y := s.snd.hom
      refine ⟨fstHom ≫ i + sndHom ≫ j, ?_⟩
      exact Submodule.add_mem _
        (GradedCategory.comp_mem
          (by simpa [fstHom] using DegreeZero.hom_mem_homDegree_zero s.fst)
          hds.i_mem_homDegree_zero)
        (GradedCategory.comp_mem
          (by simpa [sndHom] using DegreeZero.hom_mem_homDegree_zero s.snd)
          hds.j_mem_homDegree_zero)
    · intro s
      apply WideSubcategory.hom_ext
      let fstHom : s.pt.obj ⟶ x := s.fst.hom
      let sndHom : s.pt.obj ⟶ y := s.snd.hom
      change (fstHom ≫ i + sndHom ≫ j) ≫ p = fstHom
      calc
        (fstHom ≫ i + sndHom ≫ j) ≫ p = fstHom ≫ (i ≫ p) + sndHom ≫ (j ≫ p) := by
          simp [Category.assoc]
        _ = fstHom ≫ 𝟙 x + sndHom ≫ 0 := by
          rw [hds.i_comp_p, hds.j_comp_p]
        _ = fstHom := by
          simp
    · intro s
      apply WideSubcategory.hom_ext
      let fstHom : s.pt.obj ⟶ x := s.fst.hom
      let sndHom : s.pt.obj ⟶ y := s.snd.hom
      change (fstHom ≫ i + sndHom ≫ j) ≫ q = sndHom
      calc
        (fstHom ≫ i + sndHom ≫ j) ≫ q = fstHom ≫ (i ≫ q) + sndHom ≫ (j ≫ q) := by
          simp [Category.assoc]
        _ = fstHom ≫ 0 + sndHom ≫ 𝟙 y := by
          rw [hds.i_comp_q, hds.j_comp_q]
        _ = sndHom := by
          simp
    · intro s m hm₁ hm₂
      apply WideSubcategory.hom_ext
      let fstHom : s.pt.obj ⟶ x := s.fst.hom
      let sndHom : s.pt.obj ⟶ y := s.snd.hom
      have hm₁' : m.hom ≫ p = fstHom := by
        simpa [fstHom, WideSubcategory.comp_def, degreeZeroBicone_fst] using
          congrArg (fun f ↦ f.hom) hm₁
      have hm₂' : m.hom ≫ q = sndHom := by
        simpa [sndHom, WideSubcategory.comp_def, degreeZeroBicone_snd] using
          congrArg (fun f ↦ f.hom) hm₂
      change m.hom = fstHom ≫ i + sndHom ≫ j
      calc
        m.hom = m.hom ≫ 𝟙 z := by
          exact (Category.comp_id m.hom).symm
        _ = m.hom ≫ (p ≫ i + q ≫ j) := by
          rw [hds.total]
        _ = m.hom ≫ (p ≫ i) + m.hom ≫ (q ≫ j) := by
          exact Preadditive.comp_add s.pt.obj z z m.hom (p ≫ i) (q ≫ j)
        _ = (m.hom ≫ p) ≫ i + (m.hom ≫ q) ≫ j := by
          rw [← Category.assoc, ← Category.assoc]
        _ = fstHom ≫ i + sndHom ≫ j := by
          rw [hm₁', hm₂']
  isColimit := by
    change IsColimit (BinaryCofan.mk (degreeZeroBicone hds).inl (degreeZeroBicone hds).inr)
    refine BinaryCofan.isColimitMk ?_ ?_ ?_ ?_
    · intro s
      let inlHom : x ⟶ s.pt.obj := s.inl.hom
      let inrHom : y ⟶ s.pt.obj := s.inr.hom
      refine ⟨p ≫ inlHom + q ≫ inrHom, ?_⟩
      exact Submodule.add_mem _
        (GradedCategory.comp_mem
          hds.p_mem_homDegree_zero
          (by simpa [inlHom] using DegreeZero.hom_mem_homDegree_zero s.inl))
        (GradedCategory.comp_mem
          hds.q_mem_homDegree_zero
          (by simpa [inrHom] using DegreeZero.hom_mem_homDegree_zero s.inr))
    · intro s
      apply WideSubcategory.hom_ext
      let inlHom : x ⟶ s.pt.obj := s.inl.hom
      let inrHom : y ⟶ s.pt.obj := s.inr.hom
      change i ≫ (p ≫ inlHom + q ≫ inrHom) = inlHom
      calc
        i ≫ (p ≫ inlHom + q ≫ inrHom) = (i ≫ p) ≫ inlHom + (i ≫ q) ≫ inrHom := by
          simp [Category.assoc]
        _ = 𝟙 x ≫ inlHom + 0 ≫ inrHom := by
          rw [hds.i_comp_p, hds.i_comp_q]
        _ = inlHom := by
          simp
    · intro s
      apply WideSubcategory.hom_ext
      let inlHom : x ⟶ s.pt.obj := s.inl.hom
      let inrHom : y ⟶ s.pt.obj := s.inr.hom
      change j ≫ (p ≫ inlHom + q ≫ inrHom) = inrHom
      calc
        j ≫ (p ≫ inlHom + q ≫ inrHom) = (j ≫ p) ≫ inlHom + (j ≫ q) ≫ inrHom := by
          simp [Category.assoc]
        _ = 0 ≫ inlHom + 𝟙 y ≫ inrHom := by
          rw [hds.j_comp_p, hds.j_comp_q]
        _ = inrHom := by
          simp
    · intro s m hm₁ hm₂
      apply WideSubcategory.hom_ext
      let inlHom : x ⟶ s.pt.obj := s.inl.hom
      let inrHom : y ⟶ s.pt.obj := s.inr.hom
      have hm₁' : i ≫ m.hom = inlHom := by
        simpa [inlHom, WideSubcategory.comp_def, degreeZeroBicone_inl] using
          congrArg (fun f ↦ f.hom) hm₁
      have hm₂' : j ≫ m.hom = inrHom := by
        simpa [inrHom, WideSubcategory.comp_def, degreeZeroBicone_inr] using
          congrArg (fun f ↦ f.hom) hm₂
      have hp : p ≫ (i ≫ m.hom) = p ≫ inlHom := by
        simpa using congrArg (fun t ↦ p ≫ t) hm₁'
      have hq : q ≫ (j ≫ m.hom) = q ≫ inrHom := by
        simpa using congrArg (fun t ↦ q ≫ t) hm₂'
      change m.hom = p ≫ inlHom + q ≫ inrHom
      calc
        m.hom = 𝟙 z ≫ m.hom := by
          exact (Category.id_comp m.hom).symm
        _ = (p ≫ i + q ≫ j) ≫ m.hom := by
          rw [hds.total]
        _ = (p ≫ i) ≫ m.hom + (q ≫ j) ≫ m.hom := by
          exact Preadditive.add_comp z z s.pt.obj (p ≫ i) (q ≫ j) m.hom
        _ = p ≫ (i ≫ m.hom) + q ≫ (j ≫ m.hom) := by
          rw [Category.assoc, Category.assoc]
        _ = p ≫ inlHom + q ≫ inrHom := by
          rw [hp, hq]

/-- A graded direct sum supplies the product-side universal property of its degree-`0` bicone. -/
instance instIsLimitDegreeZeroBicone [hds : IsGradedDirectSum i j p q] :
    IsLimit (degreeZeroBicone hds).toCone :=
  (degreeZeroIsBilimit hds).isLimit

/-- A graded direct sum supplies the coproduct-side universal property of its degree-`0` bicone. -/
instance instIsColimitDegreeZeroBicone [hds : IsGradedDirectSum i j p q] :
    IsColimit (degreeZeroBicone hds).toCocone :=
  (degreeZeroIsBilimit hds).isColimit

/-- A graded direct sum equips its two summands with a binary biproduct in the degree-zero category
`𝒜^0`. -/
abbrev hasBinaryBiproductDegreeZero (hds : IsGradedDirectSum i j p q) :
    HasBinaryBiproduct (⟨x⟩ : C^0) (⟨y⟩ : C^0) :=
  HasBinaryBiproduct.mk
    { bicone := degreeZeroBicone hds
      isBilimit := degreeZeroIsBilimit hds }

/-- The binary bicone underlying graded direct-sum data. -/
def bicone (hds : IsGradedDirectSum i j p q) : BinaryBicone x y where
  pt := z
  fst := p
  snd := q
  inl := i
  inr := j
  inl_fst := hds.i_comp_p
  inl_snd := hds.i_comp_q
  inr_fst := hds.j_comp_p
  inr_snd := hds.j_comp_q

@[simp] theorem bicone_fst (hds : IsGradedDirectSum i j p q) :
    (bicone hds).fst = p :=
  rfl

@[simp] theorem bicone_snd (hds : IsGradedDirectSum i j p q) :
    (bicone hds).snd = q :=
  rfl

@[simp] theorem bicone_inl (hds : IsGradedDirectSum i j p q) :
    (bicone hds).inl = i :=
  rfl

@[simp] theorem bicone_inr (hds : IsGradedDirectSum i j p q) :
    (bicone hds).inr = j :=
  rfl

/-- The underlying bicone of a graded direct sum is a binary bilimit. -/
def isBilimit (hds : IsGradedDirectSum i j p q) :
    (bicone hds).IsBilimit :=
  isBinaryBilimitOfTotal (bicone hds) (by simpa using hds.total)

/-- A graded direct sum supplies the product-side universal property of its underlying binary
bicone. -/
instance instIsLimitBicone [hds : IsGradedDirectSum i j p q] :
    IsLimit (bicone hds).toCone :=
  (isBilimit hds).isLimit

/-- A graded direct sum supplies the coproduct-side universal property of its underlying binary
bicone. -/
instance instIsColimitBicone [hds : IsGradedDirectSum i j p q] :
    IsColimit (bicone hds).toCocone :=
  (isBilimit hds).isColimit

/-- A graded direct sum equips its two summands with a binary biproduct. -/
abbrev hasBinaryBiproduct (hds : IsGradedDirectSum i j p q) :
    HasBinaryBiproduct x y :=
  HasBinaryBiproduct.mk
    { bicone := bicone hds
      isBilimit := isBilimit hds }

end IsGradedDirectSum

end

end GradedCategory

end CategoryTheory
