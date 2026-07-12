import StacksProject_2024.Chap22.Definition_22_26_3
import StacksProject_2024.Chap22.Situation_22_27_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open DifferentialGradedCategory

universe u v w

section

variable {R : Type u} [CommRing R]
variable {A : Type v} [D : DifferentialGradedCategory.{u, v, w} R A]
variable [HasShift (Comp R A) ℤ]
variable [HasAdmissibleCones R A]

-- Semantic recall: `lean_leansearch` surfaced the canonical square owner `CategoryTheory.CommSq`,
-- and local precedent `Chap13/Lemma_13_9_5` shows that the source-facing API should assert the
-- existence of a homotopic replacement map making the square commute strictly.

/-- Lemma 22.27.5 (1): in Situation `22.27.2`, if a square in `Comp(𝒜)` commutes up to homotopy
and the top map is an admissible monomorphism, then the right map is homotopic to a morphism
making the square commute strictly. -/
@[stacks 09QL]
theorem exists_homotopic_rightMap_of_admissibleMono
    {x y z w : Comp R A}
    {f : x ⟶ y}
    {a : x ⟶ z}
    {b : y ⟶ w}
    {g : z ⟶ w}
    (hcomm : Homotopic x.obj w.obj (f ≫ b) (a ≫ g))
    (hf : IsAdmissibleMono compForgetToDegreeZero f) :
    ∃ b' : y ⟶ w, Homotopic y.obj w.obj b b' ∧ CommSq f a b' g := sorry

/-- Bridge/view form of Lemma `22.27.5` (1): if the square already commutes in `K(𝒜)`, then the
strictifying replacement of the right map can be chosen with the same class in `K(𝒜)` as the
original map. -/
theorem exists_rightMap_eq_in_K_of_admissibleMono
    {x y z w : Comp R A}
    {f : x ⟶ y}
    {a : x ⟶ z}
    {b : y ⟶ w}
    {g : z ⟶ w}
    (sq : CommSq f.inK a.inK b.inK g.inK)
    (hf : IsAdmissibleMono compForgetToDegreeZero f) :
    ∃ b' : y ⟶ w, b.inK = b'.inK ∧ CommSq f a b' g := by
  have hcomm : Homotopic x.obj w.obj (f ≫ b) (a ≫ g) := by
    refine CompHom.homotopic_of_toHomotopyClass_eq ?_
    calc
      (f ≫ b).inK = f.inK ≫ b.inK := by
        simpa using (Comp.inKFunctor : Comp R A ⥤ K R A).map_comp f b
      _ = a.inK ≫ g.inK := sq.w
      _ = (a ≫ g).inK := by
        simpa using ((Comp.inKFunctor : Comp R A ⥤ K R A).map_comp a g).symm
  obtain ⟨b', hb, hsq⟩ := exists_homotopic_rightMap_of_admissibleMono hcomm hf
  exact ⟨b', CompHom.toHomotopyClass_eq_of_homotopic hb, hsq⟩

/-- Lemma 22.27.5 (2): in Situation `22.27.2`, if a square in `Comp(𝒜)` commutes up to homotopy
and the bottom map is an admissible epimorphism, then the left map is homotopic to a morphism
making the square commute strictly. -/
@[stacks 09QL]
theorem exists_homotopic_leftMap_of_admissibleEpi
    {x y z w : Comp R A}
    {f : x ⟶ y}
    {a : x ⟶ z}
    {b : y ⟶ w}
    {g : z ⟶ w}
    (hcomm : Homotopic x.obj w.obj (f ≫ b) (a ≫ g))
    (hg : IsAdmissibleEpi compForgetToDegreeZero g) :
    ∃ a' : x ⟶ z, Homotopic x.obj z.obj a a' ∧ CommSq f a' b g := sorry

/-- Bridge/view form of Lemma `22.27.5` (2): if the square already commutes in `K(𝒜)`, then the
strictifying replacement of the left map can be chosen with the same class in `K(𝒜)` as the
original map. -/
theorem exists_leftMap_eq_in_K_of_admissibleEpi
    {x y z w : Comp R A}
    {f : x ⟶ y}
    {a : x ⟶ z}
    {b : y ⟶ w}
    {g : z ⟶ w}
    (sq : CommSq f.inK a.inK b.inK g.inK)
    (hg : IsAdmissibleEpi compForgetToDegreeZero g) :
    ∃ a' : x ⟶ z, a.inK = a'.inK ∧ CommSq f a' b g := by
  have hcomm : Homotopic x.obj w.obj (f ≫ b) (a ≫ g) := by
    refine CompHom.homotopic_of_toHomotopyClass_eq ?_
    calc
      (f ≫ b).inK = f.inK ≫ b.inK := by
        simpa using (Comp.inKFunctor : Comp R A ⥤ K R A).map_comp f b
      _ = a.inK ≫ g.inK := sq.w
      _ = (a ≫ g).inK := by
        simpa using ((Comp.inKFunctor : Comp R A ⥤ K R A).map_comp a g).symm
  obtain ⟨a', ha, hsq⟩ := exists_homotopic_leftMap_of_admissibleEpi hcomm hg
  exact ⟨a', CompHom.toHomotopyClass_eq_of_homotopic ha, hsq⟩

end
