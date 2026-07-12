import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology

open CategoryTheory
open ComplexShape
open CochainComplex.HomComplex

noncomputable section

universe v u

namespace CategoryTheory
namespace CochainComplex

section

variable {C : Type u} [Category.{v} C] [Abelian C]

local notation "Cpx" => CochainComplex C ℤ

/-- Precomposition on fixed-degree Hom-complex cochains is additive. -/
lemma homComplexPrecomp_map_add
    {L M I : Cpx} (f : L ⟶ M) (n : ℤ)
    (z z' : CochainComplex.HomComplex.Cochain M I n) :
    (CochainComplex.HomComplex.Cochain.ofHom f).comp (z + z') (zero_add n) =
      (CochainComplex.HomComplex.Cochain.ofHom f).comp z (zero_add n) +
        (CochainComplex.HomComplex.Cochain.ofHom f).comp z' (zero_add n) := by
  ext p q hpq
  simp

/-- Precomposition with a cochain-complex morphism induces an additive map on fixed-degree
Hom-complex cochains. -/
noncomputable def homComplexPrecompAddMonoidHom
    {L M I : Cpx} (f : L ⟶ M) (n : ℤ) :
    CochainComplex.HomComplex.Cochain M I n →+
      CochainComplex.HomComplex.Cochain L I n where
  toFun := fun z ↦ (CochainComplex.HomComplex.Cochain.ofHom f).comp z (zero_add n)
  map_zero' := by
    ext p q hpq
    simp
  map_add' := homComplexPrecomp_map_add f n

/-- The fixed-degree precomposition maps commute with the Hom-complex differential. -/
lemma homComplexPrecomp_comm
    {L M I : Cpx} (f : L ⟶ M) (i j : ℤ) (_hij : (ComplexShape.up ℤ).Rel i j) :
    AddCommGrpCat.ofHom (homComplexPrecompAddMonoidHom (f := f) (I := I) i) ≫
        (CochainComplex.HomComplex L I).d i j =
      (CochainComplex.HomComplex M I).d i j ≫
        AddCommGrpCat.ofHom (homComplexPrecompAddMonoidHom (f := f) (I := I) j) := by
  ext z
  change
    CochainComplex.HomComplex.δ i j
        ((CochainComplex.HomComplex.Cochain.ofHom f).comp z (zero_add i)) =
      (CochainComplex.HomComplex.Cochain.ofHom f).comp
        (CochainComplex.HomComplex.δ i j z) (zero_add j)
  simpa only using
    (CochainComplex.HomComplex.δ_ofHom_comp (n := i) f z j)

/-- Precomposition with a cochain-complex morphism induces a chain map between Hom complexes. -/
noncomputable def homComplexPrecomp
    {L M I : Cpx} (f : L ⟶ M) :
    CochainComplex.HomComplex M I ⟶ CochainComplex.HomComplex L I where
  f n := AddCommGrpCat.ofHom (homComplexPrecompAddMonoidHom (f := f) (I := I) n)
  comm' := homComplexPrecomp_comm (f := f)

end

end CochainComplex
end CategoryTheory
