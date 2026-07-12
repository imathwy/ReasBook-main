import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import StacksProject_2024.Chap22.Example_22_26_6_Differential_graded_category_of_complexes
import StacksProject_2024.Chap22.Lemma_22_26_5

open CategoryTheory
open CategoryTheory.Limits
open CochainComplex.HomComplex
open DifferentialGradedCategory

noncomputable section

universe u u' v v'

namespace CategoryTheory

section

variable {𝒝 : Type u} {𝒝' : Type u'}
variable [Category.{v} 𝒝] [Category.{v'} 𝒝']
variable [Preadditive 𝒝] [Preadditive 𝒝']
variable [HasFiniteBiproducts 𝒝] [HasFiniteBiproducts 𝒝']
variable (F : 𝒝 ⥤ 𝒝') [F.Additive]

-- Source/core/bridge triage:
-- * source-facing: the DG functor on cochain complexes induced by an additive functor;
-- * core/canonical: `DifferentialGradedCategory.DgFunctor`;
-- * bridge/view: the induced functors `DgFunctor.mapComp` and `DgFunctor.mapK`.

local notation "MapComplexes" =>
  F.mapHomologicalComplex (ComplexShape.up ℤ)

/-- Lemma 22.26.7: an additive functor induces a differential graded functor on cochain
complexes. The underlying object map is the canonical ordinary functor
`F.mapHomologicalComplex (ComplexShape.up ℤ)`, while the action on homogeneous morphisms is
`Cochain.map`. Its canonical companions on `Comp` and `K` are then supplied by
`DgFunctor.mapComp` and `DgFunctor.mapK` from Lemma `22.26.5`. -/
@[stacks 09LB]
def Functor.mapCochainComplexDgFunctor :
    DgFunctor ℤ (CochainComplex 𝒝 ℤ) (CochainComplex 𝒝' ℤ) where
  obj := (MapComplexes).obj
  map {A B} {n} f := Cochain.map f F
  map_add {A B} {n} f g := by
    simpa using Cochain.map_add f g F
  map_smul {A B} {n} r f := by
    change Cochain.map (r • f) F = r • Cochain.map f F
    apply Cochain.ext
    intro p q hpq
    rw [Cochain.map_v]
    have hsmul : (r • f).v p q hpq = r • f.v p q hpq :=
      Cochain.smul_v r f p q hpq
    rw [hsmul]
    have hmap : (r • Cochain.map f F).v p q hpq = r • (Cochain.map f F).v p q hpq :=
      Cochain.smul_v r (Cochain.map f F) p q hpq
    rw [hmap, Cochain.map_v, Functor.map_zsmul]
    rfl
  map_d {A B} {n} f := by
    change Cochain.map (δ n (n + 1) f) F = δ n (n + 1) (Cochain.map f F)
    simpa using (δ_map n (n + 1) f F).symm
  map_id A := by
    change
      Cochain.map ((((Cocycle.equivHom A A) (𝟙 A) : Cocycle A A 0) : Cochain A A 0)) F =
        ((((Cocycle.equivHom ((MapComplexes).obj A) ((MapComplexes).obj A))
          (𝟙 ((MapComplexes).obj A)) : Cocycle ((MapComplexes).obj A) ((MapComplexes).obj A) 0)) :
          Cochain ((MapComplexes).obj A) ((MapComplexes).obj A) 0)
    ext n
    simp
  map_comp {A} {B} {C} {i} {j} g f := by
    change Cochain.map (Cochain.comp f g rfl) F =
      Cochain.comp (Cochain.map f F) (Cochain.map g F) rfl
    simpa using Cochain.map_comp C f g rfl F

/-- The DG functor of Lemma 22.26.7 acts on objects by the usual functor on complexes. -/
@[simp] theorem Functor.mapCochainComplexDgFunctor_obj
    (A : CochainComplex 𝒝 ℤ) :
    (F.mapCochainComplexDgFunctor).obj A = (MapComplexes).obj A := rfl

/-- The DG functor of Lemma 22.26.7 acts on homogeneous cochains by `Cochain.map`. -/
@[simp] theorem Functor.mapCochainComplexDgFunctor_map
    {A B : CochainComplex 𝒝 ℤ} {n : ℤ} (f : Cochain A B n) :
    (F.mapCochainComplexDgFunctor).map f = Cochain.map f F := rfl

end

end CategoryTheory
