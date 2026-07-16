import Mathlib
import StacksProject_2024.stacks_project.Chap30.Lemma_30_23_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` surfaced `Scheme.Modules.pullback`,
-- `CategoryTheory.rightExactFunctor`, and `CategoryTheory.exactFunctor`; local precedent in
-- Lemma 30.23.2 supplies the owner `CoherentFormalModules X I`.

/-- A functor between coherent formal-module categories is the pullback along `f` when it applies
`Scheme.Modules.pullback f` to every stage and every stagewise morphism. -/
class IsCoherentFormalModulesPullbackFunctor
    {X Y : Scheme.{u}} (f : X ⟶ Y) (J : Y.IdealSheafData)
    (F : CoherentFormalModules Y J ⥤ CoherentFormalModules X (J.comap f)) : Prop where
  /-- On objects, the `n`th stage is the pullback of the original `n`th coherent sheaf. -/
  obj_eq : ∀ (M : CoherentFormalModules Y J) (n : ℕ),
    (((F.obj M).obj).obj (op n)).obj =
      (Scheme.Modules.pullback f).obj (((M.obj).obj (op n)).obj)
  /-- On morphisms, the `n`th stage map is obtained by pulling back the original stage map. -/
  map_eq : ∀ {M N : CoherentFormalModules Y J} (g : M ⟶ N) (n : ℕ),
    ((F.map g).hom.app (op n)).hom =
      eqToHom (obj_eq M n) ≫
        (Scheme.Modules.pullback f).map ((g.hom.app (op n)).hom) ≫
        eqToHom (Eq.symm (obj_eq N n))

/-- The object and morphism specifications for a coherent-formal-module pullback functor. -/
theorem isCoherentFormalModulesPullbackFunctor_spec
    {X Y : Scheme.{u}} (f : X ⟶ Y) (J : Y.IdealSheafData)
    (F : CoherentFormalModules Y J ⥤ CoherentFormalModules X (J.comap f))
    [hF : IsCoherentFormalModulesPullbackFunctor f J F] :
    (∀ (M : CoherentFormalModules Y J) (n : ℕ),
      (((F.obj M).obj).obj (op n)).obj =
        (Scheme.Modules.pullback f).obj (((M.obj).obj (op n)).obj)) ∧
      ∀ {M N : CoherentFormalModules Y J} (g : M ⟶ N) (n : ℕ),
        ((F.map g).hom.app (op n)).hom =
          eqToHom (hF.obj_eq M n) ≫
            (Scheme.Modules.pullback f).map ((g.hom.app (op n)).hom) ≫
            eqToHom (Eq.symm (hF.obj_eq N n)) := sorry

/-- Lemma 30.23.9 (1): for a morphism `f : X ⟶ Y` of Noetherian schemes and a
quasi-coherent ideal sheaf `J` on `Y`, with pulled-back ideal sheaf `J.comap f` on `X`, there is a
right exact functor `f^* : Coh(Y, J) ⥤ Coh(X, J.comap f)` whose value on a system `(G_n)` is the
stagewise pullback system `(f^* G_n)`. -/
@[stacks 0887]
theorem coherentFormalModules_pullbackFunctor_exists_rightExact
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) (J : Y.IdealSheafData) :
    ∃ pullbackFunctor : CoherentFormalModules Y J ⥤ CoherentFormalModules X (J.comap f),
      IsCoherentFormalModulesPullbackFunctor f J pullbackFunctor ∧
        rightExactFunctor (CoherentFormalModules Y J)
          (CoherentFormalModules X (J.comap f)) pullbackFunctor := sorry

/-- Lemma 30.23.9 (2): if `f : X ⟶ Y` is flat, then the stagewise pullback functor
`f^* : Coh(Y, J) ⥤ Coh(X, J.comap f)` on coherent formal modules is exact. -/
@[stacks 0887]
theorem coherentFormalModules_pullbackFunctor_exact_of_flat
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [Flat f] (J : Y.IdealSheafData)
    (pullbackFunctor : CoherentFormalModules Y J ⥤ CoherentFormalModules X (J.comap f))
    [IsCoherentFormalModulesPullbackFunctor f J pullbackFunctor] :
    exactFunctor (CoherentFormalModules Y J)
      (CoherentFormalModules X (J.comap f)) pullbackFunctor := sorry

end AlgebraicGeometry.Scheme
