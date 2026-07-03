import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_14_24_1 (from Chap14) -/
open CategoryTheory
open Abelian.DoldKan

universe v u

namespace CategoryTheory

variable {A : Type u} [Category.{v} A] [Abelian A]

/- Domain-style sampling for Lemma 14.24.1:
- primary domain: the Dold-Kan correspondence for simplicial objects in an abelian category and
  the normalized Moore complex functor;
- sampled owner declarations:
  `Abelian.DoldKan.N`,
  `Abelian.DoldKan.equivalence`,
  `Functor.ReflectsMonomorphisms`,
  `Functor.ReflectsEpimorphisms`;
- best owner abstraction: the canonical functor `N : SimplicialObject A ⥤ ChainComplex A ℕ`,
  viewed as the functor part of the Dold-Kan equivalence `Abelian.DoldKan.equivalence`;
- primitive data: only the ambient abelian category `A`;
- derived API: faithfulness and reflection of isomorphisms from the equivalence structure, and
  reflection of monomorphisms and epimorphisms from the canonical faithful-functor owners.

Source/core/bridge triage:
- `source-facing`: the four textbook clauses about the normalized Moore complex functor;
- `core/canonical`: `Abelian.DoldKan.equivalence` and its functor `N`;
- `bridge/view`: the generic functor-level instance machinery deriving reflected monos and epis
  from faithfulness.

This file therefore targets the `source-facing` layer by specializing already-canonical owner
facts, and should not keep parallel theorem wrappers around those exact instances.
-/

/- Companion recall: the normalized Moore complex functor is the functor of the canonical
Dold-Kan equivalence. -/
recall equivalence

/- Lemma 14.24.1 (1): for an abelian category `A`, the Dold-Kan normalized Moore complex functor
`N : SimplicialObject A ⥤ ChainComplex A ℕ` is faithful. -/
#check
  (show (N : SimplicialObject A ⥤ ChainComplex A ℕ).Faithful from by
    simpa using
      (inferInstance :
        ((equivalence : SimplicialObject A ≌ ChainComplex A ℕ).functor).Faithful))

/- Lemma 14.24.1 (2): for an abelian category `A`, the Dold-Kan normalized Moore complex functor
`N : SimplicialObject A ⥤ ChainComplex A ℕ` reflects isomorphisms. -/
#check
  (show Functor.ReflectsIsomorphisms (N : SimplicialObject A ⥤ ChainComplex A ℕ) from
    by
      simpa using
        (inferInstance :
          ((equivalence : SimplicialObject A ≌ ChainComplex A ℕ).functor).ReflectsIsomorphisms))

/- Lemma 14.24.1 (3): for an abelian category `A`, the Dold-Kan normalized Moore complex functor
`N : SimplicialObject A ⥤ ChainComplex A ℕ` reflects injections, i.e. monomorphisms. -/
#check
  (show Functor.ReflectsMonomorphisms (N : SimplicialObject A ⥤ ChainComplex A ℕ) from
    by
      simpa using
        (inferInstance :
          ((equivalence : SimplicialObject A ≌ ChainComplex A ℕ).functor).ReflectsMonomorphisms))

/- Lemma 14.24.1 (4): for an abelian category `A`, the Dold-Kan normalized Moore complex functor
`N : SimplicialObject A ⥤ ChainComplex A ℕ` reflects surjections, i.e. epimorphisms. -/
#check
  (show Functor.ReflectsEpimorphisms (N : SimplicialObject A ⥤ ChainComplex A ℕ) from
    by
      simpa using
        (inferInstance :
          ((equivalence : SimplicialObject A ≌ ChainComplex A ℕ).functor).ReflectsEpimorphisms))

end CategoryTheory

/-! ### Lemma_14_24_2 (from Chap14) -/
open CategoryTheory

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

section

/-
Domain-style sampling for Lemma 14.24.2:
- primary domain: equivalences of categories from chosen quasi-inverse data;
- sampled owner declarations:
  `CategoryTheory.Equivalence.mk`,
  `CategoryTheory.Functor.IsEquivalence`,
  `CategoryTheory.Functor.IsEquivalence.mk'`,
  `CategoryTheory.Functor.asEquivalence`;
- best owner abstraction: the owner predicate `Functor.IsEquivalence`, with
  `Functor.IsEquivalence.mk'` as the canonical bridge from a quasi-inverse together with unit and
  counit isomorphisms;
- primitive data: the functors `N : A ⥤ B` and `S : B ⥤ A`, the faithful and essentially
  surjective hypotheses, and the source-facing counit isomorphism `g : S ⋙ N ≅ 𝟭 B`;
- derived API: the constructed unit isomorphism `𝟭 A ≅ N ⋙ S` and the resulting equivalence
  instances for `N` and `S`;
- source/core/bridge triage:
  `source-facing`: the Stacks lemma asserting that `N` and `S` are equivalences under these
    hypotheses;
  `core/canonical`: `Functor.IsEquivalence`;
  `bridge/view`: the constructed unit isomorphism, which supplies the missing half of the
    canonical `Functor.IsEquivalence.mk'` input and should not be repackaged as a separate public
    equivalence owner.
- layer target: `source-facing` theorems stated directly in the canonical owner form
  `N.IsEquivalence` and `S.IsEquivalence`.
-/
variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable (N : A ⥤ B) (S : B ⥤ A) [N.Faithful] [S.EssSurj] (g : S ⋙ N ≅ 𝟭 B)

private noncomputable def unitIsoOfFaithfulEssSurjCounitApp (X : A) :
    X ≅ (N ⋙ S).obj X :=
  (S.objObjPreimageIso X).symm ≪≫
    S.mapIso ((g.app (S.objPreimage X)).symm ≪≫ N.mapIso (S.objObjPreimageIso X))

omit [N.Faithful] in
private theorem map_unitIsoOfFaithfulEssSurjCounitApp_hom_comp (X : A) :
    N.map ((unitIsoOfFaithfulEssSurjCounitApp N S g X).hom) ≫ g.hom.app (N.obj X) = 𝟙 (N.obj X) := by
  let e : S.obj (S.objPreimage X) ≅ X := S.objObjPreimageIso X
  have h_right :
      N.map (S.map (N.map e.hom)) ≫ g.hom.app (N.obj X) =
        g.hom.app (N.obj (S.obj (S.objPreimage X))) ≫ N.map e.hom := by
    simpa using g.hom.naturality (N.map e.hom)
  have h_left :
      N.map (S.map (g.inv.app (S.objPreimage X))) ≫
          g.hom.app (N.obj (S.obj (S.objPreimage X))) =
        g.hom.app (S.objPreimage X) ≫ g.inv.app (S.objPreimage X) := by
    simpa using g.hom.naturality (g.inv.app (S.objPreimage X))
  calc
    N.map ((unitIsoOfFaithfulEssSurjCounitApp N S g X).hom) ≫ g.hom.app (N.obj X)
        = N.map e.inv ≫
            (N.map (S.map (g.inv.app (S.objPreimage X))) ≫
              (N.map (S.map (N.map e.hom)) ≫ g.hom.app (N.obj X))) := by
              simp [unitIsoOfFaithfulEssSurjCounitApp, e, Functor.map_comp, Category.assoc]
    _ = N.map e.inv ≫
          (N.map (S.map (g.inv.app (S.objPreimage X))) ≫
            (g.hom.app (N.obj (S.obj (S.objPreimage X))) ≫ N.map e.hom)) := by
          simpa [Category.assoc] using
            congrArg
              (fun k ↦ N.map e.inv ≫ N.map (S.map (g.inv.app (S.objPreimage X))) ≫ k)
              h_right
    _ = N.map e.inv ≫
          ((N.map (S.map (g.inv.app (S.objPreimage X))) ≫
              g.hom.app (N.obj (S.obj (S.objPreimage X)))) ≫
            N.map e.hom) := by
          simp [Category.assoc]
    _ = N.map e.inv ≫ ((g.hom.app (S.objPreimage X) ≫ g.inv.app (S.objPreimage X)) ≫ N.map e.hom) := by
          simpa [Category.assoc] using congrArg (fun k ↦ N.map e.inv ≫ k ≫ N.map e.hom) h_left
    _ = N.map e.inv ≫ N.map e.hom := by
          simpa [Category.assoc] using
            congrArg (fun k ↦ N.map e.inv ≫ k ≫ N.map e.hom)
              (g.app (S.objPreimage X)).hom_inv_id
    _ = 𝟙 (N.obj X) := by
          simp [e]

private theorem unitIsoOfFaithfulEssSurjCounitApp_naturality {X Y : A} (f : X ⟶ Y) :
    f ≫ (unitIsoOfFaithfulEssSurjCounitApp N S g Y).hom =
      (unitIsoOfFaithfulEssSurjCounitApp N S g X).hom ≫ S.map (N.map f) := by
  let uX := unitIsoOfFaithfulEssSurjCounitApp N S g X
  let uY := unitIsoOfFaithfulEssSurjCounitApp N S g Y
  have hX := map_unitIsoOfFaithfulEssSurjCounitApp_hom_comp N S g X
  have hY := map_unitIsoOfFaithfulEssSurjCounitApp_hom_comp N S g Y
  apply N.map_injective
  apply (cancel_mono (g.hom.app (N.obj Y))).1
  have h_left :
      N.map (f ≫ uY.hom) ≫ g.hom.app (N.obj Y) = N.map f ≫ 𝟙 (N.obj Y) := by
    calc
      N.map (f ≫ uY.hom) ≫ g.hom.app (N.obj Y)
          = N.map f ≫ (N.map uY.hom ≫ g.hom.app (N.obj Y)) := by
              simp [Functor.map_comp, Category.assoc]
      _ = N.map f ≫ 𝟙 (N.obj Y) := by
            simpa [uY, Category.assoc] using congrArg (fun k ↦ N.map f ≫ k) hY
  have h_right :
      N.map (uX.hom ≫ S.map (N.map f)) ≫ g.hom.app (N.obj Y) = N.map f ≫ 𝟙 (N.obj Y) := by
    calc
      N.map (uX.hom ≫ S.map (N.map f)) ≫ g.hom.app (N.obj Y)
          = N.map uX.hom ≫ N.map (S.map (N.map f)) ≫ g.hom.app (N.obj Y) := by
              simp [Functor.map_comp, Category.assoc]
      _ = N.map uX.hom ≫ g.hom.app (N.obj X) ≫ N.map f := by
            simpa [Category.assoc] using
              congrArg (fun k ↦ N.map uX.hom ≫ k) (g.hom.naturality (N.map f))
      _ = 𝟙 (N.obj X) ≫ N.map f := by
            simpa [uX, Category.assoc] using congrArg (fun k ↦ k ≫ N.map f) hX
      _ = N.map f ≫ 𝟙 (N.obj Y) := by
            simp
  exact h_left.trans h_right.symm

private noncomputable def unitIsoOfFaithfulEssSurjCounit : 𝟭 A ≅ N ⋙ S :=
  NatIso.ofComponents
    (unitIsoOfFaithfulEssSurjCounitApp N S g)
    (fun f ↦ unitIsoOfFaithfulEssSurjCounitApp_naturality N S g f)

-- Proof sketch: choose, for each `X : A`, a preimage `Y : B` of `X` under the essential
-- surjectivity data for `S`, and combine the chosen isomorphism `S.obj Y ≅ X` with the counit
-- `g.app Y : N.obj (S.obj Y) ≅ Y` to obtain `X ≅ S.obj (N.obj X)`. Faithfulness of `N` shows
-- that these components are natural, so they assemble into the unit of the desired equivalence.
/-- Lemma 14.24.2: if `N : A ⥤ B` is faithful, `S : B ⥤ A` is essentially surjective, and
`g : S ⋙ N ≅ 𝟭 B`, then `N` is an equivalence of categories. -/
theorem isEquivalence_of_faithful_essSurj_of_counitIso
    (N : A ⥤ B) (S : B ⥤ A) [N.Faithful] [S.EssSurj] (g : S ⋙ N ≅ 𝟭 B) :
    N.IsEquivalence := by
  exact Functor.IsEquivalence.mk' S (unitIsoOfFaithfulEssSurjCounit N S g) g

/-- The functor `S` in Lemma 14.24.2 is likewise an equivalence. -/
theorem quasiInverse_isEquivalence_of_faithful_essSurj_of_counitIso
    (N : A ⥤ B) (S : B ⥤ A) [N.Faithful] [S.EssSurj] (g : S ⋙ N ≅ 𝟭 B) :
    S.IsEquivalence := by
  exact Functor.IsEquivalence.mk' N g.symm (unitIsoOfFaithfulEssSurjCounit N S g).symm

end

end CategoryTheory

/-! ### Theorem_14_24_3 (from Chap14) -/
universe v u

namespace CategoryTheory.Abelian.DoldKan

variable {A : Type u} [Category.{v} A] [Abelian A]

/- Domain-style sampling for Theorem 14.24.3:
- primary domain: the Dold-Kan correspondence for simplicial objects in an abelian category and
  the normalized Moore complex functor;
- sampled owner declarations:
  `CategoryTheory.Abelian.DoldKan.N`,
  `CategoryTheory.Abelian.DoldKan.Γ`,
  `CategoryTheory.Abelian.DoldKan.equivalence`,
  `CategoryTheory.Idempotents.DoldKan.equivalence`;
- best owner abstraction: the canonical owner is
  `CategoryTheory.Abelian.DoldKan.equivalence : SimplicialObject A ≌ ChainComplex A ℕ`, whose
  functor is definitionally the normalized Moore complex `N`;
- primitive data: the ambient abelian category `A`;
- derived API: the specific functors `N`, `Γ`, and the induced equivalence itself.

Source/core/bridge triage:
- `source-facing`: the theorem that the normalized Moore complex functor induces the Dold-Kan
  equivalence;
- `core/canonical`: `equivalence`;
- `bridge/view`: the comparison with the pseudoabelian construction used internally upstream. -/

/- Theorem 14.24.3: the normalized Moore complex functor
`CategoryTheory.Abelian.DoldKan.N : SimplicialObject A ⥤ ChainComplex A ℕ`
induces the Dold-Kan equivalence
`SimplicialObject A ≌ ChainComplex A ℕ`. -/
recall equivalence

end CategoryTheory.Abelian.DoldKan
