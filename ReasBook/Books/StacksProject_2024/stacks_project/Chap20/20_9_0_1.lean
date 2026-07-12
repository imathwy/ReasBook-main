import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
import Mathlib.Tactic.Recall

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

universe w v v' u u'

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
variable {A : Type u'} [Category.{v'} A] [HasProducts.{w} A] [Preadditive A]
variable {ι : Type w} (U : ι → C)

namespace AlgebraicTopology

section

variable {A : Type u'} [Category.{v'} A] [Preadditive A]

/-- The differential in the alternating coface map complex is `objD`. This is the dual analogue of
`alternatingFaceMapComplex_obj_d`, publicized here because Chapter 20 uses the cochain-side API
directly. -/
@[simp] theorem alternatingCofaceMapComplex_obj_d
    (X : CosimplicialObject A) (p : ℕ) :
    ((alternatingCofaceMapComplex A).obj X).d p (p + 1) = AlternatingCofaceMapComplex.objD X p := by
  dsimp only [alternatingCofaceMapComplex, AlternatingCofaceMapComplex.obj]
  exact CochainComplex.of_d _ _ _ _

end

end AlgebraicTopology

/- Domain-style sampling for 20.9.0.1:
- primary domain: the canonical Čech cochain complex attached to a family `U : ι → C` in a
  category with finite products, together with the alternating-coface formula for its
  differential;
- sampled owner declarations:
  `FormalCoproduct.cochainComplexFunctor`,
  `cechComplexFunctor`,
  `alternatingCofaceMapComplex_obj_d`,
  `AlternatingCofaceMapComplex.objD`;
- best owner abstraction: this file is a canonical support file that recalls the mathlib Čech
  owner directly and adds one source-facing bridge lemma for the differential formula. For the
  topological applications later in Chapter 20, the finite-product structure on `Opens X` is
  provided canonically by typeclass inference from mathlib rather than by a local wrapper owner.

Source/core/bridge triage:
- `source-facing`: none; this file is a canonical support file for later Čech and sheaf-cohomology
  statements in Chapter 20;
- `core/canonical`: `FormalCoproduct.cochainComplexFunctor`, `cechComplexFunctor`, and
  `AlternatingCofaceMapComplex.objD`;
- `bridge/view`: `cechComplexFunctor_d_eq_objD`, which exposes the canonical Čech differential in
  the alternating-coface form used downstream.

Primitive data versus derived API:
- primitive data: the family `U : ι → C`;
- derived API: the canonical Čech complex functor and its alternating-coface differential.
-/

/-- Helper for 20.9.0.1: the Čech complex functor is the formal-coproduct cochain complex built
from `U`. -/
@[simp] lemma cechComplexFunctor_obj_eq_formalCoproductCochainComplex
    (F : Cᵒᵖ ⥤ A) :
    (cechComplexFunctor U).obj F =
      (FormalCoproduct.cochainComplexFunctor (FormalCoproduct.mk _ U).cech).obj F := by
  -- Unfolding the Čech complex functor exposes exactly the formal-coproduct cochain model.
  rfl

/-- Helper for 20.9.0.1: the formal-coproduct Čech cochain complex is the alternating coface map
complex of the associated cosimplicial object. -/
@[simp] lemma formalCoproductCochainComplex_obj_eq_alternatingCofaceMapComplex_obj
    (F : Cᵒᵖ ⥤ A) :
    (FormalCoproduct.cochainComplexFunctor (FormalCoproduct.mk _ U).cech).obj F =
      (alternatingCofaceMapComplex A).obj
        ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj F) := by
  -- Both spellings present the same alternating-coface cochain complex attached to the Čech
  -- cosimplicial object of the formal coproduct.
  rfl

/-- Helper for 20.9.0.1: the public Čech complex is the alternating coface map complex of the
associated formal-coproduct Čech cosimplicial object. -/
@[simp] lemma cechComplexFunctor_obj_eq_alternatingCofaceMapComplex_obj
    (F : Cᵒᵖ ⥤ A) :
    (cechComplexFunctor U).obj F =
      (alternatingCofaceMapComplex A).obj
        ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj F) := by
  -- The public Čech spelling and the alternating-coface spelling are definitionally the same
  -- complex attached to the formal coproduct built from `U`.
  rfl

/-- Helper for 20.9.0.1: after transporting the whole Čech complex to its alternating-coface
presentation, the differential agrees with the alternating-coface differential. -/
@[simp] lemma cechComplexFunctor_obj_d_eq_alternatingCofaceMapComplex_obj_d
    (F : Cᵒᵖ ⥤ A) (p : ℕ) :
    ((cechComplexFunctor U).obj F).d p (p + 1) =
      ((alternatingCofaceMapComplex A).obj
        ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj F)).d
        p (p + 1) := by
  -- We remove the dependent transport by replacing the whole Čech complex first.
  cases cechComplexFunctor_obj_eq_alternatingCofaceMapComplex_obj (U := U) (A := A) F
  -- Once the complexes are identified, the two differentials are definitionally equal.
  rfl

/-- Helper for 20.9.0.1: the differential in the Čech complex is definitionally the differential
in the formal-coproduct Čech cochain complex. -/
@[simp] lemma cechComplexFunctor_obj_d_eq_formalCoproductCochainComplex_obj_d
    (F : Cᵒᵖ ⥤ A) (p : ℕ) :
    ((cechComplexFunctor U).obj F).d p (p + 1) =
      ((FormalCoproduct.cochainComplexFunctor (FormalCoproduct.mk _ U).cech).obj F).d p (p + 1) := by
  -- The two differentials agree because the underlying cochain complexes are definitionally equal.
  rfl

/-- Helper for 20.9.0.1: after transporting the formal-coproduct Čech cochain complex to its
alternating-coface presentation, the differentials agree degreewise. -/
@[simp] lemma formalCoproductCochainComplex_obj_d_eq_alternatingCofaceMapComplex_obj_d
    (F : Cᵒᵖ ⥤ A) (p : ℕ) :
    ((FormalCoproduct.cochainComplexFunctor (FormalCoproduct.mk _ U).cech).obj F).d p (p + 1) =
      ((alternatingCofaceMapComplex A).obj
        ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj F)).d
        p (p + 1) := by
  -- We remove the dependent transport by identifying the whole cochain complex first.
  cases formalCoproductCochainComplex_obj_eq_alternatingCofaceMapComplex_obj
    (U := U) (A := A) F
  -- The two differential components are then definitionally equal.
  rfl

/-- Helper for 20.9.0.1: the alternating-coface presentation of the formal-coproduct Čech
cosimplicial object computes its differential by `AlternatingCofaceMapComplex.objD`. -/
@[simp] lemma alternatingCofaceMapComplex_formalCoproduct_obj_d_eq_objD
    (F : Cᵒᵖ ⥤ A) (p : ℕ) :
    ((alternatingCofaceMapComplex A).obj
      ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj F)).d
      p (p + 1) =
      AlternatingCofaceMapComplex.objD
        ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj F) p := by
  -- This is the generic alternating-coface differential formula specialized to the Čech
  -- cosimplicial object coming from the formal coproduct of `U`.
  simpa using AlgebraicTopology.alternatingCofaceMapComplex_obj_d
    (((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj F)) p

/-- Helper for 20.9.0.1: the differential in the formal-coproduct Čech cochain complex is the
alternating coface differential `objD`. -/
lemma formalCoproductCochainComplex_obj_d_eq_objD
    (F : Cᵒᵖ ⥤ A) (p : ℕ) :
    ((FormalCoproduct.cochainComplexFunctor (FormalCoproduct.mk _ U).cech).obj F).d p (p + 1) =
      AlternatingCofaceMapComplex.objD
        ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj F) p := by
  -- Route correction: first pass through the stable formal-coproduct-to-alternating bridge.
  rw [formalCoproductCochainComplex_obj_d_eq_alternatingCofaceMapComplex_obj_d
    (U := U) (A := A) F p]
  -- The alternating presentation computes its differential by the generic `objD` formula.
  exact alternatingCofaceMapComplex_formalCoproduct_obj_d_eq_objD (U := U) (A := A) F p

/-- Helper for 20.9.0.1: the public Čech differential is the canonical alternating-coface
operator `AlternatingCofaceMapComplex.objD`. -/
lemma cechComplexFunctor_obj_d_eq_objD
    (F : Cᵒᵖ ⥤ A) (p : ℕ) :
    ((cechComplexFunctor U).obj F).d p (p + 1) =
      AlternatingCofaceMapComplex.objD
        ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj F) p := by
  -- First rewrite the public Čech complex through the stable formal-coproduct model.
  rw [cechComplexFunctor_obj_d_eq_formalCoproductCochainComplex_obj_d (U := U) (A := A) F p]
  -- The formal-coproduct model computes the differential by the canonical `objD` formula.
  exact formalCoproductCochainComplex_obj_d_eq_objD (U := U) (A := A) F p

/-- 20.9.0.1: for a family `U : ι → C` and a presheaf `F`, the degree-`p` differential in the
canonical Čech complex is the alternating coface differential of the Čech cosimplicial object of
the formal coproduct defined by `U`; unpacking `objD` gives the usual alternating-sum formula on
coordinates. -/
theorem cechComplexFunctor_d_eq_objD
    (F : Cᵒᵖ ⥤ A) (p : ℕ) :
    ((cechComplexFunctor U).obj F).d p (p + 1) =
      AlternatingCofaceMapComplex.objD
        ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj F) p := by
  -- Reuse the dedicated bridge lemma so the final theorem stays at the public Čech API.
  exact cechComplexFunctor_obj_d_eq_objD (U := U) (A := A) F p

attribute [stacks 01EE, simp] cechComplexFunctor_d_eq_objD

recall AlternatingCofaceMapComplex.objD
recall FormalCoproduct.cochainComplexFunctor
recall cechComplexFunctor
