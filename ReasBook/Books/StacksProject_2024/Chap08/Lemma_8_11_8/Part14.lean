import Mathlib
import Mathlib.CategoryTheory.Sites.Over
import StacksProject_2024.Chap07.Lemma_7_26_5
import StacksProject_2024.Chap07.Lemma_7_26_6
import StacksProject_2024.Chap08.Lemma_8_3_7
import StacksProject_2024.Chap08.Definition_8_5_5
import StacksProject_2024.Chap08.Definition_8_11_1
import StacksProject_2024.Chap08.Lemma_8_11_8.Part13

universe u v w

namespace CategoryTheory

open StackInGroupoidsOver
open Opposite
open Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {𝒮 : StackInGroupoidsOver J}
/-- Helper for Lemma 8.11.8: the remaining owner-composite component of the pulled chosen-local
conjugation should agree with the literal `qS := S.unop.hom ≫ (I.Y.hom ≫ K.f)` common-owner shell
evaluated on the pulled section. This isolates the last unresolved comparison after the generic
owner-transport shell has already been normalized. -/
private theorem chosen_local_owner_component_eq_qS_common_owner_shell_app
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} {x : 𝒮.p.Fiber U}
    (L : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (K :
      (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).Arrow)
    {T : (Over K.Y)ᵒᵖ}
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow)
    {S : (Over I.Y.left)ᵒᵖ}
    (β :
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        ((I.Y.hom ≫ K.f) ^*[canonicalPullbackChoice 𝒮.p]
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.obj S) :
    let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
    let qS : S.unop.left ⟶ L.Y := S.unop.hom ≫ qI
    ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
              (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom).1.app
          (op (Over.mk (S.unop.hom ≫ I.Y.hom))))
        (Eq.mp
          (congrArg
            ((automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).1.obj)
            (over_map_obj_mk_eq_op I.Y.hom S.unop.hom (S.unop.hom ≫ I.Y.hom) rfl))
          β)) =
    ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_common_owner_isomorphism
              (𝒮 := 𝒮) hGerbe qS (K := K) (g := S.unop.hom ≫ I.Y.hom)
              (by simp [qI, qS, Category.assoc])).hom).hom).1.app
          (op (Over.mk (𝟙 S.unop.left))))
        (pullHom β S.unop.hom (𝟙 I.Y.left) (𝟙 I.Y.left)
          (by simp) (by simp))) := by
  let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
  let qS : S.unop.left ⟶ L.Y := S.unop.hom ≫ qI
  let βS :=
    pullHom β S.unop.hom (𝟙 I.Y.left) (𝟙 I.Y.left) (by simp) (by simp)
  have howner_transport :
      ((((J.pseudofunctorOver (Type (max u v))).map
            (S.unop.hom ≫ I.Y.hom).op.toLoc).toFunctor.map
          ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
              (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom)).1.app
          (op (Over.mk (𝟙 S.unop.left))))
        βS =
      ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
              (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom).1.app
          (op (Over.mk (S.unop.hom ≫ I.Y.hom))))
        (Eq.mp
          (congrArg
            ((automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).1.obj)
            (over_map_obj_mk_eq_op (S.unop.hom ≫ I.Y.hom) (𝟙 S.unop.left)
              (S.unop.hom ≫ I.Y.hom) (by simp)))
          βS) := by
    -- First move the pulled chosen-local conjugation to the literal owner
    -- `op (Over.mk (𝟙 S.unop.left)))`.
    simpa [βS] using
      (pseudofunctor_over_map_app_eq_owner_transport
        (J := J) (g := S.unop.hom ≫ I.Y.hom)
        (φ := (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom)
        (k := 𝟙 S.unop.left) (h := S.unop.hom ≫ I.Y.hom) (hk := by simp)
        (s := βS))
  have hβinput :
      (Eq.mp
        (congrArg
          ((automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).1.obj)
          (over_map_obj_mk_eq_op I.Y.hom S.unop.hom
            (S.unop.hom ≫ I.Y.hom) rfl))
        β) =
      (Eq.mp
        (congrArg
          ((automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).1.obj)
          (over_map_obj_mk_eq_op (S.unop.hom ≫ I.Y.hom) (𝟙 S.unop.left)
            (S.unop.hom ≫ I.Y.hom) (by simp)))
        βS := by
    -- This is the remaining cast bridge between the statement's explicit owner component and the
    -- literal owner input used by the `qS` shell.
    simpa [βS] using
      chosen_local_owner_leg_source_boundary_input_eq_pullHom_app
        (𝒮 := 𝒮) hGerbe hAbelian L K I β
  -- Route correction: once the owner transport and input cast are aligned, the proof should now
  -- close through the direct `qS` owner-leg comparison rather than reopening the shell adapter.
  calc
    ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
              (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom).1.app
          (op (Over.mk (S.unop.hom ≫ I.Y.hom))))
        (Eq.mp
          (congrArg
            ((automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).1.obj)
            (over_map_obj_mk_eq_op I.Y.hom S.unop.hom (S.unop.hom ≫ I.Y.hom) rfl))
          β)) =
      ((((J.pseudofunctorOver (Type (max u v))).map
            (S.unop.hom ≫ I.Y.hom).op.toLoc).toFunctor.map
          ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
              (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom)).1.app
          (op (Over.mk (𝟙 S.unop.left))))
        βS := by
          rw [hβinput]
          exact howner_transport.symm
    _ =
      ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_common_owner_isomorphism
              (𝒮 := 𝒮) hGerbe qS (K := K) (g := S.unop.hom ≫ I.Y.hom)
              (by simp [qI, qS, Category.assoc])).hom).hom).1.app
          (op (Over.mk (𝟙 S.unop.left))))
        βS) := by
          -- The last step is exactly the direct owner-leg comparison at the composite owner `qS`.
          simpa [qI, qS, βS] using
            chosen_local_qS_pulled_conjugation_eq_common_owner_component_app
              (𝒮 := 𝒮) hGerbe hAbelian L K I β

/-- Helper for Lemma 8.11.8: after the owner-change comparison is rewritten to the literal owner
`op (Over.mk (𝟙 S.unop.left))`, the pullback of the fixed `qI` common-owner shell is just the
actual `S`-component of that shell. This packages the final owner-leg transport back to the
component used by the main corridor. -/
private theorem chosen_local_owner_leg_pullback_qI_shell_eq_common_owner_component_app
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} {x : 𝒮.p.Fiber U}
    (L : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (K :
      (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).Arrow)
    {T : (Over K.Y)ᵒᵖ}
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow)
    {S : (Over I.Y.left)ᵒᵖ}
    (β :
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        ((I.Y.hom ≫ K.f) ^*[canonicalPullbackChoice 𝒮.p]
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.obj S) :
    let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
    ((((((J.pseudofunctorOver (Type (max u v))).map S.unop.hom.op.toLoc).toFunctor.map
            ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              (chosen_local_common_owner_isomorphism
                (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
                (by simp [qI])).hom).hom)).1.app
          (op (Over.mk (𝟙 S.unop.left)))))
        (pullHom β S.unop.hom (𝟙 I.Y.left) (𝟙 I.Y.left)
          (by simp) (by simp)) =
      ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_common_owner_isomorphism
              (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
              (by simp [qI])).hom).hom).1.app S)
        β) := by
  let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
  -- Collapse the owner-leg pullback shell back to the actual `S`-component of the fixed
  -- common-owner conjugation.
  simpa [qI] using
    (pseudofunctor_over_map_app_eq_owner_transport
      (J := J) (g := S.unop.hom)
      (φ := (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (chosen_local_common_owner_isomorphism
          (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
          (by simp [qI])).hom).hom)
      (k := 𝟙 S.unop.left) (h := S.unop.hom) (hk := by simp)
      (s := pullHom β S.unop.hom (𝟙 I.Y.left) (𝟙 I.Y.left)
        (by simp) (by simp)))

/-- Helper for Lemma 8.11.8: after identifying the literal owner
`qS := S.unop.hom ≫ (I.Y.hom ≫ K.f)`, its common-owner component is exactly the actual
`S`-component of the fixed `qI := I.Y.hom ≫ K.f` common-owner comparison. This packages the
owner-leg transport corridor as one reusable app-level equality. -/
private theorem chosen_local_qS_common_owner_component_eq_qI_common_owner_component_app
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} {x : 𝒮.p.Fiber U}
    (L : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (K :
      (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).Arrow)
    {T : (Over K.Y)ᵒᵖ}
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow)
    {S : (Over I.Y.left)ᵒᵖ}
    (β :
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        ((I.Y.hom ≫ K.f) ^*[canonicalPullbackChoice 𝒮.p]
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.obj S) :
    let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
    let qS : S.unop.left ⟶ L.Y := S.unop.hom ≫ qI
    let βS :=
      pullHom β S.unop.hom (𝟙 I.Y.left) (𝟙 I.Y.left) (by simp) (by simp)
    ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe qS (K := K) (g := S.unop.hom ≫ I.Y.hom)
            (by simp [qI, qS, Category.assoc])).hom).hom).1.app
        (op (Over.mk (𝟙 S.unop.left))))
      βS) =
      ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_common_owner_isomorphism
              (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
              (by simp [qI])).hom).hom).1.app S)
        β) := by
  let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
  let qS : S.unop.left ⟶ L.Y := S.unop.hom ≫ qI
  let βS :=
    pullHom β S.unop.hom (𝟙 I.Y.left) (𝟙 I.Y.left) (by simp) (by simp)
  -- First expose the `qS` common-owner component as the owner-leg pullback of the fixed `qI`
  -- common-owner shell.
  calc
    ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe qS (K := K) (g := S.unop.hom ≫ I.Y.hom)
            (by simp [qI, qS, Category.assoc])).hom).hom).1.app
        (op (Over.mk (𝟙 S.unop.left))))
      βS) =
        ((((((J.pseudofunctorOver (Type (max u v))).map S.unop.hom.op.toLoc).toFunctor.map
              ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
                (chosen_local_common_owner_isomorphism
                  (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
                  (by simp [qI])).hom).hom)).1.app
            (op (Over.mk (𝟙 S.unop.left)))))
          βS) := by
            simpa [qI, qS, βS] using
              chosen_local_owner_leg_qS_common_owner_shell_eq_pullback_qI_app
                (𝒮 := 𝒮) hGerbe hAbelian L K I β
    _ =
        ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              (chosen_local_common_owner_isomorphism
                (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
                (by simp [qI])).hom).hom).1.app S)
          β) := by
            -- Then collapse that owner-leg pullback back to the actual `S`-component.
            simpa [qI, βS] using
              chosen_local_owner_leg_pullback_qI_shell_eq_common_owner_component_app
                (𝒮 := 𝒮) hGerbe hAbelian L K I β

/-- Helper for Lemma 8.11.8: before evaluating on the literal owner
`op (Over.mk (𝟙 I.Y.left))`, commute the remaining raw source-side `mapComp'` inverse boundary
through the common-owner middle shell after specializing to an arbitrary owner leg
`S : Over I.Y.left`. This isolates the exact owner-generic naturality rewrite that is still
missing. -/
private theorem chosen_local_owner_leg_pulled_conjugation_eq_common_owner_component_app
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} {x : 𝒮.p.Fiber U}
    (L : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (K :
      (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).Arrow)
    {T : (Over K.Y)ᵒᵖ}
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow)
    {S : (Over I.Y.left)ᵒᵖ}
    (β :
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        ((I.Y.hom ≫ K.f) ^*[canonicalPullbackChoice 𝒮.p]
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.obj S) :
    let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
    ((((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.map
        ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom)).1.app S)
      β =
      ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_common_owner_isomorphism
              (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
              (by simp [qI])).hom).hom).1.app S)
        β) := by
  -- Reuse the earlier fixed-owner normalization so the later owner-leg corridor does not
  -- duplicate the same comparison.
  simpa using
    chosen_local_fixed_qI_component_normalized_app
      (𝒮 := 𝒮) hGerbe hAbelian L K I β

/-- Helper for Lemma 8.11.8: before evaluating on the literal owner
`op (Over.mk (𝟙 I.Y.left))`, commute the remaining raw source-side `mapComp'` inverse boundary
through the common-owner middle shell after specializing to an arbitrary owner leg
`S : Over I.Y.left`. This isolates the exact owner-generic naturality rewrite that is still
missing. -/
private theorem chosen_local_common_owner_middle_owner_leg_normalized_app
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} {x : 𝒮.p.Fiber U}
    (L : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (K :
      (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).Arrow)
    {T : (Over K.Y)ᵒᵖ}
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow)
    {S : (Over I.Y.left)ᵒᵖ}
    (β :
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        ((I.Y.hom ≫ K.f) ^*[canonicalPullbackChoice 𝒮.p]
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.obj S) :
    let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
    ((((((((J.pseudofunctorOver (Type (max u v))).mapComp'
              K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)).inv.toNatTrans.app
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))) ≫
          (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_common_owner_isomorphism
              (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
              (by simp [qI])).hom).hom ≫
          (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_common_owner_target_iso
              (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
              (by simp [qI])).hom).hom).1.app S)
      β) =
      ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_common_owner_isomorphism
              (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
              (by simp [qI])).hom).hom).1.app S)
        β) := by
  let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
  -- Route correction: first collapse the explicit boundary shell to the pulled chosen-local
  -- conjugation along `I.Y.hom`; only the owner-leg transport back to the common-owner component
  -- remains open afterwards.
  trans
    ((((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.map
        ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom)).1.app S)
      β
  · simpa [qI] using
      chosen_local_common_owner_middle_as_pulled_conjugation_app
        (𝒮 := 𝒮) hGerbe hAbelian L K I β
  · -- The remaining owner-leg transport is isolated in the dedicated bridge lemma above.
    simpa [qI] using
      chosen_local_owner_leg_pulled_conjugation_eq_common_owner_component_app
        (𝒮 := 𝒮) hGerbe hAbelian L K I β

/-- Helper for Lemma 8.11.8: before evaluating on the literal owner
`op (Over.mk (𝟙 I.Y.left))`, commute the remaining raw source-side `mapComp'` inverse boundary
through the common-owner middle shell as a sheaf-morphism equality. -/
private theorem chosen_local_common_owner_middle_raw_boundary_component_transport
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} {x : 𝒮.p.Fiber U}
    (L : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (K :
      (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).Arrow)
    {T : (Over K.Y)ᵒᵖ}
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow)
    {S : (Over I.Y.left)ᵒᵖ}
    (β :
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        ((I.Y.hom ≫ K.f) ^*[canonicalPullbackChoice 𝒮.p]
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.obj S) :
    let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
    ((((((((J.pseudofunctorOver (Type (max u v))).mapComp'
              K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)).inv.toNatTrans.app
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))) ≫
          (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_common_owner_isomorphism
              (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
              (by simp [qI])).hom).hom ≫
          (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_common_owner_target_iso
              (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
              (by simp [qI])).hom).hom).1.app S)
      β) =
      ((((((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              (chosen_local_common_owner_isomorphism
                (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
                (by simp [qI])).hom).hom) ≫
            (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              (chosen_local_common_owner_target_iso
                (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
                (by simp [qI])).hom).hom) ≫
          (((J.pseudofunctorOver (Type (max u v))).mapComp'
              K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)).inv.toNatTrans.app
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
              (L.f ^*[canonicalPullbackChoice 𝒮.p] x)))).1.app S)
      β) := by
  let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
  -- Route correction: the owner-generic naturality fight is now isolated in the previous helper,
  -- so this component theorem only reduces both sides to the same bare common-owner middle map.
  calc
    ((((((((J.pseudofunctorOver (Type (max u v))).mapComp'
              K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)).inv.toNatTrans.app
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))) ≫
          (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_common_owner_isomorphism
              (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
              (by simp [qI])).hom).hom ≫
          (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_common_owner_target_iso
              (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
              (by simp [qI])).hom).hom).1.app S)
      β) =
        ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              (chosen_local_common_owner_isomorphism
                (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
                (by simp [qI])).hom).hom).1.app S)
          β) := by
            simpa [qI] using
              chosen_local_common_owner_middle_owner_leg_normalized_app
                (𝒮 := 𝒮) hGerbe hAbelian L K I β
    _ =
        ((((((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
                (chosen_local_common_owner_isomorphism
                  (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
                  (by simp [qI])).hom).hom) ≫
              (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
                (chosen_local_common_owner_target_iso
                  (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
                  (by simp [qI])).hom).hom) ≫
            (((J.pseudofunctorOver (Type (max u v))).mapComp'
                K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)).inv.toNatTrans.app
              (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
                (L.f ^*[canonicalPullbackChoice 𝒮.p] x)))).1.app S)
        β) := by
          -- Collapse the target-side `hom ≫ inv` shell, leaving only the common-owner middle map.
          symm
          simpa [qI, Category.assoc] using
            congrFun
              (congrArg
                (fun ψ ↦
                  (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
                      (chosen_local_common_owner_isomorphism
                        (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
                        (by simp [qI])).hom).hom ≫ ψ).1.app S))
                (chosen_local_target_boundary_normalization
                  (𝒮 := 𝒮) hGerbe hAbelian qI (K := K) I.Y.hom (by simp [qI])))
              β

/-- Helper for Lemma 8.11.8: before evaluating on the literal owner
`op (Over.mk (𝟙 I.Y.left))`, commute the remaining raw source-side `mapComp'` inverse boundary
through the common-owner middle shell as a sheaf-morphism equality. -/
private theorem chosen_local_common_owner_middle_raw_boundary_transport
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} {x : 𝒮.p.Fiber U}
    (L : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (K :
      (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).Arrow)
    {T : (Over K.Y)ᵒᵖ}
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow) :
    let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
    ((((J.pseudofunctorOver (Type (max u v))).mapComp'
        K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)).inv.toNatTrans.app
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))) ≫
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (chosen_local_common_owner_isomorphism
          (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
          (by simp [qI])).hom).hom ≫
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (chosen_local_common_owner_target_iso
          (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
          (by simp [qI])).hom).hom) =
      ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
            (by simp [qI])).hom).hom ≫
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_common_owner_target_iso
            (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
            (by simp [qI])).hom).hom ≫
        (((J.pseudofunctorOver (Type (max u v))).mapComp'
            K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)).inv.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x)))) := by
  -- Route correction: once the owner-generic component transport is named explicitly, the
  -- sheaf-level equality is only extensionality on `S : Over I.Y.left`.
  apply Sheaf.hom_ext
  ext S β
  exact
    chosen_local_common_owner_middle_raw_boundary_component_transport
      (𝒮 := 𝒮) hGerbe hAbelian L K I β

/-- Helper for Lemma 8.11.8: evaluating the previous sheaf-morphism transport on the literal
owner `op (Over.mk (𝟙 I.Y.left))` gives the exact middle rewrite needed in the app-level boundary
cancelation proof. -/
private theorem chosen_local_common_owner_middle_raw_boundary_transport_app
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y)
    (L : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (K :
      (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).Arrow)
    (T : (Over K.Y)ᵒᵖ)
    (α :
      ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.obj T))
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow) :
    let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
    let αI :=
      ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.map I.f.op α)
    let pulledφ :
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x) ⟶
          (L.f ^*[canonicalPullbackChoice 𝒮.p] y) :=
      ((canonicalPullbackChoice 𝒮.p).pullbackFunctor L.f).map φ
    (((((((((J.pseudofunctorOver (Type (max u v))).mapComp'
              K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)).inv.toNatTrans.app
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))) ≫
          (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_common_owner_isomorphism
              (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
              (by simp [qI])).hom).hom ≫
          (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_common_owner_target_iso
              (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
              (by simp [qI])).hom).hom) ≫
        ((J.pseudofunctorOver (Type (max u v))).map qI.op.toLoc).toFunctor.map
          ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian pulledφ).hom)).1.app
        (op (Over.mk (𝟙 I.Y.left))))
      αI) =
      (((((((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              (chosen_local_common_owner_isomorphism
                (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
                (by simp [qI])).hom).hom) ≫
            (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              (chosen_local_common_owner_target_iso
                (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
                (by simp [qI])).hom).hom) ≫
          (((J.pseudofunctorOver (Type (max u v))).mapComp'
              K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)).inv.toNatTrans.app
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
              (L.f ^*[canonicalPullbackChoice 𝒮.p] x)))) ≫
        ((J.pseudofunctorOver (Type (max u v))).map qI.op.toLoc).toFunctor.map
          ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian pulledφ).hom)).1.app
        (op (Over.mk (𝟙 I.Y.left))))
      αI) := by
  let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
  let αI :=
    ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.map I.f.op α)
  let pulledφ :
      (L.f ^*[canonicalPullbackChoice 𝒮.p] x) ⟶
        (L.f ^*[canonicalPullbackChoice 𝒮.p] y) :=
    ((canonicalPullbackChoice 𝒮.p).pullbackFunctor L.f).map φ
  -- Append the already-exposed pulled-`φ` tail after the sheaf-level transport, then evaluate on
  -- the literal owner section `αI`.
  simpa [qI, αI, pulledφ, Category.assoc] using
    congrFun
      (congrArg
        (fun ψ ↦
          ((ψ ≫
              ((J.pseudofunctorOver (Type (max u v))).map qI.op.toLoc).toFunctor.map
                ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian pulledφ).hom)).1.app
            (op (Over.mk (𝟙 I.Y.left)))))
        (chosen_local_common_owner_middle_raw_boundary_transport
          (𝒮 := 𝒮) hGerbe hAbelian L K I))
      αI

/-- Helper for Lemma 8.11.8: on one refinement member of the pulled chosen local `y`-cover, the
restricted left branch can be rewritten all the way to the shared-owner `qI := I.Y.hom ≫ K.f`
shell for the source chosen local cover arrow `K`, followed by the pulled morphism on that same
owner. This isolates the last source-side transport before the cross-cover common-owner
comparison is applied. -/
private theorem chosen_local_source_common_owner_boundary_cancel_app
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y)
    (L : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (K :
      (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).Arrow)
    (T : (Over K.Y)ᵒᵖ)
    (α :
      ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.obj T))
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow) :
    let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
    let αI :=
      ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.map I.f.op α)
    let pulledφ :
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x) ⟶
          (L.f ^*[canonicalPullbackChoice 𝒮.p] y) :=
      ((canonicalPullbackChoice 𝒮.p).pullbackFunctor L.f).map φ
    ((((((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_common_owner_source_iso
              (𝒮 := 𝒮) hGerbe qI I.Y.hom (by simp [qI])).inv.hom).hom) ≫
          (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_common_owner_isomorphism
              (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
              (by simp [qI])).hom).hom ≫
          (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_common_owner_target_iso
              (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
              (by simp [qI])).hom).hom) ≫
        ((J.pseudofunctorOver (Type (max u v))).map qI.op.toLoc).toFunctor.map
          ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian pulledφ).hom)).1.app
        (op (Over.mk (𝟙 I.Y.left))))
      αI) =
      ((((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_common_owner_isomorphism
              (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
              (by simp [qI])).hom).hom) ≫
          (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (((canonicalPullbackChoice 𝒮.p).pullbackFunctor qI).map pulledφ)).hom).1.app
        (op (Over.mk (𝟙 I.Y.left))))
      αI) := by
  -- First expose the source-side common-owner inverse comparison as the raw `mapComp'` boundary.
  rw [chosen_local_source_common_owner_left_flank_mapComp_app
    (𝒮 := 𝒮) hGerbe hAbelian φ L K T α I]
  -- Route correction: the remaining middle transport is now isolated as a single sheaf-level
  -- rewrite, evaluated once on the literal owner.
  rw [chosen_local_common_owner_middle_raw_boundary_transport_app
    (𝒮 := 𝒮) hGerbe hAbelian φ L K T α I]
  -- After that transport, the tail is exactly the already-normalized pulled-`φ` shell.
  exact
    chosen_local_source_common_owner_pulled_phi_tail_app
      (𝒮 := 𝒮) hGerbe hAbelian φ L K T α I

/-- Helper for Lemma 8.11.8: on one refinement member of the pulled chosen local `y`-cover, the
restricted left branch can be rewritten all the way to the shared-owner `qI := I.Y.hom ≫ K.f`
shell for the source chosen local cover arrow `K`, followed by the pulled morphism on that same
owner. This isolates the last source-side transport before the cross-cover common-owner
comparison is applied. -/
private theorem chosen_local_source_common_owner_middle_with_pulled_phi_app
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y)
    (L : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (K :
      (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).Arrow)
    (T : (Over K.Y)ᵒᵖ)
    (α :
      ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.obj T))
    {B : J.Cover T.unop.left}
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow) (Ī : B.Arrow) (_hĪ : Ī.f = I.f.left) :
    let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
    let αI :=
      ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.map I.f.op α)
    let pulledφ :
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x) ⟶
          (L.f ^*[canonicalPullbackChoice 𝒮.p] y) :=
      ((canonicalPullbackChoice 𝒮.p).pullbackFunctor L.f).map φ
    ((((((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
          ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ).hom)).1.app
        (op (Over.mk qI))))
      ((((((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.map
            ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
                (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom)).1.app
          (op (Over.mk (𝟙 I.Y.left))))
        αI)) =
      ((((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_common_owner_isomorphism
              (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
              (by simp [qI])).hom).hom) ≫
          (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (((canonicalPullbackChoice 𝒮.p).pullbackFunctor qI).map pulledφ)).hom).1.app
        (op (Over.mk (𝟙 I.Y.left))))
      αI := by
  -- Route correction: the earlier owner transport and pulled-conjugation rewrites are now
  -- packaged by `chosen_local_source_common_owner_boundary_shell_app`, so only the final boundary
  -- cancellation from that explicit shell to the direct common-owner/pulled-`φ` composite remains.
  rw [chosen_local_source_common_owner_boundary_shell_app
    (𝒮 := 𝒮) hGerbe hAbelian φ L K T α I Ī _hĪ]
  -- The remaining shell is the dedicated app-level cancellation isolated immediately above.
  exact
    chosen_local_source_common_owner_boundary_cancel_app
      (𝒮 := 𝒮) hGerbe hAbelian φ L K T α I

/-- Helper for Lemma 8.11.8: on one refinement member of the pulled chosen local `y`-cover, the
restricted left branch can be rewritten all the way to the shared-owner `qI := I.Y.hom ≫ K.f`
shell for the source chosen local cover arrow `K`, followed by the pulled morphism on that same
owner. This isolates the last source-side transport before the cross-cover common-owner
comparison is applied. -/
private theorem chosen_local_source_refinement_member_qI_shell_app
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y)
    (L : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (K :
      (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).Arrow)
    (T : (Over K.Y)ᵒᵖ)
    (α :
      ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.obj T))
    {B : J.Cover T.unop.left}
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow) (Ī : B.Arrow) (_hĪ : Ī.f = I.f.left) :
    let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
    let αI :=
      ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.map I.f.op α)
    let pulledφ :
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x) ⟶
          (L.f ^*[canonicalPullbackChoice 𝒮.p] y) :=
      ((canonicalPullbackChoice 𝒮.p).pullbackFunctor L.f).map φ
    ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (L.f ^*[canonicalPullbackChoice 𝒮.p] y))).1.map I.f.op
        ((((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
              (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom) ≫
          ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
            (((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
              ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ).hom))).1.app T) α) =
      ((((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_common_owner_isomorphism
              (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
              (by simp [qI])).hom).hom) ≫
          (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (((canonicalPullbackChoice 𝒮.p).pullbackFunctor qI).map pulledφ)).hom).1.app
        (op (Over.mk (𝟙 I.Y.left))))
      αI) := by
  -- Route correction: the outer restriction shell is now factored out into
  -- `chosen_local_source_refinement_member_restrict_eq`. The remaining blocker is exactly the
  -- owner-transport step from `op I.Y` to `op (Over.mk (𝟙 I.Y.left))`, together with the
  -- `mapComp'` normalization around the pulled `φ` factor.
  have hRestrict :=
    chosen_local_source_refinement_member_restrict_eq
      (𝒮 := 𝒮) hGerbe hAbelian φ L K T α I Ī _hĪ
  have hOwnerTransport :=
    chosen_local_source_refinement_member_owner_transport_app
      (𝒮 := 𝒮) hGerbe hAbelian φ L K T α I Ī _hĪ
  have hTransportedSection :=
    chosen_local_source_refinement_member_transported_section_eq_mapped_app
      (𝒮 := 𝒮) hGerbe hAbelian φ L K T α I Ī _hĪ
  let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
  let αI :=
    ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.map I.f.op α)
  let pulledφ :
      (L.f ^*[canonicalPullbackChoice 𝒮.p] x) ⟶
        (L.f ^*[canonicalPullbackChoice 𝒮.p] y) :=
    ((canonicalPullbackChoice 𝒮.p).pullbackFunctor L.f).map φ
  -- First expose the outer restriction and owner transport on the source branch.
  rw [hRestrict]
  rw [hOwnerTransport]
  -- Replace the transported source section by the literal `I.Y.hom`-pulled chosen-local
  -- conjugation component on the common owner `op (Over.mk (𝟙 I.Y.left))`.
  rw [hTransportedSection]
  -- The remaining source-faithful mismatch is now isolated in a dedicated app-level helper.
  simpa [qI, αI, pulledφ] using
    chosen_local_source_common_owner_middle_with_pulled_phi_app
      (𝒮 := 𝒮) hGerbe hAbelian φ L K T α I Ī _hĪ

/-- Helper for Lemma 8.11.8: on one refinement member of the pulled chosen local `y`-cover, the
two candidate sections from `chosen_local_automorphism_iso_pulled_conj_component_app` are both
rewritten to the same common-owner conjugation over `qI := I.Y.hom ≫ K.f`. -/
private theorem chosen_local_automorphism_iso_pulled_conj_refinement_member_eq
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y)
    (L : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (K :
      (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).Arrow)
    (T : (Over K.Y)ᵒᵖ)
    (α :
      ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.obj T))
    {B : J.Cover T.unop.left}
    {R : (J.over K.Y).Cover T.unop}
    (hR : (R : Sieve T.unop) = (Sieve.overEquiv T.unop).symm (B : Sieve T.unop.left))
    (I : R.Arrow) (Ī : B.Arrow) (hĪ : Ī.f = I.f.left) :
    ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (L.f ^*[canonicalPullbackChoice 𝒮.p] y))).1.map I.f.op
        ((((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
              (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom) ≫
          ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
            (((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
              ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ).hom))).1.app T) α) =
      ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (L.f ^*[canonicalPullbackChoice 𝒮.p] y))).1.map I.f.op
          ((((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
              ((chosen_local_automorphism_iso
                (𝒮 := 𝒮) hGerbe hAbelian
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
                (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom)).1.app T) α)) := by
  let qT := T.unop.hom ≫ K.f
  let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
  let Ky :
      (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).Arrow :=
    Ī.base
  have hgx : I.Y.hom ≫ K.f = qI := by
    rfl
  have hgy : 𝟙 I.Y.left ≫ Ky.f = qI := by
    -- Reuse the isolated owner-arrow witness for the target refinement member.
    simpa [qI, Ky] using
      chosen_local_target_refinement_member_identity_leg_eq
        (𝒮 := 𝒮) hGerbe L K T I Ī hĪ
  let αI :=
    ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.map I.f.op α)
  -- Route correction: the source proof fixes one refinement member first. The remaining work is
  -- to rewrite both restricted branches to the same owner `qI` and then apply the cross-cover
  -- common-owner conjugation equality.
  have hRightRestrict :=
    chosen_local_target_refinement_member_right_branch_restrict_eq
      (𝒮 := 𝒮) hGerbe hAbelian φ L K T α I Ī hĪ
  have hRightImage :=
    chosen_local_target_refinement_member_right_branch_image_app
      (𝒮 := 𝒮) hGerbe hAbelian φ L K T α I Ī hĪ
  have hRightOwnerTransport :=
    chosen_local_target_refinement_member_right_branch_common_owner_app
      (𝒮 := 𝒮) hGerbe hAbelian φ L K T α I Ī hĪ
  have hRightQIShell :=
    chosen_local_target_refinement_member_descent_component_qI_shell_app
      (𝒮 := 𝒮) hGerbe hAbelian φ L K T α I Ī hĪ
  have hLeftQIShell :=
    chosen_local_source_refinement_member_qI_shell_app
      (𝒮 := 𝒮) hGerbe hAbelian φ L K T α I Ī hĪ
  let pulledφ :
      (L.f ^*[canonicalPullbackChoice 𝒮.p] x) ⟶
        (L.f ^*[canonicalPullbackChoice 𝒮.p] y) :=
    ((canonicalPullbackChoice 𝒮.p).pullbackFunctor L.f).map φ
  -- Route correction: both branches are now explicit apps of the common-owner shells over `qI`,
  -- so one pointwise cross-cover comparison finishes the refinement-member equality.
  calc
    ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (L.f ^*[canonicalPullbackChoice 𝒮.p] y))).1.map I.f.op
        ((((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
              (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom) ≫
          ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
            (((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
              ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ).hom))).1.app T) α)
        =
      ((((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_common_owner_isomorphism
              (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom) hgx).hom).hom) ≫
          (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (((canonicalPullbackChoice 𝒮.p).pullbackFunctor qI).map pulledφ)).hom).1.app
        (op (Over.mk (𝟙 I.Y.left))))
      αI := by
        simpa [qI, αI, pulledφ] using hLeftQIShell
    _ =
      ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe qI (K := Ky) (g := 𝟙 I.Y.left) hgy).hom).hom).1.app
        (op (Over.mk (𝟙 I.Y.left))))
      αI := by
        simpa [pulledφ, qI] using
          chosen_local_cross_cover_common_owner_conjugation_hom_eq_app
            (𝒮 := 𝒮) hGerbe hAbelian pulledφ qI
            (Kx := K) (Ky := Ky) (gx := I.Y.hom) (gy := 𝟙 I.Y.left)
            hgx hgy (op (Over.mk (𝟙 I.Y.left))) αI
    _ =
      ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (L.f ^*[canonicalPullbackChoice 𝒮.p] y))).1.map I.f.op
          ((((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
              ((chosen_local_automorphism_iso
                (𝒮 := 𝒮) hGerbe hAbelian
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
                (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom)).1.app T) α)) := by
        rw [hRightRestrict]
        rw [← hRightOwnerTransport]
        rw [hRightImage]
        exact hRightQIShell.symm

/-- Helper for Lemma 8.11.8: after transporting the pulled-conjugation comparison through the
chosen local cover descent equivalence for `(A, L.f ^* x)`, the remaining blocker is a
componentwise section equality on one fixed chosen-local cover arrow `K`. -/
private theorem chosen_local_automorphism_iso_pulled_conj_component_app
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y)
    (L : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (K :
      (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).Arrow) :
    (((localizedSheafToCoverDescentEquivalence (J := J)
        (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
          (L.f ^*[canonicalPullbackChoice 𝒮.p] x))).functor.map
      ((chosen_local_automorphism_iso
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
          (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).hom ≫
        ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
          ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ).hom))).hom K =
    (((localizedSheafToCoverDescentEquivalence (J := J)
          (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x))).functor.map
        ((chosen_local_automorphism_iso
            (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
            (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom)).hom K := by
  let A := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L
  let xL := L.f ^*[canonicalPullbackChoice 𝒮.p] x
  let yL := L.f ^*[canonicalPullbackChoice 𝒮.p] y
  let Sx := chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe A xL
  -- Route correction: follow the source proof literally. First expose the `K`-component on the
  -- chosen local `x`-cover, then prove equality of the resulting sections after restricting to the
  -- pulled chosen local `y`-cover over each `T`.
  rw [Functor.map_comp]
  rw [localizedSheafToCoverDescentEquivalence_functor_map_component (J := J)
    Sx
    ((chosen_local_automorphism_iso
      (𝒮 := 𝒮) hGerbe hAbelian A xL).hom) K]
  rw [localizedSheafToCoverDescentEquivalence_functor_map_component (J := J)
    Sx
    (((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
      ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ).hom)) K]
  rw [localizedSheafToCoverDescentEquivalence_functor_map_component (J := J)
    Sx
    ((chosen_local_automorphism_iso
      (𝒮 := 𝒮) hGerbe hAbelian A yL).hom) K]
  rw [chosen_local_automorphism_iso_functor_map_component
    (𝒮 := 𝒮) hGerbe hAbelian (x := A) (z := xL) K]
  simpa [chosen_local_automorphism_descent_iso] using by
    apply Sheaf.hom_ext
    intro T
    funext α
    obtain ⟨B, R, hR⟩ :=
      chosen_local_target_cover_on_slice
        (𝒮 := 𝒮) hGerbe (x := x) (y := y) L K T
    -- Equality on the pulled chosen local `y`-cover forces equality of the two sections on `T`.
    refine sections_eq_of_cover_on_slice (J := J) _ T.unop R _ _ ?_
    intro I
    obtain ⟨Ī, hĪ⟩ :=
      chosen_cover_overlap_common_refinement_base_arrow (J := J) (T := T.unop) hR I
    -- The componentwise source-faithful comparison is now isolated in the refinement-member lemma.
    exact
      chosen_local_automorphism_iso_pulled_conj_refinement_member_eq
        (𝒮 := 𝒮) hGerbe hAbelian φ L K T α
        (B := B) (R := R) hR I Ī hĪ

/-- Helper for Lemma 8.11.8: on the slice `C / L.Y`, the chosen local comparison to `L.f ^* x`
followed by the pullback of conjugation by `φ` is the chosen local comparison to `L.f ^* y`.
This isolates the exact owner-level pulled-conjugation blocker exposed after the outer
identity-pullback shell is cancelled. -/
theorem chosen_local_automorphism_iso_pulled_conj
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y)
    (L : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow) :
    (chosen_local_automorphism_iso
      (𝒮 := 𝒮) hGerbe hAbelian
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
      (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).hom ≫
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ).hom) =
    (chosen_local_automorphism_iso
      (𝒮 := 𝒮) hGerbe hAbelian
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
      (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom := by
  let S :=
    chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
      (L.f ^*[canonicalPullbackChoice 𝒮.p] x)
  let E := localizedSheafToCoverDescentEquivalence (J := J) S
  -- Route correction: first pass to the chosen-local descent datum for `(A, L.f ^* x)`. The
  -- remaining source-faithful blocker is then checked componentwise on that cover.
  apply Functor.map_injective E.functor
  apply Pseudofunctor.DescentData.hom_ext
  intro K
  -- Evaluate both transported morphisms on the fixed chosen-local component `K`.
  simpa [S, E] using
    chosen_local_automorphism_iso_pulled_conj_component_app
      (𝒮 := 𝒮) hGerbe hAbelian φ L K

end CategoryTheory
