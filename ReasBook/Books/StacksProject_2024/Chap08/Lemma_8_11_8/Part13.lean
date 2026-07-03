import Mathlib
import Mathlib.CategoryTheory.Sites.Over
import StacksProject_2024.Chap07.Lemma_7_26_5
import StacksProject_2024.Chap07.Lemma_7_26_6
import StacksProject_2024.Chap08.Lemma_8_3_7
import StacksProject_2024.Chap08.Definition_8_5_5
import StacksProject_2024.Chap08.Definition_8_11_1
import StacksProject_2024.Chap08.Lemma_8_11_8.Part12

universe u v w

namespace CategoryTheory

open StackInGroupoidsOver
open Opposite
open Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {𝒮 : StackInGroupoidsOver J}
/-- Helper for Lemma 8.11.8: on one refinement member of the pulled chosen local `y`-cover, the
restricted left branch can be rewritten all the way to the shared-owner `qI := I.Y.hom ≫ K.f`
shell for the source chosen local cover arrow `K`, followed by the pulled morphism on that same
owner. This isolates the last source-side transport before the cross-cover common-owner
comparison is applied. -/
theorem chosen_local_source_common_owner_left_flank_mapComp_app
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
      αI) := by
  -- Expose the source-side common-owner inverse comparison as the raw `mapComp'` boundary.
  rw [chosen_local_source_mapComp'_inv_eq_common_owner_source_iso_inv
    (𝒮 := 𝒮) hGerbe hAbelian (I.Y.hom ≫ K.f) I.Y.hom (by simp)]

/-- Helper for Lemma 8.11.8: once the middle common-owner conjugation reaches the target-side raw
boundary shell, the remaining tail is exactly the previously isolated pulled-`φ` collapse on the
owner `qI := I.Y.hom ≫ K.f`. -/
theorem chosen_local_source_common_owner_pulled_phi_tail_app
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
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x))) ≫
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
  -- Collapse the target-side raw boundary shell first; the middle common-owner conjugation is
  -- just a prefix that passes unchanged through this evaluation.
  simpa [Category.assoc] using
    congrFun
      (congrArg
        (fun ψ ↦
          (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              (chosen_local_common_owner_isomorphism
                (𝒮 := 𝒮) hGerbe (I.Y.hom ≫ K.f) (K := K) (g := I.Y.hom)
                (by simp)).hom).hom) ≫ ψ).1.app
            (op (Over.mk (𝟙 I.Y.left)))))
        (chosen_local_source_pulled_phi_mapComp_qI_shell
          (𝒮 := 𝒮) hGerbe hAbelian φ L K I))
      ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.map I.f.op α)

/-- Helper for Lemma 8.11.8: on an arbitrary owner leg `S : Over I.Y.left`, the explicit raw
source/common-owner/target shell is already the pulled chosen-local conjugation along
`I.Y.hom`. This clears the solved boundary identifications first, leaving only the owner-leg
transport from the pulled conjugation back to the common-owner component. -/
theorem chosen_local_common_owner_middle_as_pulled_conjugation_app
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
      ((((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.map
          ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
              (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom)).1.app S)
        β) := by
  let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
  -- First rewrite the source-side raw boundary to the common-owner source comparison.
  rw [chosen_local_source_mapComp'_inv_eq_common_owner_source_iso_inv
    (𝒮 := 𝒮) hGerbe hAbelian qI I.Y.hom (by simp [qI])]
  -- Then collapse the three explicit conjugation factors to the pulled chosen-local conjugation.
  simpa [qI, Category.assoc] using
    congrFun
      (congrArg
        (fun ψ ↦ (ψ.1.app S))
        (chosen_local_pulled_conjugation_eq_common_owner_middle
          (𝒮 := 𝒮) hGerbe hAbelian qI (K := K) (g := I.Y.hom)
          (by simp [qI])))
      β

/-- Helper for Lemma 8.11.8: before evaluating on the literal owner
`op (Over.mk (𝟙 I.Y.left))`, commute the remaining raw source-side `mapComp'` inverse boundary
through the common-owner middle shell after specializing to an arbitrary owner leg
`S : Over I.Y.left`. This isolates the exact owner-generic naturality rewrite that is still
missing. -/
private theorem automorphism_underlying_sheaf_pull_hom_eq_restrict
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} {x : 𝒮.p.Fiber U} {S : (Over U)ᵒᵖ}
    (β : (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x).1.obj S) :
    pullHom β S.unop.hom (𝟙 U) (𝟙 U) (by simp) (by simp) =
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x).1.map
        (Over.homMk S.unop.hom (by simp)).op β := by
  -- Restriction in the automorphism Hom-sheaf is definitionally the owner-side `pullHom`.
  cases S
  rfl

/-- Helper for Lemma 8.11.8: before evaluating on the literal owner
`op (Over.mk (𝟙 I.Y.left))`, commute the remaining raw source-side `mapComp'` inverse boundary
through the common-owner middle shell after specializing to an arbitrary owner leg
`S : Over I.Y.left`. This isolates the exact owner-generic naturality rewrite that is still
missing. -/
private theorem chosen_local_common_owner_middle_owner_leg_naturality_app
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
    (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
            (by simp [qI])).hom).hom).1.app
        (op (Over.mk (𝟙 I.Y.left))))
      (pullHom β S.unop.hom (𝟙 I.Y.left) (𝟙 I.Y.left)
        (by simp) (by simp)) =
      pullHom
        ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              (chosen_local_common_owner_isomorphism
                (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
                (by simp [qI])).hom).hom).1.app S)
          β)
        S.unop.hom (𝟙 I.Y.left) (𝟙 I.Y.left)
        (by simp) (by simp) := by
  let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
  let ownerLeg : Over.mk (𝟙 I.Y.left) ⟶ S.unop := Over.homMk S.unop.hom (by simp)
  -- Specialize the generic pullback naturality of conjugation to the owner leg
  -- `S.unop.hom : S.unop.left ⟶ I.Y.left`.
  simpa [qI, ownerLeg] using
    (automorphismUnderlyingSheafConj_pull_naturality
      (𝒮 := 𝒮) hAbelian
      (chosen_local_common_owner_isomorphism
        (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
        (by simp [qI]))
      ownerLeg.op β)

/-- Helper for Lemma 8.11.8: after introducing the true owner
`qS := S.unop.hom ≫ (I.Y.hom ≫ K.f)`, evaluating the `qS` common-owner shell on the literal
identity owner of `S.unop.left` is exactly the pullback of the fixed `qI` common-owner shell
along `S.unop.hom`. This exposes the owner-change comparison before the remaining naturality
rewrite back to the `S`-component. -/
theorem chosen_local_owner_leg_qS_common_owner_shell_eq_pullback_qI_app
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
    (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe qS (K := K) (g := S.unop.hom ≫ I.Y.hom)
            (by simp [qI, qS, Category.assoc])).hom).hom).1.app
        (op (Over.mk (𝟙 S.unop.left))))
      (pullHom β S.unop.hom (𝟙 I.Y.left) (𝟙 I.Y.left)
        (by simp) (by simp)) =
      ((((((J.pseudofunctorOver (Type (max u v))).map S.unop.hom.op.toLoc).toFunctor.map
            ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              (chosen_local_common_owner_isomorphism
                (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
                (by simp [qI])).hom).hom)).1.app
          (op (Over.mk (𝟙 S.unop.left)))))
        (pullHom β S.unop.hom (𝟙 I.Y.left) (𝟙 I.Y.left)
          (by simp) (by simp)) := by
  let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
  let qS : S.unop.left ⟶ L.Y := S.unop.hom ≫ qI
  -- Evaluate the sheaf-level owner-change equality on the literal identity owner of
  -- `S.unop.left`.
  simpa [qI, qS] using
    congrFun
      (congrArg
        (fun ψ ↦ (ψ.1.app (op (Over.mk (𝟙 S.unop.left)))))
        (chosen_local_common_owner_conjugation_pullback_eq_owner_leg
          (𝒮 := 𝒮) hGerbe hAbelian qI I.Y.hom (by simp [qI]) S.unop.hom))
      (pullHom β S.unop.hom (𝟙 I.Y.left) (𝟙 I.Y.left)
        (by simp) (by simp))

/-- Helper for Lemma 8.11.8: before evaluating on the literal owner
`op (Over.mk (𝟙 I.Y.left))`, commute the remaining raw source-side `mapComp'` inverse boundary
through the common-owner middle shell after specializing to an arbitrary owner leg
`S : Over I.Y.left`. This isolates the exact owner-generic naturality rewrite that is still
missing. -/
private theorem chosen_local_owner_leg_transported_pulled_conjugation_eq_owner_component_app
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
    ((((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.map
        ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom)).1.app S)
      β =
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
          β)) := by
  -- Expose the composite owner hidden by the `I.Y.hom` pullback before any common-owner
  -- normalization is applied.
  simpa using
    (pseudofunctor_over_map_app_eq_owner_transport
      (J := J) (g := I.Y.hom)
      (φ := (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
          (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom)
      (k := S.unop.hom) (h := S.unop.hom ≫ I.Y.hom) (hk := rfl)
      (s := β))

/-- Helper for Lemma 8.11.8: the explicit owner-component cast of `β` along `I.Y.hom`
coincides with first restricting to the literal owner `op (Over.mk (𝟙 S.unop.left)))` in the
pulled `qI`-automorphism sheaf and then applying the tautological composite-owner cast. This is
the exact source-boundary input normalization needed before the `qS` shell cancellations. -/
theorem chosen_local_owner_leg_source_boundary_input_eq_pullHom_app
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
    Eq.mp
      (congrArg
        ((automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).1.obj)
        (over_map_obj_mk_eq_op I.Y.hom S.unop.hom (S.unop.hom ≫ I.Y.hom) rfl))
      β =
    Eq.mp
      (congrArg
        ((automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).1.obj)
        (over_map_obj_mk_eq_op (S.unop.hom ≫ I.Y.hom) (𝟙 S.unop.left)
          (S.unop.hom ≫ I.Y.hom) (by simp)))
      (pullHom β S.unop.hom (𝟙 I.Y.left) (𝟙 I.Y.left)
        (by simp) (by simp)) := by
  let βS :=
    pullHom β S.unop.hom (𝟙 I.Y.left) (𝟙 I.Y.left) (by simp) (by simp)
  have hβrestrict :
      βS =
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          ((I.Y.hom ≫ K.f) ^*[canonicalPullbackChoice 𝒮.p]
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.map
          (Over.homMk S.unop.hom (by simp)).op β := by
    -- The literal owner-leg section is just restriction in the pulled automorphism sheaf.
    simpa [βS] using
      automorphism_underlying_sheaf_pull_hom_eq_restrict
        (𝒮 := 𝒮) hAbelian
        (x := ((I.Y.hom ≫ K.f) ^*[canonicalPullbackChoice 𝒮.p]
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)))
        (S := S) β
  -- Normalize both transports to explicit presheaf maps on the fixed owner sheaf.
  rw [over_map_obj_mk_section_cast_eq_map]
  rw [over_map_obj_mk_section_cast_eq_map]
  -- After replacing `pullHom` by the corresponding restriction map, both sides are literally
  -- the same owner morphism in the source sheaf.
  rw [hβrestrict]
  cases S
  rfl

/-- Helper for Lemma 8.11.8: the literal-owner evaluation of the pulled chosen-local
conjugation along `S.unop.hom ≫ I.Y.hom` is just the actual `S`-component of the same pulled
conjugation after normalizing the owner-input cast with `pullHom`. This isolates the left-hand
transport step of the fixed-owner corridor from the later common-owner comparison. -/
private theorem chosen_local_qS_pulled_conjugation_eq_owner_component_app
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
    let βS :=
      pullHom β S.unop.hom (𝟙 I.Y.left) (𝟙 I.Y.left) (by simp) (by simp)
    ((((J.pseudofunctorOver (Type (max u v))).map
          (S.unop.hom ≫ I.Y.hom).op.toLoc).toFunctor.map
        ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom)).1.app
        (op (Over.mk (𝟙 S.unop.left))))
      βS =
      ((((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.map
          ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
              (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom)).1.app S)
        β) := by
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
    -- Move the literal-owner component back to the composite owner hidden by the pullback.
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
    -- Normalize the explicit owner-input cast by first restricting to the literal owner.
    simpa [βS] using
      chosen_local_owner_leg_source_boundary_input_eq_pullHom_app
        (𝒮 := 𝒮) hGerbe hAbelian L K I β
  have hcomponent :
      ((((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.map
          ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
              (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom)).1.app S)
        β =
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
    -- The owner-generic transport theorem now lands on the same literal input.
    rw [← hβinput]
    simpa using
      chosen_local_owner_leg_transported_pulled_conjugation_eq_owner_component_app
        (𝒮 := 𝒮) hGerbe hAbelian L K I β
  -- Both presentations are the same once the owner object and the input cast are aligned.
  exact howner_transport.trans hcomponent.symm

/-- Helper for Lemma 8.11.8: after specializing to the literal owner
`op (Over.mk (𝟙 S.unop.left)))`, the explicit `qS` source/common-owner/target shell should
collapse to the pure common-owner component. Packaging this as its own app-level lemma keeps the
owner-leg corridor from reopening the same boundary-cancellation fight. -/
private theorem chosen_local_qS_common_owner_shell_eq_pulled_conjugation_app
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
    ((((J.pseudofunctorOver (Type (max u v))).map
          (S.unop.hom ≫ I.Y.hom).op.toLoc).toFunctor.map
        ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom)).1.app
        (op (Over.mk (𝟙 S.unop.left))))
      βS =
      (((((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              (chosen_local_common_owner_source_iso
                (𝒮 := 𝒮) hGerbe qS (g := S.unop.hom ≫ I.Y.hom)
                (by simp [qI, qS, Category.assoc])).inv.hom).hom) ≫
            (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              (chosen_local_common_owner_isomorphism
                (𝒮 := 𝒮) hGerbe qS (K := K) (g := S.unop.hom ≫ I.Y.hom)
                (by simp [qI, qS, Category.assoc])).hom).hom ≫
            (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              (chosen_local_common_owner_target_iso
                (𝒮 := 𝒮) hGerbe qS (K := K) (g := S.unop.hom ≫ I.Y.hom)
                (by simp [qI, qS, Category.assoc])).hom).hom).1.app
          (op (Over.mk (𝟙 S.unop.left)))))
        βS) := by
  let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
  let qS : S.unop.left ⟶ L.Y := S.unop.hom ≫ qI
  let βS :=
    pullHom β S.unop.hom (𝟙 I.Y.left) (𝟙 I.Y.left) (by simp) (by simp)
  -- Evaluate the already-normalized common-owner factorization of the pulled chosen-local
  -- conjugation on the literal owner of `S.unop.left`.
  simpa [qI, qS, βS, Category.assoc] using
    congrFun
      (congrArg
        (fun ψ ↦ (ψ.1.app (op (Over.mk (𝟙 S.unop.left)))))
        (chosen_local_pulled_conjugation_eq_common_owner_middle
          (𝒮 := 𝒮) hGerbe hAbelian qS (K := K)
          (g := S.unop.hom ≫ I.Y.hom)
          (by simp [qI, qS, Category.assoc])))
      βS

/-- Helper for Lemma 8.11.8: after specializing to the literal owner
`op (Over.mk (𝟙 S.unop.left)))`, the explicit `qS` source/common-owner/target shell should
first match the owner-leg pullback of the fixed `qI := I.Y.hom ≫ K.f` common-owner comparison.
This is the source-faithful pivot: compare everything against the fixed `qI` corridor before
collapsing back to the literal `qS` presentation. -/
theorem chosen_local_fixed_qI_component_normalized_app
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
  let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
  have hpulled :
      ((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.map
          ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
              (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom) =
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (((canonicalPullbackChoice 𝒮.p).pullbackFunctor I.Y.hom).mapIso
            (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
              (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K)).hom).hom := by
    -- Rewrite the pulled chosen-local conjugation as conjugation by the pulled local isomorphism.
    simpa [qI] using
      chosen_local_pulled_conjugation_eq_pulled_iso_conj
        (𝒮 := 𝒮) hGerbe hAbelian qI (K := K) (g := I.Y.hom) (by simp [qI])
  have hparallel :
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (((canonicalPullbackChoice 𝒮.p).pullbackFunctor I.Y.hom).mapIso
            (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
              (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K)).hom).hom =
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
            (by simp [qI])).hom).hom := by
    -- Route correction: once both comparisons live over the fixed owner `qI`, endpoint
    -- independence of conjugation identifies the two sheaf morphisms directly.
    exact congrArg Iso.hom <|
      automorphismUnderlyingSheafConj_eq_of_parallel (𝒮 := 𝒮) hAbelian
        ((((canonicalPullbackChoice 𝒮.p).pullbackFunctor I.Y.hom).mapIso
          (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K)).hom)
        ((chosen_local_common_owner_isomorphism
          (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
          (by simp [qI])).hom)
  -- Evaluate the fixed-owner equality on the actual `S`-component and the section `β`.
  calc
    ((((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.map
        ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom)).1.app S)
      β =
        ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              (((canonicalPullbackChoice 𝒮.p).pullbackFunctor I.Y.hom).mapIso
                (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
                  (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
                  (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K)).hom).hom).1.app S)
          β) := by
            simpa using congrFun (congrArg (fun ψ ↦ (ψ.1.app S)) hpulled) β
    _ =
        ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              (chosen_local_common_owner_isomorphism
                (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
                (by simp [qI])).hom).hom).1.app S)
          β) := by
            simpa [qI] using congrFun (congrArg (fun ψ ↦ (ψ.1.app S)) hparallel) β

/-- Helper for Lemma 8.11.8: after specializing to the literal owner
`op (Over.mk (𝟙 S.unop.left)))`, the explicit `qS` source/common-owner/target shell should
first match the owner-leg pullback of the fixed `qI := I.Y.hom ≫ K.f` common-owner comparison.
This is the source-faithful pivot: compare everything against the fixed `qI` corridor before
collapsing back to the literal `qS` presentation. -/
private theorem chosen_local_qS_pulled_conjugation_eq_pullback_qI_common_owner_component_app
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
    let βS :=
      pullHom β S.unop.hom (𝟙 I.Y.left) (𝟙 I.Y.left) (by simp) (by simp)
    ((((J.pseudofunctorOver (Type (max u v))).map
          (S.unop.hom ≫ I.Y.hom).op.toLoc).toFunctor.map
        ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom)).1.app
        (op (Over.mk (𝟙 S.unop.left))))
      βS =
      ((((((J.pseudofunctorOver (Type (max u v))).map S.unop.hom.op.toLoc).toFunctor.map
            ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              (chosen_local_common_owner_isomorphism
                (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
                (by simp [qI])).hom).hom)).1.app
          (op (Over.mk (𝟙 S.unop.left)))))
        βS) := by
  let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
  let βS :=
    pullHom β S.unop.hom (𝟙 I.Y.left) (𝟙 I.Y.left) (by simp) (by simp)
  -- Route correction: the left-hand owner transport is now isolated. The only remaining work is
  -- the fixed `qI` corridor normalization from the actual `S`-component of the pulled
  -- chosen-local conjugation to the owner-leg pullback of the fixed `qI` common-owner
  -- comparison.
  calc
    ((((J.pseudofunctorOver (Type (max u v))).map
          (S.unop.hom ≫ I.Y.hom).op.toLoc).toFunctor.map
        ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom)).1.app
        (op (Over.mk (𝟙 S.unop.left))))
      βS =
        ((((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.map
            ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
                (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom)).1.app S)
          β) := by
            simpa [βS] using
              chosen_local_qS_pulled_conjugation_eq_owner_component_app
                (𝒮 := 𝒮) hGerbe hAbelian L K I β
    _ =
        ((((((J.pseudofunctorOver (Type (max u v))).map S.unop.hom.op.toLoc).toFunctor.map
              ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
                (chosen_local_common_owner_isomorphism
                  (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
                  (by simp [qI])).hom).hom)).1.app
            (op (Over.mk (𝟙 S.unop.left)))))
          βS) := by
            -- Normalize first on the actual `S`-component over the fixed owner `qI`, then
            -- retransport once to the literal owner leg.
            calc
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
                      simpa [qI] using
                        chosen_local_fixed_qI_component_normalized_app
                          (𝒮 := 𝒮) hGerbe hAbelian L K I β
              _ =
                  ((((((J.pseudofunctorOver (Type (max u v))).map S.unop.hom.op.toLoc).toFunctor.map
                        ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
                          (chosen_local_common_owner_isomorphism
                            (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
                            (by simp [qI])).hom).hom)).1.app
                      (op (Over.mk (𝟙 S.unop.left)))))
                    βS) := by
                      symm
                      simpa [qI, βS] using
                        (pseudofunctor_over_map_app_eq_owner_transport
                          (J := J) (g := S.unop.hom)
                          (φ := (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
                            (chosen_local_common_owner_isomorphism
                              (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
                              (by simp [qI])).hom).hom)
                          (k := 𝟙 S.unop.left) (h := S.unop.hom) (hk := by simp)
                          (s := βS))

/-- Helper for Lemma 8.11.8: after specializing to the literal owner
`op (Over.mk (𝟙 S.unop.left)))`, the explicit `qS` source/common-owner/target shell should
collapse to the pure common-owner component. Packaging this as its own app-level lemma keeps the
owner-leg corridor from reopening the same boundary-cancellation fight. -/
theorem chosen_local_qS_pulled_conjugation_eq_common_owner_component_app
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
    ((((J.pseudofunctorOver (Type (max u v))).map
          (S.unop.hom ≫ I.Y.hom).op.toLoc).toFunctor.map
        ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom)).1.app
        (op (Over.mk (𝟙 S.unop.left))))
      βS =
      ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_common_owner_isomorphism
              (𝒮 := 𝒮) hGerbe qS (K := K) (g := S.unop.hom ≫ I.Y.hom)
              (by simp [qI, qS, Category.assoc])).hom).hom).1.app
          (op (Over.mk (𝟙 S.unop.left))))
        βS) := by
  let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
  let qS : S.unop.left ⟶ L.Y := S.unop.hom ≫ qI
  let βS :=
    pullHom β S.unop.hom (𝟙 I.Y.left) (𝟙 I.Y.left) (by simp) (by simp)
  -- Route correction: the literal `qS` comparison is now only an adapter. First compare the
  -- pulled chosen-local conjugation with the owner-leg pullback of the fixed `qI` comparison,
  -- then identify that pullback with the literal `qS` common-owner component.
  calc
    ((((J.pseudofunctorOver (Type (max u v))).map
          (S.unop.hom ≫ I.Y.hom).op.toLoc).toFunctor.map
        ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom)).1.app
        (op (Over.mk (𝟙 S.unop.left))))
      βS =
        ((((((J.pseudofunctorOver (Type (max u v))).map S.unop.hom.op.toLoc).toFunctor.map
              ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
                (chosen_local_common_owner_isomorphism
                  (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
                  (by simp [qI])).hom).hom)).1.app
            (op (Over.mk (𝟙 S.unop.left)))))
          βS) := by
            simpa [qI, βS] using
              chosen_local_qS_pulled_conjugation_eq_pullback_qI_common_owner_component_app
                (𝒮 := 𝒮) hGerbe hAbelian L K I β
    _ =
        ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              (chosen_local_common_owner_isomorphism
                (𝒮 := 𝒮) hGerbe qS (K := K) (g := S.unop.hom ≫ I.Y.hom)
                (by simp [qI, qS, Category.assoc])).hom).hom).1.app
            (op (Over.mk (𝟙 S.unop.left))))
          βS) := by
            simpa [qI, qS, βS] using
              (chosen_local_owner_leg_qS_common_owner_shell_eq_pullback_qI_app
                (𝒮 := 𝒮) hGerbe hAbelian L K I β).symm

/-- Helper for Lemma 8.11.8: after specializing to the literal owner
`op (Over.mk (𝟙 S.unop.left)))`, the explicit `qS` source/common-owner/target shell should
collapse to the pure common-owner component. Packaging this as its own app-level lemma keeps the
owner-leg corridor from reopening the same boundary-cancellation fight. -/
private theorem chosen_local_qS_boundary_shell_cancel_app
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
    (((((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              (chosen_local_common_owner_source_iso
                (𝒮 := 𝒮) hGerbe qS (g := S.unop.hom ≫ I.Y.hom)
                (by simp [qI, qS, Category.assoc])).inv.hom).hom) ≫
            (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              (chosen_local_common_owner_isomorphism
                (𝒮 := 𝒮) hGerbe qS (K := K) (g := S.unop.hom ≫ I.Y.hom)
                (by simp [qI, qS, Category.assoc])).hom).hom ≫
            (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              (chosen_local_common_owner_target_iso
                (𝒮 := 𝒮) hGerbe qS (K := K) (g := S.unop.hom ≫ I.Y.hom)
                (by simp [qI, qS, Category.assoc])).hom).hom).1.app
          (op (Over.mk (𝟙 S.unop.left)))))
        βS) =
      ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_common_owner_isomorphism
              (𝒮 := 𝒮) hGerbe qS (K := K) (g := S.unop.hom ≫ I.Y.hom)
              (by simp [qI, qS, Category.assoc])).hom).hom).1.app
          (op (Over.mk (𝟙 S.unop.left))))
        βS) := by
  let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
  let qS : S.unop.left ⟶ L.Y := S.unop.hom ≫ qI
  let βS :=
    pullHom β S.unop.hom (𝟙 I.Y.left) (𝟙 I.Y.left) (by simp) (by simp)
  -- This is now just the adapter from the explicit shell to the direct owner-leg comparison.
  calc
    (((((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              (chosen_local_common_owner_source_iso
                (𝒮 := 𝒮) hGerbe qS (g := S.unop.hom ≫ I.Y.hom)
                (by simp [qI, qS, Category.assoc])).inv.hom).hom) ≫
            (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              (chosen_local_common_owner_isomorphism
                (𝒮 := 𝒮) hGerbe qS (K := K) (g := S.unop.hom ≫ I.Y.hom)
                (by simp [qI, qS, Category.assoc])).hom).hom ≫
            (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              (chosen_local_common_owner_target_iso
                (𝒮 := 𝒮) hGerbe qS (K := K) (g := S.unop.hom ≫ I.Y.hom)
                (by simp [qI, qS, Category.assoc])).hom).hom).1.app
          (op (Over.mk (𝟙 S.unop.left)))))
      βS =
      ((((J.pseudofunctorOver (Type (max u v))).map
            (S.unop.hom ≫ I.Y.hom).op.toLoc).toFunctor.map
          ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
              (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom)).1.app
          (op (Over.mk (𝟙 S.unop.left))))
        βS := by
          simpa [qI, qS, βS] using
            (chosen_local_qS_common_owner_shell_eq_pulled_conjugation_app
              (𝒮 := 𝒮) hGerbe hAbelian L K I β).symm
    _ =
      ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_common_owner_isomorphism
              (𝒮 := 𝒮) hGerbe qS (K := K) (g := S.unop.hom ≫ I.Y.hom)
              (by simp [qI, qS, Category.assoc])).hom).hom).1.app
          (op (Over.mk (𝟙 S.unop.left))))
        βS) := by
          simpa [qI, qS, βS] using
            chosen_local_qS_pulled_conjugation_eq_common_owner_component_app
              (𝒮 := 𝒮) hGerbe hAbelian L K I β

end CategoryTheory
