import Mathlib
import Mathlib.CategoryTheory.Sites.Over
import StacksProject_2024.Chap07.Lemma_7_26_4.Index
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

/-- Generic owner-input cast: for a `Type`-valued presheaf, transport of a section across an
object equality by `Eq.mp (congrArg F.obj h)` agrees with the `eqToHom`-presheaf restriction. -/
private theorem eqmp_eq_map_eqToHom {D : Type (max u v)} [Category.{v} D]
    (F : Dᵒᵖ ⥤ Type (max u v)) {A B : Dᵒᵖ} (h : A = B) (β : F.obj A) :
    Eq.mp (congrArg F.obj h) β = F.map (eqToHom h) β := by
  cases h; simp

section
set_option allowUnsafeReducibility true in
attribute [local irreducible] canonicalPullbackChoice

/-- Frontier for the source-side boundary in the chosen-local common-owner corridor: the inverse
source comparison is exactly the raw `mapComp'` inverse boundary after the iterated base-change
bridge. This is the reusable morphism-level form of the left-flank normalization below. -/
private theorem chosen_local_source_common_owner_left_flank_boundary_morphism
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} {x y : 𝒮.p.Fiber U} (_φ : x ⟶ y)
    (L : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (K :
      (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).Arrow)
    (T : (Over K.Y)ᵒᵖ)
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow) :
    let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
    let B1g :=
      ((((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))) ≪≫
        automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I.Y.hom
          (K.f ^*[canonicalPullbackChoice 𝒮.p]
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)))
    (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (chosen_local_common_owner_source_iso
          (𝒮 := 𝒮) hGerbe qI I.Y.hom (by simp [qI])).inv).hom =
      B1g.inv ≫
        (((J.pseudofunctorOver (Type (max u v))).mapComp'
            K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)).inv.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))) ≫
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).hom := by
  intro qI B1g
  have hsrc :=
    chosen_local_source_mapComp'_inv_eq_common_owner_source_iso_inv
      (𝒮 := 𝒮) hGerbe hAbelian qI (K := K) I.Y.hom (by simp [qI])
  have hsrcB :
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)).inv.toNatTrans.app
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))) =
        B1g.hom ≫
          (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_common_owner_source_iso
              (𝒮 := 𝒮) hGerbe qI I.Y.hom (by simp [qI])).inv).hom ≫
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).inv := by
    simpa [B1g] using hsrc
  erw [hsrcB]
  let Csrc :=
    (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
      (chosen_local_common_owner_source_iso
        (𝒮 := 𝒮) hGerbe qI I.Y.hom (by simp [qI])).inv).hom
  let Q :=
    automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
  change Csrc = B1g.inv ≫ (B1g.hom ≫ Csrc ≫ Q.inv) ≫ Q.hom
  have hcancel : B1g.inv ≫ (B1g.hom ≫ Csrc ≫ Q.inv) ≫ Q.hom = Csrc := by
    simp only [Category.assoc]
    rw [B1g.inv_hom_id_assoc]
    exact (Iso.eq_comp_inv Q).mp rfl
  exact hcancel.symm

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
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow) :
    let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
    let pulledφ :
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x) ⟶
          (L.f ^*[canonicalPullbackChoice 𝒮.p] y) :=
      ((canonicalPullbackChoice 𝒮.p).pullbackFunctor L.f).map φ
    let O : (Over I.Y.left)ᵒᵖ := op (Over.mk (𝟙 I.Y.left))
    -- Iterated-pullback base-change bridge for the source datum.
    let B1g :=
      ((((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))) ≪≫
        automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I.Y.hom
          (K.f ^*[canonicalPullbackChoice 𝒮.p]
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)))
    -- Shared common-owner / target / pulled-`φ` tail (forced base-change bridges woven in).
    let REST :=
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
            (by simp [qI])).hom).hom ≫
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_common_owner_target_iso
            (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
            (by simp [qI])).hom).hom ≫
        ((((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.mapIso
              (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
                (L.f ^*[canonicalPullbackChoice 𝒮.p] x)) ≪≫
            automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I.Y.hom
              (K.f ^*[canonicalPullbackChoice 𝒮.p]
                (L.f ^*[canonicalPullbackChoice 𝒮.p] x))).inv ≫
          (((J.pseudofunctorOver (Type (max u v))).mapComp'
              K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)).inv.toNatTrans.app
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
              (L.f ^*[canonicalPullbackChoice 𝒮.p] x)))) ≫
        ((J.pseudofunctorOver (Type (max u v))).map qI.op.toLoc).toFunctor.map
          ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian pulledφ).hom)
    ∀ s :
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (I.Y.hom ^*[canonicalPullbackChoice 𝒮.p]
            (K.f ^*[canonicalPullbackChoice 𝒮.p]
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)))).1.obj O,
    (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_common_owner_source_iso
              (𝒮 := 𝒮) hGerbe qI I.Y.hom (by simp [qI])).inv).hom ≫ REST).1.app O)
        s =
      (((((J.pseudofunctorOver (Type (max u v))).mapComp'
                K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)).inv.toNatTrans.app
              (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))) ≫
            (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).hom ≫ REST).1.app O)
          (B1g.inv.1.app O s) := by
  intro qI pulledφ O B1g REST s
  have h :=
    chosen_local_source_common_owner_left_flank_boundary_morphism
      (𝒮 := 𝒮) hGerbe hAbelian φ L K T I
  exact congrFun (congrArg (fun m => (m ≫ REST).1.app O) h) s

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
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow) :
    let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
    let pulledφ :
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x) ⟶
          (L.f ^*[canonicalPullbackChoice 𝒮.p] y) :=
      ((canonicalPullbackChoice 𝒮.p).pullbackFunctor L.f).map φ
    let O : (Over I.Y.left)ᵒᵖ := op (Over.mk (𝟙 I.Y.left))
    ∀ s :
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (qI ^*[canonicalPullbackChoice 𝒮.p]
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.obj O,
    ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
          (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom.1.app O)
        ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
                (chosen_local_common_owner_isomorphism
                  (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
                  (by simp [qI])).hom).hom ≫
              (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
                (chosen_local_common_owner_target_iso
                  (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
                  (by simp [qI])).hom).hom ≫
              ((((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.mapIso
                    (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
                      (L.f ^*[canonicalPullbackChoice 𝒮.p] x)) ≪≫
                  automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I.Y.hom
                    (K.f ^*[canonicalPullbackChoice 𝒮.p]
                      (L.f ^*[canonicalPullbackChoice 𝒮.p] x))).inv ≫
                (((J.pseudofunctorOver (Type (max u v))).mapComp'
                    K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)).inv.toNatTrans.app
                  (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
                    (L.f ^*[canonicalPullbackChoice 𝒮.p] x)))) ≫
              ((J.pseudofunctorOver (Type (max u v))).map qI.op.toLoc).toFunctor.map
                ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian pulledφ).hom)).1.app O)
          s) =
      (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              (chosen_local_common_owner_isomorphism
                (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
                (by simp [qI])).hom).hom ≫
            (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              (((canonicalPullbackChoice 𝒮.p).pullbackFunctor qI).map pulledφ)).hom).1.app O)
        s := by
  intro qI pulledφ O s
  exact congrFun
    (congrArg (fun m => m.1.app O)
      (chosen_local_source_pulled_phi_mapComp_qI_shell (𝒮 := 𝒮) hGerbe hAbelian φ L K I))
    ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (chosen_local_common_owner_isomorphism
          (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom) (by simp [qI])).hom).hom.1.app O s)

/-- Frontier for the fixed `qI` middle corridor: after the source `mapComp'` boundary and the
target common-owner boundary are exposed, the morphism is the pullback of the chosen-local
conjugation along `I.Y.hom`. -/
private theorem chosen_local_common_owner_middle_as_pulled_conjugation_morphism
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
    let inB :=
      ((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.mapIso
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))
    let outBridge :=
      automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I.Y.hom
        (K.f ^*[canonicalPullbackChoice 𝒮.p] (L.f ^*[canonicalPullbackChoice 𝒮.p] x))
    inB.inv ≫
        (((J.pseudofunctorOver (Type (max u v))).mapComp'
            K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)).inv.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))) ≫
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).hom ≫
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
            (by simp [qI])).hom).hom ≫
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_common_owner_target_iso
            (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
            (by simp [qI])).hom).hom ≫
        outBridge.inv =
      ((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.map
        ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom) := by
  intro qI inB outBridge
  let A₀ :=
    automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
  let Bq₀ :=
    automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
  let Biter :=
    automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I.Y.hom
      (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))
  let M :=
    (J.pseudofunctorOver (Type (max u v))).mapComp'
      K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)
  let source :=
    (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
      (chosen_local_common_owner_source_iso
        (𝒮 := 𝒮) hGerbe qI I.Y.hom (by simp [qI])).inv).hom
  let common :=
    (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
      (chosen_local_common_owner_isomorphism
        (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
        (by simp [qI])).hom).hom
  let target :=
    (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
      (chosen_local_common_owner_target_iso
        (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
        (by simp [qI])).hom).hom
  have hpulled :
      ((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.map
          ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
              (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom) =
        Biter.hom ≫ (source ≫ common ≫ target) ≫ outBridge.inv := by
    -- This is the Part06 common-owner factorization of the pulled chosen-local conjugation.
    simpa [Biter, source, common, target, outBridge] using
      (chosen_local_pulled_conjugation_eq_common_owner_middle
        (𝒮 := 𝒮) hGerbe hAbelian qI (K := K) I.Y.hom (by simp [qI]))
  have hsource :
      Biter.hom ≫ source = inB.inv ≫ M.inv.toNatTrans.app A₀ ≫ Bq₀.hom := by
    have hboundary :=
      chosen_local_source_common_owner_left_flank_boundary_morphism
        (𝒮 := 𝒮) hGerbe hAbelian (𝟙 x) L K (T := T) I
    -- The boundary lemma has the same source comparison with the combined iterated bridge
    -- `(inB ≪≫ Biter)⁻¹`; multiplying by `Biter.hom` leaves exactly `inB.inv`.
    have hboundary' :
        source = (inB ≪≫ Biter).inv ≫ M.inv.toNatTrans.app A₀ ≫ Bq₀.hom := by
      simpa [source, inB, Biter, M, A₀, Bq₀, qI] using hboundary
    rw [hboundary']
    simp only [Iso.trans_inv, Category.assoc]
    simpa only [Category.assoc, Category.id_comp] using
      congrArg (fun f => f ≫ inB.inv ≫ M.inv.toNatTrans.app A₀ ≫ Bq₀.hom)
        Biter.hom_inv_id
  -- Substitute the normalized source flank into the expanded common-owner corridor.
  change inB.inv ≫ M.inv.toNatTrans.app A₀ ≫ Bq₀.hom ≫ common ≫ target ≫
      outBridge.inv =
    ((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.map
      ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
          (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom)
  have hleft :
      inB.inv ≫ M.inv.toNatTrans.app A₀ ≫ Bq₀.hom ≫ common ≫ target ≫ outBridge.inv =
        Biter.hom ≫ source ≫ common ≫ target ≫ outBridge.inv := by
    simpa only [Category.assoc] using
      congrArg (fun m => m ≫ common ≫ target ≫ outBridge.inv) hsource.symm
  have hright :
      Biter.hom ≫ source ≫ common ≫ target ≫ outBridge.inv =
        ((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.map
          ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
              (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom) := by
    simpa only [Category.assoc] using hpulled.symm
  exact hleft.trans hright

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
    {S : (Over I.Y.left)ᵒᵖ} :
    let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
    -- Source datum lives in the iterated pulled sheaf; output lands in the iterated pullback.
    let inB :=
      ((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.mapIso
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))
    let outBridge :=
      automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I.Y.hom
        (K.f ^*[canonicalPullbackChoice 𝒮.p] (L.f ^*[canonicalPullbackChoice 𝒮.p] x))
    ∀ s :
        (((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (K.f ^*[canonicalPullbackChoice 𝒮.p]
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)))).1.obj S,
    (outBridge.inv.1.app S)
        (((((J.pseudofunctorOver (Type (max u v))).mapComp'
                  K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)).inv.toNatTrans.app
                (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
                  (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)) ≫
              (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).hom ≫
              (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
                (chosen_local_common_owner_isomorphism
                  (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
                  (by simp [qI])).hom).hom ≫
              (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
                (chosen_local_common_owner_target_iso
                  (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
                  (by simp [qI])).hom).hom).1.app S)
          ((inB.inv.1.app S) s)) =
      ((((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.map
          ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
              (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom)).1.app S)
          s := by
  intro qI inB outBridge s
  have h :=
    chosen_local_common_owner_middle_as_pulled_conjugation_morphism
      (𝒮 := 𝒮) hGerbe hAbelian L K (T := T) I
  exact congrFun (congrArg (fun m => m.1.app S) h) s



/-- Frontier for the qS/qI owner leg: pulling the fixed `qI` common-owner conjugation along the
owner arrow `S.unop.hom` and inserting the canonical base-change coherences gives the literal
`qS := S.unop.hom ≫ qI` common-owner conjugation. This is the fiber-level owner-change blocker
left after the source/target `mapComp'` boundaries have been normalized. -/
private theorem chosen_local_owner_leg_qS_common_owner_shell_eq_pullback_qI_morphism
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
    {S : (Over I.Y.left)ᵒᵖ} :
    let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
    let qS : S.unop.left ⟶ L.Y := S.unop.hom ≫ qI
    let cohIn :=
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qS
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).inv ≫
        (((J.pseudofunctorOver (Type (max u v))).mapComp'
            qI.op.toLoc S.unop.hom.op.toLoc qS.op.toLoc (by cat_disch)).hom.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))) ≫
        ((J.pseudofunctorOver (Type (max u v))).map S.unop.hom.op.toLoc).toFunctor.map
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).hom
    let cohOutInv :=
      ((J.pseudofunctorOver (Type (max u v))).map S.unop.hom.op.toLoc).toFunctor.map
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).inv ≫
        (((J.pseudofunctorOver (Type (max u v))).mapComp'
            qI.op.toLoc S.unop.hom.op.toLoc qS.op.toLoc (by cat_disch)).inv.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x))) ≫
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qS
          (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).hom
    (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (chosen_local_common_owner_isomorphism
          (𝒮 := 𝒮) hGerbe qS (K := K) (g := S.unop.hom ≫ I.Y.hom)
          (by simp [qI, qS, Category.assoc])).hom).hom =
      cohIn ≫
        ((J.pseudofunctorOver (Type (max u v))).map S.unop.hom.op.toLoc).toFunctor.map
          ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_common_owner_isomorphism
              (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
              (by simp [qI])).hom).hom) ≫
        cohOutInv := by
  intro qI qS cohIn cohOutInv
  let A₀ :=
    chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L
  let A₁ :=
    L.f ^*[canonicalPullbackChoice 𝒮.p] x
  let M :=
    (J.pseudofunctorOver (Type (max u v))).mapComp'
      qI.op.toLoc S.unop.hom.op.toLoc qS.op.toLoc (by cat_disch)
  let BqS₀ :=
    automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qS A₀
  let BqS₁ :=
    automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qS A₁
  let BqI₀ :=
    automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI A₀
  let BqI₁ :=
    automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI A₁
  let Bs₀ :=
    automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian S.unop.hom
      (qI ^*[canonicalPullbackChoice 𝒮.p] A₀)
  let Bs₁ :=
    automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian S.unop.hom
      (qI ^*[canonicalPullbackChoice 𝒮.p] A₁)
  let e₀ :=
    (canonicalPullbackChoice 𝒮.p).pullbackCompComponentIso qI S.unop.hom A₀
  let e₁ :=
    (canonicalPullbackChoice 𝒮.p).pullbackCompComponentIso qI S.unop.hom A₁
  let commonI :=
    chosen_local_common_owner_isomorphism
      (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom) (by simp [qI])
  let commonS :=
    chosen_local_common_owner_isomorphism
      (𝒮 := 𝒮) hGerbe qS (K := K) (g := S.unop.hom ≫ I.Y.hom)
      (by simp [qI, qS, Category.assoc])
  let pulledCommon :=
    ((canonicalPullbackChoice 𝒮.p).pullbackFunctor S.unop.hom).mapIso
      (asIso commonI.hom)
  let C₀ :=
    automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian e₀.symm.hom
  let C₁ :=
    automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian e₁.symm.hom
  have he₀ :
      ((canonicalFiberPseudofunctor 𝒮.p).mapComp'
          qI.op.toLoc S.unop.hom.op.toLoc qS.op.toLoc
          (by cat_disch)).inv.toNatTrans.app A₀ = e₀.inv := by
    simpa [e₀, qS] using
      (fiberPseudofunctor_mapComp'_inv_app_eq_pullbackCompComponentIso_inv
        (hc := canonicalPullbackChoice 𝒮.p) qI S.unop.hom A₀)
  have he₁ :
      ((canonicalFiberPseudofunctor 𝒮.p).mapComp'
          qI.op.toLoc S.unop.hom.op.toLoc qS.op.toLoc
          (by cat_disch)).hom.toNatTrans.app A₁ = e₁.hom := by
    simpa [e₁, qS] using
      (fiberPseudofunctor_mapComp'_hom_app_eq_pullbackCompComponentIso_hom
        (hc := canonicalPullbackChoice 𝒮.p) qI S.unop.hom A₁)
  have hfront_bridge :
      ((J.pseudofunctorOver (Type (max u v))).map S.unop.hom.op.toLoc).toFunctor.map
          BqI₀.hom ≫ Bs₀.hom ≫ C₀.hom =
        M.inv.toNatTrans.app
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian A₀) ≫ BqS₀.hom := by
    simpa [M, BqI₀, Bs₀, BqS₀, C₀, e₀, A₀] using
      (automorphismUnderlyingSheafBaseChangeIso_comp_conj_hom
        (𝒮 := 𝒮) hAbelian qI S.unop.hom qS A₀ (by cat_disch) e₀ he₀)
  have hfront :
      BqS₀.inv ≫ M.hom.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian A₀) ≫
        ((J.pseudofunctorOver (Type (max u v))).map S.unop.hom.op.toLoc).toFunctor.map
          BqI₀.hom ≫ Bs₀.hom = C₀.inv := by
    have hM₀ :
        M.hom.toNatTrans.app (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian A₀) ≫
          M.inv.toNatTrans.app (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian A₀) =
        𝟙 _ := by
      simpa [Cat.Hom.toNatIso] using
        Iso.hom_inv_id_app (Cat.Hom.toNatIso M)
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian A₀)
    have hfront_sub :
        BqS₀.inv ≫ M.hom.toNatTrans.app
              (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian A₀) ≫
            (((J.pseudofunctorOver (Type (max u v))).map
                S.unop.hom.op.toLoc).toFunctor.map BqI₀.hom ≫ Bs₀.hom ≫ C₀.hom) =
          BqS₀.inv ≫ M.hom.toNatTrans.app
              (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian A₀) ≫
            (M.inv.toNatTrans.app
                (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian A₀) ≫ BqS₀.hom) := by
      exact congrArg
        (fun m =>
          BqS₀.inv ≫ M.hom.toNatTrans.app
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian A₀) ≫ m)
        hfront_bridge
    have hcancel :
        (BqS₀.inv ≫ M.hom.toNatTrans.app
              (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian A₀) ≫
            ((J.pseudofunctorOver (Type (max u v))).map S.unop.hom.op.toLoc).toFunctor.map
              BqI₀.hom ≫ Bs₀.hom) ≫ C₀.hom =
          C₀.inv ≫ C₀.hom := by
      have hassoc :
          (BqS₀.inv ≫ M.hom.toNatTrans.app
                (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian A₀) ≫
              ((J.pseudofunctorOver (Type (max u v))).map S.unop.hom.op.toLoc).toFunctor.map
                BqI₀.hom ≫ Bs₀.hom) ≫ C₀.hom =
            BqS₀.inv ≫ M.hom.toNatTrans.app
              (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian A₀) ≫
            (((J.pseudofunctorOver (Type (max u v))).map
                S.unop.hom.op.toLoc).toFunctor.map BqI₀.hom ≫ Bs₀.hom ≫ C₀.hom) := by
        simp only [Category.assoc]
      have hlast :
          BqS₀.inv ≫ M.hom.toNatTrans.app
              (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian A₀) ≫
            (M.inv.toNatTrans.app
                (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian A₀) ≫ BqS₀.hom) =
            C₀.inv ≫ C₀.hom := by
        have hmain :
            BqS₀.inv ≫ M.hom.toNatTrans.app
                (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian A₀) ≫
              M.inv.toNatTrans.app
                (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian A₀) ≫
              BqS₀.hom =
            BqS₀.inv ≫ 𝟙 _ ≫ BqS₀.hom := by
          simpa only [Category.assoc] using
            congrArg (fun m => BqS₀.inv ≫ m ≫ BqS₀.hom) hM₀
        have hmain' :
            BqS₀.inv ≫ M.hom.toNatTrans.app
                (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian A₀) ≫
              (M.inv.toNatTrans.app
                  (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian A₀) ≫ BqS₀.hom) =
            BqS₀.inv ≫ 𝟙 _ ≫ BqS₀.hom := by
          simpa only [Category.assoc] using hmain
        have hiso :
            BqS₀.inv ≫ 𝟙 _ ≫ BqS₀.hom = C₀.inv ≫ C₀.hom := by
          simpa only [Category.id_comp, Category.comp_id] using
            BqS₀.inv_hom_id.trans C₀.inv_hom_id.symm
        exact hmain'.trans hiso
      exact hassoc.trans (hfront_sub.trans hlast)
    exact (cancel_mono C₀.hom).mp hcancel
  have htail_bridge :
      (C₁.inv ≫ Bs₁.inv) ≫
          ((J.pseudofunctorOver (Type (max u v))).map S.unop.hom.op.toLoc).toFunctor.map
            BqI₁.inv =
        BqS₁.inv ≫ M.hom.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian A₁) := by
    simpa [M, BqI₁, Bs₁, BqS₁, C₁, e₁, A₁] using
      (automorphismUnderlyingSheafBaseChangeIso_comp_conj_inv
        (𝒮 := 𝒮) hAbelian qI S.unop.hom qS A₁ (by cat_disch) e₁ he₁)
  have htail :
      Bs₁.inv ≫
          ((J.pseudofunctorOver (Type (max u v))).map S.unop.hom.op.toLoc).toFunctor.map
            BqI₁.inv ≫
          M.inv.toNatTrans.app
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian A₁) ≫
          BqS₁.hom =
        C₁.hom := by
    have hM₁ :
        M.hom.toNatTrans.app (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian A₁) ≫
          M.inv.toNatTrans.app (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian A₁) =
        𝟙 _ := by
      simpa [Cat.Hom.toNatIso] using
        Iso.hom_inv_id_app (Cat.Hom.toNatIso M)
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian A₁)
    have htail_sub :
        ((C₁.inv ≫ Bs₁.inv) ≫
            ((J.pseudofunctorOver (Type (max u v))).map S.unop.hom.op.toLoc).toFunctor.map
              BqI₁.inv) ≫
          M.inv.toNatTrans.app
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian A₁) ≫
          BqS₁.hom =
        (BqS₁.inv ≫ M.hom.toNatTrans.app
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian A₁)) ≫
          M.inv.toNatTrans.app
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian A₁) ≫
          BqS₁.hom := by
      simpa only [Category.assoc] using
        congrArg
          (fun m =>
            m ≫ M.inv.toNatTrans.app
              (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian A₁) ≫ BqS₁.hom)
          htail_bridge
    have hcancel :
        C₁.inv ≫
            (Bs₁.inv ≫
              ((J.pseudofunctorOver (Type (max u v))).map S.unop.hom.op.toLoc).toFunctor.map
                BqI₁.inv ≫
              M.inv.toNatTrans.app
                (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian A₁) ≫
              BqS₁.hom) =
          C₁.inv ≫ C₁.hom := by
      have hassoc :
          C₁.inv ≫
            (Bs₁.inv ≫
              ((J.pseudofunctorOver (Type (max u v))).map S.unop.hom.op.toLoc).toFunctor.map
                BqI₁.inv ≫
              M.inv.toNatTrans.app
                (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian A₁) ≫
              BqS₁.hom) =
            ((C₁.inv ≫ Bs₁.inv) ≫
              ((J.pseudofunctorOver (Type (max u v))).map S.unop.hom.op.toLoc).toFunctor.map
                BqI₁.inv) ≫
              M.inv.toNatTrans.app
                (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian A₁) ≫
              BqS₁.hom := by
        simp only [Category.assoc]
      have hlast :
          (BqS₁.inv ≫ M.hom.toNatTrans.app
              (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian A₁)) ≫
              M.inv.toNatTrans.app
                (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian A₁) ≫
              BqS₁.hom =
            C₁.inv ≫ C₁.hom := by
        have hmain :
            (BqS₁.inv ≫ M.hom.toNatTrans.app
                (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian A₁)) ≫
              M.inv.toNatTrans.app
                (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian A₁) ≫
              BqS₁.hom =
            BqS₁.inv ≫ 𝟙 _ ≫ BqS₁.hom := by
          simpa only [Category.assoc] using
            congrArg (fun m => BqS₁.inv ≫ m ≫ BqS₁.hom) hM₁
        have hiso :
            BqS₁.inv ≫ 𝟙 _ ≫ BqS₁.hom = C₁.inv ≫ C₁.hom := by
          simpa only [Category.id_comp, Category.comp_id] using
            BqS₁.inv_hom_id.trans C₁.inv_hom_id.symm
        exact hmain.trans hiso
      exact hassoc.trans (htail_sub.trans hlast)
    exact (cancel_epi C₁.inv).mp hcancel
  have hpull :
      ((J.pseudofunctorOver (Type (max u v))).map S.unop.hom.op.toLoc).toFunctor.map
          ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian commonI.hom).hom) =
        Bs₀.hom ≫
          (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian pulledCommon.hom).hom ≫
          Bs₁.inv := by
    simpa [commonI, pulledCommon, Bs₀, Bs₁, A₀, A₁] using
      (chosen_local_common_owner_conjugation_pullback_eq_owner_leg
        (𝒮 := 𝒮) hGerbe hAbelian qI (K := K) I.Y.hom
        (by simp [qI]) S.unop.hom)
  have hC₀_inv :
      C₀.inv = (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian e₀.hom).hom := by
    change
      automorphismUnderlyingSheafConj_hom (𝒮 := 𝒮) hAbelian (asIso e₀.symm.hom).inv =
        automorphismUnderlyingSheafConj_hom (𝒮 := 𝒮) hAbelian e₀.hom
    exact automorphismUnderlyingSheafConj_hom_eq_of_parallel (𝒮 := 𝒮) hAbelian _ _
  have htriple :
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (e₀.hom ≫ pulledCommon.hom ≫ e₁.symm.hom)).hom =
        C₀.inv ≫
          (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian pulledCommon.hom).hom ≫
          C₁.hom := by
    rw [hC₀_inv]
    change
      automorphismUnderlyingSheafConj_hom (𝒮 := 𝒮) hAbelian
          (e₀.hom ≫ pulledCommon.hom ≫ e₁.inv) =
        automorphismUnderlyingSheafConj_hom (𝒮 := 𝒮) hAbelian e₀.hom ≫
          automorphismUnderlyingSheafConj_hom (𝒮 := 𝒮) hAbelian pulledCommon.hom ≫
          automorphismUnderlyingSheafConj_hom (𝒮 := 𝒮) hAbelian e₁.inv
    calc
      automorphismUnderlyingSheafConj_hom (𝒮 := 𝒮) hAbelian
          (e₀.hom ≫ pulledCommon.hom ≫ e₁.inv) =
        automorphismUnderlyingSheafConj_hom (𝒮 := 𝒮) hAbelian
            (e₀.hom ≫ pulledCommon.hom) ≫
          automorphismUnderlyingSheafConj_hom (𝒮 := 𝒮) hAbelian e₁.inv := by
          simpa only [Category.assoc] using
            (automorphismUnderlyingSheafConj_hom_comp (𝒮 := 𝒮) hAbelian
              (e₀.hom ≫ pulledCommon.hom) e₁.inv)
      _ =
        (automorphismUnderlyingSheafConj_hom (𝒮 := 𝒮) hAbelian e₀.hom ≫
            automorphismUnderlyingSheafConj_hom (𝒮 := 𝒮) hAbelian pulledCommon.hom) ≫
          automorphismUnderlyingSheafConj_hom (𝒮 := 𝒮) hAbelian e₁.inv := by
          rw [automorphismUnderlyingSheafConj_hom_comp (𝒮 := 𝒮) hAbelian
            e₀.hom pulledCommon.hom]
      _ =
        automorphismUnderlyingSheafConj_hom (𝒮 := 𝒮) hAbelian e₀.hom ≫
          automorphismUnderlyingSheafConj_hom (𝒮 := 𝒮) hAbelian pulledCommon.hom ≫
          automorphismUnderlyingSheafConj_hom (𝒮 := 𝒮) hAbelian e₁.inv := by
          simp only [Category.assoc]
  have hcommon :
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian commonS.hom).hom =
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (e₀.hom ≫ pulledCommon.hom ≫ e₁.symm.hom)).hom := by
    exact congrArg Iso.hom
      (automorphismUnderlyingSheafConj_eq_of_parallel (𝒮 := 𝒮) hAbelian commonS.hom
        (e₀.hom ≫ pulledCommon.hom ≫ e₁.symm.hom))
  have hrhs :
      cohIn ≫
          ((J.pseudofunctorOver (Type (max u v))).map S.unop.hom.op.toLoc).toFunctor.map
            ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian commonI.hom).hom) ≫
          cohOutInv =
        C₀.inv ≫
          (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian pulledCommon.hom).hom ≫
          C₁.hom := by
    dsimp [cohIn, cohOutInv]
    erw [hpull]
    calc
      ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qS A₀).inv ≫
            M.hom.toNatTrans.app (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian A₀) ≫
          ((J.pseudofunctorOver (Type (max u v))).map S.unop.hom.op.toLoc).toFunctor.map
            (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI A₀).hom) ≫
        (Bs₀.hom ≫
          (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian pulledCommon.hom).hom ≫
          Bs₁.inv) ≫
        ((J.pseudofunctorOver (Type (max u v))).map S.unop.hom.op.toLoc).toFunctor.map
            (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI A₁).inv ≫
        M.inv.toNatTrans.app (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian A₁) ≫
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qS A₁).hom =
          (BqS₀.inv ≫ M.hom.toNatTrans.app
              (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian A₀) ≫
            ((J.pseudofunctorOver (Type (max u v))).map S.unop.hom.op.toLoc).toFunctor.map
              BqI₀.hom ≫ Bs₀.hom) ≫
          (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian pulledCommon.hom).hom ≫
          (Bs₁.inv ≫
            ((J.pseudofunctorOver (Type (max u v))).map S.unop.hom.op.toLoc).toFunctor.map
              BqI₁.inv ≫
            M.inv.toNatTrans.app (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian A₁) ≫
            BqS₁.hom) := by
          simp only [BqS₀, BqI₀, BqI₁, BqS₁, Category.assoc]
      _ =
          C₀.inv ≫
            (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian pulledCommon.hom).hom ≫
            C₁.hom := by
          let P :=
            (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian pulledCommon.hom).hom
          let Tail :=
            Bs₁.inv ≫
              ((J.pseudofunctorOver (Type (max u v))).map S.unop.hom.op.toLoc).toFunctor.map
                BqI₁.inv ≫
              M.inv.toNatTrans.app (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian A₁) ≫
              BqS₁.hom
          have hleft :
              (BqS₀.inv ≫ M.hom.toNatTrans.app
                  (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian A₀) ≫
                ((J.pseudofunctorOver (Type (max u v))).map S.unop.hom.op.toLoc).toFunctor.map
                  BqI₀.hom ≫ Bs₀.hom) ≫ P ≫ Tail =
                C₀.inv ≫ P ≫ Tail := by
            simpa [P, Tail, Category.assoc] using
              congrArg (fun m => m ≫ P ≫ Tail) hfront
          have hright : C₀.inv ≫ P ≫ Tail = C₀.inv ≫ P ≫ C₁.hom := by
            simpa only [Tail] using
              congrArg (fun m => C₀.inv ≫ P ≫ m) htail
          exact hleft.trans hright
  exact (hcommon.trans htriple).trans hrhs.symm

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
    {S : (Over I.Y.left)ᵒᵖ} :
    let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
    let qS : S.unop.left ⟶ L.Y := S.unop.hom ≫ qI
    let O' : (Over S.unop.left)ᵒᵖ := op (Over.mk (𝟙 S.unop.left))
    -- Owner-change coherence bridges between the composite owner `qS` and `S.unop.hom`-pull of `qI`.
    let cohIn :=
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qS
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).inv ≫
        (((J.pseudofunctorOver (Type (max u v))).mapComp'
            qI.op.toLoc S.unop.hom.op.toLoc qS.op.toLoc (by cat_disch)).hom.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))) ≫
        ((J.pseudofunctorOver (Type (max u v))).map S.unop.hom.op.toLoc).toFunctor.map
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).hom
    let cohOutInv :=
      ((J.pseudofunctorOver (Type (max u v))).map S.unop.hom.op.toLoc).toFunctor.map
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).inv ≫
        (((J.pseudofunctorOver (Type (max u v))).mapComp'
            qI.op.toLoc S.unop.hom.op.toLoc qS.op.toLoc (by cat_disch)).inv.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x))) ≫
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qS
          (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).hom
    ∀ t :
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (qS ^*[canonicalPullbackChoice 𝒮.p]
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.obj O',
    (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_common_owner_isomorphism
              (𝒮 := 𝒮) hGerbe qS (K := K) (g := S.unop.hom ≫ I.Y.hom)
              (by simp [qI, qS, Category.assoc])).hom).hom).1.app O')
        t =
      (cohOutInv.1.app O')
        (((((J.pseudofunctorOver (Type (max u v))).map S.unop.hom.op.toLoc).toFunctor.map
                ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
                  (chosen_local_common_owner_isomorphism
                    (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
                    (by simp [qI])).hom).hom)).1.app O')
            ((cohIn.1.app O') t)) := by
  intro qI qS O' cohIn cohOutInv t
  have h :=
    chosen_local_owner_leg_qS_common_owner_shell_eq_pullback_qI_morphism
      (𝒮 := 𝒮) hGerbe hAbelian L K (T := T) I (S := S)
  exact congrFun (congrArg (fun m => m.1.app O') h) t


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
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.obj
        (op ((Over.map (𝟙 I.Y.left)).obj (Over.mk S.unop.hom)))) :
    -- Owner-input cast normalization of the boundary section `β`: the `Eq.mp` owner cast equals
    -- the corresponding `eqToHom` presheaf restriction in the pulled `qI`-automorphism sheaf.
    Eq.mp
        (congrArg
          ((automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            ((I.Y.hom ≫ K.f) ^*[canonicalPullbackChoice 𝒮.p]
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.obj)
          (over_map_obj_mk_eq_op (𝟙 I.Y.left) S.unop.hom S.unop.hom (by simp)))
        β =
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          ((I.Y.hom ≫ K.f) ^*[canonicalPullbackChoice 𝒮.p]
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.map
        (eqToHom (over_map_obj_mk_eq_op (𝟙 I.Y.left) S.unop.hom S.unop.hom (by simp))) β := by
  exact eqmp_eq_map_eqToHom
    (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      ((I.Y.hom ≫ K.f) ^*[canonicalPullbackChoice 𝒮.p]
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1
    (over_map_obj_mk_eq_op (𝟙 I.Y.left) S.unop.hom S.unop.hom (by simp)) β


/-- Frontier for the fixed `qI` component normalization: the pulled chosen-local conjugation is
the fixed common-owner comparison with the source and target `mapComp'`/base-change boundaries
inserted in the orientation used by owner-leg consumers. -/
private theorem chosen_local_fixed_qI_component_normalized_morphism
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
    let inB :=
      ((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.map
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).inv ≫
        (((J.pseudofunctorOver (Type (max u v))).mapComp'
            K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)).inv.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))) ≫
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).hom
    let outBridgeInv :=
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
          (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).inv ≫
        (((J.pseudofunctorOver (Type (max u v))).mapComp'
            K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)).hom.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x))) ≫
        ((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.map
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).hom
    ((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.map
        ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom) =
      inB ≫
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
            (by simp [qI])).hom).hom ≫
        outBridgeInv := by
  intro qI inB outBridgeInv
  let A₀ :=
    automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
  let A₁ :=
    automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (L.f ^*[canonicalPullbackChoice 𝒮.p] x)
  let Bq₀ :=
    automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
  let Bq₁ :=
    automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
      (L.f ^*[canonicalPullbackChoice 𝒮.p] x)
  let Biter₀ :=
    automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I.Y.hom
      (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))
  let Biter₁ :=
    automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I.Y.hom
      (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x))
  let MK₀ :=
    ((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.mapIso
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))
  let MK₁ :=
    ((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.mapIso
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x))
  let M :=
    (J.pseudofunctorOver (Type (max u v))).mapComp'
      K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)
  let source :=
    (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
      (chosen_local_common_owner_source_iso
        (𝒮 := 𝒮) hGerbe qI I.Y.hom (by simp [qI])).inv).hom
  let common :=
    (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
      (chosen_local_common_owner_isomorphism
        (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
        (by simp [qI])).hom).hom
  let target :=
    (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
      (chosen_local_common_owner_target_iso
        (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
        (by simp [qI])).hom).hom
  have hpulled :
      ((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.map
          ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
              (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom) =
        Biter₀.hom ≫ (source ≫ common ≫ target) ≫ Biter₁.inv := by
    -- Use the canonical Part06 factorization before rotating the source/target flanks.
    simpa [Biter₀, Biter₁, source, common, target] using
      (chosen_local_pulled_conjugation_eq_common_owner_middle
        (𝒮 := 𝒮) hGerbe hAbelian qI (K := K) I.Y.hom (by simp [qI]))
  have hsource : Biter₀.hom ≫ source = inB := by
    have hboundary :=
      chosen_local_source_common_owner_left_flank_boundary_morphism
        (𝒮 := 𝒮) hGerbe hAbelian (𝟙 x) L K (T := T) I
    have hboundary' :
        source = (MK₀ ≪≫ Biter₀).inv ≫ M.inv.toNatTrans.app A₀ ≫ Bq₀.hom := by
      simpa [source, MK₀, Biter₀, M, A₀, Bq₀, qI] using hboundary
    rw [hboundary']
    dsimp [inB]
    simpa only [Category.assoc, Category.id_comp] using
      congrArg (fun f => f ≫ MK₀.inv ≫ M.inv.toNatTrans.app A₀ ≫ Bq₀.hom)
        Biter₀.hom_inv_id
  have htarget : target ≫ Biter₁.inv = outBridgeInv := by
    have hboundary :=
      chosen_local_target_mapComp'_hom_eq_common_owner_target_iso_hom
        (𝒮 := 𝒮) hGerbe hAbelian qI (K := K) I.Y.hom (by simp [qI])
    have hboundary' :
        M.hom.toNatTrans.app A₁ = Bq₁.hom ≫ target ≫ (MK₁ ≪≫ Biter₁).inv := by
      simpa [target, MK₁, Biter₁, M, A₁, Bq₁, qI] using hboundary
    dsimp [outBridgeInv]
    change target ≫ Biter₁.inv = Bq₁.inv ≫ M.hom.toNatTrans.app A₁ ≫ MK₁.hom
    rw [hboundary']
    simp only [Iso.trans_inv]
    have hbq :
        Bq₁.inv ≫ (Bq₁.hom ≫ target ≫ Biter₁.inv ≫ MK₁.inv) ≫ MK₁.hom =
          target ≫ Biter₁.inv ≫ MK₁.inv ≫ MK₁.hom := by
      simpa only [Category.assoc, Category.id_comp] using
        congrArg (fun f => f ≫ target ≫ Biter₁.inv ≫ MK₁.inv ≫ MK₁.hom)
          Bq₁.inv_hom_id
    have hmk :
        target ≫ Biter₁.inv ≫ MK₁.inv ≫ MK₁.hom = target ≫ Biter₁.inv := by
      simpa only [Category.assoc, Category.comp_id] using
        congrArg (fun f => (target ≫ Biter₁.inv) ≫ f) MK₁.inv_hom_id
    exact (hbq.trans hmk).symm
  have hleft :
      Biter₀.hom ≫ source ≫ common ≫ target ≫ Biter₁.inv =
        inB ≫ common ≫ target ≫ Biter₁.inv := by
    simpa only [Category.assoc] using
      congrArg (fun m => m ≫ common ≫ target ≫ Biter₁.inv) hsource
  have hright :
      inB ≫ common ≫ target ≫ Biter₁.inv =
        inB ≫ common ≫ outBridgeInv := by
    simpa only [Category.assoc] using
      congrArg (fun m => inB ≫ common ≫ m) htarget
  change
    ((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.map
        ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom) =
      inB ≫ common ≫ outBridgeInv
  exact hpulled.trans (hleft.trans hright)

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
    {S : (Over I.Y.left)ᵒᵖ} :
    let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
    -- Bridge from the `I.Y.hom`-pulled `K.f^*`-sheaf to the composite `qI`-pullback sheaf.
    let inB :=
      ((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.map
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).inv ≫
        (((J.pseudofunctorOver (Type (max u v))).mapComp'
            K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)).inv.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))) ≫
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).hom
    let outBridgeInv :=
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
          (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).inv ≫
        (((J.pseudofunctorOver (Type (max u v))).mapComp'
            K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)).hom.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x))) ≫
        ((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.map
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).hom
    ∀ s :
        (((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (K.f ^*[canonicalPullbackChoice 𝒮.p]
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)))).1.obj S,
    ((((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.map
          ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
              (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom)).1.app S)
        s =
      (outBridgeInv.1.app S)
        (((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
                (chosen_local_common_owner_isomorphism
                  (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
                  (by simp [qI])).hom).hom).1.app S)
            ((inB.1.app S) s))) := by
  intro qI inB outBridgeInv s
  have h :=
    chosen_local_fixed_qI_component_normalized_morphism
      (𝒮 := 𝒮) hGerbe hAbelian L K (T := T) I
  exact congrFun (congrArg (fun m => m.1.app S) h) s


/-- Frontier for the literal `qS` component normalization: this is the fixed-`qI` normalization
with `I.Y.hom` replaced by the composite owner `g7 := S.unop.hom ≫ I.Y.hom`, ready to combine
with the qS/qI owner-leg comparison. -/
private theorem chosen_local_qS_pulled_conjugation_eq_common_owner_component_morphism
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
    {S : (Over I.Y.left)ᵒᵖ} :
    let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
    let qS : S.unop.left ⟶ L.Y := S.unop.hom ≫ qI
    let g7 : S.unop.left ⟶ K.Y := S.unop.hom ≫ I.Y.hom
    let inB :=
      ((J.pseudofunctorOver (Type (max u v))).map g7.op.toLoc).toFunctor.map
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).inv ≫
        (((J.pseudofunctorOver (Type (max u v))).mapComp'
            K.f.op.toLoc g7.op.toLoc qS.op.toLoc (by simp [qS, qI, g7, Category.assoc])).inv.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))) ≫
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qS
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).hom
    let outBridgeInv :=
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qS
          (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).inv ≫
        (((J.pseudofunctorOver (Type (max u v))).mapComp'
            K.f.op.toLoc g7.op.toLoc qS.op.toLoc (by simp [qS, qI, g7, Category.assoc])).hom.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x))) ≫
        ((J.pseudofunctorOver (Type (max u v))).map g7.op.toLoc).toFunctor.map
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).hom
    ((J.pseudofunctorOver (Type (max u v))).map g7.op.toLoc).toFunctor.map
        ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom) =
      inB ≫
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe qS (K := K) (g := S.unop.hom ≫ I.Y.hom)
            (by simp [qI, qS, Category.assoc])).hom).hom ≫
        outBridgeInv := by
  intro qI qS g7 inB outBridgeInv
  let A₀ :=
    automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
  let A₁ :=
    automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (L.f ^*[canonicalPullbackChoice 𝒮.p] x)
  let Bq₀ :=
    automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qS
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
  let Bq₁ :=
    automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qS
      (L.f ^*[canonicalPullbackChoice 𝒮.p] x)
  let Biter₀ :=
    automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian g7
      (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))
  let Biter₁ :=
    automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian g7
      (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x))
  let MK₀ :=
    ((J.pseudofunctorOver (Type (max u v))).map g7.op.toLoc).toFunctor.mapIso
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))
  let MK₁ :=
    ((J.pseudofunctorOver (Type (max u v))).map g7.op.toLoc).toFunctor.mapIso
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x))
  let M :=
    (J.pseudofunctorOver (Type (max u v))).mapComp'
      K.f.op.toLoc g7.op.toLoc qS.op.toLoc (by simp [qS, qI, g7, Category.assoc])
  let source :=
    (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
      (chosen_local_common_owner_source_iso
        (𝒮 := 𝒮) hGerbe qS (K := K) (g := g7)
        (by simp [qS, qI, g7, Category.assoc])).inv).hom
  let common :=
    (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
      (chosen_local_common_owner_isomorphism
        (𝒮 := 𝒮) hGerbe qS (K := K) (g := S.unop.hom ≫ I.Y.hom)
        (by simp [qI, qS, Category.assoc])).hom).hom
  let target :=
    (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
      (chosen_local_common_owner_target_iso
        (𝒮 := 𝒮) hGerbe qS (K := K) (g := g7)
        (by simp [qS, qI, g7, Category.assoc])).hom).hom
  have hpulled :
      ((J.pseudofunctorOver (Type (max u v))).map g7.op.toLoc).toFunctor.map
          ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
              (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom) =
        Biter₀.hom ≫ (source ≫ common ≫ target) ≫ Biter₁.inv := by
    -- Apply the fixed-owner factorization with the composite owner `g7`.
    simpa [Biter₀, Biter₁, source, common, target, g7] using
      (chosen_local_pulled_conjugation_eq_common_owner_middle
        (𝒮 := 𝒮) hGerbe hAbelian qS (K := K) g7
        (by simp [qS, qI, g7, Category.assoc]))
  have hsource : Biter₀.hom ≫ source = inB := by
    have hboundary :=
      chosen_local_source_mapComp'_inv_eq_common_owner_source_iso_inv
        (𝒮 := 𝒮) hGerbe hAbelian qS (K := K) g7
        (by simp [qS, qI, g7, Category.assoc])
    have hboundary' :
        M.inv.toNatTrans.app A₀ = (MK₀ ≪≫ Biter₀).hom ≫ source ≫ Bq₀.inv := by
      simpa [source, MK₀, Biter₀, M, A₀, Bq₀, qS, qI, g7] using hboundary
    dsimp [inB]
    rw [hboundary']
    simp only [Iso.trans_hom, Category.assoc]
    have hmk :
        MK₀.inv ≫ (MK₀.hom ≫ Biter₀.hom ≫ source ≫ Bq₀.inv) ≫ Bq₀.hom =
          Biter₀.hom ≫ source ≫ Bq₀.inv ≫ Bq₀.hom := by
      simpa only [Category.assoc, Category.id_comp] using
        congrArg (fun f => f ≫ Biter₀.hom ≫ source ≫ Bq₀.inv ≫ Bq₀.hom)
          MK₀.inv_hom_id
    have hbq :
        Biter₀.hom ≫ source ≫ Bq₀.inv ≫ Bq₀.hom = Biter₀.hom ≫ source := by
      simpa only [Category.assoc, Category.comp_id] using
        congrArg (fun f => (Biter₀.hom ≫ source) ≫ f) Bq₀.inv_hom_id
    exact (hmk.trans hbq).symm
  have htarget : target ≫ Biter₁.inv = outBridgeInv := by
    have hboundary :=
      chosen_local_target_mapComp'_hom_eq_common_owner_target_iso_hom
        (𝒮 := 𝒮) hGerbe hAbelian qS (K := K) g7
        (by simp [qS, qI, g7, Category.assoc])
    have hboundary' :
        M.hom.toNatTrans.app A₁ = Bq₁.hom ≫ target ≫ (MK₁ ≪≫ Biter₁).inv := by
      simpa [target, MK₁, Biter₁, M, A₁, Bq₁, qS, qI, g7] using hboundary
    dsimp [outBridgeInv]
    change target ≫ Biter₁.inv = Bq₁.inv ≫ M.hom.toNatTrans.app A₁ ≫ MK₁.hom
    rw [hboundary']
    simp only [Iso.trans_inv]
    have hbq :
        Bq₁.inv ≫ (Bq₁.hom ≫ target ≫ Biter₁.inv ≫ MK₁.inv) ≫ MK₁.hom =
          target ≫ Biter₁.inv ≫ MK₁.inv ≫ MK₁.hom := by
      simpa only [Category.assoc, Category.id_comp] using
        congrArg (fun f => f ≫ target ≫ Biter₁.inv ≫ MK₁.inv ≫ MK₁.hom)
          Bq₁.inv_hom_id
    have hmk :
        target ≫ Biter₁.inv ≫ MK₁.inv ≫ MK₁.hom = target ≫ Biter₁.inv := by
      simpa only [Category.assoc, Category.comp_id] using
        congrArg (fun f => (target ≫ Biter₁.inv) ≫ f) MK₁.inv_hom_id
    exact (hbq.trans hmk).symm
  have hleft :
      Biter₀.hom ≫ source ≫ common ≫ target ≫ Biter₁.inv =
        inB ≫ common ≫ target ≫ Biter₁.inv := by
    simpa only [Category.assoc] using
      congrArg (fun m => m ≫ common ≫ target ≫ Biter₁.inv) hsource
  have hright :
      inB ≫ common ≫ target ≫ Biter₁.inv =
        inB ≫ common ≫ outBridgeInv := by
    simpa only [Category.assoc] using
      congrArg (fun m => inB ≫ common ≫ m) htarget
  change
    ((J.pseudofunctorOver (Type (max u v))).map g7.op.toLoc).toFunctor.map
        ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom) =
      inB ≫ common ≫ outBridgeInv
  exact hpulled.trans (hleft.trans hright)

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
    {S : (Over I.Y.left)ᵒᵖ} :
    let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
    let qS : S.unop.left ⟶ L.Y := S.unop.hom ≫ qI
    let g7 : S.unop.left ⟶ K.Y := S.unop.hom ≫ I.Y.hom
    let O' : (Over S.unop.left)ᵒᵖ := op (Over.mk (𝟙 S.unop.left))
    -- Bridge from the `g7`-pulled `K.f^*`-sheaf to the composite `qS`-pullback sheaf.
    let inB :=
      ((J.pseudofunctorOver (Type (max u v))).map g7.op.toLoc).toFunctor.map
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).inv ≫
        (((J.pseudofunctorOver (Type (max u v))).mapComp'
            K.f.op.toLoc g7.op.toLoc qS.op.toLoc (by simp [qS, qI, g7, Category.assoc])).inv.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))) ≫
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qS
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).hom
    let outBridgeInv :=
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qS
          (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).inv ≫
        (((J.pseudofunctorOver (Type (max u v))).mapComp'
            K.f.op.toLoc g7.op.toLoc qS.op.toLoc (by simp [qS, qI, g7, Category.assoc])).hom.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x))) ≫
        ((J.pseudofunctorOver (Type (max u v))).map g7.op.toLoc).toFunctor.map
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).hom
    ∀ s :
        (((J.pseudofunctorOver (Type (max u v))).map g7.op.toLoc).toFunctor.obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (K.f ^*[canonicalPullbackChoice 𝒮.p]
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)))).1.obj O',
    ((((J.pseudofunctorOver (Type (max u v))).map g7.op.toLoc).toFunctor.map
          ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
              (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom)).1.app O')
        s =
      (outBridgeInv.1.app O')
        (((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
                (chosen_local_common_owner_isomorphism
                  (𝒮 := 𝒮) hGerbe qS (K := K) (g := S.unop.hom ≫ I.Y.hom)
                  (by simp [qI, qS, Category.assoc])).hom).hom).1.app O')
            ((inB.1.app O') s))) := by
  intro qI qS g7 O' inB outBridgeInv s
  have h :=
    chosen_local_qS_pulled_conjugation_eq_common_owner_component_morphism
      (𝒮 := 𝒮) hGerbe hAbelian L K (T := T) I (S := S)
  exact congrFun (congrArg (fun m => m.1.app O') h) s


end

end CategoryTheory
