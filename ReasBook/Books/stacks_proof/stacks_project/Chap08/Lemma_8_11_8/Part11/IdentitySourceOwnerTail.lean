import stacks_proof.stacks_project.Chap08.Lemma_8_11_8.Part11.TransitionSquare
import stacks_proof.stacks_project.Chap08.Lemma_8_11_8.Part11.IdentityBaseChange

universe u v w

namespace CategoryTheory

open StackInGroupoidsOver
open Opposite
open Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {𝒮 : StackInGroupoidsOver J}

/-- Helper for Lemma 8.11.8: in the identity-pullback cover over `I.f ≫ 𝟙 U`, the original
chosen-cover owner stored by a pullback-cover arrow is the explicit precomposition of `I` by
the pullback-cover leg.  This names the owner normal form without using it to rewrite the main
target. -/
private theorem chosen_cover_identity_source_owner_eq_precomp
    (hGerbe : IsGerbe J 𝒮.p)
    (U : C) (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (K0 : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe (I.f ≫ 𝟙 U)).Arrow) :
    K0.base = I.precomp K0.f := by
  ext <;> simp

private theorem iso_inv_hom_eqToHom_self_comp₂
    {D : Type*} [Category D] {A B Z W : D}
    (e : A ≅ B) (h : B = B) (m : B ⟶ Z) (n : Z ⟶ W) :
    e.inv ≫ (((e.hom ≫ eqToHom h) ≫ m) ≫ n) = m ≫ n := by
  cases h
  simp [Category.assoc]

/-- Helper for Lemma 8.11.8: the chosen-cover counit compatibility on the owner overlap
`K0.base --𝟙--> K0.base` and `K0.base --K0.f--> I`.  This is the datum-side source of the
owner-tail identity before the identity-source shell is stripped. -/
private theorem chosen_cover_descent_datum_overlap_component_owner_tail
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Z : C} (q : Z ⟶ U)
    {I₁ I₂ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = q := by cat_disch) (hg₂ : g₂ ≫ I₂.f = q := by cat_disch) :
    (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
        (chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian U I₁)).hom ≫
      (automorphism_overlap_hom_of_locally_isomorphic_cover
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q g₁ g₂) =
    (chosen_cover_descent_datum
      (𝒮 := 𝒮) hGerbe hAbelian U).hom q g₁ g₂ ≫
      (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso
        (chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian U I₂)).hom := by
  exact (chosen_cover_overlap_descent_datum_counitIso_part11
    (𝒮 := 𝒮) hGerbe hAbelian U).hom.comm q g₁ g₂ hg₁ hg₂

/-- Helper for Lemma 8.11.8: the cover/local-object tail normal form still carrying the
identity-source `map (𝟙 K0.Y)` shell.  The remaining owner-tail work is exactly to strip this
shell on both sides. -/
private theorem chosen_cover_identity_source_owner_tail_with_identity_shell
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (U : C) (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (K0 : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe (I.f ≫ 𝟙 U)).Arrow) :
    ((J.pseudofunctorOver (Type (max u v))).map (𝟙 K0.Y).op.toLoc).toFunctor.map
        (chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian U K0.base).hom ≫
      (automorphismUnderlyingSheafBaseChangeIso
        (𝒮 := 𝒮) hAbelian (𝟙 K0.Y)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U K0.base)).hom ≫
      (chosen_local_automorphism_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        ((𝟙 K0.Y) ^*[canonicalPullbackChoice 𝒮.p]
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U K0.base))
        (K0.f ^*[canonicalPullbackChoice 𝒮.p]
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I))).hom ≫
      (automorphismUnderlyingSheafBaseChangeIso
        (𝒮 := 𝒮) hAbelian K0.f
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I)).inv =
    (chosen_cover_descent_datum
      (𝒮 := 𝒮) hGerbe hAbelian U).hom
        (i₁ := K0.base) (i₂ := I)
        (K0.f ≫ (I.f ≫ 𝟙 U)) (𝟙 K0.Y) K0.f (by simp) (by simp) ≫
      ((J.pseudofunctorOver (Type (max u v))).map K0.f.op.toLoc).toFunctor.map
        (chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian U I).hom := by
  let S := chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U
  let xS := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U
  let q := K0.f ≫ (I.f ≫ 𝟙 U)
  have htail :=
    automorphism_overlap_hom_eq_chosen_local_tail
      (𝒮 := 𝒮) hGerbe hAbelian S xS q
      (I₁ := K0.base) (I₂ := I) (𝟙 K0.Y) K0.f
      (hf₁ := by simp [q]) (hf₂ := by simp [q])
  have hcover :=
    chosen_cover_descent_datum_overlap_component_owner_tail
      (𝒮 := 𝒮) hGerbe hAbelian q
      (I₁ := K0.base) (I₂ := I) (𝟙 K0.Y) K0.f
      (hg₁ := by simp [q]) (hg₂ := by simp [q])
  rw [htail] at hcover
  simpa [S, xS, q, local_overlap_source_object, local_overlap_target_object,
    Functor.mapIso_hom, Category.assoc] using hcover

private theorem chosen_cover_identity_source_owner_tail_left_baseChange_shell
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (U : C) (K0 : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow) :
    let G := chosen_cover_underlying_automorphism_sheaf
      (𝒮 := 𝒮) hGerbe hAbelian U
    let Gbase := (((J.pseudofunctorOver (Type (max u v))).toDescentData
      (fun I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow => I.f)).obj G).obj K0
    ((J.pseudofunctorOver (Type (max u v))).mapId
        (LocallyDiscrete.mk (op K0.Y))).inv.toNatTrans.app Gbase ≫
      ((J.pseudofunctorOver (Type (max u v))).map (𝟙 K0.Y).op.toLoc).toFunctor.map
        (chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian U K0).hom ≫
      (automorphismUnderlyingSheafBaseChangeIso
        (𝒮 := 𝒮) hAbelian (𝟙 K0.Y)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U K0)).hom =
    (chosen_cover_underlying_automorphism_sheaf_cover_iso
        (𝒮 := 𝒮) hGerbe hAbelian U K0).hom ≫
      (automorphismUnderlyingSheafConj
        (𝒮 := 𝒮) hAbelian
        ((canonicalPullbackChoice 𝒮.p).pullbackIdComponentIso K0.Y
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U K0)).hom).hom := by
  let F := J.pseudofunctorOver (Type (max u v))
  let G := chosen_cover_underlying_automorphism_sheaf
    (𝒮 := 𝒮) hGerbe hAbelian U
  let Gbase := ((F.toDescentData
    (fun I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow => I.f)).obj G).obj K0
  let e := chosen_cover_underlying_automorphism_sheaf_cover_iso
    (𝒮 := 𝒮) hGerbe hAbelian U K0
  let x0 := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U K0
  change
    (F.mapId (LocallyDiscrete.mk (op K0.Y))).inv.toNatTrans.app Gbase ≫
      (F.map (𝟙 K0.Y).op.toLoc).toFunctor.map e.hom ≫
      (automorphismUnderlyingSheafBaseChangeIso
        (𝒮 := 𝒮) hAbelian (𝟙 K0.Y) x0).hom =
    e.hom ≫
      (automorphismUnderlyingSheafConj
        (𝒮 := 𝒮) hAbelian
        ((canonicalPullbackChoice 𝒮.p).pullbackIdComponentIso K0.Y x0).hom).hom
  have hnat :=
    ((F.mapId (LocallyDiscrete.mk (op K0.Y))).inv.toNatTrans.naturality e.hom)
  have hnat' :
      (F.mapId (LocallyDiscrete.mk (op K0.Y))).inv.toNatTrans.app Gbase ≫
          (F.map (𝟙 K0.Y).op.toLoc).toFunctor.map e.hom =
        e.hom ≫
          (F.mapId (LocallyDiscrete.mk (op K0.Y))).inv.toNatTrans.app
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x0) := by
    simpa [F, Gbase, e, x0, op_id, Quiver.Hom.id_toLoc] using hnat.symm
  rw [← Category.assoc, hnat']
  exact (Category.assoc _ _ _).trans
    (congrArg (fun m => e.hom ≫ m)
      (automorphismUnderlyingSheaf_identity_baseChange_eq_conj_pullbackId_part11
        (𝒮 := 𝒮) hAbelian x0))

@[reassoc]
private theorem chosen_cover_identity_source_owner_tail_left_baseChange_shell_pullback
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (U : C) (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (K0 : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe (I.f ≫ 𝟙 U)).Arrow) :
    let G := chosen_cover_underlying_automorphism_sheaf
      (𝒮 := 𝒮) hGerbe hAbelian U
    let Gbase := (((J.pseudofunctorOver (Type (max u v))).toDescentData
      (fun I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow => I.f)).obj G).obj K0.base
    ((J.pseudofunctorOver (Type (max u v))).mapId
        (LocallyDiscrete.mk (op K0.Y))).inv.toNatTrans.app Gbase ≫
      ((J.pseudofunctorOver (Type (max u v))).map (𝟙 K0.Y).op.toLoc).toFunctor.map
        (chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian U K0.base).hom ≫
      (automorphismUnderlyingSheafBaseChangeIso
        (𝒮 := 𝒮) hAbelian (𝟙 K0.Y)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U K0.base)).hom =
    (chosen_cover_underlying_automorphism_sheaf_cover_iso
        (𝒮 := 𝒮) hGerbe hAbelian U K0.base).hom ≫
      (automorphismUnderlyingSheafConj
        (𝒮 := 𝒮) hAbelian
        ((canonicalPullbackChoice 𝒮.p).pullbackIdComponentIso K0.Y
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U K0.base)).hom).hom := by
  simpa using
    chosen_cover_identity_source_owner_tail_left_baseChange_shell
      (𝒮 := 𝒮) hGerbe hAbelian U K0.base

@[reassoc]
private theorem chosen_local_automorphism_iso_identity_source_conj_part11
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} (x A : 𝒮.p.Fiber U) :
    (automorphismUnderlyingSheafConj
      (𝒮 := 𝒮) hAbelian
      ((canonicalPullbackChoice 𝒮.p).pullbackIdComponentIso U x).hom).hom ≫
      (chosen_local_automorphism_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        ((𝟙 U) ^*[canonicalPullbackChoice 𝒮.p] x) A).hom =
    (chosen_local_automorphism_iso
      (𝒮 := 𝒮) hGerbe hAbelian x A).hom := by
  -- Residual source-local adapter: this is the source-side analogue of the existing
  -- chosen-local conjugation transport lemma, specialized to the canonical identity pullback.
  sorry

/-- Helper for Lemma 8.11.8: source-side identity shell removal in the owner tail.  This is the
left half of `chosen_cover_identity_source_owner_tail_strip_identity_shell`: the identity
restriction/base-change shell on `K0.base` is absorbed into the source of the chosen-local
automorphism comparison. -/
private theorem chosen_cover_identity_source_owner_tail_left_strip_identity_shell
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (U : C) (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (K0 : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe (I.f ≫ 𝟙 U)).Arrow) :
    let G := chosen_cover_underlying_automorphism_sheaf
      (𝒮 := 𝒮) hGerbe hAbelian U
    let Gbase := (((J.pseudofunctorOver (Type (max u v))).toDescentData
      (fun I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow => I.f)).obj G).obj K0.base
    ((J.pseudofunctorOver (Type (max u v))).mapId
        (LocallyDiscrete.mk (op K0.Y))).inv.toNatTrans.app Gbase ≫
      ((J.pseudofunctorOver (Type (max u v))).map (𝟙 K0.Y).op.toLoc).toFunctor.map
        (chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian U K0.base).hom ≫
      (automorphismUnderlyingSheafBaseChangeIso
        (𝒮 := 𝒮) hAbelian (𝟙 K0.Y)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U K0.base)).hom ≫
      (chosen_local_automorphism_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        ((𝟙 K0.Y) ^*[canonicalPullbackChoice 𝒮.p]
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U K0.base))
        (K0.f ^*[canonicalPullbackChoice 𝒮.p]
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I))).hom ≫
      (automorphismUnderlyingSheafBaseChangeIso
        (𝒮 := 𝒮) hAbelian K0.f
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I)).inv =
    (chosen_cover_underlying_automorphism_sheaf_cover_iso
        (𝒮 := 𝒮) hGerbe hAbelian U K0.base).hom ≫
      (chosen_local_automorphism_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U K0.base)
        (K0.f ^*[canonicalPullbackChoice 𝒮.p]
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I))).hom ≫
      (automorphismUnderlyingSheafBaseChangeIso
        (𝒮 := 𝒮) hAbelian K0.f
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I)).inv := by
  let x0 : 𝒮.p.Fiber K0.Y := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U K0.base
  let A := K0.f ^*[canonicalPullbackChoice 𝒮.p]
    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I)
  let tail :=
    (automorphismUnderlyingSheafBaseChangeIso
      (𝒮 := 𝒮) hAbelian K0.f
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I)).inv
  dsimp only
  rw [reassoc_of% chosen_cover_identity_source_owner_tail_left_baseChange_shell_pullback
    (𝒮 := 𝒮) hGerbe hAbelian U I K0]
  change
    (chosen_cover_underlying_automorphism_sheaf_cover_iso
        (𝒮 := 𝒮) hGerbe hAbelian U K0.base).hom ≫
      (automorphismUnderlyingSheafConj
        (𝒮 := 𝒮) hAbelian
        ((canonicalPullbackChoice 𝒮.p).pullbackIdComponentIso K0.Y x0).hom).hom ≫
      (chosen_local_automorphism_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        ((𝟙 K0.Y) ^*[canonicalPullbackChoice 𝒮.p] x0) A).hom ≫ tail =
    (chosen_cover_underlying_automorphism_sheaf_cover_iso
        (𝒮 := 𝒮) hGerbe hAbelian U K0.base).hom ≫
      (chosen_local_automorphism_iso
        (𝒮 := 𝒮) hGerbe hAbelian x0 A).hom ≫ tail
  erw [reassoc_of% chosen_local_automorphism_iso_identity_source_conj_part11
      (𝒮 := 𝒮) hGerbe hAbelian x0 A]
  rfl

/-- Helper for Lemma 8.11.8: target-side owner normalization in the owner tail.  This is the
right half of `chosen_cover_identity_source_owner_tail_strip_identity_shell`: the overlap-descent
component with source leg `𝟙 K0.Y` is the displayed `I.f,K0.f` `mapComp'` boundary. -/
private theorem chosen_cover_identity_source_owner_tail_right_strip_identity_shell
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (U : C) (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (K0 : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe (I.f ≫ 𝟙 U)).Arrow) :
    let G := chosen_cover_underlying_automorphism_sheaf
      (𝒮 := 𝒮) hGerbe hAbelian U
    let Gbase := (((J.pseudofunctorOver (Type (max u v))).toDescentData
      (fun I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow => I.f)).obj G).obj K0.base
    ((J.pseudofunctorOver (Type (max u v))).mapId
        (LocallyDiscrete.mk (op K0.Y))).inv.toNatTrans.app Gbase ≫
      (chosen_cover_descent_datum
      (𝒮 := 𝒮) hGerbe hAbelian U).hom
        (i₁ := K0.base) (i₂ := I)
        (K0.f ≫ (I.f ≫ 𝟙 U)) (𝟙 K0.Y) K0.f (by simp) (by simp) ≫
      ((J.pseudofunctorOver (Type (max u v))).map K0.f.op.toLoc).toFunctor.map
        (chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian U I).hom =
    (((Cat.Hom.toNatIso
      ((J.pseudofunctorOver (Type (max u v))).mapComp'
        I.f.op.toLoc K0.f.op.toLoc (K0.f ≫ (I.f ≫ 𝟙 U)).op.toLoc
        (by simp [← Quiver.Hom.comp_toLoc, ← op_comp]))).app
      (chosen_cover_underlying_automorphism_sheaf
        (𝒮 := 𝒮) hGerbe hAbelian U)).hom) ≫
      ((J.pseudofunctorOver (Type (max u v))).map K0.f.op.toLoc).toFunctor.map
        (chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian U I).hom := by
  let F := J.pseudofunctorOver (Type (max u v))
  let G := chosen_cover_underlying_automorphism_sheaf
    (𝒮 := 𝒮) hGerbe hAbelian U
  let Gbase := ((F.toDescentData
    (fun I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow => I.f)).obj G).obj K0.base
  change
    (F.mapId (LocallyDiscrete.mk (op K0.Y))).inv.toNatTrans.app Gbase ≫
      (chosen_cover_descent_datum
      (𝒮 := 𝒮) hGerbe hAbelian U).hom
        (i₁ := K0.base) (i₂ := I)
        (K0.f ≫ (I.f ≫ 𝟙 U)) (𝟙 K0.Y) K0.f (by simp) (by simp) ≫
      (F.map K0.f.op.toLoc).toFunctor.map
        (chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian U I).hom =
    (((Cat.Hom.toNatIso
      (F.mapComp'
        I.f.op.toLoc K0.f.op.toLoc (K0.f ≫ (I.f ≫ 𝟙 U)).op.toLoc
        (by simp [← Quiver.Hom.comp_toLoc, ← op_comp]))).app G).hom) ≫
      (F.map K0.f.op.toLoc).toFunctor.map
        (chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian U I).hom
  dsimp [chosen_cover_descent_datum, Gbase, G]
  rw [Pseudofunctor.mapComp'_comp_id_inv_app]
  simpa [F, G] using
    iso_inv_hom_eqToHom_self_comp₂
      ((Cat.Hom.toNatIso
        (F.mapId (LocallyDiscrete.mk (op K0.Y)))).app
        ((F.map ((𝟙 (LocallyDiscrete.mk (op U)) ≫ I.f.op.toLoc) ≫ K0.f.op.toLoc)).toFunctor.obj G))
      (by simp)
      (((F.mapComp'
          I.f.op.toLoc K0.f.op.toLoc
          ((𝟙 (LocallyDiscrete.mk (op U)) ≫ I.f.op.toLoc) ≫ K0.f.op.toLoc)
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app G))
      ((F.map K0.f.op.toLoc).toFunctor.map
        (chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian U I).hom)

/-- Helper for Lemma 8.11.8: stripping the identity-source shell from
`chosen_cover_identity_source_owner_tail_with_identity_shell`.  This is the remaining narrow
adapter: the left side uses the `mapId`/identity base-change/pullback-id source conjugation,
while the right side cancels the `mapComp' _ (𝟙 _)` shell to the displayed `I.f,K0.f`
`mapComp'`. -/
private theorem chosen_cover_identity_source_owner_tail_strip_identity_shell
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (U : C) (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (K0 : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe (I.f ≫ 𝟙 U)).Arrow) :
    (chosen_cover_underlying_automorphism_sheaf_cover_iso
        (𝒮 := 𝒮) hGerbe hAbelian U K0.base).hom ≫
      (chosen_local_automorphism_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U K0.base)
        (K0.f ^*[canonicalPullbackChoice 𝒮.p]
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I))).hom ≫
      (automorphismUnderlyingSheafBaseChangeIso
        (𝒮 := 𝒮) hAbelian K0.f
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I)).inv =
    (((Cat.Hom.toNatIso
      ((J.pseudofunctorOver (Type (max u v))).mapComp'
        I.f.op.toLoc K0.f.op.toLoc (K0.f ≫ (I.f ≫ 𝟙 U)).op.toLoc
        (by simp [← Quiver.Hom.comp_toLoc, ← op_comp]))).app
      (chosen_cover_underlying_automorphism_sheaf
        (𝒮 := 𝒮) hGerbe hAbelian U)).hom) ≫
      ((J.pseudofunctorOver (Type (max u v))).map K0.f.op.toLoc).toFunctor.map
        (chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian U I).hom := by
  let G := chosen_cover_underlying_automorphism_sheaf
    (𝒮 := 𝒮) hGerbe hAbelian U
  let Gbase := (((J.pseudofunctorOver (Type (max u v))).toDescentData
    (fun I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow => I.f)).obj G).obj K0.base
  let idInv :=
    ((J.pseudofunctorOver (Type (max u v))).mapId
      (LocallyDiscrete.mk (op K0.Y))).inv.toNatTrans.app Gbase
  have hshell := chosen_cover_identity_source_owner_tail_with_identity_shell
    (𝒮 := 𝒮) hGerbe hAbelian U I K0
  have hshell_pre := congrArg (fun m => idInv ≫ m) hshell
  rw [← chosen_cover_identity_source_owner_tail_left_strip_identity_shell
    (𝒮 := 𝒮) hGerbe hAbelian U I K0]
  exact hshell_pre.trans
    (chosen_cover_identity_source_owner_tail_right_strip_identity_shell
      (𝒮 := 𝒮) hGerbe hAbelian U I K0)

/-- Helper for Lemma 8.11.8: the identity-pullback owner tail is the chosen-cover component
pulled through the `I.f ≫ 𝟙 U = I.f` mapComp shell. -/
theorem chosen_cover_identity_source_owner_tail
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (U : C) (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (K0 : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe (I.f ≫ 𝟙 U)).Arrow) :
    (chosen_cover_underlying_automorphism_sheaf_cover_iso
        (𝒮 := 𝒮) hGerbe hAbelian U K0.base).hom ≫
      (chosen_local_automorphism_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U K0.base)
        (K0.f ^*[canonicalPullbackChoice 𝒮.p]
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I))).hom ≫
      (automorphismUnderlyingSheafBaseChangeIso
        (𝒮 := 𝒮) hAbelian K0.f
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I)).inv =
    (((Cat.Hom.toNatIso
      ((J.pseudofunctorOver (Type (max u v))).mapComp'
        I.f.op.toLoc K0.f.op.toLoc (K0.f ≫ (I.f ≫ 𝟙 U)).op.toLoc
        (by simp [← Quiver.Hom.comp_toLoc, ← op_comp]))).app
      (chosen_cover_underlying_automorphism_sheaf
        (𝒮 := 𝒮) hGerbe hAbelian U)).hom) ≫
      ((J.pseudofunctorOver (Type (max u v))).map K0.f.op.toLoc).toFunctor.map
        (chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian U I).hom := by
  exact chosen_cover_identity_source_owner_tail_strip_identity_shell
    (𝒮 := 𝒮) hGerbe hAbelian U I K0

end CategoryTheory
