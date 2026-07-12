import StacksProject_2024.Chap08.Lemma_8_11_8.Part11.IdentityOverlapToLocal
import StacksProject_2024.Chap08.Lemma_8_11_8.Part11.TransitionSquare
import StacksProject_2024.Chap08.Lemma_8_11_8.Part11.TransitionComponentRaw
import StacksProject_2024.Chap08.Lemma_8_11_8.Part11.IdentityBaseChange
import StacksProject_2024.Chap08.Lemma_8_11_8.Part11.IdentitySourceOwnerTail

universe u v w

namespace CategoryTheory

open StackInGroupoidsOver
open Opposite
open Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {𝒮 : StackInGroupoidsOver J}

/-- Helper for Lemma 8.11.8: explicit-`K0` owner bridge for the identity pullback component.
The overlap specialization is intentionally phrased with `I₁ := K0.base`, `I₂ := I`,
`g₁ := 𝟙 K0.Y`, and `g₂ := K0.f`; `K0.base` remains the main owner throughout. -/
private theorem chosen_cover_identity_source_owner_bridge
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (U : C) (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (K0 : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe (I.f ≫ 𝟙 U)).Arrow) :
    (pullback_cover_source_component_iso
        (𝒮 := 𝒮) hGerbe hAbelian (I.f ≫ 𝟙 U) K0).hom ≫
      (chosen_local_automorphism_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U K0.base)
        (K0.f ^*[canonicalPullbackChoice 𝒮.p]
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I))).hom ≫
      (automorphismUnderlyingSheafBaseChangeIso
        (𝒮 := 𝒮) hAbelian K0.f
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I)).inv =
    ((J.pseudofunctorOver (Type (max u v))).map K0.f.op.toLoc).toFunctor.map
        ((J.overMapPullbackCongr (Type (max u v))
          (by simp : I.f ≫ 𝟙 U = I.f)).hom.app
            (chosen_cover_underlying_automorphism_sheaf
              (𝒮 := 𝒮) hGerbe hAbelian U)) ≫
      ((J.pseudofunctorOver (Type (max u v))).map K0.f.op.toLoc).toFunctor.map
        (chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian U I).hom := by
  let G := chosen_cover_underlying_automorphism_sheaf (𝒮 := 𝒮) hGerbe hAbelian U
  let F := ((J.pseudofunctorOver (Type (max u v))).map K0.f.op.toLoc).toFunctor
  let h01 : I.f ≫ 𝟙 U = I.f := by simp
  dsimp [pullback_cover_source_component_iso]
  let a :=
    (((Cat.Hom.toNatIso
      ((J.pseudofunctorOver (Type (max u v))).mapComp'
        (I.f ≫ 𝟙 U).op.toLoc K0.f.op.toLoc (K0.f ≫ (I.f ≫ 𝟙 U)).op.toLoc
        (by simp [← Quiver.Hom.comp_toLoc, ← op_comp]))).app G).inv)
  let b :=
    (chosen_cover_underlying_automorphism_sheaf_cover_iso
      (𝒮 := 𝒮) hGerbe hAbelian U K0.base).hom
  let c :=
    (chosen_local_automorphism_iso
      (𝒮 := 𝒮) hGerbe hAbelian
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U K0.base)
      (K0.f ^*[canonicalPullbackChoice 𝒮.p]
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I))).hom
  let d :=
    (automorphismUnderlyingSheafBaseChangeIso
      (𝒮 := 𝒮) hAbelian K0.f
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I)).inv
  change (a ≫ b) ≫ c ≫ d =
    F.map ((J.overMapPullbackCongr (Type (max u v)) h01).hom.app G) ≫
      F.map (chosen_cover_underlying_automorphism_sheaf_cover_iso
        (𝒮 := 𝒮) hGerbe hAbelian U I).hom
  rw [show (a ≫ b) ≫ c ≫ d = a ≫ b ≫ c ≫ d by rfl]
  dsimp [b, c, d]
  change a ≫
      ((chosen_cover_underlying_automorphism_sheaf_cover_iso
        (𝒮 := 𝒮) hGerbe hAbelian U K0.base).hom ≫
      (chosen_local_automorphism_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U K0.base)
        (K0.f ^*[canonicalPullbackChoice 𝒮.p]
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I))).hom ≫
      (automorphismUnderlyingSheafBaseChangeIso
        (𝒮 := 𝒮) hAbelian K0.f
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I)).inv) =
    F.map ((J.overMapPullbackCongr (Type (max u v)) h01).hom.app G) ≫
      F.map (chosen_cover_underlying_automorphism_sheaf_cover_iso
        (𝒮 := 𝒮) hGerbe hAbelian U I).hom
  rw [show
    a ≫
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
      a ≫
        ((chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian U K0.base).hom ≫
        (chosen_local_automorphism_iso
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U K0.base)
          (K0.f ^*[canonicalPullbackChoice 𝒮.p]
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I))).hom ≫
        (automorphismUnderlyingSheafBaseChangeIso
          (𝒮 := 𝒮) hAbelian K0.f
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I)).inv) by
    rfl]
  erw [chosen_cover_identity_source_owner_tail (𝒮 := 𝒮) hGerbe hAbelian U I K0]
  simpa [G, F, h01, Category.assoc] using
    overMapPullback_mapComp'_inv_hom_congr_assoc
      (J := J) (f₀ := I.f ≫ 𝟙 U) (f₁ := I.f)
      h01 K0.f G
      (F.map (chosen_cover_underlying_automorphism_sheaf_cover_iso
        (𝒮 := 𝒮) hGerbe hAbelian U I).hom)

/-- Helper for Lemma 8.11.8: the identity pullback/local-object component before cancelling the
fixed chosen-cover counit. -/
private theorem chosen_cover_identity_pullback_to_local_object_component_hom
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (U : C) (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (K : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe (I.f ≫ 𝟙 U)).Arrow) :
    (pullback_cover_local_object_component_iso
        (𝒮 := 𝒮) hGerbe hAbelian (I.f ≫ 𝟙 U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I) K).hom =
      ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
        ((J.overMapPullbackCongr (Type (max u v))
          (by simp : I.f ≫ 𝟙 U = I.f)).hom.app
            (chosen_cover_underlying_automorphism_sheaf
              (𝒮 := 𝒮) hGerbe hAbelian U)) ≫
      ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
        (chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian U I).hom := by
  let G :=
    chosen_cover_underlying_automorphism_sheaf
      (𝒮 := 𝒮) hGerbe hAbelian U
  dsimp [pullback_cover_local_object_component_iso]
  simpa [Iso.trans_hom, Iso.symm_hom, Category.assoc] using
    chosen_cover_identity_source_owner_bridge
      (𝒮 := 𝒮) hGerbe hAbelian U I K

/-- Helper for Lemma 8.11.8: the component form of the identity pullback-to-local-object
source shell.  After faithful descent on the pullback cover of `I.f ≫ 𝟙 U`, this is the only
remaining identity adapter: one pullback-cover component, followed by the fixed chosen-cover
counit inverse, is the `overMapPullbackCongr` component. -/
private theorem chosen_cover_identity_pullback_to_local_object_component_congr
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (U : C) (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (K : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe (I.f ≫ 𝟙 U)).Arrow) :
    (pullback_cover_local_object_component_iso
        (𝒮 := 𝒮) hGerbe hAbelian (I.f ≫ 𝟙 U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I) K).hom ≫
      ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
        (chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian U I).inv =
    ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
      ((J.overMapPullbackCongr (Type (max u v))
        (by simp : I.f ≫ 𝟙 U = I.f)).hom.app
          (chosen_cover_underlying_automorphism_sheaf
            (𝒮 := 𝒮) hGerbe hAbelian U)) := by
  rw [chosen_cover_identity_pullback_to_local_object_component_hom
    (𝒮 := 𝒮) hGerbe hAbelian U I K]
  let F := ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor
  let a :=
    ((J.overMapPullbackCongr (Type (max u v))
      (by simp : I.f ≫ 𝟙 U = I.f)).hom.app
        (chosen_cover_underlying_automorphism_sheaf
          (𝒮 := 𝒮) hGerbe hAbelian U))
  let e :=
    chosen_cover_underlying_automorphism_sheaf_cover_iso
      (𝒮 := 𝒮) hGerbe hAbelian U I
  change (F.map a ≫ F.map e.hom) ≫ F.map e.inv = F.map a
  calc
    (F.map a ≫ F.map e.hom) ≫ F.map e.inv =
        F.map a ≫ (F.map e.hom ≫ F.map e.inv) := by
      simp only [Category.assoc]
    _ = F.map a ≫ F.map (e.hom ≫ e.inv) := by
      rw [← Functor.map_comp]
    _ = F.map a := by
      have he : e.hom ≫ e.inv = 𝟙 _ := e.hom_inv_id
      have hmap : F.map (e.hom ≫ e.inv) = F.map (𝟙 _) := congrArg F.map he
      calc
        F.map a ≫ F.map (e.hom ≫ e.inv) = F.map a ≫ F.map (𝟙 _) := by
          exact congrArg (fun m ↦ F.map a ≫ m) hmap
        _ = F.map a := by
          exact Category.comp_id (F.map a)

/-- Helper for Lemma 8.11.8: the identity-pullback local-object comparison, after the fixed
chosen-cover counit is removed, is exactly the canonical congruence
`overMapPullback (I.f ≫ 𝟙 U) ≅ overMapPullback I.f`.  This is the narrow source-shell adapter
left by the `ρ_id` calculation. -/
private theorem chosen_cover_identity_pullback_to_local_object_cover_inv
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (U : C) (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow) :
    (chosen_cover_pullback_to_local_object_iso
        (𝒮 := 𝒮) hGerbe hAbelian (q := I.f ≫ 𝟙 U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I)).hom ≫
      (chosen_cover_underlying_automorphism_sheaf_cover_iso
        (𝒮 := 𝒮) hGerbe hAbelian U I).inv =
    ((J.overMapPullbackCongr (Type (max u v))
        (by simp : I.f ≫ 𝟙 U = I.f)).hom.app
      (chosen_cover_underlying_automorphism_sheaf
        (𝒮 := 𝒮) hGerbe hAbelian U)) := by
  -- Reduce the identity source-shell adapter to the one remaining component comparison on the
  -- pullback cover of `I.f ≫ 𝟙 U`.
  let S := chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe (I.f ≫ 𝟙 U)
  haveI : (localizedSheafToCoverDescentEquivalence (J := J) S).functor.Faithful :=
    (localizedSheafToCoverDescentFullyFaithful (J := J) S).faithful
  apply Functor.map_injective (localizedSheafToCoverDescentEquivalence (J := J) S).functor
  rw [Functor.map_comp]
  have hpb :
      (localizedSheafToCoverDescentEquivalence (J := J) S).functor.map
        (chosen_cover_pullback_to_local_object_iso
          (𝒮 := 𝒮) hGerbe hAbelian (q := I.f ≫ 𝟙 U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I)).hom =
      (pullback_cover_local_object_comparison_descent_iso
        (𝒮 := 𝒮) hGerbe hAbelian (I.f ≫ 𝟙 U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I)).hom := by
    simpa [S, chosen_cover_pullback_to_local_object_iso] using
      localizedSheafTransportIsoOfCoverDescentIso_functor_map (J := J)
        (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe (I.f ≫ 𝟙 U))
        (pullback_cover_local_object_comparison_descent_iso
          (𝒮 := 𝒮) hGerbe hAbelian (I.f ≫ 𝟙 U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I))
  rw [hpb]
  apply Pseudofunctor.DescentData.hom_ext
  intro K
  rw [Pseudofunctor.DescentData.comp_hom,
    localizedSheafToCoverDescentEquivalence_functor_map_component]
  -- The only remaining source-faithful content is the named component normal form.
  exact chosen_cover_identity_pullback_to_local_object_component_congr
    (𝒮 := 𝒮) hGerbe hAbelian U I K

/-- Helper for Lemma 8.11.8: the identity transition source shell is the canonical
`overMapPullbackId` comparison after composing the composite-pullback comparison with the
local-object/counit adapter. -/
private theorem chosen_cover_identity_transition_source_shell
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (U : C) (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow) :
    (chosen_cover_pulled_component_composite_pullback_iso
        (𝒮 := 𝒮) hGerbe hAbelian (𝟙 U) I).hom ≫
      (chosen_cover_pullback_to_local_object_iso
        (𝒮 := 𝒮) hGerbe hAbelian (I.f ≫ 𝟙 U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I)).hom ≫
      (chosen_cover_underlying_automorphism_sheaf_cover_iso
        (𝒮 := 𝒮) hGerbe hAbelian U I).inv =
    ((J.pseudofunctorOver (Type (max u v))).map I.f.op.toLoc).toFunctor.map
      (((J.overMapPullbackId (Type (max u v)) U).app
        (chosen_cover_underlying_automorphism_sheaf
          (𝒮 := 𝒮) hGerbe hAbelian U)).hom) := by
  slice_lhs 2 3 =>
    erw [chosen_cover_identity_pullback_to_local_object_cover_inv
      (𝒮 := 𝒮) hGerbe hAbelian U I]
  exact overMapPullbackComp_hom_congr_comp_id
    (J := J) I.f
    (chosen_cover_underlying_automorphism_sheaf
      (𝒮 := 𝒮) hGerbe hAbelian U)

/-- Helper for Lemma 8.11.8: the identity transition law reduced to one chosen-cover component.
The source proof's `ρ_id` assertion is exactly this local comparison after the canonical
`overMapPullbackId` shell is exposed by the chosen-cover descent functor. -/
theorem chosen_cover_descent_transition_component_iso_id_hom
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (U : C) (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow) :
    (chosen_cover_descent_transition_component_iso
      (𝒮 := 𝒮) hGerbe hAbelian (𝟙 U) I).hom =
      ((J.pseudofunctorOver (Type (max u v))).map I.f.op.toLoc).toFunctor.map
        (((J.overMapPullbackId (Type (max u v)) U).app
          (chosen_cover_underlying_automorphism_sheaf
            (𝒮 := 𝒮) hGerbe hAbelian U)).hom) := by
  rw [chosen_cover_descent_transition_component_iso_hom_raw]
  exact chosen_cover_identity_transition_source_shell
    (𝒮 := 𝒮) hGerbe hAbelian U I

end CategoryTheory
