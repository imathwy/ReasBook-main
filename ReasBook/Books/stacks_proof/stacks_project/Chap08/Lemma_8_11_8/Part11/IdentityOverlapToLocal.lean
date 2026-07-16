import stacks_proof.stacks_project.Chap08.Lemma_8_11_8.Part11.IdentityCoherenceTools

universe u v w

namespace CategoryTheory

open StackInGroupoidsOver
open Opposite
open Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {𝒮 : StackInGroupoidsOver J}

/-- Helper for Lemma 8.11.8: in the identity-pullback cover over `I.f ≫ 𝟙 U`, the original
chosen-cover owner stored by a pullback-cover arrow is structurally the precomposition of `I` by
the explicit pullback-cover map.  This is only a structural equality; identity-pullback proofs
below keep `K0.base` as the primary owner. -/
private theorem chosen_cover_identity_pullback_base_eq_precomp
    (hGerbe : IsGerbe J 𝒮.p)
    (U : C) (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (K0 : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe (I.f ≫ 𝟙 U)).Arrow) :
    K0.base = I.precomp K0.f := by
  ext <;> simp

/-- Helper for Lemma 8.11.8: with the identity-pullback source owner made explicit, the overlap
map from the identity leg to `g` is exactly the source identity base-change, the chosen local
comparison, and the target base-change tail.  Keeping `I0` explicit avoids reducing through a
`K0.base` owner. -/
private theorem chosen_cover_identity_source_overlap_to_local_tail
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (U : C) (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    {Y0 : C} (g : Y0 ⟶ I.Y)
    (h0 : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) (g ≫ (I.f ≫ 𝟙 U))) :
    let I0 : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow :=
      ⟨Y0, g ≫ (I.f ≫ 𝟙 U), h0⟩
    automorphism_overlap_hom_of_locally_isomorphic_cover
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
        (g ≫ (I.f ≫ 𝟙 U)) (I₁ := I0) (I₂ := I) (𝟙 Y0) g
        (_hf₁ := by dsimp [I0]; simp) (_hf₂ := by simp) =
      (automorphismUnderlyingSheafBaseChangeIso
        (𝒮 := 𝒮) hAbelian (𝟙 Y0)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I0)).hom ≫
      (chosen_local_automorphism_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        ((𝟙 Y0) ^*[canonicalPullbackChoice 𝒮.p]
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I0))
        (g ^*[canonicalPullbackChoice 𝒮.p]
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I))).hom ≫
      (automorphismUnderlyingSheafBaseChangeIso
        (𝒮 := 𝒮) hAbelian g
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I)).inv := by
  intro I0
  let S :=
    local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
      (I₁ := I0) (I₂ := I) (𝟙 Y0) g
  haveI : (localizedSheafToCoverDescentEquivalence (J := J) S).functor.Faithful :=
    (localizedSheafToCoverDescentFullyFaithful (J := J) S).faithful
  apply Functor.map_injective (localizedSheafToCoverDescentEquivalence (J := J) S).functor
  apply Pseudofunctor.DescentData.hom_ext
  intro K
  rw [localizedSheafToCoverDescentEquivalence_functor_map_component]
  rw [automorphism_overlap_hom_secondary_cover_component
    (𝒮 := 𝒮) hGerbe hAbelian
    (S := chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
    (xS := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
    (q := g ≫ (I.f ≫ 𝟙 U)) (I₁ := I0) (I₂ := I)
    (f₁ := 𝟙 Y0) (f₂ := g)
    (hf₁ := by dsimp [I0]; simp) (hf₂ := by simp) (K := K)]
  rw [secondary_cover_descent_iso_on_local_overlap_hom_component_explicit
    (𝒮 := 𝒮) hGerbe hAbelian
    (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
    (I₁ := I0) (I₂ := I) (𝟙 Y0) g K]
  simp only [S, localizedSheafToCoverDescentEquivalence_functor_map_component,
    Functor.map_comp, Functor.mapIso_hom, Functor.mapIso_inv]
  have hlocal :=
    chosen_local_automorphism_iso_functor_map_eq_chosen_local_conjugation_component
      (𝒮 := 𝒮) hGerbe hAbelian
      ((𝟙 Y0) ^*[canonicalPullbackChoice 𝒮.p]
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I0))
      (g ^*[canonicalPullbackChoice 𝒮.p]
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I)) K
  rw [localizedSheafToCoverDescentEquivalence_functor_map_component] at hlocal
  let F := ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor
  let a :=
    F.map
      (automorphismUnderlyingSheafBaseChangeIso
        (𝒮 := 𝒮) hAbelian (𝟙 Y0)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I0)).hom
  let c :=
    F.map
      (automorphismUnderlyingSheafBaseChangeIso
        (𝒮 := 𝒮) hAbelian g
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I)).inv
  simpa [F, a, c, local_overlap_source_object, local_overlap_target_object,
    local_overlap_conjugation_iso, local_overlap_isomorphism, Category.assoc] using
    (congrArg (fun m ↦ a ≫ m ≫ c) hlocal).symm

/-- Helper for Lemma 8.11.8: changing the source of a chosen-local automorphism comparison by a
global fiber isomorphism conjugates the transported sheaf comparison.  This is the source-side
analogue of the target-side adapter used later in Part15. -/
private theorem chosen_local_automorphism_iso_conj_source_of_iso_part11
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} (x y A : 𝒮.p.Fiber U) (e : x ≅ y) :
    automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian e.hom ≪≫
        chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian y A =
      chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian x A := by
  let Sx := chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe x A
  let Sy := chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe y A
  let S := Sx ⊓ Sy
  apply Iso.ext
  haveI : (localizedSheafToCoverDescentEquivalence (J := J) S).functor.Faithful :=
    (localizedSheafToCoverDescentFullyFaithful (J := J) S).faithful
  apply Functor.map_injective (localizedSheafToCoverDescentEquivalence (J := J) S).functor
  apply Pseudofunctor.DescentData.hom_ext
  intro K
  let Kx : Sx.Arrow := ⟨K.Y, K.f, K.hf.1⟩
  let Ky : Sy.Arrow := ⟨K.Y, K.f, K.hf.2⟩
  have hx :
      ((localizedSheafToCoverDescentEquivalence (J := J) S).functor.map
        (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian x A).hom).hom K =
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f x).hom ≫
          (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe x A Kx).hom).hom ≫
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f A).inv := by
    rw [localizedSheafToCoverDescentEquivalence_functor_map_component]
    simpa [Kx] using
      chosen_local_automorphism_iso_functor_map_eq_chosen_local_conjugation_component
        (𝒮 := 𝒮) hGerbe hAbelian x A Kx
  have hy :
      ((localizedSheafToCoverDescentEquivalence (J := J) S).functor.map
        (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian y A).hom).hom K =
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f y).hom ≫
          (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe y A Ky).hom).hom ≫
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f A).inv := by
    rw [localizedSheafToCoverDescentEquivalence_functor_map_component]
    simpa [Ky] using
      chosen_local_automorphism_iso_functor_map_eq_chosen_local_conjugation_component
        (𝒮 := 𝒮) hGerbe hAbelian y A Ky
  simp only [Iso.trans_hom, Functor.map_comp, Pseudofunctor.DescentData.comp_hom]
  rw [hx, hy,
    localizedSheafToCoverDescentEquivalence_functor_map_component,
    automorphismUnderlyingSheafConj_pullbackFunctor_map (𝒮 := 𝒮) hAbelian K.f e.hom]
  let Bx := automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f x
  let By := automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f y
  let BA := automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f A
  let Ce := automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
    (((canonicalPullbackChoice 𝒮.p).pullbackFunctor K.f).mapIso
      (asIso e.hom)).hom
  let Cy := automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
    (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe y A Ky).hom
  let Cx := automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
    (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe x A Kx).hom
  have hconj :
      Ce.hom ≫ Cy.hom = Cx.hom := by
    have hconjIso : Ce ≪≫ Cy = Cx := by
      dsimp [Ce, Cy, Cx]
      exact
        (automorphismUnderlyingSheafConj_comp (𝒮 := 𝒮) hAbelian
          (((canonicalPullbackChoice 𝒮.p).pullbackFunctor K.f).map e.hom)
          (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe y A Ky).hom).symm.trans
          (automorphismUnderlyingSheafConj_eq_of_parallel (𝒮 := 𝒮) hAbelian
            ((((canonicalPullbackChoice 𝒮.p).pullbackFunctor K.f).map e.hom) ≫
              (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe y A Ky).hom)
            (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe x A Kx).hom)
    simpa only [Iso.trans_hom] using congrArg Iso.hom hconjIso
  change ((Bx.hom ≫ Ce.hom ≫ By.inv) ≫ By.hom ≫ Cy.hom ≫ BA.inv) =
    Bx.hom ≫ Cx.hom ≫ BA.inv
  calc
    ((Bx.hom ≫ Ce.hom ≫ By.inv) ≫ By.hom ≫ Cy.hom ≫ BA.inv) =
        Bx.hom ≫ Ce.hom ≫ By.inv ≫ By.hom ≫ Cy.hom ≫ BA.inv := by
      simp only [Category.assoc]
    _ = Bx.hom ≫ Ce.hom ≫ Cy.hom ≫ BA.inv := by
      have hcancelTail : By.inv ≫ By.hom ≫ Cy.hom ≫ BA.inv = Cy.hom ≫ BA.inv := by
        simpa only [Category.assoc] using (Iso.inv_hom_id_assoc By (Cy.hom ≫ BA.inv))
      simpa only [Category.assoc] using
        congrArg (fun m => Bx.hom ≫ Ce.hom ≫ m) hcancelTail
    _ = Bx.hom ≫ Cx.hom ≫ BA.inv := by
      have htail : Ce.hom ≫ Cy.hom ≫ BA.inv = Cx.hom ≫ BA.inv := by
        simpa only [Category.assoc] using congrArg (fun m => m ≫ BA.inv) hconj
      simpa only [Category.assoc] using congrArg (fun m => Bx.hom ≫ m) htail

end CategoryTheory
