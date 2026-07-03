import Mathlib
import Mathlib.CategoryTheory.Sites.Over
import stacks_project.Chap07.Lemma_7_26_5
import stacks_project.Chap07.Lemma_7_26_6
import stacks_project.Chap08.Lemma_8_3_7
import stacks_project.Chap08.Definition_8_5_5
import stacks_project.Chap08.Definition_8_11_1
import stacks_project.Chap08.Lemma_8_11_8.Part04

universe u v w

namespace CategoryTheory

open StackInGroupoidsOver
open Opposite
open Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {𝒮 : StackInGroupoidsOver J}
/-- Helper for Lemma 8.11.8: on one refinement member `I`, the first-branch self-leg
common-owner shell at `op (Over.mk Ī.toMiddleHom)` can be rewritten to the shared-owner
`qI := I.Y.hom` shell evaluated at `op (Over.mk (𝟙 I.Y.left))`, while keeping the same owner leg
`Ī.toMiddleHom`. This isolates the remaining owner-change step before endpoint-independence is
used. -/
private theorem chosen_cover_refinement_member_first_branch_self_leg_to_qI_shell
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U Y : C}
    (q : Y ⟶ U)
    {I₁ I₂ I₃ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) (f₃ : Y ⟶ I₃.Y)
    (_hf₁ : f₁ ≫ I₁.f = q) (_hf₂ : f₂ ≫ I₂.f = q) (_hf₃ : f₃ ≫ I₃.f = q)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃).Arrow)
    (T : (Over K.Y)ᵒᵖ)
    (α : (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁))).1.obj T)
    {B : J.Cover T.unop.left}
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow) (Ī : B.Arrow) (hĪ : Ī.f = I.f.left) :
    let qI : I.Y.left ⟶ K.Y := I.Y.hom
    let K₁₂ :
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₁) (K.f ≫ f₂)).Arrow :=
      Ī.fromMiddle
    let αI :=
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (K.f ^*[canonicalPullbackChoice 𝒮.p]
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁))).1.map I.f.op α
    ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (local_overlap_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
            (K.f ≫ f₁) (K.f ≫ f₂) K₁₂.f (𝟙 K₁₂.Y)).hom).hom).1.app
        (op (Over.mk Ī.toMiddleHom)))
      αI =
      (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (local_overlap_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
            (K.f ≫ f₁) (K.f ≫ f₂) qI Ī.toMiddleHom
            (by
              simpa [K₁₂, qI, T, hĪ, Category.assoc] using
                congrArg (fun k ↦ k ≫ T.unop.hom) Ī.middle_spec)).hom).hom).1.app
        (op (Over.mk (𝟙 I.Y.left))))
      αI := by
  -- Route correction: isolate only the first-branch owner change from the self-leg owner `K₁₂.f`
  -- to the shared owner `qI`. Endpoint-independence for the leg itself is handled later.
  dsimp [qI, K₁₂, αI]
  simpa using
    (local_overlap_common_owner_self_leg_app_to_shared_owner_app
      (𝒮 := 𝒮) hGerbe hAbelian
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
      (K.f ≫ f₁) (K.f ≫ f₂) I.Y.hom Ī.toMiddleHom
      (by
        simpa [qI, K₁₂, T, hĪ, Category.assoc] using
          congrArg (fun k ↦ k ≫ T.unop.hom) Ī.middle_spec)
      ((automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (K.f ^*[canonicalPullbackChoice 𝒮.p]
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁))).1.map I.f.op α))

/-- Helper for Lemma 8.11.8: after restricting the direct `(f₁,f₃)` branch along one refinement
member `I`, the remaining term is already the pulled direct conjugation over the shared owner
`qI := I.Y.hom`, evaluated on the identity object of `C / I.Y.left`. This isolates the direct
branch from the pairwise-shell comparison in the final memberwise cocycle calculation. -/
private theorem chosen_cover_refinement_member_direct_branch_restrict_eq_pulled_direct_app
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U Y : C}
    (q : Y ⟶ U)
    {I₁ I₂ I₃ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) (f₃ : Y ⟶ I₃.Y)
    (_hf₁ : f₁ ≫ I₁.f = q) (_hf₂ : f₂ ≫ I₂.f = q) (_hf₃ : f₃ ≫ I₃.f = q)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃).Arrow)
    (T : (Over K.Y)ᵒᵖ)
    (α : (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁))).1.obj T)
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow) :
    let qI : I.Y.left ⟶ K.Y := I.Y.hom
    let αI :=
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (K.f ^*[canonicalPullbackChoice 𝒮.p]
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁))).1.map I.f.op α
    (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₃))).1.map I.f.op
        ((((local_overlap_conjugation_iso
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃ K).hom).1.app T) α) =
      (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          ((((canonicalPullbackChoice 𝒮.p).pullbackFunctor qI).mapIso
            (local_overlap_isomorphism
              (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃ K)).hom)).hom).1.app
        (op (Over.mk (𝟙 I.Y.left))))
      αI := by
  let qI : I.Y.left ⟶ K.Y := I.Y.hom
  let αI :=
    (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁))).1.map I.f.op α
  have hRestrict :
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (K.f ^*[canonicalPullbackChoice 𝒮.p]
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₃))).1.map I.f.op
          ((((local_overlap_conjugation_iso
            (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃ K).hom).1.app T) α) =
        ((((local_overlap_conjugation_iso
            (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃ K).hom).1.app
          (op I.Y))
        αI) := by
    -- First remove the outer restriction from the direct `(f₁,f₃)` branch by naturality.
    simpa [αI] using
      sheaf_hom_app_restrict_eq
        ((local_overlap_conjugation_iso
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃ K).hom)
        I.f α
  -- Route correction: the direct branch does not need a new refinement argument. After the outer
  -- naturality rewrite, evaluating at `op I.Y` is exactly the pulled direct conjugation over the
  -- shared owner `qI`, read on the identity object of `C / I.Y.left`.
  calc
    (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₃))).1.map I.f.op
        ((((local_overlap_conjugation_iso
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃ K).hom).1.app T) α)
        =
      ((((local_overlap_conjugation_iso
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃ K).hom).1.app
        (op I.Y))
      αI) := hRestrict
    _ =
      (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          ((((canonicalPullbackChoice 𝒮.p).pullbackFunctor qI).mapIso
            (local_overlap_isomorphism
              (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃ K)).hom)).hom).1.app
        (op (Over.mk (𝟙 I.Y.left))))
      αI := by
        simpa [qI, αI, local_overlap_conjugation_iso, automorphismUnderlyingSheafConj,
          automorphismUnderlyingSheafConj_hom, automorphismUnderlyingSheaf,
          automorphismAddCommSheafConj, automorphismAddCommPresheaf, automorphismSection,
          automorphismSectionObj]

/-- Helper for Lemma 8.11.8: after fixing `T` and one section `α`, the source-faithful remaining
task is to choose a common refinement cover of `qT := T.unop.hom` in `C / K.Y` and prove that the
two candidate target sections agree after restriction to every member of that cover. -/
private theorem chosen_cover_pairwise_descent_comp_eq_on_refinement_member
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U Y : C}
    (q : Y ⟶ U)
    {I₁ I₂ I₃ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) (f₃ : Y ⟶ I₃.Y)
    (_hf₁ : f₁ ≫ I₁.f = q) (_hf₂ : f₂ ≫ I₂.f = q) (_hf₃ : f₃ ≫ I₃.f = q)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃).Arrow)
    (T : (Over K.Y)ᵒᵖ)
    (α : (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁))).1.obj T)
    {B : J.Cover T.unop.left}
    {R : (J.over K.Y).Cover T.unop}
    (hR : (R : Sieve T.unop) = (Sieve.overEquiv T.unop).symm (B : Sieve T.unop.left))
    (I : R.Arrow) (Ī : B.Arrow) (hĪ : Ī.f = I.f.left) :
    (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₃))).1.map I.f.op
        (((((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
              (automorphism_overlap_hom_of_locally_isomorphic_cover
                (𝒮 := 𝒮) hGerbe hAbelian
                (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₁ f₂)) ≫
            (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
              (automorphism_overlap_hom_of_locally_isomorphic_cover
                (𝒮 := 𝒮) hGerbe hAbelian
                (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₂ f₃))).1.app T) α) =
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (K.f ^*[canonicalPullbackChoice 𝒮.p]
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₃))).1.map I.f.op
        ((((local_overlap_conjugation_iso
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃ K).hom).1.app T) α) := by
  let qT := T.unop.hom
  let qI : I.Y.left ⟶ K.Y := I.Y.hom
  let S12 :=
    local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₁) (K.f ≫ f₂)
  let S23 :=
    local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₂) (K.f ≫ f₃)
  have hqI : I.f.left ≫ qT = qI := by
    -- The refinement member lives over `T.unop`, so its left map followed by `qT` is the owner
    -- arrow `qI : I.Y.left ⟶ K.Y`.
    simpa [qT, qI] using Over.w I.f
  let K₁₂ : S12.Arrow := Ī.fromMiddle
  let K₂₃ : S23.Arrow := Ī.toMiddle.base
  have hg₁₂ : Ī.toMiddleHom ≫ K₁₂.f = qI := by
    -- The first branch of the bind cover restricts the `(f₁,f₂)` overlap cover to the owner `qI`.
    simpa [K₁₂, qI, qT, hĪ, Category.assoc] using congrArg (fun k ↦ k ≫ qT) Ī.middle_spec
  have hg₂₃ : Ī.toMiddle.base.f = qI := by
    -- The second branch of the bind cover is already over the same owner `qI`.
    simpa [K₂₃, qI, qT, hĪ, GrothendieckTopology.Cover.Arrow.base, Category.assoc] using
      congrArg (fun k ↦ k ≫ qT) Ī.middle_spec
  let αI :=
    (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁))).1.map I.f.op α
  -- Route correction: the common refinement is now fixed. The remaining source-faithful task is
  -- only the owner-object alignment on this one member `I`.
  have hFirstRestrict :
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (K.f ^*[canonicalPullbackChoice 𝒮.p]
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂))).1.map I.f.op
          ((((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
                (automorphism_overlap_hom_of_locally_isomorphic_cover
                  (𝒮 := 𝒮) hGerbe hAbelian
                  (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                  (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₁ f₂)).1.app T) α) =
        ((((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
              (automorphism_overlap_hom_of_locally_isomorphic_cover
                (𝒮 := 𝒮) hGerbe hAbelian
                (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₁ f₂)).1.app
            (op I.Y)) αI) := by
    -- First peel off the outer restriction from the `(f₁,f₂)` branch by naturality.
    simpa [αI] using
      sheaf_hom_app_restrict_eq
        ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          (automorphism_overlap_hom_of_locally_isomorphic_cover
            (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₁ f₂)))
        I.f α
  have hSecondRestrict :
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (K.f ^*[canonicalPullbackChoice 𝒮.p]
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₃))).1.map I.f.op
          ((((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
                (automorphism_overlap_hom_of_locally_isomorphic_cover
                  (𝒮 := 𝒮) hGerbe hAbelian
                  (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                  (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₂ f₃)).1.app T)
            ((((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
                  (automorphism_overlap_hom_of_locally_isomorphic_cover
                    (𝒮 := 𝒮) hGerbe hAbelian
                    (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₁ f₂)).1.app T) α)) =
        ((((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
              (automorphism_overlap_hom_of_locally_isomorphic_cover
                (𝒮 := 𝒮) hGerbe hAbelian
                (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₂ f₃)).1.app
            (op I.Y))
          ((automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (K.f ^*[canonicalPullbackChoice 𝒮.p]
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂))).1.map I.f.op
              ((((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
                    (automorphism_overlap_hom_of_locally_isomorphic_cover
                      (𝒮 := 𝒮) hGerbe hAbelian
                      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₁ f₂)).1.app T) α))) := by
    -- Then peel off the outer restriction from the `(f₂,f₃)` branch in the same way.
    simpa using
      sheaf_hom_app_restrict_eq
        ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          (automorphism_overlap_hom_of_locally_isomorphic_cover
            (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₂ f₃)))
        I.f
        ((((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
              (automorphism_overlap_hom_of_locally_isomorphic_cover
                (𝒮 := 𝒮) hGerbe hAbelian
                (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₁ f₂)).1.app T) α)
  have hObj12 : (Over.map K₁₂.f).obj (Over.mk Ī.toMiddleHom) = I.Y := by
    -- The first refinement leg lands on the fixed owner object `I.Y`.
    simpa [qI] using over_map_obj_mk_eq K₁₂.f Ī.toMiddleHom qI hg₁₂
  have hObj23 : (Over.map K₂₃.f).obj (Over.mk (𝟙 I.Y.left)) = I.Y := by
    -- The second refinement leg is the identity over the same owner `I.Y.left`.
    simpa [qI] using over_map_obj_mk_eq K₂₃.f (𝟙 I.Y.left) qI hg₂₃
  have hObj12op :
      op ((Over.map K₁₂.f).obj (Over.mk Ī.toMiddleHom)) = op I.Y := by
    -- Move the first owner-object equality to the opposite slice object expected by `.app`.
    simpa [qI] using over_map_obj_mk_eq_op K₁₂.f Ī.toMiddleHom qI hg₁₂
  have hObj23op :
      op ((Over.map K₂₃.f).obj (Over.mk (𝟙 I.Y.left))) = op I.Y := by
    -- Move the second owner-object equality to the opposite slice object as well.
    simpa [qI] using over_map_obj_mk_eq_op K₂₃.f (𝟙 I.Y.left) qI hg₂₃
  let βI :=
    (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂))).1.map I.f.op
      ((((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
            (automorphism_overlap_hom_of_locally_isomorphic_cover
              (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₁ f₂)).1.app T) α)
  have hFirstMapToOwner :=
    chosen_cover_refinement_member_first_branch_map_app_to_owner
      (𝒮 := 𝒮) hGerbe hAbelian q f₁ f₂ f₃ _hf₁ _hf₂ _hf₃ K T α
      (B := B) (R := R) I Ī hĪ
  have hSecondMapToOwner :=
    chosen_cover_refinement_member_second_branch_map_app_to_owner
      (𝒮 := 𝒮) hGerbe hAbelian q f₁ f₂ f₃ _hf₁ _hf₂ _hf₃ K T α
      (B := B) (R := R) I Ī hĪ
  have hFirstQILeg :
      (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (local_overlap_common_owner_isomorphism
              (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
              (K.f ≫ f₁) (K.f ≫ f₂) qI Ī.toMiddleHom hg₁₂).hom).hom).1.app
          (op (Over.mk (𝟙 I.Y.left))))
        αI =
        (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (local_overlap_common_owner_isomorphism
              (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
              (K.f ≫ f₁) (K.f ≫ f₂) qI (𝟙 I.Y.left) (by simp [qI])).hom).hom).1.app
          (op (Over.mk (𝟙 I.Y.left))))
        αI := by
    -- The first branch already lives over the shared owner `qI`; only the chosen owner leg can
    -- still vary, and endpoint-independence removes that variation.
    simpa [qI, αI] using
      chosen_cover_refinement_member_first_branch_qI_leg_eq_identity_leg
        (𝒮 := 𝒮) hGerbe hAbelian q f₁ f₂ f₃ _hf₁ _hf₂ _hf₃ K T α
        (B := B) (R := R) I Ī hĪ
  have hSecondQIShell :
      (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (local_overlap_common_owner_isomorphism
              (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
              (K.f ≫ f₂) (K.f ≫ f₃) K₂₃.f (𝟙 K₂₃.Y)).hom).hom).1.app
          (op (Over.mk (𝟙 I.Y.left))))
        βI =
        (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (local_overlap_common_owner_isomorphism
              (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
              (K.f ≫ f₂) (K.f ≫ f₃) qI (𝟙 I.Y.left) (by simp [qI])).hom).hom).1.app
          (op (Over.mk (𝟙 I.Y.left))))
        βI := by
    -- The second branch is already the shared-owner shell after unfolding `K₂₃`.
    simpa [qI, K₂₃, βI] using
      chosen_cover_refinement_member_second_branch_qI_shell
        (𝒮 := 𝒮) hGerbe hAbelian q f₁ f₂ f₃ _hf₁ _hf₂ _hf₃ K T α
        (B := B) (R := R) I Ī hĪ
  have hFirstSelfLeg :
      βI =
        ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (local_overlap_common_owner_isomorphism
              (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
              (K.f ≫ f₁) (K.f ≫ f₂) K₁₂.f (𝟙 K₁₂.Y)).hom).hom).1.app
          (op (Over.mk Ī.toMiddleHom)))
        αI := by
    -- Package the already-solved first-branch naturality and owner-object transport.
    simpa [K₁₂, βI, αI] using
      chosen_cover_refinement_member_first_branch_restrict_eq_self_leg_shell
        (𝒮 := 𝒮) hGerbe hAbelian q f₁ f₂ f₃ _hf₁ _hf₂ _hf₃ K T α
        (B := B) (R := R) I Ī hĪ
  have hSecondShared :
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (K.f ^*[canonicalPullbackChoice 𝒮.p]
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₃))).1.map I.f.op
          (((((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
                (automorphism_overlap_hom_of_locally_isomorphic_cover
                  (𝒮 := 𝒮) hGerbe hAbelian
                  (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                  (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₁ f₂)) ≫
              (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
                (automorphism_overlap_hom_of_locally_isomorphic_cover
                  (𝒮 := 𝒮) hGerbe hAbelian
                  (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                  (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₂ f₃))).1.app T) α) =
        (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (local_overlap_common_owner_isomorphism
              (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
              (K.f ≫ f₂) (K.f ≫ f₃) qI (𝟙 I.Y.left) (by simp [qI])).hom).hom).1.app
          (op (Over.mk (𝟙 I.Y.left))))
        βI := by
    -- The second branch is now fully normalized to the shared-owner `qI` shell.
    simpa [qI, K₂₃, βI] using
      chosen_cover_refinement_member_second_branch_restrict_eq_qI_shell
        (𝒮 := 𝒮) hGerbe hAbelian q f₁ f₂ f₃ _hf₁ _hf₂ _hf₃ K T α
        (B := B) (R := R) I Ī hĪ
  have hFirstShared :
      βI =
        (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (local_overlap_common_owner_isomorphism
              (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
              (K.f ≫ f₁) (K.f ≫ f₂) qI (𝟙 I.Y.left)
              (by simp [qI])).hom).hom).1.app
          (op (Over.mk (𝟙 I.Y.left))))
        αI := by
    -- First move the first branch from its self-leg owner to the shared owner `qI`, then remove
    -- the remaining choice of owner leg by endpoint-independence.
    calc
      βI =
        (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (local_overlap_common_owner_isomorphism
              (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
              (K.f ≫ f₁) (K.f ≫ f₂) qI Ī.toMiddleHom hg₁₂).hom).hom).1.app
          (op (Over.mk (𝟙 I.Y.left))))
        αI := by
          rw [hFirstSelfLeg]
          simpa [qI, K₁₂, αI] using
            chosen_cover_refinement_member_first_branch_self_leg_to_qI_shell
              (𝒮 := 𝒮) hGerbe hAbelian q f₁ f₂ f₃ _hf₁ _hf₂ _hf₃ K T α
              (B := B) (R := R) I Ī hĪ
      _ =
        (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (local_overlap_common_owner_isomorphism
              (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
              (K.f ≫ f₁) (K.f ≫ f₂) qI (𝟙 I.Y.left)
              (by simp [qI])).hom).hom).1.app
          (op (Over.mk (𝟙 I.Y.left))))
        αI := hFirstQILeg
  have hFirstSharedFromSelf :
      βI =
        (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (local_overlap_common_owner_isomorphism
              (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
              (K.f ≫ f₁) (K.f ≫ f₂) qI Ī.toMiddleHom hg₁₂).hom).hom).1.app
          (op (Over.mk (𝟙 I.Y.left))))
        αI := by
    -- Keep the first branch on the actual refinement leg `Ī.toMiddleHom`; this is the exact
    -- owner used by the common-owner cocycle theorem before endpoint-independence collapses it.
    rw [hFirstSelfLeg]
    simpa [qI, K₁₂, αI] using
      chosen_cover_refinement_member_first_branch_self_leg_to_qI_shell
        (𝒮 := 𝒮) hGerbe hAbelian q f₁ f₂ f₃ _hf₁ _hf₂ _hf₃ K T α
        (B := B) (R := R) I Ī hĪ
  -- Route correction: the common refinement and both pairwise normalizations are fixed. The final
  -- source-faithful step is one flat cocycle calculation on the shared owner `qI`.
  calc
    (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₃))).1.map I.f.op
        (((((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
              (automorphism_overlap_hom_of_locally_isomorphic_cover
                (𝒮 := 𝒮) hGerbe hAbelian
                (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₁ f₂)) ≫
            (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
              (automorphism_overlap_hom_of_locally_isomorphic_cover
                (𝒮 := 𝒮) hGerbe hAbelian
                (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₂ f₃))).1.app T) α)
        =
      (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (local_overlap_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
            (K.f ≫ f₂) (K.f ≫ f₃) qI (𝟙 I.Y.left) (by simp [qI])).hom).hom).1.app
        (op (Over.mk (𝟙 I.Y.left))))
      βI := hSecondShared
    _ =
      (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          ((((canonicalPullbackChoice 𝒮.p).pullbackFunctor qI).mapIso
            (local_overlap_isomorphism
              (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃ K)).hom)).hom).1.app
        (op (Over.mk (𝟙 I.Y.left))))
      αI := by
        rw [hFirstSharedFromSelf]
        simpa [qI] using
          chosen_cover_pairwise_common_owner_conjugation_comp_hom_app
            (𝒮 := 𝒮) hGerbe hAbelian q f₁ f₂ f₃ K qI
            (K₁₂ := K₁₂) (K₂₃ := K₂₃) Ī.toMiddleHom (𝟙 I.Y.left) hg₁₂
            (by simp [qI]) (op (Over.mk (𝟙 I.Y.left))) αI
    _ =
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (K.f ^*[canonicalPullbackChoice 𝒮.p]
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₃))).1.map I.f.op
        ((((local_overlap_conjugation_iso
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃ K).hom).1.app T) α) := by
        symm
        simpa [qI, αI] using
          chosen_cover_refinement_member_direct_branch_restrict_eq_pulled_direct_app
            (𝒮 := 𝒮) hGerbe hAbelian q f₁ f₂ f₃ _hf₁ _hf₂ _hf₃ K T α
            (R := R) I

/-- Helper for Lemma 8.11.8: after fixing `T` and one section `α`, the source-faithful remaining
task is to choose a common refinement cover of `qT := T.unop.hom` in `C / K.Y` and prove that the
two candidate target sections agree after restriction to every member of that cover. -/
private theorem chosen_cover_pairwise_descent_comp_restrict_eq_on_qT_refinement
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U Y : C}
    (q : Y ⟶ U)
    {I₁ I₂ I₃ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) (f₃ : Y ⟶ I₃.Y)
    (_hf₁ : f₁ ≫ I₁.f = q) (_hf₂ : f₂ ≫ I₂.f = q) (_hf₃ : f₃ ≫ I₃.f = q)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃).Arrow)
    (T : (Over K.Y)ᵒᵖ)
    (α : (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁))).1.obj T) :
    ∃ R : (J.over K.Y).Cover T.unop,
      ∀ I : R.Arrow,
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (K.f ^*[canonicalPullbackChoice 𝒮.p]
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₃))).1.map I.f.op
            (((((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
                  (automorphism_overlap_hom_of_locally_isomorphic_cover
                    (𝒮 := 𝒮) hGerbe hAbelian
                    (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₁ f₂)) ≫
                (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
                  (automorphism_overlap_hom_of_locally_isomorphic_cover
                    (𝒮 := 𝒮) hGerbe hAbelian
                    (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₂ f₃))).1.app T) α) =
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (K.f ^*[canonicalPullbackChoice 𝒮.p]
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₃))).1.map I.f.op
            ((((local_overlap_conjugation_iso
              (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃ K).hom).1.app T) α) := by
  -- Route correction: this is the actual source-faithful blocker. One must choose a common
  -- refinement of the two pairwise overlap covers after pulling them back along `qT := T.unop.hom`,
  -- convert that refinement to a cover of `T.unop` in `J.over K.Y`, and then compare the two
  -- restricted branches via the existing common-owner app cocycle.
  obtain ⟨B, R, hR⟩ :=
    chosen_cover_overlap_common_refinement_cover_on_slice
      (𝒮 := 𝒮) hGerbe f₁ f₂ f₃ K T
  refine ⟨R, ?_⟩
  intro I
  obtain ⟨Ī, hĪ⟩ :=
    chosen_cover_overlap_common_refinement_base_arrow (J := J) (T := T.unop) hR I
  -- The cover-level work is complete; only the fixed-member equality remains.
  exact
    chosen_cover_pairwise_descent_comp_eq_on_refinement_member
      (𝒮 := 𝒮) hGerbe hAbelian q f₁ f₂ f₃ _hf₁ _hf₂ _hf₃ K T α
      (B := B) (R := R) hR I Ī hĪ

/-- Helper for Lemma 8.11.8: the fixed chosen gerbe cover of `U` satisfies the cocycle law for
the overlap morphisms between local underlying automorphism sheaves. -/
private theorem secondary_cover_pairwise_descent_comp_on_common_refinement_app
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U Y : C}
    (q : Y ⟶ U)
    {I₁ I₂ I₃ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) (f₃ : Y ⟶ I₃.Y)
    (_hf₁ : f₁ ≫ I₁.f = q) (_hf₂ : f₂ ≫ I₂.f = q) (_hf₃ : f₃ ≫ I₃.f = q)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃).Arrow)
    (T : (Over K.Y)ᵒᵖ)
    (α : (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁))).1.obj T) :
    (((((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          (automorphism_overlap_hom_of_locally_isomorphic_cover
            (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₁ f₂)) ≫
        (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          (automorphism_overlap_hom_of_locally_isomorphic_cover
            (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₂ f₃))).1.app T) α =
      (((local_overlap_conjugation_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃ K).hom).1.app T) α := by
  have h12 :=
    chosen_cover_overlap_map_eq_pulled_overlap
      (𝒮 := 𝒮) hGerbe hAbelian q f₁ f₂ f₃ _hf₁ _hf₂ K
  have h23 :=
    chosen_cover_overlap_map_eq_pulled_overlap
      (𝒮 := 𝒮) hGerbe hAbelian q f₂ f₃ f₁ _hf₂ _hf₃ K
  -- Route correction: the transport shell has now been eliminated. The remaining blocker is the
  -- direct composition of the two pulled-leg overlap maps on `C / K.Y`.
  rw [h12, h23]
  let targetSheaf :=
    automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₃))
  let lhsSection : targetSheaf.1.obj T :=
    (((((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
        (automorphism_overlap_hom_of_locally_isomorphic_cover
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₁ f₂)) ≫
      (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
        (automorphism_overlap_hom_of_locally_isomorphic_cover
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₂ f₃))).1.app T) α
  let rhsSection : targetSheaf.1.obj T :=
    ((((local_overlap_conjugation_iso
      (𝒮 := 𝒮) hGerbe hAbelian
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃ K).hom).1.app T) α)
  obtain ⟨R, hR⟩ :=
    chosen_cover_pairwise_descent_comp_restrict_eq_on_qT_refinement
      (𝒮 := 𝒮) hGerbe hAbelian q f₁ f₂ f₃ _hf₁ _hf₂ _hf₃ K T α
  -- Apply separatedness on the slice sheaf over `K.Y`: equality on the common refinement cover
  -- of `T.unop` forces equality of the original two sections on `T`.
  have hEq : lhsSection = rhsSection := by
    exact sections_eq_of_cover_on_slice (J := J) targetSheaf T.unop R lhsSection rhsSection hR
  simpa [targetSheaf, lhsSection, rhsSection] using hEq

/-- Helper for Lemma 8.11.8: the fixed chosen gerbe cover of `U` satisfies the cocycle law for
the overlap morphisms between local underlying automorphism sheaves after packaging the remaining
common-refinement comparison sectionwise. -/
private theorem secondary_cover_triple_overlap_comp_on_refinement
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U Y : C}
    (q : Y ⟶ U)
    {I₁ I₂ I₃ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) (f₃ : Y ⟶ I₃.Y)
    (_hf₁ : f₁ ≫ I₁.f = q) (_hf₂ : f₂ ≫ I₂.f = q) (_hf₃ : f₃ ≫ I₃.f = q)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃).Arrow) :
    (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
        (automorphism_overlap_hom_of_locally_isomorphic_cover
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₁ f₂)) ≫
      (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
        (automorphism_overlap_hom_of_locally_isomorphic_cover
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₂ f₃)) =
      (local_overlap_conjugation_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃ K).hom := by
  -- Route correction: package the remaining common-refinement comparison into one sectionwise
  -- statement, so the sheaf-level theorem is only extensionality on `T : Over K.Y`.
  apply Sheaf.hom_ext
  ext T α
  exact
    secondary_cover_pairwise_descent_comp_on_common_refinement_app
      (𝒮 := 𝒮) hGerbe hAbelian q f₁ f₂ f₃ _hf₁ _hf₂ _hf₃ K T α

/-- Helper for Lemma 8.11.8: the fixed chosen gerbe cover of `U` satisfies the cocycle law for
the overlap morphisms between local underlying automorphism sheaves. -/
private theorem chosen_cover_overlap_cocycle_on_common_refinement
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U : C} :
    ∀ ⦃Y : C⦄ (q : Y ⟶ U)
      ⦃I₁ I₂ I₃ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow⦄
      (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) (f₃ : Y ⟶ I₃.Y)
      (hf₁ : f₁ ≫ I₁.f = q) (hf₂ : f₂ ≫ I₂.f = q) (hf₃ : f₃ ≫ I₃.f = q),
      ((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃)).functor.map
        (automorphism_overlap_hom_of_locally_isomorphic_cover
            (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₁ f₂ ≫
          automorphism_overlap_hom_of_locally_isomorphic_cover
            (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₂ f₃)) =
        (secondary_cover_descent_iso_on_local_overlap
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃).hom := by
  intro Y q I₁ I₂ I₃ f₁ f₂ f₃ hf₁ hf₂ hf₃
  -- Once the branchwise common-refinement calculation is isolated, the cocycle is just
  -- extensionality on the `(f₁,f₃)` secondary cover.
  apply Pseudofunctor.DescentData.hom_ext
  intro K
  rw [localizedSheafToCoverDescentEquivalence_functor_map_component (J := J)
    (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃)]
  rw [Functor.map_comp]
  rw [secondary_cover_descent_iso_on_local_overlap_hom_component
    (𝒮 := 𝒮) hGerbe hAbelian
    (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃]
  -- The remaining branch computation is now exactly the isolated common-refinement lemma.
  exact
    secondary_cover_triple_overlap_comp_on_refinement
      (𝒮 := 𝒮) hGerbe hAbelian q f₁ f₂ f₃ hf₁ hf₂ hf₃ K

/-- Helper for Lemma 8.11.8: the fixed chosen gerbe cover of `U` satisfies the cocycle law for
the overlap morphisms between local underlying automorphism sheaves. -/
theorem automorphism_cover_overlap_comp
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U : C} :
    ∀ ⦃Y : C⦄ (q : Y ⟶ U)
      ⦃I₁ I₂ I₃ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow⦄
      (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) (f₃ : Y ⟶ I₃.Y)
      (hf₁ : f₁ ≫ I₁.f = q) (hf₂ : f₂ ≫ I₂.f = q) (hf₃ : f₃ ≫ I₃.f = q),
      automorphism_overlap_hom_of_locally_isomorphic_cover
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₁ f₂ ≫
        automorphism_overlap_hom_of_locally_isomorphic_cover
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₂ f₃ =
        automorphism_overlap_hom_of_locally_isomorphic_cover
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₁ f₃ := by
  intro Y q I₁ I₂ I₃ f₁ f₂ f₃ hf₁ hf₂ hf₃
  -- Route correction: map the three overlap morphisms to the common secondary-cover descent
  -- owner, collapse the self-overlap factor, and then use conjugation functoriality.
  let T :=
    local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃
  let E := localizedSheafToCoverDescentEquivalence (J := J) T
  apply Functor.map_injective E.functor
  rw [Functor.map_comp]
  rw [automorphism_overlap_hom_characterization
    (𝒮 := 𝒮) hGerbe hAbelian
    (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₁ f₃ hf₁ hf₃]
  exact
    chosen_cover_overlap_cocycle_on_common_refinement
      (𝒮 := 𝒮) hGerbe hAbelian q f₁ f₂ f₃ hf₁ hf₂ hf₃

/-- Helper for Lemma 8.11.8: the chosen-cover overlap pullback and cocycle laws descend the fixed
local automorphism sheaves on `C / U` to one canonical slice sheaf. -/
private noncomputable def chosen_cover_underlying_automorphism_sheaf
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮) (U : C) :
    Sheaf (J.over U) (Type (max u v)) :=
  Classical.choose <|
    chosen_cover_underlying_automorphism_descent
      (𝒮 := 𝒮) hGerbe hAbelian U
      (automorphism_cover_overlap_pull (𝒮 := 𝒮) hGerbe hAbelian)
      (automorphism_cover_overlap_comp (𝒮 := 𝒮) hGerbe hAbelian)

/-- Helper for Lemma 8.11.8: the descended chosen-cover sheaf still identifies with the local
automorphism sheaf on each arrow of the fixed chosen gerbe cover. -/
private noncomputable def chosen_cover_underlying_automorphism_sheaf_cover_iso
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (U : C) (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow) :
    (((J.pseudofunctorOver (Type (max u v))).toDescentData
        (fun I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow ↦ I.f)).obj
      (chosen_cover_underlying_automorphism_sheaf
        (𝒮 := 𝒮) hGerbe hAbelian U)).obj I ≅
      automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I) :=
  (Classical.choose_spec <|
      chosen_cover_underlying_automorphism_descent
        (𝒮 := 𝒮) hGerbe hAbelian U
        (automorphism_cover_overlap_pull (𝒮 := 𝒮) hGerbe hAbelian)
        (automorphism_cover_overlap_comp (𝒮 := 𝒮) hGerbe hAbelian)) I

/-- Helper for Lemma 8.11.8: once the chosen-cover descended slice sheaves are fixed, the
remaining absolute-glueing step is exactly to provide the transition isomorphisms and their
identity/cocycle laws. -/
private noncomputable abbrev chosen_cover_descent_functor
    (hGerbe : IsGerbe J 𝒮.p) (U : C) :=
  ((J.pseudofunctorOver (Type (max u v))).toDescentData
    (fun I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow ↦ I.f))

/-- Helper for Lemma 8.11.8: the chosen-cover descent datum of the canonical descended
automorphism sheaf on `C / U`. This names the datum-side owner so the remaining pullback step can
be phrased entirely in the descent category before transporting back to sheaves. -/
private noncomputable abbrev chosen_cover_descent_datum
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮) (U : C) :=
  (chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe U).obj
    (chosen_cover_underlying_automorphism_sheaf
      (𝒮 := 𝒮) hGerbe hAbelian U)

/-- Helper for Lemma 8.11.8: after pulling the chosen-cover descended sheaf on `C / U` back along
`f : V ⟶ U`, the chosen cover of `V` still sees it as one explicit descent datum. This is the
left-hand datum in the remaining source-faithful base-change packaging step. -/
private noncomputable abbrev chosen_cover_pulled_descent_datum
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U) :=
  (chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe V).obj
    ((J.overMapPullback (Type (max u v)) f).obj
      (chosen_cover_underlying_automorphism_sheaf
        (𝒮 := 𝒮) hGerbe hAbelian U))

/-- Helper for Lemma 8.11.8: once a chosen-cover pullback comparison is built directly in the
descent-data category on the chosen cover of `V`, transport it back to the localized sheaf on
`C / V`. This keeps the main theorem on the datum-first route prescribed by the source proof. -/
private noncomputable def chosen_cover_transport_transition
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U)
    (e :
      chosen_cover_pulled_descent_datum
          (𝒮 := 𝒮) hGerbe hAbelian f ≅
        chosen_cover_descent_datum
          (𝒮 := 𝒮) hGerbe hAbelian V) :
    (J.overMapPullback (Type (max u v)) f).obj
      (chosen_cover_underlying_automorphism_sheaf
        (𝒮 := 𝒮) hGerbe hAbelian U) ≅
      chosen_cover_underlying_automorphism_sheaf
        (𝒮 := 𝒮) hGerbe hAbelian V :=
  localizedSheafTransportIsoOfCoverDescentIso (J := J)
    (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V) e

end CategoryTheory
