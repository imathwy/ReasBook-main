import Mathlib
import StacksProject_2024.Chap12.Definition_12_3_8

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.ObjectProperty.IsStableUnderRetracts

namespace CategoryTheory.Limits

section

variable {𝒥 : Type u₁} [Category.{v₁} 𝒥]
variable {A : Type u₂} [Category.{v₂} A] [HasZeroMorphisms A] [HasBinaryBiproducts A]
variable (F G : 𝒥 ⥤ A)

/- Domain-style sampling for Lemma 12.30.2 in the functor-category / biproduct-colimit domain:
- primary domain: binary biproducts in functor categories, colimits of specific diagrams, and
  retract-stable object properties in idempotent-complete categories with zero morphisms
- core/canonical declarations inspected:
  * `FunctorCategory.pointwiseBinaryBicone`
  * `FunctorCategory.pointwiseBinaryBicone.isBilimit`
  * `colimit.isoColimitCocone`
  * `ObjectProperty.IsStableUnderRetracts.of_biprod_left`
  * `ObjectProperty.IsStableUnderRetracts.of_biprod_right`
  * `IsIdempotentComplete.idempotents_split`
- best owner abstraction: the object property `fun H : 𝒥 ⥤ A ↦ HasColimit H` on the functor
  category, together with the canonical pointwise biproduct owner `F ⊞ G`
- primitive data: chosen colimit cocones for the specific diagrams `F` and `G`
- derived API: the induced colimit cocone on `F ⊞ G`, the comparison isomorphism with
  `colimit F ⊞ colimit G`, and retract-stability of `HasColimit` in `𝒥 ⥤ A`
- source/core/bridge triage:
  * `source-facing`: `hasColimit_biprod_iff`
  * `core/canonical`: `HasColimit` as an object property on `𝒥 ⥤ A`
  * `bridge/view`: `colimit_biprod_iso` and the retract-stability theorem below

Because the file assumes colimits only for the specific diagrams `F` and `G`, not globally for all
`𝒥`-shaped diagrams in `A`, there is no upstream theorem with this exact hypothesis pattern; the
local cocone construction is therefore genuine supporting data, while the direct-summand direction
should be expressed through the generic retract API rather than by bespoke left/right wrappers. -/
section

variable [HasColimit F] [HasColimit G]

private noncomputable def pointwiseBiprod : 𝒥 ⥤ A :=
  (pointwiseBinaryBicone F G).pt

private noncomputable def pointwiseBiprodIso : pointwiseBiprod F G ≅ F ⊞ G :=
  biprod.uniqueUpToIso F G (pointwiseBinaryBicone.isBilimit F G)

private noncomputable def biprod_colimit_ι (j : 𝒥) :
    (pointwiseBiprod F G).obj j ⟶ colimit F ⊞ colimit G :=
  biprod.map (colimit.ι F j) (colimit.ι G j)

-- Proof sketch: the structure maps of the cocone are the pointwise biproduct lifts of the two
-- colimit cocone maps. Naturality follows by checking the two projections and using the cocone
-- relations for `F` and `G`.
/-- The structure maps of the biproduct colimit cocone are natural in the diagram variable. -/
private theorem biprod_colimit_ι_naturality {i j : 𝒥} (f : i ⟶ j) :
    biprod_colimit_ι F G i = (pointwiseBiprod F G).map f ≫ biprod_colimit_ι F G j := by
  apply biprod.hom_ext
  · simp [pointwiseBiprod, biprod_colimit_ι, Category.assoc]
  · simp [pointwiseBiprod, biprod_colimit_ι, Category.assoc]

/-- The canonical colimit cocone on the explicit pointwise biproduct diagram with vertex
`colimit F ⊞ colimit G`. -/
private noncomputable def biprod_colimit_cocone :
    ColimitCocone (pointwiseBiprod F G) where
  cocone :=
    { pt := colimit F ⊞ colimit G
      ι :=
        { app := fun j ↦ biprod_colimit_ι F G j
          naturality := fun _ _ f ↦ by
            simpa using (biprod_colimit_ι_naturality F G f).symm } }
  -- Proof sketch: for any cocone on `F ⊞ G`, use the colimit properties of `F` and `G` to obtain
  -- maps out of `colimit F` and `colimit G`, combine them via `biprod.desc`, and prove uniqueness
  -- after precomposing with the pointwise inclusions of the direct sum diagram.
  isColimit := by
    refine
      { desc := fun s ↦
          biprod.desc
            (colimit.desc F ((Cocone.precompose (pointwiseBinaryBicone F G).inl).obj s))
            (colimit.desc G ((Cocone.precompose (pointwiseBinaryBicone F G).inr).obj s))
        fac := ?_
        uniq := ?_ }
    · intro s j
      refine biprod.hom_ext' _ _ ?_ ?_
      · have h₁ :
            biprod.inl ≫ biprod_colimit_ι F G j ≫
                biprod.desc
                  (colimit.desc F ((Cocone.precompose (pointwiseBinaryBicone F G).inl).obj s))
                  (colimit.desc G ((Cocone.precompose (pointwiseBinaryBicone F G).inr).obj s)) =
              colimit.ι F j ≫
                colimit.desc F ((Cocone.precompose (pointwiseBinaryBicone F G).inl).obj s) := by
              simp [biprod_colimit_ι]
        have h₂ :
            colimit.ι F j ≫ colimit.desc F ((Cocone.precompose (pointwiseBinaryBicone F G).inl).obj s) =
              biprod.inl ≫ s.ι.app j := by
          simpa using
            (colimit.ι_desc ((Cocone.precompose (pointwiseBinaryBicone F G).inl).obj s) j)
        exact h₁.trans h₂
      · have h₁ :
            biprod.inr ≫ biprod_colimit_ι F G j ≫
                biprod.desc
                  (colimit.desc F ((Cocone.precompose (pointwiseBinaryBicone F G).inl).obj s))
                  (colimit.desc G ((Cocone.precompose (pointwiseBinaryBicone F G).inr).obj s)) =
              colimit.ι G j ≫
                colimit.desc G ((Cocone.precompose (pointwiseBinaryBicone F G).inr).obj s) := by
              simp [biprod_colimit_ι]
        have h₂ :
            colimit.ι G j ≫ colimit.desc G ((Cocone.precompose (pointwiseBinaryBicone F G).inr).obj s) =
              biprod.inr ≫ s.ι.app j := by
          simpa using
            (colimit.ι_desc ((Cocone.precompose (pointwiseBinaryBicone F G).inr).obj s) j)
        exact h₁.trans h₂
    · intro s m hm
      apply biprod.hom_ext'
      · apply colimit.hom_ext
        intro j
        have h := hm j
        have h₁ : colimit.ι F j ≫ biprod.inl ≫ m = biprod.inl ≫ s.ι.app j := by
          simpa [pointwiseBiprod, biprod_colimit_ι, Category.assoc] using
            congrArg (fun k ↦ biprod.inl ≫ k) h
        have h₂ :
            biprod.inl ≫ s.ι.app j =
              colimit.ι F j ≫ biprod.inl ≫
                biprod.desc
                  (colimit.desc F ((Cocone.precompose (pointwiseBinaryBicone F G).inl).obj s))
                  (colimit.desc G ((Cocone.precompose (pointwiseBinaryBicone F G).inr).obj s)) := by
          simpa using
            (colimit.ι_desc ((Cocone.precompose (pointwiseBinaryBicone F G).inl).obj s) j).symm
        exact h₁.trans h₂
      · apply colimit.hom_ext
        intro j
        have h := hm j
        have h₁ : colimit.ι G j ≫ biprod.inr ≫ m = biprod.inr ≫ s.ι.app j := by
          simpa [pointwiseBiprod, biprod_colimit_ι, Category.assoc] using
            congrArg (fun k ↦ biprod.inr ≫ k) h
        have h₂ :
            biprod.inr ≫ s.ι.app j =
              colimit.ι G j ≫ biprod.inr ≫
                biprod.desc
                  (colimit.desc F ((Cocone.precompose (pointwiseBinaryBicone F G).inl).obj s))
                  (colimit.desc G ((Cocone.precompose (pointwiseBinaryBicone F G).inr).obj s)) := by
          simpa using
            (colimit.ι_desc ((Cocone.precompose (pointwiseBinaryBicone F G).inr).obj s) j).symm
        exact h₁.trans h₂

/-- If `F` and `G` admit colimits, then the explicit pointwise biproduct diagram admits a colimit.
-/
private noncomputable instance hasColimit_pointwiseBiprod :
    HasColimit (pointwiseBiprod F G) :=
  HasColimit.mk (biprod_colimit_cocone F G)

/-- If `F` and `G` admit colimits, then their chosen binary biproduct diagram also admits a
colimit. -/
private noncomputable instance hasColimit_biprod :
    HasColimit (F ⊞ G) :=
  hasColimit_of_iso (pointwiseBiprodIso F G).symm

/-- Companion bridge for Lemma 12.30.2: when `F` and `G` admit colimits, the colimit of the
pointwise direct sum diagram `F ⊞ G` is canonically the binary biproduct of `colimit F` and
`colimit G`. -/
noncomputable def colimit_biprod_iso :
    colimit (F ⊞ G) ≅ colimit F ⊞ colimit G :=
  HasColimit.isoOfNatIso (pointwiseBiprodIso F G).symm ≪≫
    colimit.isoColimitCocone (biprod_colimit_cocone F G)

/-- Under `colimit_biprod_iso`, the structure map from stage `j` is the biproduct lift of the two
component colimit maps. -/
theorem colimit_biprod_iso_ι_hom (j : 𝒥) :
    colimit.ι (F ⊞ G) j ≫ (colimit_biprod_iso F G).hom =
      biprod.lift
        (((biprod.fst : F ⊞ G ⟶ F).app j) ≫ colimit.ι F j)
        (((biprod.snd : F ⊞ G ⟶ G).app j) ≫ colimit.ι G j) := by
  sorry

@[reassoc]
theorem colimit_biprod_iso_hom_fst (j : 𝒥) :
    colimit.ι (F ⊞ G) j ≫ (colimit_biprod_iso F G).hom ≫ biprod.fst =
      ((biprod.fst : F ⊞ G ⟶ F).app j) ≫ colimit.ι F j := by
  rw [← Category.assoc, colimit_biprod_iso_ι_hom]
  simp

attribute [simp] colimit_biprod_iso_hom_fst_assoc

@[reassoc]
theorem colimit_biprod_iso_hom_snd (j : 𝒥) :
    colimit.ι (F ⊞ G) j ≫ (colimit_biprod_iso F G).hom ≫ biprod.snd =
      ((biprod.snd : F ⊞ G ⟶ G).app j) ≫ colimit.ι G j := by
  rw [← Category.assoc, colimit_biprod_iso_ι_hom]
  simp

attribute [simp] colimit_biprod_iso_hom_snd_assoc

end

end

section

variable {𝒥 : Type u₁} [Category.{v₁} 𝒥]
variable {A : Type u₂} [Category.{v₂} A]

/-- In an idempotent-complete target category, any retract of a colimit-admitting diagram again
admits a colimit. -/
theorem hasColimit_of_retract [IsIdempotentComplete A] {H K : 𝒥 ⥤ A} (r : Retract H K)
    [HasColimit K] :
    HasColimit H := by
  sorry

private instance hasColimit_isStableUnderRetracts [IsIdempotentComplete A] :
    ObjectProperty.IsStableUnderRetracts (fun H : 𝒥 ⥤ A ↦ HasColimit H) where
  of_retract r h := by
    letI := h
    exact hasColimit_of_retract r

section

variable [HasZeroMorphisms A] [HasBinaryBiproducts A]
variable (F G : 𝒥 ⥤ A)

-- Proof sketch: for the forward implication, view `HasColimit` as an object property on the
-- functor category and apply the generic direct-summand lemmas `of_biprod_left` and
-- `of_biprod_right`, whose only input is retract-stability established above by splitting the
-- induced idempotent on the colimit of the ambient diagram. For the reverse implication, combine
-- the colimiting cocones of `F` and `G` into a colimiting cocone for `F ⊞ G` using the biproduct
-- universal property.
/-- Lemma 12.30.2: in an idempotent-complete category with zero morphisms and binary biproducts,
the colimit of the pointwise direct sum diagram `F ⊞ G` exists if and only if the colimits of `F`
and `G` both exist. -/
theorem hasColimit_biprod_iff [IsIdempotentComplete A] :
    HasColimit (F ⊞ G) ↔ HasColimit F ∧ HasColimit G := by
  constructor
  · intro h
    letI := h
    exact ⟨of_biprod_left (fun H : 𝒥 ⥤ A ↦ HasColimit H)
        (show HasColimit (F ⊞ G) from inferInstance),
      of_biprod_right (fun H : 𝒥 ⥤ A ↦ HasColimit H)
        (show HasColimit (F ⊞ G) from inferInstance)⟩
  · rintro ⟨hF, hG⟩
    letI := hF
    letI := hG
    exact inferInstance

end

end

end CategoryTheory.Limits
