import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_12_30_1 (from Chap12) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

universe uI vI uA vA

namespace CategoryTheory

section Filtered

variable {I : Type uI} [Category.{vI} I]
variable {A : Type uA} [Category.{vA} A] [Preadditive A]

/- Domain-style sampling for Lemma 12.30.1 in the filtered/cofiltered additive-diagram domain:
- sampled owner-level declarations:
  * `IsEssentiallyConstantFilteredDiagram`
  * `essentiallyConstantFilteredDiagram_exists_essentiallyConstant_colimitCocone`
  * `essentiallyConstantFilteredDiagram_iff_comp_final`
  * `essentiallyConstantCofilteredDiagram_iff_comp_initial`
- best owner abstraction: the chapter owner
  `IsEssentiallyConstantFilteredDiagram M` from `Definition_4_22_2`.

Primitive-vs-derived split:
- primitive source-facing data: for a fixed colimit cocone `c`, each stage `M.obj i` splits into a
  stable summand that maps isomorphically to the colimit value and a complementary summand that
  eventually dies under some transition map.
- derived source-facing bridge criterion: a cofinal filtered full subcategory on which this
  pointwise stable-splitting condition holds.
- derived API: the dual cofiltered criterion `HasEventuallySplitLimit`, obtained by applying the
  filtered statement to the opposite diagram.

Source/core/bridge triage:
- `source-facing`: `HasEventuallySplitColimit` and its dual `HasEventuallySplitLimit`.
- `core/canonical`: `IsEssentiallyConstantFilteredDiagram`,
  `IsEssentiallyConstantCofilteredDiagram`, and the actual colimit owner `ColimitCocone`.
- `bridge/view`: restriction to a cofinal filtered full subcategory, and passage to the opposite
  diagram for the cofiltered dual.

The colimit witness should therefore use the canonical owner `ColimitCocone M`, not a duplicated
pair `(c : Cocone M)` together with a separate `IsColimit c`. -/

private def stableSplitStage {M : I ⥤ A} (c : ColimitCocone M) (i : I) : Prop :=
  ∃ (X Z : A) (f : X ⟶ M.obj i) (g : M.obj i ⟶ Z) (zero : f ≫ g = 0)
    (s : (ShortComplex.mk f g zero).Splitting),
      IsIso (f ≫ c.cocone.ι.app i) ∧
        ∃ (j : I) (h : i ⟶ j), s.s ≫ M.map h = 0

-- Internal stable-splitting criterion used to define the source-facing bridge
-- `HasEventuallySplitColimit`.
private def hasStableSplitColimit (M : I ⥤ A) : Prop :=
  ∃ c : ColimitCocone M,
    ∀ i : I, stableSplitStage c i

/-- A diagram has an eventual split colimit if, after restricting along the inclusion of some
cofinal filtered full subcategory, the restricted diagram has a stable split colimit. In Lemma
12.30.1 this is the source-facing bridge criterion for filtered diagrams. -/
def HasEventuallySplitColimit (M : I ⥤ A) : Prop :=
  ∃ P : ObjectProperty I,
    ∃ _ : IsFiltered P.FullSubcategory,
      ∃ _ : Functor.Final P.ι,
        hasStableSplitColimit (P.ι ⋙ M)

-- Proof sketch: from an essentially constant filtered cocone, take its colimit value, pass to the
-- cofinal full subcategory of stages receiving a map from the chosen index, and split the induced
-- idempotent at each such stage using idempotent completeness.
/-- Lemma 12.30.1 (1): for a filtered diagram in a preadditive Karoubian category, being
essentially constant is equivalent to admitting a cofinal filtered full subcategory whose stages
split into a stable summand mapping isomorphically to a colimit value and a complementary summand
that eventually becomes zero. -/
theorem essentiallyConstantFilteredDiagram_iff_hasEventuallySplitColimit
    [IsFiltered I] [IsIdempotentComplete A] (M : I ⥤ A) :
    IsEssentiallyConstantFilteredDiagram M ↔
      HasEventuallySplitColimit M := sorry

end Filtered

section Cofiltered

variable {I : Type uI} [Category.{vI} I]
variable {A : Type uA} [Category.{vA} A] [Preadditive A]

/-- A diagram has an eventual split limit if, after passing to the opposite diagram, it has an
eventual split colimit. In Lemma 12.30.1 this is the cofiltered dual of
`HasEventuallySplitColimit`, applied to cofiltered diagrams. -/
abbrev HasEventuallySplitLimit (M : I ⥤ A) : Prop :=
  HasEventuallySplitColimit M.op

-- Proof sketch: apply the filtered statement to the opposite diagram `M.op`, translate the split
-- decomposition data across `op`/`unop`, and rewrite essential constancy using the dual
-- characterization of essentially constant cofiltered cones.
/-- Lemma 12.30.1 (2): for a cofiltered diagram in a preadditive Karoubian category, being
essentially constant is equivalent to admitting an initial cofiltered full subcategory whose stages
split into a stable summand receiving the limit isomorphically and a complementary summand killed
by some earlier transition map. -/
theorem essentiallyConstantCofilteredDiagram_iff_hasEventuallySplitLimit
    [IsCofiltered I] [IsIdempotentComplete A] (M : I ⥤ A) :
    IsEssentiallyConstantCofilteredDiagram M ↔
      HasEventuallySplitLimit M := by
  rw [isEssentiallyConstantCofilteredDiagram_iff_op]
  simpa [HasEventuallySplitLimit] using
    essentiallyConstantFilteredDiagram_iff_hasEventuallySplitColimit M.op

end Cofiltered

end CategoryTheory

/-! ### Lemma_12_30_2 (from Chap12) -/
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

/-! ### Lemma_12_30_3 (from Chap12) -/
open CategoryTheory
open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {I : Type u₁} [Category.{v₁} I] [IsFiltered I]
variable {A : Type u₂} [Category.{v₂} A] [HasZeroMorphisms A] [HasBinaryBiproducts A]
variable [IsIdempotentComplete A]

/- Domain-style sampling for Lemma 12.30.3 in the filtered additive-diagram domain:
- sampled chapter/mathlib declarations:
  * `IsEssentiallyConstantFilteredDiagram`
  * `IsEssentiallyConstantFilteredCocone`
  * `essentiallyConstantFilteredDiagram_exists_essentiallyConstant_colimitCocone`
  * `Limits.hasColimit_biprod_iff`
  * `Limits.colimit_biprod_iso`

Primitive-vs-derived split:
- primitive source-facing data: essentially constant cocones on `F`, `G`, and `F ⊞ G`
- derived API used in the proof: the canonical colimit cocones supplied by
  `essentiallyConstantFilteredDiagram_exists_essentiallyConstant_colimitCocone` and the biproduct
  colimit comparison from Lemma 12.30.2

Source/core/bridge triage:
- `source-facing`: `essentiallyConstantFilteredDiagram_biprod_iff`, the Chapter 12 closure theorem
  for the Chapter 4 owner predicate `IsEssentiallyConstantFilteredDiagram`
- `core/canonical`: the owner predicate `IsEssentiallyConstantFilteredDiagram`
- `bridge/view`: the internal cocone-level transport to the canonical biproduct colimit vertex in
  the reverse implication; no separate public `HasEventuallySplitColimit` bridge is retained here

The refinement therefore keeps the public statement directly at the owner level and at the minimal
binary-biproduct assumption layer already used by `Limits.hasColimit_biprod_iff`, instead of
routing the file through a parallel split-colimit theorem or a local finite-biproduct bridge. -/

/-- Lemma 12.30.3: in the canonical owner predicate
`IsEssentiallyConstantFilteredDiagram`, the pointwise direct-sum diagram `F ⊞ G` is essentially
constant if and only if both `F` and `G` are essentially constant. -/
theorem essentiallyConstantFilteredDiagram_biprod_iff (F G : I ⥤ A) :
    IsEssentiallyConstantFilteredDiagram (F ⊞ G) ↔
      IsEssentiallyConstantFilteredDiagram F ∧ IsEssentiallyConstantFilteredDiagram G := by
  constructor
  · intro hFG
    obtain ⟨c, hc⟩ :=
      essentiallyConstantFilteredDiagram_exists_essentiallyConstant_colimitCocone (F ⊞ G) hFG
    letI : HasColimit (F ⊞ G) := HasColimit.mk c
    have hcol := (Limits.hasColimit_biprod_iff F G).mp inferInstance
    letI : HasColimit F := hcol.1
    letI : HasColimit G := hcol.2
    -- Transport the essentially constant colimit cocone on `F ⊞ G` to the canonical vertex
    -- `colimit F ⊞ colimit G` via `Limits.colimit_biprod_iso`, then project the source-facing
    -- section/factorization data to the two summand cocones.
    sorry
  · rintro ⟨hF, hG⟩
    obtain ⟨cF, hcF⟩ :=
      essentiallyConstantFilteredDiagram_exists_essentiallyConstant_colimitCocone F hF
    obtain ⟨cG, hcG⟩ :=
      essentiallyConstantFilteredDiagram_exists_essentiallyConstant_colimitCocone G hG
    -- Combine the two essentially constant colimit cocones into a cocone on the pointwise
    -- biproduct diagram `F ⊞ G`; filteredness supplies a common distinguished stage and a common
    -- eventual target for the componentwise factorization data.
    sorry

end

end CategoryTheory
