import Mathlib
import stacks_proof.stacks_project.Chap06.Lemma_6_15_2
import stacks_proof.stacks_project.Chap06.Lemma_6_32_1
import stacks_proof.stacks_project.Chap06.Lemma_6_32_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopCat TopologicalSpace

noncomputable section

universe u

section

variable {X : TopCat.{u}} {Z : Set X}

local notation "iZ" => X.closedSubsetInclusion Z

/- Domain-style sampling for Remark 17.6.4:
- primary domain: pointed sheaves on a closed subset, the closed-subset pushforward functor, and
  the pointed closed-support subsheaf on `X` and its restriction to `Z`;
- sampled owner declarations:
  `TopCat.closedSubsetInclusion`,
  `CategoryTheory.Subobject`,
  `Sheaf.pushforward`,
  `Sheaf.pullback`,
  `closedSubsetSectionsWithSupportFunctor`,
  `Sheaf.pullbackPushforwardAdjunction`,
  `subsetSheaf_pullback_pushforward_counit_isIso`;
- best owner abstraction:
  the source-facing owners are the pointed closed-support subsheaf
  `ClosedSubsetSectionsWithSupport.Pointed.subsheaf hZ ℱ ⊆ ℱ` on `X` and its restriction
  `ClosedSubsetSectionsWithSupport.Pointed.sheaf hZ ℱ` to `Z`; the functor `𝓗[hZ]` is derived
  from those owners;
- primitive data:
  the closed subset `Z`, its open complement, the explicit support-condition subsheaf on `X`, and
  the canonical distinguished point section on that sheaf;
- derived API:
  the restricted pointed sheaf on `Z`, the functor `𝓗[hZ]`, and the
  left-adjoint/right-adjoint/exactness consequences for closed-subset pushforward.

Source/core/bridge triage:
- `source-facing`: the pointed closed-support subsheaf on `X`, the restricted pointed sheaf on `Z`,
  and the induced functor `𝓗[hZ]`;
- `core/canonical`: the adjointness of `Sheaf.pushforward Pointed iZ` and the resulting exactness;
- `bridge/view`: the explicit support-condition subsheaf on `X`, pointified canonically on `X`
  before restricting to `Z`; there is no chosen `Type`-valued point data on `Z`. -/

/-- The open complement of a closed subset `Z ⊆ X`. -/
private abbrev closedSubsetOpenComplement (hZ : IsClosed Z) : Opens X :=
  ⟨Zᶜ, hZ.isOpen_compl⟩

/-- A section of a pointed sheaf over `U` is supported in `Z` when its restriction to the open
complement `U ∩ (X \ Z)` is the distinguished point section. -/
def ClosedSubsetSectionsWithSupport.Pointed.appPred
    (hZ : IsClosed Z) (ℱ : X.Sheaf Pointed) (U : Opens X)
    (s : ℱ.presheaf.obj (op U)) : Prop :=
  ℱ.presheaf.map (Opens.infLELeft U (closedSubsetOpenComplement hZ)).op s =
    (ℱ.presheaf.obj (op (U ⊓ closedSubsetOpenComplement hZ))).point

/-- Helper for Remark 17.6.4: restricting a supported section along a smaller open keeps it
supported. -/
private theorem supportedTypePresheaf_map_mem
    (hZ : IsClosed Z) (ℱ : X.Sheaf Pointed) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
    (s : ℱ.presheaf.obj U)
    (hs : ClosedSubsetSectionsWithSupport.Pointed.appPred hZ ℱ U.unop s) :
    ClosedSubsetSectionsWithSupport.Pointed.appPred hZ ℱ V.unop (ℱ.presheaf.map i s) := by
  let j : op (U.unop ⊓ closedSubsetOpenComplement hZ) ⟶
      op (V.unop ⊓ closedSubsetOpenComplement hZ) :=
    (homOfLE <| fun x hx ↦ ⟨i.unop.le hx.1, hx.2⟩).op
  have hij :
      i ≫ (Opens.infLELeft V.unop (closedSubsetOpenComplement hZ)).op =
        (Opens.infLELeft U.unop (closedSubsetOpenComplement hZ)).op ≫ j :=
    Subsingleton.elim _ _
  -- Rewrite the two-step restriction through the common restriction from `U ∩ Zᶜ`.
  unfold ClosedSubsetSectionsWithSupport.Pointed.appPred at hs ⊢
  calc
    ℱ.presheaf.map (Opens.infLELeft V.unop (closedSubsetOpenComplement hZ)).op
        (ℱ.presheaf.map i s)
        =
      ℱ.presheaf.map
        ((Opens.infLELeft U.unop (closedSubsetOpenComplement hZ)).op ≫ j) s := by
          rw [← hij]
          simpa using
            congrArg (fun f ↦ f s)
              (ℱ.presheaf.map_comp i
                (Opens.infLELeft V.unop (closedSubsetOpenComplement hZ)).op)
    _ =
      ℱ.presheaf.map j
        (ℱ.presheaf.map (Opens.infLELeft U.unop (closedSubsetOpenComplement hZ)).op s) := by
          simpa using
            congrArg (fun f ↦ f s)
              (ℱ.presheaf.map_comp
                (Opens.infLELeft U.unop (closedSubsetOpenComplement hZ)).op j)
    _ = ℱ.presheaf.map j ((ℱ.presheaf.obj
        (op (U.unop ⊓ closedSubsetOpenComplement hZ))).point) := by
          rw [hs]
    _ = (ℱ.presheaf.obj (op (V.unop ⊓ closedSubsetOpenComplement hZ))).point := by
          simpa using (ℱ.presheaf.map j).map_point

/-- Helper for Remark 17.6.4: the object on an open `U` is the type of sections supported in
`Z`. -/
private abbrev supportedTypePresheafObj
    (hZ : IsClosed Z) (ℱ : X.Sheaf Pointed) (U : (Opens X)ᵒᵖ) :=
  { s : ℱ.presheaf.obj U // ClosedSubsetSectionsWithSupport.Pointed.appPred hZ ℱ U.unop s }

/-- Helper for Remark 17.6.4: the restriction map on supported sections is induced from the
ambient pointed sheaf. -/
private def supportedTypePresheafMap
    (hZ : IsClosed Z) (ℱ : X.Sheaf Pointed) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    supportedTypePresheafObj hZ ℱ U → supportedTypePresheafObj hZ ℱ V :=
  fun s ↦ ⟨ℱ.presheaf.map i s.1, supportedTypePresheaf_map_mem hZ ℱ i s.1 s.2⟩

/-- Helper for Remark 17.6.4: the supported-sections restriction map for an identity open
inclusion is the identity. -/
private theorem supportedTypePresheafMap_id
    (hZ : IsClosed Z) (ℱ : X.Sheaf Pointed) (U : (Opens X)ᵒᵖ) :
    supportedTypePresheafMap hZ ℱ (𝟙 U) = id := by
  -- The restriction map along the identity inclusion is the identity on supported sections.
  funext s
  apply Subtype.ext
  simpa [supportedTypePresheafMap]

/-- Helper for Remark 17.6.4: the supported-sections restriction maps compose as expected. -/
private theorem supportedTypePresheafMap_comp
    (hZ : IsClosed Z) (ℱ : X.Sheaf Pointed)
    {U V W : (Opens X)ᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) :
    supportedTypePresheafMap hZ ℱ (i ≫ j) =
      supportedTypePresheafMap hZ ℱ j ∘ supportedTypePresheafMap hZ ℱ i := by
  -- Composition is inherited componentwise from the ambient presheaf.
  funext s
  apply Subtype.ext
  simpa [supportedTypePresheafMap] using
    congrArg (fun f ↦ f s.1) (ℱ.presheaf.map_comp i j)

/-- The `Type`-valued presheaf of local sections whose restriction to the open complement of `Z`
is the distinguished point section. -/
private def supportedTypePresheaf
    (hZ : IsClosed Z) (ℱ : X.Sheaf Pointed) : X.Presheaf (Type u) where
  obj U := supportedTypePresheafObj hZ ℱ U
  map {U V} i := supportedTypePresheafMap hZ ℱ i
  map_id := supportedTypePresheafMap_id hZ ℱ
  map_comp := by
    intro U V W i j
    simpa using supportedTypePresheafMap_comp hZ ℱ i j

/-- Helper for Remark 17.6.4: if compatible local sections supported in `Z` admit an ambient
gluing, then restricting that ambient gluing to `X \ Z` is the distinguished point section. -/
private theorem pointed_section_eq_point_of_restrict_eq_point_on_cover
    (ℱ : X.Sheaf Pointed) {ι : Type u} (U : ι → Opens X)
    (t : ℱ.presheaf.obj (op (iSup U)))
    (ht : ∀ i : ι,
      ℱ.presheaf.map (Opens.leSupr U i).op t = (ℱ.presheaf.obj (op (U i))).point) :
    t = (ℱ.presheaf.obj (op (iSup U))).point := by
  -- The global section and the distinguished point section agree on every cover member.
  apply TopCat.Sheaf.eq_of_locally_eq ℱ U t (ℱ.presheaf.obj (op (iSup U))).point
  intro i
  rw [ht i]
  simpa using (ℱ.presheaf.map (Opens.leSupr U i).op).map_point

/-- Helper for Remark 17.6.4: if compatible local sections supported in `Z` admit an ambient
gluing, then restricting that ambient gluing to `X \ Z` is the distinguished point section. -/
private theorem iSup_inf_closedSubsetOpenComplement_eq
    (hZ : IsClosed Z) {ι : Type*} (U : ι → Opens X) :
    iSup (fun i ↦ U i ⊓ closedSubsetOpenComplement hZ) =
      (iSup U) ⊓ closedSubsetOpenComplement hZ := by
  -- Membership in the supremum of the complement cover is exactly membership in the ambient
  -- cover together with membership in the complement.
  ext x
  simp

/-- Helper for Remark 17.6.4: if compatible local sections supported in `Z` admit an ambient
gluing, then restricting that ambient gluing to `X \ Z` is the distinguished point section. -/
private theorem supported_glue_restrict_eq_point
    (hZ : IsClosed Z) (ℱ : X.Sheaf Pointed)
    {ι : Type u} (U : ι → Opens X)
    (si : ∀ i, supportedTypePresheafObj hZ ℱ (op (U i)))
    (s : ℱ.presheaf.obj (op (iSup U)))
    (hs : TopCat.Presheaf.IsGluing ℱ.presheaf U (fun i ↦ (si i).1) s) :
    ClosedSubsetSectionsWithSupport.Pointed.appPred hZ ℱ (iSup U) s := by
  let V : ι → Opens X := fun i ↦ U i ⊓ closedSubsetOpenComplement hZ
  have ht :
      ∀ i : ι,
        ℱ.presheaf.map (Opens.leSupr V i).op
            (ℱ.presheaf.map (Opens.infLELeft (iSup U) (closedSubsetOpenComplement hZ)).op s) =
          (ℱ.presheaf.obj (op (V i))).point := by
    intro i
    have hcomp :
        (Opens.infLELeft (iSup U) (closedSubsetOpenComplement hZ)).op ≫
            (Opens.leSupr V i).op =
          (Opens.leSupr U i).op ≫
            (Opens.infLELeft (U i) (closedSubsetOpenComplement hZ)).op :=
      Subsingleton.elim _ _
    calc
      ℱ.presheaf.map (Opens.leSupr V i).op
          (ℱ.presheaf.map (Opens.infLELeft (iSup U) (closedSubsetOpenComplement hZ)).op s)
          =
        ℱ.presheaf.map
          ((Opens.infLELeft (iSup U) (closedSubsetOpenComplement hZ)).op ≫
            (Opens.leSupr V i).op) s := by
              simpa using
                congrArg (fun f ↦ f s)
                  (ℱ.presheaf.map_comp
                    (Opens.infLELeft (iSup U) (closedSubsetOpenComplement hZ)).op
                    (Opens.leSupr V i).op)
      _ =
        ℱ.presheaf.map
          ((Opens.leSupr U i).op ≫
            (Opens.infLELeft (U i) (closedSubsetOpenComplement hZ)).op) s := by
              rw [hcomp]
      _ =
        ℱ.presheaf.map (Opens.infLELeft (U i) (closedSubsetOpenComplement hZ)).op
          (ℱ.presheaf.map (Opens.leSupr U i).op s) := by
            simpa using
              congrArg (fun f ↦ f s)
                (ℱ.presheaf.map_comp
                  (Opens.leSupr U i).op
                  (Opens.infLELeft (U i) (closedSubsetOpenComplement hZ)).op)
      _ =
        ℱ.presheaf.map (Opens.infLELeft (U i) (closedSubsetOpenComplement hZ)).op
          ((si i).1) := by
            rw [hs i]
      _ = (ℱ.presheaf.obj (op (V i))).point := by
            exact (si i).2
  -- After restricting to the complement cover, the ambient gluing must be the point section.
  unfold ClosedSubsetSectionsWithSupport.Pointed.appPred
  simpa [V, iSup_inf_closedSubsetOpenComplement_eq hZ U] using
    pointed_section_eq_point_of_restrict_eq_point_on_cover ℱ V
      (ℱ.presheaf.map (Opens.infLELeft (iSup U) (closedSubsetOpenComplement hZ)).op s) ht

private theorem supportedTypePresheaf_isSheaf
    (hZ : IsClosed Z) (ℱ : X.Sheaf Pointed) :
    (supportedTypePresheaf hZ ℱ).IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hsf
  have hUnderlyingIsSheaf : (ℱ.presheaf ⋙ forget Pointed).IsSheaf := by
    exact
      (TopCat.Presheaf.isSheaf_iff_isSheaf_comp' (forget Pointed) ℱ.presheaf).1 ℱ.property
  have hcompat :
      (ℱ.presheaf ⋙ forget Pointed).IsCompatible U (fun i ↦ (sf i).1) := by
    intro i j
    exact congrArg Subtype.val (hsf i j)
  obtain ⟨s, hs, hsuniq⟩ :=
    TopCat.Presheaf.IsSheaf.isSheafUniqueGluing_types hUnderlyingIsSheaf
      (fun i ↦ (sf i).1) hcompat
  refine ⟨⟨s, supported_glue_restrict_eq_point hZ ℱ U sf s hs⟩, ?_, ?_⟩
  · intro i
    apply Subtype.ext
    exact hs i
  · intro t ht
    apply Subtype.ext
    exact hsuniq t.1 (fun i ↦ congrArg Subtype.val (ht i))

/-- The `Type`-valued sheaf on `X` consisting of sections whose restriction to the open complement
of `Z` is the distinguished point section. -/
private abbrev supportedTypeSheafOnX
    (hZ : IsClosed Z) (ℱ : X.Sheaf Pointed) : X.Sheaf (Type u) :=
  ⟨supportedTypePresheaf hZ ℱ, supportedTypePresheaf_isSheaf hZ ℱ⟩

/-- The distinguished point section defines a canonical morphism from the singleton sheaf to the
`Type`-valued sections-with-support sheaf on `X`. -/
/- The support condition for the distinguished point section is immediate from preservation of the
chosen point by restriction maps. -/
private theorem supportedTypeSheafOnX_point_mem
    (hZ : IsClosed Z) (ℱ : X.Sheaf Pointed) (U : (Opens X)ᵒᵖ) :
    ClosedSubsetSectionsWithSupport.Pointed.appPred hZ ℱ U.unop
      (ℱ.presheaf.obj U).point := by
  unfold ClosedSubsetSectionsWithSupport.Pointed.appPred
  simpa using
    (ℱ.presheaf.map (Opens.infLELeft U.unop (closedSubsetOpenComplement hZ)).op).map_point

private def supportedTypeSheafOnX_point
    (hZ : IsClosed Z) (ℱ : X.Sheaf Pointed) :
    TopCat.sheafToType X (ULift Unit) ⟶
      supportedTypeSheafOnX hZ ℱ :=
  ObjectProperty.homMk
    { app := fun U _ ↦
        show (supportedTypePresheaf hZ ℱ).obj U from
          ⟨(ℱ.presheaf.obj U).point, supportedTypeSheafOnX_point_mem hZ ℱ U⟩
      naturality := by
        intro U V i
        -- Both sides pick the distinguished point section and then restrict it.
        funext s
        apply Subtype.ext
        simpa [supportedTypePresheafMap] using ((ℱ.presheaf.map i).map_point).symm }

/-- The `Type`-valued map on sections-with-support sheaves induced by a morphism of pointed
sheaves. -/
/- A morphism of pointed sheaves preserves the support condition because it commutes with
restriction maps and preserves the distinguished points. -/
private theorem supportedTypeSheafOnX_map_mem
    (hZ : IsClosed Z) {ℱ 𝒢 : X.Sheaf Pointed} (φ : ℱ ⟶ 𝒢) (U : (Opens X)ᵒᵖ)
    (s : (supportedTypePresheaf hZ ℱ).obj U) :
    ClosedSubsetSectionsWithSupport.Pointed.appPred hZ 𝒢 U.unop (φ.1.app U s.1) := by
  -- Naturality of `φ` transports the support equation from `ℱ` to `𝒢`.
  have hs :
      ClosedSubsetSectionsWithSupport.Pointed.appPred hZ ℱ U.unop s.1 := s.2
  unfold ClosedSubsetSectionsWithSupport.Pointed.appPred at hs ⊢
  let i : U ⟶ op (U.unop ⊓ closedSubsetOpenComplement hZ) :=
    (Opens.infLELeft U.unop (closedSubsetOpenComplement hZ)).op
  have hnat :
      𝒢.presheaf.map i (φ.1.app U s.1) =
        φ.1.app (op (U.unop ⊓ closedSubsetOpenComplement hZ)) (ℱ.presheaf.map i s.1) := by
    simpa using
      congrFun (congrArg Pointed.Hom.toFun (φ.1.naturality i).symm) s.1
  calc
    𝒢.presheaf.map i (φ.1.app U s.1) =
      φ.1.app (op (U.unop ⊓ closedSubsetOpenComplement hZ)) (ℱ.presheaf.map i s.1) := by
        exact hnat
    _ = φ.1.app (op (U.unop ⊓ closedSubsetOpenComplement hZ))
        ((ℱ.presheaf.obj (op (U.unop ⊓ closedSubsetOpenComplement hZ))).point) := by
        rw [hs]
    _ = (𝒢.presheaf.obj (op (U.unop ⊓ closedSubsetOpenComplement hZ))).point := by
        simpa using
          (φ.1.app (op (U.unop ⊓ closedSubsetOpenComplement hZ))).map_point

private def supportedTypeSheafOnX_map
    (hZ : IsClosed Z) {ℱ 𝒢 : X.Sheaf Pointed} (φ : ℱ ⟶ 𝒢) :
    supportedTypeSheafOnX hZ ℱ ⟶ supportedTypeSheafOnX hZ 𝒢 :=
  ObjectProperty.homMk
    { app := fun U s ↦
        show (supportedTypePresheaf hZ 𝒢).obj U from
          ⟨φ.1.app U s.1, supportedTypeSheafOnX_map_mem hZ φ U s⟩
      naturality := by
        intro U V i
        -- Naturality is inherited from the underlying natural transformation `φ`.
        funext s
        apply Subtype.ext
        have hnat :
            φ.1.app V (ℱ.presheaf.map i s.1) = 𝒢.presheaf.map i (φ.1.app U s.1) := by
          simpa using
            congrFun (congrArg Pointed.Hom.toFun (φ.1.naturality i)) s.1
        change φ.1.app V (ℱ.presheaf.map i s.1) =
          𝒢.presheaf.map i (φ.1.app U s.1)
        exact hnat }

/-- A sheaf of types with a distinguished singleton-valued section family canonically determines a
sheaf of pointed sets. -/
private def pointifyPresheaf {Y : TopCat.{u}} (F : Y.Sheaf (Type u))
    (η : TopCat.sheafToType Y (ULift Unit) ⟶ F) : Y.Presheaf Pointed where
  obj U := Pointed.of (η.1.app U (fun _ ↦ ⟨()⟩))
  map {U V} i :=
    ⟨fun s ↦ F.1.map i s, by
      change F.1.map i (η.1.app U (fun _ ↦ ⟨()⟩)) = η.1.app V (fun _ ↦ ⟨()⟩)
      simpa using (congrFun (η.1.naturality i) (fun _ ↦ ⟨()⟩)).symm⟩
  map_id := by
    -- The pointified restriction map has the same underlying identity law as `F`.
    intro U
    apply Pointed.Hom.ext
    funext s
    simpa using congrFun (F.1.map_id U) s
  map_comp := by
    -- The pointified restriction maps compose exactly as those of `F`.
    intro U V W i j
    apply Pointed.Hom.ext
    funext s
    simpa using congrFun (F.1.map_comp i j) s

/-- Helper for Remark 17.6.4: the pointified presheaf is a sheaf because forgetting to types
recovers the original type-valued sheaf. -/
private theorem pointifyPresheaf_isSheaf {Y : TopCat.{u}} (F : Y.Sheaf (Type u))
    (η : TopCat.sheafToType Y (ULift Unit) ⟶ F) :
    (pointifyPresheaf F η).IsSheaf := by
  -- Route correction: the imported Pointed algebraic-structure instance makes the standard
  -- forgetful sheaf bridge available, so the underlying type-valued sheaf condition is enough.
  exact
    (TopCat.Presheaf.isSheaf_iff_isSheaf_comp' (forget Pointed) (pointifyPresheaf F η)).2 <| by
      simpa [pointifyPresheaf] using F.property

/-- A sheaf of types with a distinguished singleton-valued section family canonically determines a
sheaf of pointed sets. -/
private abbrev pointifySheaf {Y : TopCat.{u}} (F : Y.Sheaf (Type u))
    (η : TopCat.sheafToType Y (ULift Unit) ⟶ F) : Y.Sheaf Pointed :=
  ⟨pointifyPresheaf F η, pointifyPresheaf_isSheaf F η⟩

/-- A morphism of type-valued sheaves respecting distinguished singleton-valued sections induces a
morphism of the associated sheaves of pointed sets. -/
/- The pointified map preserves chosen points exactly because the distinguished sections are
compatible with `φ`. -/
private theorem pointifySheafMap_app_preserves_point
    {Y : TopCat.{u}} {F G : Y.Sheaf (Type u)}
    {ηF : TopCat.sheafToType Y (ULift Unit) ⟶ F}
    {ηG : TopCat.sheafToType Y (ULift Unit) ⟶ G}
    (φ : F ⟶ G) (hφ : ηF ≫ φ = ηG) (U : (Opens Y)ᵒᵖ) :
    φ.1.app U ((pointifySheaf F ηF).presheaf.obj U).point =
      ((pointifySheaf G ηG).presheaf.obj U).point := by
  change φ.1.app U (ηF.1.app U (fun _ ↦ ⟨()⟩)) = ηG.1.app U (fun _ ↦ ⟨()⟩)
  exact congrFun (congrArg (fun α ↦ α.1.app U) hφ) (fun _ ↦ ⟨()⟩)

private def pointifySheafMap {Y : TopCat.{u}} {F G : Y.Sheaf (Type u)}
    {ηF : TopCat.sheafToType Y (ULift Unit) ⟶ F}
    {ηG : TopCat.sheafToType Y (ULift Unit) ⟶ G}
    (φ : F ⟶ G) (hφ : ηF ≫ φ = ηG) :
    pointifySheaf F ηF ⟶ pointifySheaf G ηG :=
  ObjectProperty.homMk
    { app := fun U ↦
        ⟨φ.1.app U, pointifySheafMap_app_preserves_point φ hφ U⟩
      naturality := by
        -- Naturality is exactly the naturality of `φ` on underlying type-valued sections.
        intro U V i
        apply Pointed.Hom.ext
        funext s
        simpa using congrFun (φ.1.naturality i) s }

private theorem supportedTypeSheafOnX_point_naturality
    (hZ : IsClosed Z) {ℱ 𝒢 : X.Sheaf Pointed} (φ : ℱ ⟶ 𝒢) :
    supportedTypeSheafOnX_point hZ ℱ ≫ supportedTypeSheafOnX_map hZ φ =
      supportedTypeSheafOnX_point hZ 𝒢 := by
  -- Both composites send the unique local section to the distinguished point of `𝒢`.
  apply CategoryTheory.Sheaf.hom_ext
  ext U s
  apply Subtype.ext
  simpa [supportedTypeSheafOnX_point, supportedTypeSheafOnX_map] using
    (φ.1.app U).map_point

/-- Internal bridge/view: the pointed sheaf on `X` whose sections restrict to the distinguished
point section on the open complement `X \ Z`. -/
private def ClosedSubsetSectionsWithSupport.Pointed.bridgeObject
    (hZ : IsClosed Z) (ℱ : X.Sheaf Pointed) : X.Sheaf Pointed :=
  pointifySheaf (supportedTypeSheafOnX hZ ℱ) (supportedTypeSheafOnX_point hZ ℱ)

/-- Helper for Remark 17.6.4: on an open contained in the complement `X \ Z`, any ambient section
whose support lies in `Z` is already the distinguished point section. -/
private theorem pushforward_section_eq_point_of_le_complement
    (hZ : IsClosed Z) (ℱ : (TopCat.of Z).Sheaf Pointed) {U : Opens X}
    (hU : U ≤ closedSubsetOpenComplement hZ)
    (s : ((Sheaf.pushforward Pointed iZ).obj ℱ).presheaf.obj (op U)) :
    s = (((Sheaf.pushforward Pointed iZ).obj ℱ).presheaf.obj (op U)).point := by
  -- Route correction: identify the inverse-image open in `Z` with `⊥`, then use that sections
  -- over the empty open are terminal in any sheaf of pointed sets.
  let G := (Sheaf.pushforward Pointed iZ).obj ℱ
  have hEq : (Opens.map iZ).obj U = ⊥ := by
    ext z
    constructor
    · intro hz
      exact (hU hz) z.2
    · intro hz
      cases hz
  change s = (ℱ.presheaf.obj (op ((Opens.map iZ).obj U))).point
  let A : Pointed := ℱ.presheaf.obj (op ((Opens.map iZ).obj U))
  have hA : IsTerminal A := by
    simpa [A] using ℱ.isTerminalOfEqEmpty hEq
  let c : A ⟶ A := ⟨fun _ ↦ A.point, rfl⟩
  have hc : (𝟙 A : A ⟶ A) = c := hA.hom_ext _ _
  exact congrFun (congrArg Pointed.Hom.toFun hc) s

/-- Helper for Remark 17.6.4: a pointed object with only one element is terminal. -/
private theorem terminal_from_isIso_of_subsingleton (P : Pointed) [Subsingleton P] :
    IsIso (terminal.from P) := by
  let g : ⊤_ Pointed ⟶ P := ⟨fun _ ↦ P.point, rfl⟩
  -- In a subsingleton pointed set, the unique map to and from the terminal object are inverse.
  refine ⟨⟨g, ?_, ?_⟩⟩
  · apply Pointed.Hom.ext
    funext x
    exact Subsingleton.elim _ _
  · apply Pointed.Hom.ext
    funext x
    exact Subsingleton.elim _ _

/-- Helper for Remark 17.6.4: if all sections on some neighbourhood of `x` and its smaller opens
are already the distinguished point, then the stalk at `x` is terminal. -/
private theorem stalk_isTerminal_of_locally_eq_point
    (𝒢 : X.Sheaf Pointed) (x : X) {U : Opens X} (hxU : x ∈ U)
    (hU : ∀ ⦃V : Opens X⦄, V ≤ U →
      ∀ s : 𝒢.presheaf.obj (op V), s = (𝒢.presheaf.obj (op V)).point) :
    IsIso (terminal.from (𝒢.presheaf.stalk x)) := by
  -- Any germ is represented on some neighborhood, and shrinking to `U` identifies it with the
  -- germ of the distinguished point section on `U`.
  letI : Subsingleton (𝒢.presheaf.stalk x) := by
    refine ⟨fun m n ↦ ?_⟩
    obtain ⟨V, hxV, s, rfl⟩ := TopCat.Presheaf.germ_exist 𝒢.presheaf x m
    obtain ⟨W, hxW, t, rfl⟩ := TopCat.Presheaf.germ_exist 𝒢.presheaf x n
    have hs_point :
        𝒢.presheaf.germ V x hxV s =
          𝒢.presheaf.germ U x hxU ((𝒢.presheaf.obj (op U)).point) := by
      have hVU : V ⊓ U ≤ U := by
        intro y hy
        exact hy.2
      have hs_restrict :
          𝒢.presheaf.map (Opens.infLELeft V U).op s =
            (𝒢.presheaf.obj (op (V ⊓ U))).point := by
        exact hU hVU (𝒢.presheaf.map (Opens.infLELeft V U).op s)
      have hpoint_restrict :
          𝒢.presheaf.map (Opens.infLERight V U).op ((𝒢.presheaf.obj (op U)).point) =
            (𝒢.presheaf.obj (op (V ⊓ U))).point := by
        simpa using (𝒢.presheaf.map (Opens.infLERight V U).op).map_point
      exact 𝒢.presheaf.germ_ext (V ⊓ U) ⟨hxV, hxU⟩
        (Opens.infLELeft V U) (Opens.infLERight V U) (hs_restrict.trans hpoint_restrict.symm)
    have ht_point :
        𝒢.presheaf.germ W x hxW t =
          𝒢.presheaf.germ U x hxU ((𝒢.presheaf.obj (op U)).point) := by
      have hWU : W ⊓ U ≤ U := by
        intro y hy
        exact hy.2
      have ht_restrict :
          𝒢.presheaf.map (Opens.infLELeft W U).op t =
            (𝒢.presheaf.obj (op (W ⊓ U))).point := by
        exact hU hWU (𝒢.presheaf.map (Opens.infLELeft W U).op t)
      have hpoint_restrict :
          𝒢.presheaf.map (Opens.infLERight W U).op ((𝒢.presheaf.obj (op U)).point) =
            (𝒢.presheaf.obj (op (W ⊓ U))).point := by
        simpa using (𝒢.presheaf.map (Opens.infLERight W U).op).map_point
      exact 𝒢.presheaf.germ_ext (W ⊓ U) ⟨hxW, hxU⟩
        (Opens.infLELeft W U) (Opens.infLERight W U) (ht_restrict.trans hpoint_restrict.symm)
    exact hs_point.trans ht_point.symm
  -- Once the stalk is a subsingleton pointed set, the map to the terminal object is an
  -- isomorphism.
  simpa using terminal_from_isIso_of_subsingleton (𝒢.presheaf.stalk x)

/-- Helper for Remark 17.6.4: every section of a pushed-forward pointed sheaf is automatically
supported in `Z`, so the support-subsheaf inclusion is an isomorphism. -/
private theorem appPred_iff_eq_point_of_le_complement
    (hZ : IsClosed Z) (ℱ : X.Sheaf Pointed) {U : Opens X}
    (hU : U ≤ closedSubsetOpenComplement hZ)
    (s : ℱ.presheaf.obj (op U)) :
    ClosedSubsetSectionsWithSupport.Pointed.appPred hZ ℱ U s ↔
      s = (ℱ.presheaf.obj (op U)).point := by
  have hEq : U ⊓ closedSubsetOpenComplement hZ = U := by
    ext x
    constructor
    · intro hx
      exact hx.1
    · intro hx
      exact ⟨hx, hU hx⟩
  -- On an open already contained in the complement, the support restriction is just the identity.
  unfold ClosedSubsetSectionsWithSupport.Pointed.appPred
  simpa [hEq]

/-- Helper for Remark 17.6.4: every section of a pushed-forward pointed sheaf is automatically
supported in `Z`, so the support-subsheaf inclusion is an isomorphism. -/
private theorem restriction_eq_point_of_le_complement
    (hZ : IsClosed Z) (ℱ : X.Sheaf Pointed) {U : Opens X}
    (hU : U ≤ closedSubsetOpenComplement hZ)
    (s : ℱ.presheaf.obj (op U))
    (hs : ClosedSubsetSectionsWithSupport.Pointed.appPred hZ ℱ U s) :
    s = (ℱ.presheaf.obj (op U)).point := by
  -- Rewrite the support condition on a complement-contained open into the desired point equality.
  exact (appPred_iff_eq_point_of_le_complement hZ ℱ hU s).mp hs

/-- Helper for Remark 17.6.4: on an open contained in the complement `X \ Z`, a section supported
in `Z` is already the distinguished point section. -/
private theorem supported_section_eq_point_of_le_complement
    (hZ : IsClosed Z) (ℱ : X.Sheaf Pointed) {U : Opens X}
    (hU : U ≤ closedSubsetOpenComplement hZ)
    (s : (ClosedSubsetSectionsWithSupport.Pointed.bridgeObject hZ ℱ).presheaf.obj (op U)) :
    s = ((ClosedSubsetSectionsWithSupport.Pointed.bridgeObject hZ ℱ).presheaf.obj (op U)).point := by
  -- The bridge object packages raw supported sections, so equality reduces to the ambient lemma.
  apply Subtype.ext
  exact restriction_eq_point_of_le_complement hZ ℱ hU s.1 s.2

/-- Internal bridge/view: the pointed map on sections-with-support sheaves induced by a morphism
of pointed sheaves. -/
private def bridgeMap
    (hZ : IsClosed Z) {ℱ 𝒢 : X.Sheaf Pointed} (φ : ℱ ⟶ 𝒢) :
    ClosedSubsetSectionsWithSupport.Pointed.bridgeObject hZ ℱ ⟶
      ClosedSubsetSectionsWithSupport.Pointed.bridgeObject hZ 𝒢 :=
  pointifySheafMap
    (supportedTypeSheafOnX_map hZ φ)
    (supportedTypeSheafOnX_point_naturality hZ φ)

namespace ClosedSubsetSectionsWithSupport.Pointed

-- Proof sketch: sections with support in `Z` first form a pointed sheaf on `X`, namely the
-- pointed subsheaf whose sections restrict to the distinguished point on `X \ Z`; restricting
-- that pointed sheaf to `Z` yields the source-facing pointed closed-support functor
-- `\mathcal H_Z = 𝓗[hZ]`.
/-- The canonical inclusion from the pointed closed-support object back into `ℱ`. -/
private def subsheafHom
    (hZ : IsClosed Z) (ℱ : X.Sheaf Pointed) :
    bridgeObject hZ ℱ ⟶ ℱ := by
  refine ObjectProperty.homMk ?_
  refine
    { app := fun U ↦ ?_
      naturality := ?_ }
  · refine ⟨fun s ↦ s.1, ?_⟩
    rfl
  · intro U V i
    ext s
    rfl

private instance subsheafHom_mono
    (hZ : IsClosed Z) (ℱ : X.Sheaf Pointed) :
    Mono (subsheafHom hZ ℱ) := by
  letI : (TopCat.Sheaf.forget Pointed X).ReflectsMonomorphisms :=
    Functor.reflectsMonomorphisms_of_faithful (TopCat.Sheaf.forget Pointed X)
  apply (TopCat.Sheaf.forget Pointed X).mono_of_mono_map
  exact
    (NatTrans.mono_iff_mono_app ((TopCat.Sheaf.forget Pointed X).map (subsheafHom hZ ℱ))).2
      fun U ↦
        by
          let g := ((TopCat.Sheaf.forget Pointed X).map (subsheafHom hZ ℱ)).app U
          letI : (forget Pointed).ReflectsMonomorphisms :=
            Functor.reflectsMonomorphisms_of_faithful (forget Pointed)
          exact (forget Pointed).mono_of_mono_map <|
            (CategoryTheory.mono_iff_injective ((forget Pointed).map g)).2
              fun s t hst ↦ Subtype.ext hst

/-- The pointed closed-support subsheaf of `ℱ` on `X`: its local sections are exactly the
sections whose restriction to the open complement `X \ Z` is the distinguished point. -/
def subsheaf
    (hZ : IsClosed Z) (ℱ : X.Sheaf Pointed) : Subobject ℱ :=
  Subobject.mk (subsheafHom hZ ℱ)

/-- The pointed sheaf on the closed subset `Z` obtained by restricting the pointed closed-support
subsheaf of `ℱ` on `X`. -/
def sheaf
    (hZ : IsClosed Z) (ℱ : X.Sheaf Pointed) :
    (TopCat.of Z).Sheaf Pointed :=
  (Sheaf.pullback Pointed iZ).obj ((subsheaf hZ ℱ : Subobject ℱ) : X.Sheaf Pointed)

/-- The morphism on pointed closed-support subsheaves induced by a morphism of pointed sheaves. -/
def subsheafMap
    (hZ : IsClosed Z) {ℱ 𝒢 : X.Sheaf Pointed} (φ : ℱ ⟶ 𝒢) :
    ((subsheaf hZ ℱ : Subobject ℱ) : X.Sheaf Pointed) ⟶
      ((subsheaf hZ 𝒢 : Subobject 𝒢) : X.Sheaf Pointed) :=
  (Subobject.underlyingIso (subsheafHom hZ ℱ)).hom ≫
    bridgeMap hZ φ ≫
      (Subobject.underlyingIso (subsheafHom hZ 𝒢)).inv

/-- Helper for Remark 17.6.4: the bridge-level map induced by `φ` commutes with the ambient
support inclusion maps. -/
private theorem bridgeMap_comp_subsheafHom
    (hZ : IsClosed Z) {ℱ 𝒢 : X.Sheaf Pointed} (φ : ℱ ⟶ 𝒢) :
    bridgeMap hZ φ ≫ subsheafHom hZ 𝒢 = subsheafHom hZ ℱ ≫ φ := by
  -- Both composites forget the support witness and then apply `φ` objectwise.
  apply CategoryTheory.Sheaf.hom_ext
  ext U s
  rfl

/-- Helper for Remark 17.6.4: the induced subobject morphism is the unique map whose composite
with the support inclusion equals the ambient morphism. -/
private theorem subsheafMap_comp_arrow
    (hZ : IsClosed Z) {ℱ 𝒢 : X.Sheaf Pointed} (φ : ℱ ⟶ 𝒢) :
    subsheafMap hZ φ ≫ (subsheaf hZ 𝒢).arrow = (subsheaf hZ ℱ).arrow ≫ φ := by
  -- Normalize both `Subobject.underlyingIso` boundaries back to the concrete support inclusion.
  calc
    subsheafMap hZ φ ≫ (subsheaf hZ 𝒢).arrow =
      (Subobject.underlyingIso (subsheafHom hZ ℱ)).hom ≫
        bridgeMap hZ φ ≫
          subsheafHom hZ 𝒢 := by
            simp [subsheafMap, subsheaf, Category.assoc]
    _ =
      (Subobject.underlyingIso (subsheafHom hZ ℱ)).hom ≫
        subsheafHom hZ ℱ ≫ φ := by
          rw [bridgeMap_comp_subsheafHom]
          simp [Category.assoc]
    _ = (subsheaf hZ ℱ).arrow ≫ φ := by
          simp [subsheaf, Category.assoc]

/-- Helper for Remark 17.6.4: the induced morphism on pointed support subsheaves respects
identity morphisms. -/
private theorem subsheafMap_id
    (hZ : IsClosed Z) (ℱ : X.Sheaf Pointed) :
    subsheafMap hZ (𝟙 ℱ) = 𝟙 ((subsheaf hZ ℱ : Subobject ℱ) : X.Sheaf Pointed) := by
  -- The support inclusion is mono, so equality follows after composing into `ℱ`.
  apply (cancel_mono (subsheaf hZ ℱ).arrow).1
  rw [subsheafMap_comp_arrow]
  simp

/-- Helper for Remark 17.6.4: the induced morphism on pointed support subsheaves respects
composition. -/
private theorem subsheafMap_comp
    (hZ : IsClosed Z) {ℱ 𝒢 𝒦 : X.Sheaf Pointed}
    (φ : ℱ ⟶ 𝒢) (ψ : 𝒢 ⟶ 𝒦) :
    subsheafMap hZ (φ ≫ ψ) =
      subsheafMap hZ φ ≫ subsheafMap hZ ψ := by
  -- Again it is enough to compare the composites into the ambient target sheaf.
  apply (cancel_mono (subsheaf hZ 𝒦).arrow).1
  calc
    subsheafMap hZ (φ ≫ ψ) ≫ (subsheaf hZ 𝒦).arrow =
      (subsheaf hZ ℱ).arrow ≫ (φ ≫ ψ) := by
        rw [subsheafMap_comp_arrow]
    _ = ((subsheaf hZ ℱ).arrow ≫ φ) ≫ ψ := by
          simp [Category.assoc]
    _ = (subsheafMap hZ φ ≫ (subsheaf hZ 𝒢).arrow) ≫ ψ := by
          rw [subsheafMap_comp_arrow]
    _ = subsheafMap hZ φ ≫ ((subsheaf hZ 𝒢).arrow ≫ ψ) := by
          simp [Category.assoc]
    _ = subsheafMap hZ φ ≫ (subsheafMap hZ ψ ≫ (subsheaf hZ 𝒦).arrow) := by
          rw [subsheafMap_comp_arrow]
    _ = (subsheafMap hZ φ ≫ subsheafMap hZ ψ) ≫ (subsheaf hZ 𝒦).arrow := by
          simp [Category.assoc]

/-- Helper for Remark 17.6.4: the pointed closed-support functor preserves identity morphisms. -/
private theorem functor_map_id
    (hZ : IsClosed Z) (ℱ : X.Sheaf Pointed) :
    (Sheaf.pullback Pointed iZ).map (subsheafMap hZ (𝟙 ℱ)) = 𝟙 (sheaf hZ ℱ) := by
  -- Pullback preserves the identity once the support-subobject map does.
  simpa [sheaf] using congrArg ((Sheaf.pullback Pointed iZ).map) (subsheafMap_id hZ ℱ)

/-- Helper for Remark 17.6.4: the pointed closed-support functor preserves composition. -/
private theorem functor_map_comp
    (hZ : IsClosed Z) {ℱ 𝒢 𝒦 : X.Sheaf Pointed}
    (φ : ℱ ⟶ 𝒢) (ψ : 𝒢 ⟶ 𝒦) :
    (Sheaf.pullback Pointed iZ).map (subsheafMap hZ (φ ≫ ψ)) =
      (Sheaf.pullback Pointed iZ).map (subsheafMap hZ φ) ≫
        (Sheaf.pullback Pointed iZ).map (subsheafMap hZ ψ) := by
  -- Pullback preserves composition once the support-subobject map does.
  simpa [sheaf] using congrArg ((Sheaf.pullback Pointed iZ).map) (subsheafMap_comp hZ φ ψ)

/-- Remark 17.6.4: the pointed closed-support functor along a closed subset inclusion, written
`𝓗[hZ] = \mathcal H_Z`, sends a pointed sheaf `\mathcal F` on `X` to the pointed sheaf on `Z`
obtained by restricting the pointed closed-support subsheaf on `X` to `Z`. -/
@[stacks 01B0]
def functor
    (hZ : IsClosed Z) :
    X.Sheaf Pointed ⥤ (TopCat.of Z).Sheaf Pointed :=
  { obj := sheaf hZ
    map := fun φ ↦ (Sheaf.pullback Pointed iZ).map (subsheafMap hZ φ)
    map_id := functor_map_id hZ
    map_comp := functor_map_comp hZ }

end ClosedSubsetSectionsWithSupport.Pointed

namespace ClosedSubsetSectionsWithSupport.Pointed

scoped notation "𝓗[" hZ "]" => functor hZ

end ClosedSubsetSectionsWithSupport.Pointed

open scoped ClosedSubsetSectionsWithSupport.Pointed

namespace ClosedSubsetSectionsWithSupport.Pointed

variable (hZ : IsClosed Z)

private theorem subsheaf_arrow_app_apply
    (ℱ : X.Sheaf Pointed) (U : Opens X)
    (t : (((subsheaf hZ ℱ : Subobject ℱ) : X.Sheaf Pointed).presheaf.obj (op U))) :
    ((subsheaf hZ ℱ).arrow.1.app (op U)) t =
      ((subsheafHom hZ ℱ).1.app (op U))
        (((Subobject.underlyingIso (subsheafHom hZ ℱ)).hom.1.app (op U)) t) := by
  change (((Subobject.mk (subsheafHom hZ ℱ)).arrow).1.app (op U)) t =
      ((subsheafHom hZ ℱ).1.app (op U))
        (((Subobject.underlyingIso (subsheafHom hZ ℱ)).hom.1.app (op U)) t)
  rw [← Subobject.underlyingIso_hom_comp_eq_mk (subsheafHom hZ ℱ)]
  rfl

private theorem subsheaf_arrow_inv_app_apply
    (ℱ : X.Sheaf Pointed) (U : Opens X)
    (t : (bridgeObject hZ ℱ).presheaf.obj (op U)) :
    ((subsheaf hZ ℱ).arrow.1.app (op U))
        (((Subobject.underlyingIso (subsheafHom hZ ℱ)).inv.1.app (op U)) t) =
      ((subsheafHom hZ ℱ).1.app (op U)) t := by
  change (((Subobject.underlyingIso (subsheafHom hZ ℱ)).inv ≫
      ((Subobject.mk (subsheafHom hZ ℱ)).arrow)).1.app (op U)) t =
    ((subsheafHom hZ ℱ).1.app (op U)) t
  simpa using
    congrArg (fun η ↦ η.1.app (op U) t)
      (Subobject.underlyingIso_arrow (subsheafHom hZ ℱ))

/-- For an open set `U ⊆ X`, the image of the canonical map
`(subsheaf hZ ℱ)(U) → ℱ(U)` is exactly the set of sections whose restriction to
`U ∩ (X \ Z)` is the distinguished point. -/
theorem subsheaf_app_range
    (ℱ : X.Sheaf Pointed) (U : Opens X) :
    Set.range ((subsheaf hZ ℱ).arrow.1.app (op U)) =
      { s | appPred hZ ℱ U s } := by
  ext s
  constructor
  · rintro ⟨t, rfl⟩
    rw [subsheaf_arrow_app_apply hZ ℱ U t]
    exact (((Subobject.underlyingIso (subsheafHom hZ ℱ)).hom.1.app (op U)) t).2
  · intro hs
    refine
      ⟨((Subobject.underlyingIso (subsheafHom hZ ℱ)).inv.1.app (op U) ⟨s, hs⟩), ?_⟩
    rw [subsheaf_arrow_inv_app_apply hZ ℱ U ⟨s, hs⟩]
    rfl

/-- A section of `ℱ(U)` lies in the image of `(subsheaf hZ ℱ)(U) → ℱ(U)` exactly when its
restriction to `U ∩ (X \ Z)` is the distinguished point. -/
theorem subsheaf_app_iff
    (ℱ : X.Sheaf Pointed) (U : Opens X) (s : ℱ.presheaf.obj (op U)) :
    s ∈ Set.range ((subsheaf hZ ℱ).arrow.1.app (op U)) ↔
      appPred hZ ℱ U s := by
  simpa using congrArg (fun S : Set (ℱ.presheaf.obj (op U)) ↦ s ∈ S) (subsheaf_app_range hZ ℱ U)

variable {hZ}

/-- Helper for Remark 17.6.4: if `x ∉ Z`, then the stalk of the supported-subsheaf object at `x`
is terminal. -/
private theorem subsheaf_stalk_isTerminal_of_not_mem
    (hZ : IsClosed Z) (ℱ : X.Sheaf Pointed) {x : X} (hx : x ∉ Z) :
    IsIso
      (terminal.from ((((subsheaf hZ ℱ : Subobject ℱ) : X.Sheaf Pointed).presheaf.stalk x))) := by
  have hbridge :
      IsIso (terminal.from ((bridgeObject hZ ℱ).presheaf.stalk x)) := by
    -- On the complement of `Z`, every supported section is already the distinguished point.
    apply stalk_isTerminal_of_locally_eq_point
      (𝒢 := bridgeObject hZ ℱ) (x := x) (U := closedSubsetOpenComplement hZ)
    · exact hx
    · intro V hV s
      exact supported_section_eq_point_of_le_complement hZ ℱ hV s
  let e :
      ((((subsheaf hZ ℱ : Subobject ℱ) : X.Sheaf Pointed).presheaf.stalk x)) ≅
        ((bridgeObject hZ ℱ).presheaf.stalk x) :=
    (TopCat.Presheaf.stalkFunctor Pointed x).mapIso
      ((TopCat.Sheaf.forget Pointed X).mapIso (Subobject.underlyingIso (subsheafHom hZ ℱ)))
  have hcomp :
      e.hom ≫ terminal.from ((bridgeObject hZ ℱ).presheaf.stalk x) =
        terminal.from ((((subsheaf hZ ℱ : Subobject ℱ) : X.Sheaf Pointed).presheaf.stalk x)) := by
    exact terminalIsTerminal.hom_ext _ _
  -- Transport terminality across the canonical stalk isomorphism coming from
  -- `Subobject.underlyingIso`.
  rw [← hcomp]
  infer_instance

private theorem subsheaf_pushforward_arrow_isIso
    (hZ : IsClosed Z) (ℱ : (TopCat.of Z).Sheaf Pointed) :
    IsIso
      (subsheaf hZ ((Sheaf.pushforward Pointed iZ).obj ℱ)).arrow := by
  let G := (Sheaf.pushforward Pointed iZ).obj ℱ
  -- Reflect the isomorphism to the underlying presheaf map and check it objectwise.
  rw [← CategoryTheory.isIso_iff_of_reflects_iso
    (subsheaf hZ G).arrow
    (TopCat.Sheaf.forget Pointed X)]
  rw [CategoryTheory.NatTrans.isIso_iff_isIso_app]
  intro U
  rw [CategoryTheory.isIso_iff_bijective]
  constructor
  · intro s t hst
    exact Subtype.ext hst
  · intro s
    have hs : ClosedSubsetSectionsWithSupport.Pointed.appPred hZ G U.unop s := by
      -- Restricting once more to the complement leaves a pushed-forward section on the complement.
      unfold ClosedSubsetSectionsWithSupport.Pointed.appPred
      simpa using
        pushforward_section_eq_point_of_le_complement hZ ℱ
          (U := U.unop ⊓ closedSubsetOpenComplement hZ)
          (fun x hx ↦ hx.2)
          (G.presheaf.map (Opens.infLELeft U.unop (closedSubsetOpenComplement hZ)).op s)
    exact (subsheaf_app_iff hZ G U.unop s).2 hs

private theorem subsheaf_pullback_pushforward_unit_isIso
    (hZ : IsClosed Z) (ℱ : X.Sheaf Pointed) :
    IsIso
      ((Sheaf.pullbackPushforwardAdjunction Pointed iZ).unit.app
        (((subsheaf hZ ℱ : Subobject ℱ) : X.Sheaf Pointed))) := by
  have hess :
      (Sheaf.pushforward Pointed iZ).essImage
        (((subsheaf hZ ℱ : Subobject ℱ) : X.Sheaf Pointed)) := by
    exact
      (closedSubsetSheafPushforward_essImage_iff_stalk_isTerminal_of_not_mem Z hZ
        (((subsheaf hZ ℱ : Subobject ℱ) : X.Sheaf Pointed))).2
        (fun x hx ↦ subsheaf_stalk_isTerminal_of_not_mem hZ ℱ hx)
  let _ : (Sheaf.pushforward Pointed iZ).Full := inferInstance
  let _ : (Sheaf.pushforward Pointed iZ).Faithful := inferInstance
  -- The unit is invertible exactly on the essential image of the fully faithful pushforward.
  exact
    (((TopCat.Sheaf.pullbackPushforwardAdjunction Pointed iZ).isIso_unit_app_iff_mem_essImage :
      IsIso
        ((TopCat.Sheaf.pullbackPushforwardAdjunction Pointed iZ).unit.app
          (((subsheaf hZ ℱ : Subobject ℱ) : X.Sheaf Pointed))) ↔
            (Sheaf.pushforward Pointed iZ).essImage
              (((subsheaf hZ ℱ : Subobject ℱ) : X.Sheaf Pointed))).2
      hess)

/-- Helper for Remark 17.6.4: a morphism out of a pushed-forward sheaf lands in the bridge object
of supported sections. -/
private theorem pushforwardLiftToBridge_mem
    (hZ : IsClosed Z) {A : (TopCat.of Z).Sheaf Pointed} {B : X.Sheaf Pointed}
    (f : (Sheaf.pushforward Pointed iZ).obj A ⟶ B) (U : (Opens X)ᵒᵖ)
    (s : ((Sheaf.pushforward Pointed iZ).obj A).presheaf.obj U) :
    appPred hZ B U.unop ((f.1.app U) s) := by
  -- Naturality rewrites the complement restriction of `f.app U s` to the image of the
  -- complement restriction of `s`, and that pushed-forward section is already the point.
  unfold ClosedSubsetSectionsWithSupport.Pointed.appPred
  let i : U ⟶ op (U.unop ⊓ closedSubsetOpenComplement hZ) :=
    (Opens.infLELeft U.unop (closedSubsetOpenComplement hZ)).op
  have hnat :
      B.presheaf.map i ((f.1.app U) s) =
        f.1.app (op (U.unop ⊓ closedSubsetOpenComplement hZ))
          (((Sheaf.pushforward Pointed iZ).obj A).presheaf.map i s) := by
    simpa using
      congrFun (congrArg Pointed.Hom.toFun (f.1.naturality i).symm) s
  calc
    B.presheaf.map i ((f.1.app U) s) =
      f.1.app (op (U.unop ⊓ closedSubsetOpenComplement hZ))
        (((Sheaf.pushforward Pointed iZ).obj A).presheaf.map i s) := by
          exact hnat
    _ =
      f.1.app (op (U.unop ⊓ closedSubsetOpenComplement hZ))
        ((((Sheaf.pushforward Pointed iZ).obj A).presheaf.obj
          (op (U.unop ⊓ closedSubsetOpenComplement hZ))).point) := by
          rw [pushforward_section_eq_point_of_le_complement hZ A
            (U := U.unop ⊓ closedSubsetOpenComplement hZ) (fun x hx ↦ hx.2)
            (((Sheaf.pushforward Pointed iZ).obj A).presheaf.map i s)]
    _ = (B.presheaf.obj (op (U.unop ⊓ closedSubsetOpenComplement hZ))).point := by
          simpa using
            (f.1.app (op (U.unop ⊓ closedSubsetOpenComplement hZ))).map_point

/-- Helper for Remark 17.6.4: a morphism out of a pushed-forward sheaf factors through the bridge
object of supported sections. -/
private def pushforwardLiftToBridge
    (hZ : IsClosed Z) {A : (TopCat.of Z).Sheaf Pointed} {B : X.Sheaf Pointed}
    (f : (Sheaf.pushforward Pointed iZ).obj A ⟶ B) :
    (Sheaf.pushforward Pointed iZ).obj A ⟶ bridgeObject hZ B :=
  ObjectProperty.homMk
    { app := fun U ↦
        ⟨fun s ↦ ⟨f.1.app U s, pushforwardLiftToBridge_mem hZ f U s⟩, by
          apply Subtype.ext
          simpa using (f.1.app U).map_point⟩
      naturality := by
        intro U V i
        apply Pointed.Hom.ext
        funext s
        apply Subtype.ext
        change f.1.app V (((Sheaf.pushforward Pointed iZ).obj A).presheaf.map i s) =
          B.presheaf.map i (f.1.app U s)
        simpa using congrFun (congrArg Pointed.Hom.toFun (f.1.naturality i)) s }

/-- Helper for Remark 17.6.4: the bridge lift is functorial in the source morphism. -/
private theorem pushforwardLiftToBridge_naturality_left
    (hZ : IsClosed Z)
    {A₁ A₂ : (TopCat.of Z).Sheaf Pointed} {B : X.Sheaf Pointed}
    (u : A₁ ⟶ A₂) (f : (Sheaf.pushforward Pointed iZ).obj A₂ ⟶ B) :
    pushforwardLiftToBridge hZ ((Sheaf.pushforward Pointed iZ).map u ≫ f) =
      (Sheaf.pushforward Pointed iZ).map u ≫ pushforwardLiftToBridge hZ f := by
  -- The bridge lift is defined pointwise by the ambient section map, so source composition is
  -- literal composition on the underlying functions.
  apply CategoryTheory.Sheaf.hom_ext
  ext U s
  apply Subtype.ext
  rfl

/-- Helper for Remark 17.6.4: the bridge lift is functorial in the target morphism. -/
private theorem pushforwardLiftToBridge_naturality_right
    (hZ : IsClosed Z)
    {A : (TopCat.of Z).Sheaf Pointed} {B C : X.Sheaf Pointed}
    (f : (Sheaf.pushforward Pointed iZ).obj A ⟶ B) (g : B ⟶ C) :
    pushforwardLiftToBridge hZ (f ≫ g) =
      pushforwardLiftToBridge hZ f ≫ bridgeMap hZ g := by
  -- The supported witness is preserved by `g`, so target composition is again pointwise.
  apply CategoryTheory.Sheaf.hom_ext
  ext U s
  apply Subtype.ext
  rfl

/-- Helper for Remark 17.6.4: every morphism out of a pushed-forward sheaf factors through the
actual supported subobject. -/
private def pushforwardLiftToSubsheaf
    (hZ : IsClosed Z) {A : (TopCat.of Z).Sheaf Pointed} {B : X.Sheaf Pointed}
    (f : (Sheaf.pushforward Pointed iZ).obj A ⟶ B) :
    (Sheaf.pushforward Pointed iZ).obj A ⟶
      ((subsheaf hZ B : Subobject B) : X.Sheaf Pointed) :=
  pushforwardLiftToBridge hZ f ≫ (Subobject.underlyingIso (subsheafHom hZ B)).inv

/-- Helper for Remark 17.6.4: composing the supported lift with the support inclusion recovers
the original morphism. -/
private theorem pushforwardLiftToSubsheaf_comp_arrow
    (hZ : IsClosed Z) {A : (TopCat.of Z).Sheaf Pointed} {B : X.Sheaf Pointed}
    (f : (Sheaf.pushforward Pointed iZ).obj A ⟶ B) :
    pushforwardLiftToSubsheaf hZ f ≫ (subsheaf hZ B).arrow = f := by
  -- Normalize the final `Subobject.underlyingIso` boundary back to `subsheafHom`; the remaining
  -- componentwise map is literally `f`.
  calc
    pushforwardLiftToSubsheaf hZ f ≫ (subsheaf hZ B).arrow
        = pushforwardLiftToBridge hZ f ≫ subsheafHom hZ B := by
            simp [pushforwardLiftToSubsheaf, subsheaf, Category.assoc]
    _ = f := by
          apply CategoryTheory.Sheaf.hom_ext
          ext U s
          rfl

/-- Helper for Remark 17.6.4: the supported lift is functorial in the source morphism. -/
private theorem pushforwardLiftToSubsheaf_naturality_left
    (hZ : IsClosed Z)
    {A₁ A₂ : (TopCat.of Z).Sheaf Pointed} {B : X.Sheaf Pointed}
    (u : A₁ ⟶ A₂) (f : (Sheaf.pushforward Pointed iZ).obj A₂ ⟶ B) :
    pushforwardLiftToSubsheaf hZ ((Sheaf.pushforward Pointed iZ).map u ≫ f) =
      (Sheaf.pushforward Pointed iZ).map u ≫ pushforwardLiftToSubsheaf hZ f := by
  -- The support inclusion is mono, so compare the composites back into the ambient target.
  apply (cancel_mono (subsheaf hZ B).arrow).1
  simp [Category.assoc, pushforwardLiftToSubsheaf_comp_arrow]

/-- Helper for Remark 17.6.4: the supported lift is functorial in the target morphism. -/
private theorem pushforwardLiftToSubsheaf_naturality_right
    (hZ : IsClosed Z)
    {A : (TopCat.of Z).Sheaf Pointed} {B C : X.Sheaf Pointed}
    (f : (Sheaf.pushforward Pointed iZ).obj A ⟶ B) (g : B ⟶ C) :
    pushforwardLiftToSubsheaf hZ (f ≫ g) =
      pushforwardLiftToSubsheaf hZ f ≫ subsheafMap hZ g := by
  -- Compose with the target support inclusion and use the established normal forms.
  apply (cancel_mono (subsheaf hZ C).arrow).1
  simp [Category.assoc, pushforwardLiftToSubsheaf_comp_arrow, subsheafMap_comp_arrow]

/-- Helper for Remark 17.6.4: factoring through the supported subobject is equivalent to giving a
raw morphism into the ambient sheaf. -/
private noncomputable def pushforwardFactorThroughSubsheafEquiv
    (hZ : IsClosed Z) (A : (TopCat.of Z).Sheaf Pointed) (B : X.Sheaf Pointed) :
    (((Sheaf.pushforward Pointed iZ).obj A) ⟶ B) ≃
      (((Sheaf.pushforward Pointed iZ).obj A) ⟶
        ((subsheaf hZ B : Subobject B) : X.Sheaf Pointed)) :=
  { toFun := pushforwardLiftToSubsheaf hZ
    invFun := fun g ↦ g ≫ (subsheaf hZ B).arrow
    left_inv := pushforwardLiftToSubsheaf_comp_arrow hZ
    right_inv := by
      intro g
      apply (cancel_mono (subsheaf hZ B).arrow).1
      simpa [Category.assoc] using
        pushforwardLiftToSubsheaf_comp_arrow hZ
          (f := g ≫ (subsheaf hZ B).arrow) }

/-- Helper for Remark 17.6.4: once the target is in the pushforward essential image, full
faithfulness of closed-subset pushforward converts maps into maps after pullback. -/
private noncomputable def pushforwardSubsheafPullbackEquiv
    (hZ : IsClosed Z) (A : (TopCat.of Z).Sheaf Pointed) (B : X.Sheaf Pointed) :
    ((((Sheaf.pushforward Pointed iZ).obj A) ⟶
        ((subsheaf hZ B : Subobject B) : X.Sheaf Pointed))) ≃
      (A ⟶ (𝓗[hZ]).obj B) :=
  -- This is the ambient pullback/pushforward Hom-equivalence on the supported subobject object.
  (TopCat.Sheaf.pullbackPushforwardAdjunction Pointed iZ).homEquiv A
    (((subsheaf hZ B : Subobject B) : X.Sheaf Pointed))

/-- Helper for Remark 17.6.4: maps out of a pushed-forward pointed sheaf are equivalent to maps
into the pointed sections-with-support object. -/
private noncomputable def pushforwardSectionsWithSupportHomEquiv
    (hZ : IsClosed Z) (A : (TopCat.of Z).Sheaf Pointed) (B : X.Sheaf Pointed) :
    (((Sheaf.pushforward Pointed iZ).obj A) ⟶ B) ≃
      (A ⟶ (𝓗[hZ]).obj B) :=
  -- First factor through the support subobject, then apply the ambient adjunction equivalence.
  (pushforwardFactorThroughSubsheafEquiv hZ A B).trans
    (pushforwardSubsheafPullbackEquiv hZ A B)

/-- Helper for Remark 17.6.4: the Hom-equivalence is natural in the left variable. -/
private theorem pushforwardSectionsWithSupportHomEquiv_naturality_left
    (hZ : IsClosed Z)
    {A₁ A₂ : (TopCat.of Z).Sheaf Pointed} {B : X.Sheaf Pointed}
    (u : A₁ ⟶ A₂) (f : (Sheaf.pushforward Pointed iZ).obj A₂ ⟶ B) :
    pushforwardSectionsWithSupportHomEquiv hZ A₁ B
        ((Sheaf.pushforward Pointed iZ).map u ≫ f) =
      u ≫ pushforwardSectionsWithSupportHomEquiv hZ A₂ B f := by
  -- Normalize the chosen support factorization, then use ambient adjunction naturality.
  simpa [pushforwardSectionsWithSupportHomEquiv,
    pushforwardFactorThroughSubsheafEquiv, pushforwardLiftToSubsheaf_naturality_left] using
    (CategoryTheory.Adjunction.homEquiv_naturality_left_symm
      (TopCat.Sheaf.pullbackPushforwardAdjunction Pointed iZ)
      u
      (pushforwardLiftToSubsheaf hZ f))

/-- Helper for Remark 17.6.4: the Hom-equivalence is natural in the right variable. -/
private theorem pushforwardSectionsWithSupportHomEquiv_naturality_right
    (hZ : IsClosed Z)
    {A : (TopCat.of Z).Sheaf Pointed} {B₁ B₂ : X.Sheaf Pointed}
    (f : (Sheaf.pushforward Pointed iZ).obj A ⟶ B₁) (g : B₁ ⟶ B₂) :
    pushforwardSectionsWithSupportHomEquiv hZ A B₂ (f ≫ g) =
      pushforwardSectionsWithSupportHomEquiv hZ A B₁ f ≫ (𝓗[hZ]).map g := by
  -- Right naturality is the ambient adjunction naturality after rewriting the support lift.
  simpa [pushforwardSectionsWithSupportHomEquiv,
    ClosedSubsetSectionsWithSupport.Pointed.functor,
    pushforwardFactorThroughSubsheafEquiv, pushforwardLiftToSubsheaf_naturality_right] using
    (CategoryTheory.Adjunction.homEquiv_naturality_right
      (TopCat.Sheaf.pullbackPushforwardAdjunction Pointed iZ)
      (pushforwardLiftToSubsheaf hZ f)
      (subsheafMap hZ g))

/-- Remark 17.6.4: for a closed subset inclusion `i : Z ↪ X`, pushforward of pointed sheaves is
left adjoint to the explicit pointed sections-with-support functor `𝓗[hZ] = \mathcal H_Z`. -/
@[stacks 01B0]
noncomputable def pushforwardSectionsWithSupportAdjunction
    (hZ : IsClosed Z) :
    Sheaf.pushforward Pointed iZ ⊣ 𝓗[hZ] :=
  -- Route correction: package the adjunction by the repaired Hom-bijection.
  Adjunction.mkOfHomEquiv
    { homEquiv := pushforwardSectionsWithSupportHomEquiv hZ
      homEquiv_naturality_left_symm :=
        pushforwardSectionsWithSupportHomEquiv_naturality_left hZ
      homEquiv_naturality_right :=
        pushforwardSectionsWithSupportHomEquiv_naturality_right hZ }

section

variable (hZ : IsClosed Z)

/- Pushforward of pointed sheaves along a closed subset inclusion is a left adjoint. This is the
canonical owner theorem `Adjunction.isLeftAdjoint` for the adjunction above. -/
#check ((pushforwardSectionsWithSupportAdjunction hZ).isLeftAdjoint :
  (Sheaf.pushforward Pointed iZ).IsLeftAdjoint)

/- The pointed closed-support functor `𝓗[hZ]` is a right adjoint. This is the canonical owner
form `Functor.IsRightAdjoint (𝓗[hZ])` coming from the specialized adjunction above. -/
#check ((pushforwardSectionsWithSupportAdjunction hZ).isRightAdjoint :
  Functor.IsRightAdjoint (𝓗[hZ]))

-- Proof sketch: in the pointed setting, closed-subset pushforward is exact because Remark 17.6.4
-- makes it both a right adjoint and a left adjoint.
/-- Remark 17.6.4 (1): for a closed subset `Z ⊆ X`, the pushforward functor
`i_* : Sh(Z, Pointed) ⥤ Sh(X, Pointed)` is exact. -/
@[stacks 01B0]
theorem pushforward_exact
    (hZ : IsClosed Z) :
    exactFunctor ((TopCat.of Z).Sheaf Pointed) (X.Sheaf Pointed)
      (Sheaf.pushforward Pointed iZ) := by
  let F := Sheaf.pushforward Pointed iZ
  -- Pushforward is the right adjoint in the canonical pullback/pushforward adjunction.
  let _ : F.IsRightAdjoint := (Sheaf.pullbackPushforwardAdjunction Pointed iZ).isRightAdjoint
  let _ : PreservesFiniteLimits F := inferInstance
  -- Remark 17.6.4 provides the left adjoint structure, hence colimit preservation.
  let _ : F.IsLeftAdjoint := (pushforwardSectionsWithSupportAdjunction hZ).isLeftAdjoint
  let _ : PreservesColimits F := (pushforwardSectionsWithSupportAdjunction hZ).leftAdjoint_preservesColimits
  let _ : PreservesFiniteColimits F := inferInstance
  exact (exactFunctor_iff F).2 ⟨inferInstance, inferInstance⟩

end

end ClosedSubsetSectionsWithSupport.Pointed

end
