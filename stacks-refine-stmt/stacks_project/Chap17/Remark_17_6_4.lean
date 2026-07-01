import Mathlib
import stacks_project.Chap06.Lemma_6_15_2
import stacks_project.Chap06.Lemma_6_32_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Opposite
open TopCat TopologicalSpace

noncomputable section

universe u

section

variable {X : TopCat.{u}} {Z : Set X}

local notation "iZ" => X.closedSubsetInclusion Z

/- Domain-style sampling for Remark 17.6.4:
- primary domain: pointed sheaves on a closed subset, the closed-subset pushforward functor, and
  the pointed sheaf of sections with support in `Z`;
- sampled owner declarations:
  `TopCat.closedSubsetInclusion`,
  `Sheaf.pushforward`,
  `Sheaf.pullback`,
  `closedSubsetSectionsWithSupportFunctor`,
  `Sheaf.pullbackPushforwardAdjunction`,
  `subsetSheaf_pullback_pushforward_counit_isIso`;
- best owner abstraction:
  the source-facing owner is the pointed closed-support functor
  `ClosedSubsetSectionsWithSupport.Pointed.functor hZ`, written `𝓗[hZ]`, whose object part is the
  pointed sheaf on `Z` obtained by restricting the pointed sheaf on `X` of sections that become
  the distinguished point on `X \ Z`;
- primitive data:
  the closed subset `Z`, its open complement, the explicit support-condition subsheaf on `X`, and
  the canonical distinguished point section on that sheaf;
- derived API:
  the functor `𝓗[hZ]`, its objectwise pointed sheaf `((𝓗[hZ]).obj ℱ)`, and the
  left-adjoint/right-adjoint/exactness consequences for closed-subset pushforward.

Source/core/bridge triage:
- `source-facing`: the pointed closed-support functor `𝓗[hZ]` and its object part
  `((𝓗[hZ]).obj ℱ)`;
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

/-- The `Type`-valued presheaf of local sections whose restriction to the open complement of `Z`
is the distinguished point section. -/
private def closedSubsetPointedSectionsWithSupportTypePresheaf
    (hZ : IsClosed Z) (ℱ : X.Sheaf Pointed) : X.Presheaf (Type u) where
  obj U := { s : ℱ.presheaf.obj U // ClosedSubsetSectionsWithSupport.Pointed.appPred hZ ℱ U.unop s }
  map {U V} i s := ⟨ℱ.presheaf.map i s.1, by sorry⟩
  map_id := by sorry
  map_comp := by sorry

private theorem closedSubsetPointedSectionsWithSupportTypePresheaf_isSheaf
    (hZ : IsClosed Z) (ℱ : X.Sheaf Pointed) :
    (closedSubsetPointedSectionsWithSupportTypePresheaf hZ ℱ).IsSheaf := by
  sorry

/-- The `Type`-valued sheaf on `X` consisting of sections whose restriction to the open complement
of `Z` is the distinguished point section. -/
private def closedSubsetPointedSectionsWithSupportTypeSheafOnX
    (hZ : IsClosed Z) (ℱ : X.Sheaf Pointed) : X.Sheaf (Type u) :=
  ⟨closedSubsetPointedSectionsWithSupportTypePresheaf hZ ℱ,
    closedSubsetPointedSectionsWithSupportTypePresheaf_isSheaf hZ ℱ⟩

/-- The distinguished point section defines a canonical morphism from the singleton sheaf to the
`Type`-valued sections-with-support sheaf on `X`. -/
private def closedSubsetPointedSectionsWithSupportTypeSheafOnX_point
    (hZ : IsClosed Z) (ℱ : X.Sheaf Pointed) :
    TopCat.sheafToType X (ULift Unit) ⟶
      closedSubsetPointedSectionsWithSupportTypeSheafOnX hZ ℱ :=
  ObjectProperty.homMk
    { app := fun U _ ↦
        ⟨(ℱ.presheaf.obj U).point, by
          show ClosedSubsetSectionsWithSupport.Pointed.appPred hZ ℱ U.unop (ℱ.presheaf.obj U).point
          unfold ClosedSubsetSectionsWithSupport.Pointed.appPred
          simpa using
            (ℱ.presheaf.map (Opens.infLELeft U.unop (closedSubsetOpenComplement hZ)).op).map_point⟩
      naturality := by
        intro U V i
        sorry }

/-- The `Type`-valued map on sections-with-support sheaves induced by a morphism of pointed
sheaves. -/
private def closedSubsetPointedSectionsWithSupportTypeSheafOnX_map
    (hZ : IsClosed Z) {ℱ 𝒢 : X.Sheaf Pointed} (φ : ℱ ⟶ 𝒢) :
    closedSubsetPointedSectionsWithSupportTypeSheafOnX hZ ℱ ⟶
      closedSubsetPointedSectionsWithSupportTypeSheafOnX hZ 𝒢 :=
  ObjectProperty.homMk
    { app := fun U s ↦ ⟨φ.1.app U s.1, by sorry⟩
      naturality := by
        intro U V i
        sorry }

/-- A sheaf of types with a distinguished singleton-valued section family canonically determines a
sheaf of pointed sets. -/
private def pointifySheaf {Y : TopCat.{u}} (F : Y.Sheaf (Type u))
    (η : TopCat.sheafToType Y (ULift Unit) ⟶ F) : Y.Sheaf Pointed := by
  refine ⟨?_, ?_⟩
  · let P : Y.Presheaf (Type u) := F.1
    refine
      { obj := fun U ↦ Pointed.of (η.1.app U (fun _ ↦ ⟨()⟩))
        map := fun {U V} i ↦ ⟨fun s ↦ P.map i s, by
          change P.map i (η.1.app U (fun _ ↦ ⟨()⟩)) = η.1.app V (fun _ ↦ ⟨()⟩)
          simpa using (congr_fun (η.1.naturality i) (fun _ ↦ ⟨()⟩)).symm⟩
        map_id := by sorry
        map_comp := by sorry }
  · sorry

/-- A morphism of type-valued sheaves respecting distinguished singleton-valued sections induces a
morphism of the associated sheaves of pointed sets. -/
private def pointifySheafMap {Y : TopCat.{u}} {F G : Y.Sheaf (Type u)}
    {ηF : TopCat.sheafToType Y (ULift Unit) ⟶ F}
    {ηG : TopCat.sheafToType Y (ULift Unit) ⟶ G}
    (φ : F ⟶ G) (hφ : ηF ≫ φ = ηG) :
    pointifySheaf F ηF ⟶ pointifySheaf G ηG :=
  ObjectProperty.homMk
    { app := fun U ↦
        ⟨φ.1.app U, by sorry⟩
      naturality := by
        sorry }

private theorem closedSubsetPointedSectionsWithSupportTypeSheafOnX_point_naturality
    (hZ : IsClosed Z) {ℱ 𝒢 : X.Sheaf Pointed} (φ : ℱ ⟶ 𝒢) :
    closedSubsetPointedSectionsWithSupportTypeSheafOnX_point hZ ℱ ≫
        closedSubsetPointedSectionsWithSupportTypeSheafOnX_map hZ φ =
      closedSubsetPointedSectionsWithSupportTypeSheafOnX_point hZ 𝒢 := by
  sorry

/-- The pointed sheaf on `X` whose sections restrict to the distinguished point section on the
open complement `X \ Z`. -/
def ClosedSubsetSectionsWithSupport.Pointed.sheafOnX
    (hZ : IsClosed Z) (ℱ : X.Sheaf Pointed) : X.Sheaf Pointed :=
  pointifySheaf
    (closedSubsetPointedSectionsWithSupportTypeSheafOnX hZ ℱ)
    (closedSubsetPointedSectionsWithSupportTypeSheafOnX_point hZ ℱ)

/-- The pointed map on sections-with-support sheaves induced by a morphism of pointed sheaves. -/
private def sheafOnXMap
    (hZ : IsClosed Z) {ℱ 𝒢 : X.Sheaf Pointed} (φ : ℱ ⟶ 𝒢) :
    ClosedSubsetSectionsWithSupport.Pointed.sheafOnX hZ ℱ ⟶
      ClosedSubsetSectionsWithSupport.Pointed.sheafOnX hZ 𝒢 :=
  pointifySheafMap
    (closedSubsetPointedSectionsWithSupportTypeSheafOnX_map hZ φ)
    (closedSubsetPointedSectionsWithSupportTypeSheafOnX_point_naturality hZ φ)

namespace ClosedSubsetSectionsWithSupport.Pointed

-- Proof sketch: sections with support in `Z` first form a pointed sheaf on `X`, namely the
-- pointed subsheaf whose sections restrict to the distinguished point on `X \ Z`; restricting
-- that pointed sheaf to `Z` yields the source-facing pointed closed-support functor
-- `\mathcal H_Z = 𝓗[hZ]`.
/-- The pointed sheaf on the closed subset `Z` obtained by restricting the pointed sheaf
`sheafOnX hZ ℱ` of sections that become the distinguished point on `X \ Z`. -/
def sheaf
    (hZ : IsClosed Z) (ℱ : X.Sheaf Pointed) :
    (TopCat.of Z).Sheaf Pointed :=
  (Sheaf.pullback Pointed iZ).obj (sheafOnX hZ ℱ)

/-- Remark 17.6.4: the pointed closed-support functor along a closed subset inclusion, written
`𝓗[hZ] = \mathcal H_Z`, sends a pointed sheaf `\mathcal F` on `X` to the pointed sheaf on `Z`
obtained by restricting the pointed sheaf on `X` of local sections whose restriction to
`X \ Z` is the distinguished point section. -/
def functor
    (hZ : IsClosed Z) :
    X.Sheaf Pointed ⥤ (TopCat.of Z).Sheaf Pointed where
  obj ℱ := sheaf hZ ℱ
  map φ := (Sheaf.pullback Pointed iZ).map (sheafOnXMap hZ φ)
  map_id := by
    sorry
  map_comp := by
    sorry

end ClosedSubsetSectionsWithSupport.Pointed

namespace ClosedSubsetSectionsWithSupport.Pointed

scoped notation "𝓗[" hZ "]" => functor hZ

end ClosedSubsetSectionsWithSupport.Pointed

open scoped ClosedSubsetSectionsWithSupport.Pointed

namespace ClosedSubsetSectionsWithSupport.Pointed

/-- The canonical morphism from the pointed sheaf of sections supported on `Z` back to `ℱ`. -/
def sheafOnXHom
    (hZ : IsClosed Z) (ℱ : X.Sheaf Pointed) :
    sheafOnX hZ ℱ ⟶ ℱ := by
  refine ObjectProperty.homMk ?_
  refine
    { app := fun U ↦ ?_
      naturality := ?_ }
  · refine ⟨fun s ↦ s.1, ?_⟩
    rfl
  · intro U V i
    ext s
    rfl

variable (hZ : IsClosed Z)

/-- For an open set `U ⊆ X`, the image of the canonical map
`sheafOnX hZ ℱ(U) → ℱ(U)` is exactly the set of sections whose restriction to
`U ∩ (X \ Z)` is the distinguished point. -/
theorem sheafOnX_app_range
    (ℱ : X.Sheaf Pointed) (U : Opens X) :
    Set.range ((sheafOnXHom hZ ℱ).1.app (op U)) =
      { s | appPred hZ ℱ U s } := by
  ext s
  constructor
  · rintro ⟨t, rfl⟩
    exact t.2
  · intro hs
    exact ⟨⟨s, hs⟩, rfl⟩

/-- A section of `ℱ(U)` lies in the image of `sheafOnX hZ ℱ(U) → ℱ(U)` exactly when its
restriction to `U ∩ (X \ Z)` is the distinguished point. -/
theorem sheafOnX_app_iff
    (ℱ : X.Sheaf Pointed) (U : Opens X) (s : ℱ.presheaf.obj (op U)) :
    s ∈ Set.range ((sheafOnXHom hZ ℱ).1.app (op U)) ↔
      appPred hZ ℱ U s := by
  simpa using congrArg (fun S : Set (ℱ.presheaf.obj (op U)) ↦ s ∈ S) (sheafOnX_app_range hZ ℱ U)

variable {hZ}

private theorem closedSubsetPointedSectionsWithSupportSheafOnX_pushforwardHom_isIso
    (hZ : IsClosed Z) (ℱ : (TopCat.of Z).Sheaf Pointed) :
    IsIso
      (sheafOnXHom hZ
        ((Sheaf.pushforward Pointed iZ).obj ℱ)) := by
  sorry

private theorem closedSubsetPointedSectionsWithSupportSheafOnX_pullback_pushforward_unit_isIso
    (hZ : IsClosed Z) (ℱ : X.Sheaf Pointed) :
    IsIso
      ((Sheaf.pullbackPushforwardAdjunction Pointed iZ).unit.app
        (sheafOnX hZ ℱ)) := by
  sorry

private noncomputable abbrev pushforwardSectionsWithSupportAdjunctionUnitApp
    (hZ : IsClosed Z) (ℱ : (TopCat.of Z).Sheaf Pointed) :
    ℱ ⟶
      (𝓗[hZ]).obj ((Sheaf.pushforward Pointed iZ).obj ℱ) :=
  letI := subsetSheaf_pullback_pushforward_counit_isIso ℱ
  letI := closedSubsetPointedSectionsWithSupportSheafOnX_pushforwardHom_isIso hZ ℱ
  let e := asIso
    (sheafOnXHom hZ
      ((Sheaf.pushforward Pointed iZ).obj ℱ))
  (asIso ((Sheaf.pullbackPushforwardAdjunction Pointed iZ).counit.app ℱ)).inv ≫
    (Sheaf.pullback Pointed iZ).map e.inv

private noncomputable abbrev pushforwardSectionsWithSupportAdjunctionCounitApp
    (hZ : IsClosed Z) (ℱ : X.Sheaf Pointed) :
    (Sheaf.pushforward Pointed iZ).obj ((𝓗[hZ]).obj ℱ) ⟶ ℱ :=
  letI := closedSubsetPointedSectionsWithSupportSheafOnX_pullback_pushforward_unit_isIso hZ ℱ
  (asIso
      ((Sheaf.pullbackPushforwardAdjunction Pointed iZ).unit.app
        (sheafOnX hZ ℱ))).inv ≫
    sheafOnXHom hZ ℱ

/-- Remark 17.6.4: for a closed subset inclusion `i : Z ↪ X`, pushforward of pointed sheaves is
left adjoint to the explicit pointed sections-with-support functor `𝓗[hZ] = \mathcal H_Z`. -/
noncomputable def pushforwardSectionsWithSupportAdjunction
    (hZ : IsClosed Z) :
    Sheaf.pushforward Pointed iZ ⊣ 𝓗[hZ] where
  unit :=
    { app := pushforwardSectionsWithSupportAdjunctionUnitApp hZ
      naturality := by
        sorry }
  counit :=
    { app := pushforwardSectionsWithSupportAdjunctionCounitApp hZ
      naturality := by
        sorry }
  left_triangle_components := by
    sorry
  right_triangle_components := by
    sorry

section

variable (hZ : IsClosed Z)

/- Pushforward of pointed sheaves along a closed subset inclusion is a left adjoint. This is the
canonical owner theorem `Adjunction.isLeftAdjoint` for the adjunction above. -/
#check ((pushforwardSectionsWithSupportAdjunction hZ).isLeftAdjoint :
  (Sheaf.pushforward Pointed iZ).IsLeftAdjoint)

local instance : Functor.IsRightAdjoint (𝓗[hZ]) :=
  (pushforwardSectionsWithSupportAdjunction hZ).isRightAdjoint

/- The pointed closed-support functor `𝓗[hZ]` is a right adjoint. This is the canonical owner
form `Functor.IsRightAdjoint (𝓗[hZ])` coming from the specialized adjunction above. -/
#check (show Functor.IsRightAdjoint (𝓗[hZ]) from inferInstance)

-- Proof sketch: in the pointed setting, closed-subset pushforward is exact because Remark 17.6.4
-- makes it both a right adjoint and a left adjoint.
/-- Remark 17.6.4 (1): for a closed subset `Z ⊆ X`, the pushforward functor
`i_* : Sh(Z, Pointed) ⥤ Sh(X, Pointed)` is exact. -/
theorem pushforward_exact
    (hZ : IsClosed Z) :
    exactFunctor ((TopCat.of Z).Sheaf Pointed) (X.Sheaf Pointed)
      (Sheaf.pushforward Pointed iZ) := by
  sorry

end

end ClosedSubsetSectionsWithSupport.Pointed

end
