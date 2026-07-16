import Mathlib
import StacksProject_2024.stacks_project.Chap06.Lemma_6_21_5
import StacksProject_2024.stacks_project.Chap06.Lemma_6_21_6
import StacksProject_2024.stacks_project.Chap06.Definition_6_30_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace ConcreteCategory
open TopCat.Sheaf
open scoped TopCat

universe u

attribute [local instance] Types.instFunLike Types.instConcreteCategory

section

variable {I : Type u} [Category I]
variable (F : I ⥤ TopCat.{u})

/- Domain-style sampling for Lemma 6.29.3:
- primary domain: pullback of sheaves of types along continuous maps in an inverse system of
  spectral spaces, with the source-facing comparison map expressed on compact opens;
- sampled owner declarations:
  `TopCat.Sheaf.pullback`,
  `TopCat.Sheaf.pullbackPushforwardAdjunction`,
  `TopCat.Sheaf.pullbackComp`,
  `PrespectralSpace.isBasis_opens`,
  `CategoryTheory.colimitSiteStagePullbackSectionsComparison`;
- owner abstraction: the comparison on stagewise pullback sections is canonically owned by the
  site-level declaration `CategoryTheory.colimitSiteStagePullbackSectionsComparison`, applied to
  the compact-open basis sites of the spectral stages; the topological map in this file is the
  source-facing specialization of that owner;
- primitive data: a cofiltered diagram `F`, a stage `i`, a sheaf `𝒢` on `F.obj i`, and a
  quasi-compact open `U ⊆ F.obj i`;
- derived API: the explicit `(Over i)ᵒᵖ` diagram of pullback section sets and the colimit
  comparison map. These are bridge-level presentations and should not remain the main public
  owner once the site-level comparison is available.

Source/core/bridge triage:
- `source-facing`: the comparison
  `colim_a f_a⁻¹ 𝒢 (f_a⁻¹(U)) ⟶ p_i⁻¹ 𝒢 (p_i⁻¹(U))`;
- `core/canonical`: the Chapter 7 site-level comparison owner on the compact-open basis site of
  the spectral stages, together with the basis restriction equivalence for sheaves;
- `bridge/view`: the explicit `(Over i)ᵒᵖ` diagram of stagewise pullback section types below, kept
  private because it is only an implementation view of the source-facing comparison. -/

private abbrev compactOpenBasis (X : TopCat.{u}) : Set (Opens X) :=
  { U : Opens X | IsCompact (U : Set X) }

private theorem compactOpenBasis_isBasis (X : TopCat.{u}) [SpectralSpace X] :
    Opens.IsBasis (compactOpenBasis X) :=
  PrespectralSpace.isBasis_opens X

/-- The iterated-pullback section space computed through `f` and then `g` is the section space of
the pullback along `f ≫ g`. -/
private theorem inverseImageSectionValue_comp {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (𝒢 : Z.Sheaf (Type u)) (U : Opens Z) :
    ((((f ≫ g)⁻¹).obj 𝒢).presheaf).obj
      (op ((Opens.map f).obj ((Opens.map g).obj U))) =
    ((((f ≫ g)⁻¹).obj 𝒢).presheaf).obj
      (op ((Opens.map (f ≫ g)).obj U)) := by
  rfl

/-- The canonical map on sections induced by pulling back first along `g` and then along `f`. -/
private noncomputable def iteratedPullbackSectionsMap {X Y Z : TopCat.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (𝒢 : Z.Sheaf (Type u)) (U : Opens Z) :
    ((((g⁻¹).obj 𝒢).presheaf).obj (op ((Opens.map g).obj U))) ⟶
      ((((f ≫ g)⁻¹).obj 𝒢).presheaf).obj (op ((Opens.map (f ≫ g)).obj U)) :=
  let η := (((pullbackPushforwardAdjunction (Type u) f).unit.app ((g⁻¹).obj 𝒢)).1.app
    (op ((Opens.map g).obj U)))
  let e := (pullbackComp f g).hom.app 𝒢
  fun s ↦ cast (inverseImageSectionValue_comp f g 𝒢 U)
    ((e.1.app (op ((Opens.map f).obj ((Opens.map g).obj U)))) (η s))

/-- A morphism in `Over i` identifies the corresponding iterated pullback section space with the
direct pullback section space. -/
private theorem overPullbackSections_eq {i : I} (𝒢 : (F.obj i).Sheaf (Type u))
    (U : Opens (F.obj i)) {A B : Over i} (φ : A ⟶ B) :
    ((((F.map φ.left ≫ F.map B.hom)⁻¹).obj 𝒢).presheaf).obj
      (op ((Opens.map (F.map φ.left ≫ F.map B.hom)).obj U)) =
    ((((F.map A.hom)⁻¹).obj 𝒢).presheaf).obj
      (op ((Opens.map (F.map A.hom)).obj U)) := by
  simpa [Functor.map_comp] using
    congrArg
      (fun f : A.left ⟶ i ↦
        ((((F.map f)⁻¹).obj 𝒢).presheaf).obj (op ((Opens.map (F.map f)).obj U)))
      (Over.w φ)

/-- The transition map on pulled-back sections along a morphism in `Over i`. -/
private noncomputable def overPullbackSectionsMap {i : I} (𝒢 : (F.obj i).Sheaf (Type u))
    (U : Opens (F.obj i)) {A B : Over i}
    (φ : A ⟶ B) :
    ((((F.map B.hom)⁻¹).obj 𝒢).presheaf).obj
        (op ((Opens.map (F.map B.hom)).obj U)) ⟶
      ((((F.map A.hom)⁻¹).obj 𝒢).presheaf).obj
        (op ((Opens.map (F.map A.hom)).obj U)) :=
  fun s ↦ cast (overPullbackSections_eq F 𝒢 U φ)
    (iteratedPullbackSectionsMap (F.map φ.left) (F.map B.hom) 𝒢 U s)

-- Proof sketch: for an identity morphism the adjunction unit and the pullback-composition
-- isomorphism are both identities on sections.
/-- Identity compatibility for the stagewise pullback section transition maps. -/
private theorem overPullbackSectionsMap_id {i : I} (𝒢 : (F.obj i).Sheaf (Type u))
    (U : Opens (F.obj i)) (A : Over i) :
    overPullbackSectionsMap F 𝒢 U (𝟙 A) = id := sorry

-- Proof sketch: functoriality follows from naturality of the adjunction unit and coherence of the
-- pullback-composition isomorphism.
/-- Composition compatibility for the stagewise pullback section transition maps. -/
private theorem overPullbackSectionsMap_comp {i : I} (𝒢 : (F.obj i).Sheaf (Type u))
    (U : Opens (F.obj i))
    {A B C : Over i} (φ : A ⟶ B) (ψ : B ⟶ C) :
    overPullbackSectionsMap F 𝒢 U (φ ≫ ψ) =
      overPullbackSectionsMap F 𝒢 U φ ∘ overPullbackSectionsMap F 𝒢 U ψ := sorry

/-- The over-category diagram
`(a : j ⟶ i) ↦ f_a⁻¹ 𝒢 (f_a⁻¹(U))`
of stagewise pullback sections. -/
private noncomputable def limitPullbackSectionsDiagram (i : I) (𝒢 : (F.obj i).Sheaf (Type u))
    (U : Opens (F.obj i)) :
    (Over i)ᵒᵖ ⥤ Type u where
  obj A := (((((F.map A.unop.hom)⁻¹).obj 𝒢).presheaf).obj
    (op ((Opens.map (F.map A.unop.hom)).obj U)))
  map φ := overPullbackSectionsMap F 𝒢 U φ.unop
  map_id := by
    intro A
    simpa using overPullbackSectionsMap_id F 𝒢 U A.unop
  map_comp := by
    intro A B C φ ψ
    simpa using overPullbackSectionsMap_comp F 𝒢 U ψ.unop φ.unop

/-- The iterated pullback to the limit through an object of `Over i` is the direct pullback along
the projection `p_i`. -/
private theorem limitPullbackSections_eq {i : I} (𝒢 : (F.obj i).Sheaf (Type u))
    (U : Opens (F.obj i)) (A : Over i) :
    ((((limit.π F A.left ≫ F.map A.hom)⁻¹).obj 𝒢).presheaf).obj
      (op ((Opens.map (limit.π F A.left ≫ F.map A.hom)).obj U)) =
    ((((limit.π F i)⁻¹).obj 𝒢).presheaf).obj
      (op ((Opens.map (limit.π F i)).obj U)) := by
  exact congrArg
    (fun f : limit F ⟶ F.obj i ↦
      (((f⁻¹).obj 𝒢).presheaf).obj (op ((Opens.map f).obj U)))
    (limit.w F A.hom)

/-- The map from a stagewise pullback section to the pullback section on the limit space. -/
private noncomputable def pullbackSectionsToLimitMap {i : I}
    (𝒢 : (F.obj i).Sheaf (Type u)) (U : Opens (F.obj i)) (A : Over i) :
    ((((F.map A.hom)⁻¹).obj 𝒢).presheaf).obj
        (op ((Opens.map (F.map A.hom)).obj U)) ⟶
      ((((limit.π F i)⁻¹).obj 𝒢).presheaf).obj
        (op ((Opens.map (limit.π F i)).obj U)) :=
  fun s ↦ cast (limitPullbackSections_eq F 𝒢 U A)
    (iteratedPullbackSectionsMap (limit.π F A.left) (F.map A.hom) 𝒢 U s)

-- Proof sketch: the comparison to the limit is compatible with stage transition maps by the same
-- adjunction-unit naturality and pullback-composition coherence used above.
/-- Stagewise comparison maps to the limit are compatible with the over-category transitions. -/
private theorem pullbackSectionsToLimitMap_naturality {i : I}
    (𝒢 : (F.obj i).Sheaf (Type u)) (U : Opens (F.obj i))
    {A B : Over i} (φ : A ⟶ B) :
    overPullbackSectionsMap F 𝒢 U φ ≫ pullbackSectionsToLimitMap F 𝒢 U A =
      (pullbackSectionsToLimitMap F 𝒢 U B :
        ((((F.map B.hom)⁻¹).obj 𝒢).presheaf).obj
            (op ((Opens.map (F.map B.hom)).obj U)) ⟶
          ((((limit.π F i)⁻¹).obj 𝒢).presheaf).obj
            (op ((Opens.map (limit.π F i)).obj U))) := sorry

/-- The cocone from stagewise pullback sections to pullback sections on the limit space. -/
private noncomputable def limitPullbackSectionsCocone (i : I)
    (𝒢 : (F.obj i).Sheaf (Type u)) (U : Opens (F.obj i)) :
    Cocone (limitPullbackSectionsDiagram F i 𝒢 U) where
  pt := ((((limit.π F i)⁻¹).obj 𝒢).presheaf).obj
    (op ((Opens.map (limit.π F i)).obj U))
  ι :=
    { app := fun A ↦ pullbackSectionsToLimitMap F 𝒢 U A.unop
      naturality := fun {_ _} f ↦
        by simpa using pullbackSectionsToLimitMap_naturality F 𝒢 U f.unop }

/-- The canonical map from the colimit of stagewise pullback sections to the pullback sections on
the limit space. -/
noncomputable def limitPullbackSectionsColimitMap (i : I)
    (𝒢 : (F.obj i).Sheaf (Type u)) (U : Opens (F.obj i)) :
    colimit (limitPullbackSectionsDiagram F i 𝒢 U) ⟶
      ((((limit.π F i)⁻¹).obj 𝒢).presheaf).obj
        (op ((Opens.map (limit.π F i)).obj U)) :=
  colimit.desc (limitPullbackSectionsDiagram F i 𝒢 U) (limitPullbackSectionsCocone F i 𝒢 U)

-- Proof sketch: restrict `𝒢` to the compact-open basis on each spectral stage, package the
-- resulting basis sites and spectral preimage functors into the Chapter 7 owner
-- `CofilteredSiteDiagram`, identify the source-facing topological comparison map above with the
-- site-level owner `CategoryTheory.colimitSiteStagePullbackSectionsComparison`, and then apply
-- `CategoryTheory.colimitSiteStagePullbackSectionsComparison_bijective`.
private theorem limitPullbackSectionsColimitMap_isIso_viaSiteComparison
    [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a)) (i : I)
    (𝒢 : (F.obj i).Sheaf (Type u)) (U : Opens (F.obj i)) (hU : IsCompact (U : Set (F.obj i))) :
    IsIso (limitPullbackSectionsColimitMap F i 𝒢 U) := by
  let B : ∀ j : I, Set (Opens (F.obj j)) := fun j ↦ compactOpenBasis (F.obj j)
  let UB : BasisOpen (B i) := ⟨U, hU⟩
  let _ := hF
  let _ := UB
  sorry

-- Proof sketch: identify `limitPullbackSectionsColimitMap` with the canonical map in the Stacks
-- proof by transporting it to the Chapter 7 site-level owner on compact-open basis sites, then
-- use `CategoryTheory.colimitSiteStagePullbackSectionsComparison_bijective` for that owner.
/-- Lemma 6.29.3: for a cofiltered diagram of spectral spaces with spectral transition maps, the
canonical comparison map from the colimit of the stagewise pullback sections
`f_a⁻¹ 𝒢 (f_a⁻¹(U))` to the pullback sections `p_i⁻¹ 𝒢 (p_i⁻¹(U))` on the limit space is an
isomorphism for every quasi-compact open `U ⊆ X_i`. -/
theorem limitPullbackSectionsColimitMap_isIso [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a)) (i : I)
    (𝒢 : (F.obj i).Sheaf (Type u)) (U : Opens (F.obj i)) (hU : IsCompact (U : Set (F.obj i))) :
    IsIso (limitPullbackSectionsColimitMap F i 𝒢 U) :=
  limitPullbackSectionsColimitMap_isIso_viaSiteComparison F hF i 𝒢 U hU

end
