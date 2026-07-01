import Mathlib
import stacks_project.Chap06.Lemma_6_21_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopCat TopologicalSpace
open TopologicalSpace.Opens

attribute [local instance] CategoryTheory.Types.instFunLike CategoryTheory.Types.instConcreteCategory

noncomputable section

universe u w

section

variable {X : TopCat.{u}}

/-- The topological space underlying the open subspace `U ⊆ X`. -/
abbrev openSubsetSpace (U : Opens X) : TopCat.{u} :=
  (Opens.toTopCat X).obj U

/-- The inclusion of the open subspace `U` into the ambient space `X`. -/
abbrev openSubsetInclusion (U : Opens X) : openSubsetSpace U ⟶ X :=
  Opens.inclusion' U

/-- The inclusion of `U ∩ V` into `U`. -/
abbrev openSubsetIntersectionLeftInclusion (U V : Opens X) :
    openSubsetSpace (U ⊓ V) ⟶ openSubsetSpace U :=
  (Opens.toTopCat X).map (homOfLE inf_le_left)

/-- The inclusion of `U ∩ V` into `V`. -/
abbrev openSubsetIntersectionRightInclusion (U V : Opens X) :
    openSubsetSpace (U ⊓ V) ⟶ openSubsetSpace V :=
  (Opens.toTopCat X).map (homOfLE inf_le_right)

/-- The inclusion of `U ∩ V ∩ W` into `U`. -/
abbrev openSubsetTripleFirstInclusion (U V W : Opens X) :
    openSubsetSpace (U ⊓ V ⊓ W) ⟶ openSubsetSpace U :=
  (Opens.toTopCat X).map (homOfLE <|
    (show U ⊓ V ⊓ W ≤ U ⊓ V from inf_le_left).trans
      (show U ⊓ V ≤ U from inf_le_left))

/-- The inclusion of `U ∩ V ∩ W` into `V`. -/
abbrev openSubsetTripleSecondInclusion (U V W : Opens X) :
    openSubsetSpace (U ⊓ V ⊓ W) ⟶ openSubsetSpace V :=
  (Opens.toTopCat X).map (homOfLE <|
    (show U ⊓ V ⊓ W ≤ U ⊓ V from inf_le_left).trans
      (show U ⊓ V ≤ V from inf_le_right))

/-- The inclusion of `U ∩ V ∩ W` into `W`. -/
abbrev openSubsetTripleThirdInclusion (U V W : Opens X) :
    openSubsetSpace (U ⊓ V ⊓ W) ⟶ openSubsetSpace W :=
  (Opens.toTopCat X).map (homOfLE inf_le_right)

/-- The inclusion of `U ∩ V ∩ W` into `U ∩ V`. -/
abbrev openSubsetTripleToPairLeftInclusion (U V W : Opens X) :
    openSubsetSpace (U ⊓ V ⊓ W) ⟶ openSubsetSpace (U ⊓ V) :=
  (Opens.toTopCat X).map (homOfLE inf_le_left)

/-- The inclusion of `U ∩ V ∩ W` into `V ∩ W`. -/
abbrev openSubsetTripleToPairCenterInclusion (U V W : Opens X) :
    openSubsetSpace (U ⊓ V ⊓ W) ⟶ openSubsetSpace (V ⊓ W) :=
  (Opens.toTopCat X).map (homOfLE (inf_le_inf inf_le_right le_rfl))

/-- The inclusion of `U ∩ V ∩ W` into `U ∩ W`. -/
abbrev openSubsetTripleToPairOuterInclusion (U V W : Opens X) :
    openSubsetSpace (U ⊓ V ⊓ W) ⟶ openSubsetSpace (U ⊓ W) :=
  (Opens.toTopCat X).map (homOfLE
    (inf_le_inf (show U ⊓ V ≤ U from inf_le_left) le_rfl))

private abbrev tripleOverlapHom12
    {ι : Type w} (U : ι → Opens X)
    (family : ∀ i : ι, TopCat.Sheaf (Type u) (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      ((TopCat.Sheaf.pullback (Type u)
        (openSubsetIntersectionLeftInclusion (U i) (U j))).obj (family i)) ≅
      ((TopCat.Sheaf.pullback (Type u)
        (openSubsetIntersectionRightInclusion (U i) (U j))).obj (family j)))
    (i j k : ι) :
    ((TopCat.Sheaf.pullback (Type u)
      (openSubsetTripleFirstInclusion (U i) (U j) (U k))).obj (family i)) ⟶
    ((TopCat.Sheaf.pullback (Type u)
      (openSubsetTripleSecondInclusion (U i) (U j) (U k))).obj (family j)) :=
  (TopCat.Sheaf.pullbackComp
      (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))
      (openSubsetIntersectionLeftInclusion (U i) (U j))).symm.hom.app (family i) ≫
    ((TopCat.Sheaf.pullback (Type u)
      (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))).mapIso
        (overlapIso i j)).hom ≫
    (TopCat.Sheaf.pullbackComp
      (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))
      (openSubsetIntersectionRightInclusion (U i) (U j))).symm.inv.app (family j)

private abbrev tripleOverlapHom23
    {ι : Type w} (U : ι → Opens X)
    (family : ∀ i : ι, TopCat.Sheaf (Type u) (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      ((TopCat.Sheaf.pullback (Type u)
        (openSubsetIntersectionLeftInclusion (U i) (U j))).obj (family i)) ≅
      ((TopCat.Sheaf.pullback (Type u)
        (openSubsetIntersectionRightInclusion (U i) (U j))).obj (family j)))
    (i j k : ι) :
    ((TopCat.Sheaf.pullback (Type u)
      (openSubsetTripleSecondInclusion (U i) (U j) (U k))).obj (family j)) ⟶
    ((TopCat.Sheaf.pullback (Type u)
      (openSubsetTripleThirdInclusion (U i) (U j) (U k))).obj (family k)) :=
  (TopCat.Sheaf.pullbackComp
      (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))
      (openSubsetIntersectionLeftInclusion (U j) (U k))).symm.hom.app (family j) ≫
    ((TopCat.Sheaf.pullback (Type u)
      (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))).mapIso
        (overlapIso j k)).hom ≫
    (TopCat.Sheaf.pullbackComp
      (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))
      (openSubsetIntersectionRightInclusion (U j) (U k))).symm.inv.app (family k)

private abbrev tripleOverlapHom13
    {ι : Type w} (U : ι → Opens X)
    (family : ∀ i : ι, TopCat.Sheaf (Type u) (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      ((TopCat.Sheaf.pullback (Type u)
        (openSubsetIntersectionLeftInclusion (U i) (U j))).obj (family i)) ≅
      ((TopCat.Sheaf.pullback (Type u)
        (openSubsetIntersectionRightInclusion (U i) (U j))).obj (family j)))
    (i j k : ι) :
    ((TopCat.Sheaf.pullback (Type u)
      (openSubsetTripleFirstInclusion (U i) (U j) (U k))).obj (family i)) ⟶
    ((TopCat.Sheaf.pullback (Type u)
      (openSubsetTripleThirdInclusion (U i) (U j) (U k))).obj (family k)) :=
  (TopCat.Sheaf.pullbackComp
      (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))
      (openSubsetIntersectionLeftInclusion (U i) (U k))).symm.hom.app (family i) ≫
    ((TopCat.Sheaf.pullback (Type u)
      (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))).mapIso
        (overlapIso i k)).hom ≫
    (TopCat.Sheaf.pullbackComp
      (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))
      (openSubsetIntersectionRightInclusion (U i) (U k))).symm.inv.app (family k)

/-- The cocycle condition for pairwise overlap isomorphisms in a sheaf gluing datum over an open
cover. -/
def SheafOpenCoverGlueingCocycleCondition
    {ι : Type w} (U : ι → Opens X)
    (family : ∀ i : ι, TopCat.Sheaf (Type u) (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      ((TopCat.Sheaf.pullback (Type u)
        (openSubsetIntersectionLeftInclusion (U i) (U j))).obj (family i)) ≅
      ((TopCat.Sheaf.pullback (Type u)
        (openSubsetIntersectionRightInclusion (U i) (U j))).obj (family j))) :
    Prop :=
  ∀ i j k : ι,
    tripleOverlapHom12 U family overlapIso i j k ≫
      tripleOverlapHom23 U family overlapIso i j k =
    tripleOverlapHom13 U family overlapIso i j k

/-- Gluing data for sheaves of sets on an open cover: a family of local sheaves together with
pairwise overlap isomorphisms satisfying the cocycle condition on triple intersections. -/
structure SheafOpenCoverGlueing {ι : Type w} (U : ι → Opens X) where
  /-- The local sheaf on the cover member `U i`. -/
  localSheaf : ∀ i, TopCat.Sheaf (Type u) (openSubsetSpace (U i))
  /-- The prescribed identification of the restrictions of `F i` and `F j` to `U i ∩ U j`. -/
  overlapIso : ∀ i j,
    ((TopCat.Sheaf.pullback (Type u)
      (openSubsetIntersectionLeftInclusion (U i) (U j))).obj (localSheaf i)) ≅
    ((TopCat.Sheaf.pullback (Type u)
      (openSubsetIntersectionRightInclusion (U i) (U j))).obj (localSheaf j))
  /-- The overlap identifications satisfy the cocycle condition on triple intersections. -/
  cocycle : SheafOpenCoverGlueingCocycleCondition U localSheaf overlapIso
  /-- The indexed family of opens covers the ambient space. -/
  isCover : TopologicalSpace.IsOpenCover U

namespace SheafOpenCoverGlueing

variable {ι : Type w} {U : ι → Opens X}

private abbrev realizationLeftHom (data : SheafOpenCoverGlueing U)
    (F : X.Sheaf (Type u))
    (φ : ∀ i : ι,
      ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i))).obj F) ≅ data.localSheaf i)
    (i j : ι) :
    ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i ⊓ U j))).obj F) ⟶
      ((TopCat.Sheaf.pullback (Type u)
        (openSubsetIntersectionLeftInclusion (U i) (U j))).obj (data.localSheaf i)) :=
  (TopCat.Sheaf.pullbackComp
      (openSubsetIntersectionLeftInclusion (U i) (U j))
      (openSubsetInclusion (U i))).symm.hom.app F ≫
    ((TopCat.Sheaf.pullback (Type u)
      (openSubsetIntersectionLeftInclusion (U i) (U j))).mapIso (φ i)).hom

private abbrev realizationRightHom (data : SheafOpenCoverGlueing U)
    (F : X.Sheaf (Type u))
    (φ : ∀ i : ι,
      ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i))).obj F) ≅ data.localSheaf i)
    (i j : ι) :
    ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i ⊓ U j))).obj F) ⟶
      ((TopCat.Sheaf.pullback (Type u)
        (openSubsetIntersectionRightInclusion (U i) (U j))).obj (data.localSheaf j)) :=
  (TopCat.Sheaf.pullbackComp
      (openSubsetIntersectionRightInclusion (U i) (U j))
      (openSubsetInclusion (U j))).symm.hom.app F ≫
    ((TopCat.Sheaf.pullback (Type u)
      (openSubsetIntersectionRightInclusion (U i) (U j))).mapIso (φ j)).hom

/-- A sheaf on `X` realizes the given open-cover gluing datum if its restrictions to the cover
members recover the chosen local sheaves and the induced overlap comparisons agree with the
prescribed pairwise isomorphisms. -/
def Realizes (data : SheafOpenCoverGlueing U) (F : X.Sheaf (Type u)) : Prop :=
  ∃ φ : ∀ i : ι,
      ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i))).obj F) ≅ data.localSheaf i,
    ∀ i j : ι,
      realizationLeftHom data F φ i j ≫ (data.overlapIso i j).hom =
        realizationRightHom data F φ i j

/-- A morphism of open-cover gluing data is a family of local morphisms compatible with the
prescribed overlap isomorphisms. -/
@[ext] structure Hom (A B : SheafOpenCoverGlueing U) where
  /-- The component on each member of the open cover. -/
  hom : ∀ i, A.localSheaf i ⟶ B.localSheaf i
  /-- Compatibility with the pairwise overlap identifications. -/
  comm : ∀ i j,
    ((TopCat.Sheaf.pullback (Type u)
      (openSubsetIntersectionLeftInclusion (U i) (U j))).map (hom i)) ≫
        (B.overlapIso i j).hom =
      (A.overlapIso i j).hom ≫
        ((TopCat.Sheaf.pullback (Type u)
          (openSubsetIntersectionRightInclusion (U i) (U j))).map (hom j))

/-- The identity morphism of open-cover gluing data. -/
def id (A : SheafOpenCoverGlueing U) : Hom A A where
  hom i := 𝟙 (A.localSheaf i)
  comm i j := by simp

/-- Morphisms of open-cover gluing data are determined by their local components. -/
@[ext] theorem hom_ext {A B : SheafOpenCoverGlueing U} {f g : Hom A B}
    (h : ∀ i, f.hom i = g.hom i) : f = g := by
  cases f with
  | mk fh fc =>
    cases g with
    | mk gh gc =>
      dsimp at h
      have hh : fh = gh := funext h
      cases hh
      have hc : fc = gc := Subsingleton.elim _ _
      cases hc
      rfl

/-- Composition of morphisms of open-cover gluing data. -/
def comp {A B C : SheafOpenCoverGlueing U} (f : Hom A B) (g : Hom B C) : Hom A C where
  hom i := f.hom i ≫ g.hom i
  comm i j := by
    simpa [Functor.map_comp, Category.assoc] using
      calc
        ((TopCat.Sheaf.pullback (Type u)
            (openSubsetIntersectionLeftInclusion (U i) (U j))).map (f.hom i ≫ g.hom i)) ≫
            (C.overlapIso i j).hom
            =
              ((TopCat.Sheaf.pullback (Type u)
                  (openSubsetIntersectionLeftInclusion (U i) (U j))).map (f.hom i)) ≫
                (((TopCat.Sheaf.pullback (Type u)
                    (openSubsetIntersectionLeftInclusion (U i) (U j))).map (g.hom i)) ≫
                  (C.overlapIso i j).hom) := by
                    simp [Functor.map_comp, Category.assoc]
        _ =
              ((TopCat.Sheaf.pullback (Type u)
                  (openSubsetIntersectionLeftInclusion (U i) (U j))).map (f.hom i)) ≫
                ((B.overlapIso i j).hom ≫
                  ((TopCat.Sheaf.pullback (Type u)
                    (openSubsetIntersectionRightInclusion (U i) (U j))).map (g.hom j))) := by
                      rw [g.comm i j]
        _ =
              (((TopCat.Sheaf.pullback (Type u)
                  (openSubsetIntersectionLeftInclusion (U i) (U j))).map (f.hom i)) ≫
                (B.overlapIso i j).hom) ≫
                  ((TopCat.Sheaf.pullback (Type u)
                    (openSubsetIntersectionRightInclusion (U i) (U j))).map (g.hom j)) := by
                      simp [Category.assoc]
        _ =
              ((A.overlapIso i j).hom ≫
                ((TopCat.Sheaf.pullback (Type u)
                  (openSubsetIntersectionRightInclusion (U i) (U j))).map (f.hom j))) ≫
                    ((TopCat.Sheaf.pullback (Type u)
                      (openSubsetIntersectionRightInclusion (U i) (U j))).map (g.hom j)) := by
                        rw [f.comm i j]
        _ =
              (A.overlapIso i j).hom ≫
                (((TopCat.Sheaf.pullback (Type u)
                    (openSubsetIntersectionRightInclusion (U i) (U j))).map (f.hom j)) ≫
                  ((TopCat.Sheaf.pullback (Type u)
                    (openSubsetIntersectionRightInclusion (U i) (U j))).map (g.hom j))) := by
                      simp [Category.assoc]
        _ =
              (A.overlapIso i j).hom ≫
                ((TopCat.Sheaf.pullback (Type u)
                  (openSubsetIntersectionRightInclusion (U i) (U j))).map
                    (f.hom j ≫ g.hom j)) := by
                      simp [Functor.map_comp]

instance : Category (SheafOpenCoverGlueing U) where
  Hom A B := Hom A B
  id A := id A
  comp f g := comp f g
  id_comp f := by ext i; simp [id, comp]
  comp_id f := by ext i; simp [id, comp]
  assoc f g h := by ext i; simp [comp, Category.assoc]

private abbrev memberSheaf (U : ι → Opens X) (i : ι) :=
  (openSubsetSpace (U i)).Sheaf (Type u)

private abbrev overlapSheaf (U : ι → Opens X) (i j : ι) :=
  (openSubsetSpace (U i ⊓ U j)).Sheaf (Type u)

private abbrev tripleSheaf (U : ι → Opens X) (i j k : ι) :=
  (openSubsetSpace (U i ⊓ U j ⊓ U k)).Sheaf (Type u)

private abbrev restrictToMember (U : Opens X) :
    X.Sheaf (Type u) ⥤ (openSubsetSpace U).Sheaf (Type u) :=
  TopCat.Sheaf.pullback (Type u) (openSubsetInclusion U)

private abbrev restrictToOverlapLeft (U : ι → Opens X) (i j : ι) :
    memberSheaf U i ⥤ overlapSheaf U i j :=
  TopCat.Sheaf.pullback (Type u) (openSubsetIntersectionLeftInclusion (U i) (U j))

private abbrev restrictToOverlapRight (U : ι → Opens X) (i j : ι) :
    memberSheaf U j ⥤ overlapSheaf U i j :=
  TopCat.Sheaf.pullback (Type u) (openSubsetIntersectionRightInclusion (U i) (U j))

private abbrev restrictOverlapToTripleLeft (U : ι → Opens X) (i j k : ι) :
    overlapSheaf U i j ⥤ tripleSheaf U i j k :=
  TopCat.Sheaf.pullback (Type u) (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))

private abbrev restrictOverlapToTripleCenter (U : ι → Opens X) (i j k : ι) :
    overlapSheaf U j k ⥤ tripleSheaf U i j k :=
  TopCat.Sheaf.pullback (Type u) (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))

private abbrev restrictOverlapToTripleOuter (U : ι → Opens X) (i j k : ι) :
    overlapSheaf U i k ⥤ tripleSheaf U i j k :=
  TopCat.Sheaf.pullback (Type u) (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))

private abbrev restrictToTripleFirst (U : ι → Opens X) (i j k : ι) :
    memberSheaf U i ⥤ tripleSheaf U i j k :=
  TopCat.Sheaf.pullback (Type u) (openSubsetTripleFirstInclusion (U i) (U j) (U k))

private abbrev restrictToTripleSecond (U : ι → Opens X) (i j k : ι) :
    memberSheaf U j ⥤ tripleSheaf U i j k :=
  TopCat.Sheaf.pullback (Type u) (openSubsetTripleSecondInclusion (U i) (U j) (U k))

private abbrev restrictToTripleThird (U : ι → Opens X) (i j k : ι) :
    memberSheaf U k ⥤ tripleSheaf U i j k :=
  TopCat.Sheaf.pullback (Type u) (openSubsetTripleThirdInclusion (U i) (U j) (U k))

@[simp] private theorem openSubsetIntersectionLeftInclusion_comp_inclusion
    (U V : Opens X) :
    openSubsetIntersectionLeftInclusion U V ≫ openSubsetInclusion U =
      openSubsetInclusion (U ⊓ V) :=
  rfl

@[simp] private theorem openSubsetIntersectionRightInclusion_comp_inclusion
    (U V : Opens X) :
    openSubsetIntersectionRightInclusion U V ≫ openSubsetInclusion V =
      openSubsetInclusion (U ⊓ V) :=
  rfl

@[simp] private theorem openSubsetTripleToPairLeft_comp_intersectionLeft
    (U V W : Opens X) :
    openSubsetTripleToPairLeftInclusion U V W ≫ openSubsetIntersectionLeftInclusion U V =
      openSubsetTripleFirstInclusion U V W :=
  rfl

@[simp] private theorem openSubsetTripleToPairLeft_comp_intersectionRight
    (U V W : Opens X) :
    openSubsetTripleToPairLeftInclusion U V W ≫ openSubsetIntersectionRightInclusion U V =
      openSubsetTripleSecondInclusion U V W :=
  rfl

@[simp] private theorem openSubsetTripleToPairCenter_comp_intersectionLeft
    (U V W : Opens X) :
    openSubsetTripleToPairCenterInclusion U V W ≫ openSubsetIntersectionLeftInclusion V W =
      openSubsetTripleSecondInclusion U V W :=
  rfl

@[simp] private theorem openSubsetTripleToPairCenter_comp_intersectionRight
    (U V W : Opens X) :
    openSubsetTripleToPairCenterInclusion U V W ≫ openSubsetIntersectionRightInclusion V W =
      openSubsetTripleThirdInclusion U V W :=
  rfl

@[simp] private theorem openSubsetTripleToPairOuter_comp_intersectionLeft
    (U V W : Opens X) :
    openSubsetTripleToPairOuterInclusion U V W ≫ openSubsetIntersectionLeftInclusion U W =
      openSubsetTripleFirstInclusion U V W :=
  rfl

@[simp] private theorem openSubsetTripleToPairOuter_comp_intersectionRight
    (U V W : Opens X) :
    openSubsetTripleToPairOuterInclusion U V W ≫ openSubsetIntersectionRightInclusion U W =
      openSubsetTripleThirdInclusion U V W :=
  rfl

private noncomputable def restrictToTripleFirstViaIJIso (U : ι → Opens X) (i j k : ι) :
    restrictToTripleFirst U i j k ≅
      restrictToOverlapLeft U i j ⋙ restrictOverlapToTripleLeft U i j k :=
  eqToIso (congrArg (TopCat.Sheaf.pullback (Type u))
      (openSubsetTripleToPairLeft_comp_intersectionLeft (U i) (U j) (U k)).symm) ≪≫
    (TopCat.Sheaf.pullbackComp
      (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))
      (openSubsetIntersectionLeftInclusion (U i) (U j))).symm

private noncomputable def restrictToTripleSecondViaIJIso (U : ι → Opens X) (i j k : ι) :
    restrictToTripleSecond U i j k ≅
      restrictToOverlapRight U i j ⋙ restrictOverlapToTripleLeft U i j k :=
  eqToIso (congrArg (TopCat.Sheaf.pullback (Type u))
      (openSubsetTripleToPairLeft_comp_intersectionRight (U i) (U j) (U k)).symm) ≪≫
    (TopCat.Sheaf.pullbackComp
      (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))
      (openSubsetIntersectionRightInclusion (U i) (U j))).symm

private noncomputable def restrictToTripleSecondViaJKIso (U : ι → Opens X) (i j k : ι) :
    restrictToTripleSecond U i j k ≅
      restrictToOverlapLeft U j k ⋙ restrictOverlapToTripleCenter U i j k :=
  eqToIso (congrArg (TopCat.Sheaf.pullback (Type u))
      (openSubsetTripleToPairCenter_comp_intersectionLeft (U i) (U j) (U k)).symm) ≪≫
    (TopCat.Sheaf.pullbackComp
      (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))
      (openSubsetIntersectionLeftInclusion (U j) (U k))).symm

private noncomputable def restrictToTripleThirdViaJKIso (U : ι → Opens X) (i j k : ι) :
    restrictToTripleThird U i j k ≅
      restrictToOverlapRight U j k ⋙ restrictOverlapToTripleCenter U i j k :=
  eqToIso (congrArg (TopCat.Sheaf.pullback (Type u))
      (openSubsetTripleToPairCenter_comp_intersectionRight (U i) (U j) (U k)).symm) ≪≫
    (TopCat.Sheaf.pullbackComp
      (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))
      (openSubsetIntersectionRightInclusion (U j) (U k))).symm

private noncomputable def restrictToTripleFirstViaIKIso (U : ι → Opens X) (i j k : ι) :
    restrictToTripleFirst U i j k ≅
      restrictToOverlapLeft U i k ⋙ restrictOverlapToTripleOuter U i j k :=
  eqToIso (congrArg (TopCat.Sheaf.pullback (Type u))
      (openSubsetTripleToPairOuter_comp_intersectionLeft (U i) (U j) (U k)).symm) ≪≫
    (TopCat.Sheaf.pullbackComp
      (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))
      (openSubsetIntersectionLeftInclusion (U i) (U k))).symm

private noncomputable def restrictToTripleThirdViaIKIso (U : ι → Opens X) (i j k : ι) :
    restrictToTripleThird U i j k ≅
      restrictToOverlapRight U i k ⋙ restrictOverlapToTripleOuter U i j k :=
  eqToIso (congrArg (TopCat.Sheaf.pullback (Type u))
      (openSubsetTripleToPairOuter_comp_intersectionRight (U i) (U j) (U k)).symm) ≪≫
    (TopCat.Sheaf.pullbackComp
      (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))
      (openSubsetIntersectionRightInclusion (U i) (U k))).symm

private noncomputable def pairIsoOnTriple12 (U : ι → Opens X) (i j k : ι)
    (A : memberSheaf U i) (B : memberSheaf U j)
    (e : (restrictToOverlapLeft U i j).obj A ≅ (restrictToOverlapRight U i j).obj B) :
    (restrictToTripleFirst U i j k).obj A ≅ (restrictToTripleSecond U i j k).obj B :=
  (restrictToTripleFirstViaIJIso U i j k).app A ≪≫
    (restrictOverlapToTripleLeft U i j k).mapIso e ≪≫
      ((restrictToTripleSecondViaIJIso U i j k).app B).symm

private noncomputable def pairIsoOnTriple23 (U : ι → Opens X) (i j k : ι)
    (A : memberSheaf U j) (B : memberSheaf U k)
    (e : (restrictToOverlapLeft U j k).obj A ≅ (restrictToOverlapRight U j k).obj B) :
    (restrictToTripleSecond U i j k).obj A ≅ (restrictToTripleThird U i j k).obj B :=
  (restrictToTripleSecondViaJKIso U i j k).app A ≪≫
    (restrictOverlapToTripleCenter U i j k).mapIso e ≪≫
      ((restrictToTripleThirdViaJKIso U i j k).app B).symm

private noncomputable def pairIsoOnTriple13 (U : ι → Opens X) (i j k : ι)
    (A : memberSheaf U i) (B : memberSheaf U k)
    (e : (restrictToOverlapLeft U i k).obj A ≅ (restrictToOverlapRight U i k).obj B) :
    (restrictToTripleFirst U i j k).obj A ≅ (restrictToTripleThird U i j k).obj B :=
  (restrictToTripleFirstViaIKIso U i j k).app A ≪≫
    (restrictOverlapToTripleOuter U i j k).mapIso e ≪≫
      ((restrictToTripleThirdViaIKIso U i j k).app B).symm

private noncomputable def globalRestrictionToPairViaLeftIso (U : ι → Opens X) (i j : ι) :
    restrictToMember (U i ⊓ U j) ≅
      restrictToMember (U i) ⋙ restrictToOverlapLeft U i j :=
  eqToIso (congrArg (TopCat.Sheaf.pullback (Type u))
      (openSubsetIntersectionLeftInclusion_comp_inclusion (U i) (U j)).symm) ≪≫
    (TopCat.Sheaf.pullbackComp
      (openSubsetIntersectionLeftInclusion (U i) (U j))
      (openSubsetInclusion (U i))).symm

private noncomputable def globalRestrictionToPairViaRightIso (U : ι → Opens X) (i j : ι) :
    restrictToMember (U i ⊓ U j) ≅
      restrictToMember (U j) ⋙ restrictToOverlapRight U i j :=
  eqToIso (congrArg (TopCat.Sheaf.pullback (Type u))
      (openSubsetIntersectionRightInclusion_comp_inclusion (U i) (U j)).symm) ≪≫
    (TopCat.Sheaf.pullbackComp
      (openSubsetIntersectionRightInclusion (U i) (U j))
      (openSubsetInclusion (U j))).symm

private noncomputable def overlapIsoOfSheaf (U : ι → Opens X) (i j : ι)
    (F : X.Sheaf (Type u)) :
    (restrictToOverlapLeft U i j).obj ((restrictToMember (U i)).obj F) ≅
      (restrictToOverlapRight U i j).obj ((restrictToMember (U j)).obj F) :=
  ((globalRestrictionToPairViaLeftIso U i j).app F).symm ≪≫
    (globalRestrictionToPairViaRightIso U i j).app F

private theorem ofSheaf_cocycle (U : ι → Opens X) (F : X.Sheaf (Type u)) :
    ∀ i j k,
      (pairIsoOnTriple12 U i j k
        ((restrictToMember (U i)).obj F)
        ((restrictToMember (U j)).obj F)
        (overlapIsoOfSheaf U i j F)).hom ≫
        (pairIsoOnTriple23 U i j k
          ((restrictToMember (U j)).obj F)
          ((restrictToMember (U k)).obj F)
          (overlapIsoOfSheaf U j k F)).hom =
            (pairIsoOnTriple13 U i j k
              ((restrictToMember (U i)).obj F)
              ((restrictToMember (U k)).obj F)
              (overlapIsoOfSheaf U i k F)).hom := by
  intro i j k
  sorry

/-- The canonical gluing datum obtained by restricting a sheaf on `X` to the members of an open
cover `U`. -/
def ofSheaf (U : ι → Opens X) (hU : TopologicalSpace.IsOpenCover U) (F : X.Sheaf (Type u)) :
    SheafOpenCoverGlueing U where
  localSheaf i := (restrictToMember (U i)).obj F
  overlapIso i j := overlapIsoOfSheaf U i j F
  cocycle := ofSheaf_cocycle U F
  isCover := hU

private theorem ofSheaf_map_comm
    (U : ι → Opens X) {F G : X.Sheaf (Type u)} (α : F ⟶ G) :
    ∀ i j,
      (restrictToOverlapLeft U i j).map ((restrictToMember (U i)).map α) ≫
        (overlapIsoOfSheaf U i j G).hom =
          (overlapIsoOfSheaf U i j F).hom ≫
            (restrictToOverlapRight U i j).map ((restrictToMember (U j)).map α) := by
  intro i j
  sorry

/-- The restriction functor from sheaves on `X` to gluing data on the open cover `U`. -/
def ofSheafFunctor (U : ι → Opens X) (hU : TopologicalSpace.IsOpenCover U) :
    X.Sheaf (Type u) ⥤ SheafOpenCoverGlueing U where
  obj F := ofSheaf U hU F
  map α :=
    { hom := fun i ↦ (restrictToMember (U i)).map α
      comm := ofSheaf_map_comm U α }
  map_id F := by
    apply SheafOpenCoverGlueing.Hom.ext
    funext i
    change (restrictToMember (U i)).map (𝟙 F) =
      𝟙 ((restrictToMember (U i)).obj F)
    simp
  map_comp α β := by
    apply SheafOpenCoverGlueing.Hom.ext
    funext i
    change (restrictToMember (U i)).map (α ≫ β) =
      (restrictToMember (U i)).map α ≫ (restrictToMember (U i)).map β
    simp

end SheafOpenCoverGlueing

/-- A sheaf gluing datum on an open cover canonically supplies the covering hypothesis as a
`Fact`. -/
instance {ι : Type w} {U : ι → Opens X} (data : SheafOpenCoverGlueing U) :
    Fact (TopologicalSpace.IsOpenCover U) :=
  ⟨data.isCover⟩

end
