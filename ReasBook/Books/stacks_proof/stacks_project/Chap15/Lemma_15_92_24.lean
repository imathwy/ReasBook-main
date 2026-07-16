import Mathlib
import stacks_proof.stacks_project.Chap13.Lemma_13_4_7
import stacks_proof.stacks_project.Chap15.Definition_15_92_4
import stacks_proof.stacks_project.Chap15.Lemma_15_82_17.Index
import stacks_proof.stacks_project.Chap15.Lemma_15_92_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "DModB" => DerivedCategory (ModuleCat B)
local notation "HA" => DerivedCategory.homologyFunctor (ModuleCat A)
local notation "HB" => DerivedCategory.homologyFunctor (ModuleCat B)
local notation "UA" => ModuleCat.forget₂ A AddCommGrpCat
local notation "UB" => ModuleCat.forget₂ B AddCommGrpCat
local notation "DAb" => DerivedCategory AddCommGrpCat

/-- Helper for Lemma 15.92.24: derived completeness is equivalent to containment in the radical
ideal cut out by the localization-away vanishing condition. -/
theorem isDerivedCompleteWithRespectTo_iff_le_localizationAwayDerivedHomVanishingIdeal
    {R : Type u} [CommRing R]
    (K : DerivedCategory (ModuleCat R)) (I : Ideal R) :
    K.IsDerivedCompleteWithRespectTo I ↔ I ≤ K.localizationAwayDerivedHomVanishingIdeal := by
  constructor
  · intro hK
    -- Proof comment: unpack derived completeness at an element `f ∈ I` and read it as ideal
    -- membership in the localization-away vanishing ideal.
    intro f hf
    exact
      (CategoryTheory.DerivedCategory.isDerivedCompleteWithRespectTo_iff
        (K := K) (I := I)).1 hK f hf
  · intro hI
    -- Proof comment: conversely, ideal containment says exactly that every `f ∈ I` satisfies the
    -- vanishing condition defining derived completeness.
    rw [CategoryTheory.DerivedCategory.isDerivedCompleteWithRespectTo_iff]
    intro f hf
    exact
      (CategoryTheory.DerivedCategory.mem_localizationAwayDerivedHomVanishingIdeal_iff K f).1
        (hI hf)

/-- Helper for Lemma 15.92.24: restriction of scalars on the derived category both preserves and
reflects zero objects. -/
theorem isZero_restrictScalars_mapDerivedCategory_obj_iff
    (K : DModB) :
    IsZero (((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).obj K) ↔
      IsZero K := by
  constructor
  · intro hRestricted
    have hHomology :
        ∀ i : ℤ,
          IsZero ((DerivedCategory.homologyFunctor (ModuleCat B) i).obj K) := by
      intro i
      -- Proof comment: zero restricted derived object has zero restricted homology, and the
      -- canonical homology comparison reflects this back to the original `B`-module homology.
      have hzeroRestrictedHi :
          IsZero
            ((DerivedCategory.homologyFunctor (ModuleCat A) i).obj
              (((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).obj K)) :=
        (DerivedCategory.homologyFunctor (ModuleCat A) i).map_isZero hRestricted
      have hzeroRestrictedModule :
          IsZero
            ((ModuleCat.restrictScalars (algebraMap A B)).obj
              ((DerivedCategory.homologyFunctor (ModuleCat B) i).obj K)) :=
        (restrictScalars_homology_iso (f := algebraMap A B) K i).isZero_iff.1
          hzeroRestrictedHi
      exact
        isZero_of_restrictScalars_obj
          (f := algebraMap A B)
          ((DerivedCategory.homologyFunctor (ModuleCat B) i).obj K)
          hzeroRestrictedModule
    -- Proof comment: vanishing of every homology object places `K` in both halves of the
    -- standard t-structure with an empty support interval, hence `K` is zero.
    have hLE : K.IsLE 0 := by
      rw [DerivedCategory.isLE_iff]
      intro i hi
      exact hHomology i
    have hGE : K.IsGE 1 := by
      rw [DerivedCategory.isGE_iff]
      intro i hi
      exact hHomology i
    letI : K.IsLE 0 := hLE
    letI : K.IsGE 1 := hGE
    exact t.isZero K 0 1 (by omega)
  · intro hK
    -- Proof comment: the forward direction is functorial because restriction of scalars is an
    -- exact functor on modules, hence on the derived category as well.
    simpa using
      Functor.map_isZero
        ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory) hK

/-- Helper for Lemma 15.92.24: each successor map in the localization-away tower is scalar
multiplication by the chosen element. -/
theorem localizationAwayTower_map_succ
    {R : Type u} [CommRing R]
    (K : DerivedCategory (ModuleCat R)) (f : R) (n : ℕ) :
    (CategoryTheory.DerivedCategory.localizationAwayTower (A := R) f K).map
        (homOfLE (Nat.le_succ n)).op =
      f • 𝟙 K := by
  -- Proof comment: unfold the owner-level inverse system once; it is the constant tower on `K`
  -- with successor map `f • 𝟙`.
  simpa [CategoryTheory.DerivedCategory.localizationAwayTower,
    Functor.ofOpSequence_map_homOfLE_succ]

/-- Helper for Lemma 15.92.24: stagewise, restricting the `B`-localization-away tower along
`A → B` gives the same objects as the `A`-tower for the restricted complex. -/
theorem restrictScalars_localizationAwayTower_obj
    (L : DModB) (f : A) (n : ℕ) :
    (((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).obj
      ((CategoryTheory.DerivedCategory.localizationAwayTower
        (A := B) (algebraMap A B f) L).obj (Opposite.op n))) =
      (CategoryTheory.DerivedCategory.localizationAwayTower
        (A := A) f (((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).obj L)).obj
          (Opposite.op n) := by
  -- Proof comment: both source-facing towers are constant on the same restricted derived object.
  rfl

/-- Helper for Lemma 15.92.24: after restricting scalars, the successor maps in the
`B`-localization-away tower match the successor maps in the `A`-tower. -/
theorem restrictScalars_localizationAwayTower_map_succ
    (L : DModB) (f : A) (n : ℕ) :
    (((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).map
      ((CategoryTheory.DerivedCategory.localizationAwayTower
        (A := B) (algebraMap A B f) L).map (homOfLE (Nat.le_succ n)).op)) =
      (CategoryTheory.DerivedCategory.localizationAwayTower
        (A := A) f (((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).obj L)).map
          (homOfLE (Nat.le_succ n)).op := by
  -- Proof comment: both successor morphisms are multiplication by the same scalar `f`, and
  -- restriction of scalars commutes with that scalar action on morphisms.
  rw [localizationAwayTower_map_succ, localizationAwayTower_map_succ]
  simpa [Functor.map_id] using
    (Functor.map_smul
      ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory)
      f (𝟙 L)).symm

/-- Helper for Lemma 15.92.24: after forgetting to abelian groups, the two localization-away
towers agree. -/
theorem restrictScalars_localizationAwayTower_forget_iso
    (L : DModB) (f : A) :
    (CategoryTheory.DerivedCategory.localizationAwayTower
        (A := A) f
        (((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).obj L) ⋙
      UA.mapDerivedCategory) ≅
      (CategoryTheory.DerivedCategory.localizationAwayTower
        (A := B) (algebraMap A B f) L ⋙
        UB.mapDerivedCategory) := by
  -- Proof comment: both forgotten towers are definitionally the same constant tower on the
  -- underlying abelian-group object, with transition map given by multiplication by `f`.
  rfl

/-- Helper for Lemma 15.92.24: a tower isomorphism induces an isomorphism between the associated
product objects. -/
private noncomputable def tower_product_iso
    {Ksys Lsys : SequentialInverseSystem DAb}
    [HasProduct (inverseSystemFamily Ksys)] [HasProduct (inverseSystemFamily Lsys)]
    (e : Ksys ≅ Lsys) :
    (∏ᶜ inverseSystemFamily Ksys) ≅ ∏ᶜ inverseSystemFamily Lsys := by
  -- Proof comment: transport the discrete product diagram stagewise along the given tower
  -- isomorphism.
  let eFamily :
      Discrete.functor (inverseSystemFamily Ksys) ≅
        Discrete.functor (inverseSystemFamily Lsys) :=
    Discrete.natIso fun n : Discrete ℕ ↦ e.app (Opposite.op n.as)
  exact HasLimit.isoOfNatIso eFamily

/-- Helper for Lemma 15.92.24: the product isomorphism induced by a tower isomorphism preserves
each stage projection. -/
private theorem tower_product_iso_hom_comp_π
    {Ksys Lsys : SequentialInverseSystem DAb}
    [HasProduct (inverseSystemFamily Ksys)] [HasProduct (inverseSystemFamily Lsys)]
    (e : Ksys ≅ Lsys) (n : ℕ) :
    (tower_product_iso e).hom ≫ Pi.π (inverseSystemFamily Lsys) n =
      Pi.π (inverseSystemFamily Ksys) n ≫ (e.app (Opposite.op n)).hom := by
  -- Proof comment: this is the defining projection formula for `HasLimit.isoOfNatIso`.
  let eFamily :
      Discrete.functor (inverseSystemFamily Ksys) ≅
        Discrete.functor (inverseSystemFamily Lsys) :=
    Discrete.natIso fun m : Discrete ℕ ↦ e.app (Opposite.op m.as)
  simpa [tower_product_iso, eFamily] using
    limMap_π (α := eFamily.hom) (j := Discrete.mk n)

/-- Helper for Lemma 15.92.24: the product isomorphism induced by a tower isomorphism
intertwines the two Milnor difference maps. -/
private theorem tower_product_iso_hom_comm_difference
    {Ksys Lsys : SequentialInverseSystem DAb}
    [HasProduct (inverseSystemFamily Ksys)] [HasProduct (inverseSystemFamily Lsys)]
    (e : Ksys ≅ Lsys) :
    (tower_product_iso e).hom ≫ derivedLimitDifferenceMap Lsys =
      derivedLimitDifferenceMap Ksys ≫ (tower_product_iso e).hom := by
  -- Proof comment: compare the two Milnor endomorphisms after each projection to reduce to tower
  -- naturality.
  apply Pi.hom_ext
  intro n
  calc
    ((tower_product_iso e).hom ≫ derivedLimitDifferenceMap Lsys) ≫
        Pi.π (inverseSystemFamily Lsys) n =
      (tower_product_iso e).hom ≫
        (Pi.π (inverseSystemFamily Lsys) n -
          Pi.π (inverseSystemFamily Lsys) (n + 1) ≫
            Lsys.transitionMap (Nat.le_succ n)) := by
          rw [Category.assoc, derivedLimitDifferenceMap_comp_π]
    _ =
      Pi.π (inverseSystemFamily Ksys) n ≫ (e.app (Opposite.op n)).hom -
        (Pi.π (inverseSystemFamily Ksys) (n + 1) ≫
          (e.app (Opposite.op (n + 1))).hom ≫
            Lsys.transitionMap (Nat.le_succ n)) := by
          rw [Preadditive.comp_sub]
          rw [tower_product_iso_hom_comp_π]
          simpa [Category.assoc] using
            congrArg
              (fun t ↦ t ≫ Lsys.transitionMap (Nat.le_succ n))
              (tower_product_iso_hom_comp_π e (n + 1))
    _ =
      Pi.π (inverseSystemFamily Ksys) n ≫ (e.app (Opposite.op n)).hom -
        (Pi.π (inverseSystemFamily Ksys) (n + 1) ≫
          Ksys.transitionMap (Nat.le_succ n) ≫
            (e.app (Opposite.op n)).hom) := by
          -- Proof comment: naturality identifies the successor-transition contribution.
          congr 1
          simpa [Category.assoc] using
            congrArg
              (fun t ↦ Pi.π (inverseSystemFamily Ksys) (n + 1) ≫ t)
              (e.hom.naturality ((homOfLE (Nat.le_succ n)).op)).symm
    _ =
      (Pi.π (inverseSystemFamily Ksys) n -
        Pi.π (inverseSystemFamily Ksys) (n + 1) ≫
          Ksys.transitionMap (Nat.le_succ n)) ≫
        (e.app (Opposite.op n)).hom := by
          rw [Preadditive.sub_comp]
          simp [Category.assoc]
    _ =
      derivedLimitDifferenceMap Ksys ≫ Pi.π (inverseSystemFamily Ksys) n ≫
        (e.app (Opposite.op n)).hom := by
          rw [← derivedLimitDifferenceMap_comp_π_assoc]
    _ =
      ((derivedLimitDifferenceMap Ksys ≫ (tower_product_iso e).hom) ≫
        Pi.π (inverseSystemFamily Lsys) n) := by
          rw [Category.assoc, ← tower_product_iso_hom_comp_π, ← Category.assoc]

/-- Helper for Lemma 15.92.24: a derived-limit witness transports across an isomorphism of
forgotten towers when the limiting object is kept fixed. -/
private theorem isDerivedLimit_of_tower_iso
    {Ksys Lsys : SequentialInverseSystem DAb} {K : DAb}
    (e : Ksys ≅ Lsys)
    (hK : IsDerivedLimit Ksys K) :
    IsDerivedLimit Lsys K := by
  rcases hK with ⟨hP, hMilnor⟩
  letI : HasProduct (inverseSystemFamily Ksys) := hP
  let eFamily :
      Discrete.functor (inverseSystemFamily Ksys) ≅
        Discrete.functor (inverseSystemFamily Lsys) :=
    Discrete.natIso fun n : Discrete ℕ ↦ e.app (Opposite.op n.as)
  let hQ : HasProduct (inverseSystemFamily Lsys) := by
    exact hasLimit_of_iso eFamily
  letI : HasProduct (inverseSystemFamily Lsys) := hQ
  rcases hMilnor with ⟨ι, δ, hδ⟩
  let p : (∏ᶜ inverseSystemFamily Ksys) ≅ ∏ᶜ inverseSystemFamily Lsys :=
    tower_product_iso e
  let T : Triangle DAb :=
    Triangle.mk ι (derivedLimitDifferenceMap Ksys) δ
  let T' : Triangle DAb :=
    Triangle.mk (ι ≫ p.hom) (derivedLimitDifferenceMap Lsys) (p.inv ≫ δ)
  have hIso : T ≅ T' := by
    -- Proof comment: repackage the original Milnor triangle through the product comparison
    -- isomorphism induced by the tower isomorphism.
    refine Triangle.isoMk _ _ (Iso.refl _) p p ?_ ?_ ?_
    · simp [T, T']
    · simpa [T, T'] using (tower_product_iso_hom_comm_difference e).symm
    · simp [T, T']
  have hT' : T' ∈ distTriang DAb := by
    -- Proof comment: distinguished triangles are stable under isomorphism.
    exact isomorphic_distinguished _ hδ _ hIso.symm
  exact ⟨hQ, ⟨ι ≫ p.hom, p.inv ≫ δ, hT'⟩⟩

/-- Helper for Lemma 15.92.24: once a Milnor triangle is known for a fixed forgotten tower, the
limiting object can be replaced by any isomorphic object. -/
private theorem isDerivedLimit_of_object_iso
    {Ksys : SequentialInverseSystem DAb} {K L : DAb}
    (e : K ≅ L)
    (hK : IsDerivedLimit Ksys K) :
    IsDerivedLimit Ksys L := by
  rcases hK with ⟨hP, hMilnor⟩
  letI : HasProduct (inverseSystemFamily Ksys) := hP
  rcases hMilnor with ⟨ι, δ, hδ⟩
  let T : Triangle DAb :=
    Triangle.mk ι (derivedLimitDifferenceMap Ksys) δ
  let T' : Triangle DAb :=
    Triangle.mk (e.inv ≫ ι) (derivedLimitDifferenceMap Ksys)
      (δ ≫ (shiftFunctor DAb (1 : ℤ)).map e.hom)
  have hIso : T ≅ T' := by
    -- Proof comment: precompose the Milnor comparison map by the chosen object isomorphism and
    -- adjust the connecting morphism by the shifted companion isomorphism.
    refine Triangle.isoMk e (Iso.refl _) (e.commShiftIso (1 : ℤ)) ?_ ?_ ?_
    · simp [T, T']
    · simp [T, T']
    · simp [T, T']
  have hT' : T' ∈ distTriang DAb := by
    -- Proof comment: the Milnor triangle stays distinguished after changing only the limit
    -- vertex by an isomorphism.
    exact isomorphic_distinguished _ hδ _ hIso.symm
  exact ⟨hP, ⟨e.inv ≫ ι, δ ≫ (shiftFunctor DAb (1 : ℤ)).map e.hom, hT'⟩⟩

/-- Helper for Lemma 15.92.24: forgetting module structure carries the canonical localization-away
derived limit to a derived limit of the forgotten localization-away tower. -/
private theorem forget_module_localizationAwayT_isDerivedLimit
    {R : Type u} [CommRing R]
    (K : DerivedCategory (ModuleCat R)) (f : R) :
    IsDerivedLimit
      (CategoryTheory.DerivedCategory.localizationAwayTower (A := R) f K ⋙
        (ModuleCat.forget₂ R AddCommGrpCat).mapDerivedCategory)
      (((ModuleCat.forget₂ R AddCommGrpCat).mapDerivedCategory).obj
        (CategoryTheory.DerivedCategory.localizationAwayT
          (A := R) (inferInstance : MonoidalClosed (DerivedCategory (ModuleCat R))) f K)) := by
  let G :
      DerivedCategory (ModuleCat R) ⥤ DAb :=
    (ModuleCat.forget₂ R AddCommGrpCat).mapDerivedCategory
  letI : G.IsTriangulated := inferInstance
  letI : PreservesLimitsOfShape (Discrete ℕ) G := inferInstance
  let hK :
      IsDerivedLimit
        (CategoryTheory.DerivedCategory.localizationAwayTower (A := R) f K)
        (CategoryTheory.DerivedCategory.localizationAwayT
          (A := R) (inferInstance : MonoidalClosed (DerivedCategory (ModuleCat R))) f K) :=
    CategoryTheory.DerivedCategory.localizationAwayT_isDerivedLimit
      (A := R) (H := (inferInstance : MonoidalClosed (DerivedCategory (ModuleCat R)))) f K
  rcases hK with ⟨hP, ⟨ι, δ, hδ⟩⟩
  letI : HasProduct
      (inverseSystemFamily
        (CategoryTheory.DerivedCategory.localizationAwayTower (A := R) f K)) := hP
  let _ :
      PreservesLimit
        (Discrete.functor
          (inverseSystemFamily
            (CategoryTheory.DerivedCategory.localizationAwayTower (A := R) f K))) G := by
    infer_instance
  let hQ :
      HasProduct
        (inverseSystemFamily
          (CategoryTheory.DerivedCategory.localizationAwayTower (A := R) f K ⋙ G)) := by
    refine HasLimit.mk ⟨
      Fan.mk
        (G.obj
          (∏ᶜ inverseSystemFamily
            (CategoryTheory.DerivedCategory.localizationAwayTower (A := R) f K)))
        (fun n ↦ G.map
          (Pi.π
            (inverseSystemFamily
              (CategoryTheory.DerivedCategory.localizationAwayTower (A := R) f K)) n)),
      ?_⟩
    simpa [inverseSystemFamily] using
      (isLimitOfHasProductOfPreservesLimit G
        (inverseSystemFamily
          (CategoryTheory.DerivedCategory.localizationAwayTower (A := R) f K)))
  letI :
      HasProduct
        (inverseSystemFamily
          (CategoryTheory.DerivedCategory.localizationAwayTower (A := R) f K ⋙ G)) := hQ
  let eprod :
      G.obj
          (∏ᶜ inverseSystemFamily
            (CategoryTheory.DerivedCategory.localizationAwayTower (A := R) f K)) ≅
        ∏ᶜ inverseSystemFamily
          (CategoryTheory.DerivedCategory.localizationAwayTower (A := R) f K ⋙ G) :=
    PreservesProduct.iso G
      (inverseSystemFamily
        (CategoryTheory.DerivedCategory.localizationAwayTower (A := R) f K))
  have heprod_π (n : ℕ) :
      eprod.hom ≫
          Pi.π
            (inverseSystemFamily
              (CategoryTheory.DerivedCategory.localizationAwayTower (A := R) f K ⋙ G)) n =
        G.map
          (Pi.π
            (inverseSystemFamily
              (CategoryTheory.DerivedCategory.localizationAwayTower (A := R) f K)) n) := by
    simpa [eprod, CategoryTheory.Limits.PreservesProduct.iso_hom, inverseSystemFamily,
      Category.assoc] using
      (piComparison_comp_π G
        (inverseSystemFamily
          (CategoryTheory.DerivedCategory.localizationAwayTower (A := R) f K)) n)
  have heprod_difference :
      G.map
          (derivedLimitDifferenceMap
            (CategoryTheory.DerivedCategory.localizationAwayTower (A := R) f K)) ≫
        eprod.hom =
      eprod.hom ≫
        derivedLimitDifferenceMap
          (CategoryTheory.DerivedCategory.localizationAwayTower (A := R) f K ⋙ G) := by
    -- Proof comment: compare both morphisms after each stage projection of the forgotten
    -- product and rewrite by the Milnor difference-map formula.
    apply Pi.hom_ext
    intro n
    calc
      (G.map
            (derivedLimitDifferenceMap
              (CategoryTheory.DerivedCategory.localizationAwayTower (A := R) f K)) ≫
          eprod.hom) ≫
            Pi.π
              (inverseSystemFamily
                (CategoryTheory.DerivedCategory.localizationAwayTower (A := R) f K ⋙ G)) n =
        G.map
            (derivedLimitDifferenceMap
              (CategoryTheory.DerivedCategory.localizationAwayTower (A := R) f K)) ≫
          G.map
            (Pi.π
              (inverseSystemFamily
                (CategoryTheory.DerivedCategory.localizationAwayTower (A := R) f K)) n) := by
          rw [Category.assoc, heprod_π]
      _ =
        G.map
          (derivedLimitDifferenceMap
              (CategoryTheory.DerivedCategory.localizationAwayTower (A := R) f K) ≫
            Pi.π
              (inverseSystemFamily
                (CategoryTheory.DerivedCategory.localizationAwayTower (A := R) f K)) n) := by
          simp [Functor.map_comp]
      _ =
        G.map
          (Pi.π
              (inverseSystemFamily
                (CategoryTheory.DerivedCategory.localizationAwayTower (A := R) f K)) n -
            Pi.π
                (inverseSystemFamily
                  (CategoryTheory.DerivedCategory.localizationAwayTower (A := R) f K)) (n + 1) ≫
              (CategoryTheory.DerivedCategory.localizationAwayTower (A := R) f K).transitionMap
                (Nat.le_succ n)) := by
          rw [derivedLimitDifferenceMap_comp_π]
      _ =
        G.map
          (Pi.π
              (inverseSystemFamily
                (CategoryTheory.DerivedCategory.localizationAwayTower (A := R) f K)) n) -
          G.map
            (Pi.π
                (inverseSystemFamily
                  (CategoryTheory.DerivedCategory.localizationAwayTower (A := R) f K)) (n + 1) ≫
              (CategoryTheory.DerivedCategory.localizationAwayTower (A := R) f K).transitionMap
                (Nat.le_succ n)) := by
          simp [Functor.map_sub]
      _ =
        G.map
          (Pi.π
              (inverseSystemFamily
                (CategoryTheory.DerivedCategory.localizationAwayTower (A := R) f K)) n) -
          (G.map
              (Pi.π
                (inverseSystemFamily
                  (CategoryTheory.DerivedCategory.localizationAwayTower (A := R) f K)) (n + 1)) ≫
            (CategoryTheory.DerivedCategory.localizationAwayTower (A := R) f K ⋙ G)
              .transitionMap
                (Nat.le_succ n)) := by
          simp [Functor.map_comp, SequentialInverseSystem.transitionMap]
      _ =
        (eprod.hom ≫
            Pi.π
              (inverseSystemFamily
                (CategoryTheory.DerivedCategory.localizationAwayTower (A := R) f K ⋙ G)) n) -
          ((eprod.hom ≫
              Pi.π
                (inverseSystemFamily
                  (CategoryTheory.DerivedCategory.localizationAwayTower (A := R) f K ⋙ G))
                  (n + 1)) ≫
            (CategoryTheory.DerivedCategory.localizationAwayTower (A := R) f K ⋙ G)
              .transitionMap
                (Nat.le_succ n)) := by
          rw [heprod_π, heprod_π]
      _ =
        eprod.hom ≫
          (Pi.π
              (inverseSystemFamily
                (CategoryTheory.DerivedCategory.localizationAwayTower (A := R) f K ⋙ G)) n -
            Pi.π
                (inverseSystemFamily
                  (CategoryTheory.DerivedCategory.localizationAwayTower (A := R) f K ⋙ G))
                  (n + 1) ≫
              (CategoryTheory.DerivedCategory.localizationAwayTower (A := R) f K ⋙ G)
                .transitionMap
                  (Nat.le_succ n)) := by
          rw [Preadditive.comp_sub]
          simp [Category.assoc]
      _ =
        eprod.hom ≫
          derivedLimitDifferenceMap
            (CategoryTheory.DerivedCategory.localizationAwayTower (A := R) f K ⋙ G) := by
          rw [derivedLimitDifferenceMap_comp_π]
  let Tmilnor : Triangle (DerivedCategory (ModuleCat R)) :=
    Triangle.mk ι
      (derivedLimitDifferenceMap
        (CategoryTheory.DerivedCategory.localizationAwayTower (A := R) f K))
      δ
  let Tmapped : Triangle DAb :=
    G.mapTriangle.obj Tmilnor
  let Ttransported : Triangle DAb :=
    Triangle.mk
      (G.map ι ≫ eprod.hom)
      (derivedLimitDifferenceMap
        (CategoryTheory.DerivedCategory.localizationAwayTower (A := R) f K ⋙ G))
      (eprod.inv ≫ G.map δ ≫ (G.commShiftIso (1 : ℤ)).hom.app
        (CategoryTheory.DerivedCategory.localizationAwayT
          (A := R) (inferInstance : MonoidalClosed (DerivedCategory (ModuleCat R))) f K))
  have hIso : Tmapped ≅ Ttransported := by
    -- Proof comment: rewrite the mapped product vertex to the canonical product of the forgotten
    -- tower and replace the middle morphism by the standard forgotten Milnor difference map.
    refine Triangle.isoMk _ _ (Iso.refl _) eprod eprod ?_ ?_ ?_
    · simp [Tmapped, Tmilnor, Ttransported]
    · simpa [Tmapped, Tmilnor, Ttransported, Category.assoc] using heprod_difference
    · simp [Tmapped, Tmilnor, Ttransported, Category.assoc]
  have hTtransported : Ttransported ∈ distTriang DAb := by
    -- Proof comment: the forgetful derived functor is triangulated, so the transported Milnor
    -- triangle remains distinguished after the product rewrite.
    exact isomorphic_distinguished _ (G.map_distinguished Tmilnor hδ) _ hIso.symm
  exact
    ⟨hQ, ⟨G.map ι ≫ eprod.hom,
      eprod.inv ≫ G.map δ ≫ (G.commShiftIso (1 : ℤ)).hom.app
        (CategoryTheory.DerivedCategory.localizationAwayT
          (A := R) (inferInstance : MonoidalClosed (DerivedCategory (ModuleCat R))) f K),
      hTtransported⟩⟩

/-- Helper for Lemma 15.92.24: after forgetting module structure, the two localization-away
objects are isomorphic because they are both derived limits of the same forgotten tower. -/
private noncomputable def localizationAwayT_forget_iso
    (L : DModB) (f : A) :
    UA.mapDerivedCategory.obj
        (CategoryTheory.DerivedCategory.localizationAwayT
          (A := A) (inferInstance : MonoidalClosed DModA) f
          (((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).obj L)) ≅
      UB.mapDerivedCategory.obj
        (CategoryTheory.DerivedCategory.localizationAwayT
          (A := B) (inferInstance : MonoidalClosed DModB) (algebraMap A B f) L) := by
  let Ksys :
      SequentialInverseSystem DAb :=
    CategoryTheory.DerivedCategory.localizationAwayTower
      (A := A) f (((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).obj L) ⋙
        UA.mapDerivedCategory
  let hA :
      IsDerivedLimit Ksys
        (UA.mapDerivedCategory.obj
          (CategoryTheory.DerivedCategory.localizationAwayT
            (A := A) (inferInstance : MonoidalClosed DModA) f
            (((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).obj L))) :=
    forget_module_localizationAwayT_isDerivedLimit
      (R := A)
      (((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).obj L) f
  let hBbase :
      IsDerivedLimit
        (CategoryTheory.DerivedCategory.localizationAwayTower
          (A := B) (algebraMap A B f) L ⋙ UB.mapDerivedCategory)
        (UB.mapDerivedCategory.obj
          (CategoryTheory.DerivedCategory.localizationAwayT
            (A := B) (inferInstance : MonoidalClosed DModB) (algebraMap A B f) L)) :=
    forget_module_localizationAwayT_isDerivedLimit
      (R := B) L (algebraMap A B f)
  let hB :
      IsDerivedLimit Ksys
        (UB.mapDerivedCategory.obj
          (CategoryTheory.DerivedCategory.localizationAwayT
            (A := B) (inferInstance : MonoidalClosed DModB) (algebraMap A B f) L)) :=
    isDerivedLimit_of_tower_iso
      (restrictScalars_localizationAwayTower_forget_iso (A := A) (B := B) L f).symm
      hBbase
  rcases hA with ⟨hP, ⟨ιA, δA, hδA⟩⟩
  letI : HasProduct (inverseSystemFamily Ksys) := hP
  rcases hB with ⟨_, ⟨ιB, δB, hδB⟩⟩
  let TA : Triangle DAb :=
    Triangle.mk ιA (derivedLimitDifferenceMap Ksys) δA
  let TB : Triangle DAb :=
    Triangle.mk ιB (derivedLimitDifferenceMap Ksys) δB
  have hTArot : TA.rotate ∈ distTriang DAb := by
    -- Proof comment: rotate the first Milnor triangle so that the common difference map becomes
    -- the first morphism.
    simpa [TA] using rot_of_distTriang TA hδA
  have hTBrot : TB.rotate ∈ distTriang DAb := by
    -- Proof comment: do the same for the second Milnor triangle.
    simpa [TB] using rot_of_distTriang TB hδB
  obtain ⟨e, he₁, he₂⟩ :=
    exists_distinguished_triangle_unique_up_to_iso hTArot hTBrot
  have hIso₃ : IsIso e.hom.hom₃ := by
    letI : IsIso e.hom.hom₁ := by simpa [he₁]
    letI : IsIso e.hom.hom₂ := by simpa [he₂]
    exact Pretriangulated.isIso₃_of_isIso₁₂ e.hom hTArot hTBrot inferInstance inferInstance
  letI : IsIso e.hom.hom₃ := hIso₃
  let eshift :
      (shiftFunctor DAb (1 : ℤ)).obj
          (UA.mapDerivedCategory.obj
            (CategoryTheory.DerivedCategory.localizationAwayT
              (A := A) (inferInstance : MonoidalClosed DModA) f
              (((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).obj L))) ≅
        (shiftFunctor DAb (1 : ℤ)).obj
          (UB.mapDerivedCategory.obj
            (CategoryTheory.DerivedCategory.localizationAwayT
              (A := B) (inferInstance : MonoidalClosed DModB) (algebraMap A B f) L)) :=
    asIso e.hom.hom₃
  -- Proof comment: shift back by `[-1]` and use the shift-equivalence counit to recover an
  -- isomorphism between the underlying forgotten localization-away objects.
  exact
    ((shiftFunctorCompIsoId DAb (1 : ℤ) (-1 : ℤ) (by omega)).app _).symm ≪≫
      (shiftFunctor DAb (-1 : ℤ)).mapIso eshift ≪≫
      (shiftFunctorCompIsoId DAb (1 : ℤ) (-1 : ℤ) (by omega)).app _

/-- Helper for Lemma 15.92.24: if the underlying abelian group of a module is zero, then the
module itself is zero. -/
theorem isZero_of_forget_addCommGrp_obj
    {R : Type u} [CommRing R]
    (M : ModuleCat R)
    (hM : IsZero ((ModuleCat.forget₂ R AddCommGrpCat).obj M)) :
    IsZero M := by
  -- Proof comment: forgetting to abelian groups does not change the underlying carrier, so
  -- subsingleton underlying groups reflect zero modules.
  letI : Subsingleton ↑((ModuleCat.forget₂ R AddCommGrpCat).obj M) :=
    AddCommGrpCat.subsingleton_of_isZero hM
  have hsub : Subsingleton ↑M := by
    simpa using
      (inferInstance : Subsingleton ↑((ModuleCat.forget₂ R AddCommGrpCat).obj M))
  letI : Subsingleton ↑M := hsub
  exact ModuleCat.isZero_of_subsingleton M

/-- Helper for Lemma 15.92.24: forgetting module structure commutes with homology on the derived
category of modules. -/
theorem forget_module_homology_iso
    {R : Type u} [CommRing R]
    (K : DerivedCategory (ModuleCat R)) (i : ℤ) :
    (DerivedCategory.homologyFunctor AddCommGrpCat i).obj
        ((ModuleCat.forget₂ R AddCommGrpCat).mapDerivedCategory.obj K) ≅
      (ModuleCat.forget₂ R AddCommGrpCat).obj
        ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj K) := by
  letI : Limits.PreservesFiniteLimits (ModuleCat.forget₂ R AddCommGrpCat) := inferInstance
  let C := DerivedCategory.Q.objPreimage K
  let FC := ((ModuleCat.forget₂ R AddCommGrpCat).mapHomologicalComplex (ComplexShape.up ℤ)).obj C
  let eR :
      (DerivedCategory.homologyFunctor (ModuleCat R) i).obj K ≅ C.homology i :=
    ((DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso
      (DerivedCategory.Q.objObjPreimageIso K)).symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat R) i).app C
  -- Proof comment: compute homology on a chosen cochain model of `K`, forget to abelian groups
  -- before taking strict homology, and then return to the derived category.
  exact
    (DerivedCategory.homologyFunctor AddCommGrpCat i).mapIso
        ((((ModuleCat.forget₂ R AddCommGrpCat).mapDerivedCategory).mapIso
            (DerivedCategory.Q.objObjPreimageIso K)).symm ≪≫
          ((ModuleCat.forget₂ R AddCommGrpCat).mapDerivedCategoryFactors.app C)) ≪≫
      (DerivedCategory.homologyFunctorFactors AddCommGrpCat i).app FC ≪≫
      (C.sc i).mapHomologyIso (ModuleCat.forget₂ R AddCommGrpCat) ≪≫
      (ModuleCat.forget₂ R AddCommGrpCat).mapIso eR.symm

/-- Helper for Lemma 15.92.24: after forgetting to abelian groups, the degreewise homology of the
two localization-away objects agrees. -/
theorem localizationAwayT_homology_forget_iso
    (L : DModB) (f : A) (i : ℤ) :
    (UA.obj
      ((HA i).obj
        (CategoryTheory.DerivedCategory.localizationAwayT
          (A := A) (inferInstance : MonoidalClosed DModA) f
          (((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).obj L)))) ≅
      (UB.obj
        ((HB i).obj
          (CategoryTheory.DerivedCategory.localizationAwayT
            (A := B) (inferInstance : MonoidalClosed DModB) (algebraMap A B f) L))) := by
  -- Route correction: the source proof compares `T(-,f)` only after applying cohomology in
  -- abelian groups, not by transporting the derived-limit witness inside module categories.
  -- Proof comment: first compare the two forgotten `T`-objects in `D(Ab)`, then apply the
  -- abelian-group-valued homology functor and translate back to forgotten module homology.
  let TA : DModA :=
    CategoryTheory.DerivedCategory.localizationAwayT
      (A := A) (inferInstance : MonoidalClosed DModA) f
      (((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).obj L)
  let TB : DModB :=
    CategoryTheory.DerivedCategory.localizationAwayT
      (A := B) (inferInstance : MonoidalClosed DModB) (algebraMap A B f) L
  exact
    (forget_module_homology_iso (R := A) TA i).symm ≪≫
      (DerivedCategory.homologyFunctor AddCommGrpCat i).mapIso
        (localizationAwayT_forget_iso (A := A) (B := B) L f) ≪≫
      (forget_module_homology_iso (R := B) TB i)

/-- Helper for Lemma 15.92.24: the degreewise homology of the two localization-away objects
vanishes simultaneously. -/
theorem homology_isZero_localizationAwayT_restrictScalars_iff
    (L : DModB) (f : A) (i : ℤ) :
    IsZero
        ((HA i).obj
          (CategoryTheory.DerivedCategory.localizationAwayT
            (A := A) (inferInstance : MonoidalClosed DModA) f
            (((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).obj L))) ↔
      IsZero
        ((HB i).obj
          (CategoryTheory.DerivedCategory.localizationAwayT
            (A := B) (inferInstance : MonoidalClosed DModB) (algebraMap A B f) L)) := by
  constructor
  · intro hA
    -- Proof comment: forget the `A`-module structure on homology, transport the resulting zero
    -- object across the abelian-group comparison, and then reflect zero back to `B`-modules.
    have hAforget :
        IsZero
          (UA.obj
            ((HA i).obj
              (CategoryTheory.DerivedCategory.localizationAwayT
                (A := A) (inferInstance : MonoidalClosed DModA) f
                (((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).obj L)))) :=
      UA.map_isZero hA
    have hBforget :
        IsZero
          (UB.obj
            ((HB i).obj
              (CategoryTheory.DerivedCategory.localizationAwayT
                (A := B) (inferInstance : MonoidalClosed DModB) (algebraMap A B f) L))) :=
      (localizationAwayT_homology_forget_iso (A := A) (B := B) (L := L) f i).isZero_iff.1
        hAforget
    exact
      isZero_of_forget_addCommGrp_obj
        ((HB i).obj
          (CategoryTheory.DerivedCategory.localizationAwayT
            (A := B) (inferInstance : MonoidalClosed DModB) (algebraMap A B f) L))
        hBforget
  · intro hB
    -- Proof comment: the reverse direction is the same argument with the comparison isomorphism
    -- used in the opposite orientation.
    have hBforget :
        IsZero
          (UB.obj
            ((HB i).obj
              (CategoryTheory.DerivedCategory.localizationAwayT
                (A := B) (inferInstance : MonoidalClosed DModB) (algebraMap A B f) L))) :=
      UB.map_isZero hB
    have hAforget :
        IsZero
          (UA.obj
            ((HA i).obj
              (CategoryTheory.DerivedCategory.localizationAwayT
                (A := A) (inferInstance : MonoidalClosed DModA) f
                (((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).obj L)))) :=
      (localizationAwayT_homology_forget_iso (A := A) (B := B) (L := L) f i).isZero_iff.2
        hBforget
    exact
      isZero_of_forget_addCommGrp_obj
        ((HA i).obj
          (CategoryTheory.DerivedCategory.localizationAwayT
            (A := A) (inferInstance : MonoidalClosed DModA) f
            (((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).obj L)))
        hAforget

/-- Helper for Lemma 15.92.24: restricting scalars from `B` to `A` does not change the
zero test for the textbook object `T(-, f)`, once `f` is viewed in `B` through
`algebraMap A B`. -/
theorem isZero_localizationAwayT_restrictScalars_iff
    (L : DModB) (f : A) :
    IsZero
        (CategoryTheory.DerivedCategory.localizationAwayT
          (A := A) (inferInstance : MonoidalClosed DModA) f
          (((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).obj L)) ↔
      IsZero
        (CategoryTheory.DerivedCategory.localizationAwayT
          (A := B) (inferInstance : MonoidalClosed DModB) (algebraMap A B f) L) := by
  let TA : DModA :=
    CategoryTheory.DerivedCategory.localizationAwayT
      (A := A) (inferInstance : MonoidalClosed DModA) f
      (((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).obj L)
  let TB : DModB :=
    CategoryTheory.DerivedCategory.localizationAwayT
      (A := B) (inferInstance : MonoidalClosed DModB) (algebraMap A B f) L
  constructor
  · intro hTA
    -- Proof comment: vanishing of all `A`-side homology groups transfers degreewise to the
    -- `B`-side via the forgotten-homology comparison, and the canonical t-structure then detects
    -- the zero object.
    have hHomology :
        ∀ i : ℤ, IsZero ((HB i).obj TB) := by
      intro i
      have hTAi : IsZero ((HA i).obj TA) := by
        simpa [TA] using (HA i).map_isZero hTA
      simpa [TA, TB] using
        (homology_isZero_localizationAwayT_restrictScalars_iff
          (A := A) (B := B) (L := L) f i).1 hTAi
    have hLE : TB.IsLE 0 := by
      rw [DerivedCategory.isLE_iff]
      intro i hi
      exact hHomology i
    have hGE : TB.IsGE 1 := by
      rw [DerivedCategory.isGE_iff]
      intro i hi
      exact hHomology i
    letI : TB.IsLE 0 := hLE
    letI : TB.IsGE 1 := hGE
    exact t.isZero TB 0 1 (by omega)
  · intro hTB
    -- Proof comment: the converse uses the same degreewise transport in the opposite direction.
    have hHomology :
        ∀ i : ℤ, IsZero ((HA i).obj TA) := by
      intro i
      have hTBi : IsZero ((HB i).obj TB) := by
        simpa [TB] using (HB i).map_isZero hTB
      simpa [TA, TB] using
        (homology_isZero_localizationAwayT_restrictScalars_iff
          (A := A) (B := B) (L := L) f i).2 hTBi
    have hLE : TA.IsLE 0 := by
      rw [DerivedCategory.isLE_iff]
      intro i hi
      exact hHomology i
    have hGE : TA.IsGE 1 := by
      rw [DerivedCategory.isGE_iff]
      intro i hi
      exact hHomology i
    letI : TA.IsLE 0 := hLE
    letI : TA.IsGE 1 := hGE
    exact t.isZero TA 0 1 (by omega)

/-- Helper for Lemma 15.92.24: restricting scalars from `B` to `A` does not change the
localization-away vanishing condition attached to a single element `f ∈ A`, once `f` is viewed in
`B` through `algebraMap A B`. -/
theorem restrictScalars_localizationAwayDerivedHomVanishingCondition_iff
    (L : DModB) (f : A) :
    CategoryTheory.DerivedCategory.localizationAwayDerivedHomVanishingCondition
        (A := A) f (((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).obj L) ↔
      CategoryTheory.DerivedCategory.localizationAwayDerivedHomVanishingCondition
        (A := B) (algebraMap A B f) L := by
  -- Proof comment: rewrite both source-facing vanishing predicates as zero statements for the
  -- corresponding textbook objects `T(-, f)`.
  rw [CategoryTheory.DerivedCategory.localizationAwayDerivedHomVanishingCondition_iff
    (A := A) (H := (inferInstance : MonoidalClosed DModA)) f
    (((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).obj L)]
  rw [CategoryTheory.DerivedCategory.localizationAwayDerivedHomVanishingCondition_iff
    (A := B) (H := (inferInstance : MonoidalClosed DModB)) (algebraMap A B f) L]
  -- Proof comment: the remaining comparison is the source-faithful `T`-object zero test.
  exact isZero_localizationAwayT_restrictScalars_iff (A := A) (B := B) (L := L) f

/-- Helper for Lemma 15.92.24: after restricting scalars along `A → B`, the vanishing ideal is
the comap of the vanishing ideal over `B`. -/
theorem restrictScalars_localizationAwayDerivedHomVanishingIdeal_eq_comap
    (L : DModB) :
    (((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).obj L)
        .localizationAwayDerivedHomVanishingIdeal =
      Ideal.comap (algebraMap A B) L.localizationAwayDerivedHomVanishingIdeal := by
  ext f
  -- Proof comment: membership in either ideal is the pointwise vanishing condition for the same
  -- scalar, and the previous lemma identifies those two conditions.
  rw [Ideal.mem_comap]
  rw [CategoryTheory.DerivedCategory.mem_localizationAwayDerivedHomVanishingIdeal_iff]
  rw [CategoryTheory.DerivedCategory.mem_localizationAwayDerivedHomVanishingIdeal_iff]
  exact restrictScalars_localizationAwayDerivedHomVanishingCondition_iff (L := L) f

/- Domain-style sampling:
- primary domain: derived completeness in derived module categories under restriction of scalars;
- sampled owner-side declarations:
  `CategoryTheory.DerivedCategory.localizationAwayDerivedHomVanishingCondition`,
  `CategoryTheory.DerivedCategory.localizationAwayDerivedHomVanishingIdeal`,
  `CategoryTheory.DerivedCategory.IsDerivedCompleteWithRespectTo`,
  `(ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory`;
- best owner abstraction: the source-facing predicate
  `K.IsDerivedCompleteWithRespectTo I`, whose core/canonical owner is the ideal
  `K.localizationAwayDerivedHomVanishingIdeal`, together with the canonical derived
  restriction-of-scalars functor;
- primitive data: the object `L : D(B)`, the ideal `I : Ideal A`, and the algebra map `A → B`;
- derived API: this restriction/base-change equivalence for the source-facing completeness
  predicate.

Layer triage:
- `source-facing`: `isDerivedCompleteWithRespectTo_iff_restrictScalars`;
- `core/canonical`: `K.localizationAwayDerivedHomVanishingIdeal`;
- `bridge/view`: restriction of scalars along `(ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory`. -/

-- Proof sketch: by Definition `15.92.4`, derived completeness with respect to an ideal is the
-- vanishing of all morphisms from localization-derived categories `D(A_f)` or `D(B_g)` after
-- restriction of scalars. Using Lemma `15.92.2`, test membership in the relevant radical ideal by
-- the generators coming from `I`; the localization-away derived-Hom condition is computed in
-- abelian groups and is unchanged when `f ∈ A` is viewed in `B`, so the two vanishing conditions
-- are equivalent.
/-- Lemma 15.92.24: a derived `B`-complex lies in the inverse image of `D_{comp}(A, I)` under the
restriction functor `D(B) ⥤ D(A)` exactly when it is derived complete with respect to the
extended ideal `I B = I.map (algebraMap A B)`. -/
@[stacks 0924]
theorem isDerivedCompleteWithRespectTo_iff_restrictScalars
    (L : DModB) (I : Ideal A) :
    (((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).obj L).IsDerivedCompleteWithRespectTo I ↔
      L.IsDerivedCompleteWithRespectTo (I.map (algebraMap A B)) := by
  -- Proof comment: rewrite both derived-completeness predicates as ideal containments in the
  -- corresponding localization-away vanishing ideals.
  rw [isDerivedCompleteWithRespectTo_iff_le_localizationAwayDerivedHomVanishingIdeal]
  rw [isDerivedCompleteWithRespectTo_iff_le_localizationAwayDerivedHomVanishingIdeal]
  -- Proof comment: restriction of scalars pulls the vanishing ideal back along `A → B`.
  rw [restrictScalars_localizationAwayDerivedHomVanishingIdeal_eq_comap]
  -- Proof comment: the remaining statement is exactly the standard `map`/`comap` Galois
  -- connection for ideals.
  simpa using
    (Ideal.map_le_iff_le_comap :
      I.map (algebraMap A B) ≤ L.localizationAwayDerivedHomVanishingIdeal ↔
        I ≤ Ideal.comap (algebraMap A B)
          L.localizationAwayDerivedHomVanishingIdeal).symm

end

end CategoryTheory
