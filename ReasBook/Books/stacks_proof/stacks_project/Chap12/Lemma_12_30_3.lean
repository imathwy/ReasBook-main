import Mathlib
import StacksProject_2024.Chap04.Lemma_4_22_3
import StacksProject_2024.Chap12.Lemma_12_30_2

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

/-- Helper for Lemma 12.30.3: extending an essentially constant filtered cocone along an
isomorphism of vertices preserves essential constancy. -/
private theorem essentiallyConstantFilteredCocone_extend {M : I ⥤ A} {c : Cocone M}
    {X : A} (f : c.pt ⟶ X) [IsIso f] (hc : IsEssentiallyConstantFilteredCocone c) :
    IsEssentiallyConstantFilteredCocone (c.extend f) := by
  rw [isEssentiallyConstantFilteredCocone_iff] at hc ⊢
  rcases hc with ⟨i, s, hs, hfac⟩
  refine ⟨i, (asIso f).inv ≫ s, ?_, ?_⟩
  · -- Move the chosen section across the isomorphism on the cocone vertex.
    simp [Cocone.extend, hs, Category.assoc]
  · intro j
    rcases hfac j with ⟨k, ik, jk, hjk⟩
    refine ⟨k, ik, jk, ?_⟩
    simp [Cocone.extend, hjk, Category.assoc]

/-- Helper for Lemma 12.30.3: after transporting the canonical colimit cocone on `F ⊞ G` to the
vertex `colimit F ⊞ colimit G`, the left component leg is the canonical colimit map of `F`. -/
private theorem transported_biprod_colimit_left_leg (F G : I ⥤ A) [HasColimit (F ⊞ G)]
    [HasColimit F] [HasColimit G] (j : I) :
    ((biprod.inl : F ⟶ F ⊞ G).app j) ≫
        ((colimit.cocone (F ⊞ G)).extend (Limits.colimit_biprod_iso F G).hom).ι.app j =
      colimit.ι F j ≫ biprod.inl := by
  -- Compare the two projections to identify the map into the biproduct vertex.
  apply biprod.hom_ext
  · change
      ((biprod.inl : F ⟶ F ⊞ G).app j) ≫ colimit.ι (F ⊞ G) j ≫
          (Limits.colimit_biprod_iso F G).hom ≫ biprod.fst =
        colimit.ι F j
    simpa [Category.assoc] using Limits.colimit_biprod_iso_hom_fst (F := F) (G := G) j
  · change
      ((biprod.inl : F ⟶ F ⊞ G).app j) ≫ colimit.ι (F ⊞ G) j ≫
          (Limits.colimit_biprod_iso F G).hom ≫ biprod.snd =
        0
    simp [Category.assoc]

/-- Helper for Lemma 12.30.3: after transporting the canonical colimit cocone on `F ⊞ G` to the
vertex `colimit F ⊞ colimit G`, the right component leg is the canonical colimit map of `G`. -/
private theorem transported_biprod_colimit_right_leg (F G : I ⥤ A) [HasColimit (F ⊞ G)]
    [HasColimit F] [HasColimit G] (j : I) :
    ((biprod.inr : G ⟶ F ⊞ G).app j) ≫
        ((colimit.cocone (F ⊞ G)).extend (Limits.colimit_biprod_iso F G).hom).ι.app j =
      colimit.ι G j ≫ biprod.inr := by
  -- Compare the two projections to identify the map into the biproduct vertex.
  apply biprod.hom_ext
  · change
      ((biprod.inr : G ⟶ F ⊞ G).app j) ≫ colimit.ι (F ⊞ G) j ≫
          (Limits.colimit_biprod_iso F G).hom ≫ biprod.fst =
        0
    simp [Category.assoc]
  · change
      ((biprod.inr : G ⟶ F ⊞ G).app j) ≫ colimit.ι (F ⊞ G) j ≫
          (Limits.colimit_biprod_iso F G).hom ≫ biprod.snd =
        colimit.ι G j
    simpa [Category.assoc] using Limits.colimit_biprod_iso_hom_snd (F := F) (G := G) j

/-- Helper for Lemma 12.30.3: an essentially constant transported biproduct colimit cocone yields
an essentially constant canonical colimit cocone on the left summand. -/
private theorem essentiallyConstant_left_of_transport_biprod_colimit (F G : I ⥤ A)
    [HasColimit (F ⊞ G)] [HasColimit F] [HasColimit G]
    (ht :
      IsEssentiallyConstantFilteredCocone
        ((colimit.cocone (F ⊞ G)).extend (Limits.colimit_biprod_iso F G).hom)) :
    IsEssentiallyConstantFilteredCocone (colimit.cocone F) := by
  rw [isEssentiallyConstantFilteredCocone_iff] at ht ⊢
  rcases ht with ⟨i, s, hs, hfac⟩
  refine ⟨i, biprod.inl ≫ s ≫ ((biprod.fst : F ⊞ G ⟶ F).app i), ?_, ?_⟩
  · -- Project the split identity to the left summand.
    calc
      biprod.inl ≫ s ≫ ((biprod.fst : F ⊞ G ⟶ F).app i) ≫ colimit.ι F i =
          biprod.inl ≫ s ≫
            ((colimit.cocone (F ⊞ G)).extend (Limits.colimit_biprod_iso F G).hom).ι.app i ≫
              biprod.fst := by
            simpa [Cocone.extend, Category.assoc] using congrArg
              (fun f ↦ biprod.inl ≫ s ≫ f)
              ((Limits.colimit_biprod_iso_hom_fst (F := F) (G := G) i).symm)
      _ = biprod.inl ≫ biprod.fst := by
            simpa [Category.assoc] using congrArg (fun f ↦ biprod.inl ≫ f ≫ biprod.fst) hs
      _ = 𝟙 (colimit F) := biprod.inl_fst
  · intro j
    rcases hfac j with ⟨k, ik, jk, hjk⟩
    refine ⟨k, ik, jk, ?_⟩
    have hfst :
        (F ⊞ G).map ik ≫ ((biprod.fst : F ⊞ G ⟶ F).app k) =
          ((biprod.fst : F ⊞ G ⟶ F).app i) ≫ F.map ik := by
      simpa using (NatTrans.naturality (η := (biprod.fst : F ⊞ G ⟶ F)) ik)
    -- Precompose the factorization in `F ⊞ G` with `biprod.inl` and postcompose with `biprod.fst`.
    calc
      F.map jk =
          ((biprod.inl : F ⟶ F ⊞ G).app j) ≫ (F ⊞ G).map jk ≫
            ((biprod.fst : F ⊞ G ⟶ F).app k) := by
          simp [Category.assoc]
      _ =
          ((biprod.inl : F ⟶ F ⊞ G).app j) ≫
            ((colimit.cocone (F ⊞ G)).extend (Limits.colimit_biprod_iso F G).hom).ι.app j ≫ s ≫
              (F ⊞ G).map ik ≫ ((biprod.fst : F ⊞ G ⟶ F).app k) := by
          simpa [Category.assoc] using congrArg
            (fun f ↦ ((biprod.inl : F ⟶ F ⊞ G).app j) ≫ f ≫
              ((biprod.fst : F ⊞ G ⟶ F).app k)) hjk
      _ = colimit.ι F j ≫ biprod.inl ≫ s ≫ ((biprod.fst : F ⊞ G ⟶ F).app i) ≫ F.map ik := by
          rw [transported_biprod_colimit_left_leg (F := F) (G := G) j]
          rw [Category.assoc, Category.assoc, hfst]
          simp [Category.assoc]
      _ = colimit.ι F j ≫ (biprod.inl ≫ s ≫ ((biprod.fst : F ⊞ G ⟶ F).app i)) ≫ F.map ik := by
          simp [Category.assoc]

/-- Helper for Lemma 12.30.3: an essentially constant transported biproduct colimit cocone yields
an essentially constant canonical colimit cocone on the right summand. -/
private theorem essentiallyConstant_right_of_transport_biprod_colimit (F G : I ⥤ A)
    [HasColimit (F ⊞ G)] [HasColimit F] [HasColimit G]
    (ht :
      IsEssentiallyConstantFilteredCocone
        ((colimit.cocone (F ⊞ G)).extend (Limits.colimit_biprod_iso F G).hom)) :
    IsEssentiallyConstantFilteredCocone (colimit.cocone G) := by
  rw [isEssentiallyConstantFilteredCocone_iff] at ht ⊢
  rcases ht with ⟨i, s, hs, hfac⟩
  refine ⟨i, biprod.inr ≫ s ≫ ((biprod.snd : F ⊞ G ⟶ G).app i), ?_, ?_⟩
  · -- Project the split identity to the right summand.
    calc
      biprod.inr ≫ s ≫ ((biprod.snd : F ⊞ G ⟶ G).app i) ≫ colimit.ι G i =
          biprod.inr ≫ s ≫
            ((colimit.cocone (F ⊞ G)).extend (Limits.colimit_biprod_iso F G).hom).ι.app i ≫
              biprod.snd := by
            simpa [Cocone.extend, Category.assoc] using congrArg
              (fun f ↦ biprod.inr ≫ s ≫ f)
              ((Limits.colimit_biprod_iso_hom_snd (F := F) (G := G) i).symm)
      _ = biprod.inr ≫ biprod.snd := by
            simpa [Category.assoc] using congrArg (fun f ↦ biprod.inr ≫ f ≫ biprod.snd) hs
      _ = 𝟙 (colimit G) := biprod.inr_snd
  · intro j
    rcases hfac j with ⟨k, ik, jk, hjk⟩
    refine ⟨k, ik, jk, ?_⟩
    have hsnd :
        (F ⊞ G).map ik ≫ ((biprod.snd : F ⊞ G ⟶ G).app k) =
          ((biprod.snd : F ⊞ G ⟶ G).app i) ≫ G.map ik := by
      simpa using (NatTrans.naturality (η := (biprod.snd : F ⊞ G ⟶ G)) ik)
    -- Precompose the factorization in `F ⊞ G` with `biprod.inr` and postcompose with `biprod.snd`.
    calc
      G.map jk =
          ((biprod.inr : G ⟶ F ⊞ G).app j) ≫ (F ⊞ G).map jk ≫
            ((biprod.snd : F ⊞ G ⟶ G).app k) := by
          simp [Category.assoc]
      _ =
          ((biprod.inr : G ⟶ F ⊞ G).app j) ≫
            ((colimit.cocone (F ⊞ G)).extend (Limits.colimit_biprod_iso F G).hom).ι.app j ≫ s ≫
              (F ⊞ G).map ik ≫ ((biprod.snd : F ⊞ G ⟶ G).app k) := by
          simpa [Category.assoc] using congrArg
            (fun f ↦ ((biprod.inr : G ⟶ F ⊞ G).app j) ≫ f ≫
              ((biprod.snd : F ⊞ G ⟶ G).app k)) hjk
      _ = colimit.ι G j ≫ biprod.inr ≫ s ≫ ((biprod.snd : F ⊞ G ⟶ G).app i) ≫ G.map ik := by
          rw [transported_biprod_colimit_right_leg (F := F) (G := G) j]
          rw [Category.assoc, Category.assoc, hsnd]
          simp [Category.assoc]
      _ = colimit.ι G j ≫ (biprod.inr ≫ s ≫ ((biprod.snd : F ⊞ G ⟶ G).app i)) ≫ G.map ik := by
          simp [Category.assoc]

/-- Helper for Lemma 12.30.3: the componentwise biproduct legs at a single stage. -/
private def biprod_filtered_cocone_ι_app {F G : I ⥤ A} (cF : Cocone F) (cG : Cocone G)
    (j : I) : (F ⊞ G).obj j ⟶ cF.pt ⊞ cG.pt :=
  biprod.lift
    (((biprod.fst : F ⊞ G ⟶ F).app j) ≫ cF.ι.app j)
    (((biprod.snd : F ⊞ G ⟶ G).app j) ≫ cG.ι.app j)

/-- Helper for Lemma 12.30.3: the componentwise biproduct legs satisfy cocone naturality. -/
private theorem biprod_filtered_cocone_ι_naturality {F G : I ⥤ A} (cF : Cocone F) (cG : Cocone G)
    {i j : I} (f : i ⟶ j) :
    (F ⊞ G).map f ≫ biprod_filtered_cocone_ι_app cF cG j =
      biprod_filtered_cocone_ι_app cF cG i ≫ ((Functor.const I).obj (cF.pt ⊞ cG.pt)).map f := by
  -- Check naturality after postcomposing with the target projections of the biproduct.
  apply biprod.hom_ext
  · simp [biprod_filtered_cocone_ι_app, Category.assoc]
  · simp [biprod_filtered_cocone_ι_app, Category.assoc]

/-- Helper for Lemma 12.30.3: the pointwise biproduct of two cocones. -/
private noncomputable def biprod_filtered_cocone {F G : I ⥤ A} (cF : Cocone F) (cG : Cocone G) :
    Cocone (F ⊞ G) where
  pt := cF.pt ⊞ cG.pt
  ι :=
    { app := fun j ↦ biprod_filtered_cocone_ι_app cF cG j
      naturality := fun _ _ f ↦ biprod_filtered_cocone_ι_naturality cF cG f }

/-- Helper for Lemma 12.30.3: the left domain injection of the biproduct diagram factors through
the corresponding left cocone leg. -/
private theorem biprod_filtered_cocone_inl {F G : I ⥤ A} (cF : Cocone F) (cG : Cocone G) (j : I) :
    ((biprod.inl : F ⟶ F ⊞ G).app j) ≫ (biprod_filtered_cocone cF cG).ι.app j =
      cF.ι.app j ≫ biprod.inl := by
  -- This is the defining left component of the explicit biproduct cocone.
  apply biprod.hom_ext
  · simp [biprod_filtered_cocone, biprod_filtered_cocone_ι_app, Category.assoc]
  · simp [biprod_filtered_cocone, biprod_filtered_cocone_ι_app, Category.assoc]

/-- Helper for Lemma 12.30.3: the right domain injection of the biproduct diagram factors through
the corresponding right cocone leg. -/
private theorem biprod_filtered_cocone_inr {F G : I ⥤ A} (cF : Cocone F) (cG : Cocone G) (j : I) :
    ((biprod.inr : G ⟶ F ⊞ G).app j) ≫ (biprod_filtered_cocone cF cG).ι.app j =
      cG.ι.app j ≫ biprod.inr := by
  -- This is the defining right component of the explicit biproduct cocone.
  apply biprod.hom_ext
  · simp [biprod_filtered_cocone, biprod_filtered_cocone_ι_app, Category.assoc]
  · simp [biprod_filtered_cocone, biprod_filtered_cocone_ι_app, Category.assoc]

/-- Helper for Lemma 12.30.3: after moving the distinguished stage of an essentially constant
filtered cocone forward along `δ`, the eventual factorization data can be rewritten using the new
stage. -/
private theorem synchronize_component_factorization {H : I ⥤ A} {c : Cocone H}
    {i₀ i : I} {s : c.pt ⟶ H.obj i₀} (δ : i₀ ⟶ i)
    (hfac : ∀ j : I, ∃ (k : I) (ik : i₀ ⟶ k) (jk : j ⟶ k),
      H.map jk = c.ι.app j ≫ s ≫ H.map ik)
    (j : I) :
    ∃ (k : I) (ik : i ⟶ k) (jk : j ⟶ k),
      H.map jk = c.ι.app j ≫ s ≫ H.map δ ≫ H.map ik := by
  rcases hfac j with ⟨k₀, ik₀, jk₀, hjk₀⟩
  let m := IsFiltered.max i k₀
  let p : i ⟶ m := IsFiltered.leftToMax i k₀
  let q : k₀ ⟶ m := IsFiltered.rightToMax i k₀
  let k := IsFiltered.coeq (δ ≫ p) (ik₀ ≫ q)
  let t : m ⟶ k := IsFiltered.coeqHom (δ ≫ p) (ik₀ ≫ q)
  refine ⟨k, p ≫ t, jk₀ ≫ q ≫ t, ?_⟩
  have hδ : δ ≫ p ≫ t = ik₀ ≫ q ≫ t := by
    simpa [Category.assoc] using (IsFiltered.coeq_condition (δ ≫ p) (ik₀ ≫ q))
  -- Push the old factorization to a common successor and equalize the two maps out of `i₀`.
  calc
    H.map (jk₀ ≫ q ≫ t) = H.map jk₀ ≫ H.map q ≫ H.map t := by
      simp [Functor.map_comp, Category.assoc]
    _ = c.ι.app j ≫ s ≫ H.map ik₀ ≫ H.map q ≫ H.map t := by
      simpa [Functor.map_comp, Category.assoc] using congrArg
        (fun f ↦ f ≫ H.map q ≫ H.map t) hjk₀
    _ = c.ι.app j ≫ s ≫ H.map (ik₀ ≫ q ≫ t) := by
      simp [Functor.map_comp, Category.assoc]
    _ = c.ι.app j ≫ s ≫ H.map (δ ≫ p ≫ t) := by
      simpa using congrArg (fun f ↦ c.ι.app j ≫ s ≫ H.map f) hδ.symm
    _ = c.ι.app j ≫ s ≫ H.map δ ≫ H.map (p ≫ t) := by
      simp [Functor.map_comp, Category.assoc]

/-- Helper for Lemma 12.30.3: the left and right eventual factorization data can be synchronized
to one common target stage for the explicit biproduct cocone. -/
private theorem synchronize_biprod_factorizations {F G : I ⥤ A}
    {cF : Cocone F} {cG : Cocone G} {iF iG i : I}
    {sF : cF.pt ⟶ F.obj iF} {sG : cG.pt ⟶ G.obj iG}
    (δF : iF ⟶ i) (δG : iG ⟶ i)
    (hfacF : ∀ j : I, ∃ (k : I) (ik : iF ⟶ k) (jk : j ⟶ k),
      F.map jk = cF.ι.app j ≫ sF ≫ F.map ik)
    (hfacG : ∀ j : I, ∃ (k : I) (ik : iG ⟶ k) (jk : j ⟶ k),
      G.map jk = cG.ι.app j ≫ sG ≫ G.map ik)
    (j : I) :
    ∃ (k : I) (ik : i ⟶ k) (jk : j ⟶ k),
      F.map jk = cF.ι.app j ≫ sF ≫ F.map δF ≫ F.map ik ∧
        G.map jk = cG.ι.app j ≫ sG ≫ G.map δG ≫ G.map ik := by
  rcases synchronize_component_factorization (δ := δF) hfacF j with ⟨kF, ikF, jkF, hF⟩
  rcases synchronize_component_factorization (δ := δG) hfacG j with ⟨kG, ikG, jkG, hG⟩
  let m := IsFiltered.max kF kG
  let u : kF ⟶ m := IsFiltered.leftToMax kF kG
  let v : kG ⟶ m := IsFiltered.rightToMax kF kG
  let n := IsFiltered.coeq (jkF ≫ u) (jkG ≫ v)
  let t : m ⟶ n := IsFiltered.coeqHom (jkF ≫ u) (jkG ≫ v)
  let k := IsFiltered.coeq (ikF ≫ u ≫ t) (ikG ≫ v ≫ t)
  let w : n ⟶ k := IsFiltered.coeqHom (ikF ≫ u ≫ t) (ikG ≫ v ≫ t)
  refine ⟨k, ikF ≫ u ≫ t ≫ w, jkF ≫ u ≫ t ≫ w, ?_, ?_⟩
  have hj :
      jkF ≫ u ≫ t = jkG ≫ v ≫ t := by
    simpa [Category.assoc] using (IsFiltered.coeq_condition (jkF ≫ u) (jkG ≫ v))
  have hi :
      ikF ≫ u ≫ t ≫ w = ikG ≫ v ≫ t ≫ w := by
    simpa [Category.assoc] using
      (IsFiltered.coeq_condition (ikF ≫ u ≫ t) (ikG ≫ v ≫ t))
  constructor
  · -- Postcompose the left factorization with the synchronizing maps.
    simpa [Functor.map_comp, Category.assoc] using congrArg
      (fun f ↦ f ≫ F.map (u ≫ t ≫ w)) hF
  · have hG' :
        G.map (jkG ≫ v ≫ t ≫ w) =
          cG.ι.app j ≫ sG ≫ G.map δG ≫ G.map (ikG ≫ v ≫ t ≫ w) := by
      simpa [Functor.map_comp, Category.assoc] using congrArg
        (fun f ↦ f ≫ G.map (v ≫ t ≫ w)) hG
    have hj' : jkF ≫ u ≫ t ≫ w = jkG ≫ v ≫ t ≫ w := by
      simpa [Category.assoc] using congrArg (fun f ↦ f ≫ w) hj
    -- Rewrite the right factorization so that it uses the same `jk` and `ik` as the left one.
    calc
      G.map (jkF ≫ u ≫ t ≫ w) = G.map (jkG ≫ v ≫ t ≫ w) := by
        simpa using congrArg (fun f ↦ G.map f) hj'
      _ = cG.ι.app j ≫ sG ≫ G.map δG ≫ G.map (ikG ≫ v ≫ t ≫ w) := hG'
      _ = cG.ι.app j ≫ sG ≫ G.map δG ≫ G.map (ikF ≫ u ≫ t ≫ w) := by
        simpa using congrArg (fun f ↦ cG.ι.app j ≫ sG ≫ G.map δG ≫ G.map f) hi.symm

/-- Helper for Lemma 12.30.3: the pointwise biproduct of two essentially constant filtered
cocones is essentially constant. -/
private theorem essentiallyConstantFilteredCocone_biprod {F G : I ⥤ A}
    (cF : Cocone F) (cG : Cocone G)
    (hcF : IsEssentiallyConstantFilteredCocone cF)
    (hcG : IsEssentiallyConstantFilteredCocone cG) :
    IsEssentiallyConstantFilteredCocone (biprod_filtered_cocone cF cG) := by
  rw [isEssentiallyConstantFilteredCocone_iff] at hcF hcG ⊢
  rcases hcF with ⟨iF, sF, hsF, hfacF⟩
  rcases hcG with ⟨iG, sG, hsG, hfacG⟩
  let i := IsFiltered.max iF iG
  let δF : iF ⟶ i := IsFiltered.leftToMax iF iG
  let δG : iG ⟶ i := IsFiltered.rightToMax iF iG
  refine ⟨i,
    biprod.desc
      ((sF ≫ F.map δF) ≫ ((biprod.inl : F ⟶ F ⊞ G).app i))
      ((sG ≫ G.map δG) ≫ ((biprod.inr : G ⟶ F ⊞ G).app i)),
    ?_, ?_⟩
  · -- Check the section identity one component at a time.
    apply biprod.hom_ext'
    · have hδF :
          (sF ≫ F.map δF) ≫ cF.ι.app i = 𝟙 cF.pt := by
        calc
          (sF ≫ F.map δF) ≫ cF.ι.app i = sF ≫ (F.map δF ≫ cF.ι.app i) := by
            simp [Category.assoc]
          _ = sF ≫ cF.ι.app iF := by
            rw [cF.w δF]
          _ = 𝟙 cF.pt := hsF
    · calc
        biprod.inl ≫
            biprod.desc
              ((sF ≫ F.map δF) ≫ ((biprod.inl : F ⟶ F ⊞ G).app i))
              ((sG ≫ G.map δG) ≫ ((biprod.inr : G ⟶ F ⊞ G).app i)) ≫
            (biprod_filtered_cocone cF cG).ι.app i =
            (sF ≫ F.map δF) ≫ ((biprod.inl : F ⟶ F ⊞ G).app i) ≫
              (biprod_filtered_cocone cF cG).ι.app i := by
              simp [Category.assoc]
        _ = (sF ≫ F.map δF) ≫ cF.ι.app i ≫ biprod.inl := by
              rw [biprod_filtered_cocone_inl (cF := cF) (cG := cG) i]
              simp [Category.assoc]
        _ = biprod.inl := by
              simpa [hδF, Category.assoc]
    · have hδG :
          (sG ≫ G.map δG) ≫ cG.ι.app i = 𝟙 cG.pt := by
        calc
          (sG ≫ G.map δG) ≫ cG.ι.app i = sG ≫ (G.map δG ≫ cG.ι.app i) := by
            simp [Category.assoc]
          _ = sG ≫ cG.ι.app iG := by
            rw [cG.w δG]
          _ = 𝟙 cG.pt := hsG
    · calc
        biprod.inr ≫
            biprod.desc
              ((sF ≫ F.map δF) ≫ ((biprod.inl : F ⟶ F ⊞ G).app i))
              ((sG ≫ G.map δG) ≫ ((biprod.inr : G ⟶ F ⊞ G).app i)) ≫
            (biprod_filtered_cocone cF cG).ι.app i =
            (sG ≫ G.map δG) ≫ ((biprod.inr : G ⟶ F ⊞ G).app i) ≫
              (biprod_filtered_cocone cF cG).ι.app i := by
              simp [Category.assoc]
        _ = (sG ≫ G.map δG) ≫ cG.ι.app i ≫ biprod.inr := by
              rw [biprod_filtered_cocone_inr (cF := cF) (cG := cG) i]
              simp [Category.assoc]
        _ = biprod.inr := by
              simpa [hδG, Category.assoc]
  · intro j
    rcases synchronize_biprod_factorizations (δF := δF) (δG := δG) hfacF hfacG j with
      ⟨k, ik, jk, hF, hG⟩
    refine ⟨k, ik, jk, ?_⟩
    -- Compare both sides after precomposing with the domain injections of the biproduct.
    apply biprod.hom_ext'
    · calc
        ((biprod.inl : F ⟶ F ⊞ G).app j) ≫ (F ⊞ G).map jk =
            F.map jk ≫ ((biprod.inl : F ⟶ F ⊞ G).app k) := by
              simp [Category.assoc]
        _ = cF.ι.app j ≫ sF ≫ F.map δF ≫ F.map ik ≫ ((biprod.inl : F ⟶ F ⊞ G).app k) := by
              simpa [Category.assoc] using congrArg
                (fun f ↦ f ≫ ((biprod.inl : F ⟶ F ⊞ G).app k)) hF
        _ = ((biprod.inl : F ⟶ F ⊞ G).app j) ≫ (biprod_filtered_cocone cF cG).ι.app j ≫
              biprod.desc
                ((sF ≫ F.map δF) ≫ ((biprod.inl : F ⟶ F ⊞ G).app i))
                ((sG ≫ G.map δG) ≫ ((biprod.inr : G ⟶ F ⊞ G).app i)) ≫
                (F ⊞ G).map ik := by
              rw [biprod_filtered_cocone_inl (cF := cF) (cG := cG) j]
              simp [Category.assoc]
    · calc
        ((biprod.inr : G ⟶ F ⊞ G).app j) ≫ (F ⊞ G).map jk =
            G.map jk ≫ ((biprod.inr : G ⟶ F ⊞ G).app k) := by
              simp [Category.assoc]
        _ = cG.ι.app j ≫ sG ≫ G.map δG ≫ G.map ik ≫ ((biprod.inr : G ⟶ F ⊞ G).app k) := by
              simpa [Category.assoc] using congrArg
                (fun f ↦ f ≫ ((biprod.inr : G ⟶ F ⊞ G).app k)) hG
        _ = ((biprod.inr : G ⟶ F ⊞ G).app j) ≫ (biprod_filtered_cocone cF cG).ι.app j ≫
              biprod.desc
                ((sF ≫ F.map δF) ≫ ((biprod.inl : F ⟶ F ⊞ G).app i))
                ((sG ≫ G.map δG) ≫ ((biprod.inr : G ⟶ F ⊞ G).app i)) ≫
                (F ⊞ G).map ik := by
              rw [biprod_filtered_cocone_inr (cF := cF) (cG := cG) j]
              simp [Category.assoc]

/-- Lemma 12.30.3: in the canonical owner predicate
`IsEssentiallyConstantFilteredDiagram`, the pointwise direct-sum diagram `F ⊞ G` is essentially
constant if and only if both `F` and `G` are essentially constant. -/
@[stacks 0A2G]
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
    let t :
        Cocone (F ⊞ G) :=
      (colimit.cocone (F ⊞ G)).extend (Limits.colimit_biprod_iso F G).hom
    have ht : IsEssentiallyConstantFilteredCocone t := by
      -- The colimit comparison is an isomorphism, so the essential-constancy witness transports.
      have hc' : IsEssentiallyConstantFilteredCocone (colimit.cocone (F ⊞ G)) := by
        simpa using hc
      simpa [t] using essentiallyConstantFilteredCocone_extend
        (f := (Limits.colimit_biprod_iso F G).hom) hc'
    exact ⟨⟨colimit.cocone F, essentiallyConstant_left_of_transport_biprod_colimit F G ht⟩,
      ⟨colimit.cocone G, essentiallyConstant_right_of_transport_biprod_colimit F G ht⟩⟩
  · rintro ⟨hF, hG⟩
    obtain ⟨cF, hcF⟩ :=
      essentiallyConstantFilteredDiagram_exists_essentiallyConstant_colimitCocone F hF
    obtain ⟨cG, hcG⟩ :=
      essentiallyConstantFilteredDiagram_exists_essentiallyConstant_colimitCocone G hG
    -- Combine the two essentially constant colimit cocones into a cocone on the pointwise
    -- biproduct diagram `F ⊞ G`; filteredness supplies a common distinguished stage and a common
    -- eventual target for the componentwise factorization data.
    exact ⟨biprod_filtered_cocone cF.cocone cG.cocone,
      essentiallyConstantFilteredCocone_biprod cF.cocone cG.cocone hcF hcG⟩

end

end CategoryTheory
