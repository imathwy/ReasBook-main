import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import StacksProject_2024.Chap13.Definition_13_27_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

namespace CategoryTheory

universe w

open DerivedCategory
open DerivedCategory.TStructure
open Triangulated
open Abelian.Ext
open CategoryTheory.Pretriangulated
open scoped DerivedExt

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

local notation "H" => homologyFunctor 𝒜
local notation "single₀" => singleFunctor 𝒜 0

/- Domain-style sampling for Lemma 13.27.3:
- primary domain: morphisms in `D(𝒜)` controlled by the canonical `t`-structure and the
  cohomology functors `H^n`;
- sampled owner declarations:
  `DerivedCategory.IsLE`,
  `DerivedCategory.IsGE`,
  `CategoryTheory.Triangulated.TStructure.zero_of_isLE_of_isGE`,
  `Abelian.Ext.homEquiv`,
  `Abelian.Ext.homEquiv₀`;
- best owner abstraction: the boundedness hypotheses belong to the canonical owners `X.IsLE a`
  and `Y.IsGE b`; the degree-`b - a` comparison is a source-facing bridge from `Ext^(b - a)(X, Y)`
  to `Hom(H^a(X), H^b(Y))`; and the single-object degree-zero clause should reuse the chapter
  owner `Abelian.Ext.homEquiv₀`, reached from the derived-side notation through
  `Abelian.Ext.homEquiv`, rather than rebuilding that identification locally;
- primitive data: objects `X Y : D(𝒜)`, bounds `a b : ℤ`, and the owner hypotheses
  `X.IsLE a`, `Y.IsGE b`;
- derived API: vanishing below `b - a`, the canonical comparison map in degree `b - a`, and the
  single-object special case.

Source/core/bridge triage:
- `source-facing`: the vanishing and comparison statements for `Ext^n(X, Y)` and their
  single-object corollaries;
- `core/canonical`: `DerivedCategory.IsLE`, `DerivedCategory.IsGE`, and
  `CategoryTheory.Triangulated.TStructure.zero_of_isLE_of_isGE`;
- `bridge/view`: the degree-`b - a` comparison map `shiftedHomToHomologyMap` and the degree-zero
  transport from derived `Ext^0` to `Abelian.Ext B A 0`, followed by `Abelian.Ext.homEquiv₀`.
-/

/-- The canonical degree-`b - a` comparison map
`Ext^(b - a)(X, Y) → Hom(H^a(X), H^b(Y))`. -/
noncomputable def shiftedHomToHomologyMap
    (X Y : DerivedCategory 𝒜) (a b : ℤ) :
    Ext^(b - a)(X, Y) → ((H a).obj X ⟶ (H b).obj Y) :=
  fun f ↦ (H 0).shiftMap f a b (sub_add_cancel b a)

/-- Lemma 13.27.3 (1), vanishing clause: if `X` has no cohomology above degree `a` and `Y` has
no cohomology below degree `b`, then `Ext^n(X, Y)` vanishes for `n < b - a`. -/
theorem shiftedHom_subsingleton_of_lt_sub
    (X Y : DerivedCategory 𝒜) (a b n : ℤ) (hX : X.IsLE a) (hY : Y.IsGE b) (hn : n < b - a) :
    Subsingleton (Ext^n(X, Y)) := by
  letI := hX
  letI := hY
  have hshift : (Y⟦n⟧).IsGE (a + 1) := by
    have hbn : (Y⟦n⟧).IsGE (b - n) := by
      simpa using
        (TStructure.t.isGE_shift Y b n (b - n) (by omega) :
          TStructure.t.IsGE (Y⟦n⟧) (b - n))
    exact TStructure.t.isGE_of_ge (Y⟦n⟧) (a + 1) (b - n) (by omega)
  refine ⟨fun f g ↦ by
    rw [TStructure.t.zero_of_isLE_of_isGE f a (a + 1) (by omega) hX hshift,
      TStructure.t.zero_of_isLE_of_isGE g a (a + 1) (by omega) hX hshift]⟩

/- Lemma 13.27.3 (1), comparison clause: under the same hypotheses, the canonical degree
`b - a` comparison map is bijective. -/
/-- Helper for Lemma 13.27.3: an object of the derived category concentrated in degree `n` is the
single object on its degree-`n` homology. -/
private noncomputable def singleFunctor_iso_of_isGE_of_isLE
    (X : DerivedCategory 𝒜) (n : ℤ) [X.IsGE n] [X.IsLE n] :
    X ≅ (singleFunctor 𝒜 n).obj ((H n).obj X) := by
  classical
  -- Use the canonical single-degree model and then rewrite the chosen coefficient object to
  -- the actual degree-`n` homology of `X`.
  let hX := exists_iso_singleFunctor_obj_of_isGE_of_isLE X n
  let Y := Classical.choose hX
  let e : X ≅ (singleFunctor 𝒜 n).obj Y := Classical.choice (Classical.choose_spec hX)
  let eH : (H n).obj X ≅ Y :=
    (H n).mapIso e ≪≫ (singleFunctorCompHomologyFunctorIso 𝒜 n).app Y
  exact e ≪≫ (singleFunctor 𝒜 n).mapIso eH.symm

/-- Helper for Lemma 13.27.3: after identifying a concentrated object with its single-degree
model, applying `H^n` to that isomorphism recovers the canonical owner isomorphism
`singleFunctor ⋙ H^n ≅ 𝟭`. -/
private theorem singleFunctor_iso_of_isGE_of_isLE_homology
    (X : DerivedCategory 𝒜) (n : ℤ) [X.IsGE n] [X.IsLE n] :
    (H n).map (singleFunctor_iso_of_isGE_of_isLE X n).hom =
      ((singleFunctorCompHomologyFunctorIso 𝒜 n).app ((H n).obj X)).inv := by
  classical
  let hX := exists_iso_singleFunctor_obj_of_isGE_of_isLE X n
  let Y := Classical.choose hX
  let e : X ≅ (singleFunctor 𝒜 n).obj Y := Classical.choice (Classical.choose_spec hX)
  let eH : (H n).obj X ≅ Y :=
    (H n).mapIso e ≪≫ (singleFunctorCompHomologyFunctorIso 𝒜 n).app Y
  let α := singleFunctorCompHomologyFunctorIso 𝒜 n
  have hnat' :
      (H n).map ((singleFunctor 𝒜 n).map eH.inv) ≫ (α.app ((H n).obj X)).hom =
        (α.app Y).hom ≫ eH.inv := by
    refine (cancel_epi (α.app Y).inv).1 ?_
    simpa [Category.assoc] using
      (NatIso.naturality_1 α eH.inv).trans
        ((Iso.inv_hom_id_assoc (α.app Y) eH.inv).symm)
  have hcomp :
      (H n).map ((singleFunctor 𝒜 n).map eH.inv) =
        (α.app Y).hom ≫ eH.inv ≫ (α.app ((H n).obj X)).inv := by
    have hcomp' :
        (α.app Y).hom ≫ eH.inv ≫ (α.app ((H n).obj X)).inv ≫
          (α.app ((H n).obj X)).hom =
            (α.app Y).hom ≫ eH.inv := by
      simpa [Category.assoc] using
        congrArg (fun t ↦ (α.app Y).hom ≫ eH.inv ≫ t)
          (Iso.inv_hom_id (α.app ((H n).obj X)))
    exact (cancel_mono (α.app ((H n).obj X)).hom).1 <| by
      simpa [Category.assoc] using hnat'.trans hcomp'.symm
  dsimp [singleFunctor_iso_of_isGE_of_isLE]
  have hmap :
      (H n).map e.hom ≫ (H n).map ((singleFunctor 𝒜 n).map eH.inv) =
        (H n).map e.hom ≫ (α.app Y).hom ≫ eH.inv ≫ (α.app ((H n).obj X)).inv := by
    rw [hcomp]
    simp
  have hfinal :
      (H n).map e.hom ≫ (α.app Y).hom ≫ eH.inv ≫ (α.app ((H n).obj X)).inv =
        ((singleFunctorCompHomologyFunctorIso 𝒜 n).app ((H n).obj X)).inv := by
    simpa [eH, Category.assoc] using
      (Iso.hom_inv_id_assoc eH ((singleFunctorCompHomologyFunctorIso 𝒜 n).app
        ((H n).obj X)).inv)
  have hmain :
      (H n).map (singleFunctor_iso_of_isGE_of_isLE X n).hom =
        (H n).map e.hom ≫ (α.app Y).hom ≫ eH.inv ≫ (α.app ((H n).obj X)).inv := by
    have hmain₁ :
        (H n).map (singleFunctor_iso_of_isGE_of_isLE X n).hom =
          (H n).map e.hom ≫
            (H n).map ((singleFunctor 𝒜 n).map ((singleFunctorCompHomologyFunctorIso 𝒜 n).inv.app Y)) ≫
              (H n).map ((singleFunctor 𝒜 n).map ((H n).map e.inv)) := by
      simpa [singleFunctor_iso_of_isGE_of_isLE, e, Y, Functor.map_comp]
    have hmain₂ :
        (H n).map e.hom ≫
            (H n).map ((singleFunctor 𝒜 n).map ((singleFunctorCompHomologyFunctorIso 𝒜 n).inv.app Y)) ≫
              (H n).map ((singleFunctor 𝒜 n).map ((H n).map e.inv)) =
          (H n).map e.hom ≫ (α.app Y).hom ≫ eH.inv ≫ (α.app ((H n).obj X)).inv := by
      simpa [eH, Functor.map_comp, Category.assoc] using hmap
    exact hmain₁.trans hmain₂
  exact hmain.trans hfinal

/-- Helper for Lemma 13.27.3: on single-degree objects, the degree-`n` homology map detects
morphisms. -/
private theorem singleFunctor_map_ext
    {A B : 𝒜} {n : ℤ}
    {q₁ q₂ : (singleFunctor 𝒜 n).obj A ⟶ (singleFunctor 𝒜 n).obj B}
    (h : (H n).map q₁ = (H n).map q₂) :
    q₁ = q₂ := by
  let α := singleFunctorCompHomologyFunctorIso 𝒜 n
  let u₁ : A ⟶ B := (singleFunctor 𝒜 n).preimage q₁
  let u₂ : A ⟶ B := (singleFunctor 𝒜 n).preimage q₂
  have h₁ := NatIso.naturality_1 α u₁
  have h₂ := NatIso.naturality_1 α u₂
  have h₁' : (α.app A).inv ≫ (H n).map q₁ ≫ (α.app B).hom = u₁ := by
    simpa [u₁, Functor.comp_map, Functor.map_comp, (singleFunctor 𝒜 n).map_preimage q₁,
      Category.assoc] using h₁
  have h₂' : (α.app A).inv ≫ (H n).map q₂ ≫ (α.app B).hom = u₂ := by
    simpa [u₂, Functor.comp_map, Functor.map_comp, (singleFunctor 𝒜 n).map_preimage q₂,
      Category.assoc] using h₂
  have hu : u₁ = u₂ := by
    exact h₁'.symm.trans <| (by rw [h]; exact h₂')
  simpa [u₁, u₂] using congrArg ((singleFunctor 𝒜 n).map) hu

/-- Helper for Lemma 13.27.3: the map on degree-`a` homology induced by the lower truncation
projection `X ⟶ τ_{\ge a} X` is an isomorphism. -/
private theorem homology_map_truncGEπ_isIso
    (X : DerivedCategory 𝒜) (a : ℤ) :
    IsIso ((H a).map ((t.truncGEπ a).app X)) := by
  let T : Triangle (DerivedCategory 𝒜) := (t.triangleLTGE a).obj X
  have hT : T ∈ distTriang (DerivedCategory 𝒜) := by
    simpa [T] using t.triangleLTGE_distinguished a X
  have h₁ : T.obj₁.IsLE (a - 1) := by
    dsimp [T]
    infer_instance
  have hmor₁_zero : (H a).map T.mor₁ = 0 := by
    -- The discarded low-degree piece has zero degree-`a` homology.
    exact (isZero_of_isLE T.obj₁ (a - 1) a (by omega)).eq_of_src _ _
  have hδ_zero : HomologySequence.δ T a (a + 1) rfl = 0 := by
    -- The connecting morphism also lands in the same zero homology group.
    exact (isZero_of_isLE T.obj₁ (a - 1) (a + 1) (by omega)).eq_of_tgt _ _
  letI : Epi ((H a).map T.mor₂) :=
    (HomologySequence.epi_homologyMap_mor₂_iff T hT a (a + 1) rfl).2 hδ_zero
  letI : Mono ((H a).map T.mor₂) :=
    (HomologySequence.mono_homologyMap_mor₂_iff T hT a).2 hmor₁_zero
  simpa [T] using isIso_of_mono_of_epi ((H a).map T.mor₂)

/-- Helper for Lemma 13.27.3: the map on degree-`a` homology induced by the upper truncation
inclusion `τ_{\le a} Z ⟶ Z` is an isomorphism. -/
private theorem homology_map_truncLEι_isIso
    (Z : DerivedCategory 𝒜) (a : ℤ) :
    IsIso ((H a).map ((t.truncLEι a).app Z)) := by
  let T : Triangle (DerivedCategory 𝒜) := (t.triangleLEGT a).obj Z
  have hT : T ∈ distTriang (DerivedCategory 𝒜) := by
    simpa [T] using t.triangleLEGT_distinguished a Z
  have h₃ : T.obj₃.IsGE (a + 1) := by
    dsimp [T]
    infer_instance
  have hmor₂_zero : (H a).map T.mor₂ = 0 := by
    -- The discarded high-degree piece has zero degree-`a` homology.
    exact (isZero_of_isGE T.obj₃ (a + 1) a (by omega)).eq_of_tgt _ _
  have hδ_zero : HomologySequence.δ T (a - 1) a (by omega) = 0 := by
    -- The connecting morphism starts in another vanishing degree.
    exact (isZero_of_isGE T.obj₃ (a + 1) (a - 1) (by omega)).eq_of_src _ _
  letI : Epi ((H a).map T.mor₁) :=
    (HomologySequence.epi_homologyMap_mor₁_iff T hT a).2 hmor₂_zero
  letI : Mono ((H a).map T.mor₁) :=
    (HomologySequence.mono_homologyMap_mor₁_iff T hT (a - 1) a (by omega)).2 hδ_zero
  simpa [T] using isIso_of_mono_of_epi ((H a).map T.mor₁)

/-- Helper for Lemma 13.27.3: the shifted comparison map is the degree-`a` homology map followed
by the canonical shift isomorphism. -/
private theorem shiftedHomToHomologyMap_eq
    (X Y : DerivedCategory 𝒜) (a b : ℤ) (f : X ⟶ Y⟦b - a⟧) :
    shiftedHomToHomologyMap X Y a b f =
      (H a).map f ≫ (((H 0).shiftIso (b - a) a b (sub_add_cancel b a)).app Y).hom := by
  rfl

/-- Helper for Lemma 13.27.3: on objects concentrated in degree `n`, applying `H^n` to a
morphism is bijective. -/
private theorem homology_map_bijective_of_isGE_of_isLE
    (X Y : DerivedCategory 𝒜) (n : ℤ) [X.IsGE n] [X.IsLE n] [Y.IsGE n] [Y.IsLE n] :
    Function.Bijective (fun f : X ⟶ Y ↦ (H n).map f) := by
  let eX := singleFunctor_iso_of_isGE_of_isLE X n
  let eY := singleFunctor_iso_of_isGE_of_isLE Y n
  constructor
  · intro f g hfg
    apply (cancel_mono eY.hom).1
    apply (cancel_epi eX.inv).1
    apply singleFunctor_map_ext (n := n)
    simpa [Functor.map_comp, Category.assoc, hfg]
  · intro u
    let α := singleFunctorCompHomologyFunctorIso 𝒜 n
    let q :
        (singleFunctor 𝒜 n).obj ((H n).obj X) ⟶
          (singleFunctor 𝒜 n).obj ((H n).obj Y) :=
      (singleFunctor 𝒜 n).map u
    have hq' :
        (H n).map q ≫ (α.app ((H n).obj Y)).hom =
          (α.app ((H n).obj X)).hom ≫ u := by
      refine (cancel_epi (α.app ((H n).obj X)).inv).1 ?_
      simpa [q, Functor.comp_map, Functor.map_comp, Category.assoc] using
        (NatIso.naturality_1 α u).trans
          ((Iso.inv_hom_id_assoc (α.app ((H n).obj X)) u).symm)
    refine ⟨eX.hom ≫ q ≫ eY.inv, ?_⟩
    have hq :
        (H n).map q =
          (α.app ((H n).obj X)).hom ≫ u ≫ (α.app ((H n).obj Y)).inv := by
      have hq'' :
          (α.app ((H n).obj X)).hom ≫ u ≫ (α.app ((H n).obj Y)).inv ≫
            (α.app ((H n).obj Y)).hom =
              (α.app ((H n).obj X)).hom ≫ u := by
        simpa [Category.assoc] using
          congrArg (fun t ↦ (α.app ((H n).obj X)).hom ≫ u ≫ t)
            (Iso.inv_hom_id (α.app ((H n).obj Y)))
      exact (cancel_mono (α.app ((H n).obj Y)).hom).1 <| by
        simpa [Category.assoc] using hq'.trans hq''.symm
    have hYinv :
        (H n).map eY.inv = (α.app ((H n).obj Y)).hom := by
      have hIso :
          (H n).mapIso eY = (α.app ((H n).obj Y)).symm := by
        ext
        simpa using singleFunctor_iso_of_isGE_of_isLE_homology (X := Y) (n := n)
      exact congrArg Iso.inv hIso
    have hXhom :
        (H n).map eX.hom = (α.app ((H n).obj X)).inv := by
      simpa [eX] using singleFunctor_iso_of_isGE_of_isLE_homology (X := X) (n := n)
    have hcalc :
        (H n).map (eX.hom ≫ q ≫ eY.inv) =
          (α.app ((H n).obj X)).inv ≫
            ((α.app ((H n).obj X)).hom ≫ u ≫ (α.app ((H n).obj Y)).inv) ≫
            (α.app ((H n).obj Y)).hom := by
      simp [Functor.map_comp, Category.assoc, hXhom, hq, hYinv]
    have hreduce :
        (α.app ((H n).obj X)).inv ≫
            ((α.app ((H n).obj X)).hom ≫ u ≫ (α.app ((H n).obj Y)).inv) ≫
            (α.app ((H n).obj Y)).hom = u := by
      have hx :
          (α.app ((H n).obj X)).inv ≫ (α.app ((H n).obj X)).hom ≫
              (u ≫ (α.app ((H n).obj Y)).inv ≫ (α.app ((H n).obj Y)).hom) =
            u ≫ (α.app ((H n).obj Y)).inv ≫ (α.app ((H n).obj Y)).hom := by
        simpa [Category.assoc] using
          congrArg (fun t ↦ t ≫ (u ≫ (α.app ((H n).obj Y)).inv ≫ (α.app ((H n).obj Y)).hom))
            (Iso.inv_hom_id (α.app ((H n).obj X)))
      have hy :
          u ≫ (α.app ((H n).obj Y)).inv ≫ (α.app ((H n).obj Y)).hom = u := by
        simpa [Category.assoc] using
          congrArg (fun t ↦ u ≫ t) (Iso.inv_hom_id (α.app ((H n).obj Y)))
      simpa [Category.assoc] using hx.trans hy
    exact hcalc.trans hreduce

theorem shiftedHomToHomologyMap_bijective
    (X Y : DerivedCategory 𝒜) (a b : ℤ) (hX : X.IsLE a) (hY : Y.IsGE b) :
    Function.Bijective (shiftedHomToHomologyMap X Y a b) := by
  let Z : DerivedCategory 𝒜 := Y⟦b - a⟧
  have hZ : Z.IsGE a := by
    simpa [Z] using
      (TStructure.t.isGE_shift Y b (b - a) a (by omega) :
        TStructure.t.IsGE (Y⟦b - a⟧) a)
  letI : Z.IsGE a := hZ
  letI : ((t.truncGE a).obj X).IsLE a := by
    infer_instance
  letI : ((t.truncLE a).obj Z).IsGE a := by
    infer_instance
  let eπ : (H a).obj X ≅ (H a).obj ((t.truncGE a).obj X) :=
    @asIso _ _ _ _ ((H a).map ((t.truncGEπ a).app X)) (homology_map_truncGEπ_isIso X a)
  let eι : (H a).obj ((t.truncLE a).obj Z) ≅ (H a).obj Z :=
    @asIso _ _ _ _ ((H a).map ((t.truncLEι a).app Z)) (homology_map_truncLEι_isIso Z a)
  let s : (H a).obj Z ≅ (H b).obj Y :=
    ((H 0).shiftIso (b - a) a b (sub_add_cancel b a)).app Y
  constructor
  · intro f g hfg
    let f' : (t.truncGE a).obj X ⟶ (t.truncLE a).obj Z :=
      t.liftTruncLE (t.descTruncGE f a) a
    let g' : (t.truncGE a).obj X ⟶ (t.truncLE a).obj Z :=
      t.liftTruncLE (t.descTruncGE g a) a
    have hshift :
        (H a).map f = (H a).map g := by
      have hshift' :
          (H a).map f ≫ s.hom = (H a).map g ≫ s.hom := by
        simpa [shiftedHomToHomologyMap_eq, s, Category.assoc] using hfg
      exact (cancel_mono s.hom).1 hshift'
    have hf_lift : f' ≫ (t.truncLEι a).app Z = t.descTruncGE f a := by
      simpa [f'] using t.liftTruncLE_ι (t.descTruncGE f a) a
    have hfcomp : (t.truncGEπ a).app X ≫ f' ≫ (t.truncLEι a).app Z = f := by
      have hcomp' :
          (t.truncGEπ a).app X ≫ f' ≫ (t.truncLEι a).app Z =
            (t.truncGEπ a).app X ≫ t.descTruncGE f a := by
        simpa [Category.assoc] using congrArg
          (fun k ↦ (t.truncGEπ a).app X ≫ k) hf_lift
      exact hcomp'.trans (t.π_descTruncGE f a)
    have hg_lift : g' ≫ (t.truncLEι a).app Z = t.descTruncGE g a := by
      simpa [g'] using t.liftTruncLE_ι (t.descTruncGE g a) a
    have hgcomp : (t.truncGEπ a).app X ≫ g' ≫ (t.truncLEι a).app Z = g := by
      have hcomp' :
          (t.truncGEπ a).app X ≫ g' ≫ (t.truncLEι a).app Z =
            (t.truncGEπ a).app X ≫ t.descTruncGE g a := by
        simpa [Category.assoc] using congrArg
          (fun k ↦ (t.truncGEπ a).app X ≫ k) hg_lift
      exact hcomp'.trans (t.π_descTruncGE g a)
    have htrunc : (H a).map f' = (H a).map g' := by
      have htrunc' :
          eπ.hom ≫ (H a).map f' ≫ eι.hom =
            eπ.hom ≫ (H a).map g' ≫ eι.hom := by
        calc
          eπ.hom ≫ (H a).map f' ≫ eι.hom = (H a).map f := by
            simpa [eπ, eι, Functor.map_comp, Category.assoc] using congrArg ((H a).map) hfcomp
          _ = (H a).map g := hshift
          _ = eπ.hom ≫ (H a).map g' ≫ eι.hom := by
            symm
            simpa [eπ, eι, Functor.map_comp, Category.assoc] using congrArg ((H a).map) hgcomp
      exact (cancel_mono eι.hom).1 ((cancel_epi eπ.hom).1 htrunc')
    have hfg' :
        f' = g' := (homology_map_bijective_of_isGE_of_isLE
          ((t.truncGE a).obj X) ((t.truncLE a).obj Z) a).1 htrunc
    have hfcomp' : f = (t.truncGEπ a).app X ≫ f' ≫ (t.truncLEι a).app Z := by
      simpa [Category.assoc] using hfcomp.symm
    have hgcomp' : (t.truncGEπ a).app X ≫ g' ≫ (t.truncLEι a).app Z = g := by
      simpa [Category.assoc] using hgcomp
    exact hfcomp'.trans <| by
      rw [hfg']
      exact hgcomp'
  · intro u
    let u' : (H a).obj ((t.truncGE a).obj X) ⟶ (H a).obj ((t.truncLE a).obj Z) :=
      eπ.inv ≫ u ≫ s.inv ≫ eι.inv
    obtain ⟨g, hg⟩ :=
      (homology_map_bijective_of_isGE_of_isLE
        ((t.truncGE a).obj X) ((t.truncLE a).obj Z) a).2 u'
    refine ⟨(t.truncGEπ a).app X ≫ g ≫ (t.truncLEι a).app Z, ?_⟩
    have hsurj :
        shiftedHomToHomologyMap X Y a b
            ((t.truncGEπ a).app X ≫ g ≫ (t.truncLEι a).app Z) =
          u ≫ s.inv ≫ s.hom := by
      have hsurj' :
          (H a).map ((t.truncGEπ a).app X) ≫ (H a).map g ≫
              (H a).map ((t.truncLEι a).app Z) ≫ s.hom =
            eπ.hom ≫ u' ≫ eι.hom ≫ s.hom := by
        simpa [eπ, eι, s, Category.assoc] using
          congrArg (fun k ↦ eπ.hom ≫ k ≫ eι.hom ≫ s.hom) hg
      have hsurj₁ :
          shiftedHomToHomologyMap X Y a b
              ((t.truncGEπ a).app X ≫ g ≫ (t.truncLEι a).app Z) =
            (H a).map ((t.truncGEπ a).app X) ≫ (H a).map g ≫
              (H a).map ((t.truncLEι a).app Z) ≫ s.hom := by
        simp [shiftedHomToHomologyMap_eq, Functor.map_comp, s, Category.assoc]
        rfl
      have hsurj₂ :
          eπ.hom ≫ u' ≫ eι.hom ≫ s.hom = u ≫ s.inv ≫ s.hom := by
        simp [u', eπ, eι, s, Category.assoc]
      exact hsurj₁.trans <| hsurj'.trans hsurj₂
    have hs :
        u ≫ s.inv ≫ s.hom = u := by
      simpa [Category.assoc] using
        congrArg (fun t ↦ u ≫ t) (Iso.inv_hom_id s)
    exact hsurj.trans hs

/- Lemma 13.27.3 (1), owner form: in degree `b - a`, the canonical comparison identifies
`Ext^(b - a)(X, Y)` with `Hom(H^a(X), H^b(Y))`; this is the equivalence attached to the
preceding bijectivity theorem, so no extra wrapper declaration is needed. -/
section

variable (X Y : DerivedCategory 𝒜) (a b : ℤ) (hX : X.IsLE a) (hY : Y.IsGE b)

#check (Equiv.ofBijective (shiftedHomToHomologyMap X Y a b)
  (shiftedHomToHomologyMap_bijective X Y a b hX hY) :
    Ext^(b - a)(X, Y) ≃ ((H a).obj X ⟶ (H b).obj Y))

end

/-- Lemma 13.27.3 (2), negative-degree clause for objects of `𝒜`: for `i < 0`, the derived
extension group from `B[0]` to `A[0]` vanishes. -/
theorem single_shiftedHom_subsingleton_of_lt_zero
    (B A : 𝒜) (i : ℤ) (hi : i < 0) :
    Subsingleton (Ext^i((single₀).obj B, (single₀).obj A)) := by
  simpa using
    shiftedHom_subsingleton_of_lt_sub ((single₀).obj B) ((single₀).obj A)
      0 0 i inferInstance inferInstance (by simpa using hi)

section

local instance : HasExt.{w} 𝒜 := hasExt_of_hasDerivedCategory 𝒜

/- Lemma 13.27.3 (2), degree-zero clause for objects of `𝒜`: the degree-zero derived extension
group from `B[0]` to `A[0]` identifies canonically with `Hom(B, A)`. This is exactly the
composite of the canonical owner equivalences `Abelian.Ext.homEquiv` and
`Abelian.Ext.homEquiv₀`, so the file should expose that composite directly rather than a
parallel local alias. -/
variable (B A : 𝒜)

#check (((homEquiv : Abelian.Ext B A 0 ≃
    Ext^((0 : ℤ))((single₀).obj B, (single₀).obj A)).symm).trans homEquiv₀ :
  Ext^((0 : ℤ))((single₀).obj B, (single₀).obj A) ≃ (B ⟶ A))

end

end CategoryTheory
