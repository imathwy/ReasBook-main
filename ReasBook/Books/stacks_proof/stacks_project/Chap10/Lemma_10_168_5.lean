import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.Algebra.Category.Grp.Ulift
import Mathlib.Algebra.Category.Ring.Under.Basic
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Comma.LocallySmall
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import Mathlib.CategoryTheory.Presentable.Finite
import stacks_proof.stacks_project.Chap10.Lemma_10_127_5
import stacks_proof.stacks_project.Chap10.Lemma_10_127_7.BackendComparison
import stacks_proof.stacks_project.Chap10.Lemma_10_131_9
import stacks_proof.stacks_project.Chap10.Lemma_10_131_14
import stacks_proof.stacks_project.Chap10.Lemma_10_151_2
import stacks_proof.stacks_project.Chap10.Lemma_10_168_5.Index

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Ring
open scoped TensorProduct

universe u v w

section

/-
Domain-style sampling:
- primary domain: descent of unramified tensor-product base change along filtered colimits of
  commutative algebras;
- sampled owner declarations:
  `RingHom.FormallyUnramified`,
  `Algebra.FormallyUnramified.base_change`,
  `Algebra.FiniteType.baseChange`,
  `Algebra.Unramified`,
  `Algebra.unramified_iff_formallyUnramified_and_finiteType`;
- best owner abstraction:
  - `source-facing`: the filtered-colimit descent theorem below
  - `core/canonical`: the tensor-product base-change hom
    `Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ R)` together with the induced algebra structure on
    the target tensor product and its owner predicate `Algebra.Unramified`
  - `bridge/view`: the owner-level formally-unramified descent theorem below, which supplies the
    primitive part of the canonical unramified owner while finite type is recovered separately by
    base change
- primitive vs. derived:
  - primitive data: the filtered diagram `F`, the map `φ₀ : B₀ →ₐ[A₀] C₀`, and the formal
    unramifiedness of its colimit base-change hom
  - derived API: finite type of each base-changed hom, obtained from `hφ₀ : φ₀.FiniteType` by
    base change; the public source-facing theorem should therefore conclude in the canonical owner
    `Algebra.Unramified`, with the decomposition into formal unramifiedness and finite type kept
    only as a bridge.
-/

variable {A₀ : Type u} [CommRing A₀]
variable {J : Type v} [SmallCategory J] [IsFiltered J]
variable (F : J ⥤ CommAlgCat.{u} A₀) [HasColimit F]
variable {B₀ C₀ : Type u} [CommRing B₀] [CommRing C₀]
variable [Algebra A₀ B₀] [Algebra A₀ C₀]

/-- Helper for Chap10 Lemma 10 168 5: the underlying type of a filtered colimit cocone of
commutative rings is covered by the images of the stage maps. -/
lemma commRing_filteredColimit_forget_jointly_surjective
    {I : Type v} [SmallCategory I] [IsFiltered I]
    {D : I ⥤ CommRingCat.{u}} {c : Cocone D} (hc : IsColimit c) :
    ∀ x : ((forget CommRingCat).mapCocone c).pt,
      ∃ i y, x = ((forget CommRingCat).mapCocone c).ι.app i y := by
  let G : Set c.pt := {z | ∃ i y, z = c.ι.app i y}
  let S : Subring c.pt := Subring.closure G
  have hclosure : ∀ z : c.pt, z ∈ S → ∃ i y, z = c.ι.app i y := by
    intro z hz
    refine Subring.closure_induction (s := G)
      (p := fun z _ ↦ ∃ i y, z = c.ι.app i y) ?_ ?_ ?_ ?_ ?_ ?_ hz
    · intro z hzG
      exact hzG
    · obtain ⟨i⟩ := (IsFiltered.nonempty : Nonempty I)
      exact ⟨i, 0, ((c.ι.app i).hom.map_zero).symm⟩
    · obtain ⟨i⟩ := (IsFiltered.nonempty : Nonempty I)
      exact ⟨i, 1, ((c.ι.app i).hom.map_one).symm⟩
    · intro x y _ _ hx hy
      obtain ⟨i, xi, hxi⟩ := hx
      obtain ⟨j, yj, hyj⟩ := hy
      let k := IsFiltered.max i j
      let fi : i ⟶ k := IsFiltered.leftToMax i j
      let fj : j ⟶ k := IsFiltered.rightToMax i j
      refine ⟨k, (D.map fi).hom xi + (D.map fj).hom yj, ?_⟩
      have hleft : (c.ι.app i).hom xi = (c.ι.app k).hom ((D.map fi).hom xi) := by
        exact (congrArg (fun f : D.obj i ⟶ c.pt ↦ f xi) (c.w fi)).symm
      have hright : (c.ι.app j).hom yj = (c.ι.app k).hom ((D.map fj).hom yj) := by
        exact (congrArg (fun f : D.obj j ⟶ c.pt ↦ f yj) (c.w fj)).symm
      rw [hxi, hyj, hleft, hright]
      exact ((c.ι.app k).hom.map_add _ _).symm
    · intro x _ hx
      obtain ⟨i, xi, hxi⟩ := hx
      refine ⟨i, -xi, ?_⟩
      rw [hxi]
      exact ((c.ι.app i).hom.map_neg _).symm
    · intro x y _ _ hx hy
      obtain ⟨i, xi, hxi⟩ := hx
      obtain ⟨j, yj, hyj⟩ := hy
      let k := IsFiltered.max i j
      let fi : i ⟶ k := IsFiltered.leftToMax i j
      let fj : j ⟶ k := IsFiltered.rightToMax i j
      refine ⟨k, (D.map fi).hom xi * (D.map fj).hom yj, ?_⟩
      have hleft : (c.ι.app i).hom xi = (c.ι.app k).hom ((D.map fi).hom xi) := by
        exact (congrArg (fun f : D.obj i ⟶ c.pt ↦ f xi) (c.w fi)).symm
      have hright : (c.ι.app j).hom yj = (c.ι.app k).hom ((D.map fj).hom yj) := by
        exact (congrArg (fun f : D.obj j ⟶ c.pt ↦ f yj) (c.w fj)).symm
      rw [hxi, hyj, hleft, hright]
      exact ((c.ι.app k).hom.map_mul _ _).symm
  have hmem (i : I) (y : D.obj i) : c.ι.app i y ∈ S :=
    Subring.subset_closure ⟨i, y, rfl⟩
  let app (i : I) : D.obj i ⟶ CommRingCat.of S :=
    CommRingCat.ofHom ((c.ι.app i).hom.codRestrict S (hmem i))
  have app_naturality : ∀ {i j : I} (f : i ⟶ j), D.map f ≫ app j = app i := by
    intro i j f
    ext y
    exact congrArg (fun g : D.obj i ⟶ c.pt ↦ g y) (c.w f)
  let d : Cocone D :=
    { pt := CommRingCat.of S
      ι :=
        { app := app
          naturality := fun _ _ f ↦ app_naturality f } }
  let liftToS : c.pt ⟶ CommRingCat.of S := hc.desc d
  let incl : CommRingCat.of S ⟶ c.pt := CommRingCat.ofHom S.subtype
  have hincl : liftToS ≫ incl = 𝟙 c.pt := by
    -- Proof comment: both endomorphisms of the colimit point agree after precomposing with every
    -- stage leg, so colimit extensionality identifies them.
    apply hc.hom_ext
    intro i
    calc
      c.ι.app i ≫ liftToS ≫ incl = d.ι.app i ≫ incl := by
        simpa [Category.assoc, liftToS] using congrArg (fun f ↦ f ≫ incl) (hc.fac d i)
      _ = c.ι.app i ≫ 𝟙 c.pt := by
        ext y
        rfl
  intro x
  -- Proof comment: the splitting through the representative subring shows that `x` already lies
  -- in the closure of stage images, where the closure induction produced a stage representative.
  have hx : x = incl (liftToS x) := by
    exact (congrArg (fun f : c.pt ⟶ c.pt ↦ f x) hincl).symm
  obtain ⟨i, y, hy⟩ := hclosure (incl (liftToS x)) (liftToS x).property
  exact ⟨i, y, hx.trans hy⟩

/-- Helper for Chap10 Lemma 10 168 5: if the concrete forgetful functor preserves the chosen
filtered colimit cocone of commutative rings, then equality at one stage descends after one later
transition. -/
lemma commRing_filteredColimit_forget_eq_descends_of_preserves
    {I : Type v} [SmallCategory I] [IsFiltered I]
    {D : I ⥤ CommRingCat.{w}} {c : Cocone D} (hc : IsColimit c)
    [PreservesColimit D (forget CommRingCat.{w})]
    {i : I} (x y : D.obj i)
    (hxy : ((forget CommRingCat).mapCocone c).ι.app i x =
      ((forget CommRingCat).mapCocone c).ι.app i y) :
    ∃ (j : I) (f : i ⟶ j), (D.map f).hom x = (D.map f).hom y := by
  -- Route correction: keep this helper on the stable abstraction boundary where preservation of
  -- the chosen colimit by `forget CommRingCat` is an explicit assumption.
  have hcForget : IsColimit ((forget CommRingCat).mapCocone c) :=
    isColimitOfPreserves (forget CommRingCat.{w}) hc
  -- Proof comment: once the forgotten cocone is known to be colimiting in `Type`, the standard
  -- filtered-colimit equality criterion returns the desired later-stage equality.
  exact (Types.FilteredColimit.isColimit_eq_iff' hcForget x y).mp hxy

/-- Helper for Chap10 Lemma 10 168 5: the explicit large `Type` cocone whose vertex is the
`Ring.DirectLimit` of the tensor-base-change stages is a filtered colimit. -/
lemma commRing_largeFilteredColimit_forget_eq_descends
    {I : Type v} [SmallCategory I] [IsFiltered I]
    {D : I ⥤ CommRingCat.{w}} {c : Cocone D} (hc : IsColimit c)
    {i : I} (x y : D.obj i)
    (hxy : ((forget CommRingCat).mapCocone c).ι.app i x =
      ((forget CommRingCat).mapCocone c).ι.app i y) :
    ∃ (j : I) (f : i ⟶ j), (D.map f).hom x = (D.map f).hom y := by
  let e : AsSmall.{w} I ≌ I := AsSmall.equiv.symm
  letI : IsFiltered (AsSmall.{w} I) :=
    IsFiltered.of_equivalence e
  letI : PreservesColimitsOfShape I (forget CommRingCat.{w}) :=
    preservesColimitsOfShape_of_equiv e (forget CommRingCat.{w})
  -- Proof comment: shrink the filtered index category to a `w`-small equivalent model, apply the
  -- standard filtered-colimit preservation result for `forget CommRingCat`, and transport that
  -- preservation back across the equivalence to the original diagram.
  exact commRing_filteredColimit_forget_eq_descends_of_preserves hc x y hxy

/-- Helper for Chap10 Lemma 10 168 5: the explicit large `Type` cocone whose vertex is the
`Ring.DirectLimit` of the tensor-base-change stages is a filtered colimit. -/
noncomputable def tensor_base_change_ringDirectLimit_uliftTypeCocone_isColimit
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀)
    (R₀ : Type u) [CommRing R₀] [Algebra A₀ R₀] :
    IsColimit (tensor_base_change_ringDirectLimit_uliftTypeCocone G R₀) := by
  classical
  let _ : SmallCategory I := inferInstance
  let _ : IsFiltered I := CategoryTheory.isFiltered_of_directed_le_nonempty I
  let D := tensor_base_change_commAlgDiagram G R₀
  haveI :
      DirectedSystem
        (fun i ↦ ↑(D.obj i))
        (fun i j h ↦ (D.map (homOfLE h)).hom) := by
    -- Proof comment: the transition maps of the tensor-base-change diagram form a directed
    -- system by functoriality of the preorder diagram.
    refine
      { map_self := ?_
        map_map := ?_ }
    · intro i x
      change ((D.map (𝟙 i)).hom) x = x
      simp
    · intro k j i hij hjk x
      simpa using
        congrArg (fun f : D.obj i ⟶ D.obj k ↦ f x)
          (D.map_comp (homOfLE hij) (homOfLE hjk)).symm
  -- Proof comment: recognize the explicit `Ring.DirectLimit` cocone by the standard
  -- filtered-colimit criterion for types: every class has a stage representative, and equality
  -- of two same-stage representatives is detected after one transition.
  refine Types.FilteredColimit.isColimitOf' _
    (tensor_base_change_ringDirectLimit_uliftTypeCocone G R₀) ?surj ?eq
  · intro y
    cases y using ULift.casesOn
    rename_i y
    induction y using Ring.DirectLimit.induction_on with
    | ih i z =>
        refine ⟨i, ULift.up z, ?_⟩
        rfl
  · intro i x y hxy
    cases x using ULift.casesOn
    rename_i x
    cases y using ULift.casesOn
    rename_i y
    have hof :
        DirectLimit.of
            (fun i ↦ ↑(D.obj i))
            (fun _ _ h ↦ (D.map (homOfLE h)).hom)
            i x =
          DirectLimit.of
            (fun i ↦ ↑(D.obj i))
            (fun _ _ h ↦ (D.map (homOfLE h)).hom)
            i y := by
      exact congrArg ULift.down hxy
    have hzero :
        DirectLimit.of
            (fun i ↦ ↑(D.obj i))
            (fun _ _ h ↦ (D.map (homOfLE h)).hom)
            i (x - y) = 0 := by
      calc
        DirectLimit.of
            (fun i ↦ ↑(D.obj i))
            (fun _ _ h ↦ (D.map (homOfLE h)).hom)
            i (x - y) =
          DirectLimit.of
              (fun i ↦ ↑(D.obj i))
              (fun _ _ h ↦ (D.map (homOfLE h)).hom)
              i x -
            DirectLimit.of
              (fun i ↦ ↑(D.obj i))
              (fun _ _ h ↦ (D.map (homOfLE h)).hom)
              i y := by
                exact (DirectLimit.of
                  (fun i ↦ ↑(D.obj i))
                  (fun _ _ h ↦ (D.map (homOfLE h)).hom)
                  i).map_sub x y
        _ = 0 := by rw [hof, sub_self]
    obtain ⟨j, hij, hkill⟩ := DirectLimit.of.zero_exact hzero
    refine ⟨j, homOfLE hij, ?_⟩
    change ULift.up ((D.map (homOfLE hij)).hom x) =
      ULift.up ((D.map (homOfLE hij)).hom y)
    have hsub :
        (D.map (homOfLE hij)).hom x - (D.map (homOfLE hij)).hom y = 0 := by
      calc
        (D.map (homOfLE hij)).hom x - (D.map (homOfLE hij)).hom y =
            (D.map (homOfLE hij)).hom (x - y) := by
              exact ((D.map (homOfLE hij)).hom.map_sub x y).symm
        _ = 0 := hkill
    exact congrArg ULift.up (sub_eq_zero.mp hsub)

/-- Helper for Chap10 Lemma 10 168 5: the actual tensor-base-change cocone remains colimiting
after forgetting from `CommAlgCat R₀` to `CommRingCat`. -/
noncomputable def tensor_base_change_commAlgCocone_forget₂_isColimit
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G)
    (R₀ : Type u) [CommRing R₀] [Algebra A₀ R₀] :
    IsColimit ((forget₂ (CommAlgCat.{u} R₀) CommRingCat).mapCocone
      (tensor_base_change_commAlgCocone G c R₀)) :=
  let cR : ColimitCocone (tensor_base_change_commAlgDiagram G R₀) :=
    { cocone := tensor_base_change_commAlgCocone G c R₀
      isColimit := tensor_base_change_commAlgCocone_isColimit G c R₀ }
  -- Proof comment: package the actual tensor-base-change cocone as a colimit cocone in
  -- `CommAlgCat R₀`, then apply the existing filtered-colimit bridge for the forgetful functor.
  commAlg_forget_commRing_mapCocone_isColimit (tensor_base_change_commAlgDiagram G R₀) cR

/-- Helper for Chap10 Lemma 10 168 5: every element of the forgotten actual
tensor-base-change cocone point is represented by some tensor-base-change stage. -/
theorem tensor_base_change_commAlgCocone_forget_jointly_surjective
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G)
    (R₀ : Type u) [CommRing R₀] [Algebra A₀ R₀] :
    ∀ y : R₀ ⊗[A₀] c.cocone.pt,
      ∃ i, ∃ z : R₀ ⊗[A₀] G.obj i,
        y = (Algebra.TensorProduct.map (AlgHom.id A₀ R₀) (c.cocone.ι.app i).hom) z := by
  let _ : SmallCategory I := inferInstance
  let _ : IsFiltered I := CategoryTheory.isFiltered_of_directed_le_nonempty I
  let cForget := ((forget₂ (CommAlgCat.{u} A₀) CommRingCat).mapCocone c.cocone)
  have hstageSurj : ∀ x : c.cocone.pt, ∃ i, ∃ z : G.obj i, x = (c.cocone.ι.app i) z := by
    -- Proof comment: every point of the original colimit cocone comes from some stage after
    -- forgetting to commutative rings.
    have hcForget : IsColimit cForget := commAlg_forget_commRing_mapCocone_isColimit G c
    simpa [cForget] using
      commRing_filteredColimit_forget_jointly_surjective hcForget
  have hmapToCocone :
      ∀ {i j : I} (f : i ⟶ j) (z : R₀ ⊗[A₀] ↑(G.obj i)),
        (Algebra.TensorProduct.map (AlgHom.id A₀ R₀) (c.cocone.ι.app j).hom)
            ((Algebra.TensorProduct.map (AlgHom.id A₀ R₀) (G.map f).hom) z) =
          (Algebra.TensorProduct.map (AlgHom.id A₀ R₀) (c.cocone.ι.app i).hom) z := by
    intro i j f z
    -- Proof comment: tensor induction turns cocone naturality for `c` into cocone naturality for
    -- the induced tensor-product maps.
    induction z using TensorProduct.induction_on with
    | zero =>
        rw [map_zero, map_zero, map_zero]
        rfl
    | tmul r x =>
        change r ⊗ₜ[A₀] ((c.cocone.ι.app j).hom ((G.map f).hom x)) =
          r ⊗ₜ[A₀] ((c.cocone.ι.app i).hom x)
        congr 1
        exact congrArg (fun g : G.obj i ⟶ c.cocone.pt ↦ g.hom x) (c.cocone.w f)
    | add z₁ z₂ hz₁ hz₂ =>
        calc
          (Algebra.TensorProduct.map (AlgHom.id A₀ R₀) (c.cocone.ι.app j).hom)
              ((Algebra.TensorProduct.map (AlgHom.id A₀ R₀) (G.map f).hom) (z₁ + z₂)) =
            (Algebra.TensorProduct.map (AlgHom.id A₀ R₀) (c.cocone.ι.app j).hom)
              ((Algebra.TensorProduct.map (AlgHom.id A₀ R₀) (G.map f).hom) z₁ +
                (Algebra.TensorProduct.map (AlgHom.id A₀ R₀) (G.map f).hom) z₂) := by
                  rw [map_add]
          _ =
            (Algebra.TensorProduct.map (AlgHom.id A₀ R₀) (c.cocone.ι.app j).hom)
                ((Algebra.TensorProduct.map (AlgHom.id A₀ R₀) (G.map f).hom) z₁) +
              (Algebra.TensorProduct.map (AlgHom.id A₀ R₀) (c.cocone.ι.app j).hom)
                ((Algebra.TensorProduct.map (AlgHom.id A₀ R₀) (G.map f).hom) z₂) := by
                  rw [map_add]
          _ =
            (Algebra.TensorProduct.map (AlgHom.id A₀ R₀) (c.cocone.ι.app i).hom) z₁ +
              (Algebra.TensorProduct.map (AlgHom.id A₀ R₀) (c.cocone.ι.app i).hom) z₂ := by
                  exact congrArg₂ HAdd.hAdd hz₁ hz₂
          _ =
            (Algebra.TensorProduct.map (AlgHom.id A₀ R₀) (c.cocone.ι.app i).hom) (z₁ + z₂) := by
                  rw [map_add]
  intro y
  -- Proof comment: every tensor is built from pure tensors, and finite sums can be moved to a
  -- common upper stage by filteredness.
  refine TensorProduct.induction_on y ?_ ?_ ?_
  · obtain ⟨i⟩ := (IsFiltered.nonempty : Nonempty I)
    refine ⟨i, 0, ?_⟩
    simpa using ((Algebra.TensorProduct.map (AlgHom.id A₀ R₀) (c.cocone.ι.app i).hom).map_zero).symm
  · intro r x
    obtain ⟨i, z, hz⟩ := hstageSurj x
    refine ⟨i, r ⊗ₜ[A₀] z, ?_⟩
    simpa [hz, AlgHom.id_apply] using
      (Algebra.TensorProduct.map_tmul (AlgHom.id A₀ R₀) (c.cocone.ι.app i).hom r z).symm
  · intro y₁ y₂ hy₁ hy₂
    obtain ⟨i, z₁, hz₁⟩ := hy₁
    obtain ⟨j, z₂, hz₂⟩ := hy₂
    let k := IsFiltered.max i j
    let fi : i ⟶ k := IsFiltered.leftToMax i j
    let fj : j ⟶ k := IsFiltered.rightToMax i j
    let gi : (R₀ ⊗[A₀] ↑(G.obj i)) →ₐ[A₀] (R₀ ⊗[A₀] ↑c.cocone.pt) :=
      Algebra.TensorProduct.map (AlgHom.id A₀ R₀) (c.cocone.ι.app i).hom
    let gj : (R₀ ⊗[A₀] ↑(G.obj j)) →ₐ[A₀] (R₀ ⊗[A₀] ↑c.cocone.pt) :=
      Algebra.TensorProduct.map (AlgHom.id A₀ R₀) (c.cocone.ι.app j).hom
    let gk : (R₀ ⊗[A₀] ↑(G.obj k)) →ₐ[A₀] (R₀ ⊗[A₀] ↑c.cocone.pt) :=
      Algebra.TensorProduct.map (AlgHom.id A₀ R₀) (c.cocone.ι.app k).hom
    let tfi : (R₀ ⊗[A₀] ↑(G.obj i)) →ₐ[A₀] (R₀ ⊗[A₀] ↑(G.obj k)) :=
      Algebra.TensorProduct.map (AlgHom.id A₀ R₀) (G.map fi).hom
    let tfj : (R₀ ⊗[A₀] ↑(G.obj j)) →ₐ[A₀] (R₀ ⊗[A₀] ↑(G.obj k)) :=
      Algebra.TensorProduct.map (AlgHom.id A₀ R₀) (G.map fj).hom
    let z : R₀ ⊗[A₀] ↑(G.obj k) :=
      tfi z₁ + tfj z₂
    refine ⟨k, z, ?_⟩
    change y₁ + y₂ = gk z
    calc
      y₁ + y₂ = gi z₁ + gj z₂ := by
            simpa [gi, gj] using congrArg₂ HAdd.hAdd hz₁ hz₂
      _ =
          gk (tfi z₁) + gk (tfj z₂) := by
            simpa [gi, gj, gk, tfi, tfj] using
              congrArg₂ HAdd.hAdd (hmapToCocone fi z₁).symm (hmapToCocone fj z₂).symm
      _ = gk z := by
            simp [z, gk, map_add]

/-- Helper for Chap10 Lemma 10 168 5: a universal differential vanishes exactly when the
corresponding singleton relation lies in the `KaehlerDifferential.kerTotal` presentation. -/
theorem kaehlerDifferential_D_eq_zero_iff_single_mem_kerTotal
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (s : S) :
    KaehlerDifferential.D R S s = 0 ↔
      Finsupp.single s (1 : S) ∈ KaehlerDifferential.kerTotal R S := by
  -- Proof comment: `kerTotal_eq` identifies the relation submodule with the kernel of the linear
  -- combination map, and a singleton relation evaluates to exactly `D s`.
  rw [← KaehlerDifferential.kerTotal_eq R S, LinearMap.mem_ker]
  simp

/-- Helper for Chap10 Lemma 10 168 5: the transition map on tensor-base-changed target rings
induces the corresponding map on finitely supported Kähler-relation witnesses. -/
noncomputable def tensorBaseChangeRelationMap
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (C₀ : Type u) [CommRing C₀] [Algebra A₀ C₀]
    {i j : I} (h : i ≤ j) :
    ((C₀ ⊗[A₀] G.obj i) →₀ (C₀ ⊗[A₀] G.obj i)) →ₗ[A₀]
      ((C₀ ⊗[A₀] G.obj j) →₀ (C₀ ⊗[A₀] G.obj j)) :=
  let fC : (C₀ ⊗[A₀] ↑(G.obj i)) →ₐ[A₀] (C₀ ⊗[A₀] ↑(G.obj j)) :=
    Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (G.map (homOfLE h)).hom
  ((Finsupp.mapRange.linearMap
      fC.toLinearMap).comp
    (Finsupp.lmapDomain (C₀ ⊗[A₀] ↑(G.obj i)) A₀ fC))

/-- Helper for Chap10 Lemma 10 168 5: `tensorBaseChangeRelationMap` is the composite of
`Finsupp.mapDomain` on support indices and `Finsupp.mapRange` on coefficients. -/
theorem tensorBaseChangeRelationMap_def
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (C₀ : Type u) [CommRing C₀] [Algebra A₀ C₀]
    {i j : I} (h : i ≤ j)
    (w : (C₀ ⊗[A₀] G.obj i) →₀ (C₀ ⊗[A₀] G.obj i)) :
    tensorBaseChangeRelationMap G C₀ h w =
      Finsupp.mapRange
        (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (G.map (homOfLE h)).hom)
        (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (G.map (homOfLE h)).hom).map_zero
        (Finsupp.mapDomain
          (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (G.map (homOfLE h)).hom) w) := by
  -- Proof comment: expose the stable normal form once so later proofs can rewrite by name
  -- instead of repeating brittle definitional `change` steps.
  rfl

/-- Helper for Chap10 Lemma 10 168 5: relation transport sends a singleton witness to the
singleton supported at the transported tensor with transported coefficient. -/
theorem tensorBaseChangeRelationMap_single
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (C₀ : Type u) [CommRing C₀] [Algebra A₀ C₀]
    {i j : I} (h : i ≤ j) (z a : C₀ ⊗[A₀] G.obj i) :
    tensorBaseChangeRelationMap G C₀ h (Finsupp.single z a) =
      Finsupp.single
        ((Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (G.map (homOfLE h)).hom) z)
        ((Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (G.map (homOfLE h)).hom) a) := by
  classical
  -- Proof comment: `tensorBaseChangeRelationMap` is exactly `mapDomain` on the support followed
  -- by `mapRange` on the coefficients, so a singleton remains a singleton.
  rw [tensorBaseChangeRelationMap_def]
  simp

/-- Helper for Chap10 Lemma 10 168 5: stage-transition relation maps compose exactly along the
directed tensor-base-change system. -/
theorem tensorBaseChangeRelationMap_comp
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (C₀ : Type u) [CommRing C₀] [Algebra A₀ C₀]
    {i j k : I} (hij : i ≤ j) (hjk : j ≤ k)
    (w : (C₀ ⊗[A₀] G.obj i) →₀ (C₀ ⊗[A₀] G.obj i)) :
    tensorBaseChangeRelationMap G C₀ hjk (tensorBaseChangeRelationMap G C₀ hij w) =
      tensorBaseChangeRelationMap G C₀ (hij.trans hjk) w := by
  let fij : (C₀ ⊗[A₀] ↑(G.obj i)) →ₐ[A₀] (C₀ ⊗[A₀] ↑(G.obj j)) :=
    Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (G.map (homOfLE hij)).hom
  let fjk : (C₀ ⊗[A₀] ↑(G.obj j)) →ₐ[A₀] (C₀ ⊗[A₀] ↑(G.obj k)) :=
    Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (G.map (homOfLE hjk)).hom
  let fik : (C₀ ⊗[A₀] ↑(G.obj i)) →ₐ[A₀] (C₀ ⊗[A₀] ↑(G.obj k)) :=
    Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (G.map (homOfLE (hij.trans hjk))).hom
  have hcomp_apply :
      ∀ t : C₀ ⊗[A₀] ↑(G.obj i), fjk (fij t) = fik t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero =>
        simp [fij, fjk, fik]
    | tmul c r =>
        -- Proof comment: on pure tensors, functoriality of `G` identifies the two routes.
        change c ⊗ₜ[A₀] ((G.map (homOfLE hjk)).hom (((G.map (homOfLE hij)).hom r))) =
          c ⊗ₜ[A₀] ((G.map (homOfLE (hij.trans hjk))).hom r)
        congr 1
        simpa using congrArg (fun f : G.obj i ⟶ G.obj k ↦ f r)
          (G.map_comp (homOfLE hij) (homOfLE hjk)).symm
    | add t₁ t₂ ht₁ ht₂ =>
        simp [fij, fjk, fik, map_add, ht₁, ht₂]
  induction w using Finsupp.induction_linear with
  | zero =>
      -- Proof comment: both transport routes preserve the zero relation.
      simp [tensorBaseChangeRelationMap]
  | add w₁ w₂ hw₁ hw₂ =>
      -- Proof comment: functoriality is additive because both transport maps are linear.
      simp [map_add, hw₁, hw₂]
  | single z a =>
      -- Proof comment: after reducing to singleton witnesses, only the tensor-stage map
      -- composition law remains.
      rw [tensorBaseChangeRelationMap_single, tensorBaseChangeRelationMap_single,
        tensorBaseChangeRelationMap_single]
      simp [fij, fjk, fik, hcomp_apply]

/-- Helper for Chap10 Lemma 10 168 5: a `kerTotal` witness at one tensor stage remains a
`kerTotal` witness after passing to any later tensor stage. -/
theorem tensorBaseChangeKerTotalTransition
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (φ₀ : B₀ →ₐ[A₀] C₀) {i j : I} (h : i ≤ j)
    {w : (C₀ ⊗[A₀] G.obj i) →₀ (C₀ ⊗[A₀] G.obj i)}
    (hw :
      letI : Algebra (B₀ ⊗[A₀] G.obj i) (C₀ ⊗[A₀] G.obj i) :=
        (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ (G.obj i))).toRingHom.toAlgebra
      w ∈ KaehlerDifferential.kerTotal (B₀ ⊗[A₀] G.obj i) (C₀ ⊗[A₀] G.obj i)) :
    letI : Algebra (B₀ ⊗[A₀] G.obj j) (C₀ ⊗[A₀] G.obj j) :=
      (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ (G.obj j))).toRingHom.toAlgebra
    tensorBaseChangeRelationMap G C₀ h w ∈
      KaehlerDifferential.kerTotal (B₀ ⊗[A₀] G.obj j) (C₀ ⊗[A₀] G.obj j) := by
  -- Proof comment: rewrite both `kerTotal` memberships as vanishing of `linearCombination`, then
  -- map that vanishing across the tensor-base-change square with the canonical Kähler map.
  let φi : (B₀ ⊗[A₀] ↑(G.obj i)) →ₐ[A₀] (C₀ ⊗[A₀] ↑(G.obj i)) :=
    Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(G.obj i))
  let φj : (B₀ ⊗[A₀] ↑(G.obj j)) →ₐ[A₀] (C₀ ⊗[A₀] ↑(G.obj j)) :=
    Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(G.obj j))
  let fB : (B₀ ⊗[A₀] ↑(G.obj i)) →ₐ[A₀] (B₀ ⊗[A₀] ↑(G.obj j)) :=
    Algebra.TensorProduct.map (AlgHom.id A₀ B₀) (G.map (homOfLE h)).hom
  let fC : (C₀ ⊗[A₀] ↑(G.obj i)) →ₐ[A₀] (C₀ ⊗[A₀] ↑(G.obj j)) :=
    Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (G.map (homOfLE h)).hom
  letI : Algebra (B₀ ⊗[A₀] ↑(G.obj i)) (C₀ ⊗[A₀] ↑(G.obj i)) :=
    φi.toRingHom.toAlgebra
  letI : Algebra (B₀ ⊗[A₀] ↑(G.obj j)) (C₀ ⊗[A₀] ↑(G.obj j)) :=
    φj.toRingHom.toAlgebra
  letI : Algebra (B₀ ⊗[A₀] ↑(G.obj i)) (B₀ ⊗[A₀] ↑(G.obj j)) :=
    fB.toRingHom.toAlgebra
  letI : Algebra (C₀ ⊗[A₀] ↑(G.obj i)) (C₀ ⊗[A₀] ↑(G.obj j)) :=
    fC.toRingHom.toAlgebra
  letI : Algebra (B₀ ⊗[A₀] ↑(G.obj i)) (C₀ ⊗[A₀] ↑(G.obj j)) :=
    (fC.toRingHom.comp φi.toRingHom).toAlgebra
  have hsourceTower :
      ∀ y : B₀ ⊗[A₀] ↑(G.obj i),
        algebraMap (B₀ ⊗[A₀] ↑(G.obj i)) (C₀ ⊗[A₀] ↑(G.obj j)) y =
          algebraMap (C₀ ⊗[A₀] ↑(G.obj i)) (C₀ ⊗[A₀] ↑(G.obj j))
            (algebraMap (B₀ ⊗[A₀] ↑(G.obj i)) (C₀ ⊗[A₀] ↑(G.obj i)) y) := by
    intro y
    rfl
  letI : IsScalarTower (B₀ ⊗[A₀] ↑(G.obj i))
      (C₀ ⊗[A₀] ↑(G.obj i)) (C₀ ⊗[A₀] ↑(G.obj j)) :=
    IsScalarTower.of_algebraMap_eq hsourceTower
  have htargetTower :
      ∀ y : B₀ ⊗[A₀] ↑(G.obj i),
        algebraMap (B₀ ⊗[A₀] ↑(G.obj i)) (C₀ ⊗[A₀] ↑(G.obj j)) y =
          algebraMap (B₀ ⊗[A₀] ↑(G.obj j)) (C₀ ⊗[A₀] ↑(G.obj j))
            (algebraMap (B₀ ⊗[A₀] ↑(G.obj i)) (B₀ ⊗[A₀] ↑(G.obj j)) y) := by
    intro y
    -- Proof comment: tensor induction compares the two routes around the base-change square on
    -- pure tensors; additivity then upgrades the comparison to every tensor.
    induction y using TensorProduct.induction_on with
    | zero =>
        simp
    | tmul b r =>
        change fC (φi (b ⊗ₜ[A₀] r)) = φj (fB (b ⊗ₜ[A₀] r))
        simp [fB, fC, φi, φj, Algebra.TensorProduct.map_tmul]
    | add y z hy hz =>
        simp [map_add, hy, hz]
  letI : IsScalarTower (B₀ ⊗[A₀] ↑(G.obj i))
      (B₀ ⊗[A₀] ↑(G.obj j)) (C₀ ⊗[A₀] ↑(G.obj j)) :=
    IsScalarTower.of_algebraMap_eq htargetTower
  rw [← KaehlerDifferential.kerTotal_eq] at hw ⊢
  rw [LinearMap.mem_ker] at hw ⊢
  have hcompat :
      KaehlerDifferential.map
          (B₀ ⊗[A₀] ↑(G.obj i)) (B₀ ⊗[A₀] ↑(G.obj j))
          (C₀ ⊗[A₀] ↑(G.obj i)) (C₀ ⊗[A₀] ↑(G.obj j))
          (Finsupp.linearCombination
            (C₀ ⊗[A₀] ↑(G.obj i))
            (KaehlerDifferential.D
              (B₀ ⊗[A₀] ↑(G.obj i)) (C₀ ⊗[A₀] ↑(G.obj i))) w) =
        Finsupp.linearCombination
          (C₀ ⊗[A₀] ↑(G.obj j))
          (KaehlerDifferential.D
            (B₀ ⊗[A₀] ↑(G.obj j)) (C₀ ⊗[A₀] ↑(G.obj j)))
          (tensorBaseChangeRelationMap G C₀ h w) := by
    -- Proof comment: both constructions are additive in the finitely supported relation, so it is
    -- enough to compare them on singleton relations.
    clear hw
    induction w using Finsupp.induction_linear with
    | zero =>
        simp [tensorBaseChangeRelationMap]
    | add w₁ w₂ hw₁ hw₂ =>
        simp [map_add, hw₁, hw₂]
    | single z a =>
        rw [Finsupp.linearCombination_single, tensorBaseChangeRelationMap_single,
          Finsupp.linearCombination_single, LinearMap.map_smul, KaehlerDifferential.map_D]
        rfl
  rw [← hcompat, hw, map_zero]

/-- Helper for Chap10 Lemma 10 168 5: vanishing of `D (x ⊗ₜ 1)` is preserved by passing from
one tensor-base-change stage to a later stage. -/
theorem tensor_base_change_D_tmul_one_transition
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀)
    (φ₀ : B₀ →ₐ[A₀] C₀) {i j : I} (h : i ≤ j) (x : C₀)
    (hz :
      letI : Algebra (B₀ ⊗[A₀] G.obj i) (C₀ ⊗[A₀] G.obj i) :=
        (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ (G.obj i))).toRingHom.toAlgebra
      KaehlerDifferential.D (B₀ ⊗[A₀] G.obj i) (C₀ ⊗[A₀] G.obj i)
        (x ⊗ₜ[A₀] (1 : G.obj i)) = 0) :
    letI : Algebra (B₀ ⊗[A₀] G.obj j) (C₀ ⊗[A₀] G.obj j) :=
      (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ (G.obj j))).toRingHom.toAlgebra
    KaehlerDifferential.D (B₀ ⊗[A₀] G.obj j) (C₀ ⊗[A₀] G.obj j)
      (x ⊗ₜ[A₀] (1 : G.obj j)) = 0 := by
  letI : Algebra (B₀ ⊗[A₀] G.obj i) (C₀ ⊗[A₀] G.obj i) :=
    (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ (G.obj i))).toRingHom.toAlgebra
  have hker :
      Finsupp.single (x ⊗ₜ[A₀] (1 : G.obj i)) (1 : C₀ ⊗[A₀] G.obj i) ∈
        KaehlerDifferential.kerTotal (B₀ ⊗[A₀] G.obj i) (C₀ ⊗[A₀] G.obj i) :=
    (kaehlerDifferential_D_eq_zero_iff_single_mem_kerTotal
      (x ⊗ₜ[A₀] (1 : G.obj i))).1 hz
  letI : Algebra (B₀ ⊗[A₀] G.obj j) (C₀ ⊗[A₀] G.obj j) :=
    (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ (G.obj j))).toRingHom.toAlgebra
  have hker' := tensorBaseChangeKerTotalTransition G φ₀ h hker
  have hsingle :
      tensorBaseChangeRelationMap G C₀ h
          (Finsupp.single (x ⊗ₜ[A₀] (1 : G.obj i)) (1 : C₀ ⊗[A₀] G.obj i)) =
        Finsupp.single (x ⊗ₜ[A₀] (1 : G.obj j)) (1 : C₀ ⊗[A₀] G.obj j) := by
    rw [tensorBaseChangeRelationMap_single]
    simp [Algebra.TensorProduct.map_tmul]
  -- Proof comment: move the singleton `kerTotal` witness along the transition map, identify the
  -- transported singleton explicitly, and then translate back to `D = 0`.
  exact
    (kaehlerDifferential_D_eq_zero_iff_single_mem_kerTotal
      (x ⊗ₜ[A₀] (1 : G.obj j))).2 <|
      by simpa [hsingle] using hker'

/-- Helper for Chap10 Lemma 10 168 5: a stage relation can be pushed forward along the
tensor-base-change cocone leg to a relation on the cocone point. -/
noncomputable def tensorBaseChangeRelationToCoconeMap
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G)
    (C₀ : Type u) [CommRing C₀] [Algebra A₀ C₀] {i : I} :
    ((C₀ ⊗[A₀] G.obj i) →₀ (C₀ ⊗[A₀] G.obj i)) →ₗ[A₀]
      ((C₀ ⊗[A₀] c.cocone.pt) →₀ (C₀ ⊗[A₀] c.cocone.pt)) :=
  let fC : (C₀ ⊗[A₀] ↑(G.obj i)) →ₐ[A₀] (C₀ ⊗[A₀] ↑c.cocone.pt) :=
    Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app i).hom
  ((Finsupp.mapRange.linearMap
      fC.toLinearMap).comp
    (Finsupp.lmapDomain (C₀ ⊗[A₀] ↑(G.obj i)) A₀ fC))

/-- Helper for Chap10 Lemma 10 168 5: `tensorBaseChangeRelationToCoconeMap` is the composite of
`Finsupp.mapDomain` on support indices and `Finsupp.mapRange` on coefficients. -/
theorem tensorBaseChangeRelationToCoconeMap_def
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G)
    (C₀ : Type u) [CommRing C₀] [Algebra A₀ C₀] {i : I}
    (w : (C₀ ⊗[A₀] G.obj i) →₀ (C₀ ⊗[A₀] G.obj i)) :
    tensorBaseChangeRelationToCoconeMap G c C₀ w =
      Finsupp.mapRange
        (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app i).hom)
        (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app i).hom).map_zero
        (Finsupp.mapDomain
          (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app i).hom) w) := by
  -- Proof comment: expose the cocone map in the same stable normal form as the stage-transition
  -- map so later proofs can rewrite by name instead of unfolding through `lmapDomain`.
  rfl

/-- Helper for Chap10 Lemma 10 168 5: the cocone relation map carries a singleton stage witness
to the singleton relation on its cocone-point image. -/
theorem tensorBaseChangeRelationToCoconeMap_single
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G)
    (C₀ : Type u) [CommRing C₀] [Algebra A₀ C₀] {i : I}
    (z a : C₀ ⊗[A₀] G.obj i) :
    tensorBaseChangeRelationToCoconeMap G c C₀ (Finsupp.single z a) =
      Finsupp.single
        ((Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app i).hom) z)
        ((Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app i).hom) a) := by
  -- Proof comment: this should be a direct `Finsupp` singleton normal-form computation for the
  -- cocone relation map, parallel to `tensorBaseChangeRelationMap_single`.
  classical
  rw [tensorBaseChangeRelationToCoconeMap_def]
  simp

/-- Helper for Chap10 Lemma 10 168 5: sending a relation to a later stage and then to the cocone
point agrees with sending it directly to the cocone point. -/
theorem tensorBaseChangeRelationToCoconeMap_comp_transition
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G)
    (C₀ : Type u) [CommRing C₀] [Algebra A₀ C₀]
    {i j : I} (h : i ≤ j)
    (w : (C₀ ⊗[A₀] G.obj i) →₀ (C₀ ⊗[A₀] G.obj i)) :
    tensorBaseChangeRelationToCoconeMap G c C₀ (tensorBaseChangeRelationMap G C₀ h w) =
      tensorBaseChangeRelationToCoconeMap G c C₀ w := by
  let fij : (C₀ ⊗[A₀] ↑(G.obj i)) →ₐ[A₀] (C₀ ⊗[A₀] ↑(G.obj j)) :=
    Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (G.map (homOfLE h)).hom
  let fj : (C₀ ⊗[A₀] ↑(G.obj j)) →ₐ[A₀] (C₀ ⊗[A₀] ↑c.cocone.pt) :=
    Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app j).hom
  let fi : (C₀ ⊗[A₀] ↑(G.obj i)) →ₐ[A₀] (C₀ ⊗[A₀] ↑c.cocone.pt) :=
    Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app i).hom
  have hcomp_apply :
      ∀ t : C₀ ⊗[A₀] ↑(G.obj i), fj (fij t) = fi t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero =>
        simp [fij, fj, fi]
    | tmul c₁ r =>
        -- Proof comment: on pure tensors, cocone naturality identifies the two routes from the
        -- stage `i` tensor to the cocone point.
        change c₁ ⊗ₜ[A₀] ((c.cocone.ι.app j).hom (((G.map (homOfLE h)).hom r))) =
          c₁ ⊗ₜ[A₀] ((c.cocone.ι.app i).hom r)
        congr 1
        exact congrArg (fun f : G.obj i ⟶ c.cocone.pt ↦ f.hom r) (c.cocone.w (homOfLE h))
    | add t₁ t₂ ht₁ ht₂ =>
        calc
          fj (fij (t₁ + t₂)) = fj (fij t₁ + fij t₂) := by
            simp [fij, map_add]
          _ = fj (fij t₁) + fj (fij t₂) := by
            simp [fj, map_add]
          _ = fi t₁ + fi t₂ := by rw [ht₁, ht₂]
          _ = fi (t₁ + t₂) := by
            simp [fi, map_add]
  induction w using Finsupp.induction_linear with
  | zero =>
      -- Proof comment: both routes send the zero relation to zero.
      simp [tensorBaseChangeRelationMap, tensorBaseChangeRelationToCoconeMap]
  | add w₁ w₂ hw₁ hw₂ =>
      -- Proof comment: compatibility follows additively once it is known on the summands.
      simp [map_add, hw₁, hw₂]
  | single z a =>
      -- Proof comment: after reducing to singleton witnesses, only cocone naturality on the
      -- underlying tensor-stage map remains.
      rw [tensorBaseChangeRelationMap_single, tensorBaseChangeRelationToCoconeMap_single,
        tensorBaseChangeRelationToCoconeMap_single]
      simpa using congrArg₂ Finsupp.single (hcomp_apply z) (hcomp_apply a)

/-- Helper for Chap10 Lemma 10 168 5: evaluating a stage-transition relation at the image of a
stage point collects exactly the coefficients over the corresponding finite support fiber. -/
theorem tensorBaseChangeRelationMap_apply_eq_sum
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (C₀ : Type u) [CommRing C₀] [Algebra A₀ C₀]
    {i j : I} (h : i ≤ j)
    [DecidableEq (C₀ ⊗[A₀] G.obj j)]
    (w : (C₀ ⊗[A₀] G.obj i) →₀ (C₀ ⊗[A₀] G.obj i))
    (z : C₀ ⊗[A₀] G.obj i) :
    tensorBaseChangeRelationMap G C₀ h w
        ((Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (G.map (homOfLE h)).hom) z) =
      (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (G.map (homOfLE h)).hom)
        (∑ a ∈ w.support with
            (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (G.map (homOfLE h)).hom) a =
              (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (G.map (homOfLE h)).hom) z,
          w a) := by
  -- Proof comment: first rewrite the transported relation into `mapRange (mapDomain ...)`
  -- normal form, then apply the standard finite-support fiber-sum formula for `mapDomain`.
  rw [tensorBaseChangeRelationMap_def, Finsupp.mapRange_apply, Finsupp.mapDomain_apply_eq_sum]

open scoped Classical in
/-- Helper for Chap10 Lemma 10 168 5: evaluating the cocone relation map at the image of a stage
point collects exactly the coefficients over the corresponding finite support fiber. -/
theorem tensorBaseChangeRelationToCoconeMap_apply_eq_sum
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G)
    (C₀ : Type u) [CommRing C₀] [Algebra A₀ C₀] {i : I}
    (w : (C₀ ⊗[A₀] G.obj i) →₀ (C₀ ⊗[A₀] G.obj i))
    (z : C₀ ⊗[A₀] G.obj i) :
    tensorBaseChangeRelationToCoconeMap G c C₀ w
        ((Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app i).hom) z) =
      (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app i).hom)
        (∑ a ∈ w.support with
            (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app i).hom) a =
              (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app i).hom) z,
          w a) := by
  -- Proof comment: the cocone map has the same `mapRange (mapDomain ...)` normal form as the
  -- stage-transition map, so the same `Finsupp.mapDomain_apply_eq_sum` computation applies.
  have hsum :
      (Finsupp.mapDomain
          (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app i).hom) w)
        ((Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app i).hom) z) =
        ∑ a ∈ w.support with
            (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app i).hom) a =
              (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app i).hom) z,
          w a :=
    Finsupp.mapDomain_apply_eq_sum
      (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app i).hom) w
  simpa [tensorBaseChangeRelationToCoconeMap_def] using
    congrArg
      (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app i).hom)
      hsum

/-- Helper for Chap10 Lemma 10 168 5: the stage-transition relation map sends scalar multiples to
the corresponding scalar multiples after transporting the scalar along the tensor-stage map. -/
theorem tensorBaseChangeRelationMap_smul
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (C₀ : Type u) [CommRing C₀] [Algebra A₀ C₀]
    {i j : I} (h : i ≤ j) (a : C₀ ⊗[A₀] G.obj i)
    (w : (C₀ ⊗[A₀] G.obj i) →₀ (C₀ ⊗[A₀] G.obj i)) :
    tensorBaseChangeRelationMap G C₀ h (a • w) =
      ((Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (G.map (homOfLE h)).hom) a) •
        tensorBaseChangeRelationMap G C₀ h w := by
  induction w using Finsupp.induction_linear with
  | zero =>
      -- Proof comment: scalar multiplication preserves the zero relation on both sides.
      simp [tensorBaseChangeRelationMap]
  | add w₁ w₂ hw₁ hw₂ =>
      -- Proof comment: both relation transport and scalar multiplication distribute over sums.
      simp [smul_add, map_add, hw₁, hw₂]
  | single z b =>
      -- Proof comment: on a singleton witness the statement reduces to the multiplicativity of
      -- the tensor-stage algebra map on the coefficient.
      have hsingle :
          a • (Finsupp.single z b :
            (C₀ ⊗[A₀] ↑(G.obj i)) →₀ (C₀ ⊗[A₀] ↑(G.obj i))) =
            Finsupp.single z (a * b) := by
        ext x
        by_cases hx : x = z
        · subst hx
          simp
        · simp [hx]
      rw [hsingle, tensorBaseChangeRelationMap_single, tensorBaseChangeRelationMap_single]
      ext x
      by_cases hx : x =
          (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (G.map (homOfLE h)).hom) z
      · subst hx
        simp [map_mul]
      · simp [hx, map_mul]

/-- Helper for Chap10 Lemma 10 168 5: the cocone relation map sends scalar multiples to the
corresponding scalar multiples after transporting the scalar to the cocone point. -/
theorem tensorBaseChangeRelationToCoconeMap_smul
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G)
    (C₀ : Type u) [CommRing C₀] [Algebra A₀ C₀] {i : I}
    (a : C₀ ⊗[A₀] G.obj i)
    (w : (C₀ ⊗[A₀] G.obj i) →₀ (C₀ ⊗[A₀] G.obj i)) :
    letI : Algebra (C₀ ⊗[A₀] G.obj i) (C₀ ⊗[A₀] c.cocone.pt) :=
      (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app i).hom).toRingHom.toAlgebra
    tensorBaseChangeRelationToCoconeMap G c C₀ (a • w) =
      (algebraMap (C₀ ⊗[A₀] G.obj i) (C₀ ⊗[A₀] c.cocone.pt) a) •
        tensorBaseChangeRelationToCoconeMap G c C₀ w := by
  let fC : (C₀ ⊗[A₀] ↑(G.obj i)) →ₐ[A₀] (C₀ ⊗[A₀] ↑c.cocone.pt) :=
    Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app i).hom
  letI : Algebra (C₀ ⊗[A₀] ↑(G.obj i)) (C₀ ⊗[A₀] ↑c.cocone.pt) :=
    fC.toRingHom.toAlgebra
  induction w using Finsupp.induction_linear with
  | zero =>
      -- Proof comment: scalar multiplication preserves the zero relation on both sides.
      simp [tensorBaseChangeRelationToCoconeMap]
  | add w₁ w₂ hw₁ hw₂ =>
      -- Proof comment: both cocone relation transport and scalar multiplication distribute over
      -- sums, so the additive step follows from the induction hypotheses.
      simp [smul_add, map_add, hw₁, hw₂]
  | single z b =>
      -- Proof comment: singleton witnesses stay singleton under both scalar multiplication and
      -- the cocone relation map, so only multiplicativity of the cocone-leg tensor map remains.
      rw [Finsupp.smul_single, tensorBaseChangeRelationToCoconeMap_single,
        tensorBaseChangeRelationToCoconeMap_single]
      have hcoeff :
          fC (a • b) = (fC a) • fC b := by
        exact map_mul fC a b
      calc
        Finsupp.single (fC z) (fC (a • b)) =
            Finsupp.single (fC z) ((fC a) • fC b) := congrArg (Finsupp.single (fC z)) hcoeff
        _ =
            (fC a) •
              Finsupp.single (fC z) (fC b) := by
                symm
                exact Finsupp.smul_single _ _ _
        _ =
            (algebraMap (C₀ ⊗[A₀] ↑(G.obj i)) (C₀ ⊗[A₀] ↑c.cocone.pt) a) •
              Finsupp.single (fC z) (fC b) := by
                rfl

/-- Helper for Chap10 Lemma 10 168 5: sending a stage tensor to a later stage and then to the
cocone point agrees with sending it directly to the cocone point. -/
theorem tensorBaseChangePointToCoconeNaturality
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G)
    (C₀ : Type u) [CommRing C₀] [Algebra A₀ C₀]
    {i j : I} (hij : i ≤ j)
    (z : C₀ ⊗[A₀] G.obj i) :
    (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app j).hom)
        ((Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (G.map (homOfLE hij)).hom) z) =
      (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app i).hom) z := by
  -- Proof comment: this is cocone naturality for the tensor-base-change cocone, proved on pure
  -- tensors and extended by additivity.
  induction z using TensorProduct.induction_on with
  | zero =>
      rw [map_zero, map_zero]
      rfl
  | tmul c₁ r =>
      change c₁ ⊗ₜ[A₀] ((c.cocone.ι.app j).hom (((G.map (homOfLE hij)).hom r))) =
        c₁ ⊗ₜ[A₀] ((c.cocone.ι.app i).hom r)
      congr 1
      exact congrArg (fun f : G.obj i ⟶ c.cocone.pt ↦ f.hom r) (c.cocone.w (homOfLE hij))
  | add z₁ z₂ hz₁ hz₂ =>
      calc
        (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app j).hom)
            ((Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (G.map (homOfLE hij)).hom)
              (z₁ + z₂)) =
          (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app j).hom)
            ((Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (G.map (homOfLE hij)).hom) z₁ +
              (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (G.map (homOfLE hij)).hom) z₂) := by
                rw [map_add]
        _ =
          (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app j).hom)
              ((Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (G.map (homOfLE hij)).hom) z₁) +
            (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app j).hom)
              ((Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (G.map (homOfLE hij)).hom) z₂) := by
                rw [map_add]
        _ =
          (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app i).hom) z₁ +
            (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app i).hom) z₂ := by
                simpa using congrArg₂ HAdd.hAdd hz₁ hz₂
        _ =
          (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app i).hom) (z₁ + z₂) := by
                rw [map_add]

/-- Helper for Chap10 Lemma 10 168 5: an additive `KaehlerDifferential.kerTotal` generator at
the cocone point already comes from a stage generator. -/
theorem tensorBaseChangeAddKerTotalGeneratorDescends
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G)
    (φ₀ : B₀ →ₐ[A₀] C₀) (u v : C₀ ⊗[A₀] c.cocone.pt) :
    ∃ i : I, ∃ w : (C₀ ⊗[A₀] G.obj i) →₀ (C₀ ⊗[A₀] G.obj i),
      letI : Algebra (B₀ ⊗[A₀] G.obj i) (C₀ ⊗[A₀] G.obj i) :=
        (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ (G.obj i))).toRingHom.toAlgebra
      w ∈ KaehlerDifferential.kerTotal (B₀ ⊗[A₀] G.obj i) (C₀ ⊗[A₀] G.obj i) ∧
        tensorBaseChangeRelationToCoconeMap G c C₀ w =
          Finsupp.single u (1 : C₀ ⊗[A₀] c.cocone.pt) +
            Finsupp.single v (1 : C₀ ⊗[A₀] c.cocone.pt) -
            Finsupp.single (u + v) (1 : C₀ ⊗[A₀] c.cocone.pt) := by
  obtain ⟨i, ui, hui⟩ := tensor_base_change_commAlgCocone_forget_jointly_surjective G c C₀ u
  obtain ⟨j, vj, hvj⟩ := tensor_base_change_commAlgCocone_forget_jointly_surjective G c C₀ v
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  let uk : C₀ ⊗[A₀] G.obj k :=
    (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (G.map (homOfLE hik)).hom) ui
  let vk : C₀ ⊗[A₀] G.obj k :=
    (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (G.map (homOfLE hjk)).hom) vj
  let w : (C₀ ⊗[A₀] G.obj k) →₀ (C₀ ⊗[A₀] G.obj k) :=
    Finsupp.single uk (1 : C₀ ⊗[A₀] G.obj k) +
      Finsupp.single vk (1 : C₀ ⊗[A₀] G.obj k) -
      Finsupp.single (uk + vk) (1 : C₀ ⊗[A₀] G.obj k)
  refine ⟨k, w, ?_⟩
  dsimp [w]
  constructor
  · -- Proof comment: the chosen stage relation is literally one of the additive generators
    -- spanning `KaehlerDifferential.kerTotal`.
    rw [KaehlerDifferential.kerTotal]
    exact Submodule.subset_span (Or.inl <| Or.inl <| ⟨⟨uk, vk⟩, rfl⟩)
  · -- Proof comment: cocone naturality identifies the transported stage generators with the
    -- prescribed cocone-point additive generator.
    have huki :
        (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app k).hom) uk =
          (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app i).hom) ui := by
      simpa [uk] using tensorBaseChangePointToCoconeNaturality G c C₀ hik ui
    have huk :
        (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app k).hom) uk = u := by
      exact huki.trans hui.symm
    have hvkj :
        (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app k).hom) vk =
          (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app j).hom) vj := by
      simpa [vk] using tensorBaseChangePointToCoconeNaturality G c C₀ hjk vj
    have hvk :
        (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app k).hom) vk = v := by
      exact hvkj.trans hvj.symm
    rw [sub_eq_add_neg, map_add, map_add, map_neg]
    rw [tensorBaseChangeRelationToCoconeMap_single, tensorBaseChangeRelationToCoconeMap_single,
      tensorBaseChangeRelationToCoconeMap_single]
    rw [huk, hvk]
    have hadd :
        (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app k).hom) (uk + vk) = u + v := by
      rw [map_add, huk, hvk]
      rfl
    rw [hadd]
    have hone :
        (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app k).hom)
            (1 : C₀ ⊗[A₀] G.obj k) =
          (1 : C₀ ⊗[A₀] c.cocone.pt) := by
      exact (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app k).hom).map_one
    rw [hone]
    conv_rhs => rw [sub_eq_add_neg]
    rfl

/-- Helper for Chap10 Lemma 10 168 5: a multiplicative `KaehlerDifferential.kerTotal` generator
at the cocone point already comes from a stage generator. -/
theorem tensorBaseChangeMulKerTotalGeneratorDescends
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G)
    (φ₀ : B₀ →ₐ[A₀] C₀) (u v : C₀ ⊗[A₀] c.cocone.pt) :
    ∃ i : I, ∃ w : (C₀ ⊗[A₀] G.obj i) →₀ (C₀ ⊗[A₀] G.obj i),
      letI : Algebra (B₀ ⊗[A₀] G.obj i) (C₀ ⊗[A₀] G.obj i) :=
        (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ (G.obj i))).toRingHom.toAlgebra
      w ∈ KaehlerDifferential.kerTotal (B₀ ⊗[A₀] G.obj i) (C₀ ⊗[A₀] G.obj i) ∧
        tensorBaseChangeRelationToCoconeMap G c C₀ w =
          Finsupp.single v u + Finsupp.single u v -
            Finsupp.single (u * v) (1 : C₀ ⊗[A₀] c.cocone.pt) := by
  obtain ⟨i, ui, hui⟩ := tensor_base_change_commAlgCocone_forget_jointly_surjective G c C₀ u
  obtain ⟨j, vj, hvj⟩ := tensor_base_change_commAlgCocone_forget_jointly_surjective G c C₀ v
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  let uk : C₀ ⊗[A₀] G.obj k :=
    (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (G.map (homOfLE hik)).hom) ui
  let vk : C₀ ⊗[A₀] G.obj k :=
    (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (G.map (homOfLE hjk)).hom) vj
  let w : (C₀ ⊗[A₀] G.obj k) →₀ (C₀ ⊗[A₀] G.obj k) :=
    Finsupp.single vk uk + Finsupp.single uk vk -
      Finsupp.single (uk * vk) (1 : C₀ ⊗[A₀] G.obj k)
  refine ⟨k, w, ?_⟩
  dsimp [w]
  constructor
  · -- Proof comment: the chosen stage relation is literally one of the multiplicative generators
    -- spanning `KaehlerDifferential.kerTotal`.
    rw [KaehlerDifferential.kerTotal]
    exact Submodule.subset_span (Or.inl <| Or.inr <| ⟨⟨uk, vk⟩, rfl⟩)
  · -- Proof comment: transport the multiplicative generator to the cocone point and rewrite each
    -- stage tensor by cocone naturality.
    have huki :
        (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app k).hom) uk =
          (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app i).hom) ui := by
      simpa [uk] using tensorBaseChangePointToCoconeNaturality G c C₀ hik ui
    have huk :
        (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app k).hom) uk = u := by
      exact huki.trans hui.symm
    have hvkj :
        (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app k).hom) vk =
          (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app j).hom) vj := by
      simpa [vk] using tensorBaseChangePointToCoconeNaturality G c C₀ hjk vj
    have hvk :
        (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app k).hom) vk = v := by
      exact hvkj.trans hvj.symm
    rw [sub_eq_add_neg, map_add, map_add, map_neg]
    rw [tensorBaseChangeRelationToCoconeMap_single, tensorBaseChangeRelationToCoconeMap_single,
      tensorBaseChangeRelationToCoconeMap_single]
    rw [huk, hvk]
    have hmul :
        (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app k).hom) (uk * vk) = u * v := by
      rw [map_mul, huk, hvk]
      rfl
    rw [hmul]
    have hone :
        (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app k).hom)
            (1 : C₀ ⊗[A₀] G.obj k) =
          (1 : C₀ ⊗[A₀] c.cocone.pt) := by
      exact (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app k).hom).map_one
    rw [hone]
    conv_rhs => rw [sub_eq_add_neg]
    rfl

/-- Helper for Chap10 Lemma 10 168 5: applying the stage algebra map and then the cocone leg
agrees with first moving a `B₀`-tensor to the cocone point and then applying the cocone algebra
map. -/
theorem tensorBaseChangeAlgebraMapToCoconeNaturality
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G)
    (φ₀ : B₀ →ₐ[A₀] C₀)
    {i : I} (r : B₀ ⊗[A₀] G.obj i) :
    (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app i).hom)
        ((Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ (G.obj i))) r) =
      (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ c.cocone.pt))
        ((Algebra.TensorProduct.map (AlgHom.id A₀ B₀) (c.cocone.ι.app i).hom) r) := by
  -- Proof comment: both composites are tensor-product algebra maps, so tensor induction reduces
  -- the comparison to the obvious pure-tensor formula.
  induction r using TensorProduct.induction_on with
  | zero =>
      rw [map_zero, map_zero]
      rfl
  | tmul b x =>
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
      rfl
  | add r₁ r₂ hr₁ hr₂ =>
      -- Proof comment: both tensor-product algebra maps preserve addition, so the inductive
      -- hypotheses reduce the additive case to the standard `map_add` identities.
      calc
        (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app i).hom)
            ((Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ (G.obj i))) (r₁ + r₂)) =
          (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app i).hom)
            ((Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ (G.obj i))) r₁ +
              (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ (G.obj i))) r₂) := by
                rw [map_add]
        _ =
          (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app i).hom)
              ((Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ (G.obj i))) r₁) +
            (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app i).hom)
              ((Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ (G.obj i))) r₂) := by
                rw [map_add]
        _ =
          (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ c.cocone.pt))
              ((Algebra.TensorProduct.map (AlgHom.id A₀ B₀) (c.cocone.ι.app i).hom) r₁) +
            (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ c.cocone.pt))
              ((Algebra.TensorProduct.map (AlgHom.id A₀ B₀) (c.cocone.ι.app i).hom) r₂) := by
                simpa using congrArg₂ HAdd.hAdd hr₁ hr₂
        _ =
          (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ c.cocone.pt))
            (((Algebra.TensorProduct.map (AlgHom.id A₀ B₀) (c.cocone.ι.app i).hom) r₁) +
              ((Algebra.TensorProduct.map (AlgHom.id A₀ B₀) (c.cocone.ι.app i).hom) r₂)) := by
              exact
                ((Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ c.cocone.pt)).map_add
                  ((Algebra.TensorProduct.map (AlgHom.id A₀ B₀) (c.cocone.ι.app i).hom) r₁)
                  ((Algebra.TensorProduct.map (AlgHom.id A₀ B₀) (c.cocone.ι.app i).hom) r₂)).symm
        _ =
          (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ c.cocone.pt))
            ((Algebra.TensorProduct.map (AlgHom.id A₀ B₀) (c.cocone.ι.app i).hom) (r₁ + r₂)) := by
              -- Proof comment: the remaining step is exactly `map_add` for the cocone-point
              -- algebra map, after rewriting the inner transition map on `r₁ + r₂`.
              rw [map_add]

/-- Helper for Chap10 Lemma 10 168 5: an `algebraMap` `KaehlerDifferential.kerTotal` generator at
the cocone point already comes from a stage generator. -/

theorem tensorBaseChangeAlgebraMapKerTotalGeneratorDescends
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G)
    (φ₀ : B₀ →ₐ[A₀] C₀) (r : B₀ ⊗[A₀] c.cocone.pt) :
    ∃ i : I, ∃ w : (C₀ ⊗[A₀] G.obj i) →₀ (C₀ ⊗[A₀] G.obj i),
      letI : Algebra (B₀ ⊗[A₀] G.obj i) (C₀ ⊗[A₀] G.obj i) :=
        (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ (G.obj i))).toRingHom.toAlgebra
      w ∈ KaehlerDifferential.kerTotal (B₀ ⊗[A₀] G.obj i) (C₀ ⊗[A₀] G.obj i) ∧
        tensorBaseChangeRelationToCoconeMap G c C₀ w =
          Finsupp.single
            ((Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ c.cocone.pt)) r)
            (1 : C₀ ⊗[A₀] c.cocone.pt) := by
  obtain ⟨i, ri, hri⟩ := tensor_base_change_commAlgCocone_forget_jointly_surjective G c B₀ r
  let wi : C₀ ⊗[A₀] G.obj i :=
    (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ (G.obj i))) ri
  let w : (C₀ ⊗[A₀] G.obj i) →₀ (C₀ ⊗[A₀] G.obj i) :=
    Finsupp.single wi (1 : C₀ ⊗[A₀] G.obj i)
  refine ⟨i, w, ?_⟩
  dsimp [w, wi]
  constructor
  · -- Proof comment: the chosen singleton witness is exactly one of the `algebraMap` generators
    -- spanning `KaehlerDifferential.kerTotal`.
    rw [KaehlerDifferential.kerTotal]
    exact Submodule.subset_span (Or.inr <| ⟨ri, rfl⟩)
  · -- Proof comment: the new bridge lemma identifies the cocone image of the chosen stage
    -- generator with the requested cocone-point `algebraMap` generator.
    rw [tensorBaseChangeRelationToCoconeMap_single]
    rw [tensorBaseChangeAlgebraMapToCoconeNaturality G c φ₀ ri, hri]
    have hone :
        (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app i).hom)
            (1 : C₀ ⊗[A₀] G.obj i) =
          (1 : C₀ ⊗[A₀] c.cocone.pt) := by
      exact (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app i).hom).map_one
    rw [hone]
    rfl

/-- Helper for Chap10 Lemma 10 168 5: any cocone-point relation lying in
`KaehlerDifferential.kerTotal` already comes from some stage relation lying in the corresponding
stage `KaehlerDifferential.kerTotal`. -/
theorem tensorBaseChangeKerTotalWitnessDescends
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G)
    (φ₀ : B₀ →ₐ[A₀] C₀)
    (wInf : (C₀ ⊗[A₀] c.cocone.pt) →₀ (C₀ ⊗[A₀] c.cocone.pt))
    (hwInf :
      letI : Algebra (B₀ ⊗[A₀] c.cocone.pt) (C₀ ⊗[A₀] c.cocone.pt) :=
        (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ c.cocone.pt)).toRingHom.toAlgebra
      wInf ∈ KaehlerDifferential.kerTotal (B₀ ⊗[A₀] c.cocone.pt) (C₀ ⊗[A₀] c.cocone.pt)) :
    ∃ i : I, ∃ w : (C₀ ⊗[A₀] G.obj i) →₀ (C₀ ⊗[A₀] G.obj i),
      letI : Algebra (B₀ ⊗[A₀] G.obj i) (C₀ ⊗[A₀] G.obj i) :=
        (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ (G.obj i))).toRingHom.toAlgebra
      w ∈ KaehlerDifferential.kerTotal (B₀ ⊗[A₀] G.obj i) (C₀ ⊗[A₀] G.obj i) ∧
        tensorBaseChangeRelationToCoconeMap G c C₀ w = wInf := by
  classical
  letI : Algebra (B₀ ⊗[A₀] c.cocone.pt) (C₀ ⊗[A₀] c.cocone.pt) :=
    (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ c.cocone.pt)).toRingHom.toAlgebra
  rw [KaehlerDifferential.kerTotal] at hwInf
  -- Proof comment: `kerTotal` is the span of the three standard generator families, so span
  -- induction reduces the descent problem to those generators and the submodule operations.
  induction hwInf using Submodule.span_induction with
  | mem y hy =>
      rcases hy with hy | hy
      · rcases hy with hy | hy
        · rcases hy with ⟨⟨u, v⟩, rfl⟩
          exact tensorBaseChangeAddKerTotalGeneratorDescends G c φ₀ u v
        · rcases hy with ⟨⟨u, v⟩, rfl⟩
          exact tensorBaseChangeMulKerTotalGeneratorDescends G c φ₀ u v
      · rcases hy with ⟨r, rfl⟩
        exact tensorBaseChangeAlgebraMapKerTotalGeneratorDescends G c φ₀ r
  | zero =>
      refine ⟨Classical.arbitrary I, 0, ?_⟩
      constructor
      · rw [KaehlerDifferential.kerTotal]
        exact Submodule.zero_mem _
      · simp
  | add x y hx hy hxDesc hyDesc =>
      rcases hxDesc with ⟨i, wi, hwiKer, hwiMap⟩
      rcases hyDesc with ⟨j, wj, hwjKer, hwjMap⟩
      obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
      let wik : (C₀ ⊗[A₀] G.obj k) →₀ (C₀ ⊗[A₀] G.obj k) :=
        tensorBaseChangeRelationMap G C₀ hik wi
      let wjk : (C₀ ⊗[A₀] G.obj k) →₀ (C₀ ⊗[A₀] G.obj k) :=
        tensorBaseChangeRelationMap G C₀ hjk wj
      refine ⟨k, wik + wjk, ?_⟩
      letI : Algebra (B₀ ⊗[A₀] G.obj k) (C₀ ⊗[A₀] G.obj k) :=
        (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ (G.obj k))).toRingHom.toAlgebra
      constructor
      · have hwikKer :
            wik ∈ KaehlerDifferential.kerTotal (B₀ ⊗[A₀] G.obj k) (C₀ ⊗[A₀] G.obj k) := by
          simpa [wik] using tensorBaseChangeKerTotalTransition G φ₀ hik hwiKer
        have hwjkKer :
            wjk ∈ KaehlerDifferential.kerTotal (B₀ ⊗[A₀] G.obj k) (C₀ ⊗[A₀] G.obj k) := by
          simpa [wjk] using tensorBaseChangeKerTotalTransition G φ₀ hjk hwjKer
        exact Submodule.add_mem _ hwikKer hwjkKer
      · calc
          tensorBaseChangeRelationToCoconeMap G c C₀ (wik + wjk) =
              tensorBaseChangeRelationToCoconeMap G c C₀ wik +
                tensorBaseChangeRelationToCoconeMap G c C₀ wjk := by
                  simp [map_add]
          _ =
              tensorBaseChangeRelationToCoconeMap G c C₀ wi +
                tensorBaseChangeRelationToCoconeMap G c C₀ wj := by
                  rw [tensorBaseChangeRelationToCoconeMap_comp_transition,
                    tensorBaseChangeRelationToCoconeMap_comp_transition]
          _ = x + y := by rw [hwiMap, hwjMap]
  | smul a x hx hxDesc =>
      rcases hxDesc with ⟨i, wi, hwiKer, hwiMap⟩
      obtain ⟨j, aj, haj⟩ := tensor_base_change_commAlgCocone_forget_jointly_surjective G c C₀ a
      obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
      let wik : (C₀ ⊗[A₀] G.obj k) →₀ (C₀ ⊗[A₀] G.obj k) :=
        tensorBaseChangeRelationMap G C₀ hik wi
      let ak : C₀ ⊗[A₀] G.obj k :=
        (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (G.map (homOfLE hjk)).hom) aj
      refine ⟨k, ak • wik, ?_⟩
      letI : Algebra (B₀ ⊗[A₀] G.obj k) (C₀ ⊗[A₀] G.obj k) :=
        (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ (G.obj k))).toRingHom.toAlgebra
      letI : Algebra (C₀ ⊗[A₀] G.obj k) (C₀ ⊗[A₀] c.cocone.pt) :=
        (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app k).hom).toRingHom.toAlgebra
      constructor
      · have hwikKer :
            wik ∈ KaehlerDifferential.kerTotal (B₀ ⊗[A₀] G.obj k) (C₀ ⊗[A₀] G.obj k) := by
          simpa [wik] using tensorBaseChangeKerTotalTransition G φ₀ hik hwiKer
        exact Submodule.smul_mem _ ak hwikKer
      · have hakj :
            (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app k).hom) ak =
              (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app j).hom) aj := by
          simpa [ak] using tensorBaseChangePointToCoconeNaturality G c C₀ hjk aj
        have hak :
            (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app k).hom) ak = a := by
          exact hakj.trans haj.symm
        calc
          tensorBaseChangeRelationToCoconeMap G c C₀ (ak • wik) =
              (algebraMap (C₀ ⊗[A₀] G.obj k) (C₀ ⊗[A₀] c.cocone.pt) ak) •
                tensorBaseChangeRelationToCoconeMap G c C₀ wik := by
                  simpa [wik] using tensorBaseChangeRelationToCoconeMap_smul G c C₀ ak wik
          _ =
              (algebraMap (C₀ ⊗[A₀] G.obj k) (C₀ ⊗[A₀] c.cocone.pt) ak) •
                tensorBaseChangeRelationToCoconeMap G c C₀ wi := by
                  rw [tensorBaseChangeRelationToCoconeMap_comp_transition]
          _ = a • tensorBaseChangeRelationToCoconeMap G c C₀ wi := by
                simpa using congrArg
                  (fun t : C₀ ⊗[A₀] c.cocone.pt ↦
                    t • tensorBaseChangeRelationToCoconeMap G c C₀ wi) hak
          _ = a • x := by rw [hwiMap]

/-- Helper for Chap10 Lemma 10 168 5: stage-point transport along the directed tensor-base-change
diagram composes exactly along comparable indices. -/
theorem tensorBaseChangePointMap_comp_transition
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (C₀ : Type u) [CommRing C₀] [Algebra A₀ C₀]
    {i j k : I} (hij : i ≤ j) (hjk : j ≤ k)
    (z : C₀ ⊗[A₀] G.obj i) :
    (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (G.map (homOfLE hjk)).hom)
        ((Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (G.map (homOfLE hij)).hom) z) =
      (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (G.map (homOfLE (hij.trans hjk))).hom) z := by
  -- Proof comment: this is tensor-product functoriality for the transition maps, proved directly
  -- on pure tensors and extended by additivity.
  induction z using TensorProduct.induction_on with
  | zero =>
      rw [map_zero, map_zero]
      rfl
  | tmul c r =>
      change c ⊗ₜ[A₀] ((G.map (homOfLE hjk)).hom (((G.map (homOfLE hij)).hom) r)) =
        c ⊗ₜ[A₀] ((G.map (homOfLE (hij.trans hjk))).hom r)
      congr 1
      simpa using congrArg (fun f : G.obj i ⟶ G.obj k ↦ f.hom r)
        (G.map_comp (homOfLE hij) (homOfLE hjk)).symm
  | add z₁ z₂ hz₁ hz₂ =>
      simp [map_add, hz₁, hz₂]

/-- Helper for Chap10 Lemma 10 168 5: sending a stage tensor to a later stage and then to the
cocone point agrees with sending it directly to the cocone point. -/
theorem tensorBaseChangePointToCocone_comp_transition
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G)
    (C₀ : Type u) [CommRing C₀] [Algebra A₀ C₀]
    {i j : I} (hij : i ≤ j)
    (z : C₀ ⊗[A₀] G.obj i) :
    (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app j).hom)
        ((Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (G.map (homOfLE hij)).hom) z) =
      (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app i).hom) z := by
  exact tensorBaseChangePointToCoconeNaturality G c C₀ hij z

/-- Helper for Chap10 Lemma 10 168 5: once a directed diagram is viewed through its chosen
canonical colimit, the unique comparison isomorphism to any other colimit cocone carries the
canonical stage leg to the given cocone leg. -/
theorem tensorBaseChangeChosenColimit_leg
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) [HasColimit G]
    (c : ColimitCocone G) {i : I} :
    colimit.ι G i ≫ ((colimit.isColimit G).coconePointUniqueUpToIso c.isColimit).hom =
      c.cocone.ι.app i := by
  let _ : SmallCategory I := inferInstance
  let _ : IsFiltered I := CategoryTheory.isFiltered_of_directed_le_nonempty I
  -- Proof comment: this is exactly the `fac` computation for the colimit desc map underlying the
  -- uniqueness isomorphism from the chosen colimit point to `c.cocone.pt`.
  exact (colimit.isColimit G).fac c.cocone i

/-- Helper for Chap10 Lemma 10 168 5: on underlying `AlgHom`s, the chosen-colimit comparison
identifies the canonical stage map with the supplied cocone leg. -/
theorem tensorBaseChangeChosenColimit_leg_hom
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) [HasColimit G]
    (c : ColimitCocone G) {i : I} :
    (((colimit.isColimit G).coconePointUniqueUpToIso c.isColimit).hom).hom.comp
        (colimit.ι G i).hom =
      (c.cocone.ι.app i).hom := by
  let _ : SmallCategory I := inferInstance
  let _ : IsFiltered I := CategoryTheory.isFiltered_of_directed_le_nonempty I
  -- Proof comment: this is the previous cocone-leg comparison rewritten on the underlying
  -- `AlgHom`s, which is the stable form needed for tensor-map transport.
  ext x
  exact congrArg
    (fun f : G.obj i ⟶ c.cocone.pt ↦ f.hom x)
    (tensorBaseChangeChosenColimit_leg (A₀ := A₀) G c (i := i))

/-- Helper for Chap10 Lemma 10 168 5: in the literal tensor-stage filtered colimit, equality at
one source stage descends after one later transition. -/
lemma literalTensorStageEqDescends
    {J : Type v} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommAlgCat.{u} A₀) [HasColimit F]
    (S : Type u) [CommRing S] [Algebra A₀ S]
    {j₀ : J}
    (x y : S ⊗[A₀] ((F.obj j₀ : CommAlgCat A₀) : Type u))
    (h :
      (Algebra.TensorProduct.map (AlgHom.id A₀ S) (colimit.ι F j₀).hom) x =
        (Algebra.TensorProduct.map (AlgHom.id A₀ S) (colimit.ι F j₀).hom) y) :
    ∃ (j : J) (f : j₀ ⟶ j),
        (Algebra.TensorProduct.map (AlgHom.id A₀ S) (F.map f).hom) x =
        (Algebra.TensorProduct.map (AlgHom.id A₀ S) (F.map f).hom) y := by
  let D' := tensor_base_change_diagram (A := A₀) (J := J) F S
  let c' : Cocone D' := tensor_base_change_cocone (A := A₀) (J := J) F S
  have hc : IsColimit c' := tensor_base_change_cocone_isColimit (A := A₀) (J := J) F S
  -- Proof comment: the literal tensor cocone is already a filtered colimit in `CommRingCat`, so
  -- equality at the colimit point descends directly to equality after one later transition.
  obtain ⟨j, f, hf⟩ :=
    commRing_largeFilteredColimit_forget_eq_descends hc x y (by
      -- Proof comment: rewrite the tensor equality as equality after applying the corresponding
      -- cocone leg in the forgotten ring diagram.
      simpa [c', D', tensor_base_change_cocone, tensor_base_change_diagram] using h)
  refine ⟨j, f, ?_⟩
  -- Proof comment: after unfolding the literal tensor-stage diagram map, the descended equality is
  -- exactly the desired equality after tensoring the transition map `F.map f`.
  simpa [D', tensor_base_change_diagram] using hf

/-- Helper for Chap10 Lemma 10 168 5: an equality transported to an arbitrary colimit cocone can
be rewritten back to the chosen colimit legs of the directed diagram. -/
lemma tensorBaseChangeChosenColimit_eq_of_coconeEq
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) [HasColimit G]
    (c : ColimitCocone G)
    (C₀ : Type u) [CommRing C₀] [Algebra A₀ C₀]
    {i : I} {z z' : C₀ ⊗[A₀] G.obj i}
    (hzz' :
      (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app i).hom) z =
        (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app i).hom) z') :
    (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (colimit.ι G i).hom) z =
      (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (colimit.ι G i).hom) z' := by
  let _ : SmallCategory I := inferInstance
  let _ : IsFiltered I := CategoryTheory.isFiltered_of_directed_le_nonempty I
  let e := (colimit.isColimit G).coconePointUniqueUpToIso c.isColimit
  have hleg :
      ∀ w : C₀ ⊗[A₀] G.obj i,
        (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) e.hom.hom)
            ((Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (colimit.ι G i).hom) w) =
          (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app i).hom) w := by
    intro w
    -- Proof comment: on pure tensors, the comparison isomorphism turns the chosen colimit leg
    -- into the supplied cocone leg, and additivity extends that identity to all tensors.
    induction w using TensorProduct.induction_on with
    | zero =>
        simpa using (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) e.hom.hom).map_zero
    | tmul c' r =>
        change c' ⊗ₜ[A₀]
            ((((e.hom).hom).comp (colimit.ι G i).hom) r) =
          c' ⊗ₜ[A₀] ((c.cocone.ι.app i).hom r)
        congr 1
        exact DFunLike.congr_fun
          (tensorBaseChangeChosenColimit_leg_hom (A₀ := A₀) G c (i := i)) r
    | add w₁ w₂ hw₁ hw₂ =>
        have hinner :
            (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) e.hom.hom)
                ((Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (colimit.ι G i).hom) (w₁ + w₂)) =
              (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) e.hom.hom)
                ((Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (colimit.ι G i).hom) w₁ +
                  (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (colimit.ι G i).hom) w₂) := by
          exact congrArg
            (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) e.hom.hom)
            ((Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (colimit.ι G i).hom).map_add w₁ w₂)
        calc
          (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) e.hom.hom)
              ((Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (colimit.ι G i).hom) (w₁ + w₂)) =
            (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) e.hom.hom)
              ((Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (colimit.ι G i).hom) w₁ +
                (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (colimit.ι G i).hom) w₂) := hinner
          _ =
            (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) e.hom.hom)
                ((Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (colimit.ι G i).hom) w₁) +
              (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) e.hom.hom)
                ((Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (colimit.ι G i).hom) w₂) := by
                  exact (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) e.hom.hom).map_add _ _
          _ =
            (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app i).hom) w₁ +
              (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app i).hom) w₂ := by
                  simpa using congrArg₂ HAdd.hAdd hw₁ hw₂
          _ =
            (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app i).hom) (w₁ + w₂) := by
                  symm
                  exact (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app i).hom).map_add _ _
  have hcancel :
      ∀ w : C₀ ⊗[A₀] (colimit G : CommAlgCat.{u} A₀),
        (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) e.inv.hom)
            ((Algebra.TensorProduct.map (AlgHom.id A₀ C₀) e.hom.hom) w) = w := by
    intro w
    -- Proof comment: tensoring with the inverse of the comparison isomorphism cancels the
    -- tensoring with its forward map because `e.hom ≫ e.inv = 𝟙`.
    induction w using TensorProduct.induction_on with
    | zero =>
        have hzero :
            (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) e.inv.hom)
                ((Algebra.TensorProduct.map (AlgHom.id A₀ C₀) e.hom.hom) 0) =
              (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) e.inv.hom) 0 := by
          exact congrArg
            (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) e.inv.hom)
            ((Algebra.TensorProduct.map (AlgHom.id A₀ C₀) e.hom.hom).map_zero)
        calc
          (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) e.inv.hom)
              ((Algebra.TensorProduct.map (AlgHom.id A₀ C₀) e.hom.hom) 0) =
            (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) e.inv.hom) 0 := hzero
          _ = 0 := (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) e.inv.hom).map_zero
    | tmul c' r =>
        change c' ⊗ₜ[A₀] (((e.inv).hom.comp (e.hom).hom) r) = c' ⊗ₜ[A₀] r
        congr 1
        exact congrArg (fun f : (colimit G : CommAlgCat.{u} A₀) ⟶ (colimit G : CommAlgCat.{u} A₀) ↦
            f.hom r) e.hom_inv_id
    | add w₁ w₂ hw₁ hw₂ =>
        have hinner :
            (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) e.inv.hom)
                ((Algebra.TensorProduct.map (AlgHom.id A₀ C₀) e.hom.hom) (w₁ + w₂)) =
              (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) e.inv.hom)
                ((Algebra.TensorProduct.map (AlgHom.id A₀ C₀) e.hom.hom) w₁ +
                  (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) e.hom.hom) w₂) := by
          exact congrArg
            (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) e.inv.hom)
            ((Algebra.TensorProduct.map (AlgHom.id A₀ C₀) e.hom.hom).map_add w₁ w₂)
        calc
          (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) e.inv.hom)
              ((Algebra.TensorProduct.map (AlgHom.id A₀ C₀) e.hom.hom) (w₁ + w₂)) =
            (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) e.inv.hom)
              ((Algebra.TensorProduct.map (AlgHom.id A₀ C₀) e.hom.hom) w₁ +
                (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) e.hom.hom) w₂) := hinner
          _ =
            (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) e.inv.hom)
                ((Algebra.TensorProduct.map (AlgHom.id A₀ C₀) e.hom.hom) w₁) +
              (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) e.inv.hom)
                ((Algebra.TensorProduct.map (AlgHom.id A₀ C₀) e.hom.hom) w₂) := by
                  exact (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) e.inv.hom).map_add _ _
          _ = w₁ + w₂ := by
                simpa using congrArg₂ HAdd.hAdd hw₁ hw₂
  have hchosen :
      (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) e.hom.hom)
          ((Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (colimit.ι G i).hom) z) =
        (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) e.hom.hom)
          ((Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (colimit.ι G i).hom) z') :=
    (hleg z).trans ((hzz').trans (hleg z').symm)
  -- Proof comment: apply the tensor map of the inverse comparison isomorphism to return from the
  -- arbitrary cocone point to the chosen colimit point.
  have happly :=
    congrArg (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) e.inv.hom) hchosen
  exact
    (hcancel ((Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (colimit.ι G i).hom) z)).symm.trans
      (happly.trans
        (hcancel ((Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (colimit.ι G i).hom) z')))

theorem tensorBaseChangePointEventuallyEqOfCoconeEq
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G)
    (C₀ : Type u) [CommRing C₀] [Algebra A₀ C₀]
    {i : I} {z z' : C₀ ⊗[A₀] G.obj i}
    (hzz' :
      (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app i).hom) z =
        (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app i).hom) z') :
    ∃ j : I, ∃ hij : i ≤ j,
      (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (G.map (homOfLE hij)).hom) z =
        (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (G.map (homOfLE hij)).hom) z' := by
  let _ : SmallCategory I := inferInstance
  let _ : IsFiltered I := CategoryTheory.isFiltered_of_directed_le_nonempty I
  let _ : HasColimit G := HasColimit.mk c
  have hchosen :
      (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (colimit.ι G i).hom) z =
        (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (colimit.ι G i).hom) z' :=
    tensorBaseChangeChosenColimit_eq_of_coconeEq (A₀ := A₀) G c C₀ hzz'
  -- Route correction: isolate the cocone-leg transport through the comparison isomorphism, then
  -- reuse the filtered literal tensor-stage descent theorem on the chosen colimit.
  -- Proof comment: once the equality is rewritten at the chosen colimit point, the filtered
  -- equality-descent lemma produces a later stage where the two tensors already coincide.
  obtain ⟨j, f, hf⟩ := literalTensorStageEqDescends (A₀ := A₀) G C₀ z z' hchosen
  refine ⟨j, leOfHom f, ?_⟩
  -- Proof comment: in a preorder category every morphism is the canonical `homOfLE`, so the
  -- descended equality already has the required target shape.
  simpa [homOfLE_leOfHom] using hf

/-- Helper for Chap10 Lemma 10 168 5: the support of a transported stage relation is contained in
the image of the original finite support under the underlying tensor-stage map. -/
theorem support_tensorBaseChangeRelationMap_subset_image
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (C₀ : Type u) [CommRing C₀] [Algebra A₀ C₀]
    {i j : I} (h : i ≤ j)
    [DecidableEq (C₀ ⊗[A₀] G.obj j)]
    (w : (C₀ ⊗[A₀] G.obj i) →₀ (C₀ ⊗[A₀] G.obj i)) :
    (tensorBaseChangeRelationMap G C₀ h w).support ⊆
      w.support.image
        ((Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (G.map (homOfLE h)).hom)) := by
  -- Proof comment: `mapRange` cannot create new support points, and `mapDomain` only supports
  -- values in the image of the original support.
  rw [tensorBaseChangeRelationMap_def]
  exact Set.Subset.trans Finsupp.support_mapRange Finsupp.mapDomain_support

open scoped Classical in
/-- Helper for Chap10 Lemma 10 168 5: once cocone-equal support points have been synchronized at
one stage, the stage fiber over `z` agrees with the cocone fiber over `z`. -/
theorem tensorBaseChangeRelationFiberFilter_eq_coconeFiberFilter
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G)
    (C₀ : Type u) [CommRing C₀] [Algebra A₀ C₀]
    {i j : I} (hij : i ≤ j)
    (w : (C₀ ⊗[A₀] G.obj i) →₀ (C₀ ⊗[A₀] G.obj i))
    (hpair :
      ∀ ⦃a b : C₀ ⊗[A₀] G.obj i⦄,
        a ∈ w.support → b ∈ w.support →
          (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app i).hom) a =
            (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app i).hom) b →
          (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (G.map (homOfLE hij)).hom) a =
            (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (G.map (homOfLE hij)).hom) b) :
    ∀ z ∈ w.support,
      w.support.filter
          (fun a ↦
            (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (G.map (homOfLE hij)).hom) a =
              (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (G.map (homOfLE hij)).hom) z) =
        w.support.filter
          (fun a ↦
            (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app i).hom) a =
              (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app i).hom) z) := by
  classical
  intro z hz
  -- Proof comment: compare the two finite support fibers pointwise. Equality at the later stage
  -- implies equality at the cocone point by cocone naturality, and `hpair` gives the converse.
  apply Finset.ext
  intro a
  constructor
  · intro ha
    rw [Finset.mem_filter] at ha
    rw [Finset.mem_filter]
    rcases ha with ⟨ha_mem, ha_eq⟩
    refine ⟨ha_mem, ?_⟩
    have hnatA :
        (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app j).hom)
            ((Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (G.map (homOfLE hij)).hom) a) =
          (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app i).hom) a :=
      tensorBaseChangePointToCoconeNaturality G c C₀ hij a
    have hnatZ :
        (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app j).hom)
            ((Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (G.map (homOfLE hij)).hom) z) =
          (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app i).hom) z :=
      tensorBaseChangePointToCoconeNaturality G c C₀ hij z
    exact hnatA.symm.trans <|
      (congrArg
        (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app j).hom) ha_eq).trans hnatZ
  · intro ha
    rw [Finset.mem_filter] at ha
    rw [Finset.mem_filter]
    rcases ha with ⟨ha_mem, ha_eq⟩
    refine ⟨ha_mem, ?_⟩
    exact hpair ha_mem hz ha_eq

/-- Helper for Chap10 Lemma 10 168 5: if a stage relation has cocone image `0`, then after some
later transition the transported relation is literally zero. -/
theorem tensorBaseChangeRelationEventuallyZeroOfCoconeZero
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G)
    (C₀ : Type u) [CommRing C₀] [Algebra A₀ C₀]
    {i : I}
    (w : (C₀ ⊗[A₀] G.obj i) →₀ (C₀ ⊗[A₀] G.obj i))
    (hw : tensorBaseChangeRelationToCoconeMap G c C₀ w = 0) :
    ∃ j : I, ∃ hij : i ≤ j,
      tensorBaseChangeRelationMap G C₀ hij w = 0 := by
  classical
  let supportPairs : Finset ((C₀ ⊗[A₀] G.obj i) × (C₀ ⊗[A₀] G.obj i)) :=
    w.support.product w.support
  let coconePointMap :
      C₀ ⊗[A₀] G.obj i →ₐ[A₀] C₀ ⊗[A₀] c.cocone.pt :=
    Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app i).hom
  let coeffOnCoconeFiber (z : C₀ ⊗[A₀] G.obj i) : C₀ ⊗[A₀] G.obj i :=
    ∑ a ∈ w.support.filter (fun a ↦ coconePointMap a = coconePointMap z), w a
  have hpairWitness :
      ∀ p ∈ supportPairs, ∃ j : I, ∃ hij : i ≤ j,
        (coconePointMap p.1 = coconePointMap p.2 →
          (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (G.map (homOfLE hij)).hom) p.1 =
            (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (G.map (homOfLE hij)).hom) p.2) := by
    intro p hp
    rcases Finset.mem_product.mp hp with ⟨hp₁, hp₂⟩
    by_cases hpEq : coconePointMap p.1 = coconePointMap p.2
    · obtain ⟨j, hij, hdesc⟩ :=
        tensorBaseChangePointEventuallyEqOfCoconeEq G c C₀ hpEq
      exact ⟨j, hij, fun _ ↦ hdesc⟩
    · exact ⟨i, le_rfl, fun hEq ↦ False.elim (hpEq hEq)⟩
  choose pairStage pairLe pairEq using hpairWitness
  have hzeroWitness :
      ∀ z ∈ w.support, ∃ j : I, ∃ hij : i ≤ j,
        (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (G.map (homOfLE hij)).hom)
          (coeffOnCoconeFiber z) = 0 := by
    intro z hz
    have happlyZero :
        tensorBaseChangeRelationToCoconeMap G c C₀ w (coconePointMap z) = 0 := by
      exact congrArg (fun r : (C₀ ⊗[A₀] c.cocone.pt) →₀ (C₀ ⊗[A₀] c.cocone.pt) ↦
        r (coconePointMap z)) hw
    have hcoeffZeroAtCocone :
        coconePointMap (coeffOnCoconeFiber z) = 0 := by
      -- Proof comment: evaluating the cocone relation at the image of `z` rewrites to the cocone
      -- image of the coefficient sum over the cocone fiber of `z`.
      have happlyZero' :
          tensorBaseChangeRelationToCoconeMap G c C₀ w
              ((Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app i).hom) z) = 0 := by
        simpa [coconePointMap] using happlyZero
      rw [tensorBaseChangeRelationToCoconeMap_apply_eq_sum] at happlyZero'
      unfold coeffOnCoconeFiber
      rw [map_sum] at happlyZero'
      simpa [coconePointMap] using happlyZero'
    have hcoeffEq :
        coconePointMap (coeffOnCoconeFiber z) =
          coconePointMap (0 : C₀ ⊗[A₀] G.obj i) := by
      simpa [coconePointMap] using hcoeffZeroAtCocone
    obtain ⟨j, hij, hdesc⟩ :=
      tensorBaseChangePointEventuallyEqOfCoconeEq G c C₀ hcoeffEq
    exact ⟨j, hij, by simpa using hdesc⟩
  choose zeroStage zeroLe zeroEq using hzeroWitness
  let allStages : Finset I :=
    ({i} : Finset I) ∪
      ((supportPairs.attach).image (fun p ↦ pairStage p.1 p.2) ∪
        (w.support.attach).image (fun z ↦ zeroStage z.1 z.2))
  obtain ⟨j, hjAll⟩ := directed_finset_common_upper_bound allStages
  have hij : i ≤ j := by
    exact hjAll i (by simp [allStages])
  have hpairUpper :
      ∀ p : {p // p ∈ supportPairs}, pairStage p.1 p.2 ≤ j := by
    intro p
    exact hjAll (pairStage p.1 p.2) (by
      simp [allStages, Finset.mem_image])
  have hzeroUpper :
      ∀ z : {z // z ∈ w.support}, zeroStage z.1 z.2 ≤ j := by
    intro z
    exact hjAll (zeroStage z.1 z.2) (by
      simp [allStages, Finset.mem_image])
  have hpairSync :
      ∀ ⦃a b : C₀ ⊗[A₀] G.obj i⦄,
        a ∈ w.support → b ∈ w.support →
          coconePointMap a = coconePointMap b →
          (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (G.map (homOfLE hij)).hom) a =
            (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (G.map (homOfLE hij)).hom) b := by
    intro a b ha hb hab
    let p : {p // p ∈ supportPairs} := ⟨(a, b), by simp [supportPairs, ha, hb]⟩
    have habStage :
        (Algebra.TensorProduct.map
            (AlgHom.id A₀ C₀) (G.map (homOfLE (pairLe p.1 p.2))).hom) a =
          (Algebra.TensorProduct.map
            (AlgHom.id A₀ C₀) (G.map (homOfLE (pairLe p.1 p.2))).hom) b :=
      pairEq p.1 p.2 hab
    have hmap :=
      congrArg
        (Algebra.TensorProduct.map
          (AlgHom.id A₀ C₀) (G.map (homOfLE (hpairUpper p))).hom)
        habStage
    have hproof : (pairLe p.1 p.2).trans (hpairUpper p) = hij := Subsingleton.elim _ _
    calc
      (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (G.map (homOfLE hij)).hom) a =
          (Algebra.TensorProduct.map
            (AlgHom.id A₀ C₀) (G.map (homOfLE (hpairUpper p))).hom)
            ((Algebra.TensorProduct.map
              (AlgHom.id A₀ C₀) (G.map (homOfLE (pairLe p.1 p.2))).hom) a) := by
                simpa [hproof] using
                  (tensorBaseChangePointMap_comp_transition G C₀
                    (pairLe p.1 p.2) (hpairUpper p) a).symm
      _ =
          (Algebra.TensorProduct.map
            (AlgHom.id A₀ C₀) (G.map (homOfLE (hpairUpper p))).hom)
            ((Algebra.TensorProduct.map
              (AlgHom.id A₀ C₀) (G.map (homOfLE (pairLe p.1 p.2))).hom) b) := hmap
      _ =
          (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (G.map (homOfLE hij)).hom) b := by
            simpa [hproof] using
              (tensorBaseChangePointMap_comp_transition G C₀
                (pairLe p.1 p.2) (hpairUpper p) b)
  have hcoeffZeroAtStage :
      ∀ z ∈ w.support,
        (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (G.map (homOfLE hij)).hom)
          (coeffOnCoconeFiber z) = 0 := by
    intro z hz
    let z' : {z // z ∈ w.support} := ⟨z, hz⟩
    have hproof : (zeroLe z z'.2).trans (hzeroUpper z') = hij := by
      exact Subsingleton.elim _ _
    calc
      (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (G.map (homOfLE hij)).hom)
          (coeffOnCoconeFiber z) =
        (Algebra.TensorProduct.map
          (AlgHom.id A₀ C₀) (G.map (homOfLE (hzeroUpper z'))).hom)
          ((Algebra.TensorProduct.map
            (AlgHom.id A₀ C₀) (G.map (homOfLE (zeroLe z z'.2))).hom)
            (coeffOnCoconeFiber z)) := by
              simpa [hproof] using
                (tensorBaseChangePointMap_comp_transition G C₀
                  (zeroLe z z'.2) (hzeroUpper z') (coeffOnCoconeFiber z)).symm
      _ = 0 := by
            simpa using congrArg
              (Algebra.TensorProduct.map
                (AlgHom.id A₀ C₀) (G.map (homOfLE (hzeroUpper z'))).hom)
              (zeroEq z z'.2)
  refine ⟨j, hij, ?_⟩
  ext y
  by_cases hy :
      y ∈ w.support.image
        ((Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (G.map (homOfLE hij)).hom))
  · rcases Finset.mem_image.mp hy with ⟨z, hz, rfl⟩
    have hfiberEq :=
      tensorBaseChangeRelationFiberFilter_eq_coconeFiberFilter G c C₀ hij w hpairSync z hz
    calc
      tensorBaseChangeRelationMap G C₀ hij w
          ((Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (G.map (homOfLE hij)).hom) z) =
        (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (G.map (homOfLE hij)).hom)
          (∑ a ∈ w.support.filter
              (fun a ↦
                (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (G.map (homOfLE hij)).hom) a =
                  (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (G.map (homOfLE hij)).hom) z),
            w a) := by
              simpa using tensorBaseChangeRelationMap_apply_eq_sum G C₀ hij w z
      _ =
        (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (G.map (homOfLE hij)).hom)
          (coeffOnCoconeFiber z) := by
            simpa [coeffOnCoconeFiber] using congrArg
              (fun s : Finset (C₀ ⊗[A₀] G.obj i) ↦
                Finset.sum s fun a ↦
                  (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (G.map (homOfLE hij)).hom)
                    (w a))
              hfiberEq
      _ = 0 := hcoeffZeroAtStage z hz
  · have hySupport :
        y ∉ (tensorBaseChangeRelationMap G C₀ hij w).support := by
      intro hy'
      exact hy
        (support_tensorBaseChangeRelationMap_subset_image G C₀ hij w hy')
    exact Finsupp.notMem_support_iff.mp hySupport

/-- Helper for Chap10 Lemma 10 168 5: if a stage relation maps to the cocone singleton for
`x ⊗ₜ[A₀] 1`, then after some later transition it becomes the literal singleton relation. -/
theorem tensorBaseChangeRelationEventuallySingletonOfCoconeSingleton
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G)
    (C₀ : Type u) [CommRing C₀] [Algebra A₀ C₀]
    {i : I} (x : C₀)
    (w : (C₀ ⊗[A₀] G.obj i) →₀ (C₀ ⊗[A₀] G.obj i))
    (hw :
      tensorBaseChangeRelationToCoconeMap G c C₀ w =
        Finsupp.single (x ⊗ₜ[A₀] (1 : c.cocone.pt)) (1 : C₀ ⊗[A₀] c.cocone.pt)) :
    ∃ j : I, ∃ hij : i ≤ j,
      tensorBaseChangeRelationMap G C₀ hij w =
        Finsupp.single (x ⊗ₜ[A₀] (1 : G.obj j)) (1 : C₀ ⊗[A₀] G.obj j) := by
  let w' : (C₀ ⊗[A₀] G.obj i) →₀ (C₀ ⊗[A₀] G.obj i) :=
    w - Finsupp.single (x ⊗ₜ[A₀] (1 : G.obj i)) (1 : C₀ ⊗[A₀] G.obj i)
  have hw' :
      tensorBaseChangeRelationToCoconeMap G c C₀ w' = 0 := by
    -- Proof comment: subtract the literal singleton stage relation whose cocone image is the
    -- prescribed singleton relation, so the new cocone relation vanishes.
    calc
      tensorBaseChangeRelationToCoconeMap G c C₀ w' =
          tensorBaseChangeRelationToCoconeMap G c C₀ w -
            tensorBaseChangeRelationToCoconeMap G c C₀
              (Finsupp.single (x ⊗ₜ[A₀] (1 : G.obj i)) (1 : C₀ ⊗[A₀] G.obj i)) := by
                simp [w', map_sub]
      _ =
          Finsupp.single (x ⊗ₜ[A₀] (1 : c.cocone.pt)) (1 : C₀ ⊗[A₀] c.cocone.pt) -
            tensorBaseChangeRelationToCoconeMap G c C₀
              (Finsupp.single (x ⊗ₜ[A₀] (1 : G.obj i)) (1 : C₀ ⊗[A₀] G.obj i)) := by
                rw [hw]
      _ = 0 := by
            rw [tensorBaseChangeRelationToCoconeMap_single]
            apply sub_eq_zero.mpr
            have hsupport :
                (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app i).hom)
                    (x ⊗ₜ[A₀] (1 : G.obj i)) =
                  x ⊗ₜ[A₀] (1 : c.cocone.pt) := by
              rw [Algebra.TensorProduct.map_tmul]
              simpa using congrArg (fun r : c.cocone.pt ↦ x ⊗ₜ[A₀] r)
                ((c.cocone.ι.app i).hom.map_one)
            have hone :
                (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (c.cocone.ι.app i).hom)
                    (1 : C₀ ⊗[A₀] G.obj i) =
                  (1 : C₀ ⊗[A₀] c.cocone.pt) := by
              exact (Algebra.TensorProduct.map
                (AlgHom.id A₀ C₀) (c.cocone.ι.app i).hom).map_one
            -- Proof comment: after rewriting the transported support and coefficient, the two
            -- singleton relations are literally the same finitely supported function.
            rw [hsupport, hone]
            rfl
  obtain ⟨j, hij, hwZero⟩ := tensorBaseChangeRelationEventuallyZeroOfCoconeZero G c C₀ w' hw'
  refine ⟨j, hij, ?_⟩
  have hwMap :
      tensorBaseChangeRelationMap G C₀ hij w -
        tensorBaseChangeRelationMap G C₀ hij
          (Finsupp.single (x ⊗ₜ[A₀] (1 : G.obj i)) (1 : C₀ ⊗[A₀] G.obj i)) = 0 := by
    simpa [w', map_sub] using hwZero
  have hwEq :
      tensorBaseChangeRelationMap G C₀ hij w =
        tensorBaseChangeRelationMap G C₀ hij
          (Finsupp.single (x ⊗ₜ[A₀] (1 : G.obj i)) (1 : C₀ ⊗[A₀] G.obj i)) := by
    exact sub_eq_zero.mp hwMap
  -- Proof comment: the transported singleton is the literal singleton at the synchronized stage.
  calc
    tensorBaseChangeRelationMap G C₀ hij w =
        tensorBaseChangeRelationMap G C₀ hij
          (Finsupp.single (x ⊗ₜ[A₀] (1 : G.obj i)) (1 : C₀ ⊗[A₀] G.obj i)) := hwEq
    _ =
        Finsupp.single (x ⊗ₜ[A₀] (1 : G.obj j)) (1 : C₀ ⊗[A₀] G.obj j) := by
          rw [tensorBaseChangeRelationMap_single]
          simp [Algebra.TensorProduct.map_tmul]

/-- Helper for Chap10 Lemma 10 168 5: the cocone-point singleton relation for
`x ⊗ₜ[A₀] 1` descends to a corresponding singleton relation at some directed stage. -/
theorem tensor_base_change_kerTotal_single_descends
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G)
    (φ₀ : B₀ →ₐ[A₀] C₀) (x : C₀)
    (hmem :
      letI : Algebra (B₀ ⊗[A₀] c.cocone.pt) (C₀ ⊗[A₀] c.cocone.pt) :=
        (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ c.cocone.pt)).toRingHom.toAlgebra
      Finsupp.single (x ⊗ₜ[A₀] (1 : c.cocone.pt)) (1 : C₀ ⊗[A₀] c.cocone.pt) ∈
        KaehlerDifferential.kerTotal (B₀ ⊗[A₀] c.cocone.pt) (C₀ ⊗[A₀] c.cocone.pt)) :
    ∃ i : I,
      letI : Algebra (B₀ ⊗[A₀] G.obj i) (C₀ ⊗[A₀] G.obj i) :=
        (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ (G.obj i))).toRingHom.toAlgebra
      Finsupp.single (x ⊗ₜ[A₀] (1 : G.obj i)) (1 : C₀ ⊗[A₀] G.obj i) ∈
        KaehlerDifferential.kerTotal (B₀ ⊗[A₀] G.obj i) (C₀ ⊗[A₀] G.obj i) := by
  letI : Algebra (B₀ ⊗[A₀] c.cocone.pt) (C₀ ⊗[A₀] c.cocone.pt) :=
    (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ c.cocone.pt)).toRingHom.toAlgebra
  obtain ⟨i, w, hwKer, hwMap⟩ :=
    tensorBaseChangeKerTotalWitnessDescends
      G c φ₀ (Finsupp.single (x ⊗ₜ[A₀] (1 : c.cocone.pt)) (1 : C₀ ⊗[A₀] c.cocone.pt)) hmem
  obtain ⟨j, hij, hsingle⟩ :=
    tensorBaseChangeRelationEventuallySingletonOfCoconeSingleton G c C₀ x w hwMap
  refine ⟨j, ?_⟩
  letI : Algebra (B₀ ⊗[A₀] G.obj j) (C₀ ⊗[A₀] G.obj j) :=
    (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ (G.obj j))).toRingHom.toAlgebra
  -- Proof comment: first move the descended `kerTotal` witness to the later synchronized stage,
  -- then rewrite it using the singleton comparison obtained above.
  simpa [hsingle] using tensorBaseChangeKerTotalTransition G φ₀ hij hwKer

/-- Helper for Chap10 Lemma 10 168 5: a single tensor-generator differential that vanishes over
the tensor-base-changed cocone point already vanishes at some directed stage. -/
theorem tensor_base_change_coconePoint_D_zero_eventually
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G)
    (φ₀ : B₀ →ₐ[A₀] C₀) (x : C₀)
    (hz :
      letI : Algebra (B₀ ⊗[A₀] c.cocone.pt) (C₀ ⊗[A₀] c.cocone.pt) :=
        (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ c.cocone.pt)).toRingHom.toAlgebra
      KaehlerDifferential.D (B₀ ⊗[A₀] c.cocone.pt) (C₀ ⊗[A₀] c.cocone.pt)
        (x ⊗ₜ[A₀] (1 : c.cocone.pt)) = 0) :
    ∃ i : I,
      letI : Algebra (B₀ ⊗[A₀] G.obj i) (C₀ ⊗[A₀] G.obj i) :=
        (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ (G.obj i))).toRingHom.toAlgebra
      KaehlerDifferential.D (B₀ ⊗[A₀] G.obj i) (C₀ ⊗[A₀] G.obj i)
        (x ⊗ₜ[A₀] (1 : G.obj i)) = 0 := by
  letI : Algebra (B₀ ⊗[A₀] c.cocone.pt) (C₀ ⊗[A₀] c.cocone.pt) :=
    (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ c.cocone.pt)).toRingHom.toAlgebra
  have hmem :
      Finsupp.single (x ⊗ₜ[A₀] (1 : c.cocone.pt)) (1 : C₀ ⊗[A₀] c.cocone.pt) ∈
        KaehlerDifferential.kerTotal (B₀ ⊗[A₀] c.cocone.pt) (C₀ ⊗[A₀] c.cocone.pt) :=
    -- Proof comment: rewrite vanishing of the universal differential into the singleton
    -- `kerTotal` presentation.
    (kaehlerDifferential_D_eq_zero_iff_single_mem_kerTotal
      (x ⊗ₜ[A₀] (1 : c.cocone.pt))).1 hz
  obtain ⟨i, hmemi⟩ := tensor_base_change_kerTotal_single_descends G c φ₀ x hmem
  refine ⟨i, ?_⟩
  letI : Algebra (B₀ ⊗[A₀] G.obj i) (C₀ ⊗[A₀] G.obj i) :=
    (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ (G.obj i))).toRingHom.toAlgebra
  -- Proof comment: translate the descended singleton `kerTotal` witness back to `D = 0`.
  exact
    (kaehlerDifferential_D_eq_zero_iff_single_mem_kerTotal
      (x ⊗ₜ[A₀] (1 : G.obj i))).2 hmemi

/-- Helper for Lemma 10.168.5: vanishing of the finitely many tensor-generator differentials on
the canonical tensor colimit descends to one stage. -/
theorem tensor_base_change_coconePoint_generator_zero_descends
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G)
    (φ₀ : B₀ →ₐ[A₀] C₀) {n : ℕ} (x : Fin n → C₀)
    (hz :
      ∀ k : Fin n,
        letI : Algebra (B₀ ⊗[A₀] c.cocone.pt) (C₀ ⊗[A₀] c.cocone.pt) :=
          (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ c.cocone.pt)).toRingHom.toAlgebra
        KaehlerDifferential.D (B₀ ⊗[A₀] c.cocone.pt) (C₀ ⊗[A₀] c.cocone.pt)
          (x k ⊗ₜ[A₀] (1 : c.cocone.pt)) = 0) :
    ∃ i : I,
      ∀ k : Fin n,
        letI : Algebra (B₀ ⊗[A₀] G.obj i) (C₀ ⊗[A₀] G.obj i) :=
          (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ (G.obj i))).toRingHom.toAlgebra
    KaehlerDifferential.D (B₀ ⊗[A₀] G.obj i) (C₀ ⊗[A₀] G.obj i)
          (x k ⊗ₜ[A₀] (1 : G.obj i)) = 0 := by
  classical
  have hstage :
      ∀ k : Fin n, ∃ i : I,
        letI : Algebra (B₀ ⊗[A₀] G.obj i) (C₀ ⊗[A₀] G.obj i) :=
          (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ (G.obj i))).toRingHom.toAlgebra
        KaehlerDifferential.D (B₀ ⊗[A₀] G.obj i) (C₀ ⊗[A₀] G.obj i)
          (x k ⊗ₜ[A₀] (1 : G.obj i)) = 0 := by
    intro k
    -- Proof comment: first descend each generator separately from the cocone point.
    exact tensor_base_change_coconePoint_D_zero_eventually G c φ₀ (x k) (hz k)
  choose i hi using hstage
  obtain ⟨j, hj⟩ := directed_fin_common_upper_bound i
  refine ⟨j, ?_⟩
  intro k
  -- Proof comment: once a common upper bound is chosen, vanishing persists along the transition
  -- maps of the tensor-base-change diagram.
  exact tensor_base_change_D_tmul_one_transition G φ₀ (hj k) (x k) (hi k)

-- Proof sketch: formal unramifiedness of the colimit base-change hom is the primitive owner
-- input. Interpreting it via Kähler differentials, finite type of `φ₀` gives finitely many
-- generators whose images vanish after tensoring to the colimit, so filtered-colimit finiteness
-- forces those generators to vanish already at some stage. That yields formal unramifiedness of
-- the stage base-change hom; finite type of the same stage hom is then recovered separately from
-- `hφ₀` by base change.
/-- Helper for Lemma 10.168.5: after reindexing a filtered diagram by a final directed poset, the
remaining source-faithful task is the directed-index proof that descends the vanishing of a finite
family of Kähler generators along the explicit direct-limit presentation. -/
theorem finite_type_formallyUnramified_baseChangeHom_descends_to_directed_reindex
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G)
    (φ₀ : B₀ →ₐ[A₀] C₀) (hφ₀ : φ₀.FiniteType)
    (hfu : (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ c.cocone.pt)).FormallyUnramified) :
    ∃ i : I, (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ (G.obj i))).FormallyUnramified := by
  classical
  letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
  letI : Algebra.FiniteType B₀ C₀ := hφ₀
  have hftOut : ∃ s : Finset C₀, Algebra.adjoin B₀ (s : Set C₀) = ⊤ := Algebra.FiniteType.out
  obtain ⟨s, hs⟩ := hftOut
  let e : s ≃ Fin s.card := Finset.equivFin s
  let x : Fin s.card → C₀ := fun k ↦ ((e.symm k : s) : C₀)
  have hx_range : Set.range x = (s : Set C₀) := by
    ext y
    constructor
    · rintro ⟨k, rfl⟩
      exact (e.symm k).2
    · intro hy
      refine ⟨e ⟨y, hy⟩, ?_⟩
      simp [x, e]
  have hzero :
      ∀ k : Fin s.card,
        letI : Algebra (B₀ ⊗[A₀] c.cocone.pt) (C₀ ⊗[A₀] c.cocone.pt) :=
          (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ c.cocone.pt)).toRingHom.toAlgebra
        KaehlerDifferential.D (B₀ ⊗[A₀] c.cocone.pt) (C₀ ⊗[A₀] c.cocone.pt)
          (x k ⊗ₜ[A₀] (1 : c.cocone.pt)) = 0 := by
    intro k
    -- Proof comment: formal unramifiedness at the cocone point kills each differential of the
    -- chosen finite generating family.
    exact tensor_base_change_D_tmul_one_eq_zero φ₀ c.cocone.pt hfu (x k)
  obtain ⟨i, hi⟩ := tensor_base_change_coconePoint_generator_zero_descends G c φ₀ x hzero
  refine ⟨i, ?_⟩
  -- Proof comment: once the descended generators still adjoin the whole algebra, vanishing of
  -- their distinguished differentials is exactly the Kähler criterion for formal unramifiedness.
  exact tensor_base_change_formallyUnramified_of_generator_zero
    φ₀ x (by simpa [hx_range] using hs) (G.obj i) hi

/-
The public theorem first reduces the arbitrary filtered index category to the canonical
directed-poset presentation from `IsFiltered.exists_directed`. Finality keeps the original colimit
point, so the formally-unramified hypothesis is unchanged; only the index category becomes
directed, which is the exact setting needed for the remaining source-faithful direct-limit proof.
-/
/-- Owner-level form of Lemma 10.168.5: if the colimit tensor-product base-change hom of
`φ₀ : B₀ →ₐ[A₀] C₀` is formally unramified, then some stage base-change hom is already formally
unramified. The finite-type input is kept separate because it is primitive data of `φ₀`, not of
the colimit base change. -/
theorem finite_type_formallyUnramified_baseChangeHom_descends_to_stage
    (φ₀ : B₀ →ₐ[A₀] C₀) (hφ₀ : φ₀.FiniteType)
    (hfu :
      (Algebra.TensorProduct.map φ₀
        (AlgHom.id A₀ (colimit F : CommAlgCat.{u} A₀))).FormallyUnramified) :
    ∃ j : J, (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ (F.obj j))).FormallyUnramified := by
  classical
  obtain ⟨K, _, _, _, FJ, hFJ⟩ := CategoryTheory.IsFiltered.exists_directed J
  let G : K ⥤ CommAlgCat.{u} A₀ := FJ ⋙ F
  let c : ColimitCocone G :=
    { cocone := (colimit.cocone F).whisker FJ
      isColimit :=
        (Functor.Final.isColimitWhiskerEquiv FJ (colimit.cocone F)).symm
          (colimit.isColimit F) }
  have hfu' :
      (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ c.cocone.pt)).FormallyUnramified := by
    simpa [G, c] using hfu
  obtain ⟨k, hk⟩ :=
    finite_type_formallyUnramified_baseChangeHom_descends_to_directed_reindex G c φ₀ hφ₀ hfu'
  exact ⟨FJ.obj k, by simpa [G] using hk⟩

/-- Chap10 Lemma 10 168 5 (Stacks tag `0C4F`, Lemma `10.168.5`): let
`A = colim_i Aᵢ` be a directed colimit of `A₀`-algebras. If the base change
`B₀ ⊗[A₀] A → C₀ ⊗[A₀] A` of a map `φ₀ : B₀ →ₐ[A₀] C₀` is unramified and `φ₀`
is of finite type, then for some stage `Aᵢ` the base-changed map
`B₀ ⊗[A₀] Aᵢ → C₀ ⊗[A₀] Aᵢ` is already unramified. This is stated on the canonical base-change
hom through the canonical owner `Algebra.Unramified`; Lemma `10.151.2` supplies the bridge from
this owner to the pair of formal unramifiedness and finite type. -/
@[stacks 0C4F]
theorem finite_type_unramified_baseChange_descends_to_stage
    (φ₀ : B₀ →ₐ[A₀] C₀) (hφ₀ : φ₀.FiniteType)
    (hunram :
      letI :=
        (Algebra.TensorProduct.map φ₀
          (AlgHom.id A₀ (colimit F : CommAlgCat.{u} A₀))).toRingHom.toAlgebra
      Algebra.Unramified
        (B₀ ⊗[A₀] (colimit F : CommAlgCat.{u} A₀))
        (C₀ ⊗[A₀] (colimit F : CommAlgCat.{u} A₀))) :
    ∃ j : J,
      letI :=
        (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ (F.obj j))).toRingHom.toAlgebra
      Algebra.Unramified (B₀ ⊗[A₀] F.obj j) (C₀ ⊗[A₀] F.obj j) := by
  letI :
      Algebra
        (B₀ ⊗[A₀] (colimit F : CommAlgCat.{u} A₀))
        (C₀ ⊗[A₀] (colimit F : CommAlgCat.{u} A₀)) :=
    (Algebra.TensorProduct.map φ₀
      (AlgHom.id A₀ (colimit F : CommAlgCat.{u} A₀))).toRingHom.toAlgebra
  have hfu :
      (Algebra.TensorProduct.map φ₀
        (AlgHom.id A₀ (colimit F : CommAlgCat.{u} A₀))).FormallyUnramified := by
    change
      Algebra.FormallyUnramified
        (B₀ ⊗[A₀] (colimit F : CommAlgCat.{u} A₀))
        (C₀ ⊗[A₀] (colimit F : CommAlgCat.{u} A₀))
    exact hunram.formallyUnramified
  obtain ⟨j, hform⟩ :=
    finite_type_formallyUnramified_baseChangeHom_descends_to_stage F φ₀ hφ₀ hfu
  refine ⟨j, ?_⟩
  letI : Algebra (B₀ ⊗[A₀] F.obj j) (C₀ ⊗[A₀] F.obj j) :=
    (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ (F.obj j))).toRingHom.toAlgebra
  letI : Algebra.FormallyUnramified (B₀ ⊗[A₀] F.obj j) (C₀ ⊗[A₀] F.obj j) := hform
  letI : Algebra.FiniteType (B₀ ⊗[A₀] F.obj j) (C₀ ⊗[A₀] F.obj j) :=
    tensor_base_change_hom_finiteType F φ₀ hφ₀ j
  -- Proof comment: unramifiedness is exactly the conjunction of formal unramifiedness and
  -- finite type for the stage base-change map.
  exact (Algebra.unramified_iff_formallyUnramified_and_finiteType).2
    ⟨inferInstance, inferInstance⟩

end
