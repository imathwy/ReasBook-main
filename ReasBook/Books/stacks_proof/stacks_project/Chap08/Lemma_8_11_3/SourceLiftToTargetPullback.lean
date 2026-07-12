import StacksProject_2024.Chap08.Lemma_8_11_3.TargetPullbackNormalForm

open CategoryTheory
open BasedFunctor
open Functor
open Functor.Fiber
open Functor.IsStronglyCartesian
open FibredCategoryOver

universe w v₁ u₁ v₂ u₂

namespace CategoryTheory

namespace StackInGroupoidsOver.Hom

section

variable {C : Type u₁} [Category.{v₁} C]
variable {J : GrothendieckTopology C}
variable {Xₛ Yₛ : StackInGroupoidsOver.{u₁, v₁, max u₁ v₁, v₁} J}

/-- Helper for Lemma 8.11.3: a vertical morphism between the two explicit target pullbacks of
the special factorization objects gives the source-facing local lift square. -/
theorem sourceLiftOfVerticalTargetPullbackHom
    (F : Xₛ ⟶ Yₛ) {U : C} (x x' : Xₛ.p.Fiber U)
    (b : (F.fiberFunctor U).obj x ⟶ (F.fiberFunctor U).obj x') [IsIso b]
    {y' : Yₛ.S}
    (i : y' ⟶ ((F.fiberFunctor U).obj x').1)
    {V : C} (hdom : Yₛ.p.obj y' = V) (f : V ⟶ U)
    (hbaseP :
      fibredInGroupoidsFactorizationToTarget_pullbackBase
          (toBasedFunctor F) (P := factorizationObjectOfFiberHom F x x' b) i =
        eqToHom hdom ≫ f)
    (hbaseQ :
      fibredInGroupoidsFactorizationToTarget_pullbackBase
          (toBasedFunctor F) (P := factorizationObjectOfFiberIdentity F x') i =
        eqToHom hdom ≫ f)
    (φ :
      factorizationTargetPullbackObject F (factorizationObjectOfFiberHom F x x' b) i ⟶
        factorizationTargetPullbackObject F (factorizationObjectOfFiberIdentity F x') i)
    (hbφ : φ.b = 𝟙 y') :
    ∃ a : f ^*[canonicalPullbackChoice Xₛ.p] x ⟶
        f ^*[canonicalPullbackChoice Xₛ.p] x',
      CommSq
        (((canonicalPullbackChoice Yₛ.p).pullbackFunctor f).map b)
        (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f x).hom
        (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f x').hom
        ((F.fiberFunctor V).map a) := by
  -- Normalize the external base object once, so all comparison helpers use the same pullback
  -- arrow spelling.
  subst hdom
  let P₀ := factorizationObjectOfFiberHom F x x' b
  let Q₀ := factorizationObjectOfFiberIdentity F x'
  obtain ⟨ePsrc, hPsrc⟩ :=
    sourcePullbackIsoOfTargetPullbackBaseEq_hom_fac
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F P₀ i f (by simpa [P₀] using hbaseP)
  obtain ⟨eQsrc, hQsrc⟩ :=
    sourcePullbackIsoOfTargetPullbackBaseEq_hom_fac
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F Q₀ i f (by simpa [Q₀] using hbaseQ)
  let aRaw :
      (factorizationTargetPullbackObject F P₀ i).obj.fst ⟶
        (factorizationTargetPullbackObject F Q₀ i).obj.fst :=
    ⟨φ.a, by
      simpa [P₀, Q₀] using
        targetPullbackHom_sourceComponent_isHomLift_id F P₀ Q₀ i i φ hbφ⟩
  let a : f ^*[canonicalPullbackChoice Xₛ.p] x ⟶
      f ^*[canonicalPullbackChoice Xₛ.p] x' :=
    ePsrc.inv ≫ aRaw ≫ eQsrc.hom
  refine ⟨a, ?_⟩
  refine ⟨?_⟩
  apply Functor.Fiber.hom_ext
  -- Compare the two target-fiber arrows after postcomposing with the mapped source pullback
  -- arrow; strong cartesianness then cancels that common tail.
  let tail := (toBasedFunctor F).map ((canonicalPullbackChoice Xₛ.p).map f x')
  have htail : Yₛ.p.IsStronglyCartesian f tail := by
    exact
      FibredCategoryMor.map_stronglyCartesian_of_lift
        (toFibredCategoryMor F) f ((canonicalPullbackChoice Xₛ.p).map f x')
        ((canonicalPullbackChoice Xₛ.p).isStronglyCartesian f x')
  let lhs :=
    ((((canonicalPullbackChoice Yₛ.p).pullbackFunctor f).map b) ≫
      (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f x').hom).1
  let rhs :=
    ((FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f x).hom ≫
      (F.fiberFunctor (Yₛ.p.obj y')).map a).1
  have hlhs : Yₛ.p.IsHomLift (𝟙 (Yₛ.p.obj y')) lhs := by
    exact
      ((((canonicalPullbackChoice Yₛ.p).pullbackFunctor f).map b) ≫
        (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f x').hom).2
  have hrhs : Yₛ.p.IsHomLift (𝟙 (Yₛ.p.obj y')) rhs := by
    exact
      ((FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f x).hom ≫
        (F.fiberFunctor (Yₛ.p.obj y')).map a).2
  change lhs = rhs
  refine
    @Functor.IsStronglyCartesian.ext _ _ _ _ Yₛ.p _ _ _ _
      f tail htail _ _ (𝟙 (Yₛ.p.obj y')) lhs rhs hlhs hrhs ?_
  -- The postcomposition equality is the explicit pullback square, rewritten through the
  -- equation-carrying source comparisons.
  have hPsrc_inv :
      ePsrc.inv.1 ≫
          fibredInGroupoidsFactorizationToTarget_left_pullback_map (toBasedFunctor F) P₀ i =
        (canonicalPullbackChoice Xₛ.p).map f x := by
    calc
      ePsrc.inv.1 ≫
          fibredInGroupoidsFactorizationToTarget_left_pullback_map (toBasedFunctor F) P₀ i =
          ePsrc.inv.1 ≫
            (ePsrc.hom.1 ≫ (canonicalPullbackChoice Xₛ.p).map f P₀.obj.fst) := by
            rw [← hPsrc]
            rfl
      _ =
          (ePsrc.inv.1 ≫ ePsrc.hom.1) ≫
            (canonicalPullbackChoice Xₛ.p).map f P₀.obj.fst := by
            rw [Category.assoc]
      _ = (canonicalPullbackChoice Xₛ.p).map f x := by
            have hinvhom : ePsrc.inv.1 ≫ ePsrc.hom.1 = 𝟙 _ :=
              congrArg Subtype.val ePsrc.inv_hom_id
            rw [hinvhom]
            simp only [Category.id_comp]
            rfl
  have hQsrc_hom :
      eQsrc.hom.1 ≫ (canonicalPullbackChoice Xₛ.p).map f x' =
        fibredInGroupoidsFactorizationToTarget_left_pullback_map (toBasedFunctor F) Q₀ i := by
    simpa [Q₀] using hQsrc
  have hQcomm :
      (toBasedFunctor F).map
          (fibredInGroupoidsFactorizationToTarget_left_pullback_map (toBasedFunctor F) Q₀ i) =
        (factorizationTargetPullbackObject F Q₀ i).comparison ≫ i := by
    -- The identity comparison in `Q₀` removes the original factorization-object comparison
    -- from the explicit target-pullback square.
    have hQid : Q₀.comparison = 𝟙 ((F.fiberFunctor U).obj x').1 := by
      rfl
    have hremove :
        (toBasedFunctor F).map
            (fibredInGroupoidsFactorizationToTarget_left_pullback_map (toBasedFunctor F) Q₀ i) =
          (toBasedFunctor F).map
              (fibredInGroupoidsFactorizationToTarget_left_pullback_map
                (toBasedFunctor F) Q₀ i) ≫ Q₀.comparison := by
      rw [hQid]
      exact (Category.comp_id _).symm
    exact hremove.trans (factorizationTargetPullback_comm F Q₀ i).w
  have hPcomm :
      (factorizationTargetPullbackObject F P₀ i).comparison ≫ i =
        (toBasedFunctor F).map
            (fibredInGroupoidsFactorizationToTarget_left_pullback_map (toBasedFunctor F) P₀ i) ≫
          b.1 := by
    -- For `P₀`, the stored target comparison is exactly the given fiber morphism `b`.
    simpa [P₀] using (factorizationTargetPullback_comm F P₀ i).w.symm
  have hφcomm :
      (toBasedFunctor F).map φ.a ≫
          (factorizationTargetPullbackObject F Q₀ i).comparison =
        (factorizationTargetPullbackObject F P₀ i).comparison := by
    have h := φ.comm.w
    rw [hbφ] at h
    exact h.trans (Category.comp_id _)
  have ha_underlying :
      a.1 = ePsrc.inv.1 ≫ φ.a ≫ eQsrc.hom.1 := by
    rfl
  have ha_src_post :
      a.1 ≫ (canonicalPullbackChoice Xₛ.p).map f x' =
        ePsrc.inv.1 ≫ φ.a ≫
          fibredInGroupoidsFactorizationToTarget_left_pullback_map (toBasedFunctor F) Q₀ i := by
    -- Expand the conjugated source component once and use the recorded source factorization
    -- for the target object `Q₀`.
    rw [ha_underlying]
    have hassoc :
        (ePsrc.inv.1 ≫ φ.a ≫ eQsrc.hom.1) ≫
            (canonicalPullbackChoice Xₛ.p).map f x' =
          ePsrc.inv.1 ≫ φ.a ≫
            (eQsrc.hom.1 ≫ (canonicalPullbackChoice Xₛ.p).map f x') := by
      simp only [Category.assoc]
    exact hassoc.trans (congrArg (fun k ↦ ePsrc.inv.1 ≫ φ.a ≫ k) hQsrc_hom)
  have ha_post :
      (toBasedFunctor F).map a.1 ≫ tail =
        (toBasedFunctor F).map ((canonicalPullbackChoice Xₛ.p).map f x) ≫ b.1 := by
    -- Push the source equality through `F` and rewrite the explicit target-pullback square in
    -- the cheapest underlying category.
    have h0 :
        (toBasedFunctor F).map a.1 ≫ tail =
          (toBasedFunctor F).map (a.1 ≫ (canonicalPullbackChoice Xₛ.p).map f x') := by
      rw [← Functor.map_comp]
    have h1 :
        (toBasedFunctor F).map (a.1 ≫ (canonicalPullbackChoice Xₛ.p).map f x') =
          (toBasedFunctor F).map
            (ePsrc.inv.1 ≫ φ.a ≫
              fibredInGroupoidsFactorizationToTarget_left_pullback_map
                (toBasedFunctor F) Q₀ i) :=
      congrArg (fun k ↦ (toBasedFunctor F).map k) ha_src_post
    have h2 :
        (toBasedFunctor F).map
            (ePsrc.inv.1 ≫ φ.a ≫
              fibredInGroupoidsFactorizationToTarget_left_pullback_map
                (toBasedFunctor F) Q₀ i) =
          (toBasedFunctor F).map ePsrc.inv.1 ≫
            ((toBasedFunctor F).map φ.a ≫
              (toBasedFunctor F).map
                (fibredInGroupoidsFactorizationToTarget_left_pullback_map
                  (toBasedFunctor F) Q₀ i)) := by
      simp only [Functor.map_comp]
    have h3 :
        (toBasedFunctor F).map ePsrc.inv.1 ≫
            ((toBasedFunctor F).map φ.a ≫
              (toBasedFunctor F).map
                (fibredInGroupoidsFactorizationToTarget_left_pullback_map
                  (toBasedFunctor F) Q₀ i)) =
          (toBasedFunctor F).map ePsrc.inv.1 ≫
            ((toBasedFunctor F).map φ.a ≫
              ((factorizationTargetPullbackObject F Q₀ i).comparison ≫ i)) :=
      congrArg
        (fun k ↦ (toBasedFunctor F).map ePsrc.inv.1 ≫
          ((toBasedFunctor F).map φ.a ≫ k))
        hQcomm
    have h4 :
        (toBasedFunctor F).map ePsrc.inv.1 ≫
            ((toBasedFunctor F).map φ.a ≫
              ((factorizationTargetPullbackObject F Q₀ i).comparison ≫ i)) =
          (toBasedFunctor F).map ePsrc.inv.1 ≫
            ((factorizationTargetPullbackObject F P₀ i).comparison ≫ i) := by
      have hassoc :
          (toBasedFunctor F).map ePsrc.inv.1 ≫
              ((toBasedFunctor F).map φ.a ≫
                ((factorizationTargetPullbackObject F Q₀ i).comparison ≫ i)) =
            (toBasedFunctor F).map ePsrc.inv.1 ≫
              (((toBasedFunctor F).map φ.a ≫
                (factorizationTargetPullbackObject F Q₀ i).comparison) ≫ i) := by
        simp only [Category.assoc]
      exact hassoc.trans
        (congrArg (fun k ↦ (toBasedFunctor F).map ePsrc.inv.1 ≫ (k ≫ i)) hφcomm)
    have h5 :
        (toBasedFunctor F).map ePsrc.inv.1 ≫
            ((factorizationTargetPullbackObject F P₀ i).comparison ≫ i) =
          (toBasedFunctor F).map ePsrc.inv.1 ≫
            ((toBasedFunctor F).map
                (fibredInGroupoidsFactorizationToTarget_left_pullback_map
                  (toBasedFunctor F) P₀ i) ≫ b.1) :=
      congrArg (fun k ↦ (toBasedFunctor F).map ePsrc.inv.1 ≫ k) hPcomm
    have h6 :
        (toBasedFunctor F).map ePsrc.inv.1 ≫
            ((toBasedFunctor F).map
                (fibredInGroupoidsFactorizationToTarget_left_pullback_map
                  (toBasedFunctor F) P₀ i) ≫ b.1) =
          (toBasedFunctor F).map
              (ePsrc.inv.1 ≫
                fibredInGroupoidsFactorizationToTarget_left_pullback_map
                  (toBasedFunctor F) P₀ i) ≫ b.1 := by
      simp only [Functor.map_comp, Category.assoc]
    have h7 :
        (toBasedFunctor F).map
            (ePsrc.inv.1 ≫
              fibredInGroupoidsFactorizationToTarget_left_pullback_map
                (toBasedFunctor F) P₀ i) ≫ b.1 =
          (toBasedFunctor F).map ((canonicalPullbackChoice Xₛ.p).map f x) ≫ b.1 :=
      congrArg (fun k ↦ (toBasedFunctor F).map k ≫ b.1) hPsrc_inv
    exact h0.trans (h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans h7))))))
  have hlhs_post :
      lhs ≫ tail =
        (canonicalPullbackChoice Yₛ.p).map f ((F.fiberFunctor U).obj x) ≫ b.1 := by
    -- Project the fiber composite to the total category, then use the standard pullback
    -- functoriality equation.
    have h0 :
        lhs ≫ tail =
          ((((canonicalPullbackChoice Yₛ.p).pullbackFunctor f).map b).1 ≫
            (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f x').hom.1) ≫
              tail := by
      rfl
    have h1 :
        ((((canonicalPullbackChoice Yₛ.p).pullbackFunctor f).map b).1 ≫
            (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f x').hom.1) ≫
              tail =
          (((canonicalPullbackChoice Yₛ.p).pullbackFunctor f).map b).1 ≫
            ((FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f x').hom.1 ≫
              tail) := by
      rw [Category.assoc]
    have h2 :
        (((canonicalPullbackChoice Yₛ.p).pullbackFunctor f).map b).1 ≫
            ((FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f x').hom.1 ≫
              tail) =
          (((canonicalPullbackChoice Yₛ.p).pullbackFunctor f).map b).1 ≫
            (canonicalPullbackChoice Yₛ.p).map f ((F.fiberFunctor U).obj x') :=
      congrArg
        (fun k ↦ (((canonicalPullbackChoice Yₛ.p).pullbackFunctor f).map b).1 ≫ k)
        (FibredCategoryMor.pullbackComparison_hom_postcompose
          (toFibredCategoryMor F) f x')
    have h3 :
        (((canonicalPullbackChoice Yₛ.p).pullbackFunctor f).map b).1 ≫
            (canonicalPullbackChoice Yₛ.p).map f ((F.fiberFunctor U).obj x') =
          (canonicalPullbackChoice Yₛ.p).map f ((F.fiberFunctor U).obj x) ≫ b.1 :=
      FibredCategoryMor.canonical_pullbackFunctor_map_fac
        (p := Yₛ.p) (f := f) (φ := b)
    exact h0.trans (h1.trans (h2.trans h3))
  have hrhs_post :
      rhs ≫ tail =
        (canonicalPullbackChoice Yₛ.p).map f ((F.fiberFunctor U).obj x) ≫ b.1 := by
    calc
      rhs ≫ tail =
          (((FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f x).hom.1 ≫
            (toBasedFunctor F).map a.1) ≫ tail) := by
            rfl
      _ =
          (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f x).hom.1 ≫
            ((toBasedFunctor F).map a.1 ≫ tail) := by
            rw [Category.assoc]
      _ =
          (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f x).hom.1 ≫
            ((toBasedFunctor F).map ((canonicalPullbackChoice Xₛ.p).map f x) ≫ b.1) := by
            exact
              congrArg
                (fun k ↦
                  (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f x).hom.1 ≫ k)
                ha_post
      _ =
          ((FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f x).hom.1 ≫
            (toBasedFunctor F).map ((canonicalPullbackChoice Xₛ.p).map f x)) ≫ b.1 := by
            rw [Category.assoc]
      _ =
          (canonicalPullbackChoice Yₛ.p).map f ((F.fiberFunctor U).obj x) ≫ b.1 := by
            exact
              congrArg (fun k ↦ k ≫ b.1)
                (FibredCategoryMor.pullbackComparison_hom_postcompose
                  (toFibredCategoryMor F) f x)
  exact hlhs_post.trans hrhs_post.symm

/-- Helper for Lemma 8.11.3: in strict target normal form, a source-local lift square becomes
the corresponding equality after composing with the target comparison isomorphisms. -/
theorem sourceLiftSquare_comp_comparison
    (F : Xₛ ⟶ Yₛ) {U V : C} (f : V ⟶ U)
    (x x' : Xₛ.p.Fiber U) (y : Yₛ.p.Fiber U)
    (e : (F.fiberFunctor U).obj x ≅ y)
    (e' : (F.fiberFunctor U).obj x' ≅ y)
    (a : f ^*[canonicalPullbackChoice Xₛ.p] x ⟶
        f ^*[canonicalPullbackChoice Xₛ.p] x')
    (hsq :
      CommSq
        (((canonicalPullbackChoice Yₛ.p).pullbackFunctor f).map (e.hom ≫ e'.inv))
        (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f x).hom
        (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f x').hom
        ((F.fiberFunctor V).map a)) :
    (toBasedFunctor F).map a.1 ≫
        (toBasedFunctor F).map ((canonicalPullbackChoice Xₛ.p).map f x') ≫
          e'.hom.1 =
      (toBasedFunctor F).map ((canonicalPullbackChoice Xₛ.p).map f x) ≫ e.hom.1 := by
  let pcx := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f x
  let pcx' := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f x'
  let b : (F.fiberFunctor U).obj x ⟶ (F.fiberFunctor U).obj x' := e.hom ≫ e'.inv
  have hpcxIso : IsIso pcx.hom.1 :=
    ⟨pcx.inv.1, congrArg Subtype.val pcx.hom_inv_id,
      congrArg Subtype.val pcx.inv_hom_id⟩
  letI : IsIso pcx.hom.1 := hpcxIso
  have hpcx_post :
      pcx.hom.1 ≫
          (toBasedFunctor F).map ((canonicalPullbackChoice Xₛ.p).map f x) =
        (canonicalPullbackChoice Yₛ.p).map f ((F.fiberFunctor U).obj x) := by
    exact FibredCategoryMor.pullbackComparison_hom_postcompose (toFibredCategoryMor F) f x
  have hpcx'_post :
      pcx'.hom.1 ≫
          (toBasedFunctor F).map ((canonicalPullbackChoice Xₛ.p).map f x') =
        (canonicalPullbackChoice Yₛ.p).map f ((F.fiberFunctor U).obj x') := by
    exact FibredCategoryMor.pullbackComparison_hom_postcompose (toFibredCategoryMor F) f x'
  have hpullback_b :
      (((canonicalPullbackChoice Yₛ.p).pullbackFunctor f).map b).1 ≫
          (canonicalPullbackChoice Yₛ.p).map f ((F.fiberFunctor U).obj x') =
        (canonicalPullbackChoice Yₛ.p).map f ((F.fiberFunctor U).obj x) ≫ b.1 :=
    FibredCategoryMor.canonical_pullbackFunctor_map_fac
      (p := Yₛ.p) (f := f) (φ := b)
  have hsq_total :
      (((canonicalPullbackChoice Yₛ.p).pullbackFunctor f).map b).1 ≫ pcx'.hom.1 =
        pcx.hom.1 ≫ (toBasedFunctor F).map a.1 := by
    have h := congrArg Subtype.val hsq.w
    change
      (((canonicalPullbackChoice Yₛ.p).pullbackFunctor f).map b).1 ≫ pcx'.hom.1 =
        pcx.hom.1 ≫ ((F.fiberFunctor V).map a).1 at h
    exact h
  have hb_cancel : b.1 ≫ e'.hom.1 = e.hom.1 := by
    have hb_fiber : b ≫ e'.hom = e.hom := by
      dsimp [b]
      rw [Category.assoc, e'.inv_hom_id, Category.comp_id]
    exact congrArg Subtype.val hb_fiber
  -- First prove the equality after precomposing by the comparison isomorphism; then cancel it.
  have hwithPrefix :
      (((pcx.hom.1 ≫ (toBasedFunctor F).map a.1) ≫
          (toBasedFunctor F).map ((canonicalPullbackChoice Xₛ.p).map f x')) ≫
        e'.hom.1) =
      ((pcx.hom.1 ≫
          (toBasedFunctor F).map ((canonicalPullbackChoice Xₛ.p).map f x)) ≫
        e.hom.1) := by
    have hA :
        (((pcx.hom.1 ≫ (toBasedFunctor F).map a.1) ≫
            (toBasedFunctor F).map ((canonicalPullbackChoice Xₛ.p).map f x')) ≫
          e'.hom.1) =
        (((((canonicalPullbackChoice Yₛ.p).pullbackFunctor f).map b).1 ≫
            pcx'.hom.1) ≫
          (toBasedFunctor F).map ((canonicalPullbackChoice Xₛ.p).map f x')) ≫
            e'.hom.1 :=
      congrArg
        (fun k ↦ (k ≫
          (toBasedFunctor F).map ((canonicalPullbackChoice Xₛ.p).map f x')) ≫ e'.hom.1)
        hsq_total.symm
    have hB :
        (((((canonicalPullbackChoice Yₛ.p).pullbackFunctor f).map b).1 ≫
            pcx'.hom.1) ≫
          (toBasedFunctor F).map ((canonicalPullbackChoice Xₛ.p).map f x')) ≫
            e'.hom.1 =
        ((((canonicalPullbackChoice Yₛ.p).pullbackFunctor f).map b).1 ≫
            (pcx'.hom.1 ≫
              (toBasedFunctor F).map ((canonicalPullbackChoice Xₛ.p).map f x'))) ≫
          e'.hom.1 := by
      rw [← Category.assoc]
    have hC :
        ((((canonicalPullbackChoice Yₛ.p).pullbackFunctor f).map b).1 ≫
            (pcx'.hom.1 ≫
              (toBasedFunctor F).map ((canonicalPullbackChoice Xₛ.p).map f x'))) ≫
          e'.hom.1 =
        ((((canonicalPullbackChoice Yₛ.p).pullbackFunctor f).map b).1 ≫
            (canonicalPullbackChoice Yₛ.p).map f ((F.fiberFunctor U).obj x')) ≫
          e'.hom.1 :=
      congrArg
        (fun k ↦ ((((canonicalPullbackChoice Yₛ.p).pullbackFunctor f).map b).1 ≫ k) ≫
          e'.hom.1)
        hpcx'_post
    have hD :
        ((((canonicalPullbackChoice Yₛ.p).pullbackFunctor f).map b).1 ≫
            (canonicalPullbackChoice Yₛ.p).map f ((F.fiberFunctor U).obj x')) ≫
          e'.hom.1 =
        (((canonicalPullbackChoice Yₛ.p).map f ((F.fiberFunctor U).obj x) ≫ b.1) ≫
          e'.hom.1) :=
      congrArg (fun k ↦ k ≫ e'.hom.1) hpullback_b
    have hE :
        (((canonicalPullbackChoice Yₛ.p).map f ((F.fiberFunctor U).obj x) ≫ b.1) ≫
          e'.hom.1) =
        (canonicalPullbackChoice Yₛ.p).map f ((F.fiberFunctor U).obj x) ≫ e.hom.1 := by
      rw [Category.assoc, hb_cancel]
    have hF :
        (canonicalPullbackChoice Yₛ.p).map f ((F.fiberFunctor U).obj x) ≫ e.hom.1 =
        (pcx.hom.1 ≫
          (toBasedFunctor F).map ((canonicalPullbackChoice Xₛ.p).map f x)) ≫ e.hom.1 :=
      congrArg (fun k ↦ k ≫ e.hom.1) hpcx_post.symm
    exact hA.trans (hB.trans (hC.trans (hD.trans (hE.trans hF))))
  have hcancelled :
      (((toBasedFunctor F).map a.1 ≫
          (toBasedFunctor F).map ((canonicalPullbackChoice Xₛ.p).map f x')) ≫
        e'.hom.1) =
      ((toBasedFunctor F).map ((canonicalPullbackChoice Xₛ.p).map f x) ≫ e.hom.1) := by
    apply (cancel_epi pcx.hom.1).1
    simpa only [Category.assoc] using hwithPrefix
  simpa only [Category.assoc] using hcancelled

/-- Helper for Lemma 8.11.3: `eqToHom` is independent of the chosen equality proof. -/
theorem eqToHom_eq_of_proof_irrel_forGerbeCriterion
    {D : Type u₂} [Category.{v₂} D] {A B : D} (h h' : A = B) :
    eqToHom h = eqToHom h' := by
  cases h
  rw [Subsingleton.elim h' rfl]

/-- Helper for Lemma 8.11.3: the strict target-normal-form factorization object over a literal
target object `y`. -/
noncomputable def strictTargetFactorizationObject
    (F : Xₛ ⟶ Yₛ) {y : Yₛ.S}
    (x : Xₛ.p.Fiber (Yₛ.p.obj y))
    (e : (F.fiberFunctor (Yₛ.p.obj y)).obj x ≅
      Functor.Fiber.mk (p := Yₛ.p) (rfl : Yₛ.p.obj y = Yₛ.p.obj y)) :
    (fibredInGroupoidsFactorization (toBasedFunctor F)).obj :=
  { U := Yₛ.p.obj y
    obj :=
      { fst := x
        snd := Functor.Fiber.mk (p := Yₛ.p) (rfl : Yₛ.p.obj y = Yₛ.p.obj y)
        iso := e } }

/-- Helper for Lemma 8.11.3: a strict source-lift square gives a vertical morphism between the
explicit target-pullback factorization objects. -/
theorem strictTargetPullbackHomOfSourceLiftSquare
    (F : Xₛ ⟶ Yₛ) {y y' : Yₛ.S} (i : y' ⟶ y)
    (x x' : Xₛ.p.Fiber (Yₛ.p.obj y))
    (e : (F.fiberFunctor (Yₛ.p.obj y)).obj x ≅
      Functor.Fiber.mk (p := Yₛ.p) (show Yₛ.p.obj y = Yₛ.p.obj y from rfl))
    (e' : (F.fiberFunctor (Yₛ.p.obj y)).obj x' ≅
      Functor.Fiber.mk (p := Yₛ.p) (show Yₛ.p.obj y = Yₛ.p.obj y from rfl))
    (a : (Yₛ.p.map i) ^*[canonicalPullbackChoice Xₛ.p] x ⟶
        (Yₛ.p.map i) ^*[canonicalPullbackChoice Xₛ.p] x')
    (hsq :
      CommSq
        (((canonicalPullbackChoice Yₛ.p).pullbackFunctor (Yₛ.p.map i)).map
          (e.hom ≫ e'.inv))
        (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) (Yₛ.p.map i) x).hom
        (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) (Yₛ.p.map i) x').hom
        ((F.fiberFunctor (Yₛ.p.obj y')).map a)) :
    Nonempty
      (Functor.Fiber.mk
          (p := (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor)
          (show (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor.obj
              (factorizationTargetPullbackObject F
                ({ U := Yₛ.p.obj y
                   obj :=
                    { fst := x
                      snd := Functor.Fiber.mk (p := Yₛ.p)
                        (show Yₛ.p.obj y = Yₛ.p.obj y from rfl)
                      iso := e } } :
                  (fibredInGroupoidsFactorization (toBasedFunctor F)).obj) i) = y' from rfl) ⟶
        Functor.Fiber.mk
          (p := (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor)
          (show (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor.obj
              (factorizationTargetPullbackObject F
                ({ U := Yₛ.p.obj y
                   obj :=
                    { fst := x'
                      snd := Functor.Fiber.mk (p := Yₛ.p)
                        (show Yₛ.p.obj y = Yₛ.p.obj y from rfl)
                      iso := e' } } :
                  (fibredInGroupoidsFactorization (toBasedFunctor F)).obj) i) = y' from rfl)) := by
  let Ftarget := fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)
  let yFiber : Yₛ.p.Fiber (Yₛ.p.obj y) :=
    Functor.Fiber.mk (p := Yₛ.p) (show Yₛ.p.obj y = Yₛ.p.obj y from rfl)
  let P₀ : (fibredInGroupoidsFactorization (toBasedFunctor F)).obj :=
    { U := Yₛ.p.obj y
      obj := { fst := x, snd := yFiber, iso := e } }
  let Q₀ : (fibredInGroupoidsFactorization (toBasedFunctor F)).obj :=
    { U := Yₛ.p.obj y
      obj := { fst := x', snd := yFiber, iso := e' } }
  obtain ⟨ePsrc, hPsrc⟩ :=
    sourcePullbackIsoOfTargetPullbackBaseEq_hom_fac
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F P₀ i (Yₛ.p.map i) (by
        change Yₛ.p.map i ≫
            eqToHom ((fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).w_obj P₀) =
          Yₛ.p.map i
        calc
          Yₛ.p.map i ≫
              eqToHom ((fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).w_obj P₀) =
              Yₛ.p.map i ≫ 𝟙 (Yₛ.p.obj y) := by
                exact congrArg (fun k ↦ Yₛ.p.map i ≫ k)
                  (eqToHom_eq_of_proof_irrel_forGerbeCriterion
                    ((fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).w_obj P₀)
                    (rfl : Yₛ.p.obj y = Yₛ.p.obj y))
          _ = Yₛ.p.map i := by
                rw [Category.comp_id])
  obtain ⟨eQsrc, hQsrc⟩ :=
    sourcePullbackIsoOfTargetPullbackBaseEq_hom_fac
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F Q₀ i (Yₛ.p.map i) (by
        change Yₛ.p.map i ≫
            eqToHom ((fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).w_obj Q₀) =
          Yₛ.p.map i
        calc
          Yₛ.p.map i ≫
              eqToHom ((fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).w_obj Q₀) =
              Yₛ.p.map i ≫ 𝟙 (Yₛ.p.obj y) := by
                exact congrArg (fun k ↦ Yₛ.p.map i ≫ k)
                  (eqToHom_eq_of_proof_irrel_forGerbeCriterion
                    ((fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).w_obj Q₀)
                    (rfl : Yₛ.p.obj y = Yₛ.p.obj y))
          _ = Yₛ.p.map i := by
                rw [Category.comp_id])
  let aExplicit :
      (factorizationTargetPullbackObject F P₀ i).obj.fst ⟶
        (factorizationTargetPullbackObject F Q₀ i).obj.fst :=
    ePsrc.hom ≫ a ≫ eQsrc.inv
  have hQsrc_inv :
      eQsrc.inv.1 ≫
          fibredInGroupoidsFactorizationToTarget_left_pullback_map (toBasedFunctor F) Q₀ i =
        (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map i) x' := by
    calc
      eQsrc.inv.1 ≫
          fibredInGroupoidsFactorizationToTarget_left_pullback_map (toBasedFunctor F) Q₀ i =
          eQsrc.inv.1 ≫
            (eQsrc.hom.1 ≫ (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map i) Q₀.obj.fst) := by
            rw [← hQsrc]
      _ =
          (eQsrc.inv.1 ≫ eQsrc.hom.1) ≫
            (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map i) Q₀.obj.fst := by
            rw [Category.assoc]
      _ = (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map i) x' := by
            have hinvhom : eQsrc.inv.1 ≫ eQsrc.hom.1 = 𝟙 _ :=
              congrArg Subtype.val eQsrc.inv_hom_id
            rw [hinvhom]
            rw [Category.id_comp]
  have hsource_comp :
      (toBasedFunctor F).map a.1 ≫
          (toBasedFunctor F).map ((canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map i) x') ≫
            e'.hom.1 =
        (toBasedFunctor F).map ((canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map i) x) ≫
          e.hom.1 :=
    sourceLiftSquare_comp_comparison
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F (Yₛ.p.map i) x x' yFiber e e' a hsq
  have hpost_core :
      (toBasedFunctor F).map aExplicit.1 ≫
          (toBasedFunctor F).map
            (fibredInGroupoidsFactorizationToTarget_left_pullback_map (toBasedFunctor F) Q₀ i) ≫
            e'.hom.1 =
        (toBasedFunctor F).map
            (fibredInGroupoidsFactorizationToTarget_left_pullback_map (toBasedFunctor F) P₀ i) ≫
          e.hom.1 := by
    calc
      (toBasedFunctor F).map aExplicit.1 ≫
          (toBasedFunctor F).map
            (fibredInGroupoidsFactorizationToTarget_left_pullback_map (toBasedFunctor F) Q₀ i) ≫
            e'.hom.1 =
          (toBasedFunctor F).map
              (aExplicit.1 ≫
                fibredInGroupoidsFactorizationToTarget_left_pullback_map (toBasedFunctor F) Q₀ i) ≫
            e'.hom.1 := by
            simp only [Functor.map_comp, Category.assoc]
      _ =
          (toBasedFunctor F).map
              (ePsrc.hom.1 ≫ a.1 ≫
                (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map i) x') ≫ e'.hom.1 := by
            exact
              congrArg (fun k ↦ (toBasedFunctor F).map k ≫ e'.hom.1) (by
                calc
                  aExplicit.1 ≫
                      fibredInGroupoidsFactorizationToTarget_left_pullback_map
                        (toBasedFunctor F) Q₀ i =
                      (ePsrc.hom.1 ≫ a.1 ≫ eQsrc.inv.1) ≫
                        fibredInGroupoidsFactorizationToTarget_left_pullback_map
                          (toBasedFunctor F) Q₀ i := by
                        rfl
                  _ =
                      ePsrc.hom.1 ≫ a.1 ≫
                        (eQsrc.inv.1 ≫
                          fibredInGroupoidsFactorizationToTarget_left_pullback_map
                            (toBasedFunctor F) Q₀ i) := by
                        simp only [Category.assoc]
                  _ =
                      ePsrc.hom.1 ≫ a.1 ≫
                        (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map i) x' := by
                        simpa only [Category.assoc] using
                          congrArg (fun k ↦ ePsrc.hom.1 ≫ a.1 ≫ k) hQsrc_inv)
      _ =
          (toBasedFunctor F).map ePsrc.hom.1 ≫
            ((toBasedFunctor F).map a.1 ≫
              (toBasedFunctor F).map
                ((canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map i) x') ≫ e'.hom.1) := by
            simp only [Functor.map_comp, Category.assoc]
      _ =
          (toBasedFunctor F).map ePsrc.hom.1 ≫
            ((toBasedFunctor F).map
              ((canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map i) x) ≫ e.hom.1) := by
            exact congrArg (fun k ↦ (toBasedFunctor F).map ePsrc.hom.1 ≫ k) hsource_comp
      _ =
          (toBasedFunctor F).map
              (ePsrc.hom.1 ≫
                (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map i) x) ≫ e.hom.1 := by
            simp only [Functor.map_comp, Category.assoc]
      _ =
          (toBasedFunctor F).map
              (fibredInGroupoidsFactorizationToTarget_left_pullback_map
                (toBasedFunctor F) P₀ i) ≫ e.hom.1 := by
            exact congrArg (fun k ↦ (toBasedFunctor F).map k ≫ e.hom.1) (by simpa [P₀] using hPsrc)
  have hcomm :
      CommSq
        ((toBasedFunctor F).map aExplicit.1)
        (factorizationTargetPullbackObject F P₀ i).comparison
        (factorizationTargetPullbackObject F Q₀ i).comparison
        (𝟙 y') := by
    refine ⟨?_⟩
    -- Compare the two vertical arrows after postcomposing with the strongly cartesian arrow `i`.
    let lhs :=
      (toBasedFunctor F).map aExplicit.1 ≫
        (factorizationTargetPullbackObject F Q₀ i).comparison
    let rhs := (factorizationTargetPullbackObject F P₀ i).comparison
    have hlhs : Yₛ.p.IsHomLift (𝟙 (Yₛ.p.obj y')) lhs := by
      have haOver : Xₛ.p.IsHomLift (𝟙 (Yₛ.p.obj y')) aExplicit.1 := aExplicit.2
      letI : Xₛ.p.IsHomLift (𝟙 (Yₛ.p.obj y')) aExplicit.1 := haOver
      have hFaOver : Yₛ.p.IsHomLift (𝟙 (Yₛ.p.obj y'))
          ((toBasedFunctor F).map aExplicit.1) := by
        infer_instance
      letI : Yₛ.p.IsHomLift (𝟙 (Yₛ.p.obj y')) ((toBasedFunctor F).map aExplicit.1) :=
        hFaOver
      have hQOver :
          Yₛ.p.IsHomLift (𝟙 (Yₛ.p.obj y'))
            (factorizationTargetPullbackObject F Q₀ i).comparison := by
        simpa [factorizationTargetPullbackObject] using
          (factorizationTargetPullbackObject F Q₀ i).comparison_over
      letI : Yₛ.p.IsHomLift (𝟙 (Yₛ.p.obj y'))
          (factorizationTargetPullbackObject F Q₀ i).comparison := hQOver
      exact
        IsHomLift.comp_lift_id_right' (p := Yₛ.p) (𝟙 (Yₛ.p.obj y'))
          ((toBasedFunctor F).map aExplicit.1) (Yₛ.p.obj y')
          (factorizationTargetPullbackObject F Q₀ i).comparison
    have hrhs : Yₛ.p.IsHomLift (𝟙 (Yₛ.p.obj y')) rhs := by
      simpa [rhs, factorizationTargetPullbackObject] using
        (factorizationTargetPullbackObject F P₀ i).comparison_over
    suffices hmain : lhs = rhs by
      change lhs = rhs ≫ 𝟙 y'
      rw [hmain]
      exact (Category.comp_id rhs).symm
    have hi : Yₛ.p.IsStronglyCartesian (Yₛ.p.map i) i := by
      infer_instance
    refine
      @Functor.IsStronglyCartesian.ext _ _ _ _ Yₛ.p _ _ _ _
        (Yₛ.p.map i) i hi _ _ (𝟙 (Yₛ.p.obj y')) lhs rhs hlhs hrhs ?_
    have hQcomm :
        (factorizationTargetPullbackObject F Q₀ i).comparison ≫ i =
          (toBasedFunctor F).map
              (fibredInGroupoidsFactorizationToTarget_left_pullback_map (toBasedFunctor F) Q₀ i) ≫
            e'.hom.1 := by
      simpa [Q₀] using (factorizationTargetPullback_comm F Q₀ i).w.symm
    have hPcomm :
        (factorizationTargetPullbackObject F P₀ i).comparison ≫ i =
          (toBasedFunctor F).map
              (fibredInGroupoidsFactorizationToTarget_left_pullback_map (toBasedFunctor F) P₀ i) ≫
            e.hom.1 := by
      simpa [P₀] using (factorizationTargetPullback_comm F P₀ i).w.symm
    have hafterQ :
        lhs ≫ i =
          (toBasedFunctor F).map aExplicit.1 ≫
            (toBasedFunctor F).map
              (fibredInGroupoidsFactorizationToTarget_left_pullback_map (toBasedFunctor F) Q₀ i) ≫
              e'.hom.1 := by
      simpa [lhs, Category.assoc] using
        congrArg (fun k ↦ (toBasedFunctor F).map aExplicit.1 ≫ k) hQcomm
    have hbeforeP :
        (toBasedFunctor F).map
              (fibredInGroupoidsFactorizationToTarget_left_pullback_map (toBasedFunctor F) P₀ i) ≫
            e.hom.1 =
          rhs ≫ i := by
      simpa [rhs] using hPcomm.symm
    exact hafterQ.trans (hpost_core.trans hbeforeP)
  let φ : factorizationTargetPullbackObject F P₀ i ⟶ factorizationTargetPullbackObject F Q₀ i :=
    { base := 𝟙 (Yₛ.p.obj y')
      a := aExplicit.1
      a_over := aExplicit.2
      b := 𝟙 y'
      b_over := by
        exact IsHomLift.id (p := Yₛ.p) (show Yₛ.p.obj y' = Yₛ.p.obj y' from rfl)
      comm := hcomm }
  refine ⟨⟨φ, ?_⟩⟩
  -- The constructed morphism is vertical for the target projection because its target component
  -- is the identity on `y'`.
  have hmap : Ftarget.toFunctor.map φ = 𝟙 y' := by
    rfl
  rw [← hmap]
  exact Functor.IsHomLift.map φ

/-- Helper for Lemma 8.11.3: a strict source-lift square gives an isomorphism between the
canonical pullbacks of the corresponding strict target-factorization objects. -/
theorem strictTargetPullbackIsoOfSourceLiftSquare
    (F : Xₛ ⟶ Yₛ) {y y' : Yₛ.S} (i : y' ⟶ y)
    [IsFibredInGroupoids
      (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor]
    (x x' : Xₛ.p.Fiber (Yₛ.p.obj y))
    (e : (F.fiberFunctor (Yₛ.p.obj y)).obj x ≅
      Functor.Fiber.mk (p := Yₛ.p) (show Yₛ.p.obj y = Yₛ.p.obj y from rfl))
    (e' : (F.fiberFunctor (Yₛ.p.obj y)).obj x' ≅
      Functor.Fiber.mk (p := Yₛ.p) (show Yₛ.p.obj y = Yₛ.p.obj y from rfl))
    (a : (Yₛ.p.map i) ^*[canonicalPullbackChoice Xₛ.p] x ⟶
        (Yₛ.p.map i) ^*[canonicalPullbackChoice Xₛ.p] x')
    (hsq :
      CommSq
        (((canonicalPullbackChoice Yₛ.p).pullbackFunctor (Yₛ.p.map i)).map
          (e.hom ≫ e'.inv))
        (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) (Yₛ.p.map i) x).hom
        (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) (Yₛ.p.map i) x').hom
        ((F.fiberFunctor (Yₛ.p.obj y')).map a)) :
    let Ftarget := fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)
    let P₀ := strictTargetFactorizationObject F x e
    let Q₀ := strictTargetFactorizationObject F x' e'
    Nonempty
      (i ^*[canonicalPullbackChoice Ftarget.toFunctor]
          Functor.Fiber.mk (p := Ftarget.toFunctor)
            (show Ftarget.toFunctor.obj P₀ = y from rfl) ≅
        i ^*[canonicalPullbackChoice Ftarget.toFunctor]
          Functor.Fiber.mk (p := Ftarget.toFunctor)
            (show Ftarget.toFunctor.obj Q₀ = y from rfl)) := by
  let Ftarget := fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)
  let P₀ := strictTargetFactorizationObject F x e
  let Q₀ := strictTargetFactorizationObject F x' e'
  obtain ⟨φ⟩ :=
    strictTargetPullbackHomOfSourceLiftSquare
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F i x x' e e' a hsq
  obtain ⟨ePcan⟩ := factorizationTargetPullback_iso_canonical F P₀ i
  obtain ⟨eQcan⟩ := factorizationTargetPullback_iso_canonical F Q₀ i
  have hφIso : IsIso φ := IsFibredInGroupoids.hom_isIso y' φ
  letI : IsIso φ := hφIso
  -- The explicit pullback hom is an isomorphism, so conjugate it by the two canonical
  -- comparison isomorphisms.
  exact ⟨ePcan.symm ≪≫ asIso φ ≪≫ eQcan⟩

/-- Helper for Lemma 8.11.3: source-local lifts give a cover of a strict target object on which
the strict factorization objects have isomorphic canonical pullbacks. -/
theorem strictTargetPullbackIsoCoverOfSourceLifts
    (F : Xₛ ⟶ Yₛ)
    (hlift : LocallyLiftsFiberMorphisms F)
    [IsFibredInGroupoids
      (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor]
    {y : Yₛ.S}
    (x x' : Xₛ.p.Fiber (Yₛ.p.obj y))
    (e : (F.fiberFunctor (Yₛ.p.obj y)).obj x ≅
      Functor.Fiber.mk (p := Yₛ.p) (show Yₛ.p.obj y = Yₛ.p.obj y from rfl))
    (e' : (F.fiberFunctor (Yₛ.p.obj y)).obj x' ≅
      Functor.Fiber.mk (p := Yₛ.p) (show Yₛ.p.obj y = Yₛ.p.obj y from rfl)) :
    let Ftarget := fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)
    let P₀ := strictTargetFactorizationObject F x e
    let Q₀ := strictTargetFactorizationObject F x' e'
    ∃ S : (inheritedTopology J Yₛ).Cover y, ∀ I : S.Arrow,
      Nonempty
        (I.f ^*[canonicalPullbackChoice Ftarget.toFunctor]
            Functor.Fiber.mk (p := Ftarget.toFunctor)
              (show Ftarget.toFunctor.obj P₀ = y from rfl) ≅
          I.f ^*[canonicalPullbackChoice Ftarget.toFunctor]
            Functor.Fiber.mk (p := Ftarget.toFunctor)
              (show Ftarget.toFunctor.obj Q₀ = y from rfl)) := by
  let Ftarget := fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)
  let P₀ := strictTargetFactorizationObject F x e
  let Q₀ := strictTargetFactorizationObject F x' e'
  obtain ⟨Sbase, hSbase⟩ := hlift x x' (e.hom ≫ e'.inv)
  refine
    ⟨⟨(Sbase : Sieve (Yₛ.p.obj y)).functorPullback Yₛ.p,
        baseCover_liftedPullbackCover_mem_inheritedTopology
          (J := J) (Yₛ := Yₛ) (y := y) Sbase⟩, ?_⟩
  intro I
  -- Pull the source-local lift indexed by the projected base arrow back to this inherited
  -- cover arrow, then convert it into a canonical target-pullback isomorphism.
  have hbase : (Sbase : Sieve (Yₛ.p.obj y)) (Yₛ.p.map I.f) := I.hf
  let Ibase : Sbase.Arrow := ⟨Yₛ.p.obj I.Y, Yₛ.p.map I.f, hbase⟩
  obtain ⟨a, hsq⟩ := hSbase Ibase
  exact
    strictTargetPullbackIsoOfSourceLiftSquare
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F I.f x x' e e' a hsq

/-- Helper for Lemma 8.11.3: source-local lifting should produce local isomorphisms between
canonical target-factorization pullbacks. -/
theorem localTargetPullbackIsoCoverOfSourceLifts
    (F : Xₛ ⟶ Yₛ)
    (hlift : LocallyLiftsFiberMorphisms F)
    [IsFibredInGroupoids
      (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor]
    {yTotal : Yₛ.S}
    (P Q : (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor.Fiber
      yTotal) :
    ∃ S : (inheritedTopology J Yₛ).Cover yTotal, ∀ I : S.Arrow,
      Nonempty
        (I.f ^*[
            canonicalPullbackChoice
              (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor] P ≅
          I.f ^*[
            canonicalPullbackChoice
              (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor] Q) := by
  let Ftarget := fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)
  -- Normalize the first target-factorization fiber object to a literal target object and base.
  rcases P with ⟨Pobj, hP⟩
  rcases Pobj with ⟨UP, Pdata⟩
  rcases Pdata with ⟨x, yP, eP⟩
  rcases yP with ⟨y, hyP⟩
  dsimp [Ftarget, fibredInGroupoidsFactorizationToTarget] at hP
  subst hP
  subst hyP
  -- Normalize the second object against the same target object, eliminating all remaining
  -- target-object transport before invoking the strict cover helper.
  rcases Q with ⟨Qobj, hQ⟩
  rcases Qobj with ⟨UQ, Qdata⟩
  rcases Qdata with ⟨x', yQ, eQ⟩
  rcases yQ with ⟨y', hyQ⟩
  dsimp [Ftarget, fibredInGroupoidsFactorizationToTarget] at hQ
  subst hQ
  subst hyQ
  exact
    strictTargetPullbackIsoCoverOfSourceLifts
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F hlift x x' eP eQ

end

end StackInGroupoidsOver.Hom

end CategoryTheory
