import StacksProject_2024.Chap08.Lemma_8_11_3.SourceLiftToTargetPullback

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

/-- Helper for Lemma 8.11.3: for the canonical strict factorization, the gerbe condition over the
inherited target topology is exactly the two source-facing local lifting conditions. -/
theorem canonicalFactorizationToTarget_isGerbeOverInheritedTopology_iff_localConditions
    (F : Xₛ ⟶ Yₛ) :
    IsGerbe (inheritedTopology J Yₛ)
      (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor ↔
      LocallyEssentiallySurjectiveOnObjects F ∧
        LocallyLiftsFiberMorphisms F := by
  constructor
  · intro hgerbe
    constructor
    · intro U y
      rcases y with ⟨yTotal, rfl⟩
      let yFiber : Yₛ.p.Fiber (Yₛ.p.obj yTotal) :=
        Functor.Fiber.mk (p := Yₛ.p) (show Yₛ.p.obj yTotal = Yₛ.p.obj yTotal from rfl)
      obtain ⟨T, hT⟩ := hgerbe.locally_inhabited yTotal
      let S : J.Cover (Yₛ.p.obj yTotal) :=
        ⟨Sieve.ofArrows (fun I : T.Arrow ↦ Yₛ.p.obj I.Y) (fun I ↦ Yₛ.p.map I.f),
          inheritedCover_arrowFamily_baseCovering (J := J) (Yₛ := Yₛ) T⟩
      refine ⟨S, ?_⟩
      intro I
      change ∃ x : Xₛ.p.Fiber I.Y,
        Nonempty (((fiberFunctor F I.Y).obj x) ≅
          (canonicalPullbackChoice Yₛ.p).pullbackFunctor I.f |>.obj yFiber)
      -- Refine the projected base arrow through an inherited-cover arrow and read the
      -- factorization object's source component after the extra base pullback.
      have hI :
          Sieve.ofArrows (fun I : T.Arrow ↦ Yₛ.p.obj I.Y) (fun I ↦ Yₛ.p.map I.f)
            I.f := by
        simpa [S] using I.hf
      rw [Sieve.mem_ofArrows_iff] at hI
      rcases hI with ⟨A, g, hg⟩
      obtain ⟨P⟩ := hT A
      simpa [hg] using
        (canonicalFactorization_fiber_localEssentialImageDatum_comp
          (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F A.f g P)
    · intro U x x' b
      -- Build the two special factorization objects `(x, F x', b)` and `(x', F x', id)`.
      -- The gerbe cover between them is an inherited cover on the target total category, so
      -- projecting it gives the base cover required by the source-facing lifting predicate.
      let Ftarget := fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)
      have hb : IsIso b := IsFibredInGroupoids.hom_isIso U b
      let y : Yₛ.p.Fiber U := (F.fiberFunctor U).obj x'
      let P₀ : (fibredInGroupoidsFactorization (toBasedFunctor F)).obj :=
        { U := U
          obj := { fst := x, snd := y, iso := asIso b } }
      let Q₀ : (fibredInGroupoidsFactorization (toBasedFunctor F)).obj :=
        { U := U
          obj := { fst := x', snd := y, iso := Iso.refl y } }
      let P : Ftarget.toFunctor.Fiber y.1 := ⟨P₀, rfl⟩
      let Q : Ftarget.toFunctor.Fiber y.1 := ⟨Q₀, rfl⟩
      obtain ⟨T, _hT⟩ := hgerbe.locally_isomorphic P Q
      let Sbase : J.Cover (Yₛ.p.obj y.1) :=
        ⟨Sieve.ofArrows (fun I : T.Arrow ↦ Yₛ.p.obj I.Y) (fun I ↦ Yₛ.p.map I.f),
          inheritedCover_arrowFamily_baseCovering (J := J) (Yₛ := Yₛ) T⟩
      let S : J.Cover U := y.2 ▸ Sbase
      refine ⟨S, ?_⟩
      intro I
      have hIbase :
          (Sbase : Sieve (Yₛ.p.obj y.1)) (I.f ≫ eqToHom y.2.symm) := by
        -- Undo the transport from `Sbase` along the fiber equality of `y`.
        simpa [S] using
          coverCast_arrow_mem_original (J := J) y.2 Sbase I
      rw [Sieve.mem_ofArrows_iff] at hIbase
      rcases hIbase with ⟨A, g, hg⟩
      let Aobj : Yₛ.p.Fiber (Yₛ.p.obj A.Y) := ⟨A.Y, rfl⟩
      let pulledA : Yₛ.S := (g ^*[canonicalPullbackChoice Yₛ.p] Aobj).1
      let χ : pulledA ⟶ A.Y := (canonicalPullbackChoice Yₛ.p).map g Aobj
      let B : T.Arrow := A.precomp χ
      obtain ⟨eB⟩ := _hT B
      have hχbase :
          Yₛ.p.map χ =
            eqToHom ((g ^*[canonicalPullbackChoice Yₛ.p] Aobj).2) ≫ g := by
        -- Record the base map of the target-side canonical pullback arrow.
        letI : Yₛ.p.IsHomLift g χ := by
          simpa [χ] using
            (show Yₛ.p.IsHomLift g ((canonicalPullbackChoice Yₛ.p).map g Aobj) from
              by
                let _ :
                    Yₛ.p.IsStronglyCartesian g
                      ((canonicalPullbackChoice Yₛ.p).map g Aobj) :=
                  (canonicalPullbackChoice Yₛ.p).isStronglyCartesian g Aobj
                infer_instance)
        simpa [pulledA, χ] using (IsHomLift.fac' Yₛ.p g χ)
      have hBbase :
          Yₛ.p.map B.f =
            eqToHom ((g ^*[canonicalPullbackChoice Yₛ.p] Aobj).2) ≫
              I.f ≫ eqToHom y.2.symm := by
        -- The refined total arrow `B` projects to the generated base arrow represented by `I`.
        simp [B, χ, hχbase, Category.assoc, hg]
      have hPullBase :
          fibredInGroupoidsFactorizationToTarget_pullbackBase
              (toBasedFunctor F) (P := P₀) B.f =
            eqToHom ((g ^*[canonicalPullbackChoice Yₛ.p] Aobj).2) ≫ I.f := by
        -- The factorization target transport cancels the final fiber equality in `hBbase`.
        dsimp [fibredInGroupoidsFactorizationToTarget_pullbackBase,
          fibredInGroupoidsFactorizationToTarget, P₀]
        -- Postcompose the projected-arrow equation by the target fiber transport and cancel it.
        have hpost := congrArg (fun k ↦ k ≫ eqToHom y.2) hBbase
        refine hpost.trans ?_
        calc
          (eqToHom ((g ^*[canonicalPullbackChoice Yₛ.p] Aobj).2) ≫
                I.f ≫ eqToHom y.2.symm) ≫
              eqToHom y.2 =
            eqToHom ((g ^*[canonicalPullbackChoice Yₛ.p] Aobj).2) ≫
                I.f ≫ (eqToHom y.2.symm ≫ eqToHom y.2) := by
              simp [Category.assoc]
          _ =
            eqToHom ((g ^*[canonicalPullbackChoice Yₛ.p] Aobj).2) ≫ I.f := by
              simp
      obtain ⟨ePcan⟩ := factorizationTargetPullback_iso_canonical F P₀ B.f
      obtain ⟨eQcan⟩ := factorizationTargetPullback_iso_canonical F Q₀ B.f
      let eExplicit :
          (Functor.Fiber.mk
              (p := Ftarget.toFunctor)
              (show Ftarget.toFunctor.obj (factorizationTargetPullbackObject F P₀ B.f) = B.Y from
                rfl)) ≅
            (Functor.Fiber.mk
              (p := Ftarget.toFunctor)
              (show Ftarget.toFunctor.obj (factorizationTargetPullbackObject F Q₀ B.f) = B.Y from
                rfl)) :=
        ePcan ≪≫ eB ≪≫ eQcan.symm
      let hdom : Yₛ.p.obj B.Y = I.Y := (g ^*[canonicalPullbackChoice Yₛ.p] Aobj).2
      have hbExplicit : eExplicit.hom.1.b = 𝟙 B.Y :=
        targetPullbackFiberHom_targetComponent_eq_id F P₀ Q₀ B.f B.f eExplicit.hom
      have hPullBaseQ :
          fibredInGroupoidsFactorizationToTarget_pullbackBase
              (toBasedFunctor F) (P := Q₀) B.f =
            eqToHom hdom ≫ I.f := by
        -- The second special factorization object has the same target component as `P₀`.
        simpa [hdom, Q₀] using hPullBase
      -- Route correction: instead of conjugating an arbitrary casted source component, use the
      -- equation-carrying bridge, which constructs the comparison isomorphisms after normalizing
      -- the external base object.
      exact
        sourceLiftOfVerticalTargetPullbackHom
          (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F x x' b B.f hdom I.f
          hPullBase hPullBaseQ eExplicit.hom.1 hbExplicit
  · intro hlocal
    rcases hlocal with ⟨hess, hlift⟩
    let Fsource := fibredInGroupoidsFactorizationFromSource (toBasedFunctor F)
    let Ftarget := fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)
    letI : IsFibredInGroupoids Ftarget.toFunctor :=
      fibredInGroupoidsFactorizationToTarget_isFibredInGroupoids (toBasedFunctor F)
    have hsourceEquiv : Fsource.IsEquivalenceOverBase :=
      fibredInGroupoidsFactorizationFromSource_isEquivalenceOverBase (toBasedFunctor F)
    refine
      { toIsStackInGroupoids :=
          factorizationProjection_isStackInGroupoidsOverInheritedTopology
            (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) Fsource Ftarget hsourceEquiv
        locally_inhabited := ?_
        locally_isomorphic := ?_ }
    · intro y
      let yFiber : Yₛ.p.Fiber (Yₛ.p.obj y) := ⟨y, rfl⟩
      obtain ⟨S, hS⟩ := hess (Yₛ.p.obj y) yFiber
      refine
        ⟨⟨(S : Sieve (Yₛ.p.obj y)).functorPullback Yₛ.p,
            baseCover_liftedPullbackCover_mem_inheritedTopology
              (J := J) (Yₛ := Yₛ) (y := y) S⟩, ?_⟩
      intro I
      change Nonempty (Ftarget.toFunctor.Fiber I.Y)
      have hbase : (S : Sieve (Yₛ.p.obj y)) (Yₛ.p.map I.f) := I.hf
      let Ibase : S.Arrow := ⟨Yₛ.p.obj I.Y, Yₛ.p.map I.f, hbase⟩
      obtain ⟨x, hx⟩ := hS Ibase
      obtain ⟨e⟩ := hx
      let pulledY : Yₛ.p.Fiber (Yₛ.p.obj I.Y) := ⟨I.Y, rfl⟩
      -- Compare the literal source of the inherited-cover arrow with the canonical pullback
      -- used in the local essential-surjectivity predicate.
      obtain ⟨ey⟩ := totalArrow_domain_iso_canonicalPullback_nonempty (J := J) (Yₛ := Yₛ) I.f
      exact
        canonicalFactorization_fiber_nonempty_of_iso (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ)
          F x pulledY (e ≪≫ ey.symm)
    · -- The converse local-isomorphism assembly is isolated in the named bridge helper so the
      -- main gerbe proof no longer carries the dependent transport details inline.
      intro yTotal P Q
      exact
        localTargetPullbackIsoCoverOfSourceLifts
          (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F hlift P Q

end

end StackInGroupoidsOver.Hom

end CategoryTheory
