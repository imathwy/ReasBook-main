import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap01.Theorem_1_2_9
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Corollary_3_7_8
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Definition_3_4_9
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Example_3_3_9
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Theorem_3_5_8

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory FundamentalGroupoid
open CategoryTheory.Functor.IsCovering
open Path.Homotopic.Quotient (symm)
open scoped FundamentalGroup

universe u

variable {E E' B : Type u}
  [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B]

namespace IsPathConnectedCoveringMap

variable {p : C(E, B)} {p' : C(E', B)}

/-- A morphism of covering spaces over `B` sends the fiber of `p` over `b` into the fiber of `p'`
over `b`. -/
-- Proof sketch: apply the commutative-triangle relation `Over.w h` to the chosen point of the
-- fiber and rewrite with the defining equation of that fiber point.
theorem coveringSpaceHom_obj_mem_fiber {b : B}
    (h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p')) (e : p ⁻¹' {b}) :
    p' (h.left.hom e.1) = b := by
  exact (Over.w_apply h e.1).trans e.2

/-- Restriction of a morphism of covering spaces over `B` to the fiber over `b`. -/
def coveringSpaceHomToFiberFun (b : B) :
    (Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p')) →
      p ⁻¹' {b} → p' ⁻¹' {b} :=
  fun h e ↦ ⟨h.left.hom e.1, coveringSpaceHom_obj_mem_fiber h e⟩

section

/-- The identity loop acts trivially on the fiber over `b` via monodromy. -/
-- Proof sketch: this is the identity law for the monodromy functor of the covering map.
theorem fiberMonodromy_one (hp : IsPathConnectedCoveringMap p) (b : B) (x : p ⁻¹' {b}) :
    hp.isCoveringMap.monodromy (1 : FundamentalGroup B b).toPath x = x := by
  -- The constant loop has trivial monodromy.
  simpa [loop_homotopy_one_eq_refl] using congrFun hp.isCoveringMap.monodromy_refl x

/-- Monodromy along loops in `π₁(B, b)` defines a left action on the fiber over `b`. -/
-- Proof sketch: `monodromyFunctor` is a functor, so it turns composition in
-- `FundamentalGroupoid B` into function composition on the fiber, while
-- `loop_homotopy_mul_eq_trans` identifies multiplication in `π₁(B,b)` with the corresponding
-- loop-class composition order.
theorem fiberMonodromy_mul (hp : IsPathConnectedCoveringMap p) (b : B)
    (γ₁ γ₂ : FundamentalGroup B b) (x : p ⁻¹' {b}) :
    hp.isCoveringMap.monodromy (γ₁ * γ₂).toPath x =
      hp.isCoveringMap.monodromy γ₁.toPath
        (hp.isCoveringMap.monodromy γ₂.toPath x) := by
  -- Route correction: `FundamentalGroup B b` uses the `End`-based multiplication on loop classes,
  -- so the correct ordinary-fiber action is by direct monodromy, not by inverse loops.
  change hp.isCoveringMap.monodromy
      ((γ₁.toPath * γ₂.toPath : Path.Homotopic.Quotient b b)) x =
    hp.isCoveringMap.monodromy γ₁.toPath
      (hp.isCoveringMap.monodromy γ₂.toPath x)
  -- Rewrite the group product as path-class concatenation, then apply monodromy functoriality.
  rw [loop_homotopy_mul_eq_trans]
  simpa using hp.isCoveringMap.monodromy_trans_apply γ₂.toPath γ₁.toPath x

/-- The monodromy action of `π₁(B, b)` on the fiber over `b`, obtained by transporting the
canonical fiber-translation action of the induced covering functor on `Π(B)` across the fiber
equivalence of Proposition 3.3.4. -/
@[reducible] noncomputable def fiberMonodromyMulAction
    (hp : IsPathConnectedCoveringMap p) (b : B) :
    MulAction (FundamentalGroup B b) (p ⁻¹' {b}) where
  smul γ x := hp.fiberTranslationMap γ.toPath x
  one_smul := by
    intro x
    -- The identity element acts by monodromy along the constant loop.
    change hp.fiberTranslationMap (1 : FundamentalGroup B b).toPath x = x
    rw [hp.fiberTranslationMap_eq_monodromy]
    exact fiberMonodromy_one hp b x
  mul_smul := by
    intro γ₁ γ₂ x
    -- Multiplication in `π₁(B, b)` matches composition of the direct monodromy maps.
    change hp.fiberTranslationMap (γ₁ * γ₂).toPath x =
      hp.fiberTranslationMap γ₁.toPath (hp.fiberTranslationMap γ₂.toPath x)
    rw [hp.fiberTranslationMap_eq_monodromy]
    rw [hp.fiberTranslationMap_eq_monodromy]
    rw [hp.fiberTranslationMap_eq_monodromy]
    exact fiberMonodromy_mul hp b γ₁ γ₂ x

/-- The fiber over `b` carries its canonical monodromy action of `π₁(B, b)`. -/
noncomputable instance instFiberMonodromyMulAction [hp : IsPathConnectedCoveringMap p] (b : B) :
    MulAction (FundamentalGroup B b) (p ⁻¹' {b}) :=
  fiberMonodromyMulAction hp b

/-- Helper for Theorem 3.7.9: restriction to the ordinary fiber agrees pointwise with the
categorical restriction map on the induced covering functors over `Π(B)`, transported across the
canonical fiber equivalence. -/
theorem coveringSpaceHomToFiberFun_eq_groupoidFiberMap
    (hp : IsPathConnectedCoveringMap p) (hp' : IsPathConnectedCoveringMap p') (b : B)
    (h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p')) (e : p ⁻¹' {b}) :
    coveringSpaceHomToFiberFun b h e =
      hp'.fundamentalGroupoidMapFiberEquiv b
        (mapOfCoveringsToFiberFun (mk b)
          (hp.toFundamentalGroupoidCoveringHom hp' h)
          ((hp.fundamentalGroupoidMapFiberEquiv b).symm e)) := by
  -- Both sides are the image of `e.1` under the same underlying map of total spaces.
  apply Subtype.ext
  rfl

/-- Helper for Theorem 3.7.9: transporting categorical fiber translation along the loop `γ`
through the canonical fiber equivalence recovers the ordinary fiber translation map. -/
theorem fundamentalGroupoidMapFiberEquiv_fiberTranslation
    (hp : IsPathConnectedCoveringMap p) (b : B) (γ : FundamentalGroup B b)
    (ξ : hp.fundamentalGroupoidMap.Fiber (mk b)) :
    hp.fundamentalGroupoidMapFiberEquiv b
        (Functor.IsCovering.fiberTranslationMap hp.fundamentalGroupoidMap_isCovering γ.toPath ξ) =
      hp.fiberTranslationMap γ.toPath (hp.fundamentalGroupoidMapFiberEquiv b ξ) := by
  -- This is exactly how `fiberTranslationMap` was defined in Example 3.3.9.
  apply Subtype.ext
  rfl

/-- Restriction to the fiber over `b` commutes with the monodromy action of `π₁(B, b)`. -/
-- Proof sketch: apply `mapOfCoveringsToFiberFun_comm` to the induced morphism of covering
-- functors on fundamental groupoids from Corollary 3.7.8, then transport the resulting
-- equivariance statement across the fiber equivalences of Proposition 3.3.4 and identify fiber
-- translation with monodromy using Example 3.3.9.
theorem coveringSpaceHomToFiberFun_comm
    [hp : IsPathConnectedCoveringMap p] [hp' : IsPathConnectedCoveringMap p'] (b : B)
    (h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p')) (γ : FundamentalGroup B b)
    (e : p ⁻¹' {b}) :
    coveringSpaceHomToFiberFun b h (γ • e) = γ • coveringSpaceHomToFiberFun b h e := by
  letI := fiberTranslationMulAction hp.fundamentalGroupoidMap_isCovering (mk b)
  letI := fiberTranslationMulAction hp'.fundamentalGroupoidMap_isCovering (mk b)
  let ξ : hp.fundamentalGroupoidMap.Fiber (mk b) := (hp.fundamentalGroupoidMapFiberEquiv b).symm e
  let δ : mk b ⟶ mk b := (γ⁻¹).toPath
  have hinv_toPath :
      δ⁻¹ = γ.toPath := by
    -- Undoing the inverse-loop scalar recovers the direct loop class on `Π(B)`.
    change symm ((γ⁻¹).toPath) = γ.toPath
    change symm (symm γ.toPath) = γ.toPath
    refine Quotient.inductionOn γ.toPath ?_
    intro p
    change (⟦p.symm.symm⟧ : Path.Homotopic.Quotient b b) = ⟦p⟧
    simp
  have hsource :
      δ • ξ =
        Functor.IsCovering.fiberTranslationMap hp.fundamentalGroupoidMap_isCovering γ.toPath ξ := by
    -- The source-facing categorical action uses inverse loops, so acting by `γ⁻¹` translates
    -- exactly by the direct loop `γ`.
    simpa [hinv_toPath] using
      (Functor.vertexGroupAction_smul_eq_map_inv
        (fiberTranslationFunctor hp.fundamentalGroupoidMap_isCovering) (mk b) δ ξ)
  have htarget :
      (δ •
          (mapOfCoveringsToFiberFun (mk b)
            (hp.toFundamentalGroupoidCoveringHom hp' h) ξ)) =
        Functor.IsCovering.fiberTranslationMap
          hp'.fundamentalGroupoidMap_isCovering γ.toPath
          (mapOfCoveringsToFiberFun (mk b)
            (hp.toFundamentalGroupoidCoveringHom hp' h) ξ) := by
    -- The same inverse-loop convention governs the target categorical fiber.
    simpa [hinv_toPath] using
      (Functor.vertexGroupAction_smul_eq_map_inv
        (fiberTranslationFunctor hp'.fundamentalGroupoidMap_isCovering)
        (mk b) δ (mapOfCoveringsToFiberFun (mk b) (hp.toFundamentalGroupoidCoveringHom hp' h) ξ))
  have hξsmul :
      (hp.fundamentalGroupoidMapFiberEquiv b).symm (γ • e) =
        Functor.IsCovering.fiberTranslationMap hp.fundamentalGroupoidMap_isCovering γ.toPath ξ := by
    -- Transport the monodromy action back through the canonical fiber equivalence.
    apply (hp.fundamentalGroupoidMapFiberEquiv b).injective
    calc
      hp.fundamentalGroupoidMapFiberEquiv b
          ((hp.fundamentalGroupoidMapFiberEquiv b).symm (γ • e)) = γ • e := by
            simp
      _ = hp.fiberTranslationMap γ.toPath (hp.fundamentalGroupoidMapFiberEquiv b ξ) := by
            change hp.fiberTranslationMap γ.toPath e =
              hp.fiberTranslationMap γ.toPath (hp.fundamentalGroupoidMapFiberEquiv b ξ)
            simp [ξ]
      _ =
          hp.fundamentalGroupoidMapFiberEquiv b
            (Functor.IsCovering.fiberTranslationMap
              hp.fundamentalGroupoidMap_isCovering γ.toPath ξ) := by
            exact (fundamentalGroupoidMapFiberEquiv_fiberTranslation hp b γ ξ).symm
  -- Apply equivariance on categorical fibers and transport the result back to ordinary fibers.
  calc
    coveringSpaceHomToFiberFun b h (γ • e) =
        hp'.fundamentalGroupoidMapFiberEquiv b
          (mapOfCoveringsToFiberFun (mk b)
            (hp.toFundamentalGroupoidCoveringHom hp' h)
            ((hp.fundamentalGroupoidMapFiberEquiv b).symm (γ • e))) := by
          simpa using coveringSpaceHomToFiberFun_eq_groupoidFiberMap hp hp' b h (γ • e)
    _ =
        hp'.fundamentalGroupoidMapFiberEquiv b
          (mapOfCoveringsToFiberFun (mk b)
            (hp.toFundamentalGroupoidCoveringHom hp' h)
            (Functor.IsCovering.fiberTranslationMap
              hp.fundamentalGroupoidMap_isCovering γ.toPath ξ)) := by
          rw [hξsmul]
    _ =
        hp'.fundamentalGroupoidMapFiberEquiv b
          (Functor.IsCovering.fiberTranslationMap hp'.fundamentalGroupoidMap_isCovering γ.toPath
            (mapOfCoveringsToFiberFun (mk b) (hp.toFundamentalGroupoidCoveringHom hp' h) ξ)) := by
          rw [← hsource]
          rw [mapOfCoveringsToFiberFun_comm
            hp.fundamentalGroupoidMap_isCovering hp'.fundamentalGroupoidMap_isCovering (mk b)
            (hp.toFundamentalGroupoidCoveringHom hp' h) δ ξ]
          exact congrArg (hp'.fundamentalGroupoidMapFiberEquiv b) htarget
    _ =
        hp'.fiberTranslationMap γ.toPath
          (hp'.fundamentalGroupoidMapFiberEquiv b
            (mapOfCoveringsToFiberFun (mk b) (hp.toFundamentalGroupoidCoveringHom hp' h) ξ)) := by
          exact fundamentalGroupoidMapFiberEquiv_fiberTranslation hp' b γ
            (mapOfCoveringsToFiberFun (mk b) (hp.toFundamentalGroupoidCoveringHom hp' h) ξ)
    _ = γ • coveringSpaceHomToFiberFun b h e := by
          rw [coveringSpaceHomToFiberFun_eq_groupoidFiberMap hp hp' b h e]
          rfl

/-- Restriction to the fiber over `b` as a bundled `π₁(B, b)`-equivariant map. -/
def coveringSpaceHomToFiber
    [hp : IsPathConnectedCoveringMap p] [hp' : IsPathConnectedCoveringMap p'] (b : B) :
    (Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p')) →
      (p ⁻¹' {b}) →[FundamentalGroup B b] (p' ⁻¹' {b}) :=
  fun h ↦
    { toFun := coveringSpaceHomToFiberFun b h
      map_smul' := coveringSpaceHomToFiberFun_comm b h }

variable [PathConnectedSpace E] [LocPathConnectedSpace E]

/-- Theorem 3.7.9: for path-connected covering spaces `p : E → B` and `p' : E' → B`, restriction
to the fiber over `b` gives a bijection between morphisms of covering spaces over `B` and
`π₁(B, b)`-equivariant maps `(p ⁻¹' {b}) → (p' ⁻¹' {b})`. -/
-- Proof sketch: Corollary 3.7.8 identifies morphisms of covering spaces with morphisms of the
-- induced covering functors on fundamental groupoids. Then `mapOfCoveringsToFiber_bijective`,
-- applied to those induced covering functors at `mk b`, gives the canonical bijection on groupoid
-- fibers. Transport that bijection across `fundamentalGroupoidMapFiberEquiv` and use Example 3.3.9
-- to identify the transported action with monodromy on the topological fibers.
theorem coveringSpaceHomToFiber_bijective
    [hp : IsPathConnectedCoveringMap p] [hp' : IsPathConnectedCoveringMap p'] (b : B) :
    Function.Bijective
      ((coveringSpaceHomToFiber b :
        (Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p')) →
          (p ⁻¹' {b}) →[FundamentalGroup B b] (p' ⁻¹' {b}))) := by
  letI : CategoryTheory.IsConnected (FundamentalGroupoid E) := by
    refine CategoryTheory.IsConnected.of_any_functor_const_on_obj ?_
    intro α F x y
    ext
    exact CategoryTheory.Discrete.eq_of_hom <|
      F.map (show x ⟶ y from ⟦PathConnectedSpace.somePath x.as y.as⟧)
  letI := fiberTranslationMulAction hp.fundamentalGroupoidMap_isCovering (mk b)
  letI := fiberTranslationMulAction hp'.fundamentalGroupoidMap_isCovering (mk b)
  have hTop := toFundamentalGroupoidCoveringHom_bijective hp hp'
  have hGroupoid :=
    mapOfCoveringsToFiber_bijective
      hp.fundamentalGroupoidMap_isCovering hp'.fundamentalGroupoidMap_isCovering (mk b)
  constructor
  · intro h₁ h₂ hEq
    have hFiberEq :
        mapOfCoveringsToFiber
            hp.fundamentalGroupoidMap_isCovering hp'.fundamentalGroupoidMap_isCovering (mk b)
            (hp.toFundamentalGroupoidCoveringHom hp' h₁) =
          mapOfCoveringsToFiber
            hp.fundamentalGroupoidMap_isCovering hp'.fundamentalGroupoidMap_isCovering (mk b)
            (hp.toFundamentalGroupoidCoveringHom hp' h₂) := by
      apply MulActionHom.ext
      intro ξ
      let e : p ⁻¹' {b} := hp.fundamentalGroupoidMapFiberEquiv b ξ
      -- Equality on ordinary fibers transports to equality on categorical fibers.
      apply (hp'.fundamentalGroupoidMapFiberEquiv b).injective
      calc
        hp'.fundamentalGroupoidMapFiberEquiv b
            (mapOfCoveringsToFiberFun (mk b)
              (hp.toFundamentalGroupoidCoveringHom hp' h₁) ξ) =
            coveringSpaceHomToFiber b h₁ e := by
              simpa [coveringSpaceHomToFiber, e] using
                (coveringSpaceHomToFiberFun_eq_groupoidFiberMap hp hp' b h₁ e).symm
        _ = coveringSpaceHomToFiber b h₂ e := by
              exact congrArg (fun φ ↦ φ e) hEq
        _ =
            hp'.fundamentalGroupoidMapFiberEquiv b
              (mapOfCoveringsToFiberFun (mk b)
                (hp.toFundamentalGroupoidCoveringHom hp' h₂) ξ) := by
              simpa [coveringSpaceHomToFiber, e] using
                coveringSpaceHomToFiberFun_eq_groupoidFiberMap hp hp' b h₂ e
    exact hTop.1 (hGroupoid.1 hFiberEq)
  · intro φ
    let φcat :
        hp.fundamentalGroupoidMap.Fiber (mk b) →[(mk b ⟶ mk b)]
          hp'.fundamentalGroupoidMap.Fiber (mk b) :=
      { toFun := fun ξ ↦
          (hp'.fundamentalGroupoidMapFiberEquiv b).symm
            (φ (hp.fundamentalGroupoidMapFiberEquiv b ξ))
        map_smul' := fun γ ξ ↦ by
          -- Transport equivariance of `φ` through the canonical fiber equivalences.
          have htransport :
              hp.fundamentalGroupoidMapFiberEquiv b (γ • ξ) =
                (fiberMonodromyMulAction hp b).smul
                  (γ⁻¹ : FundamentalGroup B b) (hp.fundamentalGroupoidMapFiberEquiv b ξ) := by
            change hp.fundamentalGroupoidMapFiberEquiv b
                (Functor.IsCovering.fiberTranslationMap
                  hp.fundamentalGroupoidMap_isCovering γ⁻¹ ξ) =
              hp.fiberTranslationMap γ⁻¹ (hp.fundamentalGroupoidMapFiberEquiv b ξ)
            exact fundamentalGroupoidMapFiberEquiv_fiberTranslation hp b
              (γ⁻¹) ξ
          have htransport' :
              (fiberMonodromyMulAction hp' b).smul
                  (γ⁻¹ : FundamentalGroup B b) (φ (hp.fundamentalGroupoidMapFiberEquiv b ξ)) =
                hp'.fundamentalGroupoidMapFiberEquiv b
                  (γ • (hp'.fundamentalGroupoidMapFiberEquiv b).symm
                    (φ (hp.fundamentalGroupoidMapFiberEquiv b ξ))) := by
            change hp'.fiberTranslationMap γ⁻¹
                (φ (hp.fundamentalGroupoidMapFiberEquiv b ξ)) =
              hp'.fundamentalGroupoidMapFiberEquiv b
                (Functor.IsCovering.fiberTranslationMap
                  hp'.fundamentalGroupoidMap_isCovering γ⁻¹
                  ((hp'.fundamentalGroupoidMapFiberEquiv b).symm
                    (φ (hp.fundamentalGroupoidMapFiberEquiv b ξ))))
            exact (fundamentalGroupoidMapFiberEquiv_fiberTranslation hp' b
              (γ⁻¹)
              ((hp'.fundamentalGroupoidMapFiberEquiv b).symm
                (φ (hp.fundamentalGroupoidMapFiberEquiv b ξ)))).symm
          apply (hp'.fundamentalGroupoidMapFiberEquiv b).injective
          calc
            hp'.fundamentalGroupoidMapFiberEquiv b
                ((hp'.fundamentalGroupoidMapFiberEquiv b).symm
                  (φ (hp.fundamentalGroupoidMapFiberEquiv b (γ • ξ)))) =
                φ (hp.fundamentalGroupoidMapFiberEquiv b (γ • ξ)) := by
                  simp
            _ = φ ((fiberMonodromyMulAction hp b).smul
                  (γ⁻¹ : FundamentalGroup B b) (hp.fundamentalGroupoidMapFiberEquiv b ξ)) := by
                  exact congrArg φ htransport
            _ = (fiberMonodromyMulAction hp' b).smul
                  (γ⁻¹ : FundamentalGroup B b) (φ (hp.fundamentalGroupoidMapFiberEquiv b ξ)) := by
                  exact φ.map_smul' (γ⁻¹ : FundamentalGroup B b)
                    (hp.fundamentalGroupoidMapFiberEquiv b ξ)
            _ =
                hp'.fundamentalGroupoidMapFiberEquiv b
                  (γ • (hp'.fundamentalGroupoidMapFiberEquiv b).symm
                    (φ (hp.fundamentalGroupoidMapFiberEquiv b ξ))) := by
                  exact htransport' }
    obtain ⟨k, hk⟩ := hGroupoid.2 φcat
    obtain ⟨h, hh⟩ := hTop.2 k
    refine ⟨h, ?_⟩
    apply MulActionHom.ext
    intro e
    let ξ : hp.fundamentalGroupoidMap.Fiber (mk b) := (hp.fundamentalGroupoidMapFiberEquiv b).symm e
    have hkξ :
        mapOfCoveringsToFiber
            hp.fundamentalGroupoidMap_isCovering hp'.fundamentalGroupoidMap_isCovering (mk b)
            (hp.toFundamentalGroupoidCoveringHom hp' h) ξ =
          φcat ξ := by
      simpa [hh] using congrArg (fun ψ ↦ ψ ξ) hk
    -- The categorical surjection lifts back to the required topological covering map.
    calc
      coveringSpaceHomToFiber b h e =
          hp'.fundamentalGroupoidMapFiberEquiv b
            (mapOfCoveringsToFiber
              hp.fundamentalGroupoidMap_isCovering hp'.fundamentalGroupoidMap_isCovering (mk b)
              (hp.toFundamentalGroupoidCoveringHom hp' h) ξ) := by
            simpa [coveringSpaceHomToFiber, ξ] using
              coveringSpaceHomToFiberFun_eq_groupoidFiberMap hp hp' b h e
      _ = hp'.fundamentalGroupoidMapFiberEquiv b (φcat ξ) := by
            rw [hkξ]
      _ = φ e := by
            change hp'.fundamentalGroupoidMapFiberEquiv b
                ((hp'.fundamentalGroupoidMapFiberEquiv b).symm
                  (φ (hp.fundamentalGroupoidMapFiberEquiv b ξ))) = φ e
            simp [ξ]

/-- The canonical equivalence realizing Theorem 3.7.9. -/
noncomputable def coveringSpaceHomToFiberEquiv
    [IsPathConnectedCoveringMap p] [IsPathConnectedCoveringMap p'] (b : B) :
    (Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p')) ≃
      ((p ⁻¹' {b}) →[FundamentalGroup B b] (p' ⁻¹' {b})) :=
  Equiv.ofBijective (coveringSpaceHomToFiber b) (coveringSpaceHomToFiber_bijective b)

@[simp] theorem coveringSpaceHomToFiberEquiv_apply
    [IsPathConnectedCoveringMap p] [IsPathConnectedCoveringMap p'] (b : B)
    (h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p')) :
    coveringSpaceHomToFiberEquiv b h = coveringSpaceHomToFiber b h :=
  rfl

end

end IsPathConnectedCoveringMap
