import Mathlib.CategoryTheory.CommSq
import Mathlib.Topology.Category.TopCat.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Definition_7_6_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.HomotopyClasses

open CategoryTheory
open TopCat
open scoped ContinuousMap unitInterval

noncomputable section

universe u

variable {E F A B : Type u}
variable [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace A] [TopologicalSpace B]
variable [CompactlyGeneratedWeakHausdorffSpace.{u, u} E]
variable [CompactlyGeneratedWeakHausdorffSpace.{u, u} F]
variable [CompactlyGeneratedWeakHausdorffSpace.{u, u} A]
variable [CompactlyGeneratedWeakHausdorffSpace.{u, u} B]

-- Semantic recall via `lean_leansearch`: `CategoryTheory.CommSq` is the canonical owner for a
-- single commutative square of maps, and `Path.Homotopic.Quotient.map` is the canonical map on
-- path classes induced by a continuous map.

/-- A commutative square `E ⟶ F` over `A ⟶ B` sends the fiber of `p` over `a` into the fiber of
`q` over `g a`. -/
theorem mapOfFibrations_obj_mem_fiber {p : C(E, A)} {q : C(F, B)} {f : C(E, F)} {g : C(A, B)}
    {a : A} (sq : CommSq (TopCat.ofHom f) (TopCat.ofHom p) (TopCat.ofHom q) (TopCat.ofHom g))
    (x : fiber p a) : q (f x.1) = g a := by
  have hx : p x.1 = a := (mem_fiber_iff p a x.1).1 x.2
  calc
    q (f x.1) = g (p x.1) := by
      simpa [ContinuousMap.comp_apply] using
        congrArg (fun h : TopCat.of E ⟶ TopCat.of B ↦ h.hom x.1) sq.w
    _ = g a := by
      rw [hx]

/-- Restriction of the total-space map in a commutative square of fibrations to the fiber over
`a`. -/
def mapOfFibrationsToFiber {p : C(E, A)} {q : C(F, B)} {f : C(E, F)} {g : C(A, B)}
    (sq : CommSq (TopCat.ofHom f) (TopCat.ofHom p) (TopCat.ofHom q) (TopCat.ofHom g)) (a : A) :
    C(fiber p a, fiber q (g a)) where
  toFun x := ⟨f x.1, mapOfFibrations_obj_mem_fiber sq x⟩
  continuous_toFun :=
    (f.continuous.comp continuous_subtype_val).subtype_mk fun x ↦
      mapOfFibrations_obj_mem_fiber sq x

/-- Helper for Theorem 7.6.9: the induced map on fibers really is the restriction of `f` along the
fiber inclusions. -/
theorem comp_mapOfFibrationsToFiber
    {p : C(E, A)} {q : C(F, B)} {f : C(E, F)} {g : C(A, B)}
    (sq : CommSq (TopCat.ofHom f) (TopCat.ofHom p) (TopCat.ofHom q) (TopCat.ofHom g)) (a : A) :
    (fiberInclusion q (g a)).comp (mapOfFibrationsToFiber sq a) = f.comp (fiberInclusion p a) := by
  -- Both sides are the same pointwise map `x ↦ f x.1`; only the fiber packaging differs.
  ext x
  rfl

/-- Helper for Theorem 7.6.9: two lifts with the same source map and the same projected base
homotopy have homotopic endpoint maps in the target fiber. -/
theorem endpointHomotopic_of_sameProjectedLift
    {q : C(F, B)} [IsFibration.{u, u, u} q] {X : Type u} [TopologicalSpace X]
    [CompactlyGeneratedWeakHausdorffSpace.{u, u} X] {b b' : B}
    {s : C(X, fiber q b)} {f₀ f₁ : C(X, fiber q b')}
    {G₀ : ((fiberInclusion q b).comp s).Homotopy ((fiberInclusion q b').comp f₀)}
    {G₁ : ((fiberInclusion q b).comp s).Homotopy ((fiberInclusion q b').comp f₁)}
    {H : (ContinuousMap.const X b).Homotopy (ContinuousMap.const X b')}
    (hG₀ : q.comp G₀.toContinuousMap = H.toContinuousMap)
    (hG₁ : q.comp G₁.toContinuousMap = H.toContinuousMap) :
    ContinuousMap.Homotopic f₀ f₁ := by
  have hProjected :
      q.comp (G₀.symm.trans G₁).toContinuousMap = (H.symm.trans H).toContinuousMap := by
    -- Projecting the comparison homotopy gives the standard self-canceling loop on the base.
    ext tx
    change q ((G₀.symm.trans G₁) tx) = (H.symm.trans H) tx
    rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
    split_ifs with ht
    · simpa [ContinuousMap.Homotopy.symm] using
        ContinuousMap.congr_fun hG₀
          (σ ⟨2 * tx.1, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨tx.1.2.1, ht⟩⟩, tx.2)
    · simpa using
        ContinuousMap.congr_fun hG₁
          (⟨2 * tx.1 - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, tx.1.2.2⟩⟩,
            tx.2)
  have hProjectedRel :
      (q.comp (G₀.symm.trans G₁).toContinuousMap).HomotopicRel
        ((ContinuousMap.Homotopy.refl (ContinuousMap.const X b')).toContinuousMap)
        (({0, 1} : Set I) ×ˢ (Set.univ : Set X)) := by
    -- Rewrite to the canonical loop and contract it relative to the boundary.
    rw [hProjected]
    exact homotopySymmTransHomotopicRelRefl H
  have hFib : IsFibration.{u, u, u} q := by
    infer_instance
  -- The public rectification lemma now converts the projected contraction into endpoint homotopy.
  exact fiberEndpointHomotopic_of_projectedHomotopyRelConst
    (p := q) (F := G₀.symm.trans G₁) hProjectedRel

/-- Helper for Theorem 7.6.9: the naturality square commutes for a represented path
`β : Path a a'`. -/
theorem fiberTranslationNaturalOfPath
    {p : C(E, A)} {q : C(F, B)} [IsFibration.{u, u, u} p] [IsFibration.{u, u, u} q]
    {f : C(E, F)} {g : C(A, B)}
    (sq : CommSq (TopCat.ofHom f) (TopCat.ofHom p) (TopCat.ofHom q) (TopCat.ofHom g))
    {a a' : A} (β : Path a a')
    {τp : fiberMapHomotopyClasses p a a'}
    {τq : fiberMapHomotopyClasses q (g a) (g a')}
    (hτp : IsFiberTranslation p (Path.Homotopic.Quotient.mk β) τp)
    (hτq : IsFiberTranslation q (Path.Homotopic.Quotient.mk (β.map g.continuous)) τq) :
    continuousMapHomotopyClassesPostcompose (mapOfFibrationsToFiber sq a')
        τp =
      continuousMapHomotopyClassesPrecompose (mapOfFibrationsToFiber sq a)
        τq := by
  rw [isFiberTranslation_mk_iff] at hτp hτq
  rcases hτp with ⟨gp, Gp, hGp, rfl⟩
  rcases hτq with ⟨gq, Gq, hGq, rfl⟩
  let leftLiftRaw :
      (f.comp (fiberInclusion p a)).Homotopy
        (f.comp ((fiberInclusion p a').comp gp)) :=
    ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl f) Gp
  let leftLift :
      ((fiberInclusion q (g a)).comp (mapOfFibrationsToFiber sq a)).Homotopy
        ((fiberInclusion q (g a')).comp ((mapOfFibrationsToFiber sq a').comp gp)) :=
    leftLiftRaw.cast (comp_mapOfFibrationsToFiber sq a).symm (by
      ext x
      rfl)
  let rightLift :
      ((fiberInclusion q (g a)).comp (mapOfFibrationsToFiber sq a)).Homotopy
        ((fiberInclusion q (g a')).comp (gq.comp (mapOfFibrationsToFiber sq a))) :=
    (Gq.compContinuousMap (mapOfFibrationsToFiber sq a)).cast rfl (by
      ext x
      rfl)
  let H := (β.map g.continuous).toHomotopyConst (Y := fiber p a)
  have hLeftLift : q.comp leftLift.toContinuousMap = H.toContinuousMap := by
    -- Postcomposing the original lift by `f` transports the base homotopy along `g`.
    ext tx
    rcases tx with ⟨t, x⟩
    have hPoint := ContinuousMap.congr_fun hGp (t, x)
    calc
      q (leftLift (t, x)) = q (f (Gp (t, x))) := by
        rfl
      _ = g (p (Gp (t, x))) := by
        simpa [ContinuousMap.comp_apply] using
          congrArg (fun h : TopCat.of E ⟶ TopCat.of B ↦ h.hom (Gp (t, x))) sq.w
      _ = g (((β.toHomotopyConst (Y := fiber p a)).toContinuousMap) (t, x)) := by
        exact congrArg g hPoint
      _ = H (t, x) := by
        rfl
  have hRightLift : q.comp rightLift.toContinuousMap = H.toContinuousMap := by
    -- Precomposing the target lift by the induced map on fibers leaves the same base path family.
    ext tx
    rcases tx with ⟨t, x⟩
    have hPoint := ContinuousMap.congr_fun hGq (t, mapOfFibrationsToFiber sq a x)
    simpa [rightLift, H, Path.toHomotopyConst] using hPoint
  have hEndpoints :
      ContinuousMap.Homotopic
        ((mapOfFibrationsToFiber sq a').comp gp)
        (gq.comp (mapOfFibrationsToFiber sq a)) := by
    -- Compare the two endpoint lifts over the common projected homotopy
    -- `(β.map g).toHomotopyConst`.
    exact endpointHomotopic_of_sameProjectedLift
      (q := q) (s := mapOfFibrationsToFiber sq a) (G₀ := leftLift) (G₁ := rightLift)
      hLeftLift hRightLift
  -- Both quotient maps are represented by the endpoint maps compared above.
  simpa [continuousMapHomotopyClassesPostcompose, continuousMapHomotopyClassesPrecompose] using
    Quotient.sound hEndpoints

/-- Theorem 7.6.9: for a commutative square of fibrations over `g : A → B`, translation of fibers
is natural, so whenever `τₚ` and `τ_q` represent translations along `α` and `α.map g`, the square
comparing them commutes in the homotopy category. -/
theorem fiberTranslation_natural {p : C(E, A)} {q : C(F, B)} [IsFibration p] [IsFibration q]
    {f : C(E, F)} {g : C(A, B)}
    (sq : CommSq (TopCat.ofHom f) (TopCat.ofHom p) (TopCat.ofHom q) (TopCat.ofHom g))
    {a a' : A} (α : Path.Homotopic.Quotient a a')
    {τp : fiberMapHomotopyClasses p a a'}
    {τq : fiberMapHomotopyClasses q (g a) (g a')}
    (hτp : IsFiberTranslation p α τp)
    (hτq : IsFiberTranslation q (α.map g) τq) :
    continuousMapHomotopyClassesPostcompose (mapOfFibrationsToFiber sq a')
        τp =
      continuousMapHomotopyClassesPrecompose (mapOfFibrationsToFiber sq a)
        τq := by
  -- Reduce the path-class statement to the represented-path case handled above.
  refine Quotient.inductionOn α
    (motive := fun α =>
      ∀ {τp : fiberMapHomotopyClasses p a a'}
        {τq : fiberMapHomotopyClasses q (g a) (g a')},
        IsFiberTranslation p α τp →
        IsFiberTranslation q (Path.Homotopic.Quotient.map α g) τq →
        continuousMapHomotopyClassesPostcompose (mapOfFibrationsToFiber sq a') τp =
          continuousMapHomotopyClassesPrecompose (mapOfFibrationsToFiber sq a) τq) ?_
      hτp hτq
  intro β τp τq hτp hτq
  have hτq' : IsFiberTranslation q (Path.Homotopic.Quotient.mk (β.map g.continuous)) τq := by
    simpa [Path.Homotopic.Quotient.mk_map] using hτq
  exact fiberTranslationNaturalOfPath (sq := sq) (β := β) (τp := τp) (τq := τq) hτp hτq'
