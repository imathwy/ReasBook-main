import Mathlib.CategoryTheory.CommSq
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Definition_7_1_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Definition_7_5_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Lemma_7_2_5

open CategoryTheory
open TopCat
open unitInterval
open scoped ContinuousMap

universe u

-- Semantic recall via `lean_leansearch`: `CategoryTheory.CommSq` is the canonical owner for a
-- single commutative square, `Arrow TopCat` is the ambient category of such squares, and
-- `Definition_7_5_2.lean` already provides the fixed-base Chapter 7 owners
-- `OverHomotopy`/`HomotopicOver`/`IsFiberHomotopyEquivalence`.

/-- A homotopy between two morphisms in `Arrow TopCat` consists of homotopies of the horizontal
maps on total and base spaces whose intermediate stages still commute with the vertical maps. -/
structure ArrowHomotopy {X Y : Arrow TopCat.{u}} (f₀ f₁ : X ⟶ Y) : Type _ where
  /-- The homotopy on source spaces. -/
  left : ContinuousMap.Homotopy f₀.left.hom f₁.left.hom
  /-- The homotopy on target spaces. -/
  right : ContinuousMap.Homotopy f₀.right.hom f₁.right.hom
  /-- Every intermediate stage is again a commutative square. -/
  comm (t : I) :
      CommSq X.hom (TopCat.ofHom (left.curry t)) (TopCat.ofHom (right.curry t)) Y.hom

/-- Two morphisms in `Arrow TopCat` are homotopic when there exists a homotopy through
commutative squares joining them. -/
abbrev HomotopicArrow {X Y : Arrow TopCat.{u}} (f₀ f₁ : X ⟶ Y) : Prop :=
  Nonempty (ArrowHomotopy f₀ f₁)

namespace ArrowHomotopy

/-- Helper for Proposition 7.5.5: the time-slices of a reversed arrow homotopy are the reversed
time-slices of the original homotopy. -/
private theorem symm_comm
    {X Y : Arrow TopCat.{u}} {f₀ f₁ : X ⟶ Y}
    (H : ArrowHomotopy f₀ f₁) (t : I) :
    CommSq X.hom (TopCat.ofHom (H.left.symm.curry t))
      (TopCat.ofHom (H.right.symm.curry t)) Y.hom := by
  -- Read the reversed stage from the original homotopy at the flipped time parameter.
  simpa [ContinuousMap.Homotopy.symm] using H.comm (σ t)

/-- Helper for Proposition 7.5.5: reversing an arrow homotopy still gives a homotopy through
commutative squares. -/
private def symm
    {X Y : Arrow TopCat.{u}} {f₀ f₁ : X ⟶ Y}
    (H : ArrowHomotopy f₀ f₁) :
    ArrowHomotopy f₁ f₀ :=
  { left := H.left.symm
    right := H.right.symm
    comm := symm_comm H }

/-- Helper for Proposition 7.5.5: the time-slices of a concatenated arrow homotopy come from the
appropriate half of the parameter interval. -/
private theorem trans_comm
    {X Y : Arrow TopCat.{u}} {f₀ f₁ f₂ : X ⟶ Y}
    (H₀ : ArrowHomotopy f₀ f₁) (H₁ : ArrowHomotopy f₁ f₂) (t : I) :
    CommSq X.hom (TopCat.ofHom ((H₀.left.trans H₁.left).curry t))
      (TopCat.ofHom ((H₀.right.trans H₁.right).curry t)) Y.hom := by
  refine ⟨?_⟩
  ext x
  change (H₀.right.trans H₁.right) (t, X.hom x) = Y.hom ((H₀.left.trans H₁.left) (t, x))
  rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split_ifs with ht
  · let t' : I :=
      ⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩
    have hcomm := congrArg TopCat.Hom.hom (H₀.comm t').w
    simpa [t'] using congrArg (fun m => m x) hcomm
  · let t' : I :=
      ⟨2 * t - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.2.2⟩⟩
    have hcomm := congrArg TopCat.Hom.hom (H₁.comm t').w
    simpa [t'] using congrArg (fun m => m x) hcomm

/-- Helper for Proposition 7.5.5: concatenating arrow homotopies preserves commutativity at each
time-slice. -/
private noncomputable def trans
    {X Y : Arrow TopCat.{u}} {f₀ f₁ f₂ : X ⟶ Y}
    (H₀ : ArrowHomotopy f₀ f₁) (H₁ : ArrowHomotopy f₁ f₂) :
    ArrowHomotopy f₀ f₂ :=
  { left := H₀.left.trans H₁.left
    right := H₀.right.trans H₁.right
    comm := trans_comm H₀ H₁ }

end ArrowHomotopy

/-- A morphism in `Arrow TopCat` is an arrow homotopy equivalence when it admits a two-sided
inverse up to homotopy through commutative squares. -/
class IsArrowHomotopyEquivalence {X Y : Arrow TopCat.{u}} (f : X ⟶ Y) : Prop where
  /-- An arrow homotopy equivalence admits a two-sided homotopy inverse through commutative
  squares. -/
  exists_inverse :
    ∃ g : Y ⟶ X, HomotopicArrow (g ≫ f) (𝟙 Y) ∧ HomotopicArrow (f ≫ g) (𝟙 X)

/-- An arrow homotopy equivalence is exactly a morphism in `Arrow TopCat` admitting a two-sided
inverse up to homotopy through commutative squares. -/
theorem isArrowHomotopyEquivalence_iff {X Y : Arrow TopCat.{u}} {f : X ⟶ Y} :
    IsArrowHomotopyEquivalence f ↔
      ∃ g : Y ⟶ X, HomotopicArrow (g ≫ f) (𝟙 Y) ∧ HomotopicArrow (f ≫ g) (𝟙 X) :=
  ⟨fun h ↦ h.exists_inverse, fun h ↦ ⟨h⟩⟩

namespace Over

/-- A morphism in `Over B` viewed as a commutative square with identity on the base. -/
def toArrowHom {B : TopCat.{u}} {X Y : Over B} (f : X ⟶ Y) : Arrow.mk X.hom ⟶ Arrow.mk Y.hom :=
  Arrow.homMk' f.left (𝟙 B) (by simpa using Over.w f)

@[simp] theorem toArrowHom_left {B : TopCat.{u}} {X Y : Over B} (f : X ⟶ Y) :
    (toArrowHom f).left = f.left :=
  rfl

@[simp] theorem toArrowHom_right {B : TopCat.{u}} {X Y : Over B} (f : X ⟶ Y) :
    (toArrowHom f).right = 𝟙 B :=
  rfl

@[simp] theorem toArrowHom_id {B : TopCat.{u}} (X : Over B) :
    toArrowHom (𝟙 X) = 𝟙 (Arrow.mk X.hom) := by
  ext <;> simp [toArrowHom]

@[simp] theorem toArrowHom_comp {B : TopCat.{u}} {X Y Z : Over B} (f : X ⟶ Y) (g : Y ⟶ Z) :
    toArrowHom (f ≫ g) = toArrowHom f ≫ toArrowHom g := by
  ext <;> simp [toArrowHom]

end Over

namespace OverHomotopy

/-- A homotopy over a fixed base gives an `ArrowHomotopy` whose base component is constant. -/
def toArrow {B : TopCat.{u}} {X Y : Over B} {f₀ f₁ : X ⟶ Y} (H : OverHomotopy f₀ f₁) :
    ArrowHomotopy (Over.toArrowHom f₀) (Over.toArrowHom f₁) where
  left := H.toHomotopy
  right := ContinuousMap.Homotopy.refl (Over.toArrowHom f₀).right.hom
  comm t := by
    refine ⟨?_⟩
    simpa using (OverHomotopy.w H t).symm

end OverHomotopy

namespace HomotopicOver

/-- A homotopy over a fixed base is, in particular, a homotopy of the corresponding commutative
squares in `Arrow TopCat`. -/
theorem toArrow {B : TopCat.{u}} {X Y : Over B} {f₀ f₁ : X ⟶ Y} (h : HomotopicOver f₀ f₁) :
    HomotopicArrow (Over.toArrowHom f₀) (Over.toArrowHom f₁) := by
  rcases h with ⟨H⟩
  exact ⟨OverHomotopy.toArrow H⟩

end HomotopicOver

/-- A fiber homotopy equivalence over a fixed base yields an arrow homotopy equivalence of the
associated commutative square with identity on the base. -/
instance toArrowHom_isArrowHomotopyEquivalence
    {B : TopCat.{u}} {X Y : Over B} (f : X ⟶ Y) [IsFiberHomotopyEquivalence f] :
    IsArrowHomotopyEquivalence (Over.toArrowHom f) where
  exists_inverse := by
    rcases isFiberHomotopyEquivalence_iff.mp ‹IsFiberHomotopyEquivalence f› with
      ⟨g, hgf, hfg⟩
    refine ⟨Over.toArrowHom g, ?_, ?_⟩
    · simpa using HomotopicOver.toArrow hgf
    · simpa using HomotopicOver.toArrow hfg

variable {D E A B : Type u}
variable [TopologicalSpace D] [TopologicalSpace E] [TopologicalSpace A] [TopologicalSpace B]
variable [CompactlyGeneratedWeakHausdorffSpace.{u, u} D]
variable [CompactlyGeneratedWeakHausdorffSpace.{u, u} E]
variable [CompactlyGeneratedWeakHausdorffSpace.{u, u} A]
variable [CompactlyGeneratedWeakHausdorffSpace.{u, u} B]

/-- Helper for Proposition 7.5.5: rewriting the categorical commutative square of `f` through the
chosen horizontal homotopy equivalences yields the continuous-map identity
`q.comp e_left.toFun = e_right.toFun.comp p`. -/
private theorem horizontalSquare_comp_eq
    {p : C(D, A)} {q : C(E, B)}
    (f : Arrow.mk (TopCat.ofHom p) ⟶ Arrow.mk (TopCat.ofHom q))
    (e_left : D ≃ₕ E) (he_left : e_left.toFun = f.left.hom)
    (e_right : A ≃ₕ B) (he_right : e_right.toFun = f.right.hom) :
    q.comp e_left.toFun = e_right.toFun.comp p := by
  -- Read the arrow morphism as the corresponding square of continuous maps.
  simpa [he_left, he_right, ContinuousMap.comp_assoc] using congrArg TopCat.Hom.hom f.w

/-- Helper for Proposition 7.5.5: every morphism in `Arrow TopCat` carries a continuous-map
commutativity identity between its horizontal and vertical maps. -/
private theorem arrowSquare_comp_eq
    {X Y A B : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace A] [TopologicalSpace B]
    {r : C(X, A)} {s : C(Y, B)}
    (u : Arrow.mk (TopCat.ofHom r) ⟶ Arrow.mk (TopCat.ofHom s)) :
    s.comp u.left.hom = u.right.hom.comp r := by
  -- Unpack the square equality from the categorical arrow morphism.
  simpa [ContinuousMap.comp_assoc] using congrArg TopCat.Hom.hom u.w

/-- Helper for Proposition 7.5.5: the chosen inverses on the horizontal maps induce some homotopy
from `p.comp e_left.symm.toFun` to `e_right.symm.toFun.comp q` on the base spaces. -/
private noncomputable def inverseBaseHomotopy
    {p : C(D, A)} {q : C(E, B)}
    (f : Arrow.mk (TopCat.ofHom p) ⟶ Arrow.mk (TopCat.ofHom q))
    (e_left : D ≃ₕ E) (he_left : e_left.toFun = f.left.hom)
    (e_right : A ≃ₕ B) (he_right : e_right.toFun = f.right.hom) :
    (p.comp e_left.symm.toFun).Homotopy (e_right.symm.toFun.comp q) := by
  let hSquare := horizontalSquare_comp_eq f e_left he_left e_right he_right
  have hCompOnInverse :
      q.comp (e_left.toFun.comp e_left.symm.toFun) =
        (e_right.toFun.comp p).comp e_left.symm.toFun := by
    -- Evaluate the normalized square after precomposing with the chosen inverse of `e_left`.
    ext x
    simpa [ContinuousMap.comp_assoc] using
      congrArg (fun m : C(D, B) => m (e_left.symm.toFun x)) hSquare
  let baseToPulled :
      (p.comp e_left.symm.toFun).Homotopy
        (e_right.symm.toFun.comp ((e_right.toFun.comp p).comp e_left.symm.toFun)) :=
    (ContinuousMap.Homotopy.comp e_right.left_inv.some.symm
      (ContinuousMap.Homotopy.refl (p.comp e_left.symm.toFun))).cast rfl
      (by
        ext x
        rfl)
  let pulledToTarget :
      (e_right.symm.toFun.comp ((e_right.toFun.comp p).comp e_left.symm.toFun)).Homotopy
        (e_right.symm.toFun.comp q) :=
    (ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl e_right.symm.toFun)
      ((ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl q) e_left.right_inv.some).cast
        hCompOnInverse
        rfl)).cast
      (by
        ext x
        rfl)
      rfl
  -- First insert the left inverse of `e_right`, then use the right inverse of `e_left`.
  exact baseToPulled.trans pulledToTarget

/-- Helper for Proposition 7.5.5: the chosen inverses on the horizontal maps induce some homotopy
from `p.comp e_left.symm.toFun` to `e_right.symm.toFun.comp q` on the base spaces. -/
private theorem inverseBaseHomotopy_exists
    {p : C(D, A)} {q : C(E, B)}
    (f : Arrow.mk (TopCat.ofHom p) ⟶ Arrow.mk (TopCat.ofHom q))
    (e_left : D ≃ₕ E) (he_left : e_left.toFun = f.left.hom)
    (e_right : A ≃ₕ B) (he_right : e_right.toFun = f.right.hom) :
    Nonempty ((p.comp e_left.symm.toFun).Homotopy (e_right.symm.toFun.comp q)) := by
  exact ⟨inverseBaseHomotopy f e_left he_left e_right he_right⟩

/-- Helper for Proposition 7.5.5: lifting `inverseBaseHomotopy` through `p` corrects the raw
inverse `e_left.symm` into an actual inverse square with base map `e_right.symm`. -/
private theorem existsArrowInverseOfIsFibration
    {p : C(D, A)} {q : C(E, B)}
    (hp : IsFibration.{u, u, u} p)
    (e_left : D ≃ₕ E) (e_right : A ≃ₕ B)
    (H : (p.comp e_left.symm.toFun).Homotopy (e_right.symm.toFun.comp q)) :
    ∃ g : Arrow.mk (TopCat.ofHom q) ⟶ Arrow.mk (TopCat.ofHom p),
      ∃ G : e_left.symm.toFun.Homotopy g.left.hom,
        p.comp G.toContinuousMap = H.toContinuousMap ∧
          g.right.hom = e_right.symm.toFun := by
  -- Lift the inverse-base homotopy through `p` starting from the raw inverse `e_left.symm`.
  obtain ⟨g₁, G, hG⟩ := by
    simpa using
      IsFibration.exists_homotopyLift.{u, u, u}
        (p := p) (hp := hp) (A := E) (H := H) (g₀ := e_left.symm.toFun) rfl
  have hg₁ :
      p.comp g₁ = e_right.symm.toFun.comp q := by
    -- Evaluate the lifted homotopy at time `1` to read off the corrected endpoint square.
    ext x
    have h := ContinuousMap.congr_fun hG (1, x)
    simpa [G.apply_one x] using h
  let g : Arrow.mk (TopCat.ofHom q) ⟶ Arrow.mk (TopCat.ofHom p) :=
    Arrow.homMk' (TopCat.ofHom g₁) (TopCat.ofHom e_right.symm.toFun) (by
      ext x
      simpa using congrArg (fun m : C(E, A) => m x) hg₁)
  -- Package the lifted endpoint as the exact inverse square and retain the correcting homotopy.
  exact ⟨g, G, hG, rfl⟩

/-- Helper for Proposition 7.5.5: a relative comparison between the projected left homotopy and
the pulled-back right homotopy rectifies to a genuine arrow homotopy. -/
private theorem arrowHomotopicOfProjectedHomotopyRel
    {X Y A B : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace A] [TopologicalSpace B]
    [CompactlyGeneratedWeakHausdorffSpace.{u, u} X]
    [CompactlyGeneratedWeakHausdorffSpace.{u, u} Y]
    [CompactlyGeneratedWeakHausdorffSpace.{u, u} A]
    [CompactlyGeneratedWeakHausdorffSpace.{u, u} B]
    {r : C(X, A)} {s : C(Y, B)}
    [IsFibration.{u, u, u} s]
    {u₀ u₁ : Arrow.mk (TopCat.ofHom r) ⟶ Arrow.mk (TopCat.ofHom s)}
    (F : u₀.left.hom.Homotopy u₁.left.hom)
    (R : u₀.right.hom.Homotopy u₁.right.hom)
    (hFrel :
      (s.comp F.toContinuousMap).HomotopicRel
        ((ContinuousMap.Homotopy.comp R (ContinuousMap.Homotopy.refl r)).toContinuousMap)
        (({0, 1} : Set I) ×ˢ (Set.univ : Set X))) :
    HomotopicArrow u₀ u₁ := by
  rcases hFrel with ⟨hFrel⟩
  letI : CompactlyGeneratedWeakHausdorffSpace.{u, u} (I × X) :=
    instCompactlyGeneratedWeakHausdorffSpaceProdUnitInterval X
  rcases @IsFibration.exists_homotopyLift Y B _ _ s (by infer_instance)
      (I × X) _ (instCompactlyGeneratedWeakHausdorffSpaceProdUnitInterval X)
      _ _ hFrel.toHomotopy F.toContinuousMap rfl with
    ⟨Graw, Kraw, hKraw⟩
  have hGraw :
      s.comp Graw =
        ((ContinuousMap.Homotopy.comp R (ContinuousMap.Homotopy.refl r)).toContinuousMap) := by
    -- Evaluating the lift at `s = 1` reads off the rectified homotopy over the pulled-back
    -- right branch.
    ext tx
    calc
      s (Graw tx) = hFrel.toHomotopy (1, tx) := by
        rw [← Kraw.apply_one tx]
        exact ContinuousMap.congr_fun hKraw (1, tx)
      _ = (R.comp (ContinuousMap.Homotopy.refl r)).toContinuousMap tx :=
        hFrel.toHomotopy.apply_one tx
  have hBaseZero : s.comp (Graw.curry 0) = u₀.right.hom.comp r := by
    -- The source endpoint of the rectified homotopy still commutes with the original right map.
    ext x
    calc
      s (Graw (0, x)) =
          ((ContinuousMap.Homotopy.comp R
              (ContinuousMap.Homotopy.refl r)).toContinuousMap) (0, x) := by
            simpa using ContinuousMap.congr_fun hGraw (0, x)
      _ = R (0, r x) := rfl
      _ = u₀.right.hom (r x) := by
            simpa using R.apply_zero (r x)
  have hBaseOne : s.comp (Graw.curry 1) = u₁.right.hom.comp r := by
    -- The target endpoint commutes with the target right map for the same reason.
    ext x
    calc
      s (Graw (1, x)) =
          ((ContinuousMap.Homotopy.comp R
              (ContinuousMap.Homotopy.refl r)).toContinuousMap) (1, x) := by
            simpa using ContinuousMap.congr_fun hGraw (1, x)
      _ = R (1, r x) := rfl
      _ = u₁.right.hom (r x) := by
            simpa using R.apply_one (r x)
  let v₀ : Arrow.mk (TopCat.ofHom r) ⟶ Arrow.mk (TopCat.ofHom s) :=
    Arrow.homMk' (TopCat.ofHom (Graw.curry 0)) u₀.right (by
      ext x
      simpa using congrArg (fun m : C(X, B) => m x) hBaseZero)
  let v₁ : Arrow.mk (TopCat.ofHom r) ⟶ Arrow.mk (TopCat.ofHom s) :=
    Arrow.homMk' (TopCat.ofHom (Graw.curry 1)) u₁.right (by
      ext x
      simpa using congrArg (fun m : C(X, B) => m x) hBaseOne)
  let sourceFace : ArrowHomotopy u₀ v₀ :=
    { left :=
        { toFun := fun sx ↦ Kraw (sx.1, (0, sx.2))
          continuous_toFun := by
            fun_prop
          map_zero_left := by
            intro x
            rw [Kraw.apply_zero (0, x)]
            simpa using F.apply_zero x
          map_one_left := by
            intro x
            rw [Kraw.apply_one (0, x)]
            rfl }
      right := ContinuousMap.Homotopy.refl u₀.right.hom
      comm := by
        intro t
        -- The `t = 0` face of the lifted square stays over the original right component.
        refine ⟨?_⟩
        ext x
        have hLift := ContinuousMap.congr_fun hKraw (t, (0, x))
        have hu₀ := ContinuousMap.congr_fun (arrowSquare_comp_eq u₀) x
        calc
          u₀.right.hom (r x) = s (u₀.left.hom x) := by
            simpa using hu₀.symm
          _ = s (F (0, x)) := by rw [F.apply_zero]
          _ = (s.comp F.toContinuousMap) (0, x) := rfl
          _ = hFrel.toHomotopy (t, (0, x)) := by
            exact (hFrel.eq_fst t ⟨by simp, by simp⟩).symm
          _ = s (Kraw (t, (0, x))) := by
            simpa using hLift.symm }
  let middleFace : ArrowHomotopy v₀ v₁ :=
    { left :=
        { toContinuousMap := Graw
          map_zero_left := by
            intro x
            rfl
          map_one_left := by
            intro x
            rfl }
      right := R
      comm := by
        intro t
        -- Every time-slice of the rectified lift lies over the corresponding right stage.
        refine ⟨?_⟩
        ext x
        symm
        simpa [ContinuousMap.Homotopy.comp] using ContinuousMap.congr_fun hGraw (t, x) }
  let targetFace : ArrowHomotopy u₁ v₁ :=
    { left :=
        { toFun := fun sx ↦ Kraw (sx.1, (1, sx.2))
          continuous_toFun := by
            fun_prop
          map_zero_left := by
            intro x
            rw [Kraw.apply_zero (1, x)]
            simpa using F.apply_one x
          map_one_left := by
            intro x
            rw [Kraw.apply_one (1, x)]
            rfl }
      right := ContinuousMap.Homotopy.refl u₁.right.hom
      comm := by
        intro t
        -- The `t = 1` face stays over the target right component by the other boundary face.
        refine ⟨?_⟩
        ext x
        have hLift := ContinuousMap.congr_fun hKraw (t, (1, x))
        have hu₁ := ContinuousMap.congr_fun (arrowSquare_comp_eq u₁) x
        calc
          u₁.right.hom (r x) = s (u₁.left.hom x) := by
            simpa using hu₁.symm
          _ = s (F (1, x)) := by rw [F.apply_one]
          _ = (s.comp F.toContinuousMap) (1, x) := rfl
          _ = hFrel.toHomotopy (t, (1, x)) := by
            exact (hFrel.eq_fst t ⟨by simp, by simp⟩).symm
          _ = s (Kraw (t, (1, x))) := by
            simpa using hLift.symm }
  -- Concatenate the three boundary faces of the lifted square to recover the requested arrow
  -- homotopy.
  exact ⟨sourceFace.trans (middleFace.trans targetFace.symm)⟩

/-- Helper for Proposition 7.5.5: any projected loop of the form `H.symm.trans H` contracts
relative to `({0, 1} : Set I) ×ˢ Set.univ`. -/
private theorem homotopySymmTransHomotopicRelRefl
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {r₀ r₁ : C(X, Y)}
    (H : r₀.Homotopy r₁) :
    (H.symm.trans H).toContinuousMap.HomotopicRel
      ((ContinuousMap.Homotopy.refl r₁).toContinuousMap)
      (({0, 1} : Set I) ×ˢ (Set.univ : Set X)) := by
  let loopParam : I × I → I := fun st ↦
    ⟨1 - Path.Homotopy.reflTransSymmAux (σ st.1, st.2), by
      have hmem := Path.Homotopy.reflTransSymmAux_mem_I (σ st.1, st.2)
      constructor
      · linarith [hmem.2]
      · linarith [hmem.1]⟩
  refine ⟨{
      toHomotopy :=
        { toFun := fun sx ↦ H (loopParam (sx.1, sx.2.1), sx.2.2)
          continuous_toFun := by
            fun_prop
          map_zero_left := by
            intro tx
            rcases tx with ⟨t, x⟩
            change H (loopParam (0, t), x) = (H.symm.trans H) (t, x)
            rw [ContinuousMap.Homotopy.trans_apply]
            split_ifs with ht
            · have hParam :
                loopParam (0, t) =
                  σ ⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩ := by
                apply Subtype.ext
                have ht' : (t : ℝ) ≤ 1 / 2 := by
                  simpa using ht
                change (↑(loopParam (0, t)) : ℝ) = 1 - 2 * (t : ℝ)
                have hAux :
                    Path.Homotopy.reflTransSymmAux (σ 0, t) =
                      (if (t : ℝ) ≤ 1 / 2 then 2 * (t : ℝ) else 2 - 2 * (t : ℝ)) := by
                  simp [Path.Homotopy.reflTransSymmAux]
                rw [show (↑(loopParam (0, t)) : ℝ) = 1 - Path.Homotopy.reflTransSymmAux (σ 0, t) by
                  simp [loopParam]]
                rw [hAux, if_pos ht']
              exact congrArg (fun u : I ↦ H (u, x)) hParam
            · have hParam :
                loopParam (0, t) = ⟨2 * t - 1,
                  unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.2.2⟩⟩ := by
                apply Subtype.ext
                have ht' : ¬ (t : ℝ) ≤ 1 / 2 := by
                  simpa using ht
                change (↑(loopParam (0, t)) : ℝ) = 2 * (t : ℝ) - 1
                have hAux :
                    Path.Homotopy.reflTransSymmAux (σ 0, t) =
                      (if (t : ℝ) ≤ 1 / 2 then 2 * (t : ℝ) else 2 - 2 * (t : ℝ)) := by
                  simp [Path.Homotopy.reflTransSymmAux]
                rw [show (↑(loopParam (0, t)) : ℝ) = 1 - Path.Homotopy.reflTransSymmAux (σ 0, t) by
                  simp [loopParam]]
                rw [hAux, if_neg ht']
                ring
              exact congrArg (fun u : I ↦ H (u, x)) hParam
          map_one_left := by
            intro tx
            rcases tx with ⟨t, x⟩
            simp [loopParam, Path.Homotopy.reflTransSymmAux] }
      prop' := ?_ }⟩
  intro s tx htx
  rcases tx with ⟨t, x⟩
  rcases Set.mem_insert_iff.mp htx.1 with ht | ht
  · subst ht
    norm_num [loopParam, Path.Homotopy.reflTransSymmAux]
  · have ht' : t = 1 := Set.mem_singleton_iff.mp ht
    subst ht'
    norm_num [loopParam, Path.Homotopy.reflTransSymmAux]

/-- Helper for Proposition 7.5.5: once the corrected inverse square is chosen, the right
composite `g ≫ f` should contract to the identity through commutative squares. -/
private theorem rightCompositeHomotopicArrowRefl
    {p : C(D, A)} {q : C(E, B)}
    [IsFibration.{u, u, u} p] [IsFibration.{u, u, u} q]
    (f : Arrow.mk (TopCat.ofHom p) ⟶ Arrow.mk (TopCat.ofHom q))
    (e_left : D ≃ₕ E) (he_left : e_left.toFun = f.left.hom)
    (e_right : A ≃ₕ B) (he_right : e_right.toFun = f.right.hom)
    {g : Arrow.mk (TopCat.ofHom q) ⟶ Arrow.mk (TopCat.ofHom p)}
    (H : (p.comp e_left.symm.toFun).Homotopy (e_right.symm.toFun.comp q))
    (G : e_left.symm.toFun.Homotopy g.left.hom)
    (hG : p.comp G.toContinuousMap = H.toContinuousMap)
    (hg_right : g.right.hom = e_right.symm.toFun) :
    HomotopicArrow (g ≫ f) (𝟙 (Arrow.mk (TopCat.ofHom q))) := by
  let FgfRaw :
      (e_left.toFun.comp e_left.symm.toFun).Homotopy
        (e_left.toFun.comp g.left.hom) :=
    ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl e_left.toFun) G
  let Fgf : (e_left.toFun.comp e_left.symm.toFun).Homotopy (g ≫ f).left.hom :=
    FgfRaw.cast rfl (by
      ext y
      rw [he_left]
      rfl)
  let F : (g ≫ f).left.hom.Homotopy (ContinuousMap.id E) :=
    Fgf.symm.trans e_left.right_inv.some
  let Rraw : (e_right.toFun.comp e_right.symm.toFun).Homotopy (ContinuousMap.id B) :=
    e_right.right_inv.some
  let R : (g ≫ f).right.hom.Homotopy (ContinuousMap.id B) :=
    Rraw.cast (by
      ext x
      rw [he_right, ← hg_right]
      rfl) rfl
  have hProjectedRel :
      (q.comp F.toContinuousMap).HomotopicRel
        ((ContinuousMap.Homotopy.comp R (ContinuousMap.Homotopy.refl q)).toContinuousMap)
        (({0, 1} : Set I) ×ˢ (Set.univ : Set E)) := by
    -- Route correction: the remaining frontier is now exactly the projected-relative comparison
    -- between the corrected left branch and the pulled-back right branch over `q`.
    sorry
  -- Once the projected comparison is available, the Arrow-level rectifier produces the homotopy.
  exact arrowHomotopicOfProjectedHomotopyRel F R hProjectedRel

/-- Helper for Proposition 7.5.5: after the right-composite contraction is in place, the left
composite `f ≫ g` should contract to the identity by the symmetric projected comparison over `p`.
-/
private theorem leftCompositeHomotopicArrowRefl
    {p : C(D, A)} {q : C(E, B)}
    [IsFibration.{u, u, u} p] [IsFibration.{u, u, u} q]
    (f : Arrow.mk (TopCat.ofHom p) ⟶ Arrow.mk (TopCat.ofHom q))
    (e_left : D ≃ₕ E) (he_left : e_left.toFun = f.left.hom)
    (e_right : A ≃ₕ B) (he_right : e_right.toFun = f.right.hom)
    {g : Arrow.mk (TopCat.ofHom q) ⟶ Arrow.mk (TopCat.ofHom p)}
    (H : (p.comp e_left.symm.toFun).Homotopy (e_right.symm.toFun.comp q))
    (G : e_left.symm.toFun.Homotopy g.left.hom)
    (hG : p.comp G.toContinuousMap = H.toContinuousMap)
    (hg_right : g.right.hom = e_right.symm.toFun) :
    HomotopicArrow (f ≫ g) (𝟙 (Arrow.mk (TopCat.ofHom p))) := by
  let FfgRaw :
      (e_left.symm.toFun.comp e_left.toFun).Homotopy
        (g.left.hom.comp e_left.toFun) :=
    ContinuousMap.Homotopy.comp G (ContinuousMap.Homotopy.refl e_left.toFun)
  let Ffg : (e_left.symm.toFun.comp e_left.toFun).Homotopy (f ≫ g).left.hom :=
    FfgRaw.cast rfl (by
      ext x
      rw [he_left]
      rfl)
  let F : (f ≫ g).left.hom.Homotopy (ContinuousMap.id D) :=
    Ffg.symm.trans e_left.left_inv.some
  let Rraw : (e_right.symm.toFun.comp e_right.toFun).Homotopy (ContinuousMap.id A) :=
    e_right.left_inv.some
  let R : (f ≫ g).right.hom.Homotopy (ContinuousMap.id A) :=
    Rraw.cast (by
      ext x
      rw [← hg_right, he_right]
      rfl) rfl
  have hProjectedRel :
      (p.comp F.toContinuousMap).HomotopicRel
        ((ContinuousMap.Homotopy.comp R (ContinuousMap.Homotopy.refl p)).toContinuousMap)
        (({0, 1} : Set I) ×ˢ (Set.univ : Set D)) := by
    -- Route correction: after extracting `K`, the only remaining blocker is the corrected
    -- left-branch comparison against the pulled-back right homotopy over `p`.
    sorry
  -- Feed the coherent left homotopy into the same Arrow-level rectifier used on the right side.
  exact arrowHomotopicOfProjectedHomotopyRel F R hProjectedRel

/-- Proposition 7.5.5. In a commutative square of fibrations `D ⟶ E` over `A ⟶ B`, if the
horizontal maps are ordinary homotopy equivalences, then the square is an arrow homotopy
equivalence. -/
theorem isArrowHomotopyEquivalence_of_horizontalHomotopyEquiv
    {p : C(D, A)} {q : C(E, B)}
    [IsFibration.{u, u, u} p] [IsFibration.{u, u, u} q]
    (f : Arrow.mk (TopCat.ofHom p) ⟶ Arrow.mk (TopCat.ofHom q))
    (e_left : D ≃ₕ E) (he_left : e_left.toFun = f.left.hom)
    (e_right : A ≃ₕ B) (he_right : e_right.toFun = f.right.hom) :
    IsArrowHomotopyEquivalence f := by
  classical
  -- Build the corrected inverse square by lifting the inverse base homotopy through `p`.
  let H : (p.comp e_left.symm.toFun).Homotopy (e_right.symm.toFun.comp q) :=
    Classical.choice (inverseBaseHomotopy_exists f e_left he_left e_right he_right)
  rcases
      existsArrowInverseOfIsFibration (p := p) (q := q) (hp := by
        infer_instance) e_left e_right H with
    ⟨g, G, hG, hg_right⟩
  refine (isArrowHomotopyEquivalence_iff).2 ?_
  refine ⟨g, ?_, ?_⟩
  · -- The right composite is the first place where the remaining arrow-homotopy bridge is used.
    exact rightCompositeHomotopicArrowRefl f e_left he_left e_right he_right H G hG hg_right
  · -- The left composite is handled by the symmetric projected-comparison argument.
    exact leftCompositeHomotopicArrowRefl f e_left he_left e_right he_right H G hG hg_right

/-- Existence-only restatement of Proposition 7.5.5 for callers that only know that the
horizontal maps of `f` are ordinary homotopy equivalences. -/
theorem isArrowHomotopyEquivalence_of_exists_horizontalHomotopyEquiv
    {p : C(D, A)} {q : C(E, B)}
    [IsFibration.{u, u, u} p] [IsFibration.{u, u, u} q]
    (f : Arrow.mk (TopCat.ofHom p) ⟶ Arrow.mk (TopCat.ofHom q))
    (h_left : ∃ e : D ≃ₕ E, e.toFun = f.left.hom)
    (h_right : ∃ e : A ≃ₕ B, e.toFun = f.right.hom) :
    IsArrowHomotopyEquivalence f := by
  rcases h_left with ⟨e_left, he_left⟩
  rcases h_right with ⟨e_right, he_right⟩
  exact isArrowHomotopyEquivalence_of_horizontalHomotopyEquiv
    f e_left he_left e_right he_right
