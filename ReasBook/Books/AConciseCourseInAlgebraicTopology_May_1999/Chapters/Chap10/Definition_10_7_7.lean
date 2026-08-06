import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Definition_10_7_6

open CategoryTheory CategoryTheory.Limits
open scoped ContinuousMap unitInterval

noncomputable section

universe u

variable {A B C : Type u} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]

namespace ContinuousMap

-- Analogues: `mappingCylinderProjection` in Construction 6.3.1 and the universal pushout lemmas
-- `pushout.inl_desc` / `pushout.inr_desc`; the owner-level inclusions of the double mapping
-- cylinder itself live in Definition 10.7.6.

/-- The canonical map `A ⊕ B ⟶ A ∪_C B` induced by the two legs of the pushout of
`i : C(C, A)` and `j : C(C, B)`. -/
def doubleMappingCylinderPushoutCoprodMap (i : C(C, A)) (j : C(C, B)) :
    C(A ⊕ B, (CategoryTheory.Limits.pushout (TopCat.ofHom i) (TopCat.ofHom j) : TopCat)) :=
  { toFun :=
      Sum.elim
        (pushout.inl (TopCat.ofHom i) (TopCat.ofHom j)).hom
        (pushout.inr (TopCat.ofHom i) (TopCat.ofHom j)).hom
    continuous_toFun :=
      Continuous.sumElim
        (pushout.inl (TopCat.ofHom i) (TopCat.ofHom j)).hom.continuous
        (pushout.inr (TopCat.ofHom i) (TopCat.ofHom j)).hom.continuous }

@[simp] theorem doubleMappingCylinderPushoutCoprodMap_inl
    (i : C(C, A)) (j : C(C, B)) (a : A) :
    doubleMappingCylinderPushoutCoprodMap i j (Sum.inl a) =
      (pushout.inl (TopCat.ofHom i) (TopCat.ofHom j)).hom a :=
  rfl

@[simp] theorem doubleMappingCylinderPushoutCoprodMap_inr
    (i : C(C, A)) (j : C(C, B)) (b : B) :
    doubleMappingCylinderPushoutCoprodMap i j (Sum.inr b) =
      (pushout.inr (TopCat.ofHom i) (TopCat.ofHom j)).hom b :=
  rfl

/-- The map `C × I ⟶ A ∪_C B` that forgets the interval coordinate and remembers only the image of
`c : C` in the pushout of `i : C(C, A)` and `j : C(C, B)`. -/
def doubleMappingCylinderPushoutCylinderMap (i : C(C, A)) (j : C(C, B)) :
    C(C × I, (CategoryTheory.Limits.pushout (TopCat.ofHom i) (TopCat.ofHom j) : TopCat)) :=
  ((pushout.inl (TopCat.ofHom i) (TopCat.ofHom j)).hom.comp i).comp ContinuousMap.fst

@[simp] theorem doubleMappingCylinderPushoutCylinderMap_apply
    (i : C(C, A)) (j : C(C, B)) (c : C) (t : I) :
    doubleMappingCylinderPushoutCylinderMap i j (c, t) =
      (pushout.inl (TopCat.ofHom i) (TopCat.ofHom j)).hom (i c) :=
  rfl

/-- The cylinder-side map restricts on `C × {0}` to the left pushout leg composed with `i`. -/
theorem doubleMappingCylinderPushoutCylinderMap_comp_timeZeroInclusion
    (i : C(C, A)) (j : C(C, B)) :
    (doubleMappingCylinderPushoutCylinderMap i j).comp (mappingCylinderTimeZeroInclusion C) =
      (pushout.inl (TopCat.ofHom i) (TopCat.ofHom j)).hom.comp i := by
  ext c
  rfl

/-- The cylinder-side map restricts on `C × {1}` to the right pushout leg composed with `j`. -/
theorem doubleMappingCylinderPushoutCylinderMap_comp_timeOneInclusion
    (i : C(C, A)) (j : C(C, B)) :
    (doubleMappingCylinderPushoutCylinderMap i j).comp (doubleMappingCylinderTimeOneInclusion C) =
      (pushout.inr (TopCat.ofHom i) (TopCat.ofHom j)).hom.comp j := by
  apply ContinuousMap.ext
  intro c
  simpa [ContinuousMap.comp_apply] using
    congrArg
      (fun f : C(C, (CategoryTheory.Limits.pushout (TopCat.ofHom i) (TopCat.ofHom j) : TopCat)) ↦
        f c)
      (congrArg TopCat.Hom.hom
        (show TopCat.ofHom i ≫ pushout.inl (TopCat.ofHom i) (TopCat.ofHom j) =
            TopCat.ofHom j ≫ pushout.inr (TopCat.ofHom i) (TopCat.ofHom j) from
          pushout.condition))

/-- The maps from `A ⊕ B` and `C × I` to `A ∪_C B` agree on the attaching locus `C ⊕ C`, so they
descend to a map from the double mapping cylinder. -/
theorem doubleMappingCylinderQuotientMap_condition (i : C(C, A)) (j : C(C, B)) :
    TopCat.ofHom (doubleMappingCylinderAttachMap i j) ≫
        TopCat.ofHom (doubleMappingCylinderPushoutCoprodMap i j) =
      TopCat.ofHom (doubleMappingCylinderBoundaryMap C) ≫
        TopCat.ofHom (doubleMappingCylinderPushoutCylinderMap i j) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  cases x with
  | inl c =>
      rfl
  | inr c =>
      simpa [ContinuousMap.comp_apply] using
        congrArg
          (fun f :
              C(C, (CategoryTheory.Limits.pushout (TopCat.ofHom i) (TopCat.ofHom j) : TopCat)) ↦
            f c)
          (congrArg TopCat.Hom.hom
            (show TopCat.ofHom i ≫ pushout.inl (TopCat.ofHom i) (TopCat.ofHom j) =
                TopCat.ofHom j ≫ pushout.inr (TopCat.ofHom i) (TopCat.ofHom j) from
              pushout.condition)).symm

/-- The canonical maps from `A ⊕ B` and `C × I` to `A ∪_C B` form a commuting square over the
attaching and boundary maps of the double mapping cylinder. -/
theorem doubleMappingCylinderPushout_commSq (i : C(C, A)) (j : C(C, B)) :
    CommSq (TopCat.ofHom (doubleMappingCylinderAttachMap i j))
      (TopCat.ofHom (doubleMappingCylinderBoundaryMap C))
      (TopCat.ofHom (doubleMappingCylinderPushoutCoprodMap i j))
      (TopCat.ofHom (doubleMappingCylinderPushoutCylinderMap i j)) := by
  exact ⟨doubleMappingCylinderQuotientMap_condition i j⟩

/-- Definition 10.7.7. The quotient map `q : M(i, j) ⟶ A ∪_C B` collapses the cylinder coordinate
and sends `(c, t)` to the image of `c` in the pushout of `i : C(C, A)` and `j : C(C, B)`. -/
def doubleMappingCylinderQuotientMap (i : C(C, A)) (j : C(C, B)) :
    M(i, j) ⟶
      (CategoryTheory.Limits.pushout (TopCat.ofHom i) (TopCat.ofHom j) : TopCat) :=
  pushout.desc
    (TopCat.ofHom (doubleMappingCylinderPushoutCoprodMap i j))
    (TopCat.ofHom (doubleMappingCylinderPushoutCylinderMap i j))
    (doubleMappingCylinderQuotientMap_condition i j)

/-- The quotient map restricts on the `A ⊕ B` side to the canonical map into the pushout
`A ∪_C B`. -/
theorem doubleMappingCylinderCoprodInclusion_comp_quotientMap (i : C(C, A)) (j : C(C, B)) :
    TopCat.ofHom (doubleMappingCylinderCoprodInclusion i j) ≫
        doubleMappingCylinderQuotientMap i j =
      TopCat.ofHom (doubleMappingCylinderPushoutCoprodMap i j) := by
  simpa [doubleMappingCylinderCoprodInclusion, doubleMappingCylinderQuotientMap] using
    (pushout.inl_desc
      (TopCat.ofHom (doubleMappingCylinderPushoutCoprodMap i j))
      (TopCat.ofHom (doubleMappingCylinderPushoutCylinderMap i j))
      (doubleMappingCylinderQuotientMap_condition i j))

/-- The quotient map restricts on `C × I` to the map that forgets the interval coordinate and
retains only the image of `c : C` in `A ∪_C B`. -/
theorem doubleMappingCylinderCylinderInclusion_comp_quotientMap (i : C(C, A)) (j : C(C, B)) :
    TopCat.ofHom (doubleMappingCylinderCylinderInclusion i j) ≫
        doubleMappingCylinderQuotientMap i j =
      TopCat.ofHom (doubleMappingCylinderPushoutCylinderMap i j) := by
  simpa [doubleMappingCylinderCylinderInclusion, doubleMappingCylinderQuotientMap] using
    (pushout.inr_desc
      (TopCat.ofHom (doubleMappingCylinderPushoutCoprodMap i j))
      (TopCat.ofHom (doubleMappingCylinderPushoutCylinderMap i j))
      (doubleMappingCylinderQuotientMap_condition i j))

end ContinuousMap
