import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Definition_7_6_3

open Path.Homotopic.Quotient
open scoped unitInterval

universe u v

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
variable [CompactlyGeneratedWeakHausdorffSpace.{u, u} E]
variable [CompactlyGeneratedWeakHausdorffSpace.{v, v} B]

-- Semantic recall via `lean_leansearch`: the path-class quotient API is organized around
-- `Path.Homotopic.Quotient.mk` and `Path.Homotopic.Quotient.eq`, so lift-independence is
-- stated by comparing an arbitrary lifted endpoint map with any class `τ` satisfying
-- `IsFiberTranslation p (mk β) τ`.

/-- Lemma 7.6.4: the translation `τ[β]` depends only on the path class `β`, so any two
fiber translations along the same path class are equal. -/
theorem fiberTranslation_eq_of_isFiberTranslation (p : C(E, B)) [IsFibration p] {b b' : B}
    {β : Path.Homotopic.Quotient b b'} {τ₀ τ₁ : fiberMapHomotopyClasses p b b'}
    (hτ₀ : IsFiberTranslation p β τ₀) (hτ₁ : IsFiberTranslation p β τ₁) :
    τ₀ = τ₁ := by
  -- Reduce the quotient statement to a represented path and compare two concrete lifted witnesses.
  revert hτ₀ hτ₁
  refine Quotient.inductionOn β ?_
  intro γ hτ₀ hτ₁
  have hτ₀' : IsFiberTranslationOfPath p γ τ₀ := by
    simpa [isFiberTranslation_mk_iff] using hτ₀
  have hτ₁' : IsFiberTranslationOfPath p γ τ₁ := by
    simpa [isFiberTranslation_mk_iff] using hτ₁
  rcases hτ₀' with ⟨g₀, G₀, hG₀, hg₀τ⟩
  rcases hτ₁' with ⟨g₁, G₁, hG₁, hg₁τ⟩
  have hgSource :
      (fiberInclusion p b).comp (ContinuousMap.id (fiber p b)) = G₀.toContinuousMap.curry 0 := by
    -- The first lift starts at the source fiber inclusion.
    ext x
    exact (G₀.apply_zero x).symm
  have hgRaw :
      (fiberInclusion p b').comp g₀ = G₀.toContinuousMap.curry 1 := by
    -- The endpoint of the first lift is exactly its induced map on the target fiber.
    ext x
    exact (G₀.apply_one x).symm
  let GrawLift : (G₀.toContinuousMap.curry 0).Homotopy ((fiberInclusion p b').comp g₀) :=
    { toFun := G₀.toContinuousMap
      continuous_toFun := G₀.toContinuousMap.continuous
      map_zero_left := by
        intro x
        rfl
      map_one_left := by
        intro x
        exact (ContinuousMap.congr_fun hgRaw x).symm }
  let G₁pre :
      (G₀.toContinuousMap.curry 0).Homotopy
        ((fiberInclusion p b').comp (g₁.comp (ContinuousMap.id (fiber p b)))) :=
    (G₁.compContinuousMap (ContinuousMap.id (fiber p b))).cast hgSource (by
      ext x
      rfl)
  have hProjectedRel :
      (p.comp (GrawLift.symm.trans G₁pre).toContinuousMap).HomotopicRel
        ((ContinuousMap.Homotopy.refl (ContinuousMap.const (fiber p b) b')).toContinuousMap)
        (({0, 1} : Set I) ×ˢ (Set.univ : Set (fiber p b))) := by
    -- Projecting the lift comparison gives the standard contractible loop over `b'`.
    simpa [GrawLift, G₁pre] using
      projectedLiftComparisonRelRefl
        (p := p) (β₁ := γ) (Graw := G₀.toContinuousMap) hG₀ hgSource hgRaw (G₁ := G₁) hG₁
  have hEndpoint :
      ContinuousMap.Homotopic g₀ g₁ := by
    -- The boundary-fixed projected contraction rectifies to a homotopy in the target fiber.
    simpa [G₁pre] using
      fiberEndpointHomotopic_of_projectedHomotopyRelConst
        (p := p) (F := GrawLift.symm.trans G₁pre) hProjectedRel
  -- Passing to homotopy classes identifies the two represented translations.
  calc
    τ₀ = ⟦g₀⟧ := by simpa using hg₀τ.symm
    _ = ⟦g₁⟧ := endpointClass_eq_of_homotopic p hEndpoint
    _ = τ₁ := hg₁τ

/-- Any represented fiber translation is equal to the canonical chosen class `fiberTranslationClass
p β`. -/
theorem fiberTranslationClass_eq (p : C(E, B)) [IsFibration p] {b b' : B}
    {β : Path.Homotopic.Quotient b b'} {τ : fiberMapHomotopyClasses p b b'}
    (hτ : IsFiberTranslation p β τ) :
    fiberTranslationClass p β = τ :=
  fiberTranslation_eq_of_isFiberTranslation p
    (isFiberTranslation_fiberTranslationClass p β) hτ

/-- Helper for Lemma 7.6.4: any admissible lift of `β.toHomotopyConst` represents the
unique fiber-translation class along `mk β`. -/
theorem fiberTranslationClass_eq_of_lift (p : C(E, B)) [IsFibration p] {b b' : B}
    (β : Path b b') (τ : fiberMapHomotopyClasses p b b')
    (g₁ : C(fiber p b, E)) (hg₁ : p.comp g₁ = ContinuousMap.const (fiber p b) b')
    (G : (fiberInclusion p b).Homotopy g₁)
    (hG : p.comp G.toContinuousMap = β.toHomotopyConst.toContinuousMap)
    (hτ : IsFiberTranslation p (mk β) τ) :
    ⟦fiberInclusionHomotopyLiftEndpointMap p g₁ hg₁⟧ = τ := by
  have hendpoint :
      IsFiberTranslation p (mk β) ⟦fiberInclusionHomotopyLiftEndpointMap p g₁ hg₁⟧ := by
    rw [isFiberTranslation_mk_iff]
    refine ⟨fiberInclusionHomotopyLiftEndpointMap p g₁ hg₁, ?_, ?_, rfl⟩
    · simpa using G
    · simpa using hG
  calc
    ⟦fiberInclusionHomotopyLiftEndpointMap p g₁ hg₁⟧ = fiberTranslationClass p (mk β) := by
      symm
      exact fiberTranslationClass_eq p hendpoint
    _ = τ := fiberTranslationClass_eq p hτ

/-- Endpoint-fixed homotopic representatives determine the same translation class. -/
theorem fiberTranslationClass_eq_of_homotopic (p : C(E, B)) [IsFibration p] {b b' : B}
    {β₀ β₁ : Path b b'} {τ₀ τ₁ : fiberMapHomotopyClasses p b b'} (hβ : β₀.Homotopic β₁)
    (hτ₀ : IsFiberTranslation p (mk β₀) τ₀) (hτ₁ : IsFiberTranslation p (mk β₁) τ₁) :
    τ₀ = τ₁ := by
  have hβq : mk β₀ = mk β₁ := eq.mpr hβ
  calc
    τ₀ = fiberTranslationClass p (mk β₀) := (fiberTranslationClass_eq p hτ₀).symm
    _ = fiberTranslationClass p (mk β₁) := by simp [hβq]
    _ = τ₁ := fiberTranslationClass_eq p hτ₁
