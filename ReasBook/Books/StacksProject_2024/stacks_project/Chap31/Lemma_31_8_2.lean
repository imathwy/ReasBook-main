import StacksProject_2024.Chap17.Lemma_17_10_4
import StacksProject_2024.Chap31.Definition_31_7_1
import StacksProject_2024.Chap31.Definition_31_8_1
import StacksProject_2024.Chap31.Lemma_31_5_8

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/- If `f` is locally of finite type, then each scheme-theoretic fiber of `f` is locally
Noetherian because it is locally of finite type over the spectrum of a field. -/
theorem fiber_isLocallyNoetherian_of_locallyOfFiniteType [LocallyOfFiniteType f] (s : S) :
    IsLocallyNoetherian (f.fiber s) := by
  let _ : LocallyOfFiniteType (f.fiberToSpecResidueField s) := by
    change LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd f (S.fromSpecResidueField s))
    infer_instance
  let _ : IsLocallyNoetherian (Spec (S.residueField s)) := inferInstance
  exact LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField s)

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}}

-- Semantic recall: `lean_leansearch` surfaced `LocallyOfFiniteType.isLocallyNoetherian` as the
-- canonical locally Noetherian transfer theorem. The local Chapter 31 owners for the two relative
-- sets are `relativeAssassin` and `relativeWeakAss`, and Lemma `31.5.8` provides the fiberwise
-- comparison once each scheme-theoretic fiber is known to be locally Noetherian.
local notation:max ℱ:max " |[" f "," s "]" =>
  ((Scheme.Modules.pullback (f.fiberι s)).obj ℱ)

/-- For a locally finite type morphism, the associated and weakly associated points of the
restriction of a quasi-coherent module to any scheme-theoretic fiber coincide. -/
theorem fiber_associatedPoints_eq_weakAss_of_locallyOfFiniteType
    (f : X ⟶ S) [LocallyOfFiniteType f] (ℱ : X.Modules) [ℱ.IsQuasicoherent] (s : S) :
    (ℱ |[f, s]).associatedPoints = (ℱ |[f, s]).weakAss := by
  letI : (ℱ |[f, s]).IsQuasicoherent := by
    simpa using ringedSpaceModulePullback_isQuasicoherent (f.fiberι s) ℱ
  let _ : IsLocallyNoetherian (f.fiber s) :=
    Scheme.Hom.fiber_isLocallyNoetherian_of_locallyOfFiniteType f s
  exact associatedPoints_eq_weakAss_of_isLocallyNoetherian (ℱ |[f, s])

/-- Fiberwise pointwise companion to `fiber_associatedPoints_eq_weakAss_of_locallyOfFiniteType`. -/
@[simp]
theorem mem_associatedPoints_iff_mem_weakAss_of_fiber_of_locallyOfFiniteType
    (f : X ⟶ S) [LocallyOfFiniteType f] (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (s : S) (y : f.fiber s) :
    y ∈ (ℱ |[f, s]).associatedPoints ↔ y ∈ (ℱ |[f, s]).weakAss := by
  rw [← fiber_associatedPoints_eq_weakAss_of_locallyOfFiniteType f ℱ s]

/-- Lemma 31.8.2: let `f : X ⟶ S` be a morphism of schemes which is locally of finite type. Let
`\mathcal F` be a quasi-coherent `\mathcal O_X`-module. Then
`\mathrm{WeakAss}_{X/S}(\mathcal F) = \mathrm{Ass}_{X/S}(\mathcal F)`. -/
@[stacks 05F2]
theorem relativeWeakAss_eq_relativeAssassin_of_locallyOfFiniteType
    (f : X ⟶ S) [LocallyOfFiniteType f] (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    relativeWeakAss f ℱ = relativeAssassin f ℱ := by
  ext x
  rw [mem_relativeWeakAss_iff, mem_relativeAssassin_iff]
  constructor
  · rintro ⟨s, y, hy, hyx⟩
    exact
      ⟨s, y,
        (mem_associatedPoints_iff_mem_weakAss_of_fiber_of_locallyOfFiniteType f ℱ s y).2 hy,
        hyx⟩
  · rintro ⟨s, y, hy, hyx⟩
    exact
      ⟨s, y,
        (mem_associatedPoints_iff_mem_weakAss_of_fiber_of_locallyOfFiniteType f ℱ s y).1 hy,
        hyx⟩

/-- Under the hypotheses of Lemma 31.8.2, a point is relatively weakly associated exactly when it
is relatively associated. -/
@[simp]
theorem mem_relativeWeakAss_iff_mem_relativeAssassin_of_locallyOfFiniteType
    (f : X ⟶ S) [LocallyOfFiniteType f] (ℱ : X.Modules) [ℱ.IsQuasicoherent] (x : X) :
    x ∈ relativeWeakAss f ℱ ↔ x ∈ relativeAssassin f ℱ := by
  rw [relativeWeakAss_eq_relativeAssassin_of_locallyOfFiniteType f ℱ]

end AlgebraicGeometry.Scheme.Modules
