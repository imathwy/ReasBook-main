import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Definition_7_4_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Theorem_7_4_3

universe u v w x y

open Bundle ContinuousMap
open scoped unitInterval

variable {ι : Type u} {E : Type v} {B : Type w} {F : Type x}
variable [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace F]
variable [CompactlyGeneratedWeakHausdorffSpace.{v, v} E]
variable [CompactlyGeneratedWeakHausdorffSpace.{w, w} B]
variable [CompactlyGeneratedWeakHausdorffSpace.{x, x} F]

-- Semantic recall via `lean_leansearch`: mathlib exposes `Bundle.Trivialization` as the
-- canonical owner for local product charts, so this corollary is stated directly in terms of a
-- numerable cover whose members are trivialization base sets.

namespace Bundle.Trivialization

variable {p : C(E, B)} [Nonempty F]

/-- A trivialization identifies the restriction of `p` to its base set with the product projection,
so that restricted map carries the canonical Chapter 7 fibration instance. -/
instance isFibration_restrictPreimage_baseSet (e : Trivialization F p) :
    IsFibration.{v, w, y} (p.restrictPreimage e.baseSet) where
  surjective := by
    classical
    intro b
    let y : F := Classical.choice ‹Nonempty F›
    refine ⟨(e.preimageHomeomorph subset_rfl).symm (b, y), ?_⟩
    apply Subtype.ext
    simpa [ContinuousMap.restrictPreimage, y] using e.proj_symm_apply' b.2
  homotopyLift {A} _ _ {f₀} {f₁} H {g₀} hg₀ := by
    let eproj : C(p ⁻¹' e.baseSet, e.baseSet × F) :=
      e.preimageHomeomorph subset_rfl
    let fiberCoord : C(A, F) := ContinuousMap.snd.comp (eproj.comp g₀)
    let g₁BaseProd : C(A, e.baseSet × F) := f₁.prodMk fiberCoord
    let g₁ : C(A, p ⁻¹' e.baseSet) :=
      (((e.preimageHomeomorph subset_rfl).symm :
          C(e.baseSet × F, p ⁻¹' e.baseSet))).comp g₁BaseProd
    have hg₀BaseProd : eproj.comp g₀ = f₀.prodMk fiberCoord := by
      apply DFunLike.ext
      intro a
      apply Prod.ext
      · apply Subtype.ext
        simpa [eproj, fiberCoord, ContinuousMap.restrictPreimage] using
          congrArg Subtype.val (ContinuousMap.congr_fun hg₀ a)
      · rfl
    let GBaseProd : (eproj.comp g₀).Homotopy g₁BaseProd :=
      (H.prodMk (ContinuousMap.Homotopy.refl fiberCoord)).cast hg₀BaseProd.symm rfl
    let Gcomp :=
      (ContinuousMap.Homotopy.refl
        ((e.preimageHomeomorph subset_rfl).symm :
          C(e.baseSet × F, p ⁻¹' e.baseSet))).comp GBaseProd
    have hG0 :
        (((((e.preimageHomeomorph subset_rfl).symm :
            C(e.baseSet × F, p ⁻¹' e.baseSet)).comp eproj).comp g₀)) = g₀ := by
      simp [eproj]
    let G : g₀.Homotopy g₁ := Gcomp.cast hG0 rfl
    refine ⟨g₁, G, ?_⟩
    ext tx
    change p (G tx) = ↑(H tx)
    simpa
      [G, Gcomp, GBaseProd, g₁, g₁BaseProd, eproj, fiberCoord,
        ContinuousMap.restrictPreimage] using
      e.proj_symm_apply' (H tx).2

/-- Rewriting the base set of a trivialization rewrites the corresponding restricted fibration. -/
theorem isFibration_restrictPreimage_of_baseSet_eq (e : Trivialization F p) {s : Set B}
    (hs : e.baseSet = s) : IsFibration.{v, w, y} (p.restrictPreimage s) := by
  induction hs
  simpa using e.isFibration_restrictPreimage_baseSet

end Bundle.Trivialization

/-- Helper for Corollary 7.4.5: a global continuous path-lifting function produces the covering
homotopy property for the requested test-space universe. -/
theorem hasCoveringHomotopyProperty_of_nonemptyContinuousPathLiftingFunction
    {p : C(E, B)} (hpath : Nonempty (ContinuousPathLiftingFunction p)) :
    HasCoveringHomotopyProperty.{v, w, max v w} p := by
  rcases hpath with ⟨s⟩
  refine (hasCoveringHomotopyProperty_iff_lift_pathSpaceEvalAtZero (p := p)).2 ?_
  intro A _ _ g₀ d hd
  have hstart (a : A) : d a 0 = p (g₀ a) := by
    -- Pointwise, the commutative square says the path starts over `p (g₀ a)`.
    simpa using ContinuousMap.congr_fun hd a
  have hfamilyMem (a : A) :
      ((g₀ a, d a) : E × C(I, B)).2 0 = p (((g₀ a, d a) : E × C(I, B)).1) := by
    -- Rephrase the compatibility equation in the ambient product used by the mapping path space.
    simpa using hstart a
  have hfamilyContinuous :
      Continuous fun a : A ↦ MappingPathSpace.mk (g₀ a) (d a) (hfamilyMem a) := by
    -- A compatible pair `(g₀ a, d a)` lands continuously in the mapping path space.
    exact MappingPathSpace.continuous_mk g₀.continuous d.continuous hfamilyMem
  let family : C(A, MappingPathSpace p) :=
    ⟨fun a ↦ MappingPathSpace.mk (g₀ a) (d a) (hfamilyMem a), hfamilyContinuous⟩
  let D : C(A, C(I, E)) := s.toContinuousMap.comp family
  have hD₀ : (pathSpaceEvalAtZero E).comp D = g₀ := by
    -- The chosen continuous lift starts at the specified point.
    apply ContinuousMap.ext
    intro a
    simpa [D, family] using s.source_eq (family a)
  have hDproj : (pathSpacePostcompose p).comp D = d := by
    -- The chosen continuous lift projects to the prescribed path family.
    apply ContinuousMap.ext
    intro a
    ext t
    simpa [D, family, pathSpacePostcompose] using
      congrArg (fun γ : I → B ↦ γ t) (s.proj_comp_eq (family a))
  exact ⟨D, hD₀, hDproj⟩

/-- If the members of a numerable open cover are the base sets of trivializations of `p`, then the
restrictions of `p` to those members are fibrations. -/
theorem forall_restrictPreimage_isFibration_of_trivializationBaseSet [Nonempty F] (p : C(E, B))
    (𝒰 : NumerableOpenCover ι B)
    (htriv : ∀ i : ι, ∃ e : Bundle.Trivialization F p, e.baseSet = 𝒰.cover i) :
    ∀ i : ι, IsFibration.{v, w, y} (p.restrictPreimage (𝒰.cover i)) := by
  intro i
  rcases htriv i with ⟨e, he⟩
  -- Normalize the cover member to the trivialization base set, then use the canonical local chart.
  exact e.isFibration_restrictPreimage_of_baseSet_eq he

/-- A numerable open cover by trivialization base sets exhibits `p` as a bundle map in the sense
of `Definition 7.4.1`. -/
theorem isFiberBundleMap_of_numerableTrivializingCover (p : C(E, B)) (𝒰 : NumerableOpenCover ι B)
    (htriv : ∀ i : ι, ∃ e : Bundle.Trivialization F p, e.baseSet = 𝒰.cover i) :
    IsFiberBundleMap F p := by
  intro b
  obtain ⟨i, hi⟩ := 𝒰.isOpenCover.exists_mem b
  rcases htriv i with ⟨e, he⟩
  exact ⟨e, he ▸ hi⟩

/-- Corollary 7.4.5: a bundle map `p : C(E, B)` is a fibration whenever it admits a numerable
open cover whose numerating functions are continuous and sum to `1`, and whose members are
exactly the base sets of local trivializations. -/
theorem isFibration_of_exists_numerableTrivializingCover [Nonempty F] (p : C(E, B))
    (𝒰 : NumerableOpenCover ι B)
    (hcont : ∀ i, Continuous (𝒰 i))
    (hsum : ∀ b, ∑' i, (𝒰 i b : ℝ) = 1)
    (htriv : ∀ i : ι, ∃ e : Bundle.Trivialization F p, e.baseSet = 𝒰.cover i) :
    IsFibration.{v, w, max v w} p := by
  -- Theorem 7.4.3 globalizes the local trivialization fibrations at the canonical universe of
  -- the mapping-path construction.
  have hlocalMax : ∀ i : ι, IsFibration.{v, w, max v w} (p.restrictPreimage (𝒰.cover i)) := by
    intro i
    -- Re-run the local trivialization argument at the universe expected by Theorem 7.4.3.
    exact forall_restrictPreimage_isFibration_of_trivializationBaseSet p 𝒰 htriv i
  exact isFibration_of_forall_restrictPreimage_isFibration 𝒰 hcont hsum p hlocalMax
