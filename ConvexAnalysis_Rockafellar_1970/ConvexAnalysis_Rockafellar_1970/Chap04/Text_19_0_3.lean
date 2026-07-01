import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_1_2
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_5_9
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_5_10
import ConvexAnalysis_Rockafellar_1970.Chap04.Definition_17_2_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open scoped Rockafellar

variable {𝕜 : Type u} {E : Type v} {Y : Type (max u v)}

/-!
Source/core/bridge triage:

- `source-facing`: Text 19.0.3 characterizes which polyhedral convex subsets are cones, namely
  those admitting a finite defining family of closed half-spaces through the origin. In this
  project the source-facing cone owner `Set.IsCone 𝕜` does not itself force the origin to belong
  to the set, so the translated statement must keep the origin condition explicit.
- `core/canonical`: the owner abstractions already present in the project are
  `Set.IsPolyhedral` for polyhedral convex sets, `Set.IsConvexCone 𝕜` for the convex-conic
  structure, `Set.IsCone 𝕜` for the positive-ray closure component, the chapter weak-system owner
  `linearInequalitySolutionSet`, and the half-space owner `closedHalfSpaceLE`.
- `bridge/view`: the textbook finite family of homogeneous closed half-spaces
  `closedHalfSpaceLE y 0` is exactly the finite homogeneous weak-system owner surface obtained
  from a finite family `S : Finset (Y × 𝕜)` with `y.2 = 0` for each `y ∈ S`.
- Primitive data vs derived API: the primitive source-facing data are the finite family of
  pairing normals defining the homogeneous inequalities; the chapter owner
  `linearInequalitySolutionSet` is the canonical set attached to that data, while the explicit
  finite-half-space intersection is a thin companion view.
- Domain-style sampling used here: `Set.IsPolyhedral`, `linearInequalitySolutionSet`,
  `mem_linearInequalitySolutionSet_iff`, `closedHalfSpaceLE`, and
  `mem_closedHalfSpaceLE_iff`.
- Layer target: `core/canonical` for the main weak-system presentation, with the explicit
  half-space statement kept as a thin `bridge/view` companion.
-/

section ConeCharacterization

section PrimitiveDirections

variable [CommSemiring 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommMonoid E] [Module 𝕜 E]
  [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing E Y 𝕜]

/-- Primitive owner-level direction: if a set is presented by finitely many homogeneous weak
linear inequalities, then it is a cone (in the chapter sense) and contains the origin. This does
not require any polyhedrality assumption, since the finite homogeneous weak-system owner already
contains the needed primitive data. -/
theorem Set.isCone_zero_mem_of_exists_finset_homogeneous_linearInequalitySolutionSet
    {C : Set E}
    (hC :
      ∃ S : Finset (Y × 𝕜),
        (∀ y ∈ S, y.2 = (0 : 𝕜)) ∧
          C = solutionSet[(S : Set (Y × 𝕜))]) :
    Set.IsCone 𝕜 C ∧ (0 : E) ∈ C := by
  rcases hC with ⟨S, hS_hom, hS⟩
  refine ⟨?_, ?_⟩
  · intro c hc x hx
    rw [hS, mem_linearInequalitySolutionSet_iff] at hx ⊢
    intro y hyS
    have hyx : (⟪x, y.1⟫ₚ : 𝕜) ≤ y.2 := hx y hyS
    have hy0 : y.2 = (0 : 𝕜) := hS_hom y hyS
    have hc0 : (0 : 𝕜) ≤ c := (show (0 : 𝕜) < c from hc).le
    have hyx0 : (⟪x, y.1⟫ₚ : 𝕜) ≤ 0 := by simpa [hy0] using hyx
    have hy_mul : c * (⟪x, y.1⟫ₚ : 𝕜) ≤ c * 0 :=
      mul_le_mul_of_nonneg_left (a := c) hyx0 hc0
    have hcy0 : (⟪c • x, y.1⟫ₚ : 𝕜) ≤ 0 := by
      calc
        (⟪c • x, y.1⟫ₚ : 𝕜) = c * ⟪x, y.1⟫ₚ := by simp
        _ ≤ c * 0 := hy_mul
        _ = 0 := by simp
    simpa [hy0] using hcy0
  · rw [hS, mem_linearInequalitySolutionSet_iff]
    intro y hyS
    simp [hS_hom y hyS]

/-- Primitive owner-level half-space bridge direction: if a set is a finite intersection of
homogeneous closed half-spaces, then it is a cone and contains the origin. -/
theorem Set.isCone_zero_mem_of_exists_finset_homogeneous_closedHalfSpaceLE
    {C : Set E}
    (hC : ∃ S : Finset Y, C = ⋂ y ∈ S, closedHalfSpaceLE y (0 : 𝕜)) :
    Set.IsCone 𝕜 C ∧ (0 : E) ∈ C := by
  classical
  rcases hC with ⟨S, hS⟩
  have hHom :
      ∃ T : Finset (Y × 𝕜),
        (∀ y ∈ T, y.2 = (0 : 𝕜)) ∧
          C = solutionSet[(T : Set (Y × 𝕜))] := by
    refine ⟨S.image fun y : Y ↦ (y, (0 : 𝕜)), ?_, ?_⟩
    · intro y hy
      rcases Finset.mem_image.mp hy with ⟨z, hz, rfl⟩
      simp
    · rw [hS]
      ext x
      simp [mem_closedHalfSpaceLE_iff]
  exact Set.isCone_zero_mem_of_exists_finset_homogeneous_linearInequalitySolutionSet hHom

/-- Primitive owner-level canonical form: a finite homogeneous weak-system presentation already
gives a convex cone (in the chapter owner `Set.IsConvexCone 𝕜`) together with origin membership.
-/
theorem Set.isConvexCone_zero_mem_of_exists_finset_homogeneous_linearInequalitySolutionSet
    {C : Set E}
    (hC :
      ∃ S : Finset (Y × 𝕜),
        (∀ y ∈ S, y.2 = (0 : 𝕜)) ∧
          C = solutionSet[(S : Set (Y × 𝕜))]) :
    Set.IsConvexCone 𝕜 C ∧ (0 : E) ∈ C := by
  rcases hC with ⟨S, hS_hom, hS⟩
  have hConeZero :
      Set.IsCone 𝕜 C ∧ (0 : E) ∈ C :=
    Set.isCone_zero_mem_of_exists_finset_homogeneous_linearInequalitySolutionSet
      (C := C) ⟨S, hS_hom, hS⟩
  have hPoly : C.IsPolyhedral 𝕜 Y := by
    refine ⟨S, ?_⟩
    simpa [hS] using
      (linearInequalitySolutionSet_eq_iInter_closedHalfSpaceLE
        (E := E) (Y := Y) (R := 𝕜) (SStar := (S : Set (Y × 𝕜))))
  exact ⟨⟨hConeZero.1, hPoly.convex⟩, hConeZero.2⟩

/-- Primitive owner-level canonical half-space bridge: a finite homogeneous closed-half-space
presentation already gives a convex cone and origin membership. -/
theorem Set.isConvexCone_zero_mem_of_exists_finset_homogeneous_closedHalfSpaceLE
    {C : Set E}
    (hC : ∃ S : Finset Y, C = ⋂ y ∈ S, closedHalfSpaceLE y (0 : 𝕜)) :
    Set.IsConvexCone 𝕜 C ∧ (0 : E) ∈ C := by
  classical
  rcases hC with ⟨S, hS⟩
  have hHom :
      ∃ T : Finset (Y × 𝕜),
        (∀ y ∈ T, y.2 = (0 : 𝕜)) ∧
          C = solutionSet[(T : Set (Y × 𝕜))] := by
    refine ⟨S.image fun y : Y ↦ (y, (0 : 𝕜)), ?_, ?_⟩
    · intro y hy
      rcases Finset.mem_image.mp hy with ⟨z, hz, rfl⟩
      simp
    · rw [hS]
      ext x
      simp [mem_closedHalfSpaceLE_iff]
  exact Set.isConvexCone_zero_mem_of_exists_finset_homogeneous_linearInequalitySolutionSet hHom

end PrimitiveDirections

section PolyhedralCharacterization

variable [Semifield 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommMonoid E] [Module 𝕜 E]
  [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing E Y 𝕜]

/-- Text 19.0.3, in canonical ambient form: a polyhedral convex set `C` is a cone with vertex at
the origin if and only if it is the solution set of a finite homogeneous weak linear system,
expressed through the chapter owner `linearInequalitySolutionSet`. The explicit hypothesis
`0 ∈ C` is the source-faithful translation of “with vertex at the origin”, since this project's
`Set.IsCone 𝕜` records only positive-scalar closure. -/
-- Proof sketch: start from a finite owner-half-space presentation of `C` coming from
-- `Set.IsPolyhedral`. If `C` is a cone and contains the origin, each defining level can be
-- replaced by `0`, yielding a finite homogeneous family encoded by
-- `solutionSet[S]` together with the owner-level homogeneity condition
-- `∀ y ∈ S, y.2 = 0`.
-- Conversely,
-- each such owner half-space is homogeneous and contains `0`, and finite intersections preserve
-- both properties.
theorem Set.IsPolyhedral.isCone_zero_mem_iff_exists_finset_homogeneous_linearInequalitySolutionSet
    {C : Set E} (hC : C.IsPolyhedral 𝕜 Y) :
    Set.IsCone 𝕜 C ∧ (0 : E) ∈ C ↔
      ∃ S : Finset (Y × 𝕜),
        (∀ y ∈ S, y.2 = (0 : 𝕜)) ∧
          C = solutionSet[(S : Set (Y × 𝕜))] := by
  classical
  constructor
  · rintro ⟨hCone, h0⟩
    rcases hC with ⟨S, hS⟩
    let T : Finset (Y × 𝕜) := S.image fun p : Y × 𝕜 ↦ (p.1, (0 : 𝕜))
    refine ⟨T, ?_, ?_⟩
    · intro y hyT
      rcases Finset.mem_image.mp hyT with ⟨p, hpS, rfl⟩
      simp
    ext x
    constructor
    · intro hx
      rw [mem_linearInequalitySolutionSet_iff]
      intro y hyT
      rcases Finset.mem_image.mp hyT with ⟨p, hpS, rfl⟩
      have hbdd : BddAbove ((fun z : E ↦ (⟪z, p.1⟫ₚ : 𝕜)) '' C) := by
        refine ⟨p.2, ?_⟩
        rintro _ ⟨z, hzC, rfl⟩
        have hzS : ∀ q ∈ S, ⟪z, q.1⟫ₚ ≤ q.2 := by
          simpa [hS, mem_closedHalfSpaceLE_iff] using hzC
        exact hzS p hpS
      have hy_nonpos : (⟪x, p.1⟫ₚ : 𝕜) ≤ 0 :=
        Set.IsCone.pairing_nonpos_of_bddAbove hCone hbdd x hx
      simpa using hy_nonpos
    · intro hx
      rw [hS]
      have h0S : ∀ p ∈ S, ⟪(0 : E), p.1⟫ₚ ≤ p.2 := by
        simpa [hS, mem_closedHalfSpaceLE_iff] using h0
      rw [mem_linearInequalitySolutionSet_iff] at hx
      have hxS : ∀ p ∈ S, ⟪x, p.1⟫ₚ ≤ p.2 := by
        intro p hp
        have hpT : (p.1, (0 : 𝕜)) ∈ T :=
          Finset.mem_image.mpr ⟨p, hp, by simp⟩
        have hpx : ⟪x, p.1⟫ₚ ≤ (0 : 𝕜) := by
          simpa using hx (p.1, (0 : 𝕜)) hpT
        have hp0 : (0 : 𝕜) ≤ p.2 := by
          simpa using h0S p hp
        exact le_trans hpx hp0
      simpa [mem_closedHalfSpaceLE_iff] using hxS
  · intro hHom
    exact Set.isCone_zero_mem_of_exists_finset_homogeneous_linearInequalitySolutionSet hHom

/-- Canonical convex-cone owner form of Text 19.0.3: for a polyhedral set, the source-facing
"cone with vertex at the origin" condition is equivalent to `Set.IsConvexCone 𝕜 C` together with
`0 ∈ C`, and this holds exactly when `C` is given by finitely many homogeneous weak inequalities.
-/
theorem Set.IsPolyhedral.isConvexCone_zero_mem_iff_exists_finset_homogeneous_linearInequalitySolutionSet
    {C : Set E} (hC : C.IsPolyhedral 𝕜 Y) :
    Set.IsConvexCone 𝕜 C ∧ (0 : E) ∈ C ↔
      ∃ S : Finset (Y × 𝕜),
        (∀ y ∈ S, y.2 = (0 : 𝕜)) ∧
          C = solutionSet[(S : Set (Y × 𝕜))] := by
  constructor
  · rintro ⟨hConvCone, h0⟩
    exact
      (Set.IsPolyhedral.isCone_zero_mem_iff_exists_finset_homogeneous_linearInequalitySolutionSet
        hC).mp ⟨hConvCone.isCone, h0⟩
  · intro hHom
    exact
      Set.isConvexCone_zero_mem_of_exists_finset_homogeneous_linearInequalitySolutionSet
        hHom

/-- Companion source-facing form: a polyhedral convex set is a cone with vertex at the origin if
and only if it is the intersection of finitely many homogeneous closed half-spaces
`closedHalfSpaceLE y 0`. -/
theorem Set.IsPolyhedral.isCone_zero_mem_iff_exists_finset_homogeneous_closedHalfSpaceLE
    {C : Set E} (hC : C.IsPolyhedral 𝕜 Y) :
    Set.IsCone 𝕜 C ∧ (0 : E) ∈ C ↔
      ∃ S : Finset Y, C = ⋂ y ∈ S, closedHalfSpaceLE y (0 : 𝕜) := by
  classical
  constructor
  · intro hConeZero
    rcases
        (Set.IsPolyhedral.isCone_zero_mem_iff_exists_finset_homogeneous_linearInequalitySolutionSet
          hC).mp hConeZero with ⟨S, hS_hom, hS⟩
    let T : Finset Y := S.image Prod.fst
    refine ⟨T, ?_⟩
    ext x
    constructor
    · intro hx
      rw [mem_iInter]
      intro y
      rw [mem_iInter]
      intro hyT
      rw [mem_closedHalfSpaceLE_iff]
      have hxS : x ∈ solutionSet[(S : Set (Y × 𝕜))] := by simpa [hS] using hx
      rw [mem_linearInequalitySolutionSet_iff] at hxS
      rcases Finset.mem_image.mp hyT with ⟨p, hpS, hp_eq⟩
      have hxp : (⟪x, p.1⟫ₚ : 𝕜) ≤ p.2 := hxS p hpS
      simpa [hS_hom p hpS, hp_eq] using hxp
    · intro hx
      rw [hS, mem_linearInequalitySolutionSet_iff]
      have hxT : ∀ y ∈ T, (⟪x, y⟫ₚ : 𝕜) ≤ 0 := by
        simpa [mem_closedHalfSpaceLE_iff]
          using hx
      intro p hpS
      have hpT : p.1 ∈ T := Finset.mem_image.mpr ⟨p, hpS, rfl⟩
      have hxp : (⟪x, p.1⟫ₚ : 𝕜) ≤ 0 := hxT p.1 hpT
      simpa [hS_hom p hpS] using hxp
  · rintro ⟨S, hS⟩
    exact Set.isCone_zero_mem_of_exists_finset_homogeneous_closedHalfSpaceLE ⟨S, hS⟩

/-- Canonical convex-cone owner companion: for a polyhedral set, the condition
`Set.IsConvexCone 𝕜 C ∧ 0 ∈ C` is equivalent to a finite homogeneous closed-half-space
presentation. -/
theorem Set.IsPolyhedral.isConvexCone_zero_mem_iff_exists_finset_homogeneous_closedHalfSpaceLE
    {C : Set E} (hC : C.IsPolyhedral 𝕜 Y) :
    Set.IsConvexCone 𝕜 C ∧ (0 : E) ∈ C ↔
      ∃ S : Finset Y, C = ⋂ y ∈ S, closedHalfSpaceLE y (0 : 𝕜) := by
  constructor
  · rintro ⟨hConvCone, h0⟩
    exact
      (Set.IsPolyhedral.isCone_zero_mem_iff_exists_finset_homogeneous_closedHalfSpaceLE
        hC).mp ⟨hConvCone.isCone, h0⟩
  · intro hHom
    exact Set.isConvexCone_zero_mem_of_exists_finset_homogeneous_closedHalfSpaceLE hHom

end PolyhedralCharacterization

end ConeCharacterization

end
