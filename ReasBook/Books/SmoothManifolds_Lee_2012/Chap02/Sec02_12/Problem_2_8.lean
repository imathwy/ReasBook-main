import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import SmoothManifolds_Lee_2012.Chap01.Sec01_04.Example_1_33
import SmoothManifolds_Lee_2012.Chap01.Sec01_07.Problem_1_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Projectivization
open scoped Manifold ContDiff

-- These source-facing affine-chart declarations are derived from the existing projective-chart
-- owners `realProjectiveChart` and `complexProjectiveChart`.

section RealProjective

variable (n : ℕ)

/-- Helper for Problem 2-8: the complement of a coordinate hyperplane is dense in real Euclidean
space. -/
theorem real_coordinate_ne_zero_dense {m : ℕ} (k : Fin m) :
    Dense {u : EuclideanSpace ℝ (Fin m) | u k ≠ 0} := by
  -- Pull back the dense punctured line along the open coordinate projection.
  simpa [Set.preimage, Set.compl_singleton_eq] using
    (dense_compl_singleton (0 : ℝ)).preimage
      (PiLp.isOpenMap_apply (p := 2) (β := fun _ : Fin m => ℝ) k)

/-- The standard affine open subset of `ℝPⁿ` cut out by the nonvanishing of the last homogeneous
coordinate. -/
def realProjectiveAffineOpen : TopologicalSpace.Opens (ℝP[n]) :=
  ⟨realProjectiveChartDomain n (Fin.last n), realProjectiveChartDomain_isOpen n (Fin.last n)⟩

/-- The map `x ↦ [x, 1]` from `ℝⁿ` into `ℝPⁿ`. -/
def realProjectiveAffineInclusion : EuclideanSpace ℝ (Fin n) → ℝP[n] :=
  (realProjectiveChart n (Fin.last n)).symm

/-- The map `x ↦ [x, 1]` viewed as a map into the standard affine open subset of `ℝPⁿ`. -/
def realProjectiveAffineInclusionToOpen :
    EuclideanSpace ℝ (Fin n) → realProjectiveAffineOpen n :=
  fun x ↦
    ⟨realProjectiveAffineInclusion n x, realProjectiveChart_symm_mem_domain n (Fin.last n) x⟩

/-- The inverse affine chart on the standard open subset of `ℝPⁿ` with last homogeneous coordinate
nonzero. -/
def realProjectiveAffineChart : realProjectiveAffineOpen n → EuclideanSpace ℝ (Fin n) :=
  fun x ↦ realProjectiveChart n (Fin.last n) x.1

/-- The standard affine open subset of `ℝPⁿ` is dense. -/
theorem realProjectiveAffineOpen_dense :
    Dense (realProjectiveAffineOpen n : Set (ℝP[n])) := by
  let E := EuclideanSpace ℝ (Fin (n + 1))
  let s : Set { v : E // v ≠ 0 } := { v | v.1 (Fin.last n) ≠ 0 }
  let q : { v : E // v ≠ 0 } → ℝP[n] := Projectivization.mk' ℝ
  have hs_dense : Dense s := by
    -- Restrict the dense nonvanishing last-coordinate locus to the open subtype of nonzero representatives.
    simpa [s, Set.preimage, Set.compl_singleton_eq] using
      (real_coordinate_ne_zero_dense (m := n + 1) (Fin.last n)).preimage
        ((isOpen_compl_singleton : IsOpen ({(0 : E)}ᶜ : Set E)).isOpenMap_subtype_val)
  have hq_cont : Continuous q := by
    -- The projectivization map is the quotient projection on nonzero representatives.
    simpa [q, Projectivization.mk'] using
      (continuous_quotient_mk' :
        Continuous (@Quotient.mk' { v : E // v ≠ 0 } (projectivizationSetoid ℝ E)))
  have hq_surj : Function.Surjective q := by
    intro x
    refine ⟨⟨x.rep, x.rep_nonzero⟩, ?_⟩
    simpa [q, x.mk_rep]
  have hq_dense : Dense (q '' s) := by
    -- A continuous surjection sends a dense subset of representatives to a dense set of projective classes.
    exact hq_surj.denseRange.dense_image hq_cont hs_dense
  have hs_eq : q '' s = (realProjectiveAffineOpen n : Set (ℝP[n])) := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      -- A representative with nonzero last coordinate lands in the last affine chart domain.
      simpa [q, s, realProjectiveAffineOpen] using
        (realProjectiveChartDomain_mk n (Fin.last n) v.1 v.2).2 hv
    · intro hx
      refine ⟨⟨x.rep, x.rep_nonzero⟩, ?_, ?_⟩
      · -- Membership in the affine open means the chosen representative has nonzero last coordinate.
        have hmem : Projectivization.mk ℝ x.rep x.rep_nonzero ∈
            realProjectiveChartDomain n (Fin.last n) := by
          simpa [realProjectiveAffineOpen, x.mk_rep] using hx
        exact (realProjectiveChartDomain_mk n (Fin.last n) x.rep x.rep_nonzero).1 hmem
      · simpa [q, x.mk_rep]
  simpa [hs_eq] using hq_dense

/-- The affine inclusion `x ↦ [x, 1]` is left-inverse to the last standard chart on `ℝPⁿ`. -/
theorem realProjectiveAffineInclusion_left_inv :
    Function.LeftInverse (realProjectiveAffineChart n)
      (realProjectiveAffineInclusionToOpen n) := by
  intro x
  -- Applying the last chart to its inverse branch recovers the original affine coordinates.
  simpa [realProjectiveAffineChart, realProjectiveAffineInclusionToOpen,
    realProjectiveAffineInclusion] using
    OpenPartialHomeomorph.right_inv (realProjectiveChart n (Fin.last n)) (Set.mem_univ x)

/-- The affine inclusion `x ↦ [x, 1]` is right-inverse to the last standard chart on `ℝPⁿ`. -/
theorem realProjectiveAffineInclusion_right_inv :
    Function.RightInverse (realProjectiveAffineChart n)
      (realProjectiveAffineInclusionToOpen n) := by
  intro x
  apply Subtype.ext
  -- On the last affine chart domain, the inverse branch returns the original projective point.
  simpa [realProjectiveAffineChart, realProjectiveAffineInclusionToOpen,
    realProjectiveAffineInclusion] using
    OpenPartialHomeomorph.left_inv (realProjectiveChart n (Fin.last n)) x.2

/-- The affine inclusion `x ↦ [x, 1]` is smooth as a map from `ℝⁿ` to the affine open subset of
`ℝPⁿ`. -/
theorem realProjectiveAffineInclusion_contMDiff :
    ContMDiff (𝓡 n) (𝓡 n) ∞ (realProjectiveAffineInclusionToOpen n) := by
  have hAtlas : realProjectiveChart n (Fin.last n) ∈ atlas (EuclideanSpace ℝ (Fin n)) (ℝP[n]) := by
    change realProjectiveChart n (Fin.last n) ∈ { e |
      ∃ i : Fin (n + 1), e = realProjectiveChart n i }
    exact ⟨Fin.last n, rfl⟩
  have hMax : realProjectiveChart n (Fin.last n) ∈
      IsManifold.maximalAtlas (𝓡 n) ∞ (ℝP[n]) :=
    IsManifold.subset_maximalAtlas hAtlas
  -- It suffices to forget the codomain subtype and prove smoothness of the ambient inverse chart.
  rw [← ContMDiff.subtypeVal_comp_iff (U := realProjectiveAffineOpen n)
    (f := realProjectiveAffineInclusionToOpen n)]
  change ContMDiff (𝓡 n) (𝓡 n) ∞ (realProjectiveAffineInclusion n)
  intro x
  -- The inverse branch of a maximal-atlas chart is smooth on the whole target, here `Set.univ`.
  simpa [realProjectiveAffineInclusion] using
    contMDiffAt_symm_of_mem_maximalAtlas hMax (by simp : x ∈ Set.univ)

/-- The last standard affine chart on `ℝPⁿ` is smooth. -/
theorem realProjectiveAffineChart_contMDiff :
    ContMDiff (𝓡 n) (𝓡 n) ∞ (realProjectiveAffineChart n) := by
  have hAtlas : realProjectiveChart n (Fin.last n) ∈ atlas (EuclideanSpace ℝ (Fin n)) (ℝP[n]) := by
    change realProjectiveChart n (Fin.last n) ∈ { e |
      ∃ i : Fin (n + 1), e = realProjectiveChart n i }
    exact ⟨Fin.last n, rfl⟩
  have hMax : realProjectiveChart n (Fin.last n) ∈
      IsManifold.maximalAtlas (𝓡 n) ∞ (ℝP[n]) :=
    IsManifold.subset_maximalAtlas hAtlas
  intro x
  -- Restrict the ambient chart to its source subtype `realProjectiveAffineOpen n`.
  refine (contMDiffAt_subtype_iff (U := realProjectiveAffineOpen n)
    (f := realProjectiveChart n (Fin.last n)) (x := x)).mpr ?_
  simpa [realProjectiveAffineOpen] using contMDiffAt_of_mem_maximalAtlas hMax x.2

/-- The underlying map of `realProjectiveAffineDiffeomorph` is the explicit affine inclusion
`x ↦ [x, 1]`. -/
theorem realProjectiveAffineInclusionToOpen_coe (x : EuclideanSpace ℝ (Fin n)) :
    ((realProjectiveAffineInclusionToOpen n x : realProjectiveAffineOpen n) :
      ℝP[n]) = realProjectiveAffineInclusion n x := by
  -- The subtype-valued inclusion has the explicit projective map as its underlying value.
  rfl

/-- Problem 2-8 (1): the map `x ↦ [x, 1]` identifies `ℝⁿ` diffeomorphically with the dense open
affine chart of `ℝPⁿ` where the last homogeneous coordinate is nonzero. -/
def realProjectiveAffineDiffeomorph :
    Diffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) (realProjectiveAffineOpen n) ∞ where
  toEquiv :=
    { toFun := realProjectiveAffineInclusionToOpen n
      invFun := realProjectiveAffineChart n
      left_inv := realProjectiveAffineInclusion_left_inv n
      right_inv := realProjectiveAffineInclusion_right_inv n }
  contMDiff_toFun := realProjectiveAffineInclusion_contMDiff n
  contMDiff_invFun := realProjectiveAffineChart_contMDiff n

/-- The forward map of `realProjectiveAffineDiffeomorph` is the affine inclusion into the
standard open subset of `ℝPⁿ`. -/
theorem realProjectiveAffineDiffeomorph_apply (x : EuclideanSpace ℝ (Fin n)) :
    realProjectiveAffineDiffeomorph n x = realProjectiveAffineInclusionToOpen n x := by
  -- The packaged diffeomorphism was defined with this map as its forward component.
  rfl

end RealProjective

section ComplexProjective

variable (n : ℕ)

/-- Helper for Problem 2-8: the complement of a coordinate hyperplane is dense in complex Euclidean
space. -/
theorem complex_coordinate_ne_zero_dense {m : ℕ} (k : Fin m) :
    Dense {u : EuclideanSpace ℂ (Fin m) | u k ≠ 0} := by
  -- Pull back the dense punctured complex line along the open coordinate projection.
  simpa [Set.preimage, Set.compl_singleton_eq] using
    (dense_compl_singleton (0 : ℂ)).preimage
      (PiLp.isOpenMap_apply (p := 2) (β := fun _ : Fin m => ℂ) k)

/-- The standard affine open subset of `ℂPⁿ` cut out by the nonvanishing of the last homogeneous
coordinate. -/
def complexProjectiveAffineOpen : TopologicalSpace.Opens (ℂP[n]) :=
  ⟨complexProjectiveChartDomain n (Fin.last n), complexProjectiveChartDomain_isOpen n (Fin.last n)⟩

/-- The map `z ↦ [z, 1]` from `ℂⁿ` into `ℂPⁿ`. -/
def complexProjectiveAffineInclusion : EuclideanSpace ℂ (Fin n) → ℂP[n] :=
  (complexProjectiveChart n (Fin.last n)).symm

/-- The map `z ↦ [z, 1]` viewed as a map into the standard affine open subset of `ℂPⁿ`. -/
def complexProjectiveAffineInclusionToOpen :
    EuclideanSpace ℂ (Fin n) → complexProjectiveAffineOpen n :=
  fun z ↦
    ⟨complexProjectiveAffineInclusion n z,
      complexProjectiveChart_symm_mem_domain n (Fin.last n) z⟩

/-- The inverse affine chart on the standard open subset of `ℂPⁿ` with last homogeneous coordinate
nonzero. -/
def complexProjectiveAffineChart : complexProjectiveAffineOpen n → EuclideanSpace ℂ (Fin n) :=
  fun z ↦ complexProjectiveChart n (Fin.last n) z.1

/-- The standard affine open subset of `ℂPⁿ` is dense. -/
theorem complexProjectiveAffineOpen_dense :
    Dense (complexProjectiveAffineOpen n : Set (ℂP[n])) := by
  let E := EuclideanSpace ℂ (Fin (n + 1))
  let s : Set { v : E // v ≠ 0 } := { v | v.1 (Fin.last n) ≠ 0 }
  let q : { v : E // v ≠ 0 } → ℂP[n] := Projectivization.mk' ℂ
  have hs_dense : Dense s := by
    -- Restrict the dense nonvanishing last-coordinate locus to the open subtype of nonzero representatives.
    simpa [s, Set.preimage, Set.compl_singleton_eq] using
      (complex_coordinate_ne_zero_dense (m := n + 1) (Fin.last n)).preimage
        ((isOpen_compl_singleton : IsOpen ({(0 : E)}ᶜ : Set E)).isOpenMap_subtype_val)
  have hq_cont : Continuous q := by
    -- The projectivization map is the quotient projection on nonzero representatives.
    simpa [q, Projectivization.mk'] using
      (continuous_quotient_mk' :
        Continuous (@Quotient.mk' { v : E // v ≠ 0 } (projectivizationSetoid ℂ E)))
  have hq_surj : Function.Surjective q := by
    intro x
    refine ⟨⟨x.rep, x.rep_nonzero⟩, ?_⟩
    simpa [q, x.mk_rep]
  have hq_dense : Dense (q '' s) := by
    -- A continuous surjection sends a dense subset of representatives to a dense set of projective classes.
    exact hq_surj.denseRange.dense_image hq_cont hs_dense
  have hs_eq : q '' s = (complexProjectiveAffineOpen n : Set (ℂP[n])) := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      -- A representative with nonzero last coordinate lands in the last affine chart domain.
      simpa [q, s, complexProjectiveAffineOpen] using
        (complexProjectiveChartDomain_mk n (Fin.last n) v.1 v.2).2 hv
    · intro hx
      refine ⟨⟨x.rep, x.rep_nonzero⟩, ?_, ?_⟩
      · -- Membership in the affine open means the chosen representative has nonzero last coordinate.
        have hmem : Projectivization.mk ℂ x.rep x.rep_nonzero ∈
            complexProjectiveChartDomain n (Fin.last n) := by
          simpa [complexProjectiveAffineOpen, x.mk_rep] using hx
        exact (complexProjectiveChartDomain_mk n (Fin.last n) x.rep x.rep_nonzero).1 hmem
      · simpa [q, x.mk_rep]
  simpa [hs_eq] using hq_dense

/-- The affine inclusion `z ↦ [z, 1]` is left-inverse to the last standard chart on `ℂPⁿ`. -/
theorem complexProjectiveAffineInclusion_left_inv :
    Function.LeftInverse (complexProjectiveAffineChart n)
      (complexProjectiveAffineInclusionToOpen n) := by
  intro z
  -- Applying the last chart to its inverse branch recovers the original affine coordinates.
  simpa [complexProjectiveAffineChart, complexProjectiveAffineInclusionToOpen,
    complexProjectiveAffineInclusion] using
    OpenPartialHomeomorph.right_inv (complexProjectiveChart n (Fin.last n)) (Set.mem_univ z)

/-- The affine inclusion `z ↦ [z, 1]` is right-inverse to the last standard chart on `ℂPⁿ`. -/
theorem complexProjectiveAffineInclusion_right_inv :
    Function.RightInverse (complexProjectiveAffineChart n)
      (complexProjectiveAffineInclusionToOpen n) := by
  intro z
  apply Subtype.ext
  -- On the last affine chart domain, the inverse branch returns the original projective point.
  simpa [complexProjectiveAffineChart, complexProjectiveAffineInclusionToOpen,
    complexProjectiveAffineInclusion] using
    OpenPartialHomeomorph.left_inv (complexProjectiveChart n (Fin.last n)) z.2

/-- The affine inclusion `z ↦ [z, 1]` is smooth as a map from `ℂⁿ` to the affine open subset of
`ℂPⁿ`. -/
theorem complexProjectiveAffineInclusion_contMDiff :
    ContMDiff
      (𝓘(ℝ, EuclideanSpace ℂ (Fin n)))
      (𝓘(ℝ, EuclideanSpace ℂ (Fin n)))
      ∞
      (complexProjectiveAffineInclusionToOpen n) := by
  have hAtlas : complexProjectiveChart n (Fin.last n) ∈
      atlas (EuclideanSpace ℂ (Fin n)) (ℂP[n]) := by
    change complexProjectiveChart n (Fin.last n) ∈ { e |
      ∃ i : Fin (n + 1), e = complexProjectiveChart n i }
    exact ⟨Fin.last n, rfl⟩
  have hMax : complexProjectiveChart n (Fin.last n) ∈
      IsManifold.maximalAtlas (𝓘(ℝ, EuclideanSpace ℂ (Fin n))) ∞ (ℂP[n]) :=
    IsManifold.subset_maximalAtlas hAtlas
  -- It suffices to forget the codomain subtype and prove smoothness of the ambient inverse chart.
  rw [← ContMDiff.subtypeVal_comp_iff (U := complexProjectiveAffineOpen n)
    (f := complexProjectiveAffineInclusionToOpen n)]
  change ContMDiff
    (𝓘(ℝ, EuclideanSpace ℂ (Fin n)))
    (𝓘(ℝ, EuclideanSpace ℂ (Fin n)))
    ∞
    (complexProjectiveAffineInclusion n)
  intro z
  -- The inverse branch of a maximal-atlas chart is smooth on the whole target, here `Set.univ`.
  simpa [complexProjectiveAffineInclusion] using
    contMDiffAt_symm_of_mem_maximalAtlas hMax (by simp : z ∈ Set.univ)

/-- The last standard affine chart on `ℂPⁿ` is smooth. -/
theorem complexProjectiveAffineChart_contMDiff :
    ContMDiff
      (𝓘(ℝ, EuclideanSpace ℂ (Fin n)))
      (𝓘(ℝ, EuclideanSpace ℂ (Fin n)))
      ∞
      (complexProjectiveAffineChart n) := by
  have hAtlas : complexProjectiveChart n (Fin.last n) ∈
      atlas (EuclideanSpace ℂ (Fin n)) (ℂP[n]) := by
    change complexProjectiveChart n (Fin.last n) ∈ { e |
      ∃ i : Fin (n + 1), e = complexProjectiveChart n i }
    exact ⟨Fin.last n, rfl⟩
  have hMax : complexProjectiveChart n (Fin.last n) ∈
      IsManifold.maximalAtlas (𝓘(ℝ, EuclideanSpace ℂ (Fin n))) ∞ (ℂP[n]) :=
    IsManifold.subset_maximalAtlas hAtlas
  intro z
  -- Restrict the ambient chart to its source subtype `complexProjectiveAffineOpen n`.
  refine (contMDiffAt_subtype_iff (U := complexProjectiveAffineOpen n)
    (f := complexProjectiveChart n (Fin.last n)) (x := z)).mpr ?_
  simpa [complexProjectiveAffineOpen] using contMDiffAt_of_mem_maximalAtlas hMax z.2

/-- The underlying map of `complexProjectiveAffineDiffeomorph` is the explicit affine inclusion
`z ↦ [z, 1]`. -/
theorem complexProjectiveAffineInclusionToOpen_coe (z : EuclideanSpace ℂ (Fin n)) :
    ((complexProjectiveAffineInclusionToOpen n z : complexProjectiveAffineOpen n) :
      ℂP[n]) = complexProjectiveAffineInclusion n z := by
  -- The subtype-valued inclusion has the explicit projective map as its underlying value.
  rfl

/-- Problem 2-8 (2): the map `z ↦ [z, 1]` identifies `ℂⁿ` diffeomorphically with the dense open
affine chart of `ℂPⁿ` where the last homogeneous coordinate is nonzero. -/
def complexProjectiveAffineDiffeomorph :
    Diffeomorph
      (𝓘(ℝ, EuclideanSpace ℂ (Fin n)))
      (𝓘(ℝ, EuclideanSpace ℂ (Fin n)))
      (EuclideanSpace ℂ (Fin n))
      (complexProjectiveAffineOpen n)
      ∞ where
  toEquiv :=
    { toFun := complexProjectiveAffineInclusionToOpen n
      invFun := complexProjectiveAffineChart n
      left_inv := complexProjectiveAffineInclusion_left_inv n
      right_inv := complexProjectiveAffineInclusion_right_inv n }
  contMDiff_toFun := complexProjectiveAffineInclusion_contMDiff n
  contMDiff_invFun := complexProjectiveAffineChart_contMDiff n

/-- The forward map of `complexProjectiveAffineDiffeomorph` is the affine inclusion into the
standard open subset of `ℂPⁿ`. -/
theorem complexProjectiveAffineDiffeomorph_apply (z : EuclideanSpace ℂ (Fin n)) :
    complexProjectiveAffineDiffeomorph n z = complexProjectiveAffineInclusionToOpen n z := by
  -- The packaged diffeomorphism was defined with this map as its forward component.
  rfl

end ComplexProjective
