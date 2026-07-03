import Mathlib
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.Geometry.Manifold.Notation
import Mathlib.Geometry.Manifold.Sheaf.Smooth
import Mathlib.Tactic.Recall
import Mathlib.Topology.Sets.OpenCover

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Remark_2_8_extra_1 (from Chap02/Sec02_08) -/
universe u

/-- Remark 2.8-extra-1: In the terminology of this text, a "function" is a map whose codomain is
`ℝ` or `EuclideanSpace ℝ (Fin k)` for some `k > 1`, while the more general words "map" and
"mapping" may refer to maps between arbitrary manifolds. -/
def is_book_function (M : Type u) {Y : Type} (f : M → Y) : Prop :=
  Y = ℝ ∨ ∃ n : ℕ, Y = EuclideanSpace ℝ (Fin (n + 2))

/-- A map is a book-function exactly when its codomain is `ℝ` or `ℝ^k` with `k > 1`. -/
theorem is_book_function_iff (M : Type u) {Y : Type} (f : M → Y) :
    is_book_function M f ↔ Y = ℝ ∨ ∃ n : ℕ, Y = EuclideanSpace ℝ (Fin (n + 2)) := sorry

/-! ### Definition_2_8_extra_2 (from Chap02/Sec02_08) -/
open scoped ContDiff Manifold

universe uE uH uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]
variable {k : ℕ} {f : M → EuclideanSpace ℝ (Fin k)}

/- Definition 2.8-extra-2: a smooth function from a smooth manifold, with or without boundary, to
`ℝ^k` is formalized by the canonical manifold smoothness predicate
`ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) ∞ f`, written on the public surface as `CMDiff ∞ f`;
the boundary case is encoded by the model with corners `I`. -/
#check (CMDiff ∞ f)

/-! ### Definition_2_8_extra_4 (from Chap02/Sec02_08) -/
open Set ChartedSpace IsManifold
open scoped Manifold ContDiff

universe uE uH uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I (∞ : ℕ∞ω) M]
variable {k : ℕ} {f : M → EuclideanSpace ℝ (Fin k)} {x x' : M}

/- Definition 2.8-extra-4: for a map from a smooth manifold to `ℝ^k`, the coordinate
representation in the preferred smooth chart centered at `x` is mathlib's
`writtenInExtChartAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) x f`, which is the conjugated map
`f ∘ (extChartAt I x).symm` on the chart image. For an arbitrary smooth chart `e` in the maximal
atlas, the corresponding coordinate representation is `f ∘ (e.extend I).symm`. -/
#check (writtenInExtChartAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) x f)

/-
Smoothness at a point is equivalent to smoothness of the coordinate representation in any smooth
chart from the maximal atlas containing that point. This is exactly
`contMDiffWithinAt_iff_source_of_mem_maximalAtlas` specialized to the Euclidean target model and
the set `univ`; since the chart representative is now a map between normed spaces, the canonical
owner for its smoothness is `ContDiffWithinAt`.
-/
#check contMDiffWithinAt_iff_source_of_mem_maximalAtlas
#check contMDiffWithinAt_iff_contDiffWithinAt

/-- A smooth map into `ℝ^k` has a smooth coordinate representation in every smooth chart from the
maximal atlas whose source contains the point. -/
theorem smooth_coordinate_representation_of_contMDiffAt
    {e : OpenPartialHomeomorph M H}
    (hf : ContMDiffAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) (∞ : ℕ∞ω) f x')
    (he : e ∈ maximalAtlas I (∞ : ℕ∞ω) M)
    (hx : x' ∈ e.source) :
    ContDiffWithinAt ℝ ∞ (f ∘ (e.extend I).symm) (range I) (e.extend I x') := by
  have hf' : ContMDiffWithinAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) (∞ : ℕ∞ω) f univ x' :=
    hf.contMDiffWithinAt
  have hcoord :
      ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) (∞ : ℕ∞ω)
        (f ∘ (e.extend I).symm) (range I) (e.extend I x') := by
    simpa [preimage_univ, univ_inter] using
      (show
        ContMDiffWithinAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) (∞ : ℕ∞ω) f univ x' ↔
          ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) (∞ : ℕ∞ω)
            (f ∘ (e.extend I).symm) ((e.extend I).symm ⁻¹' (univ : Set M) ∩ range I)
            (e.extend I x')
        from contMDiffWithinAt_iff_source_of_mem_maximalAtlas he hx).1 hf'
  exact hcoord.contDiffWithinAt

/-! ### Definition_2_8_extra_5 (from Chap02/Sec02_08) -/
open scoped ContDiff

universe uE uH uM uE' uH' uN

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {I' : ModelWithCorners ℝ E' H'}
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
variable [IsManifold I (∞ : ℕ∞ω) M] [IsManifold I' (∞ : ℕ∞ω) N]
variable {F : M → N}

/- Definition 2.8-extra-5: a smooth map between smooth manifolds, including manifolds with
boundary via the models with corners `I` and `I'`, is formalized by the canonical manifold
smoothness predicate `ContMDiff I I' ∞ F`. -/
recall ContMDiff

/-! ### Definition_2_8_extra_6 (from Chap02/Sec02_08) -/
open Set

/- Definition 2.8-extra-6 (source-facing recall): for charts `φ` on the source and `ψ` on the
target, the coordinate representation of `F` is the chart-written map `ψ ∘ F ∘ φ.symm`; when one
uses model-with-corners extensions to express smoothness, the canonical owner is
`ψ.extend J ∘ F ∘ (φ.extend I).symm`, with owner theorems
`OpenPartialHomeomorph.continuousOn_writtenInExtend_iff` and
`OpenPartialHomeomorph.contMDiffOn_writtenInExtend_iff`. -/
section

universe u𝕜 uE uE' uM uN uH uG

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {M : Type uM} [TopologicalSpace M]
variable {N : Type uN} [TopologicalSpace N]
variable {H : Type uH} [TopologicalSpace H]
variable {G : Type uG} [TopologicalSpace G]
variable {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' G}

/-- Definition 2.8-extra-6: the coordinate representation of a map `F : M → N` in charts `φ`
and `ψ` is the chart-written map `ψ ∘ F ∘ φ.symm`. -/
abbrev coordinate_representation (F : M → N) (φ : OpenPartialHomeomorph M H)
    (ψ : OpenPartialHomeomorph N G) : H → G :=
  ψ ∘ F ∘ φ.symm

/-- Helper for Definition 2.8-extra-6: on the overlap of the chart domains, evaluating the
coordinate representation at the chart coordinate `φ x` recovers `ψ (F x)`. -/
lemma coordinate_representation_apply_chart
    (F : M → N) (φ : OpenPartialHomeomorph M H) (ψ : OpenPartialHomeomorph N G)
    {x : M} (hx : x ∈ φ.source ∩ F ⁻¹' ψ.source) :
    coordinate_representation F φ ψ (φ x) = ψ (F x) := by
  -- Unfold the conjugated map and use that `φ.symm` inverts `φ` on the chart source.
  rcases hx with ⟨hxφ, _⟩
  simp [coordinate_representation, φ.left_inv hxφ]

/-- Helper for Definition 2.8-extra-6: the coordinate representation sends the chart image of
`φ.source ∩ F ⁻¹' ψ.source` into the chart image `ψ '' ψ.source`. -/
lemma coordinate_representation_mapsTo_image
    (F : M → N) (φ : OpenPartialHomeomorph M H) (ψ : OpenPartialHomeomorph N G) :
    MapsTo (coordinate_representation F φ ψ)
      (φ '' (φ.source ∩ F ⁻¹' ψ.source)) (ψ '' ψ.source) := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  -- Rewrite the written-in-coordinates value back to the concrete point `F x`.
  refine ⟨F x, hx.2, ?_⟩
  simpa using (coordinate_representation_apply_chart F φ ψ hx).symm

/-- Helper for Definition 2.8-extra-6: rewriting the codomain image as the chart target gives the
usual `MapsTo` formulation for the coordinate representation. -/
lemma coordinate_representation_mapsTo_target
    (F : M → N) (φ : OpenPartialHomeomorph M H) (ψ : OpenPartialHomeomorph N G) :
    MapsTo (coordinate_representation F φ ψ)
      (φ '' (φ.source ∩ F ⁻¹' ψ.source)) ψ.target := by
  intro y hy
  -- First land in `ψ '' ψ.source`, then rewrite that image as the chart target.
  have hy' := coordinate_representation_mapsTo_image F φ ψ hy
  simpa [ψ.image_source_eq_target] using hy'

/-- Helper for Definition 2.8-extra-6: the extended coordinate representation used by the
manifold smoothness API sends the same overlap to the extended target chart. -/
lemma extended_coordinate_representation_mapsTo
    (F : M → N) (φ : OpenPartialHomeomorph M H) (ψ : OpenPartialHomeomorph N G) :
    MapsTo (ψ.extend J ∘ F ∘ (φ.extend I).symm)
      ((φ.extend I) '' (φ.source ∩ F ⁻¹' ψ.source)) (ψ.extend J).target := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  -- Route correction: rewrite through the extended source inverse before applying the target chart.
  have hFx : F x ∈ (ψ.extend J).source := by
    simpa [ψ.extend_source (I := J)] using hx.2
  have hxchart : φ.symm (φ x) = x :=
    φ.left_inv hx.1
  -- After reducing the source-side extension, the target-side extension maps into its target.
  simpa [Function.comp_apply, hxchart] using
    (ψ.extend J).mapsTo hFx

end

/-! ### Remark_2_8_extra_7 (from Chap02/Sec02_08) -/
open scoped ContDiff

universe uE uH uM uE' uH' uN

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {I' : ModelWithCorners ℝ E' H'}
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
variable [IsManifold I (∞ : ℕ∞ω) M] [IsManifold I' (∞ : ℕ∞ω) N]
variable {F : M → N}

/- Remark 2.8-extra-7: the ambient topological-manifold data is carried by `ChartedSpace`, charts
are `OpenPartialHomeomorph`s, and smoothness of a map between manifolds with corners is expressed
by the canonical predicate `ContMDiff I I' ∞ F`. -/
recall ChartedSpace
recall OpenPartialHomeomorph
#check (ContMDiff I I' (∞ : ℕ∞ω) F)

/-! ### Corollary_2_8 (from Chap02/Sec02_08) -/
open CategoryTheory
open TopologicalSpace
open scoped Manifold ContDiff

universe u𝕜 uE uH uM uE' uH' uA

variable
  {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type uH} [TopologicalSpace H]
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type uH'} [TopologicalSpace H']
  {N : Type uM} [TopologicalSpace N] [ChartedSpace H' N]
  {I : ModelWithCorners 𝕜 E H}
  {I' : ModelWithCorners 𝕜 E' H'}

/-- Corollary 2.8 (Gluing Lemma for Smooth Maps): if smooth local maps on an open cover of `M`
agree on pairwise overlaps, then there is a unique global smooth map whose restrictions are the
given local maps. The owner abstraction is the sheaf `smoothSheaf I I' M N`; this theorem is the
source-facing gluing bridge specialized to global sections. -/
theorem gluing_lemma_for_smooth_maps
    {A : Type uA} {U : A → Opens M} {f : ∀ a, U a → N}
    (hU : IsOpenCover U)
    (hf : ∀ a, ContMDiff I I' ∞ (f a))
    (hcompat : ∀ a b (x : ↥((U a) ⊓ (U b))), f a ⟨x, x.2.1⟩ = f b ⟨x, x.2.2⟩) :
    ∃! F : C^∞⟮I, M; I', N⟯, ∀ a (x : U a), F x = f a x := by
  let 𝒮 := smoothSheaf I I' M N
  let sf : ∀ a, 𝒮.presheaf.obj (Opposite.op (U a)) := fun a ↦ ⟨f a, hf a⟩
  have hsf : TopCat.Presheaf.IsCompatible 𝒮.1 U sf := by
    intro a b
    apply ContMDiffMap.ext
    intro x
    exact hcompat a b x
  have hcover : (⊤ : Opens M) ≤ iSup U := by
    simp [hU.iSup_eq_top]
  obtain ⟨gl, hgl, -⟩ :=
    𝒮.existsUnique_gluing' U ⊤ (fun _ ↦ homOfLE le_top) hcover sf hsf
  let toTop : M → (⊤ : Opens M) := fun x ↦ ⟨x, by trivial⟩
  have htoTop : ContMDiff I I ∞ toTop := by
    have h_id : ContMDiff I I ∞ (Subtype.val ∘ toTop) := by
      change ContMDiff I I ∞ (fun x : M ↦ x)
      simpa using (contMDiff_id : ContMDiff I I ∞ (fun x : M ↦ x))
    exact (ContMDiff.subtypeVal_comp_iff (⊤ : Opens M) toTop).1 h_id
  let F : C^∞⟮I, M; I', N⟯ := ⟨fun x ↦ gl (toTop x), (smoothSheaf.contMDiff_section gl).comp htoTop⟩
  have hF : ∀ a (x : U a), F x = f a x := by
    intro a x
    simpa [F, sf, toTop] using
      congrArg (fun s : 𝒮.presheaf.obj (Opposite.op (U a)) ↦ s x) (hgl a)
  refine ⟨F, hF, ?_⟩
  intro G hG
  ext x
  rcases hU.exists_mem x with ⟨a, ha⟩
  exact (hG a ⟨x, ha⟩).trans (hF a ⟨x, ha⟩).symm

/-! ### Problem_2_8 (from Chap02/Sec02_12) -/
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
