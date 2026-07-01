import Mathlib
import SmoothManifoldsLee.Chap01.Sec01.Definition_1_extra_1
import SmoothManifoldsLee.Chap04.Sec04_25.Proposition_4_28
import SmoothManifoldsLee.Chap04.Sec04_23.Theorem_4_12
import SmoothManifoldsLee.Chap05.Sec05_29.Definition_5_29_extra_1
import SmoothManifoldsLee.Chap05.Sec05_30.Corollary_5_13

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

section LocalLevelSetCriterion

universe uE uH uM

open Manifold

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]

/-- Helper for Proposition 5.16: the last `n - k` coordinates of `ℝ^n` are indexed by the tail
slots obtained by shifting `Fin (n - k)` by `k`. -/
def euclidean_tail_coordinate {n k : ℕ} (hk : k ≤ n) (i : Fin (n - k)) : Fin n :=
  Fin.cast (Nat.add_sub_of_le hk) (i.natAdd k)

/-- Helper for Proposition 5.16: the tail-coordinate projection from `ℝ^n` to `ℝ^(n-k)`. -/
def euclidean_tail_projection {n k : ℕ} (hk : k ≤ n) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n - k)) :=
  fun x ↦ WithLp.toLp 2 fun i ↦ x (euclidean_tail_coordinate hk i)

/-- Helper for Proposition 5.16: the projection onto the first `k` coordinates of `ℝ^n`. -/
def euclidean_head_projection {n k : ℕ} (hk : k ≤ n) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin k) :=
  fun x ↦ WithLp.toLp 2 fun i ↦ x (Fin.castLE hk i)

/-- Helper for Proposition 5.16: the head-coordinate projection is continuous. -/
theorem continuous_euclidean_head_projection {n k : ℕ} (hk : k ≤ n) :
    Continuous (euclidean_head_projection hk) := by
  -- The head projection is a coordinatewise linear map on Euclidean space.
  have hcoord :
      Continuous fun x : EuclideanSpace ℝ (Fin n) =>
        fun i : Fin k ↦ x (Fin.castLE hk i) :=
    continuous_pi fun i ↦
      PiLp.continuous_apply (p := 2) (β := fun _ : Fin n ↦ ℝ) (Fin.castLE hk i)
  simpa [euclidean_head_projection] using
    (PiLp.continuous_toLp 2 (fun _ : Fin k ↦ ℝ)).comp hcoord

/-- Helper for Proposition 5.16: reinsert a tail vector into `ℝ^n` by filling the first `k`
coordinates with `0`. -/
def euclidean_zero_prefix_inclusion {n k : ℕ} (hk : k ≤ n) :
    EuclideanSpace ℝ (Fin (n - k)) → EuclideanSpace ℝ (Fin n) :=
  fun y ↦
    WithLp.toLp 2 <|
      (Fin.append (fun _ : Fin k ↦ (0 : ℝ)) y) ∘ Fin.cast (Nat.add_sub_of_le hk).symm

/-- Helper for Proposition 5.16: the zero-prefix inclusion is a right inverse to the
tail-coordinate projection. -/
theorem euclidean_tail_projection_zero_prefix_inclusion {n k : ℕ}
    (hk : k ≤ n) (y : EuclideanSpace ℝ (Fin (n - k))) :
    euclidean_tail_projection hk (euclidean_zero_prefix_inclusion hk y) = y := by
  -- Evaluating the tail projection on the inserted vector lands in the appended tail block.
  ext i
  change
    (Fin.append (fun _ : Fin k ↦ (0 : ℝ)) y)
        (Fin.cast (Nat.add_sub_of_le hk).symm
          (Fin.cast (Nat.add_sub_of_le hk) (i.natAdd k))) = y i
  rw [(Fin.leftInverse_cast (Nat.add_sub_of_le hk)) (i.natAdd k)]
  simp

/-- Helper for Proposition 5.16: the tail-coordinate projection is onto. -/
theorem euclidean_tail_projection_surjective {n k : ℕ} (hk : k ≤ n) :
    Function.Surjective (euclidean_tail_projection hk) := by
  intro y
  refine ⟨euclidean_zero_prefix_inclusion hk y, ?_⟩
  exact euclidean_tail_projection_zero_prefix_inclusion hk y

/-- Helper for Proposition 5.16: the tail-coordinate projection on `ℝ^n` is a smooth
submersion. -/
theorem euclidean_tail_projection_isSmoothSubmersion {n k : ℕ} (hk : k ≤ n) :
    IsSmoothSubmersion (𝓡 n) (𝓡 (n - k)) (euclidean_tail_projection hk) := by
  -- Route correction: isolate the fixed Euclidean model submersion before mixing it with the
  -- local immersion normal form coming from the ambient manifold.
  let L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n - k)) :=
    { toFun := euclidean_tail_projection hk
      map_add' := by
        intro x y
        ext i
        simp [euclidean_tail_projection]
      map_smul' := by
        intro c x
        ext i
        simp [euclidean_tail_projection]
      cont := by
        have hcoord :
            Continuous fun x : EuclideanSpace ℝ (Fin n) =>
              fun i : Fin (n - k) ↦ x (euclidean_tail_coordinate hk i) :=
          continuous_pi fun i ↦
            PiLp.continuous_apply (p := 2) (β := fun _ : Fin n ↦ ℝ)
              (euclidean_tail_coordinate hk i)
        simpa [euclidean_tail_projection] using
          (PiLp.continuous_toLp 2 (fun _ : Fin (n - k) ↦ ℝ)).comp hcoord }
  refine ⟨?_, ?_⟩
  · -- The tail projection is linear, hence smooth on Euclidean model spaces.
    simpa [L] using
      (L.contMDiff : ContMDiff (𝓡 n) (𝓡 (n - k)) ∞ L)
  · intro x
    rw [mfderiv_eq_fderiv]
    have hderiv :
        fderiv ℝ (euclidean_tail_projection hk) x = L := by
      simpa [L, euclidean_tail_projection] using (L.hasFDerivAt (x := x)).fderiv
    rw [hderiv]
    simpa [L] using euclidean_tail_projection_surjective hk

/-- Helper for Proposition 5.16: the immersion normal form `rank_normal_form k n k` has zero tail
coordinates, so the fixed tail projection kills it. -/
theorem euclidean_tail_projection_rank_normal_form_zero {n k : ℕ}
    (hk : k ≤ n) (x : EuclideanSpace ℝ (Fin k)) :
    euclidean_tail_projection hk (rank_normal_form k n k x) = 0 := by
  -- Every tail coordinate lies strictly beyond the first `k` slots, where the normal form for an
  -- immersion already vanishes.
  ext i
  change rank_normal_form k n k x (euclidean_tail_coordinate hk i) = 0
  have hnot : ¬ (euclidean_tail_coordinate hk i).1 < k := by
    change ¬ (k + i.1 < k)
    omega
  simp [euclidean_tail_coordinate, rank_normal_form]

/-- Helper for Proposition 5.16: the rank-`k` normal form preserves the first `k` coordinates. -/
theorem euclidean_head_projection_rank_normal_form {n k : ℕ}
    (hk : k ≤ n) (x : EuclideanSpace ℝ (Fin k)) :
    euclidean_head_projection hk (rank_normal_form k n k x) = x := by
  -- On the first `k` slots, the normal form is literally the identity.
  ext i
  simpa [euclidean_head_projection] using
    (rank_normal_form_apply_of_lt (i := Fin.castLE hk i) (x := x) i.2 i.2)

/-- Helper for Proposition 5.16: a vector in `ℝ^n` whose tail coordinates vanish is determined by
its first `k` coordinates via the rank normal form. -/
theorem rank_normal_form_eq_of_tail_projection_eq_zero {n k : ℕ}
    (hk : k ≤ n) {y : EuclideanSpace ℝ (Fin n)}
    (hy : euclidean_tail_projection hk y = 0) :
    y = rank_normal_form k n k (euclidean_head_projection hk y) := by
  -- Split coordinates into the first `k` slots and the tail slots cut out by the tail
  -- projection.
  ext i
  rcases lt_or_ge i.1 k with hi | hi
  · calc
      y i = euclidean_head_projection hk y ⟨i.1, hi⟩ := by
        simp [euclidean_head_projection]
      _ = rank_normal_form k n k (euclidean_head_projection hk y) i := by
        symm
        exact rank_normal_form_apply_of_lt (i := i) (x := euclidean_head_projection hk y) hi hi
  · let j : Fin (n - k) := ⟨i.1 - k, by omega⟩
    have hj : euclidean_tail_coordinate hk j = i := by
      apply Fin.ext
      simp [euclidean_tail_coordinate, j]
      omega
    have hyi : y i = 0 := by
      have hyj := congrArg (fun v : EuclideanSpace ℝ (Fin (n - k)) => v j) hy
      simpa [euclidean_tail_projection, hj] using hyj
    have hnot : ¬ i.1 < k := Nat.not_lt_of_ge hi
    calc
      y i = 0 := hyi
      _ = rank_normal_form k n k (euclidean_head_projection hk y) i := by
        simp [rank_normal_form, hnot]

/-- Helper for Proposition 5.16: a Euclidean `k`-slice is exactly the fiber of the tail-coordinate
projection over the prescribed tail value. -/
theorem euclideanSlice_eq_tail_projection_fiber {n k : ℕ}
    (U : Set (EuclideanSpace ℝ (Fin n))) (hk : k ≤ n) (c : Fin (n - k) → ℝ) :
    Set.euclideanSlice U k hk c =
      U ∩ euclidean_tail_projection hk ⁻¹' {WithLp.toLp 2 c} := by
  -- Membership in a Euclidean slice is the ambient target condition together with the tail
  -- coordinate equations, and those equations are exactly equality of tail projections.
  ext x
  constructor
  · intro hx
    refine ⟨hx.1, ?_⟩
    change euclidean_tail_projection hk x = WithLp.toLp 2 c
    ext i
    simpa [euclidean_tail_projection] using hx.2 i
  · intro hx
    refine ⟨hx.1, ?_⟩
    have hEq : euclidean_tail_projection hk x = WithLp.toLp 2 c := by
      simpa using hx.2
    intro i
    have hi := congrArg (fun v : EuclideanSpace ℝ (Fin (n - k)) => v i) hEq
    simpa [euclidean_tail_projection] using hi

/-- Helper for Proposition 5.16: on an open neighborhood `U`, a local level-set description by a
smooth submersion produces an embedded `k`-submanifold structure on the patch
`{x : U | (x : M) ∈ S}`. -/
lemma local_submersion_level_patch_embedded_in_opens
    (S : Set M) (k : ℕ) (hk : k ≤ Module.finrank ℝ E)
    {U : TopologicalSpace.Opens M}
    {Φ : U → EuclideanSpace ℝ (Fin (Module.finrank ℝ E - k))}
    (hΦ : IsSmoothSubmersion I (𝓡 (Module.finrank ℝ E - k)) Φ)
    (c : EuclideanSpace ℝ (Fin (Module.finrank ℝ E - k)))
    (hLevel : {x : U | (x : M) ∈ S} = Φ ⁻¹' {c}) :
    ∃ cs : ChartedSpace (EuclideanSpace ℝ (Fin k)) {x : U | (x : M) ∈ S},
      ∃ hs : IsManifold (𝓡 k) ∞ {x : U | (x : M) ∈ S},
        let _ : ChartedSpace (EuclideanSpace ℝ (Fin k)) {x : U | (x : M) ∈ S} := cs
        let _ : IsManifold (𝓡 k) ∞ {x : U | (x : M) ∈ S} := hs
        IsEmbeddedSubmanifold I (𝓡 k) {x : U | (x : M) ∈ S} := by
  -- TODO: specialize Corollary 5.13 and then transport its canonical fiber model
  -- `Φ ⁻¹' {c}` from dimension `finrank E - (finrank E - k)` to the explicit `Fin k` model.
  sorry

/-- Helper for Proposition 5.16: the local level-set hypothesis yields an embedded
`k`-submanifold structure on each open patch cut out inside the corresponding neighborhood. -/
lemma locally_level_set_patches_are_embedded
    (S : Set M) (k : ℕ) (hk : k ≤ Module.finrank ℝ E)
    (hLocal :
      ∀ p ∈ S,
        ∃ U : TopologicalSpace.Opens M, p ∈ U ∧
          ∃ Φ : U → EuclideanSpace ℝ (Fin (Module.finrank ℝ E - k)),
            IsSmoothSubmersion I (𝓡 (Module.finrank ℝ E - k)) Φ ∧
              ∃ c : EuclideanSpace ℝ (Fin (Module.finrank ℝ E - k)),
                {x : U | (x : M) ∈ S} = Φ ⁻¹' {c}) :
    ∀ p ∈ S,
      ∃ U : TopologicalSpace.Opens M, p ∈ U ∧
        ∃ cs : ChartedSpace (EuclideanSpace ℝ (Fin k)) {x : U | (x : M) ∈ S},
          ∃ hs : IsManifold (𝓡 k) ∞ {x : U | (x : M) ∈ S},
            let _ : ChartedSpace (EuclideanSpace ℝ (Fin k)) {x : U | (x : M) ∈ S} := cs
            let _ : IsManifold (𝓡 k) ∞ {x : U | (x : M) ∈ S} := hs
            IsEmbeddedSubmanifold I (𝓡 k) {x : U | (x : M) ∈ S} := by
  intro p hp
  rcases hLocal p hp with ⟨U, hpU, Φ, hΦ, c, hLevel⟩
  rcases local_submersion_level_patch_embedded_in_opens
      (S := S) (k := k) hk hΦ c hLevel with ⟨cs, hs, hEmb⟩
  -- The reverse direction is now reduced to gluing these embedded open patches on the subtype `S`.
  exact ⟨U, hpU, cs, hs, hEmb⟩

/-- Helper for Proposition 5.16: an open subset of the subtype `S` is cut out by an ambient open
set in `M`. This is the small topology bridge used to turn a subtype chart source into an ambient
open neighborhood in the forward direction. -/
lemma subtype_open_eq_preimage_ambient_open_local
    {S : Set M} {U : Set S} (hU : IsOpen U) :
    ∃ W : Set M, IsOpen W ∧ U = {y : S | y.1 ∈ W} := by
  -- The subtype topology on `S` is induced from `M`, so every open set on `S` is the pullback of
  -- an ambient open set along the inclusion `Subtype.val`.
  rcases
      (Topology.IsInducing.subtypeVal : Topology.IsInducing ((↑) : S → M)).isOpen_iff.1 hU with
    ⟨W, hW, hEq⟩
  refine ⟨W, hW, ?_⟩
  simpa using hEq.symm

/-- Helper for Proposition 5.16: the open patch of the global subtype `S` cut out by an ambient
open neighborhood `U`. -/
private noncomputable def subtype_patch_from_ambient_open
    (S : Set M) (U : TopologicalSpace.Opens M) :
    TopologicalSpace.Opens S :=
  ⟨{y : S | y.1 ∈ U}, by
    simpa [Set.preimage, Function.comp] using U.2.preimage continuous_subtype_val⟩

/-- Helper for Proposition 5.16: a chart on the local subtype patch `{x : U | (x : M) ∈ S}`
transports to a canonical chart on the global subtype `S` through the open-subtype inclusion. -/
noncomputable def embedded_patch_chartAt
    (S : Set M) (k : ℕ) {U : TopologicalSpace.Opens M}
    {cs : ChartedSpace (EuclideanSpace ℝ (Fin k)) {x : U | (x : M) ∈ S}}
    (x : S) (hxU : x.1 ∈ U) : OpenPartialHomeomorph S (EuclideanSpace ℝ (Fin k)) :=
  -- TODO: the current `OpenPartialHomeomorph` transport API for open subtype patches on `S`
  -- needs a small typing bridge before this chart can be written as a term.
  sorry

/-- Helper for Proposition 5.16: the transported local patch chart is defined at its base point in
the global subtype `S`. -/
lemma embedded_patch_chartAt_mem_source
    (S : Set M) (k : ℕ) {U : TopologicalSpace.Opens M}
    {cs : ChartedSpace (EuclideanSpace ℝ (Fin k)) {x : U | (x : M) ∈ S}}
    (x : S) (hxU : x.1 ∈ U) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin k)) {x : U | (x : M) ∈ S} := cs
    x ∈ (embedded_patch_chartAt (S := S) (k := k) (cs := cs) x hxU).source := by
  -- TODO: once `embedded_patch_chartAt` is expressed through the current subtype-patch transport,
  -- this reduces to the center-point membership of the transported local chart.
  sorry

/-- Helper for Proposition 5.16: local embedded patch charts already package to a topological
`k`-manifold structure on the global subtype `S`. This isolates the remaining converse-direction
blocker to smooth compatibility of the transported atlas and smoothness of `Subtype.val`. -/
lemma local_embedded_patches_have_topological_manifold_structure
    (S : Set M) (k : ℕ)
    (hPatch :
      ∀ p ∈ S,
        ∃ U : TopologicalSpace.Opens M, p ∈ U ∧
          ∃ cs : ChartedSpace (EuclideanSpace ℝ (Fin k)) {x : U | (x : M) ∈ S},
            ∃ hs : IsManifold (𝓡 k) ∞ {x : U | (x : M) ∈ S},
              let _ : ChartedSpace (EuclideanSpace ℝ (Fin k)) {x : U | (x : M) ∈ S} := cs
              let _ : IsManifold (𝓡 k) ∞ {x : U | (x : M) ∈ S} := hs
              IsEmbeddedSubmanifold I (𝓡 k) {x : U | (x : M) ∈ S}) :
    ∃ tm : TopologicalManifold k S,
      let _ : TopologicalManifold k S := tm
      IsManifold (𝓡 k) 0 S ∧ BoundarylessManifold (𝓡 k) S := by
  classical
  have hPointedCharts :
      ∀ x : S, ∃ e : OpenPartialHomeomorph S (EuclideanSpace ℝ (Fin k)), x ∈ e.source := by
    intro x
    rcases hPatch x.1 x.2 with ⟨U, hxU, cs, hs, hEmb⟩
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin k)) {y : U | (y : M) ∈ S} := cs
    let _ : IsManifold (𝓡 k) ∞ {y : U | (y : M) ∈ S} := hs
    -- Transport the chosen local patch chart to a fixed chart on the global subtype `S`.
    refine ⟨embedded_patch_chartAt (S := S) (k := k) (cs := cs) x hxU, ?_⟩
    exact embedded_patch_chartAt_mem_source (S := S) (k := k) (cs := cs) x hxU
  -- TODO: rebuild the charted-space term with the current `choose` output and the updated
  -- transported patch chart API.
  sorry

/-- Helper for Proposition 5.16: an embedded `k`-submanifold has, at each of its points, a local
defining map to `ℝ^(m-k)` that is a smooth submersion. -/
lemma embedded_submanifold_has_local_submersion_model
    (S : Set M) (k : ℕ) (hk : k ≤ Module.finrank ℝ E)
    (hEmb :
      ∃ tm : TopologicalManifold k S,
        let _ : TopologicalManifold k S := tm
        ∃ hs : IsManifold (𝓡 k) ∞ S,
          let _ : IsManifold (𝓡 k) ∞ S := hs
          IsEmbeddedSubmanifold I (𝓡 k) S) :
    ∀ p ∈ S,
      ∃ U : TopologicalSpace.Opens M, p ∈ U ∧
        ∃ Φ : U → EuclideanSpace ℝ (Fin (Module.finrank ℝ E - k)),
          IsSmoothSubmersion I (𝓡 (Module.finrank ℝ E - k)) Φ ∧
            ∃ c : EuclideanSpace ℝ (Fin (Module.finrank ℝ E - k)),
              {x : U | (x : M) ∈ S} = Φ ⁻¹' {c} := by
  -- Route correction: the source-faithful forward proof still needs a current general-manifold
  -- local inclusion normal form whose chart objects live over the ambient model `I`, not only the
  -- Euclidean-source Chapter 4 version.
  sorry

/-- Helper for Proposition 5.16: if every point of `S` lies in an open patch that already carries
an embedded `k`-submanifold structure, then these local subtype charts glue to a global embedded
`k`-submanifold structure on `S`. -/
lemma local_embedded_patches_yield_embedded_submanifold
    (S : Set M) (k : ℕ)
    (hPatch :
      ∀ p ∈ S,
        ∃ U : TopologicalSpace.Opens M, p ∈ U ∧
          ∃ cs : ChartedSpace (EuclideanSpace ℝ (Fin k)) {x : U | (x : M) ∈ S},
            ∃ hs : IsManifold (𝓡 k) ∞ {x : U | (x : M) ∈ S},
              let _ : ChartedSpace (EuclideanSpace ℝ (Fin k)) {x : U | (x : M) ∈ S} := cs
              let _ : IsManifold (𝓡 k) ∞ {x : U | (x : M) ∈ S} := hs
              IsEmbeddedSubmanifold I (𝓡 k) {x : U | (x : M) ∈ S}) :
    ∃ tm : TopologicalManifold k S,
        let _ : TopologicalManifold k S := tm
      ∃ hs : IsManifold (𝓡 k) ∞ S,
        let _ : IsManifold (𝓡 k) ∞ S := hs
        IsEmbeddedSubmanifold I (𝓡 k) S := by
  rcases local_embedded_patches_have_topological_manifold_structure
      (S := S) (k := k) hPatch with ⟨tm, hTop⟩
  let _ : TopologicalManifold k S := tm
  have hTopological : IsManifold (𝓡 k) 0 S := hTop.1
  have hBoundaryless : BoundarylessManifold (𝓡 k) S := hTop.2
  let _hTopological := hTopological
  let _hBoundaryless := hBoundaryless
  -- TODO: upgrade the chosen transported atlas from `C^0` to `C^∞`, then use the local patch
  -- embeddings to prove that `Subtype.val : S → M` is a smooth immersion. The topological and
  -- boundaryless owners are now fixed, so the first remaining blocker is exactly the smooth atlas
  -- compatibility argument.
  sorry

/-- Proposition 5.16: a subset `S` of a smooth `m`-manifold is an embedded `k`-submanifold if and
only if every point of `S` has a neighborhood on which `S` is a level set of a smooth submersion
to `ℝ^(m - k)`. In Lean, the local condition is stated using the chapter-level owner
`Manifold.IsSmoothSubmersion` on the open neighborhood, together with the local level-set
equation. -/
theorem embedded_submanifold_iff_locally_level_set_of_smooth_submersion
    (S : Set M) (k : ℕ) (hk : k ≤ Module.finrank ℝ E) :
    let r : ℕ := Module.finrank ℝ E - k
    (∃ tm : TopologicalManifold k S,
      let _ : TopologicalManifold k S := tm
      ∃ hs : IsManifold (𝓡 k) ∞ S,
        let _ : IsManifold (𝓡 k) ∞ S := hs
        IsEmbeddedSubmanifold I (𝓡 k) S) ↔
      ∀ p ∈ S,
        ∃ U : TopologicalSpace.Opens M, p ∈ U ∧
          ∃ Φ : U → EuclideanSpace ℝ (Fin r),
            IsSmoothSubmersion I (𝓡 r) Φ ∧
              ∃ c : EuclideanSpace ℝ (Fin r),
                {x : U | (x : M) ∈ S} = Φ ⁻¹' {c} := by
  dsimp
  constructor
  · intro hEmb
    -- Route correction: the forward implication should be proved from the generic immersion normal
    -- form for the subtype inclusion, not by forcing `Theorem_5_8` through a self-model detour.
    exact embedded_submanifold_has_local_submersion_model (S := S) (k := k) hk hEmb
  · intro hLocal
    have hPatch :
        ∀ p ∈ S,
          ∃ U : TopologicalSpace.Opens M, p ∈ U ∧
            ∃ cs : ChartedSpace (EuclideanSpace ℝ (Fin k)) {x : U | (x : M) ∈ S},
              ∃ hs : IsManifold (𝓡 k) ∞ {x : U | (x : M) ∈ S},
                let _ : ChartedSpace (EuclideanSpace ℝ (Fin k)) {x : U | (x : M) ∈ S} := cs
                let _ : IsManifold (𝓡 k) ∞ {x : U | (x : M) ∈ S} := hs
                IsEmbeddedSubmanifold I (𝓡 k) {x : U | (x : M) ∈ S} :=
      locally_level_set_patches_are_embedded (S := S) (k := k) hk hLocal
    -- The converse is reduced to the remaining gluing step for the local embedded patches on `S`.
    exact local_embedded_patches_yield_embedded_submanifold (S := S) (k := k) hPatch

end LocalLevelSetCriterion
