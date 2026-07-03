import Mathlib
import SmoothManifolds_Lee_2012.Chap01.Sec01.Definition_1_extra_1
import SmoothManifolds_Lee_2012.Chap01.Sec01.Definition_1_extra_2
import SmoothManifolds_Lee_2012.Chap05.Sec05_28.Definition_5_28_extra_1
import SmoothManifolds_Lee_2012.Chap05.Sec05_29.Definition_5_29_extra_1
import SmoothManifolds_Lee_2012.Chap05.Sec05_29.Theorem_5_8.LocalNormalFormAPI

open scoped Manifold

universe u

open LocalNormalFormAPI Set ChartedSpace

section

variable {n k : ℕ} {M : Type u} [TopologicalSpace M]
variable [TopologicalManifold n M]
variable [IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) M]

/-- Helper for Theorem 5.8: the empty subtype carries the canonical boundaryless topological
`k`-manifold structure. -/
theorem empty_subtype_topological_manifold_structure :
    ∃ tm : TopologicalManifold k (∅ : Set M),
      let _ : TopologicalManifold k (∅ : Set M) := tm
      IsManifold (𝓡 k) (0 : WithTop ℕ∞) (∅ : Set M) ∧
        BoundarylessManifold (𝓡 k) (∅ : Set M) := by
  letI : IsEmpty (∅ : Set M) := inferInstance
  letI : ChartedSpace (EuclideanSpace ℝ (Fin k)) (∅ : Set M) := ChartedSpace.empty _ _
  -- The empty subtype inherits the empty atlas modelled on `ℝ^k`.
  let tm : TopologicalManifold k (∅ : Set M) := topologicalManifoldOfChartedSpace k (∅ : Set M)
  refine ⟨tm, ?_⟩
  letI : TopologicalManifold k (∅ : Set M) := tm
  constructor
  · -- Every charted space is automatically a `C^0` manifold.
    infer_instance
  · -- The empty manifold is boundaryless for every model with corners.
    exact ⟨fun x ↦ (IsEmpty.false x).elim⟩

/-- Helper for Theorem 5.8: the empty subset is an embedded `k`-submanifold for the trivial empty
smooth structure. -/
theorem empty_subtype_embedded_submanifold_structure :
    ∃ tm : TopologicalManifold k (∅ : Set M),
      let _ : TopologicalManifold k (∅ : Set M) := tm
      ∃ hs : IsManifold (𝓡 k) (⊤ : WithTop ℕ∞) (∅ : Set M),
        let _ : IsManifold (𝓡 k) (⊤ : WithTop ℕ∞) (∅ : Set M) := hs
        IsEmbeddedSubmanifold (𝓡 n) (𝓡 k) (∅ : Set M) := by
  letI : IsEmpty (∅ : Set M) := inferInstance
  letI : ChartedSpace (EuclideanSpace ℝ (Fin k)) (∅ : Set M) := ChartedSpace.empty _ _
  -- Start from the canonical empty atlas on the subtype.
  let tm : TopologicalManifold k (∅ : Set M) := topologicalManifoldOfChartedSpace k (∅ : Set M)
  refine ⟨tm, ?_⟩
  letI : TopologicalManifold k (∅ : Set M) := tm
  -- Smooth compatibility is vacuous because every chart transition is defined on the empty set.
  let hs : IsManifold (𝓡 k) (⊤ : WithTop ℕ∞) (∅ : Set M) := by
    refine isManifold_of_contDiffOn (I := 𝓡 k) (n := (⊤ : WithTop ℕ∞))
      (M := (∅ : Set M)) ?_
    intro e e' he he'
    have hFalse : False := by
      change e ∈ (∅ : Set (OpenPartialHomeomorph (∅ : Set M) (EuclideanSpace ℝ (Fin k)))) at he
      simp at he
    exact False.elim hFalse
  refine ⟨hs, ?_⟩
  letI : IsManifold (𝓡 k) (⊤ : WithTop ℕ∞) (∅ : Set M) := hs
  -- The empty subtype inclusion is the canonical empty smooth embedding.
  refine
    { toBoundarylessManifold := ⟨fun x ↦ (IsEmpty.false x).elim⟩
      isSmoothEmbedding_subtype_val := ?_ }
  refine ⟨?_, ⟨Topology.IsInducing.subtypeVal, Subtype.val_injective⟩⟩
  exact ⟨PUnit, inferInstance, inferInstance, fun x ↦ False.elim x.2⟩

/-- Helper for Theorem 5.8: an embedded `k`-dimensional subtype of an `n`-manifold can only occur
when `k ≤ n`. -/
theorem embedded_submanifold_dimension_le
    (S : Set M) [TopologicalManifold k S]
    [IsManifold (𝓡 k) (⊤ : WithTop ℕ∞) S]
    (hS_nonempty : S.Nonempty)
    (hEmb : IsEmbeddedSubmanifold (𝓡 n) (𝓡 k) S) :
    k ≤ n := by
  let _ : IsEmbeddedSubmanifold (𝓡 n) (𝓡 k) S := hEmb
  rcases hS_nonempty with ⟨p, hp⟩
  let pS : S := ⟨p, hp⟩
  let hImm :
      Manifold.IsImmersionAt (𝓡 k) (𝓡 n) (⊤ : WithTop ℕ∞)
        (Subtype.val : S → M) pS :=
    hEmb.isSmoothEmbedding_subtype_val.isImmersion.isImmersionAt pS
  haveI : FiniteDimensional ℝ (EuclideanSpace ℝ (Fin k) × hImm.complement) :=
    FiniteDimensional.of_injective hImm.equiv.toLinearMap hImm.equiv.injective
  -- The complement chosen by the immersion data is finite-dimensional because it sits inside the
  -- finite-dimensional product identified with `ℝ^n`.
  haveI : FiniteDimensional ℝ hImm.complement :=
    FiniteDimensional.of_injective
      (LinearMap.inr ℝ (EuclideanSpace ℝ (Fin k)) hImm.complement)
      LinearMap.inr_injective
  have hfin :
      Module.finrank ℝ (EuclideanSpace ℝ (Fin k) × hImm.complement) = n := by
    calc
      Module.finrank ℝ (EuclideanSpace ℝ (Fin k) × hImm.complement)
          = Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
            exact hImm.equiv.toLinearEquiv.finrank_eq
      _ = n := by
            simpa using finrank_euclideanSpace_fin (α := ℝ) (ι := Fin n)
  -- The immersion charts identify `ℝ^n` with `ℝ^k × F`, so `k` cannot exceed `n`.
  calc
    k ≤ k + Module.finrank ℝ hImm.complement := Nat.le_add_right k _
    _ = Module.finrank ℝ (EuclideanSpace ℝ (Fin k) × hImm.complement) := by
          simpa using (Module.finrank_prod ℝ (EuclideanSpace ℝ (Fin k)) hImm.complement).symm
    _ = n := hfin

/-- Helper for Theorem 5.8: the tail coordinates of a `k`-slice in `ℝ^n` are indexed by the last
`n - k` coordinates after identifying `n` with `k + (n - k)`. -/
def euclidean_slice_tail_coordinate (hk : k ≤ n) (i : Fin (n - k)) : Fin n :=
  Fin.cast (Nat.add_sub_of_le hk) (i.natAdd k)

/-- Helper for Theorem 5.8: projection to the first `k` coordinates of `ℝ^n`. -/
def euclidean_slice_projection (hk : k ≤ n)
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 fun i ↦ x (Fin.castLE hk i)

/-- Helper for Theorem 5.8: reinsert the fixed tail coordinates of a Euclidean `k`-slice. -/
def euclidean_slice_inclusion (hk : k ≤ n) (c : Fin (n - k) → ℝ)
    (x : EuclideanSpace ℝ (Fin k)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 <|
    (Fin.append x c) ∘ Fin.cast (Nat.add_sub_of_le hk).symm

/-- Helper for Theorem 5.8: after transporting `Fin k` into `Fin (k + (n - k))`, the first
coordinates agree with `Fin.castLE hk`. -/
theorem cast_first_coordinates (hk : k ≤ n) (i : Fin k) :
    Fin.cast (Nat.add_sub_of_le hk) (Fin.castAdd (n - k) i) = Fin.castLE hk i := by
  -- Both sides are the same element of `Fin n`; only the proof witnesses differ.
  ext
  rfl

/-- Helper for Theorem 5.8: transporting a first coordinate of `Fin n` back to
`Fin (k + (n - k))` recovers the left summand index. -/
theorem cast_symm_first_coordinates (hk : k ≤ n) (i : Fin k) :
    Fin.cast (Nat.add_sub_of_le hk).symm (Fin.castLE hk i) = Fin.castAdd (n - k) i := by
  -- Apply the forward cast and use injectivity to remove the transport.
  apply Fin.cast_injective (Nat.add_sub_of_le hk)
  simpa using (cast_first_coordinates hk i).symm

/-- Helper for Theorem 5.8: the fixed-tail inclusion really has the prescribed tail coordinates. -/
theorem euclidean_slice_inclusion_tail
    (hk : k ≤ n) (c : Fin (n - k) → ℝ) (x : EuclideanSpace ℝ (Fin k))
    (i : Fin (n - k)) :
    euclidean_slice_inclusion hk c x (euclidean_slice_tail_coordinate hk i) = c i := by
  -- Rewrite the transported tail index back to `Fin.natAdd`; then `Fin.append_right` applies.
  change
    (Fin.append x c)
        (Fin.cast (Nat.add_sub_of_le hk).symm
          (Fin.cast (Nat.add_sub_of_le hk) (i.natAdd k))) = c i
  rw [(Fin.leftInverse_cast (Nat.add_sub_of_le hk)) (i.natAdd k)]
  simp

/-- Helper for Theorem 5.8: the fixed-tail inclusion keeps the first `k` coordinates unchanged. -/
theorem euclidean_slice_inclusion_first
    (hk : k ≤ n) (c : Fin (n - k) → ℝ) (x : EuclideanSpace ℝ (Fin k))
    (i : Fin k) :
    euclidean_slice_inclusion hk c x (Fin.castLE hk i) = x i := by
  -- Rewrite the transported first index back to the left summand of `Fin.append`.
  change
    (Fin.append x c)
        (Fin.cast (Nat.add_sub_of_le hk).symm (Fin.castLE hk i)) = x i
  rw [cast_symm_first_coordinates hk i]
  simp

/-- Helper for Theorem 5.8: projecting after reinserting the fixed tail gives back the original
`k`-tuple. -/
theorem euclidean_slice_projection_inclusion
    (hk : k ≤ n) (c : Fin (n - k) → ℝ) (x : EuclideanSpace ℝ (Fin k)) :
    euclidean_slice_projection hk (euclidean_slice_inclusion hk c x) = x := by
  -- On the first `k` coordinates the appended tuple is definitionally the original point.
  ext i
  change
    (Fin.append x c)
        (Fin.cast (Nat.add_sub_of_le hk).symm (Fin.castLE hk i)) = x i
  rw [cast_symm_first_coordinates hk i]
  simp

/-- Helper for Theorem 5.8: reinserting the projected first coordinates of a point already lying
in the Euclidean slice recovers that point. -/
theorem euclidean_slice_inclusion_projection
    {U : Set (EuclideanSpace ℝ (Fin n))}
    (hk : k ≤ n) (c : Fin (n - k) → ℝ)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ Set.euclideanSlice U k hk c) :
    euclidean_slice_inclusion hk c (euclidean_slice_projection hk y) = y := by
  -- Split the transported `Fin n` index into first and last coordinates and use the slice
  -- equations only on the tail part.
  ext i
  rcases (Fin.rightInverse_cast (Nat.add_sub_of_le hk)).surjective i with ⟨j, rfl⟩
  refine Fin.addCases ?_ ?_ j
  · intro j'
    change
      (Fin.append (euclidean_slice_projection hk y) c) (Fin.castAdd (n - k) j') =
        y (Fin.cast (Nat.add_sub_of_le hk) (Fin.castAdd (n - k) j'))
    rw [Fin.append_left, cast_first_coordinates]
    rfl
  · intro j'
    change
      (Fin.append (euclidean_slice_projection hk y) c) (j'.natAdd k) =
        y (Fin.cast (Nat.add_sub_of_le hk) (j'.natAdd k))
    rw [Fin.append_right]
    exact (hy.2 j').symm

/-- Helper for Theorem 5.8: reinserting a `k`-tuple whose image lies in `U` lands in the
corresponding Euclidean slice of `U`. -/
theorem euclidean_slice_inclusion_mem
    {U : Set (EuclideanSpace ℝ (Fin n))}
    (hk : k ≤ n) (c : Fin (n - k) → ℝ) {x : EuclideanSpace ℝ (Fin k)}
    (hx : euclidean_slice_inclusion hk c x ∈ U) :
    euclidean_slice_inclusion hk c x ∈ Set.euclideanSlice U k hk c := by
  -- Membership is exactly the ambient-target condition together with the tail-coordinate equalities.
  refine ⟨hx, ?_⟩
  intro i
  exact euclidean_slice_inclusion_tail hk c x i

/-- Helper for Theorem 5.8: a Euclidean slice is exactly the image of the fixed-tail inclusion
over the projected first coordinates. -/
theorem euclidean_slice_eq_image_inclusion
    (U : Set (EuclideanSpace ℝ (Fin n))) (hk : k ≤ n) (c : Fin (n - k) → ℝ) :
    Set.euclideanSlice U k hk c =
      euclidean_slice_inclusion hk c ''
        {x : EuclideanSpace ℝ (Fin k) | euclidean_slice_inclusion hk c x ∈ U} := by
  -- The forward direction projects a slice point to its free coordinates; the backward direction
  -- reinserts the fixed tail and uses the previous landing-in-slice lemma.
  ext y
  constructor
  · intro hy
    refine ⟨euclidean_slice_projection hk y, ?_, ?_⟩
    · simpa [euclidean_slice_inclusion_projection hk c hy] using hy.1
    · exact euclidean_slice_inclusion_projection hk c hy
  · rintro ⟨x, hx, rfl⟩
    exact euclidean_slice_inclusion_mem hk c hx

/-- Helper for Theorem 5.8: the projection to the first `k` coordinates is continuous. -/
theorem euclidean_slice_projection_continuous (hk : k ≤ n) :
    Continuous (euclidean_slice_projection hk :
      EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin k)) := by
  -- Check continuity coordinatewise on the underlying Pi-type, then repackage with `WithLp.toLp`.
  have hcoord :
      Continuous fun x : EuclideanSpace ℝ (Fin n) => fun i : Fin k ↦ x (Fin.castLE hk i) :=
    continuous_pi fun i ↦
      PiLp.continuous_apply (p := 2) (β := fun _ : Fin n => ℝ) (Fin.castLE hk i)
  simpa [euclidean_slice_projection] using
    (PiLp.continuous_toLp 2 (fun _ : Fin k => ℝ)).comp hcoord

/-- Helper for Theorem 5.8: the projection to the first `k` coordinates is smooth. -/
theorem euclidean_slice_projection_contMDiff (hk : k ≤ n) :
    ContMDiff (𝓡 n) (𝓡 k) (⊤ : WithTop ℕ∞) (euclidean_slice_projection hk) := by
  let projPi : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin k → ℝ) :=
    ContinuousLinearMap.pi fun i ↦
      PiLp.proj 2 (fun _ : Fin n => ℝ) (Fin.castLE hk i)
  let toLp :
      (Fin k → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin k) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin k => ℝ)).symm.toContinuousLinearMap
  -- The coordinate projection is the composition of continuous linear maps on Euclidean spaces.
  simpa [euclidean_slice_projection, projPi, toLp] using
    (toLp.comp projPi).contMDiff

/-- Helper for Theorem 5.8: reinserting fixed tail coordinates is continuous. -/
theorem euclidean_slice_inclusion_continuous
    (hk : k ≤ n) (c : Fin (n - k) → ℝ) :
    Continuous (euclidean_slice_inclusion hk c :
      EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin n)) := by
  -- Rewrite each transported coordinate either as one of the free coordinates or as a constant.
  have hcoord :
      Continuous fun x : EuclideanSpace ℝ (Fin k) =>
        fun i : Fin n ↦ ((Fin.append x c) ∘ Fin.cast (Nat.add_sub_of_le hk).symm) i := by
    refine continuous_pi ?_
    intro i
    rcases (Fin.rightInverse_cast (Nat.add_sub_of_le hk)).surjective i with ⟨j, rfl⟩
    refine Fin.addCases ?_ ?_ j
    · intro j'
      have hcast :
          Fin.cast (Nat.add_sub_of_le hk).symm
              (Fin.cast (Nat.add_sub_of_le hk) (Fin.castAdd (n - k) j')) =
            Fin.castAdd (n - k) j' :=
        (Fin.leftInverse_cast (Nat.add_sub_of_le hk)) (Fin.castAdd (n - k) j')
      simpa [Function.comp] using
        (show Continuous fun x : EuclideanSpace ℝ (Fin k) => x j' from
          PiLp.continuous_apply (p := 2) (β := fun _ : Fin k => ℝ) j')
    · intro j'
      have hcast :
          Fin.cast (Nat.add_sub_of_le hk).symm
              (Fin.cast (Nat.add_sub_of_le hk) (j'.natAdd k)) =
            j'.natAdd k :=
        (Fin.leftInverse_cast (Nat.add_sub_of_le hk)) (j'.natAdd k)
      simpa [Function.comp, hcast] using
        (continuous_const : Continuous fun _ : EuclideanSpace ℝ (Fin k) => c j')
  simpa [euclidean_slice_inclusion] using
    (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp hcoord

/-- Helper for Theorem 5.8: reinserting fixed tail coordinates is smooth. -/
theorem euclidean_slice_inclusion_contMDiff
    (hk : k ≤ n) (c : Fin (n - k) → ℝ) :
    ContMDiff (𝓡 k) (𝓡 n) (⊤ : WithTop ℕ∞) (euclidean_slice_inclusion hk c) := by
  rw [contMDiff_iff_contDiff]
  -- Keep the proof on Euclidean space: each coordinate is either one of the free coordinates
  -- or a fixed constant, and `WithLp.toLp` then packages the coordinatewise `ContDiff` map.
  refine (PiLp.contDiff_toLp (p := 2) (𝕜 := ℝ) (E := fun _ : Fin n ↦ ℝ)).comp ?_
  rw [contDiff_pi]
  intro i
  rcases (Fin.rightInverse_cast (Nat.add_sub_of_le hk)).surjective i with ⟨j, rfl⟩
  refine Fin.addCases ?_ ?_ j
  · intro j'
    have hcoord :
        (fun x : EuclideanSpace ℝ (Fin k) ↦
          ((Fin.append x c) ∘ Fin.cast (Nat.add_sub_of_le hk).symm)
            (Fin.cast (Nat.add_sub_of_le hk) (Fin.castAdd (n - k) j'))) =
          fun x : EuclideanSpace ℝ (Fin k) ↦ x j' := by
      funext x
      change
        (Fin.append x c)
          (Fin.cast (Nat.add_sub_of_le hk).symm
            (Fin.cast (Nat.add_sub_of_le hk) (Fin.castAdd (n - k) j'))) = x j'
      rw [(Fin.leftInverse_cast (Nat.add_sub_of_le hk)) (Fin.castAdd (n - k) j')]
      simp
    -- On the first `k` slots, the inclusion is exactly the corresponding coordinate projection.
    rw [hcoord]
    exact contDiff_piLp_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin k ↦ ℝ) (i := j')
  · intro j'
    have hcoord :
        (fun x : EuclideanSpace ℝ (Fin k) ↦
          ((Fin.append x c) ∘ Fin.cast (Nat.add_sub_of_le hk).symm)
            (Fin.cast (Nat.add_sub_of_le hk) (j'.natAdd k))) =
          fun _ : EuclideanSpace ℝ (Fin k) ↦ c j' := by
      funext x
      change
        (Fin.append x c)
          (Fin.cast (Nat.add_sub_of_le hk).symm
            (Fin.cast (Nat.add_sub_of_le hk) (j'.natAdd k))) = c j'
      rw [(Fin.leftInverse_cast (Nat.add_sub_of_le hk)) (j'.natAdd k)]
      simp
    -- On the last `n - k` slots, the inclusion is constant with value prescribed by the slice.
    rw [hcoord]
    exact contDiff_const

/-- Helper for Theorem 5.8: the Euclidean product model `ℝ^k × ℝ^{n-k}` identifies canonically
with `ℝ^n` after transporting `n = k + (n - k)`. -/
noncomputable def euclidean_slice_product_equiv (hk : k ≤ n) :
    (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k))) ≃L[ℝ]
      EuclideanSpace ℝ (Fin n) :=
  -- Use the canonical Euclidean decomposition `ℝ^(k + (n-k)) ≃ ℝ^k × ℝ^(n-k)` and transport the
  -- index type along `k + (n - k) = n`.
  ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := k) (m := n - k)).symm).trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
      (Equiv.cast (congrArg Fin (Nat.add_sub_of_le hk)))).toContinuousLinearEquiv

/-- Helper for Theorem 5.8: before the final `Fin`-index transport, the product-model source data
already has first component equal to the free `k`-coordinates. -/
theorem euclidean_slice_product_equiv_source_pair_fst
    (z : EuclideanSpace ℝ (Fin k)) :
    (((WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).symm.prodCongr
        (WithLp.linearEquiv 2 ℝ (Fin (n - k) → ℝ)).symm).symm
      (z, (0 : EuclideanSpace ℝ (Fin (n - k))))).1 = z.ofLp := by
  -- Unwinding the `WithLp` packaging shows that the product equivalence keeps the first block.
  rfl

/-- Helper for Theorem 5.8: before the final `Fin`-index transport, the product-model source data
already has second component equal to the zero tail. -/
theorem euclidean_slice_product_equiv_source_pair_snd
    (z : EuclideanSpace ℝ (Fin k)) :
    (((WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).symm.prodCongr
        (WithLp.linearEquiv 2 ℝ (Fin (n - k) → ℝ)).symm).symm
      (z, (0 : EuclideanSpace ℝ (Fin (n - k))))).2 =
      (fun _ : Fin (n - k) ↦ (0 : ℝ)) := by
  -- The second block of the product input is literally the zero vector.
  rfl

/-- Helper for Theorem 5.8: transporting a `Fin` index along an equality of ambient dimensions
agrees with the specialized `Fin.cast`. -/
theorem cast_congrArg_Fin_eq_Fin_cast {a b : ℕ} (h : a = b) (x : Fin a) :
    (cast (congrArg Fin h) x : Fin b) = Fin.cast h x := by
  -- After reducing the ambient equality to `rfl`, both transports are definitionally identical.
  subst h
  rfl

/-- Helper for Theorem 5.8: transporting a first-block index through the final `Fin` cast in the
product-model equivalence leaves that left-summand index unchanged. -/
theorem equiv_cast_symm_castAdd_eq_castAdd
    (hk : k ≤ n) (i : Fin k) :
    (Equiv.cast (congrArg Fin (Nat.add_sub_of_le hk))).symm
      (Fin.cast (Nat.add_sub_of_le hk) (Fin.castAdd (n - k) i)) =
      Fin.castAdd (n - k) i := by
  -- First identify the generic `Equiv.cast` transport with the specialized `Fin.cast`, then
  -- cancel the forward and backward casts.
  calc
    (Equiv.cast (congrArg Fin (Nat.add_sub_of_le hk))).symm
        (Fin.cast (Nat.add_sub_of_le hk) (Fin.castAdd (n - k) i)) =
      Fin.cast (Nat.add_sub_of_le hk).symm
        (Fin.cast (Nat.add_sub_of_le hk) (Fin.castAdd (n - k) i)) := by
          simpa [Equiv.cast] using
            cast_congrArg_Fin_eq_Fin_cast
              (a := n) (b := k + (n - k)) (Nat.add_sub_of_le hk).symm
              (Fin.cast (Nat.add_sub_of_le hk) (Fin.castAdd (n - k) i))
    _ = Fin.castAdd (n - k) i := by
          exact (Fin.leftInverse_cast (Nat.add_sub_of_le hk)) (Fin.castAdd (n - k) i)

/-- Helper for Theorem 5.8: transporting a tail-block index through the final `Fin` cast in the
product-model equivalence leaves that right-summand index unchanged. -/
theorem equiv_cast_symm_natAdd_eq_natAdd
    (hk : k ≤ n) (i : Fin (n - k)) :
    (Equiv.cast (congrArg Fin (Nat.add_sub_of_le hk))).symm
      (Fin.cast (Nat.add_sub_of_le hk) (Fin.natAdd k i)) =
      Fin.natAdd k i := by
  -- The same cast-identification and cancellation argument works on the tail block.
  calc
    (Equiv.cast (congrArg Fin (Nat.add_sub_of_le hk))).symm
        (Fin.cast (Nat.add_sub_of_le hk) (Fin.natAdd k i)) =
      Fin.cast (Nat.add_sub_of_le hk).symm
        (Fin.cast (Nat.add_sub_of_le hk) (Fin.natAdd k i)) := by
          simpa [Equiv.cast] using
            cast_congrArg_Fin_eq_Fin_cast
              (a := n) (b := k + (n - k)) (Nat.add_sub_of_le hk).symm
              (Fin.cast (Nat.add_sub_of_le hk) (Fin.natAdd k i))
    _ = Fin.natAdd k i := by
          exact (Fin.leftInverse_cast (Nat.add_sub_of_le hk)) (Fin.natAdd k i)

/-- Helper for Theorem 5.8: the product-model equivalence sends `(z, 0)` to Lee's standard
zero-tail slice inclusion. -/
theorem euclidean_slice_product_equiv_apply_zero
    (hk : k ≤ n) (z : EuclideanSpace ℝ (Fin k)) :
    euclidean_slice_product_equiv hk
        (z, (0 : EuclideanSpace ℝ (Fin (n - k)))) =
      euclidean_slice_inclusion hk (fun _ : Fin (n - k) ↦ (0 : ℝ)) z := by
  -- Route correction: the remaining work is no longer the `WithLp` product packaging but the
  -- final transport from `Fin (k + (n - k))` to `Fin n` through `Equiv.cast`.
  ext i
  rcases (Fin.rightInverse_cast (Nat.add_sub_of_le hk)).surjective i with ⟨j, rfl⟩
  refine Fin.addCases ?_ ?_ j
  · intro j'
    -- On the first `k` coordinates, the product model reduces to the left source component.
    simp only [euclidean_slice_product_equiv, euclidean_slice_inclusion,
      ContinuousLinearEquiv.trans_apply, Function.comp_apply]
    simp [Equiv.piCongrLeft']
    rw [equiv_cast_symm_castAdd_eq_castAdd, finSumFinEquiv_symm_apply_castAdd,
      euclidean_slice_product_equiv_source_pair_fst]
    exact hk
  · intro j'
    -- On the tail coordinates, the same reduction lands in the zero right source component.
    simp only [euclidean_slice_product_equiv, euclidean_slice_inclusion,
      ContinuousLinearEquiv.trans_apply, Function.comp_apply]
    simp [Equiv.piCongrLeft']
    rw [equiv_cast_symm_natAdd_eq_natAdd, finSumFinEquiv_symm_apply_natAdd,
      euclidean_slice_product_equiv_source_pair_snd]
    exact hk

/-- Helper for Theorem 5.8: subtracting the base point of an affine Euclidean slice removes the
fixed tail constants and leaves only the zero-tail inclusion. -/
theorem euclidean_slice_inclusion_sub_base
    (hk : k ≤ n) (c : Fin (n - k) → ℝ)
    (z z0 : EuclideanSpace ℝ (Fin k)) :
    euclidean_slice_inclusion hk c (z + z0) - euclidean_slice_inclusion hk c z0 =
      euclidean_slice_inclusion hk (fun _ : Fin (n - k) ↦ (0 : ℝ)) z := by
  -- Compare first and last coordinates separately: the first block subtracts to `z`, while the
  -- fixed tail cancels to `0`.
  ext i
  rcases (Fin.rightInverse_cast (Nat.add_sub_of_le hk)).surjective i with ⟨j, rfl⟩
  refine Fin.addCases ?_ ?_ j
  · intro j'
    rw [cast_first_coordinates]
    change
      euclidean_slice_inclusion hk c (z + z0) (Fin.castLE hk j') -
          euclidean_slice_inclusion hk c z0 (Fin.castLE hk j') =
        euclidean_slice_inclusion hk (fun _ : Fin (n - k) ↦ (0 : ℝ)) z (Fin.castLE hk j')
    rw [euclidean_slice_inclusion_first, euclidean_slice_inclusion_first,
      euclidean_slice_inclusion_first]
    change z j' + z0 j' - z0 j' = z j'
    ring_nf
  · intro j'
    change
      euclidean_slice_inclusion hk c (z + z0) (euclidean_slice_tail_coordinate hk j') -
          euclidean_slice_inclusion hk c z0 (euclidean_slice_tail_coordinate hk j') =
        euclidean_slice_inclusion hk (fun _ : Fin (n - k) ↦ (0 : ℝ)) z
          (euclidean_slice_tail_coordinate hk j')
    rw [euclidean_slice_inclusion_tail, euclidean_slice_inclusion_tail,
      euclidean_slice_inclusion_tail]
    ring

/-- Helper for Theorem 5.8: the Chapter 4 immersion normal form `rank_normal_form k n k` is
exactly Lee's fixed-tail inclusion with zero tail coordinates. -/
theorem rank_normal_form_self_eq_euclidean_slice_inclusion_zero
    (hk : k ≤ n) :
    LocalNormalFormAPI.rank_normal_form k n k =
      euclidean_slice_inclusion hk (fun _ : Fin (n - k) ↦ (0 : ℝ)) := by
  -- The rank-`k` normal form keeps the first `k` coordinates and sets the remaining coordinates
  -- to zero, exactly matching the zero-tail slice inclusion.
  funext x
  ext i
  rcases (Fin.rightInverse_cast (Nat.add_sub_of_le hk)).surjective i with ⟨j, rfl⟩
  refine Fin.addCases ?_ ?_ j
  · intro j'
    rw [cast_first_coordinates]
    have hfirst :
        LocalNormalFormAPI.rank_normal_form k n k x
            (Fin.cast (Nat.add_sub_of_le hk) (Fin.castAdd (n - k) j')) =
          x j' := by
      exact LocalNormalFormAPI.rank_normal_form_apply_of_lt
        (i := Fin.cast (Nat.add_sub_of_le hk) (Fin.castAdd (n - k) j')) (x := x)
        (by simpa) (by simpa)
    simpa using hfirst.trans
      (euclidean_slice_inclusion_first hk (fun _ : Fin (n - k) ↦ (0 : ℝ)) x j').symm
  · intro j'
    have hgeTail : k ≤ (euclidean_slice_tail_coordinate hk j').1 := by
      simpa [euclidean_slice_tail_coordinate] using (Nat.le_add_left k j'.1)
    have hnotTail : ¬ (euclidean_slice_tail_coordinate hk j').1 < k := Nat.not_lt_of_ge hgeTail
    change
      LocalNormalFormAPI.rank_normal_form k n k x (euclidean_slice_tail_coordinate hk j') =
        euclidean_slice_inclusion hk (fun _ : Fin (n - k) ↦ (0 : ℝ)) x
          (euclidean_slice_tail_coordinate hk j')
    rw [euclidean_slice_inclusion_tail]
    simp [_root_.rank_normal_form, LocalNormalFormAPI.rank_normal_form,
      euclidean_slice_tail_coordinate, hnotTail]

/-- Helper for Theorem 5.8: the rank-theorem inclusion form already lands in the literal
Euclidean `k`-slice with zero tail coordinates. -/
theorem rank_normal_form_self_mem_zero_slice
    (hk : k ≤ n) (x : EuclideanSpace ℝ (Fin k)) :
    LocalNormalFormAPI.rank_normal_form k n k x ∈
      Set.euclideanSlice Set.univ k hk (fun _ : Fin (n - k) ↦ (0 : ℝ)) := by
  -- After normalizing to the fixed-tail inclusion, this is exactly the canonical zero-slice
  -- landing lemma proved earlier for `euclidean_slice_inclusion`.
  rw [rank_normal_form_self_eq_euclidean_slice_inclusion_zero hk]
  exact euclidean_slice_inclusion_mem hk (fun _ : Fin (n - k) ↦ (0 : ℝ)) (by simp)

/-- Helper for Theorem 5.8: projection identifies a Euclidean slice subtype with the subtype of
`ℝ^k` cut out by the ambient target condition. -/
noncomputable def euclidean_slice_projection_homeomorph
    (U : Set (EuclideanSpace ℝ (Fin n))) (hk : k ≤ n) (c : Fin (n - k) → ℝ) :
    Set.euclideanSlice U k hk c ≃ₜ
      {u : EuclideanSpace ℝ (Fin k) | euclidean_slice_inclusion hk c u ∈ U} where
  toFun x := by
    refine ⟨euclidean_slice_projection hk x.1, ?_⟩
    -- A slice point stays in `U` after projecting and reinserting the fixed tail.
    simpa [euclidean_slice_inclusion_projection hk c x.2] using x.2.1
  invFun u := ⟨euclidean_slice_inclusion hk c u.1, euclidean_slice_inclusion_mem hk c u.2⟩
  left_inv x := by
    -- A point of the slice is determined by its first `k` coordinates.
    exact Subtype.ext (euclidean_slice_inclusion_projection hk c x.2)
  right_inv u := by
    -- Projecting a point after reinserting the fixed tail returns the original coordinates.
    exact Subtype.ext (euclidean_slice_projection_inclusion hk c u.1)
  continuous_toFun := by
    -- The subtype chart map is the ambient projection together with the target-membership proof.
    exact Continuous.subtype_mk
      ((euclidean_slice_projection_continuous hk).comp continuous_subtype_val)
      (fun x ↦ by simpa [euclidean_slice_inclusion_projection hk c x.2] using x.2.1)
  continuous_invFun := by
    -- The inverse is the fixed-tail inclusion, which lands in the slice by construction.
    exact Continuous.subtype_mk
      ((euclidean_slice_inclusion_continuous hk c).comp continuous_subtype_val)
      (fun u ↦ euclidean_slice_inclusion_mem hk c u.2)

/-- Helper for Theorem 5.8: once the projected target is known to be open and nonempty, the
Euclidean slice homeomorphism upgrades to an honest chart with ambient codomain `ℝ^k`. -/
noncomputable def euclidean_slice_projection_partial_homeomorph
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) (hk : k ≤ n)
    (c : Fin (n - k) → ℝ) (x : Set.euclideanSlice U k hk c) :
    OpenPartialHomeomorph (Set.euclideanSlice U k hk c) (EuclideanSpace ℝ (Fin k)) := by
  let targetOpen : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin k)) :=
    ⟨{u : EuclideanSpace ℝ (Fin k) | euclidean_slice_inclusion hk c u ∈ U}, by
      -- The target is open because it is the preimage of the ambient open set under the
      -- fixed-tail inclusion.
      simpa [Set.preimage, Function.comp] using
        hU.preimage (euclidean_slice_inclusion_continuous hk c)⟩
  let targetNonempty : Nonempty targetOpen := by
    -- The chosen slice point provides a point of the projected target.
    refine ⟨⟨euclidean_slice_projection hk x.1, ?_⟩⟩
    change euclidean_slice_inclusion hk c (euclidean_slice_projection hk x.1) ∈ U
    simpa [euclidean_slice_inclusion_projection hk c x.2] using x.2.1
  -- Compose the slice-subtype homeomorphism with the inclusion of the open target into `ℝ^k`.
  exact OpenPartialHomeomorph.trans'
    (euclidean_slice_projection_homeomorph U hk c).toOpenPartialHomeomorph
    (targetOpen.openPartialHomeomorphSubtypeCoe targetNonempty)
    rfl

/-- Helper for Theorem 5.8: the Euclidean slice chart really is projection to the first `k`
coordinates. -/
theorem euclidean_slice_projection_partial_homeomorph_apply
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) (hk : k ≤ n)
    (c : Fin (n - k) → ℝ) (x : Set.euclideanSlice U k hk c)
    (y : Set.euclideanSlice U k hk c) :
    euclidean_slice_projection_partial_homeomorph U hU hk c x y =
      euclidean_slice_projection hk y.1 := by
  -- Unfold the composed partial homeomorphism: the final open-subset inclusion only forgets the
  -- proof that the projected point lies in the open target.
  rfl

/-- Helper for Theorem 5.8: the inverse Euclidean slice chart projects back to the chosen target
point. -/
theorem euclidean_slice_projection_partial_homeomorph_projection_symm
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) (hk : k ≤ n)
    (c : Fin (n - k) → ℝ) (x : Set.euclideanSlice U k hk c)
    {z : EuclideanSpace ℝ (Fin k)}
    (hz : z ∈ (euclidean_slice_projection_partial_homeomorph U hU hk c x).target) :
    euclidean_slice_projection hk
      ((euclidean_slice_projection_partial_homeomorph U hU hk c x).symm z).1 = z := by
  let e := euclidean_slice_projection_partial_homeomorph U hU hk c x
  -- Apply the right-inverse identity for the partial homeomorphism and then forget the target
  -- membership proof.
  simpa [e, euclidean_slice_projection_partial_homeomorph_apply] using e.right_inv hz

/-- Helper for Theorem 5.8: the inverse Euclidean slice chart is the fixed-tail inclusion. -/
theorem euclidean_slice_projection_partial_homeomorph_symm_apply
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) (hk : k ≤ n)
    (c : Fin (n - k) → ℝ) (x : Set.euclideanSlice U k hk c)
    {z : EuclideanSpace ℝ (Fin k)}
    (hz : z ∈ (euclidean_slice_projection_partial_homeomorph U hU hk c x).target) :
    ((euclidean_slice_projection_partial_homeomorph U hU hk c x).symm z).1 =
      euclidean_slice_inclusion hk c z := by
  let e := euclidean_slice_projection_partial_homeomorph U hU hk c x
  let w : Set.euclideanSlice U k hk c := e.symm z
  have hwproj : euclidean_slice_projection hk w.1 = z := by
    simpa [e, w, euclidean_slice_projection_partial_homeomorph_apply] using e.right_inv hz
  -- A point of the slice is determined by its first `k` coordinates, so the inverse is the
  -- fixed-tail inclusion.
  calc
    w.1 = euclidean_slice_inclusion hk c (euclidean_slice_projection hk w.1) := by
      symm
      exact euclidean_slice_inclusion_projection hk c w.2
    _ = euclidean_slice_inclusion hk c z := by rw [hwproj]

/-- Helper for Theorem 5.8: translations of Euclidean space are smooth model-space chart changes,
so their associated partial homeomorphisms belong to the smooth groupoid. -/
theorem euclidean_translation_mem_contDiffGroupoid
    {m : ℕ} (v : EuclideanSpace ℝ (Fin m)) :
    (Homeomorph.addRight v).toOpenPartialHomeomorph ∈
      contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 m) := by
  -- On Euclidean space, both the translation and its inverse are smooth maps on all of `ℝ^m`.
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid]
  constructor
  · simpa [modelWithCornersSelf_coe, Homeomorph.addRight] using
      (contDiff_id.add contDiff_const).contDiffOn
  · simpa [modelWithCornersSelf_coe, Homeomorph.addRight] using
      (contDiff_id.add contDiff_const).contDiffOn

/-- Helper for Theorem 5.8: postcomposing a maximal-atlas chart with a smooth Euclidean
translation keeps it in the same maximal atlas. -/
theorem trans_mem_maximalAtlas_of_mem_groupoid
    {m : ℕ} {X : Type u} [TopologicalSpace X]
    [TopologicalManifold m X]
    [IsManifold (𝓡 m) (⊤ : WithTop ℕ∞) X]
    {e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin m))}
    (he : e ∈ IsManifold.maximalAtlas (𝓡 m) (⊤ : WithTop ℕ∞) X)
    {chi : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m))}
    (hchi : chi ∈ contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 m)) :
    e.trans chi ∈ IsManifold.maximalAtlas (𝓡 m) (⊤ : WithTop ℕ∞) X := by
  -- Maximal-atlas membership is tested by smooth compatibility with the original atlas charts.
  rw [IsManifold.mem_maximalAtlas_iff]
  intro e' he'
  have he'max : e' ∈ IsManifold.maximalAtlas (𝓡 m) (⊤ : WithTop ℕ∞) X := by
    exact IsManifold.subset_maximalAtlas he'
  have hleft : e.symm.trans e' ∈ contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 m) := by
    exact IsManifold.compatible_of_mem_maximalAtlas he he'max
  have hright : e'.symm.trans e ∈ contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 m) := by
    exact IsManifold.compatible_of_mem_maximalAtlas he'max he
  constructor
  · -- The left transition factors through `chi.symm` and the old transition from `e`.
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc]
    exact
      (contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 m)).trans
        ((contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 m)).symm hchi) hleft
  · -- The right transition is the old one followed by the new model-space chart change.
    have hright' : (e'.symm.trans e).trans chi ∈
        contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 m) := by
      exact (contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 m)).trans hright hchi
    simpa [OpenPartialHomeomorph.trans_assoc] using hright'

/-- Helper for Theorem 5.8: centering a maximal-atlas chart at one of its source points preserves
maximal-atlas membership. -/
theorem centerAt_mem_maximalAtlas
    {m : ℕ} {X : Type u} [TopologicalSpace X]
    [TopologicalManifold m X]
    [IsManifold (𝓡 m) (⊤ : WithTop ℕ∞) X]
    (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin m)))
    (he : e ∈ IsManifold.maximalAtlas (𝓡 m) (⊤ : WithTop ℕ∞) X)
    (p : e.source) :
    e.centerAt p ∈ IsManifold.maximalAtlas (𝓡 m) (⊤ : WithTop ℕ∞) X := by
  -- Centering is postcomposition with a smooth Euclidean translation, so maximal-atlas
  -- membership is preserved by the model-space groupoid action.
  simpa [OpenPartialHomeomorph.centerAt, OpenPartialHomeomorph.transHomeomorph_eq_trans] using
    trans_mem_maximalAtlas_of_mem_groupoid
      (m := m) (X := X) he
      (hchi := euclidean_translation_mem_contDiffGroupoid (-e p))

/-- Helper for Theorem 5.8: a centered Euclidean-valued chart subtracts the basepoint coordinates
from the original chart value. -/
theorem centerAt_apply_eq_sub_basepoint
    {m : ℕ} {X : Type u} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin m)))
    (p : e.source) (y : X) :
    e.centerAt p y = e y - e p := by
  -- Unfold Lee's centering operation: it is literally translation by `-e p` in Euclidean space.
  simp [OpenPartialHomeomorph.centerAt, sub_eq_add_neg]

/-- Helper for Theorem 5.8: a point in the target of a centered chart moves back into the target
of the original chart after adding the basepoint coordinates. -/
theorem centerAt_add_base_mem_target
    {m : ℕ} {X : Type u} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin m)))
    (p : e.source) {z : EuclideanSpace ℝ (Fin m)}
    (hz : z ∈ (e.centerAt p).target) :
    z + e p ∈ e.target := by
  -- The centered target is the original target translated by `-e p`, so undoing that
  -- translation returns to the old target.
  rw [OpenPartialHomeomorph.centerAt, OpenPartialHomeomorph.transHomeomorph_eq_trans,
    OpenPartialHomeomorph.trans_target] at hz
  simpa [Homeomorph.addRight, sub_eq_add_neg] using hz.2

/-- Helper for Theorem 5.8: the inverse of a centered chart is obtained by adding back the
basepoint coordinates before applying the original inverse chart. -/
theorem centerAt_symm_apply_eq_symm_add
    {m : ℕ} {X : Type u} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin m)))
    (p : e.source) {z : EuclideanSpace ℝ (Fin m)}
    (hz : z ∈ (e.centerAt p).target) :
    (e.centerAt p).symm z = e.symm (z + e p) := by
  have hy : (e.centerAt p).symm z ∈ e.source := by
    simpa [OpenPartialHomeomorph.centerAt_source] using (e.centerAt p).map_target hz
  have htarget : z + e p ∈ e.target := centerAt_add_base_mem_target e p hz
  have hcentered :
      e ((e.centerAt p).symm z) - e p = z := by
    -- Evaluate the centered chart at its inverse point and rewrite back in the original chart.
    calc
      e ((e.centerAt p).symm z) - e p = (e.centerAt p) ((e.centerAt p).symm z) := by
        symm
        exact centerAt_apply_eq_sub_basepoint e p ((e.centerAt p).symm z)
      _ = z := (e.centerAt p).right_inv hz
  have huncentered : e ((e.centerAt p).symm z) = z + e p := by
    rw [sub_eq_iff_eq_add] at hcentered
    simpa [add_comm] using hcentered
  -- Apply the original inverse chart after recovering the uncentered chart value.
  calc
    (e.centerAt p).symm z = e.symm (e ((e.centerAt p).symm z)) := by
      symm
      exact e.left_inv hy
    _ = e.symm (z + e p) := by rw [huncentered]

end
