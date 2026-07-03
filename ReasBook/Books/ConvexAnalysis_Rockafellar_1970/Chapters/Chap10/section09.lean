import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_10_9 (from Chap02) -/
section

open scoped Rockafellar Topology
open Set
open Filter

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [LocallyCompactSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 10.9 starts from a relatively open convex set `C`, a sequence of finite
  convex functions on `C`, and pointwise boundedness on all of `C`. It concludes that some
  subsequence converges uniformly on each closed bounded subset of `C` to a finite convex function.
- `core/canonical`: the owner abstractions are the chapter relative-openness owner
  `IsRelativelyOpen 𝕜 C`, `ConvexOn`,
  the chapter predicate `PointwiseBoundedOn`, and the Chapter 10 convergence owner
  `TendstoLocallyUniformlyOn`; the subsequence datum is canonically represented by a reindexing
  map `φ : ℕ → ℕ` together with `StrictMono φ`.
  of `C` is rendered by a subset carrier `C'` together with
  `C ⊆ intrinsicClosure 𝕜 C'`; the selected
  subsequence is represented by reindexing along a strictly monotone map `φ : ℕ → ℕ`.

Domain-style sampling used here:
- `IsRelativelyOpen 𝕜 C` (chapter owner surface for relative openness);
- `ConvexOn` for finite convex `𝕜`-valued functions on `C`;
- `PointwiseBoundedOn` for the source-facing boundedness hypothesis on each scalar fiber;
- `TendstoLocallyUniformlyOn` for the canonical convergence owner on `C`;
- `exists_convex_tendstoLocallyUniformlyOn_of_dense_pointwise`
  from Theorem 10.8 for the dense-subset passage from pointwise convergence to a convex locally
  uniform limit.

Primitive data vs derived API:
- primitive inputs: the owner relative-openness hypothesis `IsRelativelyOpen 𝕜 C`,
  the sequence `fSeq`,
  convexity of each
  `fSeq i` on `C`, and pointwise boundedness on `C`;
- bridge theorem data: a dense subset `D ⊆ C` together with a strictly monotone extraction
  `φ` for which the reindexed sequence `fSeq ∘ φ` converges pointwise on `D`;
- derived API: a `𝕜`-valued convex limit `f` and locally uniform convergence of `fSeq ∘ φ` to
  `f` on `C`, obtained by feeding that bridge into Theorem 10.8; the closed-bounded formulation is
  then the Euclidean compact-subset consequence of Theorem 10.8's owner theorem.

Layer target: the main labeled theorem is `source-facing`, stated directly with the chapter's
primitive relative-openness owner and standard mathlib subsequence and
uniform-convergence predicates. The
dense-subset extraction lemma is kept as a private proof bridge.
-/

variable (fSeq : ℕ → E → 𝕜) {C : Set E}

-- Proof sketch: choose a countable subset `D ⊆ C'` whose intrinsic closure still contains `C`,
-- enumerate it, and apply the diagonal Bolzano-Weierstrass argument to the bounded scalar sequences
-- `fSeq i x_j` to obtain a strictly monotone extraction `φ` with pointwise convergence on `D`.
-- The public theorem then feeds this primitive bridge into Theorem 10.8 to recover the convex
-- locally uniform limit on all of `C`.
/-- Private bridge for Theorem 10.9: if the sequence is pointwise bounded on a subset `C'`
whose intrinsic closure contains `C`, then some subsequence converges pointwise on a further dense
subset `D ⊆ C'`. This lemma is intentionally stated on the scalar-generic `𝕜` layer where
Bolzano-Weierstrass subsequence extraction is canonical. -/
private theorem exists_subsequence_tendsto_pointwiseOn_dense_subset
    {C' : Set E} (hC'_dense : C ⊆ intrinsicClosure 𝕜 C')
    (hbounded : PointwiseBoundedOn fSeq C') :
    ∃ D : Set E, D ⊆ C' ∧ C ⊆ intrinsicClosure 𝕜 D ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∀ x ∈ D, ∃ l : 𝕜, Tendsto (fun i ↦ (fSeq ∘ φ) i x) atTop (𝓝 l) := by
  classical
  haveI : ProperSpace 𝕜 := .of_locallyCompactSpace 𝕜
  letI : ProperSpace E := FiniteDimensional.proper (𝕜 := 𝕜) (E := E)
  have hC'_dense_closure : C ⊆ closure C' := by
    simpa [intrinsicClosure_eq_closure] using hC'_dense
  have hDense_subtype :
      Dense (Subtype.val ⁻¹' C' : Set (closure C')) := by
    refine (Subtype.dense_iff).2 ?_
    intro x hx
    have himage :
        (Subtype.val '' (Subtype.val ⁻¹' C' : Set (closure C'))) = C' := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz
      · intro hy
        exact ⟨⟨y, subset_closure hy⟩, hy, rfl⟩
    simpa [himage] using hx
  obtain ⟨D', hD'_subset, hD'_countable, hD'_dense⟩ :=
    hDense_subtype.exists_countable_dense_subset
  let D : Set E := Subtype.val '' D'
  have hD_subset : D ⊆ C' := by
    intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    exact hD'_subset hy
  have hclosure_subset : closure C' ⊆ closure D := by
    simpa [D] using (Subtype.dense_iff.mp hD'_dense)
  have hD_dense : C ⊆ intrinsicClosure 𝕜 D := by
    intro x hx
    have hxC' : x ∈ closure C' := hC'_dense_closure hx
    have hxD : x ∈ closure D := hclosure_subset hxC'
    simpa [intrinsicClosure_eq_closure] using hxD
  have hD_countable : D.Countable := hD'_countable.image Subtype.val
  letI : Encodable D := hD_countable.toEncodable
  have hbounded_subtype :
      ∀ x : C', Bornology.IsBounded (Set.range fun i ↦ fSeq i x) :=
    (pointwiseBoundedOn_iff_forall_isBounded_range_subtype.mp hbounded)
  have hboundedD : ∀ x : D, Bornology.IsBounded (Set.range fun i ↦ fSeq i x.1) := by
    intro x
    exact hbounded_subtype ⟨x.1, hD_subset x.2⟩
  let S : D → Set 𝕜 := fun x ↦ closure (Set.range fun i ↦ fSeq i x.1)
  have hScompact : IsCompact {g : D → 𝕜 | ∀ x, g x ∈ S x} := by
    refine isCompact_pi_infinite ?_
    intro x
    exact (hboundedD x).isCompact_closure
  let G : ℕ → D → 𝕜 := fun i x ↦ fSeq i x.1
  have hGmem : ∀ n, G n ∈ {g : D → 𝕜 | ∀ x, g x ∈ S x} := by
    intro n x
    exact subset_closure ⟨n, rfl⟩
  obtain ⟨l, _hl, φ, hφ, hconv⟩ := hScompact.tendsto_subseq hGmem
  have hpoint : ∀ x : D, Tendsto (fun i ↦ fSeq (φ i) x.1) atTop (𝓝 (l x)) := by
    intro x
    exact (tendsto_pi_nhds.mp hconv) x
  refine ⟨D, hD_subset, hD_dense, φ, hφ, ?_⟩
  intro x hx
  let xD : D := ⟨x, hx⟩
  refine ⟨l xD, ?_⟩
  simpa [Function.comp, xD] using hpoint xD

variable [CompleteSpace 𝕜] [LinearOrder 𝕜]
variable (hC_open : IsRelativelyOpen 𝕜 C) (hf_convex : ∀ i, ConvexOn 𝕜 C (fSeq i))

include hC_open hf_convex

-- Proof sketch: apply the dense-subset strengthening with `C' = C`. The density condition is
-- `subset_intrinsicClosure`, use the diagonal-extraction bridge to get pointwise
-- convergence on a dense subset `D ⊆ C`, and then apply Theorem 10.8 to the reindexed sequence
-- `fSeq ∘ φ`.
/-- Theorem 10.9, in the Chapter 10 owner ambient form: if `C` is a relatively open convex set in
a finite-dimensional normed space over `𝕜` and `f₁, f₂, …` is a sequence of finite convex
functions on `C` whose value sequence is bounded at each point of `C`, then some subsequence
converges locally uniformly on `C`, hence uniformly on every closed bounded subset of `C`, to a
finite convex function on `C`. -/
theorem
    exists_subsequence_tendstoLocallyUniformlyOn_of_convexOn_of_pointwise_bounded
    (hbounded : PointwiseBoundedOn fSeq C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : E → 𝕜,
      ConvexOn 𝕜 C f ∧
        TendstoLocallyUniformlyOn (fSeq ∘ φ) f atTop C := by
  obtain ⟨D, hD_subset, hD_dense, φ, hφ, hlimit⟩ :=
    exists_subsequence_tendsto_pointwiseOn_dense_subset
      fSeq subset_intrinsicClosure hbounded
  obtain ⟨f, hf, hloc⟩ :=
    exists_convex_tendstoLocallyUniformlyOn_of_dense_pointwise
      (fSeq ∘ φ) hC_open (fun i ↦ hf_convex (φ i)) hD_subset hD_dense hlimit
  exact ⟨φ, hφ, f, hf, hloc⟩

omit hC_open hf_convex

end
