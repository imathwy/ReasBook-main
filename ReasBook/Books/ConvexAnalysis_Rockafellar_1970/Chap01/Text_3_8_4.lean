import ConvexAnalysis_Rockafellar_1970.Chap01.Text_3_8_2
import ConvexAnalysis_Rockafellar_1970.Chap01.Proposition_2_6_12
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_3_6

-- Declarations for this item will be appended below by the statement pipeline.

section

open LinearMap
open scoped Pointwise Rockafellar

variable {E k : Type*}
variable [Field k] [PartialOrder k] [IsOrderedRing k] [PosMulReflectLT k]
  [AddCommMonoid E] [Module k E]

private def penumbraHead (C : Set E) : Set (k × E) :=
  (K[k | C] : Set (k × E)) ∩ {p : k × E | 1 ≤ p.1}

private def penumbraTail (S : Set E) : Set (k × E) :=
  {p | 1 ≤ p.1 ∧ p.2 ∈ (1 - p.1) • S}

private def penumbraLift (C S : Set E) : Set (k × E) :=
  penumbraHead C +ᶠ penumbraTail S

private theorem convex_penumbraHead {C : Set E} (hC : Convex k C) :
    Convex k (penumbraHead C : Set (k × E)) := by
  have hhalf : Convex k {p : k × E | 1 ≤ p.1} := by
    simpa using convex_halfSpace_ge (fst k k E).isLinear (1 : k)
  exact hC.homogenizationSet.inter hhalf

private def penumbraTailMap : (k × E) →ₗ[k] k × E :=
  { toFun := fun p ↦ (p.1, (-1 : k) • p.2)
    map_add' := by
      intro x y
      ext <;> simp [smul_add]
    map_smul' := by
      intro a x
      ext <;> simp [smul_smul, mul_comm] }

omit [PosMulReflectLT k] in
private theorem penumbraTail_eq (S : Set E) :
    penumbraTail S =
      ((fun p : k × E ↦ (1, (0 : E)) + p) '' (penumbraTailMap '' (K[k | S] : Set (k × E)))) := by
  ext p
  rcases p with ⟨a, y⟩
  constructor
  · rintro ⟨ha, hy⟩
    change 1 ≤ a at ha
    change y ∈ (1 - a) • S at hy
    rcases Set.mem_smul_set.mp hy with ⟨x, hx, rfl⟩
    refine ⟨(a - 1, (1 - a) • x), ?_, ?_⟩
    · refine ⟨(a - 1, (a - 1) • x), ?_, ?_⟩
      · exact ⟨sub_nonneg.mpr ha, Set.mem_smul_set.mpr ⟨x, hx, rfl⟩⟩
      · ext
        · simp [penumbraTailMap]
        · change (-1 : k) • ((a - 1) • x) = (1 - a) • x
          rw [smul_smul]
          congr 1
          ring
    · ext <;> simp
  · rintro ⟨q, hq, hp⟩
    rcases hq with ⟨⟨r, z⟩, hzK, rfl⟩
    rcases hzK with ⟨hr, hz⟩
    rcases Set.mem_smul_set.mp hz with ⟨x, hx, hzx⟩
    have ha : a = 1 + r := by
      simpa [penumbraTailMap] using (congrArg Prod.fst hp).symm
    have hy : y = (-1 : k) • z := by
      simpa [penumbraTailMap] using (congrArg Prod.snd hp).symm
    constructor
    · rw [ha]
      simpa using add_le_add_left hr (1 : k)
    · rw [ha, show 1 - (1 + r) = -r by ring]
      refine Set.mem_smul_set.mpr ⟨x, hx, ?_⟩
      calc
        (-r) • x = (-1 : k) • (r • x) := by simp [smul_smul]
        _ = (-1 : k) • z := by rw [hzx]
        _ = y := hy.symm

private theorem convex_penumbraTail {S : Set E} (hS : Convex k S) :
    Convex k (penumbraTail S : Set (k × E)) := by
  rw [penumbraTail_eq]
  exact (hS.homogenizationSet.linear_image penumbraTailMap).translate (1, (0 : E))

private theorem convex_penumbraLift {C S : Set E} (hC : Convex k C) (hS : Convex k S) :
    Convex k (penumbraLift C S : Set (k × E)) := by
  simpa [penumbraLift] using
    (convex_penumbraHead hC).fiberwiseSum (convex_penumbraTail hS)

omit [PosMulReflectLT k] in
private theorem mem_penumbraLift_iff (C S : Set E) (p : k × E) :
    p ∈ (penumbraLift C S : Set (k × E)) ↔
      1 ≤ p.1 ∧ ∃ x ∈ S, ∃ c ∈ C, p.2 = (1 - p.1) • x + p.1 • c := by
  rw [penumbraLift, Set.mem_fiberwiseSum]
  constructor
  · rintro ⟨z₁, z₂, hz₁, hz₂, hsum⟩
    rcases hz₁ with ⟨hz₁, ha⟩
    rcases hz₂ with ⟨-, hz₂⟩
    rcases hz₁ with ⟨-, hz₁⟩
    rcases Set.mem_smul_set.mp hz₁ with ⟨c, hc, hz₁⟩
    rcases Set.mem_smul_set.mp hz₂ with ⟨x, hx, hz₂⟩
    refine ⟨ha, x, hx, c, hc, ?_⟩
    calc
      p.2 = z₁ + z₂ := by simpa using hsum.symm
      _ = p.1 • c + (1 - p.1) • x := by rw [hz₁, hz₂]
      _ = (1 - p.1) • x + p.1 • c := by rw [add_comm]
  · rintro ⟨ha, x, hx, c, hc, hp⟩
    refine ⟨p.1 • c, (1 - p.1) • x, ?_, ?_, ?_⟩
    · exact ⟨⟨le_trans zero_lt_one.le ha, Set.mem_smul_set.mpr ⟨c, hc, rfl⟩⟩, ha⟩
    · exact ⟨ha, Set.mem_smul_set.mpr ⟨x, hx, rfl⟩⟩
    · simpa [add_comm] using hp.symm

omit [PosMulReflectLT k] in
private theorem penumbra_eq_snd_image_penumbraLift (C S : Set E) :
    penumbra[k | C, S] = (snd k k E) '' (penumbraLift C S : Set (k × E)) := by
  ext y
  constructor
  · intro hy
    rcases (mem_penumbra_iff_exists_affine k C S y).1 hy with ⟨x, hx, a, ha, c, hc, hy⟩
    refine ⟨(a, y), ?_, by simp⟩
    exact (mem_penumbraLift_iff C S (a, y)).2 ⟨ha, x, hx, c, hc, hy⟩
  · rintro ⟨⟨a, y'⟩, hy', rfl⟩
    rcases (mem_penumbraLift_iff C S (a, y')).1 hy' with ⟨ha, x, hx, c, hc, hy⟩
    exact (mem_penumbra_iff_exists_affine k C S y').2 ⟨x, hx, a, ha, c, hc, hy⟩

/-
Source/core/bridge triage:
- `source-facing`: Text 3.8.4 states that the source-defined set `penumbra C S` is convex when
  both `C` and `S` are convex.
- `core/canonical`: the owner abstraction is mathlib's predicate `Convex k` on subsets of a
  `k`-module, together with the chapter owners `homogenizationSet`, `+ᶠ`, and
  `Convex.linear_image` on product spaces.
- `bridge/view`: the imported source-facing definition `penumbra`, together with the owner-level
  bridge `mem_penumbra_iff` and the explicit witness bridge
  `mem_penumbra_iff_exists_affine`, provides the source-side membership views used by the private
  lift argument. The private lift `penumbraLift` is the
  fiberwise sum, over the common parameter `a`, of the clipped homogenization-set view
  `penumbraHead C` and the translated neg-second-coordinate image `penumbraTail S` of
  `homogenizationSet S`. The source-facing set is then the second projection of that convex lift.
- Primitive data vs derived API: the sets `C` and `S` together with the canonical pointwise
  scaled-set owners `p.1 • C` and `(1 - p.1) • S` are primitive; convexity of `penumbraHead C`,
  `penumbraTail S`, the lifted fiberwise sum, and finally `penumbra C S` are derived API.
- Domain-style sampling: the relevant owner-level declarations checked here are `Convex k`,
  `mem_penumbra_iff`, `mem_penumbra_iff_exists_affine`, `Convex.homogenizationSet`,
  `convex_halfSpace_ge`, `(+ᶠ)`,
  `Convex.fiberwiseSum`, `Convex.translate`, and `Convex.linear_image`. They show that
  the private lift should reuse the chapter's homogenization-set and fiberwise-sum owners rather
  than carrying parallel coordinate-level convexity proofs.
- Layer target: `source-facing`; the theorem keeps `penumbra C S` as the public object and uses
  the lifted product-space fiberwise-sum set only as a private bridge/view.
- Abstraction check (canonicalize pass):
  - Codomain/ambient over-concrete? `No`: the theorem is set-level convexity on arbitrary
    `k`-modules, not on coordinates or a concrete Euclidean model.
  - Scalar structure over-concrete? `No`: the scalar layer remains `Field k` with order axioms
    because this item reuses the upstream homogenization convexity bridge and also uses algebraic
    identities with subtraction/negation (`1 - a`, `-1`, `a - 1`) in the penumbra-tail bridge.
  - Concrete-model owner instead of intrinsic owner? `No`: the public owner is the source-facing
    `penumbra[k | C, S]` with the canonical convex predicate `Convex k`.
  - Ambient-vs-intrinsic topology mismatch? `Not applicable`: this item is not topology-facing.
  - Owner naming / notation mismatch? `No`: this file uses the short source notation
    `penumbra[k | C, S]` on theorem surfaces.
-/

/-- Text 3.8.4: if both `S` and `C` are convex, then the penumbra of `C` with respect to `S` is
convex. -/
-- Proof sketch: `penumbraHead C` is the height-`≥ 1` cut of the canonical homogenization-set
-- owner `K[k | C]`, and `penumbraTail S` is the translate by `(1, 0)` of the neg-second-coordinate
-- linear image of `K[k | S]`. Hence both lifted factors are convex by owner-level reuse of
-- `Convex.homogenizationSet`, `convex_halfSpace_ge`, `Convex.translate`, and `Convex.linear_image`.
-- The chapter owner theorem `Convex.fiberwiseSum` then gives convexity of
-- `penumbraLift C S ⊆ k × E`, and the source-facing set `penumbra C S` is its second projection.
theorem Convex.penumbra {C S : Set E} (hC : Convex k C) (hS : Convex k S) :
    Convex k (penumbra[k | C, S]) := by
  rw [penumbra_eq_snd_image_penumbraLift C S]
  simpa using (convex_penumbraLift hC hS).linear_image (snd k k E)

/-- Text 3.8.4: if both `S` and `C` are convex, then the penumbra of `C` with respect to `S` is
convex. -/
theorem convex_penumbra {C S : Set E} (hC : Convex k C) (hS : Convex k S) :
    Convex k (penumbra[k | C, S]) :=
  hC.penumbra hS

end
