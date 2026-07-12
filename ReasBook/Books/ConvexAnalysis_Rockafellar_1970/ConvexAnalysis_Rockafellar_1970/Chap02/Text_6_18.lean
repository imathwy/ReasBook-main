import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_8
import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

section IntrinsicInterior

open scoped Rockafellar

/- Rockafellar's scalar-annotated notation for intrinsic closure, used on theorem surfaces. -/
local notation "cl[" 𝕜 "](" C ")" => intrinsicClosure 𝕜 C

variable
    {𝕜 V W P Q : Type*}
    [Ring 𝕜]
    [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P]
    [AddCommGroup W] [Module 𝕜 W] [AddTorsor W Q]

/-
Source/core/bridge triage:
- `source-facing`: Text 6.18 states that for the direct sum of two convex sets, relative interiors
  and closures factor as direct sums of the corresponding relative interiors and closures.
- `core/canonical`: by Text 3.5.1, the direct sum is the Cartesian product `×ˢ`; the owner-side
  notions are `intrinsicInterior 𝕜` for relative interior and `closure` for topological closure.
- `bridge/view`: the source's coordinate realization `R^m ⊕ R^p` is demoted to the invariant
  product-space notion on arbitrary product topological affine spaces; no surrogate wrapper for a
  specific `R^(m+p)` model is introduced.
- Primitive data vs derived API: no new data is being defined; both clauses are direct statements
  about existing owner operations on sets.
- Domain-style sampling used here: `intrinsicInterior`, `AffineSubspace.map_span`,
  `Homeomorph.Set.prod`, `interior_prod_eq`, and `closure_prod_eq`.
- Best owner abstraction: `intrinsicInterior` and `closure` are already the canonical owners in
  this domain. No exact upstream theorem with the target interface for products was found for
  `intrinsicInterior`, so clause (1) remains the minimal local `bridge/view` theorem on that owner
  surface and is stated at the owner definition's ambient level, while clause (2) is exact owner
  reuse via `closure_prod_eq`.
- Semantic note: the closure identity is completely general, so the convexity adjectives in the
  source are redundant there. The same product formula is expected for `intrinsicInterior`, whose
  owner notion is defined for arbitrary subsets as well.
-/

/-- Internal bridge: the affine span of a Cartesian product is the product of affine spans. -/
private theorem affineSpan_prod_eq (s : Set P) (t : Set Q) :
    (affineSpan 𝕜 (s ×ˢ t) : Set (P × Q)) =
      (affineSpan 𝕜 s : Set P) ×ˢ (affineSpan 𝕜 t : Set Q) := by
  ext p
  constructor
  · intro hp
    exact affineSpan_induction hp
      (fun q hq ↦ ⟨subset_affineSpan 𝕜 s hq.1, subset_affineSpan 𝕜 t hq.2⟩)
      (fun c u v w hu hv hw ↦
        ⟨(affineSpan 𝕜 s).smul_vsub_vadd_mem c hu.1 hv.1 hw.1,
          (affineSpan 𝕜 t).smul_vsub_vadd_mem c hu.2 hv.2 hw.2⟩)
  · intro hp
    rcases Set.eq_empty_or_nonempty s with rfl | hs
    · simpa using hp.1
    rcases Set.eq_empty_or_nonempty t with rfl | ht
    · simpa using hp.2
    rcases hs with ⟨x0, hx0⟩
    rcases ht with ⟨y0, hy0⟩
    have hleft : ∀ {x : P}, x ∈ affineSpan 𝕜 s → (x, y0) ∈ affineSpan 𝕜 (s ×ˢ t) := by
      intro x hx
      let f : P →ᵃ[𝕜] P × Q := (AffineMap.id 𝕜 P).prod (AffineMap.const 𝕜 P y0)
      have hmem : (x, y0) ∈ AffineSubspace.map f (affineSpan 𝕜 s) := by
        rw [AffineSubspace.mem_map]
        exact ⟨x, hx, rfl⟩
      have himage : (x, y0) ∈ affineSpan 𝕜 (f '' s) := by
        simpa [f, AffineSubspace.map_span] using hmem
      exact
        (affineSpan_mono 𝕜 (by
          rintro _ ⟨z, hz, rfl⟩
          exact ⟨hz, hy0⟩)) himage
    have hright : ∀ {y : Q}, y ∈ affineSpan 𝕜 t → (x0, y) ∈ affineSpan 𝕜 (s ×ˢ t) := by
      intro y hy
      let g : Q →ᵃ[𝕜] P × Q := (AffineMap.const 𝕜 Q x0).prod (AffineMap.id 𝕜 Q)
      have hmem : (x0, y) ∈ AffineSubspace.map g (affineSpan 𝕜 t) := by
        rw [AffineSubspace.mem_map]
        exact ⟨y, hy, rfl⟩
      have himage : (x0, y) ∈ affineSpan 𝕜 (g '' t) := by
        simpa [g, AffineSubspace.map_span] using hmem
      exact
        (affineSpan_mono 𝕜 (by
          rintro _ ⟨z, hz, rfl⟩
          exact ⟨hx0, hz⟩)) himage
    have hp1 : (p.1, y0) ∈ affineSpan 𝕜 (s ×ˢ t) := hleft hp.1
    have hp2 : (x0, y0) ∈ affineSpan 𝕜 (s ×ˢ t) := subset_affineSpan 𝕜 (s ×ˢ t) ⟨hx0, hy0⟩
    have hp3 : (x0, p.2) ∈ affineSpan 𝕜 (s ×ˢ t) := hright hp.2
    have hcomb : (1 : 𝕜) • ((p.1, y0) -ᵥ (x0, y0)) +ᵥ (x0, p.2) ∈ affineSpan 𝕜 (s ×ˢ t) := by
      exact (affineSpan 𝕜 (s ×ˢ t)).smul_vsub_vadd_mem 1 hp1 hp2 hp3
    simpa using hcomb

variable [TopologicalSpace P] [TopologicalSpace Q]

private def affineSpanProdHomeomorph (s : Set P) (t : Set Q) :
    affineSpan 𝕜 (s ×ˢ t) ≃ₜ affineSpan 𝕜 s × affineSpan 𝕜 t :=
  (Homeomorph.setCongr (affineSpan_prod_eq s t)).trans
    (Homeomorph.Set.prod (affineSpan 𝕜 s : Set P) (affineSpan 𝕜 t : Set Q))

private theorem affineSpanProdHomeomorph_image_preimage (s : Set P) (t : Set Q) :
    affineSpanProdHomeomorph s t ''
      (((↑) : affineSpan 𝕜 (s ×ˢ t) → P × Q) ⁻¹' (s ×ˢ t)) =
      (((↑) : affineSpan 𝕜 s → P) ⁻¹' s) ×ˢ (((↑) : affineSpan 𝕜 t → Q) ⁻¹' t) := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa [affineSpanProdHomeomorph] using hw
  · intro hz
    refine ⟨(affineSpanProdHomeomorph s t).symm z, ?_,
      (affineSpanProdHomeomorph s t).apply_symm_apply z⟩
    simpa [affineSpanProdHomeomorph] using hz

private theorem affineSpanProdHomeomorph_symm_image (s : Set P) (t : Set Q) :
    (affineSpanProdHomeomorph s t).symm ''
      ((((↑) : affineSpan 𝕜 s → P) ⁻¹' s) ×ˢ (((↑) : affineSpan 𝕜 t → Q) ⁻¹' t)) =
      (((↑) : affineSpan 𝕜 (s ×ˢ t) → P × Q) ⁻¹' (s ×ˢ t)) := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa [affineSpanProdHomeomorph] using hw
  · intro hz
    refine ⟨affineSpanProdHomeomorph s t z, ?_,
      (affineSpanProdHomeomorph s t).symm_apply_apply z⟩
    simpa [affineSpanProdHomeomorph] using hz

/-- Canonical owner form of Text 6.18 (1): relative interior of a Cartesian product is the
product of relative interiors. -/
-- Proof sketch: rewrite relative interior as ordinary interior inside the affine span, use that
-- the affine span of a product factors as the product of the affine spans, and then apply
-- `interior_prod_eq` in that product affine-span model.
@[simp] theorem intrinsicInterior_prod_eq (s : Set P) (t : Set Q) :
    intrinsicInterior 𝕜 (s ×ˢ t) = intrinsicInterior 𝕜 s ×ˢ intrinsicInterior 𝕜 t := by
  ext p
  simp only [mem_intrinsicInterior, Set.mem_prod]
  constructor
  · rintro ⟨x, hx, rfl⟩
    let e : affineSpan 𝕜 (s ×ˢ t) ≃ₜ affineSpan 𝕜 s × affineSpan 𝕜 t :=
      affineSpanProdHomeomorph s t
    have hx_pair :
        e x ∈
          interior (((↑) : affineSpan 𝕜 s → P) ⁻¹' s) ×ˢ
            interior (((↑) : affineSpan 𝕜 t → Q) ⁻¹' t) := by
      have hx' : e x ∈ interior ((((↑) : affineSpan 𝕜 s → P) ⁻¹' s) ×ˢ
          (((↑) : affineSpan 𝕜 t → Q) ⁻¹' t)) := by
        have hx'' : e x ∈ e '' interior (((↑) : affineSpan 𝕜 (s ×ˢ t) → P × Q) ⁻¹' (s ×ˢ t)) := by
          exact ⟨x, hx, rfl⟩
        rw [e.image_interior, affineSpanProdHomeomorph_image_preimage] at hx''
        exact hx''
      simpa [interior_prod_eq] using hx'
    exact
      ⟨⟨(e x).1, hx_pair.1, rfl⟩,
        ⟨(e x).2, hx_pair.2, rfl⟩⟩
  · rintro ⟨⟨ys, hys, hys_eq⟩, ⟨yt, hyt, hyt_eq⟩⟩
    let e : affineSpan 𝕜 (s ×ˢ t) ≃ₜ affineSpan 𝕜 s × affineSpan 𝕜 t :=
      affineSpanProdHomeomorph s t
    let z : affineSpan 𝕜 s × affineSpan 𝕜 t := (ys, yt)
    have hz :
        z ∈
          interior ((((↑) : affineSpan 𝕜 s → P) ⁻¹' s) ×ˢ (((↑) : affineSpan 𝕜 t → Q) ⁻¹' t)) := by
      simpa [z, interior_prod_eq] using ⟨hys, hyt⟩
    have hx :
        e.symm z ∈
          interior (((↑) : affineSpan 𝕜 (s ×ˢ t) → P × Q) ⁻¹' (s ×ˢ t)) := by
      have hz' : e.symm z ∈ e.symm '' interior
          ((((↑) : affineSpan 𝕜 s → P) ⁻¹' s) ×ˢ (((↑) : affineSpan 𝕜 t → Q) ⁻¹' t)) := by
        exact ⟨z, hz, rfl⟩
      rw [e.symm.image_interior, affineSpanProdHomeomorph_symm_image] at hz'
      exact hz'
    refine ⟨e.symm z, hx, ?_⟩
    calc
      ↑(e.symm z) = ((ys : P), (yt : Q)) := rfl
      _ = p := by
        ext <;> simp [hys_eq, hyt_eq]

/-- Text 6.18 (1), textbook notation surface: `ri[𝕜](·)` of a Cartesian product is the product of
relative interiors. -/
@[simp] theorem ri_prod_eq (s : Set P) (t : Set Q) :
    ri[𝕜](s ×ˢ t) = ri[𝕜](s) ×ˢ ri[𝕜](t) := by
  exact intrinsicInterior_prod_eq (𝕜 := 𝕜) (s := s) (t := t)

/-- Intrinsic-closure companion to Text 6.18 on the textbook notation surface: the intrinsic
closure of a Cartesian product is the product of the intrinsic closures. -/
@[simp] theorem intrinsicClosure_prod_eq (s : Set P) (t : Set Q) :
    cl[𝕜](s ×ˢ t) = cl[𝕜](s) ×ˢ cl[𝕜](t) := by
  rw [intrinsicClosure_eq_closure_inter_affineSpan,
    intrinsicClosure_eq_closure_inter_affineSpan,
    intrinsicClosure_eq_closure_inter_affineSpan,
    closure_prod_eq, affineSpan_prod_eq]
  ext p
  simp [and_left_comm, and_assoc]

end IntrinsicInterior

section Closure

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/- Text 6.18 (2): the closure of the direct sum of two subsets, identified with the Cartesian
product `×ˢ`, is the product of their closures; this is the canonical theorem `closure_prod_eq`,
stated at its natural topological level. -/
recall closure_prod_eq

end Closure
