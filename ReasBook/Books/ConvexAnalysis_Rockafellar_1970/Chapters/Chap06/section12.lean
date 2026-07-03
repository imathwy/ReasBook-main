import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_6_12 (from Chap02) -/
open scoped Rockafellar

section

variable {𝕜 V P : Type*}
variable [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace P] [AddTorsor V P]

/-
Source/core/bridge triage:
- `source-facing`: Text 6.12 asserts that for a full-dimensional set, the relative
  interior agrees with the ordinary interior.
- `core/canonical`: mathlib's owner notions are `intrinsicInterior`, `interior`, and `affineSpan`.
- `bridge/view`: the theorem below is the intrinsic affine-topological bridge from textbook
  full-dimensional phrasing to the canonical owner API.
  After `affineSpan 𝕜 C = ⊤`, the proof passes through
  the canonical affine-span/top bridge `AffineSubspace.top_coe` and the ambient-space homeomorphism
  `Homeomorph.Set.univ`.
- Primitive data vs derived API: no new data is introduced. The convexity adjective in the prose is
  redundant for this conclusion once `affineSpan 𝕜 C = ⊤`, so it is omitted from the public header.
- Domain-style sampling: this item is guided by mathlib's `intrinsicInterior`,
  `AffineSubspace.top_coe`, `Homeomorph.Set.univ`, and the affine-span owner `affineSpan`.
- Layer target: the main labeled entry is `bridge/view`.
-/

/-- Text 6.12, on the scalar-generic affine owner layer: if a subset of an affine space is
full-dimensional, in the sense that `affineSpan 𝕜 C = ⊤`, then its relative interior is its
ordinary interior. -/
-- Proof sketch: after rewriting `affineSpan 𝕜 C = ⊤`, `intrinsicInterior 𝕜 C` becomes the image
-- of the interior of the preimage of `C` in the subtype over `Set.univ`. The canonical
-- homeomorphism `Homeomorph.Set.univ P` identifies that subtype with the ambient space, so the
-- interior transports directly to `interior C`.
theorem intrinsicInterior_eq_interior_of_affineSpan_eq_top {C : Set P}
    (hC : affineSpan 𝕜 C = ⊤) :
    ri[𝕜](C) = interior C := by
  rw [intrinsicInterior, hC]
  simpa [AffineSubspace.top_coe] using
    (Homeomorph.Set.univ P).image_interior
      (((↑) : ↥(Set.univ : Set P) → P) ⁻¹' C : Set ↥(Set.univ : Set P))

end

section

variable {𝕜 : Type*}
  [TopologicalSpace 𝕜] [LinearOrder 𝕜] [Ring 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜]

open AffineMap

/-- Over a densely linearly ordered ring with its order topology, the relative
interior of a closed upper ray is its open upper ray. -/
theorem ri_Ici (a : 𝕜) :
    ri[𝕜](Set.Ici a) = Set.Ioi a := by
  have hspan : affineSpan 𝕜 (Set.Ici a : Set 𝕜) = ⊤ := by
    refine top_unique ?_
    intro x _
    have ha : a ∈ affineSpan 𝕜 (Set.Ici a : Set 𝕜) :=
      subset_affineSpan 𝕜 (Set.Ici a : Set 𝕜) (by simp)
    have ha1 : a + 1 ∈ affineSpan 𝕜 (Set.Ici a : Set 𝕜) :=
      subset_affineSpan 𝕜 (Set.Ici a : Set 𝕜) (by
        refine le_add_of_nonneg_right ?_
        exact zero_le_one)
    have hx : lineMap a (a + 1) (x - a) = x := by
      simp only [lineMap_apply_ring]
      noncomm_ring
    rw [← hx]
    exact lineMap_mem (x - a) ha ha1
  rw [intrinsicInterior_eq_interior_of_affineSpan_eq_top hspan]
  exact interior_Ici' (a := a) Set.nonempty_Iio

/-- Upper-ray bridge on the `WithTopBot` codomain layer used by epigraph fibers: on the scalar
domain, the closed and open scalar-fiber rays at level `a` are
`{r : 𝕜 | a ≤ r}` and `{r : 𝕜 | a < r}`. Their relative interior relation is obtained by
case-splitting `a` into `⊥`, `↑t`, and `⊤`, reducing the finite case to `ri_Ici`. -/
theorem ri_preimage_coe_Ici (a : WithTopBot 𝕜) :
    ri[𝕜]({r : 𝕜 | a ≤ r}) = {r : 𝕜 | a < r} := by
  refine WithTop.recTopCoe ?htop ?hbotOrFinite a
  · have htop_i :
        ({r : 𝕜 | (⊤ : WithTopBot 𝕜) ≤ r} : Set 𝕜) = ∅ := by
      ext r
      simp
    have htop_o :
        ({r : 𝕜 | (⊤ : WithTopBot 𝕜) < r} : Set 𝕜) = ∅ := by
      ext r
      simp
    rw [htop_i, htop_o]
    simp [intrinsicInterior]
  · intro b
    refine WithBot.recBotCoe ?hbot ?hfinite b
    · have hri_univ : ri[𝕜]((Set.univ : Set 𝕜)) = Set.univ := by
        simp [intrinsicInterior, AffineSubspace.span_univ]
      have hbot_i :
          ({r : 𝕜 | (((⊥ : WithBot 𝕜) : WithTopBot 𝕜) ≤ r)} : Set 𝕜) = Set.univ := by
        ext r
        simp
      have hbot_o :
          ({r : 𝕜 | (((⊥ : WithBot 𝕜) : WithTopBot 𝕜) < r)} : Set 𝕜) = Set.univ := by
        ext r
        constructor
        · intro _
          trivial
        · intro _
          exact (WithTop.coe_lt_coe).2 (WithBot.bot_lt_coe r)
      rw [hbot_i, hbot_o]
      exact hri_univ
    · intro t
      have hcoe_i :
          ({r : 𝕜 | (((t : WithBot 𝕜) : WithTopBot 𝕜) ≤ r)} : Set 𝕜) = Set.Ici t := by
        ext r
        simp
      have hcoe_o :
          ({r : 𝕜 | (((t : WithBot 𝕜) : WithTopBot 𝕜) < r)} : Set 𝕜) = Set.Ioi t := by
        ext r
        simp
      rw [hcoe_i, hcoe_o]
      exact ri_Ici t

end
