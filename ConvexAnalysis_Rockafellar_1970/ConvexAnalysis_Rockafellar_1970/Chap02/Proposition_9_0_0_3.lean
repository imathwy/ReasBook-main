import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_5_7
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Rockafellar
open Function

section

variable {𝕜 : Type*} {E F : Type*}
variable [ConditionallyCompleteLinearOrder 𝕜]

variable (A : E → F) (h : E → WithTopBot 𝕜)

namespace Function

/-!
Source/core/bridge triage for this item.

- `source-facing`: the proposition considers the image `F` of the scalar epigraph of `h`
  under the map `(x, r) ↦ (A x, r)`, identifies the closure of its vertical section
  above a fixed `y` with the scalar heights above `(A ◁ h)(y)`, and records the resulting
  attainment criterion under closedness plus exclusion of the downward recession direction.
- `core/canonical`: the owner abstraction for `(Ah)(y)` is the chapter declaration
  `Function.linearImage A h` from Theorem 5.7, viewed through the owner
  `Function.verticalInfimum` on subsets of `F × 𝕜`, while recession directions are already
  organized by the chapter owner `recessionCone`.
- `bridge/view`: the textbook set `F` is the Chapter 5 bridge object
  `linearImageEpigraph A h`, and part (1) is refined to the sectionwise closure identity
  `closure (verticalSection (linearImageEpigraph A h) y) =
    verticalSection (epi (Function.linearImage A h)) y`, with the global epigraph equality
  kept only as the closed-image specialization in part (2). Part (3) is likewise stated first
  from the local section-closed hypothesis at `y`, with the global closed-image form kept as a
  derived specialization. Both parts use the owner-side effective-domain condition
  `y ∈ dom(Function.linearImage A h)`, which is equivalent to section nonemptiness by the
  vertical-infimum description from Theorem 5.7 and the effective-domain API of
  `Function.verticalInfimum`.
- Primitive data vs derived API: the primitive inputs are the map `A`, the function `h`,
  and the image set of its scalar epigraph. The sectionwise closure identity, its closed-image
  specialization, and the attainment statement are derived consequences and should remain theorem-
  level API, while any fiber-membership unpacking needed to prove them is internal.
- Ambient minimization: the primitive section-equality and attainment surfaces for parts (2) and
  (3) are order-theoretic (`WithTopBot` + `dom`) and do not require topological closure data; only
  the closure-identification bridge in part (1) and its derived closed-section specializations use
  order-topological hypotheses on `𝕜`. No topology on `F` is required at the primitive sectionwise
  layer. The concrete `R^n → R^m` display model is therefore demoted to a downstream
  specialization.

Domain-style sampling used here:
- `Function.verticalInfimum`;
- `Function.linearImage`;
- `linearImageEpigraph`;
- `Function.linearImage_eq_sInf_image`;
- `Function.linearImage_eq_verticalInfimum_linearImageEpigraph`;
- `recessionCone`.
-/

/-!
Sectionwise API for Proposition 9.0.0.3 (2) and (3), with closedness and global-closedness
specializations below.
-/

/-- Primitive sectionwise owner bridge for Proposition 9.0.0.3 (2): if every scalar section of
`linearImageEpigraph A h` agrees with the corresponding section of `epi (A ◁ h)`, then the two
sets are equal. -/
theorem linearImageEpigraph_eq_epi_linearImage_of_sections_eq
    (hsection_eq :
      ∀ y : F,
        verticalSection (linearImageEpigraph A h) y =
          verticalSection (epi (A ◁ h)) y) :
    linearImageEpigraph A h = epi (A ◁ h) := by
  ext p
  change p.2 ∈ verticalSection (linearImageEpigraph A h) p.1 ↔
    p.2 ∈ verticalSection (epi (A ◁ h)) p.1
  simpa [hsection_eq p.1]

/-- Primitive sectionwise attainment bridge for Proposition 9.0.0.3 (3): if the scalar section of
`linearImageEpigraph A h` above `y` agrees with the section of `epi (A ◁ h)` and `(A ◁ h) y` is
finite and not `⊥`, then the infimum value is attained along the fiber `A x = y`. -/
theorem linearImage_attains_of_section_eq_of_ne_bot_of_mem_dom
    (y : F)
    (hsection_eq :
      verticalSection (linearImageEpigraph A h) y =
        verticalSection (epi (A ◁ h)) y)
    (hy : y ∈ dom(A ◁ h))
    (hy_ne_bot : (A ◁ h) y ≠ ⊥) :
    ∃ x : E, A x = y ∧ h x = (A ◁ h) y := by
  have hy_ne_top : (A ◁ h) y ≠ ⊤ := ne_of_lt hy
  lift (A ◁ h) y to 𝕜 using ⟨hy_ne_top, hy_ne_bot⟩ with μ hμ
  have hμ_mem_epi : (y, μ) ∈ epi (A ◁ h) := by
    simp [hμ]
  have hμ_mem_section : μ ∈ verticalSection (linearImageEpigraph A h) y := by
    rw [hsection_eq]
    simpa [verticalSection] using hμ_mem_epi
  have hμ_mem_image : (y, μ) ∈ linearImageEpigraph A h := by
    simpa [verticalSection] using hμ_mem_section
  rcases (mem_linearImageEpigraph_iff A h).1 hμ_mem_image with ⟨x, hxy, hx_le⟩
  have hfx_le_hx : (A ◁ h) y ≤ h x := by
    rw [linearImage_eq_sInf_image]
    exact sInf_le ⟨x, hxy, rfl⟩
  have hμ_le_hx : (μ : WithTopBot 𝕜) ≤ h x := by
    simpa [hμ] using hfx_le_hx
  have hhx_eq_hμ : h x = (μ : WithTopBot 𝕜) := le_antisymm hx_le hμ_le_hx
  exact ⟨x, hxy, hhx_eq_hμ⟩

section

variable [TopologicalSpace 𝕜] [OrderTopology 𝕜] [DenselyOrdered 𝕜]
variable [NoBotOrder 𝕜] [NoMaxOrder 𝕜]

/-- Proposition 9.0.0.3 (1): for a fixed base point `y`, the closure of the vertical section of
the image set `F` of the scalar epigraph of `h` under `(x, r) ↦ (A x, r)` is exactly the
corresponding vertical section of `epi (A ◁ h)`. -/
theorem closure_section_linearImageEpigraph_eq_section_epi_linearImage
    (y : F) :
    closure (verticalSection (linearImageEpigraph A h) y) =
      verticalSection (epi (A ◁ h)) y := by
  have hupper :
      ∀ {μ ν : 𝕜}, μ ∈ verticalSection (linearImageEpigraph A h) y → μ ≤ ν →
        ν ∈ verticalSection (linearImageEpigraph A h) y := by
    intro μ ν hμ hμν
    rcases (mem_linearImageEpigraph_iff A h).1 (by simpa [verticalSection] using hμ) with
      ⟨x, hxy, hxμ⟩
    have hν : (y, ν) ∈ linearImageEpigraph A h :=
      (mem_linearImageEpigraph_iff A h).2 ⟨x, hxy, le_trans hxμ (by simpa using hμν)⟩
    simpa [verticalSection] using hν
  simpa [linearImage_eq_verticalInfimum_linearImageEpigraph, verticalSection, Set.preimage,
    Set.Ici] using
    (closure_verticalSection_eq_preimage_Ici_of_upward_closed
      (F := linearImageEpigraph A h) (x := y) hupper)

/-- Proposition 9.0.0.3 (2), closed-section specialization: if every scalar section
`verticalSection (linearImageEpigraph A h) y` is closed, then the image epigraph equals
`epi (A ◁ h)`. -/
theorem linearImageEpigraph_eq_epi_linearImage_of_sections_closed
    (hsection_closed :
      ∀ y : F, IsClosed (verticalSection (linearImageEpigraph A h) y)) :
    linearImageEpigraph A h = epi (A ◁ h) := by
  refine linearImageEpigraph_eq_epi_linearImage_of_sections_eq (A := A) (h := h) ?_
  intro y
  rw [← (hsection_closed y).closure_eq,
    closure_section_linearImageEpigraph_eq_section_epi_linearImage A h y]

/-- Proposition 9.0.0.3 (3), closed-section specialization: if the section
`verticalSection (linearImageEpigraph A h) y` is closed and `(A ◁ h) y` is finite and not `⊥`,
then the infimum value `(A ◁ h) y` is attained
by some point in the fiber `A x = y`.

The source-facing no-downward-recession hypothesis is a global recognition criterion that implies
this local non-`⊥` premise in typical convex-closed settings; the attainment mechanism itself only
needs the local premise. -/
theorem linearImage_attains_of_section_closed_of_ne_bot_of_mem_dom
    (y : F)
    (hsection_closed : IsClosed (verticalSection (linearImageEpigraph A h) y))
    (hy : y ∈ dom(A ◁ h))
    (hy_ne_bot : (A ◁ h) y ≠ ⊥) :
    ∃ x : E, A x = y ∧ h x = (A ◁ h) y := by
  refine linearImage_attains_of_section_eq_of_ne_bot_of_mem_dom (A := A) (h := h) y ?_ hy hy_ne_bot
  rw [← hsection_closed.closure_eq,
    closure_section_linearImageEpigraph_eq_section_epi_linearImage A h y]

section

variable [TopologicalSpace F]

/-- If `linearImageEpigraph A h` is closed, then Proposition 9.0.0.3 (2) identifies it
directly with the scalar epigraph of `A ◁ h`. -/
theorem linearImageEpigraph_eq_epi_linearImage
    (hF_closed : IsClosed (linearImageEpigraph A h)) :
    linearImageEpigraph A h = epi (A ◁ h) := by
  refine linearImageEpigraph_eq_epi_linearImage_of_sections_closed (A := A) (h := h) ?_
  intro y
  simpa [verticalSection] using hF_closed.preimage (Continuous.prodMk_right y)

/-- Proposition 9.0.0.3 (3), closed-image specialization of
`linearImage_attains_of_section_closed_of_ne_bot_of_mem_dom`. -/
theorem linearImage_attains_of_closed_imageEpigraph_of_ne_bot_of_mem_dom
    (y : F)
    (hF_closed : IsClosed (linearImageEpigraph A h))
    (hy : y ∈ dom(A ◁ h))
    (hy_ne_bot : (A ◁ h) y ≠ ⊥) :
    ∃ x : E, A x = y ∧ h x = (A ◁ h) y := by
  refine linearImage_attains_of_section_closed_of_ne_bot_of_mem_dom
    (A := A) (h := h) y ?_ hy hy_ne_bot
  simpa [verticalSection] using hF_closed.preimage (Continuous.prodMk_right y)

end

end

end Function

end
