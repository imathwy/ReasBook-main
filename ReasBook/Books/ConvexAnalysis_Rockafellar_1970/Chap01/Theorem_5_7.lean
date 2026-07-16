import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_5_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

section

variable {E : Type u} {F : Type v} {α : Type*}
variable [InfSet α]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 5.7 has two clauses. The first says that precomposition of a convex
  function with a linear transformation preserves convexity. The second says that the textbook
  image operation `Ah`, defined by taking the infimum of `h` over the fiber `A x = y`, is convex.
- `core/canonical`: the chapter owner declarations already live upstream: `Function.IsConvex` in
  Theorem 4.2, the chapter epigraph owner `epi` from Definition 4.1, and
  `Function.verticalInfimum` together with `Function.isConvex_verticalInfimum` in Theorem 5.3.
- `bridge/view`: the second clause is proved by identifying the source-facing fiberwise infimum
  `Function.linearImage A h` with the vertical infimum of the linear image of the scalar epigraph
  of `h` under `(x, μ) ↦ (A x, μ)`.
- Primitive data vs derived API: the map `A` and the functions `g`, `h` are primitive, and
  the source-facing function `Function.linearImage A h` and the bridge set
  `Function.linearImageEpigraph A h` are the new public objects here; the convexity assertions
  and the owner-side identification with `Function.verticalInfimum` are derived consequences of
  the upstream owner declarations.
- Ambient minimization: the owner `Function.linearImage` itself lives on arbitrary maps with only
  codomain infimum structure, while the convexity clauses keep the linear/module assumptions they
  actually use. No coordinates, Euclidean structure, or finite dimensionality enter these public
  declarations, and the textbook `R^n → R^m` presentation is treated as a specialization.

Domain-style sampling used here:
- `Function.IsConvex`;
- `epi`;
- `Function.verticalInfimum`;
- `Function.linearImageEpigraph`;
- `Function.IsConvex.comp_linearMap`;
- `Convex.linear_preimage`;
- `Convex.linear_image`;
- `LinearMap.prodMap`;
- `Function.isConvex_verticalInfimum`.
- Layer target: `source-facing` for the public declarations `Function.linearImage`,
  `Function.IsConvex.comp_linearMap`, and `Function.isConvex_linearImage`; `bridge/view` for the
  public set `Function.linearImageEpigraph A h` and the identification of `Function.linearImage A h`
  with the owner-side `Function.verticalInfimum` of that image set.
-/

namespace Function

/-- The textbook operation `Ah` attached to a map `A : E → F` and a function `h` on `E`,
obtained by taking the infimum of `h` along each fiber `{x | A x = y}`.
The source's extended-real-valued `R^n → R^m` case is a specialization.
Empty fibers contribute `sInf ∅` in the codomain. -/
def linearImage (A : E → F) (h : E → α) : F → α :=
  fun y ↦ sInf (h '' {x : E | A x = y})

end Function

end

scoped[Rockafellar] infixr:65 " ◁ " => Function.linearImage

open scoped Rockafellar
open Function

section

variable {𝕜 : Type w} {E : Type u} {F : Type v}
variable [LE 𝕜]

namespace Function

/-- Intrinsic epigraph-side relation for `Function.linearImage A h`: a pair `(y, μ)` belongs to
`linearImageEpigraph A h` iff some fiber point `x` with `A x = y` satisfies `h x ≤ μ`. -/
def linearImageEpigraph (A : E → F) (h : E → WithTopBot 𝕜) : Set (F × 𝕜) :=
  {p : F × 𝕜 | ∃ x : E, A x = p.1 ∧ h x ≤ (p.2 : WithTopBot 𝕜)}

/-- Membership in `linearImageEpigraph A h` means that some point of the fiber `A x = y`
has `h`-value at most the displayed scalar height. -/
theorem mem_linearImageEpigraph_iff
    (A : E → F) (h : E → WithTopBot 𝕜) {y : F} {μ : 𝕜} :
    (y, μ) ∈ linearImageEpigraph A h ↔ ∃ x : E, A x = y ∧ h x ≤ (μ : WithTopBot 𝕜) :=
  Iff.rfl

/-- Bridge to the concrete map-image view: `linearImageEpigraph A h` is exactly the image of
`epi h` under `(x, μ) ↦ (A x, μ)`. -/
theorem linearImageEpigraph_eq_image_epi_map
    (A : E → F) (h : E → WithTopBot 𝕜) :
    linearImageEpigraph A h = (fun p : E × 𝕜 ↦ (A p.1, p.2)) '' epi h := by
  ext p
  rcases p with ⟨y, μ⟩
  constructor
  · rintro ⟨x, hAy, hxμ⟩
    refine ⟨(x, μ), ?_, ?_⟩
    · exact mem_epi_restrict_iff.mpr ⟨by simp, hxμ⟩
    simp [hAy]
  · rintro ⟨⟨x, r⟩, hp, hxy⟩
    rcases mem_epi_restrict_iff.mp hp with ⟨_, hxr⟩
    rcases Prod.mk.inj hxy with ⟨hAy, hrμ⟩
    subst hrμ
    exact ⟨x, hAy, hxr⟩

section LinearMapBridge

variable [Semiring 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]
variable [AddCommMonoid F] [Module 𝕜 F]

/-- Linear-map specialization of `linearImageEpigraph_eq_image_epi_map`. -/
theorem linearImageEpigraph_eq_image_epi
    (A : E →ₗ[𝕜] F) (h : E → WithTopBot 𝕜) :
    linearImageEpigraph A h = (A.prodMap LinearMap.id) '' epi h := by
  simpa [LinearMap.prodMap_apply] using
    (linearImageEpigraph_eq_image_epi_map (A := (A : E → F)) (h := h))

end LinearMapBridge

end Function

end

section

variable {E : Type u} {F : Type v} {α : Type*}
variable [InfSet α]

namespace Function

-- Proof sketch: unfold `Function.linearImage` and `Function.verticalInfimum`. A point `(y, μ)` lies
-- in the displayed image exactly when there exists `x` with `A x = y` and `(x, μ)` in the scalar
-- epigraph of `h`, i.e. `h x ≤ μ`. Taking the infimum over those heights is the same as taking
-- the infimum of the fiber values `h x`.
/-- The value of `Function.linearImage A h` at `y` is the infimum of the values `h x` over the
fiber `A x = y`, in the textbook sense of `Ah(y) = inf {h(x) | A x = y}`. -/
theorem linearImage_eq_sInf_image (A : E → F) (h : E → α) (y : F) :
    (A ◁ h) y = sInf (h '' {x : E | A x = y}) := rfl

end Function

end

section

variable {E : Type u} {F : Type v} {α : Type*}
variable [ConditionallyCompleteLattice α]

namespace Function

-- Proof sketch: for an equivalence `A`, the fiber `{x | A x = y}` is the singleton
-- `{A.symm y}`. The source-facing fiberwise infimum defining `Function.linearImage` therefore
-- collapses to the singleton infimum `h (A.symm y)`, which is exactly composition by `A.symm`.
/-- For an invertible map `A`, the textbook image operation `Ah` is just composition with
the inverse map. -/
theorem linearImage_eq_comp_symm
    (A : E ≃ F) (h : E → α) :
    (A ◁ h) = h ∘ A.symm := by
  funext y
  rw [linearImage_eq_sInf_image]
  have hfiber : {x : E | A x = y} = {A.symm y} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    simpa using (A.apply_eq_iff_eq_symm_apply : A x = y ↔ x = A.symm y)
  rw [hfiber, Set.image_singleton, csInf_singleton]
  simp [Function.comp]

end Function

end

section

variable {𝕜 : Type w} {E : Type u} {F : Type v}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]
variable [AddCommMonoid F] [Module 𝕜 F]

-- Proof sketch: view the scalar epigraph of `g ∘ A` as the preimage of the scalar epigraph of `g`
-- under the linear map `(x, μ) ↦ (A x, μ)`. Since linear preimages of convex sets are convex, the
-- epigraph criterion from Theorem 4.2 gives convexity of `g ∘ A`.
namespace Function

/-- Theorem 5.7 (1): if `A : E → F` is linear and `g` is convex on `F`, then the composite `gA`,
defined by `x ↦ g (A x)`, is convex on `E`. The textbook `R^n → R^m` statement is the Euclidean
specialization. -/
theorem IsConvex.comp_linearMap
    {g : F → WithTopBot 𝕜} (hg : g.IsConvex 𝕜) (A : E →ₗ[𝕜] F) :
    (g ∘ A).IsConvex 𝕜 := by
  rw [isConvex_iff_convex_epigraph]
  simpa [LinearMap.prodMap_apply] using
    hg.convex_epigraph.linear_preimage (A.prodMap LinearMap.id)

end Function

end

section

variable {𝕜 : Type w} {E : Type u} {F : Type v}
variable [ConditionallyCompleteLinearOrder 𝕜] [NoBotOrder 𝕜]

/-- The image function `Ah` is the vertical-infimum function of the image of the scalar epigraph
of `h` under `(x, μ) ↦ (A x, μ)`. -/
theorem Function.linearImage_eq_verticalInfimum_linearImageEpigraph
    (A : E → F) (h : E → WithTopBot 𝕜) :
    A ◁ h = verticalInfimum (linearImageEpigraph A h) := by
  ext y
  rw [Function.linearImage_eq_sInf_image, verticalInfimum_eq_sInf]
  set T : Set (WithTopBot 𝕜) :=
    (((↑) : 𝕜 → WithTopBot 𝕜) '' {μ : 𝕜 | (y, μ) ∈ linearImageEpigraph A h})
  apply le_antisymm
  · refine le_sInf ?_
    rintro _ ⟨μ, hμ, rfl⟩
    rcases (mem_linearImageEpigraph_iff A h).1 hμ with ⟨x, hAy, hxμ⟩
    exact
      (sInf_le (show h x ∈ h '' {x : E | A x = y} from ⟨x, hAy, rfl⟩)).trans hxμ
  · refine le_sInf ?_
    rintro _ ⟨x, hAy, rfl⟩
    by_cases hbot : h x = (⊥ : WithTopBot 𝕜)
    · have hall : ∀ μ : 𝕜, (μ : WithTopBot 𝕜) ∈ T := by
        intro μ
        exact ⟨μ, (mem_linearImageEpigraph_iff A h).2 ⟨x, hAy, by simp [hbot]⟩, rfl⟩
      have hlt :
          ∀ a : 𝕜, sInf T < a := by
        intro a
        letI : NoMinOrder 𝕜 := NoBotOrder.to_noMinOrder 𝕜
        rcases exists_lt a with ⟨b, hb⟩
        exact lt_of_le_of_lt
          (sInf_le (hall b))
          (WithTop.coe_lt_coe.mpr (WithBot.coe_lt_coe.mpr hb))
      have hsInf_eq_bot :
          sInf T = (⊥ : WithTopBot 𝕜) := by
        induction hs : sInf T using WithTop.recTopCoe with
        | top =>
            have h := hlt (Classical.arbitrary 𝕜)
            rw [hs] at h
            exact (WithTop.not_top_le_coe _ (le_of_lt h)).elim
        | coe z =>
            induction z using WithBot.recBotCoe with
            | bot => simpa using hs
            | coe r =>
                have h := hlt r
                rw [hs] at h
                exact (lt_irrefl _ h).elim
      simpa [hbot] using hsInf_eq_bot.le
    · by_cases htop : h x = (⊤ : WithTopBot 𝕜)
      · simp [htop]
      · induction hr : h x using WithTop.recTopCoe with
        | top => exact (htop hr).elim
        | coe z =>
            induction z using WithBot.recBotCoe with
            | bot => exact (hbot hr).elim
            | coe r =>
                have hyr : (r : WithTopBot 𝕜) ∈ T := by
                  exact ⟨r, (mem_linearImageEpigraph_iff A h).2 ⟨x, hAy, by simp [hr]⟩, rfl⟩
                have hsInf_le : sInf T ≤ r := sInf_le hyr
                simpa [hr] using hsInf_le

namespace Function

section

variable {𝕜 : Type w} {E : Type u} {F : Type v}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [DenselyOrdered 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]
variable [AddCommMonoid F] [Module 𝕜 F]

-- Proof sketch: take the scalar epigraph `{(x, μ) | h x ≤ μ}` of `h` and apply the linear map
-- `(x, μ) ↦ (A x, μ)`. Its image is convex by `Convex.linear_image`, and
-- `Function.linearImage A h` agrees pointwise with the resulting vertical-infimum function. Then
-- apply `Function.isConvex_verticalInfimum`.
/-- Theorem 5.7 (2): if `A : E → F` is linear and `h` is convex on `E`, then the function `Ah`,
defined by `Ah(y) = inf {h(x) | A x = y}`, is convex on `F`. The textbook `R^n → R^m` statement
is the Euclidean specialization. -/
theorem isConvex_linearImage
    (A : E →ₗ[𝕜] F) (h : E → WithTopBot 𝕜) (hh : h.IsConvex 𝕜) :
    (A ◁ h).IsConvex 𝕜 := by
  rw [Function.linearImage_eq_verticalInfimum_linearImageEpigraph]
  have hlin : Convex 𝕜 (linearImageEpigraph A h) := by
    simpa [linearImageEpigraph_eq_image_epi, epi_univ_eq_setOf_le] using
      hh.convex_epigraph.linear_image (A.prodMap LinearMap.id)
  exact Function.isConvex_verticalInfimum hlin

end

end Function

end
