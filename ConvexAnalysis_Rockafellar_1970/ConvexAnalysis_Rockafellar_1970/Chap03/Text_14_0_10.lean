import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_5_11
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_14_0_1

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Pointwise PolarCone Rockafellar

variable {ι : Type*} [Fintype ι]
variable {𝕜 : Type*} [CommSemiring 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜]

local notation "E" => ι → 𝕜

/-!
Source/core/bridge triage:

- `source-facing`: Text 14.0.10 identifies the polar cone of the nonnegative orthant.
- `core/canonical`: the chapter owner surface is `K∗[𝕜]` (i.e., `sourceDualCone`) together with
  `orthant[𝕜](E)`; the raw owner `PointedCone.dual (HasLinearPairing.pairingLinear)` is retained
  as a bridge theorem.
- `bridge/view`: `polarCone` from Text 14.0.1 is the chapter sign-convention bridge over
  `PointedCone.dual`.
- `bridge/view`: the source-facing polar identity is the sign-convention bridge
  `orthant[𝕜](E)ᵒ[𝕜] = -orthant[𝕜](E)`.
- `scalar/ambient-strength decision`: the owner-level duality statements below only use the
  semiring layer required by `PointedCone.dual`; the source-facing polar statement is isolated in
  a downstream ring section because `Kᵒ[𝕜]` uses the sign-twisted dual owner.

Domain-style sampling used here:
- `sourceDualCone`, `mem_sourceDualCone_iff_pairing_nonneg`, and `sourceDualCone_eq_dual`;
- `orthant[𝕜](E)` and `mem_orthant_iff`;
- `dotProduct` and `single_one_dotProduct`.

Primitive data vs derived API:
- primitive owner data: `sourceDualCone` and `orthant[𝕜](E)`;
- source-facing bridge data: `polarCone` and pointwise negation;
- derived API: the owner-level orthant self-duality (plus its `PointedCone.dual` bridge form) and
  the source-facing equality identifying the source polar orthant with the negative orthant.

Layer target: `source-facing`.
-/

-- Proof sketch: the owner dual cone consists of vectors whose pairing evaluation with every vector
-- in the ambient positive cone is nonnegative. Testing this against the standard basis vectors
-- forces each coordinate to be nonnegative, while the converse follows because a sum of products of
-- nonnegative coordinates is nonnegative.
/-- At the source owner layer, the nonnegative orthant in `𝕜^ι` is self-dual for `K∗[𝕜]`. -/
@[simp] theorem sourceDualCone_nonnegativeOrthant_eq_nonnegativeOrthant :
    ((((orthant[𝕜](E))∗[𝕜] : PointedCone 𝕜 E) : Set E) = orthant[𝕜](E)) := by
  classical
  ext x
  change x ∈ ((orthant[𝕜](E))∗[𝕜] : PointedCone 𝕜 E) ↔ x ∈ orthant[𝕜](E)
  rw [mem_sourceDualCone_iff_pairing_nonneg, mem_orthant_iff]
  change
    (∀ y : E, y ∈ orthant[𝕜](E) → 0 ≤ y ⬝ᵥ x) ↔ ∀ i : ι, 0 ≤ x i
  constructor
  · intro hx i
    have hi : Pi.single i (1 : 𝕜) ∈ orthant[𝕜](E) := by
      change 0 ≤ (Pi.single i (1 : 𝕜) : E)
      intro j
      by_cases h : j = i
      · subst h
        simp
      · simp [Pi.single_eq_of_ne h]
    have hdot : 0 ≤ (Pi.single i (1 : 𝕜) ⬝ᵥ x) := hx _ hi
    simpa [single_one_dotProduct] using hdot
  · intro hx y hy
    have hy' : ∀ i : ι, 0 ≤ y i := by
      change 0 ≤ y at hy
      exact hy
    simpa [dotProduct] using
      Finset.sum_nonneg (fun i _ ↦ mul_nonneg (hy' i) (hx i))

/-- At the canonical owner layer, the dual cone of the ambient positive cone in `𝕜^ι` is
itself. -/
@[simp] theorem PointedCone.dual_nonnegativeOrthant_eq_nonnegativeOrthant :
    (PointedCone.dual
      (HasLinearPairing.pairingLinear : E →ₗ[𝕜] Module.Dual 𝕜 E)
      (orthant[𝕜](E)) : Set E) = orthant[𝕜](E) := by
  simpa [sourceDualCone_eq_dual] using
    (sourceDualCone_nonnegativeOrthant_eq_nonnegativeOrthant (ι := ι) (𝕜 := 𝕜))

end

section

open scoped Pointwise PolarCone Rockafellar

variable {ι : Type*} [Fintype ι]
variable {𝕜 : Type*} [CommRing 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜]

local notation "E" => ι → 𝕜

/- The source-facing polar cone of the nonnegative orthant is the nonpositive orthant. This is the
sign-convention corollary of the owner-level self-duality of the orthant. -/
/-- Text 14.0.10 at the source-facing layer: the polar cone of the nonnegative orthant is its
pointwise negative. -/
@[simp] theorem polarCone_nonnegativeOrthant_eq_neg :
    {x : E | x ∈ (orthant[𝕜](E))ᵒ[𝕜]} = -orthant[𝕜](E) := by
  ext x
  change x ∈ (orthant[𝕜](E))ᵒ[𝕜] ↔ x ∈ -orthant[𝕜](E)
  constructor
  · intro hx
    have hxStar : -x ∈ ((orthant[𝕜](E))∗[𝕜] : PointedCone 𝕜 E) := by
      exact (mem_sourceDualCone_iff_neg_mem_polarCone (K := orthant[𝕜](E)) (xStar := -x)).2 <| by
        simpa using hx
    have hstar_eq :
        (((orthant[𝕜](E))∗[𝕜] : PointedCone 𝕜 E) : Set E) = orthant[𝕜](E) :=
      sourceDualCone_nonnegativeOrthant_eq_nonnegativeOrthant (ι := ι) (𝕜 := 𝕜)
    have hxStar' : -x ∈ orthant[𝕜](E) := by
      have hmem :
          (-x ∈ (((orthant[𝕜](E))∗[𝕜] : PointedCone 𝕜 E) : Set E)) =
            (-x ∈ orthant[𝕜](E)) :=
        congrArg (fun S : Set E => -x ∈ S) hstar_eq
      exact hmem ▸ hxStar
    simpa using hxStar'
  · intro hx
    have hxStar : -x ∈ orthant[𝕜](E) := by simpa using hx
    have hstar_eq :
        (((orthant[𝕜](E))∗[𝕜] : PointedCone 𝕜 E) : Set E) = orthant[𝕜](E) :=
      sourceDualCone_nonnegativeOrthant_eq_nonnegativeOrthant (ι := ι) (𝕜 := 𝕜)
    have hxStar' : -x ∈ ((orthant[𝕜](E))∗[𝕜] : PointedCone 𝕜 E) := by
      have hmem :
          (-x ∈ (((orthant[𝕜](E))∗[𝕜] : PointedCone 𝕜 E) : Set E)) =
            (-x ∈ orthant[𝕜](E)) :=
        congrArg (fun S : Set E => -x ∈ S) hstar_eq
      exact hmem.symm ▸ hxStar
    have hxPolar :
        -(-x) ∈ (orthant[𝕜](E))ᵒ[𝕜] :=
      (mem_sourceDualCone_iff_neg_mem_polarCone (K := orthant[𝕜](E)) (xStar := -x)).1 <| by
        simpa using hxStar'
    simpa using hxPolar

end
