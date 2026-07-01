import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_7_0_4
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_6
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_12_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Rockafellar

section

variable {𝕜 : Type*} [ConditionallyCompleteLattice 𝕜] [TopologicalSpace 𝕜] [Neg 𝕜]
variable {E : Type u} [TopologicalSpace E]

/-- Definition 6.30.2: the concave closure is the sign-dual of the convex closure. -/
def concaveClosure (g : E → WithTopBot 𝕜) : E → WithTopBot 𝕜 :=
  fun x ↦ -(cl(-g) x)

/-- Owner equation for concave closure. -/
theorem concaveClosure_eq_neg_lowerSemicontinuousHull_neg (g : E → WithTopBot 𝕜) :
    concaveClosure g = fun x ↦ -(cl(-g) x) :=
  rfl

end

section

variable (𝕜 : Type*) [Semiring 𝕜] [PartialOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]
variable {α : Type*} [AddCommGroup α] [SMul 𝕜 α] [LE α]

namespace Function

/-- Concavity is encoded via convexity of the negated function. -/
abbrev IsConcave (g : E → WithTopBot α) : Prop :=
  (-g).IsConvex 𝕜

/-- Sign-dual bridge from concavity to convexity of the negated function. -/
theorem IsConcave.convex_neg {g : E → WithTopBot α} (hg : g.IsConcave 𝕜) :
    (-g).IsConvex 𝕜 :=
  hg

end Function

end

section

variable {E : Type u}
variable {α : Type*} [Neg α] [Preorder α]

namespace Function

/-- Proper concavity is encoded via properness of the negated function. -/
abbrev IsProperConcave (g : E → WithTopBot α) : Prop :=
  (-g).IsProper

/-- Definitional bridge between proper concavity and properness of `-g`. -/
theorem isProperConcave_iff (g : E → WithTopBot α) :
    g.IsProperConcave ↔ (-g).IsProper :=
  Iff.rfl

namespace IsProperConcave

/-- Proper concavity directly provides properness of `-g`. -/
theorem neg_isProper {g : E → WithTopBot α} (hg : g.IsProperConcave) :
    (-g).IsProper :=
  hg

end IsProperConcave

end Function

end

section

variable (𝕜 : Type*) [Semiring 𝕜] [PartialOrder 𝕜]
variable {E : Type u} [TopologicalSpace E] [AddCommMonoid E] [SMul 𝕜 E]
variable {α : Type*}
variable [TopologicalSpace (WithTopBot α)] [AddCommGroup α] [SMul 𝕜 α] [Preorder α]

namespace Function

/-- Closed-proper-concave owner on the Chapter 12 codomain layer, encoded as
closed-proper-convexity of the negated function. -/
abbrev IsClosedProperConcave (g : E → WithTopBot α) : Prop :=
  Function.IsClosedProperConvex (𝕜 := 𝕜) (-g)

local notation "IsClosedProperConcave[" 𝕜 "]" => Function.IsClosedProperConcave (𝕜 := 𝕜)
local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)

/-- Definitional bridge between closed proper concavity and closed proper convexity of `-g`. -/
theorem isClosedProperConcave_iff (g : E → WithTopBot α) :
    IsClosedProperConcave[𝕜] g ↔ IsClosedProperConvex[𝕜] (-g) :=
  Iff.rfl

namespace IsClosedProperConcave

/-- Closed proper concavity directly provides closed proper convexity of `-g`. -/
theorem neg_isClosedProperConvex {g : E → WithTopBot α}
    (hg : IsClosedProperConcave[𝕜] g) :
    IsClosedProperConvex[𝕜] (-g) :=
  hg

end IsClosedProperConcave

end Function

end

section

variable {𝕜 : Type*} [Ring 𝕜] [Preorder 𝕜]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E]

/-- Affine majorants of a `WithTopBot`-valued function. -/
abbrev AffineMajorant (g : E → WithTopBot 𝕜) :=
  {h : AffineMap 𝕜 E 𝕜 // g ≤ h.toWithBotTop}

instance {g : E → WithTopBot 𝕜} : CoeFun (AffineMajorant g) (fun _ ↦ E → 𝕜) where
  coe h := (h : AffineMap 𝕜 E 𝕜)

namespace AffineMajorant

/-- Coercion-free `WithTopBot`-valued view of an affine majorant. -/
abbrev toWithTopBot {g : E → WithTopBot 𝕜} (h : AffineMajorant g) : E → WithTopBot 𝕜 :=
  (h : AffineMap 𝕜 E 𝕜).toWithBotTop

@[simp] theorem toWithTopBot_apply {g : E → WithTopBot 𝕜} (h : AffineMajorant g) (x : E) :
    h.toWithTopBot x = ((h x : 𝕜) : WithTopBot 𝕜) :=
  rfl

end AffineMajorant

end

section

variable {𝕜 : Type*} [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜] [Ring 𝕜]
variable [IsOrderedAddMonoid 𝕜]
variable {E : Type u} [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]

/-- Bridge form: once `cl(-g)` is identified as the pointwise supremum of affine minorants of
`-g`, the concave closure is the pointwise infimum of affine majorants of `g`. -/
theorem concaveClosure_eq_iInf_affineMajorant_of_eq_iSup_affineMinorant
    (g : E → WithTopBot 𝕜) (x : E)
    (hcl : cl(-g) x = ⨆ h : AffineMinorant (-g), h.toWithBotTop x) :
    concaveClosure g x =
      ⨅ h : AffineMajorant g, h.toWithTopBot x := by
  have hneg_iSup :
      -(⨆ h : AffineMinorant (-g), h.toWithBotTop x) =
        ⨅ h : AffineMinorant (-g), -h.toWithBotTop x := by
    exact
      congrArg OrderDual.ofDual
        (WithTopBot.negOrderIso.map_iSup (fun h : AffineMinorant (-g) ↦ h.toWithBotTop x))
  have hle_majorants :
      -(⨆ h : AffineMinorant (-g), h.toWithBotTop x) ≤
        ⨅ h : AffineMajorant g, h.toWithTopBot x := by
    refine le_iInf ?_
    intro hMaj
    let hMin : AffineMinorant (-g) :=
      ⟨-hMaj.1, by
        intro y
        have hy : g y ≤ hMaj.toWithTopBot y := hMaj.property y
        simpa [AffineMajorant.toWithTopBot, AffineMinorant.toWithBotTop] using
          (WithTopBot.neg_le_neg_iff.2 hy)⟩
    have hMin_le :
        hMin.toWithBotTop x ≤ ⨆ h : AffineMinorant (-g), h.toWithBotTop x :=
      le_iSup_of_le hMin le_rfl
    have hneg_le : -(⨆ h : AffineMinorant (-g), h.toWithBotTop x) ≤ -hMin.toWithBotTop x :=
      (WithTopBot.neg_le_neg_iff.2 hMin_le)
    simpa [hMin, AffineMajorant.toWithTopBot, AffineMinorant.toWithBotTop] using hneg_le
  have hle_minorants :
      (⨅ h : AffineMajorant g, h.toWithTopBot x) ≤
        ⨅ h : AffineMinorant (-g), -h.toWithBotTop x := by
    refine le_iInf ?_
    intro hMin
    let hMaj : AffineMajorant g :=
      ⟨-hMin.1, by
        intro y
        have hy : hMin.toWithBotTop y ≤ (-g) y := hMin.property y
        simpa [AffineMajorant.toWithTopBot, AffineMinorant.toWithBotTop] using
          (WithTopBot.neg_le_neg_iff.2 hy)⟩
    have hMaj_le :
        (⨅ h : AffineMajorant g, h.toWithTopBot x) ≤ hMaj.toWithTopBot x :=
      iInf_le _ hMaj
    simpa [hMaj, AffineMajorant.toWithTopBot, AffineMinorant.toWithBotTop] using hMaj_le
  have hle_minorants_to_majorants :
      (⨅ h : AffineMinorant (-g), -h.toWithBotTop x) ≤
        ⨅ h : AffineMajorant g, h.toWithTopBot x := by
    simpa [hneg_iSup] using hle_majorants
  calc
    concaveClosure g x = -(cl(-g) x) := rfl
    _ = -(⨆ h : AffineMinorant (-g), h.toWithBotTop x) := by rw [hcl]
    _ = ⨅ h : AffineMinorant (-g), -h.toWithBotTop x := hneg_iSup
    _ = ⨅ h : AffineMajorant g, h.toWithTopBot x :=
      le_antisymm hle_minorants_to_majorants hle_minorants

end

section

variable {𝕜 : Type*} [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜] [Ring 𝕜]
variable [IsOrderedAddMonoid 𝕜]
variable {E : Type u} [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]

namespace Function

/-- Generic bridge form: once `cl(-g)` is identified as the pointwise supremum of affine
minorants of `-g`, the concave closure is the pointwise infimum of affine majorants of `g`. -/
theorem concaveClosure_eq_iInf_affineMajorant
    {g : E → WithTopBot 𝕜} (x : E)
    (hcl : cl(-g) x = ⨆ h : AffineMinorant (-g), h.toWithBotTop x) :
    concaveClosure g x =
      ⨅ h : AffineMajorant g, h.toWithTopBot x := by
  exact concaveClosure_eq_iInf_affineMajorant_of_eq_iSup_affineMinorant g x hcl

end Function

end

section

variable {𝕜 : Type*}
variable [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜] [CommRing 𝕜]
variable [IsStrictOrderedRing 𝕜]
variable {E : Type u}
variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
variable {Y : Type*}
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing E Y 𝕜] [HasPairing Y E 𝕜] [HasPairingSwap E Y 𝕜]

namespace Function

/-- Primitive bridge form: if a dual-pairing biconjugate identity for `-g` is available and
affine minorants of `-g` admit the pairing normal form, then the concave closure of `g` is the
pointwise infimum of its affine majorants. -/
theorem concaveClosure_eq_iInf_affineMajorant_of_neg_eq_biconjugate
    {g : E → WithTopBot 𝕜} (x : E)
    (hg_biconj : (((-g)⋆ : Y → WithTopBot 𝕜)⋆ : E → WithTopBot 𝕜) = cl(-g))
    (h_affine : AffineMinorant.IsPairingSubConstRepresentable (-g)) :
    concaveClosure g x =
      ⨅ h : AffineMajorant g, h.toWithTopBot x := by
  have hclCanon :
      cl(-g) x = ⨆ h : AffineMinorant (-g), h.toWithBotTop x := by
    calc
      cl(-g) x = (((-g)⋆ : Y → WithTopBot 𝕜)⋆ : E → WithTopBot 𝕜) x := by
        simpa using congrArg (fun f : E → WithTopBot 𝕜 ↦ f x) hg_biconj.symm
      _ = ⨆ h : AffineMinorant (-g), h.toWithBotTop x :=
        biconjugate_apply_eq_iSup_affineMinorant
          (-g) x h_affine
  exact concaveClosure_eq_iInf_affineMajorant x hclCanon

end Function

end

section

variable {𝕜 : Type*}
variable [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜] [Field 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)] [IsStrictOrderedRing 𝕜]
variable {E : Type u}
variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
variable [FiniteDimensional 𝕜 E] [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜]
variable [HasPairingSwap E E 𝕜]

namespace Function.IsConcave

/-- For a concave function `g`, the closure `ḡ` is the pointwise infimum of all affine majorants
of `g`, obtained by discharging the affine-minorant representation bridge from Theorem 12.1 on
the finite-dimensional scalar-field pairing layer. -/
theorem concaveClosure_eq_iInf_affineMajorant_of_pairingSubConstRepresentable
    {g : E → WithTopBot 𝕜} (hg : g.IsConcave 𝕜) (x : E)
    (h_affine : AffineMinorant.IsPairingSubConstRepresentable (-g)) :
    concaveClosure g x =
      ⨅ h : AffineMajorant g, h.toWithTopBot x := by
  exact Function.concaveClosure_eq_iInf_affineMajorant_of_neg_eq_biconjugate
    x hg.convex_neg.biconjugate_eq_lowerSemicontinuousHull h_affine

end Function.IsConcave

end
