module

public import Topology_Munkres_2000.Book.Algorithm_76_2.Cut
public import Topology_Munkres_2000.Book.Proposition_76_1.Realization

public section

universe u v w

open LabellingScheme
open LabellingScheme.PolygonalRegions

/--
Proposition 76.1. Let `w₁ = y₀ ++ y₁`, with cut words `y₀c⁻¹` and `cy₁`. If first
identifying the two new `c`-edges yields the original regions, and the remaining edge
identifications then yield `X`, the cut labelling scheme obtains the same space `X`.
-/
theorem cutSchemeRealizesSameSpace {α : Type u}
    (y₀ y₁ : List (α × Bool)) (c : α) (b : Bool) (rest : LabellingScheme α)
    (hy₀Length : 2 ≤ y₀.length) (hy₁Length : 2 ≤ y₁.length)
    (originalRegions : PolygonalRegions
      (⟨y₀ ++ y₁, PolygonWord.append_length y₀ y₁ hy₀Length hy₁Length⟩ ::ₘ rest))
    (cutRegions : PolygonalRegions
      (⟨y₀ ++ [(c, !b)], PolygonWord.appendLetter_length y₀ (c, !b) hy₀Length⟩ ::ₘ
        ⟨(c, b) :: y₁, PolygonWord.consLetter_length (c, b) y₁ hy₁Length⟩ ::ₘ rest))
    {Y : Type v} {X : Type w} [TopologicalSpace Y] [TopologicalSpace X]
    (firstPaste : cutRegions.Source → Y) (remainingPastes : Y → X)
    (hfirstPaste : cutRegions.PastesLabel c firstPaste)
    (intermediate : Y ≃ₜ originalRegions.Source)
    (hboundaryCompatibility : ∀ a b,
      (cutRegions.RemainingIdentified c firstPaste).r a b ↔
        originalRegions.Identified.r (intermediate a) (intermediate b))
    (hremaining : originalRegions.Realizes (remainingPastes ∘ intermediate.symm)) :
    cutRegions.Realizes (remainingPastes ∘ firstPaste) := by
  -- Transport the remaining-edge realization back across the intermediate homeomorphism.
  have hpastesRemaining : cutRegions.PastesRemaining c firstPaste remainingPastes :=
    pastesRemaining_of_homeomorph cutRegions originalRegions c firstPaste remainingPastes
      intermediate hboundaryCompatibility hremaining
  -- Compose the first labelled-edge quotient with the quotient by all remaining edges.
  exact realizes_comp cutRegions c firstPaste remainingPastes hfirstPaste hpastesRemaining

/- The quotient-map composition principle used by Proposition 76.1. -/
#check Topology.IsQuotientMap.comp

/- The verified combinatorial cut underlying the source proposition. -/
#check LabellingScheme.Cut.of
