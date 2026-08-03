module

public import Topology_Munkres_2000.Book.Definition_76_6.Renumbering

public section

universe u v

open LabellingScheme
open LabellingScheme.PolygonalRegions.Renumbering

/- Remark 74.1: cyclically changing the starting point of a polygon edge-labelling
word, represented by replacing `y₀ ++ y₁` with `y₁ ++ y₀`, changes the resulting
quotient realization only up to homeomorphism. -/
#check fun {α : Type u} (y₀ y₁ : List (α × Bool)) (rest : LabellingScheme α)
    (hLength : 3 ≤ (y₀ ++ y₁).length)
    (original : PolygonalRegions.{u, v} (⟨y₀ ++ y₁, hLength⟩ ::ₘ rest)) ↦
  realizationHomeomorph original (ofAppend y₀ y₁ rest hLength)
