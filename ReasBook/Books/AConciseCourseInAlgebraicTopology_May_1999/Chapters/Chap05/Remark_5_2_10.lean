import Mathlib.Tactic.Recall
import Mathlib.Topology.Category.TopCat.Limits.Basic

open CategoryTheory CategoryTheory.Limits

universe u v w

/- Remark 5.2.10: in `TopCat`, the canonical limit and colimit objects carry the inherited
topologies recorded by the existing mathlib owners `TopCat.limit_topology` and
`TopCat.colimit_topology`. -/
recall TopCat.limit_topology
    {J : Type v} [Category.{w} J] (F : J ⥤ TopCat.{u}) [HasLimit F] :
    (limit F).str = ⨅ j, (F.obj j).str.induced (limit.π F j)

recall TopCat.colimit_topology
    {J : Type v} [Category.{w} J] (F : J ⥤ TopCat.{u}) [HasColimit F] :
    (colimit F).str = ⨆ j, (F.obj j).str.coinduced (colimit.ι F j)
