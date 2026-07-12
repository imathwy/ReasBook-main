import Mathlib
import StacksProject_2024.Chap34.Definition_34_5_6
import StacksProject_2024.Chap34.Definition_34_6_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

/- Semantic recall:
`lean_leansearch` was used to confirm the canonical scheme-site owners around this item, including
`Scheme.grothendieckTopology` and `Scheme.fppfTopology`. Local Chapter 34 precedent then fixes the
syntomic clause as the topology `Scheme.grothendieckTopology (@Syntomic)`, so this
item is expressed as topology inclusions on `Scheme`. -/

namespace AlgebraicGeometry.Scheme

/-- Lemma 34.7.2 (1): any syntomic covering is an fppf covering. Equivalently, the big syntomic
Grothendieck topology on schemes is contained in the big fppf topology. -/
@[stacks 021N]
theorem syntomicTopology_le_fppfTopology :
    Scheme.grothendieckTopology (@Syntomic) ≤ Scheme.fppfTopology := sorry

/-- Lemma 34.7.2 (2): any smooth covering is an fppf covering. Equivalently, the big smooth
Grothendieck topology on schemes is contained in the big fppf topology. -/
@[stacks 021N]
theorem smoothTopology_le_fppfTopology :
    Scheme.bigSmoothSite ≤ Scheme.fppfTopology := sorry

/-- Lemma 34.7.2 (3): any étale covering is an fppf covering. Equivalently, the big étale
Grothendieck topology on schemes is contained in the big fppf topology. -/
@[stacks 021N]
theorem etaleTopology_le_fppfTopology :
    Scheme.etaleTopology ≤ Scheme.fppfTopology := sorry

/-- Lemma 34.7.2 (4): any Zariski covering is an fppf covering. Equivalently, the big Zariski
Grothendieck topology on schemes is contained in the big fppf topology. -/
@[stacks 021N]
theorem zariskiTopology_le_fppfTopology :
    Scheme.zariskiTopology ≤ Scheme.fppfTopology := sorry

end AlgebraicGeometry.Scheme
