import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace ERealFunction

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- Lemma 1.28: composing a lower semicontinuous extended-real-valued function with a continuous
map preserves lower semicontinuity. -/
theorem lowerSemicontinuous_comp {f : Y → EReal} {g : X → Y}
    (hf : LowerSemicontinuous f) (hg : Continuous g) :
    LowerSemicontinuous (f ∘ g) :=
  hf.comp hg

end ERealFunction
