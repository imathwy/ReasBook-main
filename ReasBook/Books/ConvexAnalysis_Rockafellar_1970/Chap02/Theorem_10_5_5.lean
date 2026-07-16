import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Definition_10_5_3

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u v w

variable {X : Type v} {Y : Type w}
variable [PseudoEMetricSpace X] [PseudoEMetricSpace Y]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 10.5.5 says that an equi-Lipschitz family on a subset `S` is uniformly
  equicontinuous on `S`.
- `core/canonical`: the intrinsic owner is `Set.EquiLipschitzOn F S`, independent of any indexing
  model; the corresponding canonical uniformly equicontinuous family is the subtype-indexed family
  `fun g : F ↦ (g : X → Y)`.
- `bridge/view`: the chapter owner `EquiLipschitzOn f S` is exactly
  `(Set.range f).EquiLipschitzOn S`, and `UniformEquicontinuousOn.comp` transports the intrinsic
  subtype-indexed conclusion back to the original indexed family along `Set.rangeFactorization f`.

Domain-style sampling used here:
- `Set.EquiLipschitzOn`;
- `EquiLipschitzOn`;
- `UniformEquicontinuousOn`;
- `LipschitzOnWith.uniformEquicontinuousOn`;
- `UniformEquicontinuousOn.comp`.

Primitive data vs derived API:
- primitive data: one common nonnegative Lipschitz constant for all members of a function-family
  set, i.e. `hF : F.EquiLipschitzOn S`;
- derived API: uniform equicontinuity for subtype-indexed families and then for range-indexed
  source families.

Layer target: `core/canonical` first (intrinsic theorem on `Set.EquiLipschitzOn`), then the
`source-facing` theorem `EquiLipschitzOn.uniformEquicontinuousOn` as a thin range/reindex bridge.
-/

/-- Intrinsic owner theorem: an equi-Lipschitz family set on `S` is uniformly equicontinuous on
`S`, stated on the canonical set-owner surface `F.UniformEquicontinuousOn S`. -/
theorem Set.EquiLipschitzOn.uniformEquicontinuousOn
    {F : Set (X → Y)} {S : Set X} (hF : F.EquiLipschitzOn S) :
    F.UniformEquicontinuousOn S := by
  rcases hF with ⟨α, hα⟩
  exact LipschitzOnWith.uniformEquicontinuousOn (fun g : F ↦ (g : X → Y)) α
    (fun g ↦ hα g g.2)

-- Proof sketch: pass through the intrinsic `Set.EquiLipschitzOn` theorem on `Set.range f`,
-- then reindex the resulting uniformly equicontinuous family along `Set.rangeFactorization f`.
/-- Theorem 10.5.5: if a family of functions on `S` is equi-Lipschitzian relative to `S`, then it
is uniformly equicontinuous relative to `S`. -/
theorem EquiLipschitzOn.uniformEquicontinuousOn
    {ι : Type u} {f : ι → X → Y} {S : Set X} (hf : EquiLipschitzOn f S) :
    UniformEquicontinuousOn f S := by
  have hsub : (Set.range f).UniformEquicontinuousOn S :=
    Set.EquiLipschitzOn.uniformEquicontinuousOn (S := S) hf
  simpa [Function.comp] using
    UniformEquicontinuousOn.comp hsub (Set.rangeFactorization f)

end
