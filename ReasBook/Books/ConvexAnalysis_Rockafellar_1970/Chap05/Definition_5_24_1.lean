import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_23_0_6

noncomputable section

open scoped SetRel

universe u v

section

variable {𝕜 : Type v} [Add 𝕜] [LE 𝕜]
variable {E : Type u} [Sub E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Definition 5.24.1 introduces the effective domain of the subdifferential
  multifunction, written in the source as `{x | ∂f(x) ≠ ∅}`.
- `core/canonical`: for set-valued maps, mathlib's owner abstraction is the relation domain
  `SetRel.dom`. For the present section, the primitive object is the pairing-level subdifferential
  relation `(x, xStar) ↦ xStar ∈ ∂[Y]f(x)` at codomain `Y`.
- `bridge/view`: the textbook set `{x | ∂f(x) ≠ ∅}` is recovered by specializing `SetRel.dom` to
  that relation, and hence (under the stronger graph ambient) to `subdifferentialGraph f`.

Domain-style sampling used here:
- `_root_.subdifferentialAt` from
  [Definition_23_0_6](ConvexAnalysis_Rockafellar_1970/Chap05/Definition_23_0_6.lean),
  which is the chapter owner for the subdifferential itself;
- `SetRel.dom` and `SetRel.mem_dom` from mathlib's
  [Data/Rel](.lake/packages/mathlib/Mathlib/Data/Rel.lean), the canonical owner API for
  domains of relations / set-valued maps;
- `_root_.subdifferentialGraph` from
  [Definition_5_24_3](ConvexAnalysis_Rockafellar_1970/Chap05/Definition_5_24_3.lean),
  which is the Chapter 5 graph owner introduced just before this domain specialization;
- the earlier chapter owner `effectiveDomain`, written `dom(f)`, from
  [Definition_4_4](ConvexAnalysis_Rockafellar_1970/Chap01/Definition_4_4.lean),
  which shows the project convention that “effective domain” should land on an existing owner
  notion rather than a new wrapper.

Primitive data vs derived API:
- primitive owner input: `subdifferentialAt`;
- canonical derived API already available upstream: `SetRel.mem_dom`, expressing domain membership
  by existence of a related codomain point;
- source-facing bridge kept here: the textbook nonemptiness reformulation of `SetRel.dom`
  specialized to the subdifferential relation, with the reusable surface notation `dom∂(f)` for
  the source object `dom ∂f`.

Layer target: `bridge/view`. The mathematical content here is not a second owner beside
`subdifferentialAt`; it is the specialization of the canonical relation-domain owner to the
subdifferential relation/graph surface.

Scalar/ambient audit:
- the pairing-explicit owner `dom∂[Y](f)` now lives on the primitive scalar/ambient layer needed
  by Definition 23.0.6 itself (`Add`/`LE` on `𝕜`, `Sub` on `E`);
- the default notation `dom∂(f)` remains the canonical `Y = StrongDual 𝕜 E` specialization.

Notation evaluation:
- the exact textbook surface `dom ∂f` is not a stable Lean term form because `∂f` itself is not
  used as project notation for the subdifferential owner;
- the codomain parameter of the subdifferential owner is mathematically meaningful and not
  recoverable from `f` alone, so the canonical source-facing notation exposes both
  `dom∂[Y](f)` (pairing-explicit) and `dom∂(f)` (default `StrongDual 𝕜 E`) directly on
  the canonical relation-domain owner.
-/

set_option quotPrecheck false in
scoped[Rockafellar] notation "dom∂[" Y_ "](" f ")" =>
  SetRel.dom (fun p : E × Y_ ↦
    Prod.snd p ∈ subdifferentialAt (Y := Y_) f (Prod.fst p))

open scoped Rockafellar

section

variable [Semiring 𝕜] [TopologicalSpace 𝕜]
variable [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
variable [HasPairing E (StrongDual 𝕜 E) 𝕜]

set_option quotPrecheck false in
scoped[Rockafellar] notation "dom∂(" f ")" =>
  SetRel.dom (fun p : E × StrongDual 𝕜 E ↦
    Prod.snd p ∈ subdifferentialAt (Y := StrongDual 𝕜 E) f (Prod.fst p))

/- Definition 5.24.1: the effective domain of `∂f` is the domain of its graph relation, namely
`f ↦ dom∂(f)`, i.e. the canonical owner `(subdifferentialGraph f).dom`. -/

end

/-- A point lies in the pairing-explicit domain owner `dom∂[Y](f)` exactly when the intrinsic
subdifferential at that point is nonempty. -/
@[simp] theorem mem_domSubdifferential_iff_nonempty {f : E → WithTopBot 𝕜}
    {Y : Type (max u v)}
    [HasPairing E Y 𝕜] {x : E} :
    x ∈ dom∂[Y](f) ↔ (∂[Y]f(x)).Nonempty := by
  rw [SetRel.mem_dom]
  exact Iff.rfl

/-- Definition 5.24.1, textbook wording: a point lies in `dom∂[Y](f)` exactly when `∂[Y]f(x)` is
not empty. -/
@[simp] theorem mem_domSubdifferential_iff_ne_empty {f : E → WithTopBot 𝕜}
    {Y : Type (max u v)}
    [HasPairing E Y 𝕜] {x : E} :
    x ∈ dom∂[Y](f) ↔ (∂[Y]f(x)) ≠ ∅ := by
  rw [mem_domSubdifferential_iff_nonempty]
  exact Set.nonempty_iff_ne_empty

/-- Compatibility wrapper for the earlier theorem name on the nonempty-domain characterization. -/
@[simp] theorem mem_domSubdifferential {f : E → WithTopBot 𝕜} {Y : Type (max u v)}
    [HasPairing E Y 𝕜] {x : E} :
    x ∈ dom∂[Y](f) ↔ (∂[Y]f(x)).Nonempty := by
  simpa using (mem_domSubdifferential_iff_nonempty (f := f) (x := x))

/-- Compatibility wrapper for the earlier theorem name on the `≠ ∅` characterization. -/
@[simp] theorem mem_subdifferentialGraph_dom {f : E → WithTopBot 𝕜} {Y : Type (max u v)}
    [HasPairing E Y 𝕜] {x : E} :
    x ∈ dom∂[Y](f) ↔ (∂[Y]f(x)) ≠ ∅ := by
  simpa using (mem_domSubdifferential_iff_ne_empty (f := f) (x := x))

end
