import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap07.Text_35_6_3

noncomputable section

open scoped Rockafellar SetRel

universe u v w u' v'

namespace Bifunction

section

variable {𝕜 : Type w} [Add 𝕜] [LE 𝕜]
variable {U : Type u} {V : Type v}
variable [Sub U] [Sub V]
variable {YU : Type u'} {YV : Type v'}
variable [HasPairing U YU 𝕜] [HasPairing V YV 𝕜]

/-!
Source/core/bridge triage:

- `source-facing`: Definition 37.3.1 recalls the saddle subdifferential `∂K(u, v)` of a
  concave-convex bifunction and then defines its domain `dom ∂K` as the locus where that
  subdifferential is nonempty.
- `core/canonical`: the chapter already owns the saddle subdifferential itself as
  `Bifunction.subdifferentialAt`, written `d(K ; u, v)`.
- `bridge/view`: the source domain `dom ∂K` is therefore the canonical pointwise nonemptiness
  locus of the already-owned saddle subdifferential `d(K ; u, v)`, i.e. the chapter owner
  `domd(K | YU, YV)`.

Domain-style sampling:
- `Bifunction.subdifferentialAt` and the notation `d(K ; u, v | YU, YV)` from `Theorem_35_7`;
- `SetRel.dom` / `SetRel.mem_dom` as the canonical relation-domain owner API;
- `mem_subdifferentialGraph_dom` from `Chap05.Definition_5_24_1`, which fixes the project pattern
  that subdifferential domains are recorded as owned domain surfaces rather than repeated raw
  comprehensions.

Primitive data vs derived API:
- primitive owner data already exist upstream: the saddle subdifferential owner
  `subdifferentialAt K u v YU YV`;
- derived API in this file: the canonical domain owner `domd(K | YU, YV)` together with the
  source-facing nonemptiness reformulations matching the textbook wording.

Layer target: `bridge/view`. This item does not introduce a second owner for the saddle
subdifferential; it reuses the existing owner and records its domain as the canonical
pointwise nonemptiness locus.
-/

/- Section 35 already defines the saddle subdifferential as the canonical chapter owner
`Bifunction.subdifferentialAt`, written `d(K ; u, v)`. -/
recall Bifunction.subdifferentialAt

/- Definition 37.3.1: the domain of the saddle subdifferential mapping is the pointwise
nonemptiness locus of the already-owned saddle subdifferential `d(K ; u, v)`. -/
abbrev subdifferentialDom (K : U → V → WithTopBot 𝕜)
    (YU : Type u') [HasPairing U YU 𝕜]
    (YV : Type v') [HasPairing V YV 𝕜] : Set (U × V) :=
  SetRel.dom (fun q : (U × V) × (YU × YV) ↦
    match q with
    | ((u, v), p) => p ∈ d(K ; u, v | YU, YV))

scoped[Rockafellar] notation "domd(" K " | " yu ", " yv ")" =>
  Bifunction.subdifferentialDom K yu yv

-- Proof sketch: this is just the defining pointwise nonemptiness condition of `domd`.
/-- A point lies in the domain of the saddle subdifferential exactly when the saddle
subdifferential at that point is nonempty. -/
@[simp] theorem mem_subdifferentialDom_iff_nonempty
    {K : U → V → WithTopBot 𝕜} {p : U × V} :
    p ∈ domd(K | YU, YV) ↔ (d(K ; p.1, p.2 | YU, YV)).Nonempty := by
  rw [SetRel.mem_dom]
  exact Iff.rfl

-- Proof sketch: this is the defining pointwise nonemptiness condition of `domd`.
/-- A point lies in the domain of the saddle subdifferential exactly when the saddle
subdifferential at that point is nonempty. -/
@[simp] theorem mem_subdifferentialDom
    {K : U → V → WithTopBot 𝕜} {p : U × V} :
    p ∈ domd(K | YU, YV) ↔ d(K ; p.1, p.2 | YU, YV) ≠ ∅ := by
  rw [mem_subdifferentialDom_iff_nonempty]
  exact Set.nonempty_iff_ne_empty

end

section

variable {𝕜 : Type w} [NormedField 𝕜] [LE 𝕜]
variable {U : Type u} {V : Type v}
variable [SeminormedAddCommGroup U] [NormedSpace 𝕜 U]
variable [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]

/- Definition 37.3.1, intrinsic strong-dual bridge: specialize the pairing-level domain owner
`domd(K | YU, YV)` to the canonical continuous-dual product, parallel to `∂ₛ K(u, v)`. -/
abbrev subdifferentialDomDual (K : U → V → WithTopBot 𝕜) : Set (U × V) :=
  domd(K | StrongDual 𝕜 U, StrongDual 𝕜 V)

scoped[Rockafellar] notation "dom∂ₛ " K =>
  Bifunction.subdifferentialDomDual K

/-- A point lies in the intrinsic strong-dual domain of the saddle subdifferential exactly when
the strong-dual saddle subdifferential at that point is nonempty. -/
@[simp] theorem mem_subdifferentialDomDual_iff_nonempty
    {K : U → V → WithTopBot 𝕜} {p : U × V} :
    p ∈ (dom∂ₛ K) ↔ (∂ₛ K(p.1, p.2)).Nonempty := by
  change p ∈ domd(K | StrongDual 𝕜 U, StrongDual 𝕜 V) ↔
      (d(K ; p.1, p.2 | StrongDual 𝕜 U, StrongDual 𝕜 V)).Nonempty
  exact
    (mem_subdifferentialDom_iff_nonempty :
      p ∈ domd(K | StrongDual 𝕜 U, StrongDual 𝕜 V) ↔
        (d(K ; p.1, p.2 | StrongDual 𝕜 U, StrongDual 𝕜 V)).Nonempty)

/-- A point lies in the intrinsic strong-dual domain of the saddle subdifferential exactly when
the strong-dual saddle subdifferential at that point is not empty. -/
@[simp] theorem mem_subdifferentialDomDual
    {K : U → V → WithTopBot 𝕜} {p : U × V} :
    p ∈ (dom∂ₛ K) ↔ ∂ₛ K(p.1, p.2) ≠ ∅ := by
  rw [mem_subdifferentialDomDual_iff_nonempty]
  exact Set.nonempty_iff_ne_empty

end

end Bifunction
