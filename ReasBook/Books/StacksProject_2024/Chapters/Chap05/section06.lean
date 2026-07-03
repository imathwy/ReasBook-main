import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_5_6_1 (from Chap05) -/
open Topology

/- Domain-style sampling for induced topologies:
- primitive owner object: `TopologicalSpace.induced`
- owner predicate on a map: `IsInducing`
- same-domain declarations inspected:
  `continuous_iff_le_induced`, `Topology.IsInducing.isOpen_iff`,
  `Topology.IsInducing.isClosed_iff`

Layer triage:
- `source-facing`: the induced topology on the domain of a map into a topological space
- `core/canonical`: `TopologicalSpace.induced` together with the owner predicate `IsInducing`
- `bridge/view`: the open/closed/continuity characterization theorems

Primitive data is just the induced topology `TopologicalSpace.induced f`; continuity, openness,
and closedness are derived API from that owner abstraction. The injectivity mentioned in the
Stacks prose is redundant for the topology owner and its basic characterization theorems, so this
file should recall the canonical owner object first and then its companion API, rather than
introducing a parallel local wrapper specialized to injective maps.
-/

/- The primitive owner object for the topology induced by a map `f` is the canonical topology
`TopologicalSpace.induced`. -/
recall TopologicalSpace.induced

/- Companion recall: the canonical map-side predicate for carrying the induced topology is
`IsInducing`. -/
recall IsInducing

/- Lemma 5.6.1 (1): for an injective map `f : Y → X`, the source statement that the induced
topology on `Y` is the weakest topology making `f` continuous is exactly the canonical theorem
`continuous_iff_le_induced`. -/
recall continuous_iff_le_induced

/- Lemma 5.6.1 (2): the open subsets of the induced topology are exactly the preimages of open
subsets of `X`, canonically expressed by `isOpen_induced_iff`. -/
recall isOpen_induced_iff

/- Lemma 5.6.1 (3): the closed subsets of the induced topology are exactly the preimages of closed
subsets of `X`, canonically expressed by `isClosed_induced_iff`. -/
recall isClosed_induced_iff

/-! ### Lemma_5_6_2 (from Chap05) -/
open Topology

/- Domain-style sampling for quotient topologies:
- primitive owner object: `TopologicalSpace.coinduced`
- owner predicates on a map: `IsCoinducing`, `IsQuotientMap`
- same-domain declarations inspected:
  `continuous_iff_coinduced_le`, `isOpen_coinduced`, `isClosed_coinduced`,
  `isQuotientMap_iff`

Layer triage:
- `source-facing`: the quotient topology on the codomain of a surjective map
- `core/canonical`: `TopologicalSpace.coinduced` together with the owner predicates
  `IsCoinducing` and `IsQuotientMap`
- `bridge/view`: the iff theorems translating the Stacks wording into those owner declarations

Primitive data is just the coinduced topology `TopologicalSpace.coinduced`; the “strongest
topology making `f` continuous”, open-set, and closed-set clauses are derived API. Surjectivity
does not belong to the topology itself, only to the quotient-map package, so this file should
recall the canonical owner declarations and their companion theorems rather than introducing a
parallel local quotient-topology wrapper.
-/

/- The primitive owner object for the quotient topology associated to a map `f` is the canonical
coinduced topology `TopologicalSpace.coinduced`. -/
recall TopologicalSpace.coinduced

/- Companion recall: the quotient-topology condition itself is the canonical predicate
`IsCoinducing`. -/
recall IsCoinducing

/- Companion recall: once surjectivity is added, the canonical owner predicate is
`IsQuotientMap`. -/
recall IsQuotientMap

/- Lemma 5.6.2 (1): for a surjective map `f`, the source statement that the quotient topology on
`Y` is the strongest topology making `f` continuous is exactly the canonical theorem
`continuous_iff_coinduced_le`. -/
recall continuous_iff_coinduced_le

/- Companion recall: a surjective coinducing map is exactly a quotient map. -/
recall isQuotientMap_iff

/- Lemma 5.6.2 (2): for a surjective map `f`, the source open-set characterization of the
quotient topology is exactly the canonical theorem `isOpen_coinduced`. -/
recall isOpen_coinduced

/- Lemma 5.6.2 (3): for a surjective map `f`, the source closed-set characterization of the
quotient topology is exactly the canonical theorem `isClosed_coinduced`. -/
recall isClosed_coinduced

/-! ### Definition_5_6_3 (from Chap05) -/
namespace Topology

open Function Set
open IsInducing

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/- Domain-style sampling for submersive maps:
- primary domain: quotient maps and range factorizations in general topology
- owner abstraction: `Topology.IsQuotientMap`
- same-domain declarations inspected:
  `Topology.IsQuotientMap`,
  `Topology.isQuotientMap_iff`,
  `Topology.IsQuotientMap.comp`,
  `Topology.IsInducing.isQuotientMap_of_surjective`,
  `Set.rangeFactorization`,
  `Set.rangeFactorization_surjective`

Layer triage:
- `source-facing`: the Stacks notion `IsStrictMap`
- `core/canonical`: `Topology.IsQuotientMap`
- `bridge/view`: the quotient-map condition on `Set.rangeFactorization` and the source-facing
  characterization theorem `isSubmersiveMap_iff`

Primitive data belongs to the source-facing predicate `IsStrictMap`: the strictness clause is the
quotient-map condition on the range factorization. The canonical owner `IsQuotientMap` remains the
core topology predicate, and `isSubmersiveMap_iff` is the thin source-facing bridge expressing the
Stacks term “submersive” through surjectivity plus strictness.
-/

/- Definition 5.6.3 uses the canonical quotient-map owner `Topology.IsQuotientMap` for the
range-factorization clause of strict maps. -/
recall IsQuotientMap

/-- Definition 5.6.3: a map is strict if the induced map onto its image is a quotient map. -/
def IsStrictMap (f : X → Y) : Prop :=
  IsQuotientMap (rangeFactorization f)

/-- Definition 5.6.3, source-facing form: a map is submersive if and only if it is
surjective and strict, equivalently a quotient map. -/
theorem isSubmersiveMap_iff {f : X → Y} :
    IsQuotientMap f ↔ Surjective f ∧ IsStrictMap f := by
  constructor
  · intro hf
    refine ⟨hf.surjective, ?_⟩
    rw [IsStrictMap, isQuotientMap_iff]
    refine ⟨?_, rangeFactorization_surjective⟩
    refine IsCoinducing.of_isOpen_preimage_iff_isOpen fun s ↦ ⟨?_, ?_⟩
    · intro hs
      have hopen : IsOpen (Subtype.val '' s : Set Y) := by
        apply hf.isOpen_preimage.mp
        have hpre : f ⁻¹' (Subtype.val '' s : Set Y) = rangeFactorization f ⁻¹' s := by
          ext x
          constructor
          · intro hx
            rcases hx with ⟨y, hy, hxy⟩
            have hxy' : rangeFactorization f x = y := Subtype.ext hxy.symm
            simpa [hxy'] using hy
          · intro hx
            exact ⟨rangeFactorization f x, hx, rfl⟩
        rw [hpre]
        exact hs
      exact subtypeVal.isOpen_iff.mpr ⟨Subtype.val '' s, hopen, by
        ext y
        simp⟩
    · intro hs
      exact hs.preimage <| hf.continuous.rangeFactorization
  · rintro ⟨hsurj, hstrict⟩
    have hval : IsQuotientMap ((↑) : range f → Y) := by
      refine subtypeVal.isQuotientMap_of_surjective fun y ↦ ?_
      rcases hsurj y with ⟨x, rfl⟩
      exact ⟨rangeFactorization f x, rfl⟩
    simpa [IsStrictMap, Function.comp_def] using hval.comp hstrict

end Topology

/-! ### Lemma_5_6_4 (from Chap05) -/
open Set Topology

universe u v

/- 
Domain-style sampling for Lemma 5.6.4:
- primary domain: quotient maps and locally closed subsets in general topology
- owner declarations inspected: `IsOpenMap.isQuotientMap`,
  `IsOpenMap.preimage_closure_eq_closure_preimage`, `IsOpenQuotientMap`,
  `Topology.IsQuotientMap`, `coborder_preimage`
- best owner abstraction: `IsOpenQuotientMap f`
- primitive data: continuity and openness for the closure formula, and surjectivity in the
  source wording
- derived API: the quotient-map consequence, the closure formula, and the locally-closed
  preimage criterion

Layer triage:
- source-facing: `IsOpenMap.isQuotientMap`,
  `IsOpenMap.preimage_closure_eq_closure_preimage`
- core/canonical: `IsOpenQuotientMap`
- bridge/view: the source wording “submersive” identified in Definition `5.6.3` with the
  quotient-map owner
-/

/- `IsOpenQuotientMap f` is mathlib's owner notion for a surjective continuous open map; the
owner-level theorem below uses this abstraction to package the locally closed preimage criterion.
-/
recall IsOpenQuotientMap

/- Lemma 5.6.4: the source statement "a surjective continuous open map is a quotient map" is
exactly mathlib's theorem `IsOpenMap.isQuotientMap`. -/
recall IsOpenMap.isQuotientMap

/- Lemma 5.6.4 also includes the closure identity
`f ⁻¹' closure T = closure (f ⁻¹' T)`, which is exactly mathlib's theorem
`IsOpenMap.preimage_closure_eq_closure_preimage`; the source surjectivity hypothesis is redundant
for this clause. -/
recall IsOpenMap.preimage_closure_eq_closure_preimage

section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}

namespace IsOpenQuotientMap

-- Proof sketch: rewrite local closedness as openness of the coborder, use the coborder preimage
-- identity for continuous open maps, and then apply the quotient-map openness criterion.
/-- Under an open quotient map, a subset is locally closed exactly when its preimage is locally
closed. -/
theorem isLocallyClosed_iff_preimage (hf : IsOpenQuotientMap f) {T : Set Y} :
    IsLocallyClosed T ↔ IsLocallyClosed (f ⁻¹' T) := by
  rw [isLocallyClosed_iff_isOpen_coborder, isLocallyClosed_iff_isOpen_coborder,
    coborder_preimage hf.isOpenMap hf.continuous]
  have hq : IsQuotientMap f := hf.isQuotientMap
  exact hq.isOpen_preimage.symm

end IsOpenQuotientMap

/-- Lemma 5.6.4, source-facing form: for a surjective continuous open map, a subset of the
codomain is locally closed if and only if its preimage is locally closed. -/
theorem isLocallyClosed_iff_preimage_of_surjective_open
    (hcont : Continuous f) (hopen : IsOpenMap f) (hsurj : Function.Surjective f) {T : Set Y} :
    IsLocallyClosed T ↔ IsLocallyClosed (f ⁻¹' T) :=
  (⟨hsurj, hcont, hopen⟩ : IsOpenQuotientMap f).isLocallyClosed_iff_preimage

end

/-! ### Lemma_5_6_5 (from Chap05) -/
open Function Set Topology

universe u v

/- Domain-style sampling for Lemma 5.6.5:
- primary domain: quotient maps and locally closed subsets in general topology
- owner declarations inspected: `IsClosedMap.isQuotientMap`,
  `IsClosedMap.closure_image_eq_of_continuous`, `IsQuotientMap.isOpen_preimage`
- best owner abstraction: `IsQuotientMap f` for topology reflection, obtained canonically from
  `IsClosedMap.isQuotientMap`
- primitive data: `IsClosedMap f`, `Continuous f`, and `Surjective f`
- derived API: the closure formula, the locally-closed reflection statement, and the quotient-map
  corollary

Layer triage:
- source-facing: the closure formula for a surjective closed continuous map
- core/canonical: `IsClosedMap.isQuotientMap` and its `IsQuotientMap` consequences
- bridge/view: the source wording “submersive” identified in Definition `5.6.3` with the
  quotient-map owner
-/

/- Lemma 5.6.5: in particular, a surjective closed continuous map is a quotient map.
Definition 5.6.3 identifies this quotient-map owner with the Stacks notion of a submersive map. -/
recall IsClosedMap.isQuotientMap

section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {f : X → Y}

namespace IsClosedMap

/-- For a surjective closed continuous map, the closure of a subset of the codomain is the image
of the closure of its preimage. -/
-- Proof sketch: apply `IsClosedMap.closure_image_eq_of_continuous` to `f ⁻¹' T`, then use
-- surjectivity to identify `f '' (f ⁻¹' T)` with `T`.
theorem closure_eq_image_closure_preimage (hclosed : IsClosedMap f) (hcont : Continuous f)
    (hsurj : Surjective f)
    (T : Set Y) :
    closure T = f '' closure (f ⁻¹' T) := by
  simpa [hsurj.image_preimage] using
    hclosed.closure_image_eq_of_continuous hcont (f ⁻¹' T)

/-- A surjective closed continuous map reflects locally closed subsets along preimage. -/
-- Proof sketch: if `T` is locally closed then continuity gives local closedness of the preimage;
-- conversely, use the closure identity to identify `closure T` with the image of
-- `closure (f ⁻¹' T)`, restrict `f` to these closures, and apply the open-set criterion above.
theorem isLocallyClosed_iff_preimage (hclosed : IsClosedMap f) (hcont : Continuous f)
    (hsurj : Surjective f) {T : Set Y} :
    IsLocallyClosed T ↔ IsLocallyClosed (f ⁻¹' T) := by
  constructor
  · intro hT
    exact hT.preimage hcont
  · intro hpre
    have hmaps : MapsTo f (closure (f ⁻¹' T)) (closure T) :=
      (mapsTo_preimage f T).closure hcont
    let g : closure (f ⁻¹' T) → closure T := hmaps.restrict f (closure (f ⁻¹' T)) (closure T)
    have hgcont : Continuous g :=
      Continuous.restrict hmaps hcont
    have hgclosed : IsClosedMap g :=
      (hclosed.restrict isClosed_closure).codRestrict fun x ↦ hmaps x.2
    have hgsurj : Surjective g := by
      intro y
      have hy' : y.1 ∈ f '' closure (f ⁻¹' T) := by
        simpa [hclosed.closure_eq_image_closure_preimage hcont hsurj T] using y.2
      rcases hy' with ⟨x, hx, hxy⟩
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
    have hopen_preimage : IsOpen (((↑) : closure (f ⁻¹' T) → X) ⁻¹' (f ⁻¹' T)) :=
      hpre.isOpen_preimage_val_closure
    have hquot : IsQuotientMap g := hgclosed.isQuotientMap hgcont hgsurj
    have hopen : IsOpen (((↑) : closure T → Y) ⁻¹' T) := by
      exact hquot.isOpen_preimage.mp <| by
        simpa [g] using hopen_preimage
    exact ((isLocallyClosed_tfae T).out 4 0).mp hopen

end IsClosedMap

/-- A surjective closed continuous map is a quotient map, hence submersive in the source
terminology of Definition 5.6.3. -/
theorem isQuotientMap_of_surjective_closed_continuous
    (hclosed : IsClosedMap f) (hcont : Continuous f) (hsurj : Surjective f) :
    IsQuotientMap f :=
  hclosed.isQuotientMap hcont hsurj

end
