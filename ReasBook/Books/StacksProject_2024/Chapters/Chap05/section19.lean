import Mathlib
import Mathlib.Tactic.Recall
import Mathlib.Topology.Inseparable
import Mathlib.Topology.Sets.Closeds

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_5_19_1 (from Chap05) -/
universe u

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling for Definition 5.19.1:
- primary domain: specialization/generalization in a topological space
- owner declarations: `Specializes`, `specializes_iff_mem_closure`,
  `StableUnderSpecialization`, `StableUnderGeneralization`
- same-domain derived API: `IsClosed.stableUnderSpecialization`,
  `IsOpen.stableUnderGeneralization`, `stableUnderGeneralization_compl_iff`

Layer triage:
- `source-facing`: the Stacks terminology of specialization, generalization, and subsets stable
  under them
- `core/canonical`: the mathlib owner declarations above in `Topology.Inseparable`
- `bridge/view`: the closure characterization `specializes_iff_mem_closure`

There is no additional primitive data to define in this file. The numbered item is only recalling
existing canonical topology notions, so the correct public surface is direct `recall` of the owner
declarations rather than local aliases or wrapper definitions.
-/

/- Definition 5.19.1 (1): for points `x, x'` of a topological space, `x` is a specialization of
`x'` and `x'` is a generalization of `x` if and only if `x' ⤳ x` in the canonical specialization
relation `Specializes`. -/
recall Specializes

/- Definition 5.19.1 (1), closure characterization: the canonical equivalence
`specializes_iff_mem_closure` states that `x' ⤳ x` if and only if `x ∈ closure ({x'} : Set X)`. -/
recall specializes_iff_mem_closure

/- Definition 5.19.1 (2): a subset stable under specialization is the canonical predicate
`StableUnderSpecialization`. -/
recall StableUnderSpecialization

/- Definition 5.19.1 (3): a subset stable under generalization is the canonical predicate
`StableUnderGeneralization`. -/
recall StableUnderGeneralization

/-! ### Lemma_5_19_2 (from Chap05) -/
universe u

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling for Lemma 5.19.2:
- primary domain: specialization/generalization stability of subsets in a topological space
- inspected declarations:
  `StableUnderSpecialization`,
  `StableUnderGeneralization`,
  `IsClosed.stableUnderSpecialization`,
  `IsOpen.stableUnderGeneralization`,
  `stableUnderGeneralization_compl_iff`
- best owner abstraction: the canonical subset-stability predicates
  `StableUnderSpecialization` and `StableUnderGeneralization`
- primitive data: only a subset together with one of those owner predicates
- derived API: the closed/open consequences and the complement equivalence
  `stableUnderGeneralization_compl_iff`

Layer triage:
- `source-facing`: the three textbook facts relating closed sets, open sets, and complements to
  specialization/generalization stability
- `core/canonical`: `StableUnderSpecialization` and `StableUnderGeneralization`
- `bridge/view`: the canonical complement equivalence between those two owner predicates

The chapter owner entry-point is `Definition_5_19_1`, which already recalls the two predicates.
This file should therefore stay on that owner layer and recall only the derived canonical lemmas,
instead of rebuilding parallel local predicates or wrapper theorems.
-/

/- Lemma 5.19.2 (1) is recalled canonically by `IsClosed.stableUnderSpecialization`: any closed
subset of a topological space is stable under specialization. -/
recall IsClosed.stableUnderSpecialization

/- Lemma 5.19.2 (2) is recalled canonically by `IsOpen.stableUnderGeneralization`: any open
subset of a topological space is stable under generalization. -/
recall IsOpen.stableUnderGeneralization

/- Lemma 5.19.2 (3): a subset is stable under specialization if and only if its complement is
stable under generalization. This is recalled exactly by the canonical complement theorem
`stableUnderGeneralization_compl_iff`. -/
recall stableUnderGeneralization_compl_iff

/-! ### Lemma_5_19_3 (from Chap05) -/
universe u

open Set TopologicalSpace

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling for specialization-stable subsets:
- owner declaration: `stableUnderSpecialization_iff_exists_sUnion_eq`
- same-domain declarations inspected:
  `StableUnderSpecialization`,
  `IsClosed.stableUnderSpecialization`,
  `stableUnderSpecialization_sUnion`,
  `TopologicalSpace.Closeds`
- target layers here:
  - `core/canonical`: `stableUnderSpecialization_iff_exists_sUnion_eq`
  - `bridge/view`: the directed bundled-closed strengthening below

Primitive data is only the subset `T` together with the owner predicate
`StableUnderSpecialization T`. The closed family witnessing the union is derived API, and mathlib
already packages closed subsets canonically as `Closeds X`. A plain rebundling of the owner
theorem into `Set (Closeds X)` would add no new mathematics, so this file keeps the owner theorem
as a direct `recall` and exposes only the genuinely new directed strengthening. That
strengthening uses the canonical directed family of all bundled closed subsets contained in `T`,
rather than an arbitrary chosen family repaired by finite unions.
-/

/- Lemma 5.19.3: the canonical owner theorem is
`stableUnderSpecialization_iff_exists_sUnion_eq`, which expresses specialization-stable subsets as
unions of closed subsets. -/
recall stableUnderSpecialization_iff_exists_sUnion_eq

/-- Lemma 5.19.3, parenthetical strengthening: the family of bundled closed subsets can be chosen
directed under inclusion. -/
theorem stableUnderSpecialization_iff_exists_directed_closeds_sUnion_eq {T : Set X} :
    StableUnderSpecialization T ↔
      ∃ S : Set (Closeds X), DirectedOn (· ≤ ·) S ∧ ⋃₀ ((↑) '' S) = T := by
  constructor
  · intro hT
    refine ⟨{Z : Closeds X | (Z : Set X) ⊆ T}, ?_, ?_⟩
    · intro A hA B hB
      refine ⟨A ⊔ B, ?_, le_sup_left, le_sup_right⟩
      simpa using union_subset hA hB
    · ext x
      constructor
      · intro hx
        rcases mem_sUnion.mp hx with ⟨U, hU, hxU⟩
        rcases hU with ⟨Z, hZ, rfl⟩
        exact hZ hxU
      · intro hx
        refine mem_sUnion.mpr ⟨closure ({x} : Set X), ?_, subset_closure (by simp)⟩
        refine ⟨Closeds.closure {x}, ?_, rfl⟩
        intro y hy
        exact hT (specializes_iff_mem_closure.mpr hy) hx
  · rintro ⟨S, _, hT⟩
    rw [← hT]
    refine stableUnderSpecialization_sUnion _ ?_
    rintro U ⟨Z, hZ, rfl⟩
    exact Z.isClosed.stableUnderSpecialization

/-! ### Definition_5_19_4 (from Chap05) -/
universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/- Domain-style sampling for Definition 5.19.4:
- primary domain: specialization/generalization lifting for maps of topological spaces
- owner declarations inspected: `SpecializingMap`, `GeneralizingMap`,
  `specializingMap_iff_closure_singleton_subset`, `SpecializingMap.comp`
- best owner abstraction: the canonical owner predicates `SpecializingMap f` and
  `GeneralizingMap f`
- primitive data: only the lifting predicates themselves
- derived API: closure/image criteria and composition lemmas already supplied upstream by mathlib

Layer triage:
- `source-facing`: the Stacks definitions of specializing and generalizing maps
- `core/canonical`: `SpecializingMap` and `GeneralizingMap`
- `bridge/view`: none

There is no extra mathematical structure to package here. The numbered item is a recall of the
canonical owner predicates, so the public API should stay on those owners directly.
-/

/- Definition 5.19.4 (1): for a continuous map `f : X → Y`, saying that specializations lift along
`f` is exactly the canonical predicate `SpecializingMap f`. -/
recall SpecializingMap

/- Definition 5.19.4 (2): for a continuous map `f : X → Y`, saying that generalizations lift along
`f` is exactly the canonical predicate `GeneralizingMap f`. -/
recall GeneralizingMap

/-! ### Lemma_5_19_5 (from Chap05) -/
universe u v w

variable {X : Type u} {Y : Type v} {Z : Type w}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-
Domain-style sampling for specialization/generalization lifting:
- primitive owner predicates: `SpecializingMap f` and `GeneralizingMap f`
- derived canonical API in the same owner file: `SpecializingMap.comp`,
  `GeneralizingMap.comp`
- bridge/view layer: none needed here, since the Stacks statements are exactly the canonical
  composition lemmas

Layer triage:
- `source-facing`: lifting specializations/generalizations along a composite map
- `core/canonical`: the owner predicates `SpecializingMap` and `GeneralizingMap`
- `bridge/view`: none

Primitive data is the lifting predicate itself; composition is derived API, so this file should
recall the owner lemmas directly rather than introduce local wrapper theorems.
-/

/- Lemma 5.19.5: if specializations lift along both `f` and `g`, then specializations lift along
`g ∘ f`. This is exactly the canonical mathlib theorem `SpecializingMap.comp`. -/
recall SpecializingMap.comp

/- Lemma 5.19.5: similarly, if generalizations lift along both `f` and `g`, then generalizations
lift along `g ∘ f`. This is exactly the canonical mathlib theorem `GeneralizingMap.comp`. -/
recall GeneralizingMap.comp

/-! ### Lemma_5_19_6 (from Chap05) -/
universe u v

open Set

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/- Domain-style sampling for Lemma 5.19.6:
- primary domain: specialization/generalization-stable subsets in topology
- inspected owner declarations: `StableUnderSpecialization`, `StableUnderGeneralization`,
  `SpecializingMap.stableUnderSpecialization_image`,
  `GeneralizingMap.stableUnderGeneralization_image`
- best owner abstraction: the lifting predicates `SpecializingMap f` and `GeneralizingMap f`,
  together with their canonical image lemmas

Layer triage:
- `source-facing`: image-stability of specialization-stable and generalization-stable subsets
- `core/canonical`: `StableUnderSpecialization`, `StableUnderGeneralization`, `SpecializingMap`,
  `GeneralizingMap`
- `bridge/view`: none

Primitive data here is only a subset together with its stability predicate, plus a map satisfying
the corresponding lifting property. The image statements are derived API of the map-lifting owner
predicates, so local wrapper theorems or recall of secondary aliases would only duplicate the
canonical mathlib surface.
-/

/- Lemma 5.19.6 (1): the image of a specialization-stable subset under a specializing map is
again specialization-stable. This is exactly the canonical owner theorem
`SpecializingMap.stableUnderSpecialization_image`; the separate continuity hypothesis is
redundant. -/
recall SpecializingMap.stableUnderSpecialization_image

/- Lemma 5.19.6 (2): the image of a generalization-stable subset under a generalizing map is again
generalization-stable. This is exactly the canonical owner theorem
`GeneralizingMap.stableUnderGeneralization_image`; the separate continuity hypothesis is
redundant. -/
recall GeneralizingMap.stableUnderGeneralization_image

/-! ### Lemma_5_19_7 (from Chap05) -/
universe u v

open Set TopologicalSpace

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/- Domain-style sampling for Lemma 5.19.7:
- primary domain: specialization/generalization lifting for maps of topological spaces
- inspected owner declarations:
  `SpecializingMap`,
  `GeneralizingMap`,
  `IsClosedMap.specializingMap`,
  `TopologicalSpace.IsOpenCover.generalizingMap_iff_comp`
- best owner abstraction: the map-lifting owner predicates `SpecializingMap f` and
  `GeneralizingMap f`
- primitive data: a map `f : X → Y` with the geometric hypotheses needed to force one of those
  owner predicates
- derived API: clause `(1)` is already the canonical owner theorem
  `IsClosedMap.specializingMap`, while clause `(2)` is a source-facing sufficient criterion for
  `GeneralizingMap f`

Layer triage:
- `source-facing`: the Stacks criterion that an open continuous map from a Noetherian quasi-sober
  source to a `T₀` target is generalizing
- `core/canonical`: `SpecializingMap` and `GeneralizingMap`
- `bridge/view`: none

Primitive data here is only the map together with open-map and continuity hypotheses; the conclusion
is the canonical owner predicate `GeneralizingMap f`. The file should therefore recall clause `(1)`
directly from mathlib and state clause `(2)` as a theorem returning that owner predicate, without a
parallel local wrapper notion.
-/

-- Proof sketch: closed subsets are stable under specialization, and the image of a closed subset
-- under a closed map is closed again; applied to closures of singletons, this is exactly the
-- specializing-map lifting condition.
/- Lemma 5.19.7 (1) is recalled canonically by `IsClosedMap.specializingMap`: a closed map is
specializing, and the canonical mathlib theorem is stronger than the Stacks phrasing because it
does not require continuity separately. -/
recall IsClosedMap.specializingMap

-- Proof sketch: for a point `x` over the specialization target, every open neighbourhood of `x`
-- meets the fibre over the specialization source because `f` is open; in a Noetherian space one
-- passes to an irreducible component of that fibre, chooses its generic point using quasi-sobriety,
-- and the `T₀` condition forces that generic point to map to the prescribed source point.
namespace IsOpenMap

/-- An open continuous map from a Noetherian quasi-sober space to a Kolmogorov space is
generalizing. -/
theorem generalizingMap_of_noetherianSpace_quasiSober_t0 [NoetherianSpace X] [QuasiSober X]
    [T0Space Y] {f : X → Y} (hopen : IsOpenMap f) (hf : Continuous f) : GeneralizingMap f := by
  intro x y hy
  have hx_closure : x ∈ closure (f ⁻¹' ({y} : Set Y)) := by
    rw [← hopen.preimage_closure_eq_closure_preimage hf ({y} : Set Y)]
    simpa [mem_preimage, specializes_iff_mem_closure] using hy
  let C : Set X := closure (f ⁻¹' ({y} : Set Y))
  have hC_closed : IsClosed C := by
    simp [C]
  have hC_closedEmb := hC_closed.isClosedEmbedding_subtypeVal
  let xC : C := ⟨x, by simpa [C] using hx_closure⟩
  haveI : QuasiSober C := hC_closedEmb.quasiSober
  let A : Set C := {z | f z = y}
  have hA_image : Subtype.val '' A = f ⁻¹' ({y} : Set Y) := by
    ext z
    constructor
    · rintro ⟨z', hz', rfl⟩
      simpa [A] using hz'
    · intro hz
      refine ⟨⟨z, by simpa [C] using subset_closure hz⟩, ?_, rfl⟩
      simpa [A] using hz
  have hA_closure : closure A = univ := by
    rw [hC_closedEmb.isEmbedding.closure_eq_preimage_closure_image, hA_image]
    ext z
    simp [C]
  have hA_dense : Dense A := dense_iff_closure_eq.mpr hA_closure
  let Z : Set C := irreducibleComponent xC
  have hZ_mem : Z ∈ irreducibleComponents C := irreducibleComponent_mem_irreducibleComponents xC
  obtain ⟨o, ho, hone, hoZ⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent Z hZ_mem
  obtain ⟨zC, hzo, hzA⟩ := hA_dense.inter_open_nonempty o ho hone
  have hzZ : zC ∈ Z := hoZ hzo
  have hZ_irr : IsIrreducible Z := isIrreducible_irreducibleComponent
  have hZ_closed : IsClosed Z := isClosed_irreducibleComponent
  let ξC : C := hZ_irr.genericPoint
  have hξC : IsGenericPoint ξC Z := hZ_irr.isGenericPoint_genericPoint hZ_closed
  have hξx : (ξC : X) ⤳ x :=
    (subtype_specializes_iff ξC xC).mp (hξC.specializes mem_irreducibleComponent)
  have hξz : (ξC : X) ⤳ (zC : X) :=
    (subtype_specializes_iff ξC zC).mp (hξC.specializes hzZ)
  have hzfy : f zC = y := hzA
  have hfξy : f ξC ⤳ y := by
    simpa [hzfy] using hξz.map hf
  have hyfξ : y ⤳ f ξC := by
    rw [specializes_iff_mem_closure]
    change (ξC : X) ∈ f ⁻¹' closure ({y} : Set Y)
    rw [hopen.preimage_closure_eq_closure_preimage hf ({y} : Set Y)]
    simp [C]
  refine ⟨ξC, hξx, ?_⟩
  exact (hyfξ.antisymm hfξy).eq.symm

end IsOpenMap

/-! ### Lemma_5_19_8 (from Chap05) -/
universe u v w

section

variable {R : Type u} {U : Type v} {X : Type w}
variable [TopologicalSpace R] [TopologicalSpace U] [TopologicalSpace X]
variable [T0Space U] [QuasiSober U]
variable (s t : R → U) (π : U → X)

omit [TopologicalSpace R] [TopologicalSpace U] [TopologicalSpace X] [T0Space U] [QuasiSober U] in
/-- Helper for Lemma 5.19.8: the `π`-fiber over `π u` is exactly the image of the `s`-fiber over
`u` under `t`. -/
lemma pi_fiber_eq_image_preimage
    (hπ_quot : ∀ u v : U, Setoid.ker π u v ↔ ∃ r : R, t r = u ∧ s r = v)
    (u : U) :
    π ⁻¹' ({π u} : Set X) = t '' (s ⁻¹' ({u} : Set U)) := by
  -- Rewrite the quotient relation into the source relation coming from `s` and `t`.
  ext v
  constructor
  · intro hv
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hv
    obtain ⟨r, htr, hsr⟩ := (hπ_quot v u).mp hv
    refine ⟨r, ?_, htr⟩
    rw [Set.mem_preimage, Set.mem_singleton_iff]
    exact hsr
  · rintro ⟨r, hr, htr⟩
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hr ⊢
    simpa [htr] using (hπ_quot (t r) u).mpr ⟨r, rfl, hr⟩

omit [TopologicalSpace R] [TopologicalSpace U] [TopologicalSpace X] [T0Space U] [QuasiSober U] in
/-- Helper for Lemma 5.19.8: every `π`-fiber is finite because it is the image of a finite
`s`-fiber. -/
lemma finite_pi_fiber
    (hs_finite : ∀ u : U, Set.Finite (s ⁻¹' ({u} : Set U)))
    (hπ_quot : ∀ u v : U, Setoid.ker π u v ↔ ∃ r : R, t r = u ∧ s r = v)
    (u : U) :
    Set.Finite (π ⁻¹' ({π u} : Set X)) := by
  -- Replace the `π`-fiber by an explicit image of the finite source fiber.
  rw [pi_fiber_eq_image_preimage (s := s) (t := t) (π := π) hπ_quot u]
  exact (hs_finite u).image t

omit [T0Space U] [QuasiSober U] in
/-- Helper for Lemma 5.19.8: over an open quotient map, specialization in the quotient lifts to a
specialization between chosen representatives once the source fiber is finite. -/
lemma exists_specializing_lift_in_fiber_of_open_quotient
    (hπ_openQuot : IsOpenQuotientMap π)
    {u v v' : U} (hx : π u ⤳ π v) (hv' : π v' = π v)
    (hfinite : Set.Finite (π ⁻¹' ({π u} : Set X))) :
    ∃ u' : U, π u' = π u ∧ u' ⤳ v' := by
  classical
  -- Route correction: the lift comes from openness of `π`, not from transporting
  -- specialization through `s` and `t`.
  let F : Set U := π ⁻¹' ({π u} : Set X)
  by_contra hno
  have hno' : ∀ u' : F, ¬ ((u' : U) ⤳ v') := by
    intro u' hu'spec
    apply hno
    refine ⟨u', ?_, hu'spec⟩
    change π u' = π u
    exact u'.2
  -- Choose, for each point in the finite fiber, an open neighborhood of `v'` avoiding it.
  choose W hWopen hv'W hu'W using
    fun u' : F => (not_specializes_iff_exists_open).mp (hno' u')
  letI : Fintype F := hfinite.fintype
  let V : Set U := ⋂ u' : F, W u'
  have hVopen : IsOpen V := by
    -- Intersect finitely many separating neighborhoods.
    simpa [V] using isOpen_iInter_of_finite (fun u' : F => hWopen u')
  have hv'V : v' ∈ V := by
    -- The chosen target lift lies in every neighborhood of the finite family.
    simpa [V] using fun u' : F => hv'W u'
  have hπspec : π u ⤳ π v' := by
    simpa [hv'] using hx
  have hπuV : π u ∈ π '' V := by
    -- Any open neighborhood of `π v'` must contain `π u`.
    apply hπspec.mem_open (hπ_openQuot.isOpenMap _ hVopen)
    exact ⟨v', hv'V, rfl⟩
  obtain ⟨u', hu'V, hu'π⟩ := hπuV
  have hu'F : u' ∈ F := by
    simpa [F, Set.mem_preimage, Set.mem_singleton_iff] using hu'π
  have hu'VW : ∀ a : F, u' ∈ W a := by
    simpa [V] using hu'V
  exact hu'W ⟨u', hu'F⟩ (hu'VW ⟨u', hu'F⟩)

omit [TopologicalSpace R] [QuasiSober U] in
/-- Helper for Lemma 5.19.8: mutual specialization in the quotient forces equality once the fibers
are finite and the quotient map is open. -/
lemma eq_of_mutual_specialization_of_open_quotient_finite_fibers
    (hπ_openQuot : IsOpenQuotientMap π)
    (hs_finite : ∀ u : U, Set.Finite (s ⁻¹' ({u} : Set U)))
    (hπ_quot : ∀ u v : U, Setoid.ker π u v ↔ ∃ r : R, t r = u ∧ s r = v)
    {x y : X} (hxy : x ⤳ y) (hyx : y ⤳ x) :
    x = y := by
  obtain ⟨u₀, rfl⟩ := hπ_openQuot.surjective x
  obtain ⟨v₀, rfl⟩ := hπ_openQuot.surjective y
  let Fx : Set U := π ⁻¹' ({π u₀} : Set X)
  let Fy : Set U := π ⁻¹' ({π v₀} : Set X)
  have hFx_fin : Set.Finite Fx := by
    simpa [Fx] using finite_pi_fiber (s := s) (t := t) (π := π) hs_finite hπ_quot u₀
  have hFy_fin : Set.Finite Fy := by
    simpa [Fy] using finite_pi_fiber (s := s) (t := t) (π := π) hs_finite hπ_quot v₀
  letI : PartialOrder U := specializationOrder U
  obtain ⟨u, huFx, huMax⟩ := hFx_fin.exists_maximal ⟨u₀, by simp [Fx]⟩
  have huπ : π u = π u₀ := by
    simpa [Fx, Set.mem_preimage, Set.mem_singleton_iff] using huFx
  -- Lift `π v₀ ⤳ π u₀` to a representative of the `π v₀`-fiber specializing to `u`.
  obtain ⟨v, hvπ, hvu⟩ :=
    exists_specializing_lift_in_fiber_of_open_quotient
      (π := π) hπ_openQuot hyx huπ hFy_fin
  -- Lift `π u₀ ⤳ π v₀` back to the `π u₀`-fiber and compare with maximality of `u`.
  obtain ⟨u', hu'π, hu'v⟩ :=
    exists_specializing_lift_in_fiber_of_open_quotient
      (π := π) hπ_openQuot hxy hvπ hFx_fin
  have hu'Fx : u' ∈ Fx := by
    simpa [Fx, Set.mem_preimage, Set.mem_singleton_iff] using hu'π
  have huu' : u ≤ u' := by
    exact hu'v.trans hvu
  have hu'leu : u' ≤ u := huMax hu'Fx huu'
  have huu'_eq : u = u' := le_antisymm huu' hu'leu
  have huv : u ⤳ v := by
    simpa [huu'_eq] using hu'v
  have huv_eq : u = v := by
    apply le_antisymm
    · exact hvu
    · exact huv
  -- Once the two chosen lifts coincide, their quotient points coincide as well.
  calc
    π u₀ = π u := huπ.symm
    _ = π v := by rw [huv_eq]
    _ = π v₀ := hvπ

/-- Lemma 5.19.8, source-facing bridge: let `π : U → X` be an open quotient map with `U`
quasi-sober and `T₀`. Assume the source-facing relation `(u, v) ↦ ∃ r, t r = u ∧ s r = v`
agrees with `Setoid.ker π`, the fibres of `s` are finite, and generalizations lift along both
`s` and `t`. Then `X` is Kolmogorov. -/
theorem t0Space_of_open_quotient_of_quasiSober_of_finiteFibers
    (hπ_openQuot : IsOpenQuotientMap π)
    (hs_finite : ∀ u : U, Set.Finite (s ⁻¹' ({u} : Set U)))
    (hs_gen : GeneralizingMap s) (ht_gen : GeneralizingMap t)
    (hπ_quot : ∀ u v : U, Setoid.ker π u v ↔ ∃ r : R, t r = u ∧ s r = v) :
    T0Space X := by
  -- The quotient is `T₀` once mutual specialization of quotient points collapses.
  refine (t0Space_iff_inseparable X).2 ?_
  intro x y hxy
  let _ := (inferInstance : QuasiSober U)
  let _ := hs_gen
  let _ := ht_gen
  exact eq_of_mutual_specialization_of_open_quotient_finite_fibers
    (s := s) (t := t) (π := π) hπ_openQuot hs_finite hπ_quot
    hxy.specializes hxy.specializes'

end

/-! ### Lemma_5_19_9 (from Chap05) -/
universe u v

/-
Domain-style sampling for Lemma 5.19.9:
- primary domain: topological Krull dimension under specialization/generalization-lifting maps
- owner declarations inspected: `topologicalKrullDim`, `SpecializingMap`, `GeneralizingMap`, and
  the quasi-sober generic-point API `IsIrreducible.genericPoint`
- best owner abstraction: the canonical dimension owner `topologicalKrullDim` together with the
  map-lifting predicates `SpecializingMap f` and `GeneralizingMap f`; the only target-space
  irreducible-closed data needed in the proof is supplied canonically by `[QuasiSober Y]`
- primitive data: a surjective map carrying one of the two canonical lifting predicates, with
  quasi-sobriety on the target to choose generic points of irreducible closed subsets
- derived API: the disjunctive source-facing dimension inequality

Layer triage:
- `source-facing`: the dimension inequality for a surjective map along which specializations or
  generalizations lift
- `core/canonical`: `topologicalKrullDim`, `SpecializingMap`, `GeneralizingMap`, `QuasiSober`
- `bridge/view`: none

The file already uses the correct owner predicates, so the refinement here is only to keep the
public statement on that canonical layer, with only the quasi-sober generic-point hypothesis that
the proof actually uses, and keep the two directional cases as internal branches of one proof
rather than as separate local declarations.
-/

section

open Set Function Order TopologicalSpace Topology TopologicalSpace.IrreducibleCloseds

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable [QuasiSober Y] {f : X → Y}

/-- Helper for Lemma 5.19.9: the irreducible closed subset generated by a point. -/
def pointClosure (x : X) : IrreducibleCloseds X :=
  ⟨closure ({x} : Set X), isIrreducible_singleton.closure, isClosed_closure⟩

/-- Helper for Lemma 5.19.9: inclusion of irreducible closed subsets makes generic points
specialize in the opposite direction. -/
lemma genericPoint_specializes_of_le {S T : IrreducibleCloseds Y} (hST : S ≤ T) :
    T.isIrreducible.genericPoint ⤳ S.isIrreducible.genericPoint := by
  -- The generic point of the larger closed set specializes to every point it contains.
  let hTgp := T.isIrreducible.isGenericPoint_genericPoint T.isClosed
  let hSgp := S.isIrreducible.isGenericPoint_genericPoint S.isClosed
  exact hTgp.specializes (hST hSgp.mem)

omit [TopologicalSpace X] [TopologicalSpace Y] [QuasiSober Y] in
/-- Helper for Lemma 5.19.9: a surjective fibration lifts a finite relation chain pointwise. -/
lemma exists_lift_of_fibration {rX : X → X → Prop} {rY : Y → Y → Prop}
    (hFib : Relation.Fibration rX rY f) (hSurj : Function.Surjective f) :
    ∀ {n : ℕ} (y : Fin (n + 1) → Y),
      (∀ i : Fin n, rY (y i.succ) (y (Fin.castSucc i))) →
      ∃ x : Fin (n + 1) → X,
        (∀ i, f (x i) = y i) ∧
        ∀ i : Fin n, rX (x i.succ) (x (Fin.castSucc i))
  | 0, y, _ => by
      -- A chain of length `0` is a single point, so surjectivity gives its lift immediately.
      rcases hSurj (y 0) with ⟨x0, hx0⟩
      refine ⟨fun _ ↦ x0, ?_, ?_⟩
      · intro i
        fin_cases i
        simpa using hx0
      · intro i
        exact Fin.elim0 i
  | n + 1, y, hy => by
      -- Lift the initial segment first, then use the fibration property for the final step.
      let yInit : Fin (n + 1) → Y := y ∘ Fin.castSucc
      have hyInit : ∀ i : Fin n, rY (yInit i.succ) (yInit (Fin.castSucc i)) := by
        intro i
        simpa [yInit, Function.comp_apply, Fin.castSucc_succ] using hy (Fin.castSucc i)
      rcases exists_lift_of_fibration hFib hSurj yInit hyInit with ⟨xInit, hxInit, hxStep⟩
      have hLast : rY (y (Fin.last (n + 1))) (f (xInit (Fin.last n))) := by
        rw [hxInit (Fin.last n)]
        simpa using hy (Fin.last n)
      rcases hFib hLast with ⟨xLast, hxLast, hfxLast⟩
      refine ⟨(Fin.snoc xInit xLast : Fin (n + 2) → X), ?_, ?_⟩
      · intro i
        refine Fin.lastCases ?_ ?_ i
        · simpa using hfxLast
        · intro j
          simpa [Fin.snoc_castSucc] using hxInit j
      · intro i
        refine Fin.lastCases ?_ ?_ i
        · simpa [Fin.snoc_last] using hxLast
        · intro j
          have hsucc : (Fin.snoc xInit xLast : Fin (n + 2) → X) j.castSucc.succ = xInit j.succ := by
            rw [show j.castSucc.succ = (j.succ).castSucc from (Fin.castSucc_succ j).symm,
              Fin.snoc_castSucc]
          rw [hsucc]
          simpa [Fin.snoc_castSucc] using hxStep j

/-- Helper for Lemma 5.19.9: lifting compatible generic points turns a strict target inclusion into
an equally strict inclusion of point-closures upstairs. -/
lemma pointClosure_lt_of_lifted_generic_points (hf : Continuous f)
    {S T : IrreducibleCloseds Y} (hST : S < T) {xS xT : X}
    (hx : xT ⤳ xS)
    (hfxS : f xS = S.isIrreducible.genericPoint)
    (hfxT : f xT = T.isIrreducible.genericPoint) :
    pointClosure xS < pointClosure xT := by
  refine lt_of_le_of_ne ?_ ?_
  · -- A specialization upstairs gives the expected inclusion of closures.
    simpa [pointClosure] using (specializes_iff_closure_subset.mp hx)
  · intro hEq
    -- Route correction: equality of the lifted closures would force a reverse specialization,
    -- whose image contradicts the strict target inclusion.
    have hEqSet : (pointClosure xS : Set X) = pointClosure xT :=
      congrArg (fun Z : IrreducibleCloseds X ↦ (Z : Set X)) hEq
    have hrev : xS ⤳ xT := by
      apply specializes_iff_closure_subset.mpr
      simpa [pointClosure] using hEqSet.symm.subset
    have hImageRev : S.isIrreducible.genericPoint ⤳ T.isIrreducible.genericPoint := by
      rw [← hfxS, ← hfxT]
      exact hf.specialization_monotone hrev
    have hTS : T ≤ S := by
      simpa [T.isIrreducible.closure_genericPoint T.isClosed,
        S.isIrreducible.closure_genericPoint S.isClosed] using
        (specializes_iff_closure_subset.mp hImageRev)
    exact hST.ne (le_antisymm hST.le hTS)

/-- Lemma 5.19.9: if `f : X → Y` is surjective, `Y` is sober, and either specializations or
generalizations lift along `f`, then the topological Krull dimension of `X` is at least that of
`Y`. For this dimension comparison, the source sober hypothesis is used only through the canonical
generic-point owner `[QuasiSober Y]`. -/
theorem topologicalKrullDim_le_of_surjective_specializing_or_generalizing
    (hf : Continuous f) (hSurj : Function.Surjective f)
    (hLift : SpecializingMap f ∨ GeneralizingMap f) :
    topologicalKrullDim Y ≤ topologicalKrullDim X := by
  classical
  -- Route correction: work chainwise on generic points and then pass to point-closures in `X`.
  rw [topologicalKrullDim, Order.krullDim]
  refine iSup_le ?_
  intro p
  let y : Fin (p.length + 1) → Y := fun i ↦ (p i).isIrreducible.genericPoint
  have hy : ∀ i : Fin p.length, y i.succ ⤳ y (Fin.castSucc i) := by
    -- Successive terms in the target chain give successive specializations of generic points.
    intro i
    exact genericPoint_specializes_of_le (p.step i).le
  rcases hLift with hSpec | hGen
  · -- Reverse the target chain so that the specializing-map fibration can be used in forward order.
    let yRev : Fin (p.length + 1) → Y := y ∘ Fin.rev
    have hyRev : ∀ i : Fin p.length, (yRev (Fin.castSucc i)) ⤳ yRev i.succ := by
      intro i
      simpa [yRev, Function.comp_apply, Fin.rev_castSucc, Fin.rev_succ] using hy i.rev
    rcases exists_lift_of_fibration (f := f) (rX := flip (· ⤳ ·)) (rY := flip (· ⤳ ·))
        hSpec hSurj yRev hyRev with ⟨xRev, hxRev, hxRevStep⟩
    let x : Fin (p.length + 1) → X := xRev ∘ Fin.rev
    have hx : ∀ i, f (x i) = y i := by
      -- Undo the reversal to recover lifts of the original generic points.
      intro i
      simpa [x, yRev, Function.comp_apply, Fin.rev_rev] using hxRev i.rev
    have hxStep : ∀ i : Fin p.length, x i.succ ⤳ x (Fin.castSucc i) := by
      -- The reversed lifted chain turns back into the desired specialization chain upstairs.
      intro i
      simpa [x, Function.comp_apply, Fin.rev_succ, Fin.rev_castSucc] using hxRevStep i.rev
    let q : LTSeries (IrreducibleCloseds X) :=
      LTSeries.mk p.length (fun i ↦ pointClosure (x i)) <|
        (Fin.strictMono_iff_lt_succ (f := fun i ↦ pointClosure (x i))).2 fun i ↦ by
          exact pointClosure_lt_of_lifted_generic_points hf (p.step i) (hxStep i)
            (hx (Fin.castSucc i)) (hx i.succ)
    -- The lifted strict chain in `IrreducibleCloseds X` has the same length as the original one.
    simpa [topologicalKrullDim, Order.krullDim] using (Order.LTSeries.length_le_krullDim q)
  · -- A generalizing map lifts the generic-point chain directly in the given order.
    rcases exists_lift_of_fibration (f := f) (rX := (· ⤳ ·)) (rY := (· ⤳ ·)) hGen hSurj y hy with
      ⟨x, hx, hxStep⟩
    let q : LTSeries (IrreducibleCloseds X) :=
      LTSeries.mk p.length (fun i ↦ pointClosure (x i)) <|
        (Fin.strictMono_iff_lt_succ (f := fun i ↦ pointClosure (x i))).2 fun i ↦ by
          exact pointClosure_lt_of_lifted_generic_points hf (p.step i) (hxStep i)
            (hx (Fin.castSucc i)) (hx i.succ)
    -- The same closure argument turns the lifted point chain into a strict chain upstairs.
    simpa [topologicalKrullDim, Order.krullDim] using (Order.LTSeries.length_le_krullDim q)

end

/-! ### Lemma_5_19_10 (from Chap05) -/
universe u

open Set TopologicalSpace Topology
open scoped Set.Notation

section

variable {X : Type u} [TopologicalSpace X] [NoetherianSpace X] [QuasiSober X]

/-
Domain-style sampling for constructible subsets stable under specialization/generalization:
- primary domain: constructible subsets in Noetherian quasi-sober spaces, together with the
  canonical specialization/generalization stability predicates;
- inspected owner declarations:
  `Topology.IsConstructible.mem_nhds_iff_forall_dense_irreducibleCloseds_trace`,
  `isOpen_iff_forall_irreducibleCloseds_inter_empty_or_contains_nonempty_open`,
  `StableUnderSpecialization`,
  `StableUnderGeneralization`;
- best owner abstraction: the source-facing conclusions `IsClosed E` and `IsOpen E`, supported by
  the canonical owner predicate `Topology.IsConstructible` and the stability predicates from
  `Topology.Inseparable`;
- primitive data: only the constructible subset `E` and its stability under specialization or
  generalization;
- derived API: openness/closedness of `E`, obtained through irreducible closed traces and the
  complement bridge `StableUnderSpecialization.compl`.

Layer triage:
- `source-facing`: Lemma 5.19.10, asserting that constructible subsets stable under specialization
  are closed and those stable under generalization are open;
- `core/canonical`: `Topology.IsConstructible`, `StableUnderSpecialization`, and
  `StableUnderGeneralization`;
- `bridge/view`: the irreducible-closed trace criteria from Lemmas `5.16.4` and `5.16.5`.

There is no earlier exact theorem owner for this statement in the chapter, so the public surface
here should stay source-facing. The redundant `T0Space` binder is not primitive data for either
part and is removed.
-/

private theorem isOpen_of_isConstructible_of_stableUnderGeneralization_aux {E : Set X}
    (hE : IsConstructible E) (hE_gen : StableUnderGeneralization E) : IsOpen E := by
  classical
  rw [isOpen_iff_forall_irreducibleCloseds_inter_empty_or_contains_nonempty_open]
  intro Y
  by_cases hYE : ((Y : Set X) ↓∩ E : Set Y) = ∅
  · exact Or.inl hYE
  · right
    let EY : Set Y := (Y : Set X) ↓∩ E
    let hY_closedEmb := Y.isClosed.isClosedEmbedding_subtypeVal
    letI : NoetherianSpace Y := IsInducing.subtypeVal.noetherianSpace
    letI : QuasiSober Y := hY_closedEmb.quasiSober
    have hYE_constructible : IsConstructible EY := by
      simpa [EY] using
        hE.preimage_of_isClosedEmbedding hY_closedEmb (NoetherianSpace.isCompact _)
    haveI : IrreducibleSpace Y := Subtype.irreducibleSpace Y.isIrreducible
    have hηE : genericPoint Y ∈ EY := by
      dsimp [EY]
      obtain ⟨y, hyE⟩ : EY.Nonempty := Set.nonempty_iff_ne_empty.mpr hYE
      exact hE_gen (by
        simpa [subtype_specializes_iff] using (genericPoint_specializes y : genericPoint Y ⤳ y))
        hyE
    have hYE_nhds : EY ∈ 𝓝 (genericPoint Y) := by
      refine (hYE_constructible.mem_nhds_iff_forall_dense_irreducibleCloseds_trace).2 ?_
      intro Z hηZ
      rw [Subtype.dense_iff]
      intro z hz
      have hη_closure :
          genericPoint Y ∈ closure ((Subtype.val : Z → Y) '' ((Subtype.val : Z → Y) ⁻¹' EY)) := by
        exact subset_closure ⟨⟨genericPoint Y, hηZ⟩, hηE, rfl⟩
      have hsubset :
          (Set.univ : Set Y) ⊆ closure ((Subtype.val : Z → Y) '' ((Subtype.val : Z → Y) ⁻¹' EY)) :=
        ((genericPoint_spec Y).mem_closed_set_iff isClosed_closure).1 hη_closure
      exact hsubset trivial
    rcases mem_nhds_iff.mp hYE_nhds with ⟨U, hU_subset, hU_open, hηU⟩
    refine ⟨⟨U, hU_open⟩, ⟨genericPoint Y, hηU⟩, ?_⟩
    simpa [EY] using hU_subset

-- Proof sketch: apply the constructible irreducible-closed criterion from Lemma `5.16.3` to the
-- trace on each irreducible closed subset, use the generic point provided by quasi-sobriety, and
-- then conclude openness of the complement by Lemma `5.16.5`.
/-- Lemma 5.19.10 (1): in a Noetherian sober topological space, a constructible subset stable under
specialization is closed. -/
theorem isClosed_of_isConstructible_of_stableUnderSpecialization {E : Set X}
    (hE : IsConstructible E) (hE_spec : StableUnderSpecialization E) : IsClosed E := by
  rw [← isOpen_compl_iff]
  exact isOpen_of_isConstructible_of_stableUnderGeneralization_aux hE.compl hE_spec.compl

-- Proof sketch: for each irreducible closed subset `Y`, if the trace `E ∩ Y` is nonempty then the
-- generic point of `Y` belongs to `E` by stability under generalization, so `E ∩ Y` is dense and
-- Lemma `5.16.3` yields a nonempty open trace; conclude by Lemma `5.16.5`.
/-- Lemma 5.19.10 (2): in a Noetherian sober topological space, a constructible subset stable under
generalization is open. -/
theorem isOpen_of_isConstructible_of_stableUnderGeneralization {E : Set X}
    (hE : IsConstructible E) (hE_gen : StableUnderGeneralization E) : IsOpen E :=
  isOpen_of_isConstructible_of_stableUnderGeneralization_aux hE hE_gen

end
