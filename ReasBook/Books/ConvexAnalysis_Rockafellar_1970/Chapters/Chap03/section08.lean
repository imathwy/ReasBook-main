import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_3_8_1 (from Chap01) -/
section

variable (k : Type*)
variable {E : Type*}

/-
Source/core/bridge triage:
- `source-facing`: Text 3.8.1 introduces the umbra of two subsets `C` and `S` by an explicit
  intersection-of-slices formula built from the affine images of `C` seen from points `x ∈ S`.
- `core/canonical`: the owner abstraction is `Set E`; the defining operations are indexed
  intersections (intrinsically indexed by `x : S`), the fixed-`x` binary-image owner
  `Set.image2`, and the affine map
  `(λ, c) ↦ (1 - λ) • x + λ • c`. The stronger affine-owner API
  `AffineMap.lineMap_apply_module` was checked as the upstream candidate for the displayed affine
  combination, but it requires `[AddCommGroup E]`, so there is no upstream owner duplicating this
  source-facing construction in the weaker additive-action setting of this file.
- `bridge/view`: `mem_umbra_iff` keeps membership at the intrinsic owner layer as the subtype
  slice condition “for every `x : S`, `y ∈ umbraSlice C x`”, while
  `mem_umbra_iff_forall_mem` and `mem_umbra_iff_forall_exists_affine_mem` give the ambient
  source-facing bridges over `x ∈ S`.
- Primitive data vs derived API: the fixed-`x` affine-image slice and the resulting umbra are
  concrete subsets determined by `C`, `x`, and `S`; the source-side assumption that `C` and `S`
  are disjoint is extrinsic to these formulas, so it is not built into the definition.
- Domain-style sampling: this item follows the project pattern of source-facing set-valued
  definitions used for `homogenizationSet`, `inverseAddition`, and the adjacent `penumbra`,
  together with the owner-side `Set.image2`, `Set.mem_iInter`, and `Convex.affinity` API. The
  stronger affine-map owner `AffineMap.lineMap_apply_module` was also
  checked, but it would force `[AddCommGroup E]` and therefore does not replace this source-facing
  owner.
- Layer target: `source-facing`; `umbra` remains the public source-facing owner, while
  `umbraSlice` is the minimal owner-side auxiliary capturing the fixed-`x` affine-image slice
  reused directly by the adjacent penumbra/convexity files.
-/

section Core

open scoped Rockafellar

variable [One k] [Sub k] [LE k] [Add E] [SMul k E]

/-- The fixed-`x` affine-image slice used in the umbra and penumbra constructions. -/
def umbraSlice (C : Set E) (x : E) : Set E :=
  Set.image2 (fun a c ↦ (1 - a) • x + a • c) {a : k | 1 ≤ a} C

scoped[Rockafellar] notation:max "umbraSlice[" k " | " C ", " x "]" => umbraSlice k C x

/-- A point lies in `umbraSlice C x` exactly when it can be written as `(1 - λ) • x + λ • c`
for some `λ ≥ 1` and some `c ∈ C`. -/
@[simp] theorem mem_umbraSlice_iff (C : Set E) (x y : E) :
    y ∈ umbraSlice[k | C, x] ↔
      ∃ a : k, 1 ≤ a ∧ ∃ c ∈ C, y = (1 - a) • x + a • c := by
  simp [umbraSlice, eq_comm]

/-- Text 3.8.1: the umbra of subsets `C` and `S` of a `k`-module is the intersection over
`x ∈ S` of the affine-image slices `{(1 - λ) • x + λ • c | λ ≥ 1, c ∈ C}`. -/
def umbra (C S : Set E) : Set E :=
  ⋂ x : S, umbraSlice[k | C, x]

scoped[Rockafellar] notation:max "umbra[" k " | " C ", " S "]" => umbra k C S

/-- Intrinsic owner-level membership: `y ∈ umbra C S` iff `y` lies in every fixed-`x` slice
indexed by the subtype `x : S`. -/
@[simp] theorem mem_umbra_iff (C S : Set E) (y : E) :
    y ∈ umbra[k | C, S] ↔ ∀ x : S, y ∈ umbraSlice[k | C, x] := by
  simp [umbra]

/-- Source-facing bridge: `y ∈ umbra C S` iff for every ambient `x ∈ S`,
`y ∈ umbraSlice C x`. -/
theorem mem_umbra_iff_forall_mem (C S : Set E) (y : E) :
    y ∈ umbra[k | C, S] ↔ ∀ x ∈ S, y ∈ umbraSlice[k | C, x] := by
  constructor
  · intro hy x hx
    exact (mem_umbra_iff (k := k) (C := C) (S := S) (y := y)).1 hy ⟨x, hx⟩
  · intro hy
    exact (mem_umbra_iff (k := k) (C := C) (S := S) (y := y)).2 fun x ↦ hy x x.2

/-- Intrinsic owner-level affine witness bridge: `y ∈ umbra C S` iff for each subtype-indexed
`x : S` there exist `λ ≥ 1` and `c ∈ C` with `y = (1 - λ) • x + λ • c`. -/
-- Proof sketch: first use the owner-level bridge `mem_umbra_iff`, then unpack
-- each slice membership via `mem_umbraSlice_iff`.
@[simp] theorem mem_umbra_iff_forall_exists_affine (C S : Set E) (y : E) :
    y ∈ umbra[k | C, S] ↔
      ∀ x : S, ∃ a : k, 1 ≤ a ∧ ∃ c ∈ C, y = (1 - a) • x + a • c := by
  simp [mem_umbra_iff, mem_umbraSlice_iff]

/-- Source-facing affine witness bridge: `y ∈ umbra C S` iff for every ambient `x ∈ S` there
exist `λ ≥ 1` and `c ∈ C` with `y = (1 - λ) • x + λ • c`. -/
theorem mem_umbra_iff_forall_exists_affine_mem (C S : Set E) (y : E) :
    y ∈ umbra[k | C, S] ↔
      ∀ x ∈ S, ∃ a : k, 1 ≤ a ∧ ∃ c ∈ C, y = (1 - a) • x + a • c := by
  constructor
  · intro hy x hx
    exact (mem_umbra_iff_forall_exists_affine (k := k) (C := C) (S := S) (y := y)).1 hy ⟨x, hx⟩
  · intro hy
    exact (mem_umbra_iff_forall_exists_affine (k := k) (C := C) (S := S) (y := y)).2
      (fun x ↦ hy x x.2)

end Core

section Bridge

open scoped Rockafellar

variable [Zero k] [One k] [Sub k] [Preorder k] [ZeroLEOneClass k] [Add E] [SMul k E]

/-- Owner-level bridge: `umbraSlice C x` is the affine-head image of the clipped homogenization
set `K[k | C] ∩ Prod.fst ⁻¹' Set.Ici (1 : k)`. This bridge lives at the primitive data layer of
`umbraSlice`/`homogenizationSet` and is independent of convexity assumptions. -/
theorem umbraSlice_eq_homogenization_head_image (C : Set E) (x : E) :
    umbraSlice[k | C, x] =
      (fun p : k × E ↦ (1 - p.1) • x + p.2) ''
        ((K[k | C] : Set (k × E)) ∩ (Prod.fst : k × E → k) ⁻¹' Set.Ici (1 : k)) := by
  ext y
  constructor
  · intro hy
    rcases (mem_umbraSlice_iff k C x y).1 hy with ⟨a, ha, c, hc, rfl⟩
    refine ⟨(a, a • c), ?_, rfl⟩
    refine ⟨?_, ha⟩
    refine (mem_homogenizationSet_iff k C (a, a • c)).2 ?_
    refine ⟨le_trans zero_le_one ha, ?_⟩
    exact Set.mem_smul_set.mpr ⟨c, hc, rfl⟩
  · rintro ⟨⟨a, y'⟩, hy', rfl⟩
    rcases hy' with ⟨hyK, ha⟩
    have ha' : 1 ≤ a := by simpa using ha
    rcases (mem_homogenizationSet_iff k C (a, y')).1 hyK with ⟨-, hyC⟩
    rcases Set.mem_smul_set.mp hyC with ⟨c, hc, hyc⟩
    exact (mem_umbraSlice_iff k C x _).2
      ⟨a, ha', c, hc, by simp [hyc]⟩

end Bridge

section Convexity

open LinearMap
open scoped Rockafellar

variable [Field k] [PartialOrder k] [IsOrderedRing k] [PosMulReflectLT k]
  [AddCommMonoid E] [Module k E]

/-- If `C` is convex, then every fixed-`x` slice used in the umbra construction is convex. -/
theorem Convex.umbraSlice {C : Set E} (hC : Convex k C) (x : E) :
    Convex k (umbraSlice[k | C, x]) := by
  have hhalf : Convex k ((Prod.fst : k × E → k) ⁻¹' Set.Ici (1 : k)) := by
    simpa using convex_halfSpace_ge (fst k k E).isLinear (1 : k)
  have hhead :
      Convex k ((K[k | C] : Set (k × E)) ∩ (Prod.fst : k × E → k) ⁻¹' Set.Ici (1 : k)) :=
    (hC.homogenizationSet).inter hhalf
  rw [umbraSlice_eq_homogenization_head_image k C x]
  intro y hy z hz t s ht hs hts
  rcases hy with ⟨p, hp, rfl⟩
  rcases hz with ⟨q, hq, rfl⟩
  refine ⟨t • p + s • q, hhead hp hq ht hs hts, ?_⟩
  rcases p with ⟨a, u⟩
  rcases q with ⟨b, v⟩
  symm
  change
    t • ((1 - a) • x + u) + s • ((1 - b) • x + v) =
      (1 - (t * a + s * b)) • x + (t • u + s • v)
  calc
    t • ((1 - a) • x + u) + s • ((1 - b) • x + v)
        = (t * (1 - a) + s * (1 - b)) • x + (t • u + s • v) := by
            simp [smul_add, add_smul, smul_smul, add_assoc, add_left_comm, add_comm]
    _ = (1 - (t * a + s * b)) • x + (t • u + s • v) := by
          have hcoeff : t * (1 - a) + s * (1 - b) = 1 - (t * a + s * b) := by
            calc
              t * (1 - a) + s * (1 - b) = (t + s) - (t * a + s * b) := by ring
              _ = 1 - (t * a + s * b) := by simp [hts]
          rw [hcoeff]

end Convexity

end

/-! ### Text_3_8_2 (from Chap01) -/
section

variable (k : Type*)
variable {E : Type*}

/- 
Source/core/bridge triage:
- `source-facing`: Text 3.8.2 introduces the penumbra of two subsets `C` and `S` by an explicit
  union-of-slices formula built from the affine images of `C` seen from points `x ∈ S`.
- `core/canonical`: the owner abstraction is `Set E`; the primitive fixed-`x` affine-image owner
  from the adjacent item is `umbraSlice`, and `penumbra k C S` is encoded intrinsically as the
  subtype-indexed union `⋃ x : S, ...`.
- `bridge/view`: `mem_penumbra_iff_exists_subtype` is the intrinsic subtype-indexed membership
  view, while `mem_penumbra_iff` is the source-facing ambient bridge with binders
  `∃ x ∈ S, ...`;
  and
  `mem_penumbra_iff_exists_affine` is the explicit affine witness bridge
  “there exist `x ∈ S`, `λ ≥ 1`, and `c ∈ C` with
  `y = (1 - λ) • x + λ • c`”. Their binder shapes follow the chapter membership API style used
  for `mem_umbraSlice_iff` and `mem_inverseAddition_iff`.
- Primitive data vs derived API: the fixed-`x` affine-image slice and the resulting penumbra are
  concrete subsets determined by `C`, `x`, and `S`; the source-side assumption that `C` and `S`
  are disjoint is extrinsic to these formulas, so it is not built into the definition.
- Domain-style sampling: this item aligns with the preceding source-facing set definition
  `umbra k`, its shared slice owner `umbraSlice k`, the chapter's other `⋃`-based set formulas
  such as `inverseAddition`, and the canonical set API `Set.image` and indexed-union membership
  rules.
  The stronger affine-owner API `AffineMap.lineMap` was checked as the upstream candidate for the
  displayed affine maps, but it would force stronger structure than this source-facing item needs.
- Layer target: `source-facing`; no earlier chapter/project owner duplicates this set-valued
  construction, so this file remains the owner; its public definition presents the source formula
  directly at the fixed-`x` slice owner layer.
-/

section Core

open scoped Rockafellar

variable [One k] [Sub k] [LE k] [Add E] [SMul k E]

/-- Text 3.8.2: the penumbra of subsets `C` and `S` is the union over
`x ∈ S` of the unions of the affine images `{(1 - λ) • x + λ • c | c ∈ C}` for scalars
`λ ≥ 1`. -/
def penumbra (C S : Set E) : Set E :=
  ⋃ x : S, umbraSlice[k | C, x]

scoped[Rockafellar] notation:max "penumbra[" k " | " C ", " S "]" => penumbra k C S

/-- Intrinsic bridge: subtype-indexed view of `penumbra C S` membership. -/
@[simp] theorem mem_penumbra_iff_exists_subtype (C S : Set E) (y : E) :
    y ∈ penumbra[k | C, S] ↔ ∃ x : S, y ∈ umbraSlice[k | C, x] := by
  simp [penumbra]

/-- Source-facing membership view: `y ∈ penumbra C S` iff there exists `x ∈ S` with
`y ∈ umbraSlice C x`. -/
theorem mem_penumbra_iff (C S : Set E) (y : E) :
    y ∈ penumbra[k | C, S] ↔ ∃ x ∈ S, y ∈ umbraSlice[k | C, x] := by
  constructor
  · intro hy
    rcases (mem_penumbra_iff_exists_subtype (k := k) C S y).1 hy with ⟨x, hyx⟩
    exact ⟨x, x.2, hyx⟩
  · rintro ⟨x, hx, hyx⟩
    exact (mem_penumbra_iff_exists_subtype (k := k) C S y).2 ⟨⟨x, hx⟩, hyx⟩

/- A bridge from owner-level membership to the explicit affine witness form from Text 3.8.2. -/
-- Proof sketch: first use the owner-level bridge `mem_penumbra_iff`, then unpack
-- slice membership via `mem_umbraSlice_iff`.
@[simp] theorem mem_penumbra_iff_exists_affine (C S : Set E) (y : E) :
    y ∈ penumbra[k | C, S] ↔
      ∃ x ∈ S, ∃ a : k, 1 ≤ a ∧ ∃ c ∈ C, y = (1 - a) • x + a • c := by
  simp [mem_umbraSlice_iff]

end Core

end

/-! ### Text_3_8_3 (from Chap01) -/
open scoped Rockafellar

section

variable {E k : Type*}
variable [Semiring k] [Sub k] [PartialOrder k] [AddCommMonoid E] [SMul k E]

/-- Source-facing bridge: if every ambient fixed-`x` umbra slice over `S` is convex, then the
corresponding umbra is convex. -/
theorem convex_umbra_of_convex_slices_mem {C S : Set E}
    (hSlice : ∀ x ∈ S, Convex k (umbraSlice[k | C, x])) :
    Convex k (umbra[k | C, S]) := by
  simpa [umbra] using convex_iInter (fun x : S ↦ hSlice x x.2)

end

section

variable {E k : Type*}
variable [Field k] [PartialOrder k] [IsOrderedRing k] [PosMulReflectLT k]
  [AddCommMonoid E] [Module k E]

/-
Source/core/bridge triage:
- `source-facing`: Text 3.8.3 states that the umbra of a convex set `C` is convex.
- `core/canonical`: the owner abstraction is the standard convexity predicate `Convex k` on
  subsets of a `k`-module.
- `bridge/view`: the set under discussion is the source-facing set `umbra C S`, so the theorem
  should be stated directly for that canonical source-facing set.
- Primitive data vs derived API: the sets `C` and `S` and the convexity of `C` are primitive; the
  convexity of `umbra C S` is the sole derived conclusion.
- Domain-style sampling: this item aligns with the chapter's closure results for convexity under
  arbitrary intersections. Concretely, the relevant owner-level API is the predicate `Convex k`,
  together with mathlib's subtype-indexed `convex_iInter` and the owner-side derived theorem
  `Convex.umbraSlice` for the fixed-`x` slices from `Text_3_8_1`. The more special theorem
  `Convex.affinity` was also checked during sampling as the canonical affine-image owner for each
  individual slice parameter, but the reusable owner theorem is already packaged at the chapter
  level as `Convex.umbraSlice`.
- Layer target: `bridge/view`; the source-facing theorem about `umbra` is preserved, with the
  outer convexity step delegated to subtype-indexed `convex_iInter` and the inner slice convexity
  delegated to
  the owner theorem `Convex.umbraSlice`.
-/

/-- If `C` is convex, then its umbra with respect to any subset `S` is convex. -/
theorem Convex.umbra {C S : Set E} (hC : Convex k C) :
    Convex k (umbra[k | C, S]) := by
  exact convex_umbra_of_convex_slices_mem (S := S) fun x _hx ↦ hC.umbraSlice (x := x)

/-- Text 3.8.3: if `C` is convex, then its umbra with respect to any subset `S` is convex. -/
theorem convex_umbra {C S : Set E} (hC : Convex k C) :
    Convex k (umbra[k | C, S]) :=
  hC.umbra

end

/-! ### Text_3_8_4 (from Chap01) -/
section

open LinearMap
open scoped Pointwise Rockafellar

variable {E k : Type*}
variable [Field k] [PartialOrder k] [IsOrderedRing k] [PosMulReflectLT k]
  [AddCommMonoid E] [Module k E]

private def penumbraHead (C : Set E) : Set (k × E) :=
  (K[k | C] : Set (k × E)) ∩ {p : k × E | 1 ≤ p.1}

private def penumbraTail (S : Set E) : Set (k × E) :=
  {p | 1 ≤ p.1 ∧ p.2 ∈ (1 - p.1) • S}

private def penumbraLift (C S : Set E) : Set (k × E) :=
  penumbraHead C +ᶠ penumbraTail S

private theorem convex_penumbraHead {C : Set E} (hC : Convex k C) :
    Convex k (penumbraHead C : Set (k × E)) := by
  have hhalf : Convex k {p : k × E | 1 ≤ p.1} := by
    simpa using convex_halfSpace_ge (fst k k E).isLinear (1 : k)
  exact hC.homogenizationSet.inter hhalf

private def penumbraTailMap : (k × E) →ₗ[k] k × E :=
  { toFun := fun p ↦ (p.1, (-1 : k) • p.2)
    map_add' := by
      intro x y
      ext <;> simp [smul_add]
    map_smul' := by
      intro a x
      ext <;> simp [smul_smul, mul_comm] }

omit [PosMulReflectLT k] in
private theorem penumbraTail_eq (S : Set E) :
    penumbraTail S =
      ((fun p : k × E ↦ (1, (0 : E)) + p) '' (penumbraTailMap '' (K[k | S] : Set (k × E)))) := by
  ext p
  rcases p with ⟨a, y⟩
  constructor
  · rintro ⟨ha, hy⟩
    change 1 ≤ a at ha
    change y ∈ (1 - a) • S at hy
    rcases Set.mem_smul_set.mp hy with ⟨x, hx, rfl⟩
    refine ⟨(a - 1, (1 - a) • x), ?_, ?_⟩
    · refine ⟨(a - 1, (a - 1) • x), ?_, ?_⟩
      · exact ⟨sub_nonneg.mpr ha, Set.mem_smul_set.mpr ⟨x, hx, rfl⟩⟩
      · ext
        · simp [penumbraTailMap]
        · change (-1 : k) • ((a - 1) • x) = (1 - a) • x
          rw [smul_smul]
          congr 1
          ring
    · ext <;> simp
  · rintro ⟨q, hq, hp⟩
    rcases hq with ⟨⟨r, z⟩, hzK, rfl⟩
    rcases hzK with ⟨hr, hz⟩
    rcases Set.mem_smul_set.mp hz with ⟨x, hx, hzx⟩
    have ha : a = 1 + r := by
      simpa [penumbraTailMap] using (congrArg Prod.fst hp).symm
    have hy : y = (-1 : k) • z := by
      simpa [penumbraTailMap] using (congrArg Prod.snd hp).symm
    constructor
    · rw [ha]
      simpa using add_le_add_left hr (1 : k)
    · rw [ha, show 1 - (1 + r) = -r by ring]
      refine Set.mem_smul_set.mpr ⟨x, hx, ?_⟩
      calc
        (-r) • x = (-1 : k) • (r • x) := by simp [smul_smul]
        _ = (-1 : k) • z := by rw [hzx]
        _ = y := hy.symm

private theorem convex_penumbraTail {S : Set E} (hS : Convex k S) :
    Convex k (penumbraTail S : Set (k × E)) := by
  rw [penumbraTail_eq]
  exact (hS.homogenizationSet.linear_image penumbraTailMap).translate (1, (0 : E))

private theorem convex_penumbraLift {C S : Set E} (hC : Convex k C) (hS : Convex k S) :
    Convex k (penumbraLift C S : Set (k × E)) := by
  simpa [penumbraLift] using
    (convex_penumbraHead hC).fiberwiseSum (convex_penumbraTail hS)

omit [PosMulReflectLT k] in
private theorem mem_penumbraLift_iff (C S : Set E) (p : k × E) :
    p ∈ (penumbraLift C S : Set (k × E)) ↔
      1 ≤ p.1 ∧ ∃ x ∈ S, ∃ c ∈ C, p.2 = (1 - p.1) • x + p.1 • c := by
  rw [penumbraLift, Set.mem_fiberwiseSum]
  constructor
  · rintro ⟨z₁, z₂, hz₁, hz₂, hsum⟩
    rcases hz₁ with ⟨hz₁, ha⟩
    rcases hz₂ with ⟨-, hz₂⟩
    rcases hz₁ with ⟨-, hz₁⟩
    rcases Set.mem_smul_set.mp hz₁ with ⟨c, hc, hz₁⟩
    rcases Set.mem_smul_set.mp hz₂ with ⟨x, hx, hz₂⟩
    refine ⟨ha, x, hx, c, hc, ?_⟩
    calc
      p.2 = z₁ + z₂ := by simpa using hsum.symm
      _ = p.1 • c + (1 - p.1) • x := by rw [hz₁, hz₂]
      _ = (1 - p.1) • x + p.1 • c := by rw [add_comm]
  · rintro ⟨ha, x, hx, c, hc, hp⟩
    refine ⟨p.1 • c, (1 - p.1) • x, ?_, ?_, ?_⟩
    · exact ⟨⟨le_trans zero_lt_one.le ha, Set.mem_smul_set.mpr ⟨c, hc, rfl⟩⟩, ha⟩
    · exact ⟨ha, Set.mem_smul_set.mpr ⟨x, hx, rfl⟩⟩
    · simpa [add_comm] using hp.symm

omit [PosMulReflectLT k] in
private theorem penumbra_eq_snd_image_penumbraLift (C S : Set E) :
    penumbra[k | C, S] = (snd k k E) '' (penumbraLift C S : Set (k × E)) := by
  ext y
  constructor
  · intro hy
    rcases (mem_penumbra_iff_exists_affine k C S y).1 hy with ⟨x, hx, a, ha, c, hc, hy⟩
    refine ⟨(a, y), ?_, by simp⟩
    exact (mem_penumbraLift_iff C S (a, y)).2 ⟨ha, x, hx, c, hc, hy⟩
  · rintro ⟨⟨a, y'⟩, hy', rfl⟩
    rcases (mem_penumbraLift_iff C S (a, y')).1 hy' with ⟨ha, x, hx, c, hc, hy⟩
    exact (mem_penumbra_iff_exists_affine k C S y').2 ⟨x, hx, a, ha, c, hc, hy⟩

/-
Source/core/bridge triage:
- `source-facing`: Text 3.8.4 states that the source-defined set `penumbra C S` is convex when
  both `C` and `S` are convex.
- `core/canonical`: the owner abstraction is mathlib's predicate `Convex k` on subsets of a
  `k`-module, together with the chapter owners `homogenizationSet`, `+ᶠ`, and
  `Convex.linear_image` on product spaces.
- `bridge/view`: the imported source-facing definition `penumbra`, together with the owner-level
  bridge `mem_penumbra_iff` and the explicit witness bridge
  `mem_penumbra_iff_exists_affine`, provides the source-side membership views used by the private
  lift argument. The private lift `penumbraLift` is the
  fiberwise sum, over the common parameter `a`, of the clipped homogenization-set view
  `penumbraHead C` and the translated neg-second-coordinate image `penumbraTail S` of
  `homogenizationSet S`. The source-facing set is then the second projection of that convex lift.
- Primitive data vs derived API: the sets `C` and `S` together with the canonical pointwise
  scaled-set owners `p.1 • C` and `(1 - p.1) • S` are primitive; convexity of `penumbraHead C`,
  `penumbraTail S`, the lifted fiberwise sum, and finally `penumbra C S` are derived API.
- Domain-style sampling: the relevant owner-level declarations checked here are `Convex k`,
  `mem_penumbra_iff`, `mem_penumbra_iff_exists_affine`, `Convex.homogenizationSet`,
  `convex_halfSpace_ge`, `(+ᶠ)`,
  `Convex.fiberwiseSum`, `Convex.translate`, and `Convex.linear_image`. They show that
  the private lift should reuse the chapter's homogenization-set and fiberwise-sum owners rather
  than carrying parallel coordinate-level convexity proofs.
- Layer target: `source-facing`; the theorem keeps `penumbra C S` as the public object and uses
  the lifted product-space fiberwise-sum set only as a private bridge/view.
- Abstraction check (canonicalize pass):
  - Codomain/ambient over-concrete? `No`: the theorem is set-level convexity on arbitrary
    `k`-modules, not on coordinates or a concrete Euclidean model.
  - Scalar structure over-concrete? `No`: the scalar layer remains `Field k` with order axioms
    because this item reuses the upstream homogenization convexity bridge and also uses algebraic
    identities with subtraction/negation (`1 - a`, `-1`, `a - 1`) in the penumbra-tail bridge.
  - Concrete-model owner instead of intrinsic owner? `No`: the public owner is the source-facing
    `penumbra[k | C, S]` with the canonical convex predicate `Convex k`.
  - Ambient-vs-intrinsic topology mismatch? `Not applicable`: this item is not topology-facing.
  - Owner naming / notation mismatch? `No`: this file uses the short source notation
    `penumbra[k | C, S]` on theorem surfaces.
-/

/-- Text 3.8.4: if both `S` and `C` are convex, then the penumbra of `C` with respect to `S` is
convex. -/
-- Proof sketch: `penumbraHead C` is the height-`≥ 1` cut of the canonical homogenization-set
-- owner `K[k | C]`, and `penumbraTail S` is the translate by `(1, 0)` of the neg-second-coordinate
-- linear image of `K[k | S]`. Hence both lifted factors are convex by owner-level reuse of
-- `Convex.homogenizationSet`, `convex_halfSpace_ge`, `Convex.translate`, and `Convex.linear_image`.
-- The chapter owner theorem `Convex.fiberwiseSum` then gives convexity of
-- `penumbraLift C S ⊆ k × E`, and the source-facing set `penumbra C S` is its second projection.
theorem Convex.penumbra {C S : Set E} (hC : Convex k C) (hS : Convex k S) :
    Convex k (penumbra[k | C, S]) := by
  rw [penumbra_eq_snd_image_penumbraLift C S]
  simpa using (convex_penumbraLift hC hS).linear_image (snd k k E)

/-- Text 3.8.4: if both `S` and `C` are convex, then the penumbra of `C` with respect to `S` is
convex. -/
theorem convex_penumbra {C S : Set E} (hC : Convex k C) (hS : Convex k S) :
    Convex k (penumbra[k | C, S]) :=
  hC.penumbra hS

end

/-! ### Theorem_3_8 (from Chap01) -/
universe u v

open scoped Pointwise
open scoped Rockafellar

/-
Source/core/bridge triage:
- `source-facing`: Theorem 3.8 states two set identities for convex cones containing the origin:
  the Minkowski sum equals the convex hull of the union, and the chapter's source-facing inverse
  addition notation `#[R]` equals the intersection.
- `core/canonical`: the owner layer is `PointedCone R E` over an ordered semiring layer;
  the canonical ambient operations are the lattice supremum/infimum on pointed cones and the
  generated-cone owner `PointedCone.hull R`.
- `bridge/view`: the theorem remains source-facing as a pair of set identities on the underlying
  sets of pointed cones; the first keeps the textbook Minkowski sum `((K₁ : Set E) + (K₂ : Set E))`
  explicit while routing it through the canonical supremum `K₁ ⊔ K₂`, the owner equality
  `Submodule.span_union`, and the earlier chapter theorem
  `PointedCone.hull_eq_convexHull_nonnegativeRay`; the second keeps the source notation
  `#[R]` on set carriers and internally identifies the right-hand side with the pointed-cone
  infimum.
- Primitive data vs derived API: the pointed cones are primitive; the two equalities are direct
  set-theoretic conclusions and should remain explicit set identities rather than a packaged
  wrapper.
- Domain-style sampling: the owner abstractions are `PointedCone R E` together with the
  supporting API `Submodule.coe_sup`, `Submodule.coe_inf`, `Submodule.span_union`,
  `PointedCone.hull_eq_convexHull_nonnegativeRay`, and `Set.mem_inverseAddition_primitive_iff`.
-/

namespace PointedCone

section OrderedSemiringHull

variable {R : Type v} [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable {E : Type u} [AddCommMonoid E] [Module R E]

/-- Primitive owner form for Theorem 3.8 (1): the supremum of two pointed cones is the generated
cone of the union of their carriers. -/
theorem sup_eq_hull_union (K₁ K₂ : PointedCone R E) :
    (K₁ ⊔ K₂ : PointedCone R E) = cone[R] ((K₁ : Set E) ∪ K₂) := by
  ext x
  rw [hull, Submodule.span_union]
  simp

end OrderedSemiringHull

section OrderedSemifieldHull

variable {R : Type v} [Semifield R] [PartialOrder R] [IsOrderedRing R] [PosMulReflectLT R]
variable {E : Type u} [AddCommMonoid E] [Module R E]

/-- Source-facing form of Theorem 3.8 (1): the carrier of the supremum of two pointed cones is
the convex hull of the union of their carriers. -/
-- Proof sketch: first use the primitive owner identity `sup_eq_hull_union`, then apply
-- `hull_eq_convexHull_nonnegativeRay` and simplify because the union of pointed cones is already
-- closed under nonnegative scaling.
theorem sup_eq_convexHull_union (K₁ K₂ : PointedCone R E) :
    ((K₁ ⊔ K₂ : PointedCone R E) : Set E) = conv[R] ((K₁ : Set E) ∪ K₂) := by
  let U : Set E := (K₁ : Set E) ∪ K₂
  have hU :
      (Set.Ici (0 : R)) • U = U := by
    ext x
    constructor
    · rintro ⟨r, hr, y, hy, rfl⟩
      rcases hy with hy | hy
      · exact Or.inl <| K₁.smul_mem hr hy
      · exact Or.inr <| K₂.smul_mem hr hy
    · intro hx
      simpa using Set.smul_mem_smul (show (1 : R) ∈ Set.Ici (0 : R) by simp) hx
  calc
    ((K₁ ⊔ K₂ : PointedCone R E) : Set E) =
        (cone[R] ((K₁ : Set E) ∪ K₂) : Set E) := by
      exact congrArg (fun K : PointedCone R E => (K : Set E))
        (sup_eq_hull_union (K₁ := K₁) (K₂ := K₂))
    _ = (cone[R] U : Set E) := by
      rfl
    _ = convexHull R ((Set.Ici (0 : R)) • U) := by
      simpa [U] using hull_eq_convexHull_nonnegativeRay (R := R) (S := U) ⟨0, Or.inl K₁.zero_mem⟩
    _ = conv[R] U := by
      simp [hU]

/-- Theorem 3.8 (1): for pointed convex cones in a module over an ordered semifield, the
Minkowski sum is the convex hull of the union. -/
theorem add_eq_convexHull_union (K₁ K₂ : PointedCone R E) :
    ((K₁ : Set E) + (K₂ : Set E)) = conv[R] ((K₁ : Set E) ∪ K₂) := by
  calc
    ((K₁ : Set E) + (K₂ : Set E)) = ((K₁ ⊔ K₂ : PointedCone R E) : Set E) := by
      simpa using (Submodule.coe_sup K₁ K₂).symm
    _ = conv[R] ((K₁ : Set E) ∪ K₂) := sup_eq_convexHull_union K₁ K₂

end OrderedSemifieldHull

section OrderedDivisionSemiringInverseAddition

variable {R : Type v} [DivisionSemiring R] [PartialOrder R] [IsOrderedRing R] [PosMulReflectLT R]
variable {E : Type u} [AddCommMonoid E] [Module R E]

/-- Owner form of Theorem 3.8 (2): inverse addition of two pointed-cone carriers equals the
carrier of their infimum. -/
-- Proof sketch: unfold membership in inverse addition using the primitive two-coefficient owner
-- theorem `Set.mem_inverseAddition_primitive_iff`; one direction uses cone closure
-- under nonnegative
-- scaling, and the other uses the canonical symmetric witness `((2 : R)⁻¹, (2 : R)⁻¹)`.
theorem inverseAddition_eq_coe_inf (K₁ K₂ : PointedCone R E) :
    (K₁ #[R] K₂ : Set E) = ((K₁ ⊓ K₂ : PointedCone R E) : Set E) := by
  ext x
  rw [Set.mem_inverseAddition_primitive_iff]
  constructor
  · rintro ⟨t₁, t₂, ht₁, ht₂, -, hx⟩
    rcases hx with ⟨hx₁, hx₂⟩
    refine ⟨?_, ?_⟩
    · rcases Set.mem_smul_set.mp hx₁ with ⟨y, hy, rfl⟩
      exact K₁.smul_mem ht₁.le hy
    · rcases Set.mem_smul_set.mp hx₂ with ⟨y, hy, rfl⟩
      exact K₂.smul_mem ht₂.le hy
  · rintro ⟨hx₁, hx₂⟩
    have htwo_pos : (0 : R) < 2 := zero_lt_two
    have htwo_ne : (2 : R) ≠ 0 := ne_of_gt htwo_pos
    have hhalf_pos : (0 : R) < (2 : R)⁻¹ := inv_pos.mpr htwo_pos
    refine ⟨(2 : R)⁻¹, (2 : R)⁻¹, hhalf_pos, hhalf_pos, ?_, ?_⟩
    · calc
        ((2 : R)⁻¹ + (2 : R)⁻¹ : R) = (2 : R) * (2 : R)⁻¹ := by
          simp [two_mul]
        _ = 1 := by simp [htwo_ne]
    · constructor
      · refine Set.mem_smul_set.mpr ⟨(2 : R) • x, K₁.smul_mem (le_of_lt htwo_pos) hx₁, ?_⟩
        calc
          ((2 : R)⁻¹ : R) • ((2 : R) • x) = (((2 : R)⁻¹ * 2) : R) • x := by
            rw [smul_smul]
          _ = x := by simp [htwo_ne]
      · refine Set.mem_smul_set.mpr ⟨(2 : R) • x, K₂.smul_mem (le_of_lt htwo_pos) hx₂, ?_⟩
        calc
          ((2 : R)⁻¹ : R) • ((2 : R) • x) = (((2 : R)⁻¹ * 2) : R) • x := by
            rw [smul_smul]
          _ = x := by simp [htwo_ne]

/-- Theorem 3.8 (2): for pointed convex cones in a module over an ordered division semiring,
`K₁ #[R] K₂ = (K₁ : Set E) ∩ (K₂ : Set E)`. -/
-- Proof sketch: combine the owner-level identity `inverseAddition_eq_coe_inf` with the standard
-- carrier description of infimum as set intersection.
theorem inverseAddition_eq_inter (K₁ K₂ : PointedCone R E) :
    (K₁ #[R] K₂ : Set E) = (K₁ ∩ K₂ : Set E) := by
  calc
    (K₁ #[R] K₂ : Set E) = ((K₁ ⊓ K₂ : PointedCone R E) : Set E) := by
      exact inverseAddition_eq_coe_inf K₁ K₂
    _ = (K₁ ∩ K₂ : Set E) := by
      exact (Submodule.coe_inf :
        ((K₁ ⊓ K₂ : PointedCone R E) : Set E) = (K₁ : Set E) ∩ (K₂ : Set E))

end OrderedDivisionSemiringInverseAddition

end PointedCone
