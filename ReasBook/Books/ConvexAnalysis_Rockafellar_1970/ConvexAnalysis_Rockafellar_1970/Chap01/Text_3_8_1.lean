import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Proposition_2_6_12

-- Declarations for this item will be appended below by the statement pipeline.

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
