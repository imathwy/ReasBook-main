import ConvexAnalysis_Rockafellar_1970.Chap01.Text_3_8_1

-- Declarations for this item will be appended below by the statement pipeline.

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
