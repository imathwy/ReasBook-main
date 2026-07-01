import ConvexAnalysis_Rockafellar_1970.Chap01.Text_1_13

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Affine

namespace AffineSubspace

/-
Source/core/bridge triage:
- `source-facing`: Text 1.13.1 records three standard presentations of a nontrivial affine
  subspace: as a translate of its direction, as the range of that translated inclusion, and after
  splitting off a complementary subspace, as the graph of an affine map.
- `core/canonical`: the owner abstractions are `AffineSubspace.mk'_eq`,
  `Submodule.subtype`, its derived affine bridge `LinearMap.toAffineMap`, `AffineSubspace.map`,
  `Submodule.prodEquivOfIsCompl`, `AffineSubspace.IsTuckerRepresentable`,
  `Submodule.exists_eq_graph`, `LinearEquiv.toAffineEquiv`, and the chapter declaration
  `AffineMap.graph`.
- `bridge/view`: explicit graph-witness existentials are retained only as bridge views of owner
  theorems stated using `AffineSubspace.IsTuckerRepresentable`.
- Domain-style sampling used here: `AffineSubspace.mk'_eq`, `Submodule.subtype`,
  `LinearMap.toAffineMap`,
  `AffineSubspace.map`, `Submodule.prodEquivOfIsCompl`, `Submodule.exists_eq_graph`, and the
  chapter owner `AffineMap.graph`.
- Layer target: owner-first (`AffineSubspace.IsTuckerRepresentable`) with explicit graph
  existentials as bridge views.
- Primitive data vs derived API: once a complementary subspace `Z` with `IsCompl C.direction Z`
  is fixed, the ambient identification is the intrinsic affine-space split obtained by composing a
  basepoint translation inverse `(AffineEquiv.vaddConst k x₀).symm` with
  `(C.direction.prodEquivOfIsCompl Z hcompl).symm.toAffineEquiv`; continuity is secondary derived
  structure, not primitive public data for this item.
- Canonicalization decision record (this pass):
  - Codomain/ambient check: no ordered-extended codomain or topology owner is primary here; the
    canonical ambient owner remains `AffineSubspace k _`.
  - Scalar check: the reused affine-subspace owners are at `[Ring k]`; complement existence for the
    downstream bridge still needs `[DivisionRing k]`.
  - Owner check: promote the two recurrent composites to short canonical owners
    `AffineSubspace.subtypeTranslate` and `AffineSubspace.splitAffineEquiv`, while keeping constant
    graph witnesses on the canonical owner `AffineMap.const`; also expose object-prefix Tucker
    bridge eliminator/introduction forms to avoid repeated explicit `(M := ...)` forcing.
-/

section Translate

variable {k : Type u} {V : Type u} {P : Type u}
  [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P]

/- Text 1.13.1 (1): once a base point `x₀ ∈ C` is chosen, the affine set is exactly the owner
construction `mk' x₀ C.direction`, so the textbook translation statement is controlled directly by
`AffineSubspace.mk'_eq`. -/
recall AffineSubspace.mk'_eq

end Translate

section Range

variable {k : Type u} {V : Type u} {P : Type u}
  [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P]

/-- Canonical translated subtype owner used in Text 1.13.1 (2). -/
abbrev subtypeTranslate (C : AffineSubspace k P) (x₀ : C) : C.direction →ᵃ[k] P :=
  (Submodule.subtype C.direction).toAffineMap +ᵥ
    AffineMap.const k C.direction (x₀ : P)

/-- Canonical owner form of Text 1.13.1 (2): once a base point is explicit, the affine subspace is
the image of `⊤` under `C.subtypeTranslate x₀`. -/
theorem eq_map_top_subtypeTranslate
    (C : AffineSubspace k P) (x₀ : C) :
    C = (⊤ : AffineSubspace k C.direction).map (C.subtypeTranslate x₀) := by
  ext x
  constructor
  · intro hx
    refine ⟨⟨x -ᵥ (x₀ : P), ?_⟩, by simp, ?_⟩
    · exact (C.vsub_right_mem_direction_iff_mem x₀.property x).2 hx
    · simp [subtypeTranslate]
  · rintro ⟨v, -, rfl⟩
    simpa [subtypeTranslate] using C.vadd_mem_of_mem_direction v.property x₀.property

/-- Text 1.13.1 (2): a nonempty affine set is the image of the ambient owner `⊤` under a translate
of the canonical subtype map of its direction. The finite-dimensional hypothesis from the
surrounding source discussion is redundant once the canonical parameter space is `C.direction`. -/
-- Proof sketch: choose `x₀ : C` from `hC`, rewrite `C` as `AffineSubspace.mk' (x₀ : P)
-- C.direction`, and identify that affine subspace with the image of `⊤` under the translated owner
-- map `C.subtypeTranslate x₀`.
theorem exists_eq_map_top_subtypeTranslate_of_nonempty
    (C : AffineSubspace k P) (hC : Nonempty C) :
    ∃ x₀ : C,
      C = (⊤ : AffineSubspace k C.direction).map (C.subtypeTranslate x₀) := by
  rcases hC with ⟨x₀⟩
  refine ⟨x₀, ?_⟩
  simpa using eq_map_top_subtypeTranslate C x₀

/-- Set-range bridge view of `eq_map_top_subtypeTranslate`. -/
theorem eq_range_subtypeTranslate
    (C : AffineSubspace k P) (x₀ : C) :
    (C : Set P) = Set.range (C.subtypeTranslate x₀) := by
  simpa [AffineSubspace.coe_map] using
    congrArg (fun s : AffineSubspace k P ↦ (s : Set P))
      (eq_map_top_subtypeTranslate C x₀)

/-- Set-range view of `exists_eq_map_top_subtypeTranslate_of_nonempty`. -/
theorem exists_eq_range_subtypeTranslate_of_nonempty
    (C : AffineSubspace k P) (hC : Nonempty C) :
    ∃ x₀ : C,
      (C : Set P) = Set.range (C.subtypeTranslate x₀) := by
  rcases exists_eq_map_top_subtypeTranslate_of_nonempty C hC with ⟨x₀, hx₀⟩
  refine ⟨x₀, ?_⟩
  simpa using eq_range_subtypeTranslate C x₀

end Range

section Graph

section Primitive

variable {k : Type u} {V : Type u} {P : Type u}
  [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P]

/-- Canonical affine equivalence attached to a basepoint and a complement splitting of
`C.direction`; this keeps the owner at intrinsic affine-space level instead of the concrete model
`P = V`. -/
noncomputable abbrev splitAffineEquiv (C : AffineSubspace k P) (x₀ : C)
    (Z : Submodule k V) (hcompl : IsCompl C.direction Z) :
    P ≃ᵃ[k] C.direction × Z :=
  (AffineEquiv.vaddConst k (x₀ : P)).symm.trans
    ((C.direction.prodEquivOfIsCompl Z hcompl).symm.toAffineEquiv)

/-- Primitive owner layer for Text 1.13.1 (3): once a base point `x₀ : C` and a complementary
subspace are fixed, the image of `C` under the canonical splitting affine equivalence is the graph
of a constant affine map. -/
theorem map_splitAffineEquiv_eq_graph_const
    (C : AffineSubspace k P) (x₀ : C)
    (Z : Submodule k V) (hcompl : IsCompl C.direction Z) :
    C.map (C.splitAffineEquiv x₀ Z hcompl) =
      (AffineMap.const k C.direction (0 : Z)).graph := by
  let L : V ≃ₗ[k] C.direction × Z := (C.direction.prodEquivOfIsCompl Z hcompl).symm
  have hmain :
      C.map (C.splitAffineEquiv x₀ Z hcompl) =
        (AffineMap.const k C.direction (0 : Z)).graph := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [AffineMap.mem_graph_iff]
      have hyvsub : y -ᵥ (x₀ : P) ∈ C.direction :=
        (C.vsub_right_mem_direction_iff_mem x₀.property y).2 hy
      have hzero : (L (y -ᵥ (x₀ : P))).2 = 0 := by
        exact
          (Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero
            (p := C.direction) (q := Z) (h := hcompl) (x := y -ᵥ (x₀ : P))).2 hyvsub
      simpa [splitAffineEquiv, L, AffineEquiv.vaddConst_symm_apply] using hzero
    · intro hx
      have hxz : x.2 = (0 : Z) := by
        exact
          (AffineMap.mem_graph_iff (T := AffineMap.const k C.direction (0 : Z)) (x := x)).1 hx
      let v : V := (C.direction.prodEquivOfIsCompl Z hcompl) (x.1, 0)
      let y : P := v +ᵥ (x₀ : P)
      have hyL : L (y -ᵥ (x₀ : P)) = (x.1, 0) := by
        simp [L, y, v]
      have hzero : (L (y -ᵥ (x₀ : P))).2 = 0 := by
        simp [hyL]
      have hyvsub : y -ᵥ (x₀ : P) ∈ C.direction := by
        exact
          (Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero
            (p := C.direction) (q := Z) (h := hcompl) (x := y -ᵥ (x₀ : P))).1 hzero
      have hyM : y ∈ C :=
        (C.vsub_right_mem_direction_iff_mem x₀.property y).1 hyvsub
      refine ⟨y, hyM, ?_⟩
      calc
        C.splitAffineEquiv x₀ Z hcompl y = (x.1, 0) := by
          simpa [splitAffineEquiv, L, AffineEquiv.vaddConst_symm_apply] using hyL
        _ = x := by ext <;> simp [hxz]
  exact hmain

/-- Bridge layer for Text 1.13.1 (3): from nonemptiness, choose a base point and recover the
graph presentation from `map_splitAffineEquiv_eq_graph_const`. -/
theorem exists_map_eq_graph_of_isCompl
    (C : AffineSubspace k P) (hC : Nonempty C)
    (Z : Submodule k V) (hcompl : IsCompl C.direction Z) :
    ∃ e : P ≃ᵃ[k] C.direction × Z,
    ∃ f : C.direction →ᵃ[k] Z,
      C.map e = f.graph := by
  rcases hC with ⟨x₀⟩
  refine ⟨C.splitAffineEquiv x₀ Z hcompl, AffineMap.const k C.direction (0 : Z), ?_⟩
  simpa using map_splitAffineEquiv_eq_graph_const C x₀ Z hcompl

/-- Owner-level form of Text 1.13.1 (3) for a fixed complement:
`C` is Tucker-representable with source `C.direction` and target `Z`. -/
theorem isTuckerRepresentable_of_isCompl
    (C : AffineSubspace k P) (hC : Nonempty C)
    (Z : Submodule k V) (hcompl : IsCompl C.direction Z) :
    C.IsTuckerRepresentable C.direction Z := by
  exact
    IsTuckerRepresentable.of_exists_map_eq_graph
      (exists_map_eq_graph_of_isCompl C hC Z hcompl)

/-- Primitive owner-level existence theorem: once nonemptiness is given, Tucker representability
only needs the primitive splitting datum `∃ Z, IsCompl C.direction Z`. -/
theorem exists_isTuckerRepresentable_of_nonempty_of_exists_isCompl
    (C : AffineSubspace k P) (hC : Nonempty C)
    (hsplit : ∃ Z : Submodule k V, IsCompl C.direction Z) :
    ∃ Z : Submodule k V, C.IsTuckerRepresentable C.direction Z := by
  rcases hsplit with ⟨Z, hcompl⟩
  exact ⟨Z, isTuckerRepresentable_of_isCompl C hC Z hcompl⟩

/-- Primitive explicit-witness bridge from nonemptiness plus splitting data. -/
theorem exists_map_eq_graph_of_nonempty_of_exists_isCompl
    (C : AffineSubspace k P) (hC : Nonempty C)
    (hsplit : ∃ Z : Submodule k V, IsCompl C.direction Z) :
    ∃ Z : Submodule k V, ∃ e : P ≃ᵃ[k] C.direction × Z,
      ∃ f : C.direction →ᵃ[k] Z,
        C.map e = f.graph := by
  rcases exists_isTuckerRepresentable_of_nonempty_of_exists_isCompl C hC hsplit with ⟨Z, hZ⟩
  rcases hZ.exists_map_eq_graph with ⟨e, f, hf⟩
  exact ⟨Z, e, f, hf⟩

end Primitive

section Bridge

variable {k : Type u} {V : Type u} {P : Type u}
  [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

/-- Text 1.13.1 (3) at the canonical owner layer:
a nonempty affine subspace is Tucker-representable after splitting off a complementary subspace to
its direction. -/
theorem exists_isTuckerRepresentable_of_nonempty
    (C : AffineSubspace k P) (hC : Nonempty C) :
    ∃ Z : Submodule k V, C.IsTuckerRepresentable C.direction Z := by
  exact
    exists_isTuckerRepresentable_of_nonempty_of_exists_isCompl C hC
      C.direction.exists_isCompl

/-- Bridge view of `exists_isTuckerRepresentable_of_nonempty` in explicit graph-witness form. -/
-- Proof sketch: use the owner theorem `exists_isTuckerRepresentable_of_nonempty`, then unfold the
-- owner via `isTuckerRepresentable_iff`.
theorem exists_map_eq_graph_of_nonempty
    (C : AffineSubspace k P) (hC : Nonempty C) :
    ∃ Z : Submodule k V, ∃ e : P ≃ᵃ[k] C.direction × Z,
      ∃ f : C.direction →ᵃ[k] Z,
        C.map e = f.graph :=
  by
  exact
    exists_map_eq_graph_of_nonempty_of_exists_isCompl C hC
      C.direction.exists_isCompl

end Bridge

end Graph

end AffineSubspace
