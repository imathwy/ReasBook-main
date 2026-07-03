

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_1_13_1 (from Chap01) -/
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

/-! ### Text_1_13 (from Chap01) -/
namespace AffineMap

variable {k : Type*} {V : Type*} {P : Type*} {W : Type*} {Q : Type*}
  [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P]
  [AddCommGroup W] [Module k W] [AddTorsor W Q]

/- The owner object for the graph of an affine map is the image of `⊤` under `AffineMap.id.prod`.
This keeps later graph statements in the `AffineSubspace` API instead of re-encoding them as raw
set ranges. -/
/-- The graph of an affine map, viewed as an affine subspace of the product. -/
def graph (T : P →ᵃ[k] Q) : AffineSubspace k (P × Q) :=
  (⊤ : AffineSubspace k P).map ((id k P).prod T)

-- Proof sketch: unfold `AffineMap.graph`, rewrite membership in the image of `⊤` under
-- `AffineMap.id.prod T`, and note that a pair `(x, y)` lies in that image exactly when
-- `y = T x`.
/-- A pair belongs to the graph affine subspace of `T` exactly when its second coordinate is
the value of `T` on its first coordinate. -/
@[simp]
theorem mem_graph_iff (T : P →ᵃ[k] Q) (x : P × Q) :
    x ∈ T.graph ↔ x.2 = T x.1 := by
  constructor
  · rintro ⟨y, -, rfl⟩
    rfl
  · intro hx
    exact ⟨x.1, by simp, by ext <;> simp [hx]⟩

/-- Pair-form membership in an affine graph, avoiding projection noise. -/
@[simp] theorem mk_mem_graph_iff (T : P →ᵃ[k] Q) (x : P) (y : Q) :
    (x, y) ∈ T.graph ↔ y = T x := by
  exact mem_graph_iff (T := T) (x := (x, y))

end AffineMap

section TuckerOwner

/-
Source/core/bridge triage:
- `source-facing`: Text 1.13 is exposed at the finite-cardinality owner layer:
  `Nat.card γ = Nat.card ι + Nat.card κ` and `M.affineDim = Nat.card ι`.
- `core/canonical`: the owner notions are `AffineSubspace.map`, `AffineMap.graph`, and the
  intrinsic representation owner `AffineSubspace.IsTuckerRepresentable`.
- `bridge/view`: explicit coordinate-change and graph witnesses
  `∃ e : Z ≃ᵃ[𝕜] X × Y, ∃ T : X →ᵃ[𝕜] Y, M.map e = T.graph`.
- `Layer target`: `source-facing`, with `AffineSubspace.IsTuckerRepresentable` as the canonical
  owner and existential witnesses as the bridge view.
- `downstream specialization`: concrete `Fin` coordinate formulations are downstream bridges and
  are not exported as source-item owner theorems in this file.
- `Primitive data vs derived API`: the affine subspace `M` is primitive owner data. Coordinate
  split and graph witnesses are theorem-level outputs.
- `Canonicalization decision record`:
  - The coordinate-change owner layer and representability owner data only require `[Ring 𝕜]`.
  - The stronger `[DivisionRing 𝕜]` assumption is deferred to affine-dimension theorems below.
-/

namespace AffineSubspace

variable {𝕜 V P : Type*} [Ring 𝕜]
  [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P]

/-- Predicate form of Tucker representability. This is the canonical owner-level API; existential
coordinate and map witnesses are a bridge view of this owner. -/
def IsTuckerRepresentable (M : AffineSubspace 𝕜 P)
    (X : Type*) [AddCommGroup X] [Module 𝕜 X]
    (Y : Type*) [AddCommGroup Y] [Module 𝕜 Y] : Prop :=
  ∃ e : P ≃ᵃ[𝕜] X × Y, ∃ T : X →ᵃ[𝕜] Y, M.map e = T.graph

/-- Bridge between the owner predicate and the explicit existential witness surface. -/
theorem isTuckerRepresentable_iff
    (M : AffineSubspace 𝕜 P)
    {X : Type*} [AddCommGroup X] [Module 𝕜 X]
    {Y : Type*} [AddCommGroup Y] [Module 𝕜 Y] :
    M.IsTuckerRepresentable X Y ↔
      ∃ e : P ≃ᵃ[𝕜] X × Y, ∃ T : X →ᵃ[𝕜] Y, M.map e = T.graph := by
  rfl

/-- Object-prefix elimination form of the Tucker owner bridge. -/
theorem IsTuckerRepresentable.exists_map_eq_graph
    {M : AffineSubspace 𝕜 P}
    {X : Type*} [AddCommGroup X] [Module 𝕜 X]
    {Y : Type*} [AddCommGroup Y] [Module 𝕜 Y]
    (hM : M.IsTuckerRepresentable X Y) :
    ∃ e : P ≃ᵃ[𝕜] X × Y, ∃ T : X →ᵃ[𝕜] Y, M.map e = T.graph := by
  exact (isTuckerRepresentable_iff (M := M)).1 hM

/-- Object-prefix introduction form of the Tucker owner bridge. -/
theorem IsTuckerRepresentable.of_exists_map_eq_graph
    {M : AffineSubspace 𝕜 P}
    {X : Type*} [AddCommGroup X] [Module 𝕜 X]
    {Y : Type*} [AddCommGroup Y] [Module 𝕜 Y]
    (hM : ∃ e : P ≃ᵃ[𝕜] X × Y, ∃ T : X →ᵃ[𝕜] Y, M.map e = T.graph) :
    M.IsTuckerRepresentable X Y := by
  exact (isTuckerRepresentable_iff (M := M)).2 hM

end AffineSubspace

end TuckerOwner

section TuckerDimension

variable {𝕜 : Type*} [DivisionRing 𝕜]

namespace AffineSubspace

variable {X Y Z : Type*}
  [AddCommGroup X] [Module 𝕜 X]
  [AddCommGroup Y] [Module 𝕜 Y]
  [AddCommGroup Z] [Module 𝕜 Z]

/-- Primitive owner-level Tucker representability: if `M` is nonempty, its direction has
`finrank X`, and the ambient space splits with `finrank Z = finrank X + finrank Y`, then `M` is
representable as a graph after an affine coordinate change `Z ≃ᵃ[𝕜] X × Y`. -/
theorem isTuckerRepresentable_of_finrank_direction_eq
    [FiniteDimensional 𝕜 X] [FiniteDimensional 𝕜 Y] [FiniteDimensional 𝕜 Z]
    (M : AffineSubspace 𝕜 Z) (hM : (M : Set Z).Nonempty)
    (hsplit : Module.finrank 𝕜 Z = Module.finrank 𝕜 X + Module.finrank 𝕜 Y)
    (hdir : Module.finrank 𝕜 M.direction = Module.finrank 𝕜 X) :
    M.IsTuckerRepresentable X Y := by
  classical
  rcases M.direction.exists_isCompl with ⟨W, hcompl⟩
  let L : Z ≃ₗ[𝕜] M.direction × W := (M.direction.prodEquivOfIsCompl W hcompl).symm
  let e0 : Z ≃ᵃ[𝕜] M.direction × W := L.toAffineEquiv
  rcases hM with ⟨x₀, hx₀⟩
  let z₀ : W := (L x₀).2
  have hmap0 : M.map e0 = (AffineMap.const 𝕜 M.direction z₀).graph := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [AffineMap.mem_graph_iff]
      change (L y).2 = z₀
      have hyvsub : y - x₀ ∈ M.direction :=
        (M.vsub_right_mem_direction_iff_mem hx₀ y).2 hy
      have hzero : (L (y - x₀)).2 = 0 := by
        exact
          (Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero
            (p := M.direction) (q := W) (h := hcompl) (x := y - x₀)).2 hyvsub
      have hsub : (L y).2 - (L x₀).2 = 0 := by
        simpa [L, map_sub] using hzero
      exact sub_eq_zero.mp (by simpa [z₀] using hsub)
    · intro hx
      have hxz : x.2 = z₀ := by
        exact (AffineMap.mem_graph_iff (T := AffineMap.const 𝕜 M.direction z₀) (x := x)).1 hx
      let y : Z := (M.direction.prodEquivOfIsCompl W hcompl) (x.1, z₀)
      have hyL : L y = (x.1, z₀) := by simp [L, y]
      have hsub : (L (y - x₀)).2 = (L y).2 - (L x₀).2 := by
        simp [L, map_sub]
      have hzero : (L (y - x₀)).2 = 0 := by
        calc
          (L (y - x₀)).2 = (L y).2 - (L x₀).2 := hsub
          _ = z₀ - z₀ := by simp [hyL, z₀]
          _ = 0 := sub_self z₀
      have hyvsub : y - x₀ ∈ M.direction := by
        exact
          (Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero
            (p := M.direction) (q := W) (h := hcompl) (x := y - x₀)).1
            (by simpa [L] using hzero)
      have hyM : y ∈ M :=
        (M.vsub_right_mem_direction_iff_mem hx₀ y).1 hyvsub
      refine ⟨y, hyM, ?_⟩
      calc
        e0 y = (x.1, z₀) := by simpa [e0] using hyL
        _ = x := by ext <;> simp [hxz]
  have hW : Module.finrank 𝕜 W = Module.finrank 𝕜 Y := by
    have hsum :
        Module.finrank 𝕜 X + Module.finrank 𝕜 W =
          Module.finrank 𝕜 X + Module.finrank 𝕜 Y := by
      calc
        Module.finrank 𝕜 X + Module.finrank 𝕜 W
            = Module.finrank 𝕜 M.direction + Module.finrank 𝕜 W := by
                exact congrArg (fun t : ℕ => t + Module.finrank 𝕜 W) hdir.symm
        _ = Module.finrank 𝕜 Z := Submodule.finrank_add_eq_of_isCompl hcompl
        _ = Module.finrank 𝕜 X + Module.finrank 𝕜 Y := hsplit
    exact Nat.add_left_cancel hsum
  let eX : X ≃ₗ[𝕜] M.direction :=
    LinearEquiv.ofFinrankEq X M.direction hdir.symm
  let eY : Y ≃ₗ[𝕜] W :=
    LinearEquiv.ofFinrankEq Y W hW.symm
  let eProd : M.direction × W ≃ᵃ[𝕜] X × Y :=
    (LinearEquiv.prodCongr eX.symm eY.symm).toAffineEquiv
  have hmapConst :
      (AffineMap.const 𝕜 M.direction z₀).graph.map eProd =
        (AffineMap.const 𝕜 X (eY.symm z₀)).graph := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [AffineMap.mem_graph_iff]
      have hy' : y.2 = z₀ := by
        simpa using
          (AffineMap.mem_graph_iff (T := AffineMap.const 𝕜 M.direction z₀) (x := y)).1 hy
      simp [eProd, hy']
    · intro hx
      have hxz : x.2 = eY.symm z₀ := by
        exact (AffineMap.mem_graph_iff (T := AffineMap.const 𝕜 X (eY.symm z₀)) (x := x)).1 hx
      refine ⟨(eX x.1, z₀), ?_, ?_⟩
      · exact
          (AffineMap.mem_graph_iff
            (T := AffineMap.const 𝕜 M.direction z₀) (x := (eX x.1, z₀))).2 rfl
      · ext <;> simp [eProd, hxz]
  refine ⟨e0.trans eProd, AffineMap.const 𝕜 X (eY.symm z₀), ?_⟩
  calc
    M.map (e0.trans eProd) = (M.map e0).map eProd := by
      simpa [AffineEquiv.trans_apply] using
        (AffineSubspace.map_map (s := M)
          (f := (e0 : Z →ᵃ[𝕜] M.direction × W))
          (g := (eProd : M.direction × W →ᵃ[𝕜] X × Y))).symm
    _ = ((AffineMap.const 𝕜 M.direction z₀).graph).map eProd := by
      simp [hmap0]
    _ = (AffineMap.const 𝕜 X (eY.symm z₀)).graph := hmapConst

/-- Bridge corollary from the affine-dimension surface to the primitive
`isTuckerRepresentable_of_finrank_direction_eq` owner theorem. -/
theorem isTuckerRepresentable_of_affineDim_eq_finrank
    [FiniteDimensional 𝕜 X] [FiniteDimensional 𝕜 Y] [FiniteDimensional 𝕜 Z]
    (M : AffineSubspace 𝕜 Z)
    (hsplit : Module.finrank 𝕜 Z = Module.finrank 𝕜 X + Module.finrank 𝕜 Y)
    (hdim : M.affineDim = (Module.finrank 𝕜 X : ℤ)) :
    M.IsTuckerRepresentable X Y := by
  have hM_ne_bot : M ≠ ⊥ := by
    intro hbot
    rw [AffineSubspace.affineDim, if_pos hbot] at hdim
    omega
  have hM : (M : Set Z).Nonempty :=
    (AffineSubspace.nonempty_iff_ne_bot M).2 hM_ne_bot
  have hdir : Module.finrank 𝕜 M.direction = Module.finrank 𝕜 X := by
    rw [AffineSubspace.affineDim, if_neg hM_ne_bot] at hdim
    exact Int.ofNat.inj hdim
  exact isTuckerRepresentable_of_finrank_direction_eq (M := M) hM hsplit hdir

end AffineSubspace

section CoordinateBridge

variable {ι κ γ : Type*}

local notation "E" => ι → 𝕜
local notation "F" => κ → 𝕜
local notation "G" => γ → 𝕜

namespace AffineSubspace

/-- Text 1.13 at the canonical finite-cardinality owner layer: if `M` has affine dimension
`Nat.card ι` and the ambient index type splits as
`Nat.card γ = Nat.card ι + Nat.card κ`, then `M` is Tucker representable. -/
theorem isTuckerRepresentable_of_affineDim_eq
    [Finite ι] [Finite κ] [Finite γ] (M : AffineSubspace 𝕜 G)
    (hsplit : Nat.card γ = Nat.card ι + Nat.card κ)
    (hdim : M.affineDim = (Nat.card ι : ℤ)) :
    M.IsTuckerRepresentable E F := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  letI : Fintype κ := Fintype.ofFinite κ
  letI : Fintype γ := Fintype.ofFinite γ
  refine isTuckerRepresentable_of_affineDim_eq_finrank (M := M) ?_ ?_
  · simpa [Nat.card_eq_fintype_card, Module.finrank_pi] using hsplit
  · simpa [Nat.card_eq_fintype_card, Module.finrank_pi] using hdim

/-- Explicit witness form for Text 1.13 at the same owner layer. -/
theorem exists_affineEquiv_map_eq_graph_of_affineDim_eq
    [Finite ι] [Finite κ] [Finite γ] (M : AffineSubspace 𝕜 G)
    (hsplit : Nat.card γ = Nat.card ι + Nat.card κ)
    (hdim : M.affineDim = (Nat.card ι : ℤ)) :
    ∃ e : G ≃ᵃ[𝕜] E × F, ∃ T : E →ᵃ[𝕜] F, M.map e = T.graph := by
  exact (isTuckerRepresentable_of_affineDim_eq (M := M) hsplit hdim).exists_map_eq_graph

end AffineSubspace

end CoordinateBridge

end TuckerDimension
