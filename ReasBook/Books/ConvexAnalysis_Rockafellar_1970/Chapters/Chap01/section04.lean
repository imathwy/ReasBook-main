import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_1_4_1 (from Chap01) -/
noncomputable section

open AffineSubspace

/-
Corollary 1.4.1 is organized around the affine-subspace owner abstraction
`AffineSubspace.is_hyperplane`. The coordinate-free chapter owner theorem
`AffineSubspace.exists_surjective_eq_pi_fiber_of_ne_bot` identifies a proper affine subspace with
the fiber of a surjective linear map into finite coordinate space. The scalar projections of that
map are then converted to the chapter-owned hyperplane constructor `linearHyperplane`, and the
hyperplane witness is discharged via the canonical owner theorem
`linearHyperplane_is_hyperplane` from Theorem 1.3 rather than a local duplicate proof.
The public corollary is formulated at the intrinsic quotient finite/free layer
`Module.Free k (V ⧸ s.direction)` + `Module.Finite k (V ⧸ s.direction)` over a division ring.
-/
recall exists_surjective_eq_pi_fiber_of_ne_bot

/-
Source/core/bridge triage:
- `source-facing`: Corollary 1.4.1 says every affine subspace is a finite intersection of
  hyperplanes.
- `core/canonical`: the owner abstraction is `AffineSubspace k V` with the predicate
  `AffineSubspace.is_hyperplane`.
- `bridge/view`: the `Finset`/`sInf` formulation is an operational finite-set bridge derived from
  the owner-level finite `iInf` statement. The finite family of scalar equations is obtained from
  the owner-side coordinate bridge `AffineSubspace.exists_surjective_eq_pi_fiber_of_ne_bot`.
- Primitive data vs derived API: the primitive data are just the affine subspace `s`; the quotient
  presentation from `AffineSubspace.exists_surjective_eq_pi_fiber_of_ne_bot` and the coordinate
  projections `LinearMap.proj` are internal proof data, while the family of `linearHyperplane`s
  and the finite-intersection statements are the public derived API.
- Domain-style sampling: the owner-side declarations used here are
  `AffineSubspace.exists_surjective_eq_pi_fiber_of_ne_bot`, `LinearMap.proj`,
  `linearHyperplane`, `linearHyperplane_is_hyperplane`, and
  `Projective.exists_dual_ne_zero`.
- Layer target: `source-facing`, with the public statements kept directly in the intrinsic
  `AffineSubspace`/hyperplane language.
-/

section HyperplaneIntersections

variable {k V : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]

private theorem exists_setFinite_eq_sInf_of_eq_iInf {ι : Type*} [Finite ι]
    {s : AffineSubspace k V}
    (H : ι → AffineSubspace k V)
    (hH : ∀ i, (H i).is_hyperplane)
    (hs : s = ⨅ i, H i) :
    ∃ T : Set (AffineSubspace k V), T.Finite ∧
      (∀ K ∈ T, K.is_hyperplane) ∧ s = sInf T := by
  refine ⟨Set.range H, Set.finite_range H, ?_, ?_⟩
  · intro K hK
    rcases hK with ⟨i, rfl⟩
    exact hH i
  · simpa [sInf_range] using hs

namespace AffineSubspace

/-- Corollary 1.4.1, primitive owner form: every proper affine subspace whose direction quotient
is finite and free over a division ring is the intersection of finitely many affine hyperplanes,
expressed as an `iInf` of a finite indexed family at the owner layer. -/
theorem exists_eq_iInf_hyperplanes_of_ne_bot (s : AffineSubspace k V)
    [Module.Free k (V ⧸ s.direction)] [Module.Finite k (V ⧸ s.direction)]
    (hs : s ≠ ⊥) :
    ∃ ι : Type, ∃ _ : Finite ι, ∃ H : ι → AffineSubspace k V,
      (∀ i, (H i).is_hyperplane) ∧ s = ⨅ i, H i := by
  classical
  rcases s.exists_surjective_eq_pi_fiber_of_ne_bot hs with ⟨ι, hι, A, b, hA_surj, hsA⟩
  let _ : Fintype ι := hι
  let H : ι → AffineSubspace k V := fun i ↦ linearHyperplane ((LinearMap.proj i).comp A) (b i)
  have hH : ∀ i, (H i).is_hyperplane := by
    intro i
    have hproj : (LinearMap.proj i).comp A ≠ 0 := by
      intro hzero
      obtain ⟨x, hx⟩ := hA_surj (Pi.single i 1)
      have hx1 : ((LinearMap.proj i).comp A) x = 1 := by
        simp [hx]
      have hx0 : ((LinearMap.proj i).comp A) x = 0 := by
        simp [hzero]
      exact one_ne_zero (hx1.symm.trans hx0)
    simpa [H] using linearHyperplane_is_hyperplane ((LinearMap.proj i).comp A) (b i) hproj
  have hs' : (affineSpan k ({b} : Set (ι → k))).comap A.toAffineMap = ⨅ i, H i := by
    refine le_antisymm ?_ ?_
    · refine le_iInf ?_
      intro i x hx
      have hxA : A x = b := by
        rw [mem_comap, mem_affineSpan_singleton] at hx
        simpa [LinearMap.coe_toAffineMap] using hx
      have hEq : ((LinearMap.proj i).comp A) x = b i := by
        simpa [LinearMap.proj_apply] using congrArg (fun y : ι → k ↦ y i) hxA
      simpa [H] using hEq
    · intro x hx
      have hxA : A x = b := by
        ext i
        have hmem : x ∈ H i := (mem_iInf_iff H x).1 hx i
        have hEq : ((LinearMap.proj i).comp A) x = b i := by
          simpa [H] using hmem
        simpa [LinearMap.proj_apply] using hEq
      rw [mem_comap, mem_affineSpan_singleton]
      simpa [LinearMap.coe_toAffineMap] using hxA
  exact ⟨ι, Finite.of_fintype ι, H, hH, hsA.trans hs'⟩

/-- Corollary 1.4.1, owner-level finite-family form: every affine subspace of a nontrivial module
whose direction quotient is finite and free over a division ring is the intersection of finitely
many affine hyperplanes, expressed canonically as an `iInf` of a finite indexed family. -/
theorem exists_eq_iInf_hyperplanes [Nontrivial V] (s : AffineSubspace k V)
    [Module.Free k (V ⧸ s.direction)] [Module.Finite k (V ⧸ s.direction)] :
    ∃ ι : Type, ∃ _ : Finite ι, ∃ H : ι → AffineSubspace k V,
      (∀ i, (H i).is_hyperplane) ∧ s = ⨅ i, H i := by
  rcases s.eq_bot_or_nonempty with rfl | ⟨p, hp⟩
  · obtain ⟨v, hv⟩ : ∃ v : V, v ≠ 0 := by
      simpa using exists_ne (0 : V)
    obtain ⟨f, hfv⟩ : ∃ f : Module.Dual k V, f v ≠ 0 :=
      Module.Projective.exists_dual_ne_zero k hv
    have hf : (f : V →ₗ[k] k) ≠ 0 := by
      intro hf0
      have : f v = 0 := by simp [hf0]
      exact hfv this
    let γ : k := f v
    let H : Bool → AffineSubspace k V
      | false => linearHyperplane f 0
      | true => linearHyperplane f γ
    have hH : ∀ i, (H i).is_hyperplane := by
      intro i
      cases i with
      | false => simpa [H] using linearHyperplane_is_hyperplane f (0 : k) hf
      | true => simpa [H, γ] using linearHyperplane_is_hyperplane f γ hf
    have hs : (⊥ : AffineSubspace k V) = ⨅ i, H i := by
      refine le_antisymm bot_le ?_
      intro x hx
      exfalso
      have h0 : f x = 0 := by
        simpa [H] using (mem_iInf_iff H x).1 hx false
      have hγ : f x = γ := by
        simpa [H, γ] using (mem_iInf_iff H x).1 hx true
      have hfv0 : f v = 0 := by
        have hγ' : f x = f v := by simpa [γ] using hγ
        exact hγ'.symm.trans h0
      exact hfv hfv0
    exact ⟨Bool, inferInstance, H, hH, hs⟩
  · have hsbot : s ≠ (⊥ : AffineSubspace k V) := by
      intro hbot
      simp [hbot] at hp
    exact exists_eq_iInf_hyperplanes_of_ne_bot s hsbot

/-- Corollary 1.4.1, intrinsic finite-set owner form from primitive data: every proper affine
subspace whose direction quotient is finite and free is an `sInf` of a finite set of affine
hyperplanes. -/
theorem exists_eq_sInf_hyperplanes_of_ne_bot (s : AffineSubspace k V)
    [Module.Free k (V ⧸ s.direction)] [Module.Finite k (V ⧸ s.direction)]
    (hs : s ≠ ⊥) :
    ∃ T : Set (AffineSubspace k V), T.Finite ∧
      (∀ H ∈ T, H.is_hyperplane) ∧ s = sInf T := by
  rcases exists_eq_iInf_hyperplanes_of_ne_bot s hs with ⟨ι, hι, H, hH, hs⟩
  let _ : Finite ι := hι
  exact exists_setFinite_eq_sInf_of_eq_iInf H hH hs

/-- Corollary 1.4.1, intrinsic finite-set owner form: every affine subspace of a nontrivial module
whose direction quotient is finite and free is an `sInf` of a finite set of affine hyperplanes.
-/
theorem exists_eq_sInf_hyperplanes [Nontrivial V] (s : AffineSubspace k V)
    [Module.Free k (V ⧸ s.direction)] [Module.Finite k (V ⧸ s.direction)] :
    ∃ T : Set (AffineSubspace k V), T.Finite ∧
      (∀ H ∈ T, H.is_hyperplane) ∧ s = sInf T := by
  rcases exists_eq_iInf_hyperplanes s with ⟨ι, hι, H, hH, hs⟩
  let _ : Finite ι := hι
  exact exists_setFinite_eq_sInf_of_eq_iInf H hH hs

/-- Corollary 1.4.1, finite-operational bridge form from primitive data: every proper affine
subspace whose direction quotient is finite and free is a finite `sInf` of affine hyperplanes,
indexed by a `Finset`. -/
theorem exists_eq_sInf_finset_hyperplanes_of_ne_bot (s : AffineSubspace k V)
    [Module.Free k (V ⧸ s.direction)] [Module.Finite k (V ⧸ s.direction)]
    (hs : s ≠ ⊥) :
    ∃ t : Finset (AffineSubspace k V),
      (∀ H ∈ t, H.is_hyperplane) ∧
        s = sInf (t : Set (AffineSubspace k V)) := by
  rcases exists_eq_sInf_hyperplanes_of_ne_bot s hs with ⟨T, hTfin, hT, hsT⟩
  refine ⟨hTfin.toFinset, ?_, ?_⟩
  · intro H hHmem
    exact hT H (hTfin.mem_toFinset.mp hHmem)
  · simpa [hTfin.coe_toFinset] using hsT

/-- Corollary 1.4.1: every affine subspace of a nontrivial module over a division ring whose
direction quotient is finite and free is the intersection of finitely many affine hyperplanes. -/
theorem exists_eq_sInf_finset_hyperplanes [Nontrivial V] (s : AffineSubspace k V)
    [Module.Free k (V ⧸ s.direction)] [Module.Finite k (V ⧸ s.direction)] :
    ∃ t : Finset (AffineSubspace k V),
      (∀ H ∈ t, H.is_hyperplane) ∧
        s = sInf (t : Set (AffineSubspace k V)) := by
  rcases exists_eq_sInf_hyperplanes s with ⟨T, hTfin, hT, hsT⟩
  refine ⟨hTfin.toFinset, ?_, ?_⟩
  · intro H hHmem
    exact hT H (hTfin.mem_toFinset.mp hHmem)
  · simpa [hTfin.coe_toFinset] using hsT

end AffineSubspace

end HyperplaneIntersections

/-! ### Text_1_4 (from Chap01) -/
/- 
Source/core/bridge triage:
- `source-facing`: Text 1.4 names the dimension of an affine set.
- `core/canonical`: the chapter owner abstraction is `AffineSubspace.affineDim`.
- `bridge/view`: no extra bridge is needed here; the numbered item is already the owner declaration.
- Primitive data vs derived API: the primitive notion is the chapter-owned definition
  `AffineSubspace.affineDim`, so this file should stay a direct recall rather than introducing a
  parallel alias or wrapper.
- Domain-style sampling used here: `AffineSubspace.affineDim` from `AffineDimension`,
  `Set.affineDim` from `Definition_2_4_10`, and the nearby owner-derived predicates
  `AffineSubspace.is_point` and `AffineSubspace.is_hyperplane`, confirming that the affine-set
  dimension notion is already owned upstream by `AffineSubspace`.
- Canonicalization checks:
  - codomain/ambient layer: no over-concrete codomain is exposed; this item only recalls the owner.
  - scalar/ambient structure: the owner is already at the generic `DivisionRing` affine-space layer.
  - owner choice: the notion is intrinsically affine-subspace dimension, so `AffineSubspace` is the
    correct owner.
  - topology phrasing: this item has no topology-facing statement.
  - owner naming: `AffineSubspace.affineDim` is already the chapter's short canonical owner.
  - notation surface: no extra notation layer is needed for this recall-only item.
-/
/- Text 1.4: the textbook dimension convention for an affine set is the canonical chapter owner
declaration `AffineSubspace.affineDim`, namely the finrank of the parallel subspace when the affine
subspace is nonempty and `-1` for the empty affine subspace. -/
recall AffineSubspace.affineDim

/-! ### Theorem_1_4 (from Chap01) -/
/-
Source/core/bridge triage:
- `source-facing`: Theorem 1.4 identifies affine subsets of finite coordinate modules with
  solution sets of finite linear systems.
- `core/canonical`: the owner abstraction is `AffineSubspace k V` on an arbitrary `k`-module `V`,
  with the intrinsic fiber construction owned as `LinearMap.affineFiber`;
  the public core statement is `AffineSubspace.eq_comap_mkQ_singleton`.
- `bridge/view`: finite coordinate families enter first through the quotient-coordinate bridges
  `AffineSubspace.exists_surjective_eq_pi_fiber_of_ne_bot`,
  `AffineSubspace.exists_eq_pi_fiber_of_ne_bot`, and `AffineSubspace.exists_eq_pi_fiber`, and
  then into matrices via `LinearMap.toMatrix'` and `Matrix.mulVecLin`.
- Primitive data vs derived API: an affine subset is primitive as an `AffineSubspace`; the matrix
  presentation is derived from the owner data `S.direction` and a point `p ∈ S` by passing to the
  intrinsic quotient point `S.direction.mkQ p` and only then choosing coordinates.
- Domain-style sampling: the relevant owner-side declarations reused here are
  `LinearMap.affineFiber`, `LinearMap.mem_affineFiber`, `Submodule.Quotient.eq`,
  `Module.Free.chooseBasis`, and `Module.Basis.equivFun`; `Matrix.mulVecLin` is
  used only in the final coordinate bridge.
- Layer target: `core/canonical` for `AffineSubspace.eq_comap_mkQ_singleton`, then
  `bridge/view` for the finite-coordinate and matrix specializations.
-/

/- Canonicalization decision record (this pass):
- Codomain/ambient check: this item is not extended-valued; no `WithTopBot`-style codomain owner
  appears.
- Scalar/ambient-structure check: all owner statements stay at the minimal `AffineSubspace`
  `[Ring k]` layer; no `ℝ`/Euclidean specialization is used.
- Owner check: the primitive owner bridge should expose only `S = A.affineFiber b`; surjectivity
  is a stronger coordinate-view witness and is kept as a separate theorem.
- Topology check: this item is algebraic (affine/linear), not topology-facing.
- Owner-name/notation check: keep canonical owner names and existing notation; no macro layer.
-/

open AffineSubspace

section Owner

variable {k V : Type*} [Ring k] [AddCommGroup V] [Module k V]

namespace LinearMap

variable {W : Type*} [AddCommGroup W] [Module k W]

/-- Affine fiber of a linear map at one target point. -/
def affineFiber (A : V →ₗ[k] W) (b : W) : AffineSubspace k V :=
  (affineSpan k ({b} : Set W)).comap A.toAffineMap

/-- Membership in a linear-map affine fiber is exactly the defining equation. -/
@[simp] theorem mem_affineFiber {A : V →ₗ[k] W} {b : W} {x : V} :
    x ∈ A.affineFiber b ↔ A x = b := by
  rw [affineFiber, AffineSubspace.mem_comap, AffineSubspace.mem_affineSpan_singleton]
  simp [LinearMap.coe_toAffineMap]

end LinearMap

namespace AffineSubspace

/-- Intrinsic owner theorem for Theorem 1.4 (2): if `p ∈ S`, then `S` is exactly the pullback of
the singleton affine subspace `{S.direction.mkQ p}` along the quotient map `S.direction.mkQ`. -/
theorem eq_comap_mkQ_singleton (S : AffineSubspace k V) {p : V} (hp : p ∈ S) :
    S = (S.direction.mkQ).affineFiber (S.direction.mkQ p) := by
  let q : V →ₗ[k] V ⧸ S.direction := S.direction.mkQ
  ext x
  rw [LinearMap.mem_affineFiber]
  constructor
  · intro hx
    exact (Submodule.Quotient.eq S.direction).2 <|
      (vsub_right_mem_direction_iff_mem hp x).2 hx
  · intro hx
    exact (vsub_right_mem_direction_iff_mem hp x).1 <|
      (Submodule.Quotient.eq S.direction).1 hx

/-- Intrinsic `ne_bot` owner form of Theorem 1.4 (2): a proper affine subspace is the pullback
of a singleton affine subspace in its quotient by direction, with the singleton point given
directly in the quotient. -/
theorem exists_eq_comap_mkQ_singleton_of_ne_bot (S : AffineSubspace k V) (hs : S ≠ ⊥) :
    ∃ q : V ⧸ S.direction, S = (S.direction.mkQ).affineFiber q := by
  rcases S.eq_bot_or_nonempty with hSbot | ⟨p, hp⟩
  · exact (hs hSbot).elim
  · exact ⟨S.direction.mkQ p, S.eq_comap_mkQ_singleton hp⟩

end AffineSubspace

namespace AffineSubspace

/-- Strong coordinate-view bridge for a proper affine subspace: choosing coordinates on the
quotient by the direction gives a surjective linear map into a finite coordinate family
`ι → k` whose fiber over one point is exactly `S`. -/
theorem exists_surjective_eq_pi_fiber_of_ne_bot {k V : Type*} [Ring k]
    [AddCommGroup V] [Module k V] (S : AffineSubspace k V)
    [Module.Free k (V ⧸ S.direction)] [Module.Finite k (V ⧸ S.direction)] (hs : S ≠ ⊥) :
    ∃ (ι : Type) (_ : Fintype ι) (A : V →ₗ[k] ι → k) (b : ι → k),
      Function.Surjective A ∧ S = A.affineFiber b := by
  let Q := V ⧸ S.direction
  let ι0 : Type _ := Module.Free.ChooseBasisIndex k Q
  let _ : Fintype ι0 := Module.Free.ChooseBasisIndex.fintype k Q
  let m : ℕ := Fintype.card ι0
  let eBasis : Q ≃ₗ[k] ι0 → k := (Module.Free.chooseBasis k Q).equivFun
  let eCoord : (ι0 → k) ≃ₗ[k] Fin m → k :=
    LinearEquiv.funCongrLeft k k (Fintype.equivFin ι0).symm
  let e : Q ≃ₗ[k] Fin m → k := eBasis.trans eCoord
  let q : V →ₗ[k] Q := S.direction.mkQ
  rcases S.exists_eq_comap_mkQ_singleton_of_ne_bot hs with ⟨qb, hS⟩
  let A : V →ₗ[k] Fin m → k := e.toLinearMap.comp q
  let b : Fin m → k := e qb
  refine ⟨Fin m, inferInstance, A, b, ?_, ?_⟩
  · intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    obtain ⟨x, hx⟩ := S.direction.mkQ_surjective z
    refine ⟨x, ?_⟩
    simpa [A] using congrArg e hx
  · have hxQ : ∀ x : V, x ∈ S ↔ q x = qb := by
      intro x
      have hS' : S = q.affineFiber qb := by simpa [Q, q] using hS
      have hxS : x ∈ S ↔ x ∈ q.affineFiber qb := by
        constructor <;> intro hx <;> simpa [hS'] using hx
      have hxq : x ∈ q.affineFiber qb ↔ q x = qb := by
        rw [LinearMap.mem_affineFiber]
      exact hxS.trans hxq
    ext x
    rw [LinearMap.mem_affineFiber]
    constructor
    · intro hx
      simpa [A, b] using congrArg e ((hxQ x).1 hx)
    · intro hx
      exact (hxQ x).2 <| e.injective <| by simpa [A, b] using hx

/-- Primitive owner-level finite-coordinate bridge for a proper affine subspace: a proper affine
subspace with finite/free quotient by direction is a linear-map fiber over one point in some
finite coordinate family `ι → k`. -/
theorem exists_eq_pi_fiber_of_ne_bot {k V : Type*} [Ring k]
    [AddCommGroup V] [Module k V] (S : AffineSubspace k V)
    [Module.Free k (V ⧸ S.direction)] [Module.Finite k (V ⧸ S.direction)] (hs : S ≠ ⊥) :
    ∃ (ι : Type) (_ : Fintype ι) (A : V →ₗ[k] ι → k) (b : ι → k),
      S = A.affineFiber b := by
  rcases S.exists_surjective_eq_pi_fiber_of_ne_bot hs with ⟨ι, hι, A, b, -, hS⟩
  exact ⟨ι, hι, A, b, hS⟩

/-- Owner-level finite-coordinate bridge for Theorem 1.4 (2): every affine subspace whose
direction quotient `V ⧸ S.direction` is finite and free over a ring is the
fiber of a linear map into some finite coordinate family `ι → k`. The matrix forms below are
derived coordinate views of this owner theorem. -/
theorem exists_eq_pi_fiber {k V : Type*} [Ring k] [Nontrivial k]
    [AddCommGroup V] [Module k V] (S : AffineSubspace k V)
    [Module.Free k (V ⧸ S.direction)] [Module.Finite k (V ⧸ S.direction)] :
    ∃ (ι : Type) (_ : Fintype ι) (A : V →ₗ[k] ι → k) (b : ι → k),
      S = A.affineFiber b := by
  rcases S.eq_bot_or_nonempty with rfl | ⟨p, hp⟩
  · refine ⟨Unit, inferInstance, 0, (fun _ : Unit ↦ (1 : k)), ?_⟩
    have h01 : (0 : Unit → k) ≠ (fun _ : Unit ↦ (1 : k)) := by
      intro h
      have h0 : (0 : k) = 1 := by
        simpa using congrArg (fun y : Unit → k ↦ y ()) h
      exact zero_ne_one h0
    ext x
    rw [LinearMap.mem_affineFiber]
    constructor
    · intro hx
      exact (False.elim <| by simpa using hx)
    · intro hx
      exact (False.elim <| h01 <| by simpa [LinearMap.zero_apply] using hx)
  · have hsbot : S ≠ (⊥ : AffineSubspace k V) := by
      intro hbot
      simp [hbot] at hp
    rcases S.exists_eq_pi_fiber_of_ne_bot hsbot with ⟨ι, hι, A, b, hS⟩
    exact ⟨ι, hι, A, b, hS⟩

end AffineSubspace

end Owner

section Matrix

variable {𝕜 : Type*}
variable {n : Type*} [Fintype n]

local notation "E" => n → 𝕜

-- Proof sketch: the solution set is the preimage of the singleton affine subspace `{b}` under the
-- affine map associated to `B.mulVecLin`, so it is canonically an affine subspace of `𝕜^n`.
/-- Theorem 1.4 (1), matrix bridge form over a commutative ring: for any matrix `B` and
right-hand side `b`, the solution set `{x | Bx = b}` in `𝕜^n` is the affine subspace obtained by
pulling back the singleton affine subspace `{b}` along `B.mulVecLin`. -/
@[simp]
theorem Matrix.solution_set_eq_affineFiber [CommRing 𝕜] {m : Type*}
    (B : Matrix m n 𝕜) (b : m → 𝕜) :
    ((B.mulVecLin).affineFiber b : Set E) =
      {x : E | B.mulVec x = b} := by
  ext x
  simp [LinearMap.mem_affineFiber]

-- Proof sketch: if `S` is nonempty, choose `p ∈ S`, pass to the finite-dimensional quotient by
-- `S.direction`, and use coordinates on that quotient to realize `S` as the fiber of a linear map;
-- then convert that owner-side linear fiber theorem to coordinates via `LinearMap.toMatrix'`.
-- For `⊥`, use the inconsistent zero-row system `0 = 1`.
/-- Theorem 1.4 (2), source-facing matrix bridge form: every affine subspace of `𝕜^n` whose
direction quotient is finite and free over a nontrivial commutative ring is
the solution affine subspace of some finite linear system `Bx = b`. -/
theorem AffineSubspace.exists_eq_matrix_solution_set [CommRing 𝕜] [Nontrivial 𝕜]
    (S : AffineSubspace 𝕜 E)
    [Module.Free 𝕜 (E ⧸ S.direction)] [Module.Finite 𝕜 (E ⧸ S.direction)] :
    ∃ (ι : Type) (_ : Fintype ι) (B : Matrix ι n 𝕜) (b : ι → 𝕜),
      S = (B.mulVecLin).affineFiber b := by
  classical
  rcases S.exists_eq_pi_fiber with ⟨ι, hι, A, b, hS⟩
  let B : Matrix ι n 𝕜 := LinearMap.toMatrix' A
  have hA : B.mulVecLin = A := by
    simpa [B, Matrix.toLin'_apply'] using (Matrix.toLin'_toMatrix' A)
  refine ⟨ι, hι, B, b, ?_⟩
  simpa [hA] using hS

end Matrix
