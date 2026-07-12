import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

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
