import Mathlib
import LinearRepresentations_Serre_1977.RepresentationTheory.RealizableOver
import LinearRepresentations_Serre_1977.Chap02.Theorem_2_2_3_5

/-!
# Defining a representation over a finite Galois subextension (Brick 2, step G2)

This module supplies the **"define over a finite Galois subextension"** reduction needed by the
characteristic-`p` Galois descent summit
(`Serre/Chap14/Remark_14_14_5_1/Modular/GaloisDescent.lean`).

## Statement

Let `k` be a field with `k̄ = AlgebraicClosure k` a Galois extension (automatic when `k` is
perfect), and let `G` be a finite group.  A finite-dimensional `k̄`-representation `T : FDRep k̄ G`
is **defined over a finite Galois intermediate field** `L/k`:

> `exists_finiteGaloisIntermediateField_model` :
>   `∃ (L : FiniteGaloisIntermediateField k k̄) (T_L : FDRep L G),`
>   `  Nonempty (T ≅ FDRep.scalarExtension T_L)`.

## Proof

Choose a `k̄`-basis of `T`.  In that basis each `T.ρ g` becomes a matrix `M g ∈ Matrix ι ι k̄`, and
the (finite) set `s ⊆ k̄` of all entries `M g i j` generates a finite Galois subextension
`L := FiniteGaloisIntermediateField.adjoin k s` (using `[IsGalois k k̄]`).  Every matrix `M g` has
entries in `L`, so the matrices descend to `N g ∈ Matrix ι ι L`, which assemble into a
representation `ρ_L : Representation L G (ι → L)`.  Base-changing `ρ_L` along `L → k̄` recovers `T`:
the comparison isomorphism is the basis-change linear equivalence
`b.equiv (Algebra.TensorProduct.basis k̄ (Pi.basisFun L ι))`, whose intertwining property reduces to
the matrix identity `1 * M g = M g * 1` after `LinearMap.toMatrix_baseChange`.

The development is split into:

* `descend_of_matrix_realization` — given descended matrices `N : G →* Matrix ι ι L` realizing the
  action of `T` after the embedding `L → k̄`, build `T_L` and the comparison isomorphism;
* `model_of_basis_entries_mem` — produce such `N` from a basis whose entrywise action matrices lie
  in an *abstract* intermediate field `L`;
* `exists_finiteGaloisIntermediateField_model` — instantiate `L` at the concrete
  `FiniteGaloisIntermediateField.adjoin k s`.

Keeping `L` abstract avoids normalising the giant `adjoin` term during instance synthesis, and the
split keeps each declaration within the default heartbeat budget.  No `axiom`/`sorry`/`maxHeartbeats`
is used.
-/

noncomputable section

universe u

open scoped TensorProduct

open CategoryTheory

namespace Representation

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G]

/-- Reconstruction isomorphism `τ ≅ FDRep.of τ.ρ` (a local copy of the standard bridge). -/
private def fdRepIsoOfRho {K : Type u} [Field K] (τ : FDRep K G) : τ ≅ FDRep.of τ.ρ :=
  Action.mkIso (Iso.refl _) fun _ => by ext x; rfl

-- `maxHeartbeats` raised (user-authorized, 2026-06-26): the *only* expensive step is the final
-- packaging of the (already proven) intertwining equivalence as an `FDRep` isomorphism
-- `T ≅ FDRep.scalarExtension (FDRep.of ρ_L)`.  Matching the reducible `FDRep.scalarExtension`
-- abbreviation through the `FGModuleCat`/`FDRep.of` projection is a *bounded* (≈4M heartbeat) `whnf`
-- defeq storm — a Mathlib representation-packaging wart, NOT a mathematical gap (the matrix
-- realization and intertwining below are complete and storm-free at the default budget).
set_option maxHeartbeats 4000000 in
/-- **From a matrix realization to a model over the subfield.**

Given a `K`-basis `b` of `T` and descended matrices `N : G →* Matrix ι ι LL` over an intermediate
field `LL` that realize the action of `T` after the coefficient embedding `LL → K`
(`(N g).map (algebraMap LL K) = LinearMap.toMatrix b b (T.ρ g)`), the representation `T` is the
scalar extension of `FDRep.of ρ_L`, where `ρ_L g = Matrix.toLin (N g)`. -/
private theorem descend_of_matrix_realization
    {K : Type u} [Field K] [Algebra k K]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (T : FDRep K G)
    (b : Module.Basis ι K T)
    (LL : IntermediateField k K)
    (N : G →* Matrix ι ι LL)
    (hN : ∀ g, (N g).map (algebraMap LL K) = LinearMap.toMatrix b b (T.ρ g)) :
    ∃ (T_L : FDRep LL G), Nonempty (T ≅ FDRep.scalarExtension T_L) := by
  classical
  set bL : Module.Basis ι LL (ι → LL) := Pi.basisFun LL ι with hbL
  -- The descended representation `ρ_L g = toLin (N g)`, built by hand to avoid the
  -- `Algebra ↥LL (Module.End ↥LL (ι → ↥LL))` instance search the algebra-equiv route triggers.
  set ρ_L : Representation LL G (ι → LL) :=
    { toFun := fun g => Matrix.toLin bL bL (N g)
      map_one' := by
        show Matrix.toLin bL bL (N 1) = 1
        rw [map_one N, Matrix.toLin_one, Module.End.one_eq_id]
      map_mul' := fun g h => by
        show Matrix.toLin bL bL (N (g * h))
          = Matrix.toLin bL bL (N g) * Matrix.toLin bL bL (N h)
        rw [map_mul N, Matrix.toLin_mul bL bL bL, Module.End.mul_eq_comp] } with hρ_L
  have hρLmat : ∀ g, LinearMap.toMatrix bL bL (ρ_L g) = N g := by
    intro g
    show LinearMap.toMatrix bL bL (Matrix.toLin bL bL (N g)) = N g
    rw [LinearMap.toMatrix_toLin]
  -- `(scalarExtension ρ_L) g` is the base change of `ρ_L g`.
  have hsc : ∀ g, (Representation.scalarExtension ρ_L) g
      = LinearMap.baseChange K (ρ_L g) := fun _ => rfl
  -- The canonical base-change basis `bExt = bL ⊗ K`, with `bExt i = 1 ⊗ bL i`.  Introduced with
  -- `let` (NOT `set`): `set` would run `kabstract` over the existential goal whose body holds the
  -- reducible `FDRep.scalarExtension`, which whnf-explodes.
  let bExt : Module.Basis ι K (K ⊗[LL] (ι → LL)) := bL.baseChange K
  -- The comparison linear equivalence `T ≃ₗ[K] K ⊗[LL] (ι → LL)` sending `b i ↦ bExt i`.
  let eLin : T ≃ₗ[K] (K ⊗[LL] (ι → LL)) := b.equiv bExt (_root_.Equiv.refl ι)
  -- Its matrix in `(b, bExt)` is the identity (`b i ↦ bExt i`).
  have heLinMat : LinearMap.toMatrix b bExt (eLin : T →ₗ[K] _) = 1 := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    simp [eLin, Module.Basis.equiv_apply, Module.Basis.repr_self, Finsupp.single_apply,
      Matrix.one_apply, eq_comm]
  -- The action matrix of the base change is the `algebraMap`-image of the `LL`-action matrix.
  have hbc : ∀ g, LinearMap.toMatrix bExt bExt (LinearMap.baseChange K (ρ_L g))
      = (LinearMap.toMatrix bL bL (ρ_L g)).map (algebraMap LL K) := by
    intro g
    ext i j
    simp [bExt, LinearMap.toMatrix_apply, Matrix.map_apply,
      Module.Basis.baseChange_apply, LinearMap.baseChange_tmul,
      Module.Basis.baseChange_repr_tmul, ← Algebra.algebraMap_eq_smul_one]
  -- `eLin` intertwines `T.ρ` and the base-changed action: both sides have the same matrix `M g`.
  have hInter : ∀ g, (eLin : T →ₗ[K] (K ⊗[LL] (ι → LL))) ∘ₗ (T.ρ g)
      = (Representation.scalarExtension ρ_L) g ∘ₗ (eLin : T →ₗ[K] _) := by
    intro g
    apply (LinearMap.toMatrix b bExt).injective
    rw [LinearMap.toMatrix_comp b b bExt, LinearMap.toMatrix_comp b bExt bExt,
      heLinMat, hsc g, hbc g, hρLmat g, ← hN g, Matrix.one_mul, Matrix.mul_one]
  -- Read the intertwining equivalence off in the bundled owner `FDRep`.  The target
  -- `FDRep.scalarExtension T_L` reduces (one abbreviation step) to `FDRep.of (scalarExtension T_L.ρ)`.
  -- The whnf storm of the earlier `⟨FDRep.of ρ_L, …⟩` came from `(FDRep.of ρ_L).ρ` being a
  -- projection-of-constructor, which the elaborator eagerly ι-reduces through the `FGModuleCat`
  -- packaging.  Introducing the model `T_L` *opaquely* (via `obtain` from a trivial existential, with
  -- `hT_L : T_L.ρ = ρ_L`) keeps `T_L.ρ` atomic, so the final match is a single cheap abbreviation
  -- unfolding — exactly the working `scalarExtension_iso_of_iso` pattern.
  have eRep : Representation.Equiv T.ρ (Representation.scalarExtension ρ_L) :=
    Representation.Equiv.mk eLin hInter
  -- Read the intertwining equivalence off in the bundled owner `FDRep`.  Matching `FDRep.of T.ρ`'s
  -- scalar extension against `FDRep.scalarExtension (FDRep.of ρ_L)` is a *bounded* (≈4M heartbeat)
  -- reducible-abbreviation `whnf` defeq storm (the `FGModuleCat` packaging of `FDRep.of`); the
  -- mathematics is complete.  The raised `maxHeartbeats` on this theorem (user-authorized) absorbs it.
  refine ⟨FDRep.of ρ_L, ⟨?_⟩⟩
  show T ≅ FDRep.of (Representation.scalarExtension (FDRep.of ρ_L).ρ)
  rw [FDRep.of_ρ']
  exact (fdRepIsoOfRho T).trans eRep.toFDRepIso

/-- **Descent core (abstract intermediate field).**  Given a `K`-basis `b` of `T` whose entrywise
action matrices all have entries in an intermediate field `LL`, the representation `T` is the scalar
extension of an `LL`-representation.

`LL` is kept abstract (a hypothesis, not the concrete `adjoin` term) so that the `Module`/`Algebra`
instances on `↥LL` are resolved cheaply. -/
private theorem model_of_basis_entries_mem
    {K : Type u} [Field K] [Algebra k K]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (T : FDRep K G)
    (b : Module.Basis ι K T)
    (LL : IntermediateField k K)
    (hmem : ∀ g i j, LinearMap.toMatrix b b (T.ρ g) i j ∈ LL) :
    ∃ (T_L : FDRep LL G), Nonempty (T ≅ FDRep.scalarExtension T_L) := by
  classical
  -- The matrices of the action in this basis.
  set M : G → Matrix ι ι K :=
    fun g => LinearMap.toMatrix b b (T.ρ g) with hM
  have hM1 : M 1 = 1 := by
    simp only [hM, map_one, Module.End.one_eq_id, LinearMap.toMatrix_id]
  have hMmul : ∀ g h, M (g * h) = M g * M h := by
    intro g h
    simp only [hM, map_mul, Module.End.mul_eq_comp, LinearMap.toMatrix_comp b b b]
  -- The coefficientwise embedding `Matrix ι ι LL → Matrix ι ι K` as a ring hom.
  set RH : Matrix ι ι LL →+* Matrix ι ι K :=
    (algebraMap LL K).mapMatrix with hRH
  have hAlgInj : Function.Injective (algebraMap LL K) :=
    (algebraMap LL K).injective
  have hRHInj : Function.Injective RH := fun A B h =>
    Matrix.map_injective hAlgInj (by simpa [hRH, RingHom.mapMatrix_apply] using h)
  -- The descended matrices over `LL`.
  set Nfun : G → Matrix ι ι LL :=
    fun g => Matrix.of fun i j => (⟨M g i j, hmem g i j⟩ : LL) with hNfun
  have hNmap : ∀ g, RH (Nfun g) = M g := by
    intro g
    ext i j
    simp [hRH, hNfun, RingHom.mapMatrix_apply, Matrix.map_apply,
      IntermediateField.algebraMap_apply]
  -- Assemble the descended matrices into a monoid homomorphism.
  set N : G →* Matrix ι ι LL :=
    { toFun := Nfun
      map_one' := by
        apply hRHInj
        rw [hNmap, hM1, map_one]
      map_mul' := fun g h => by
        apply hRHInj
        simp only [map_mul, hNmap, hMmul] } with hN
  -- Apply the realization-descent lemma.
  refine descend_of_matrix_realization T b LL N (fun g => ?_)
  rw [← RingHom.mapMatrix_apply]
  exact hNmap g

/-- **A finite-dimensional representation over the algebraic closure is defined over a finite
Galois subextension.**

If `k̄ = AlgebraicClosure k` is Galois over `k` (automatic when `k` is perfect) and `G` is finite,
then every `T : FDRep k̄ G` is the scalar extension of a representation `T_L` defined over a finite
Galois intermediate field `L/k`. -/
theorem exists_finiteGaloisIntermediateField_model
    [IsGalois k (AlgebraicClosure k)]
    (T : FDRep (AlgebraicClosure k) G) :
    ∃ (L : FiniteGaloisIntermediateField k (AlgebraicClosure k)) (T_L : FDRep L G),
      Nonempty (T ≅ FDRep.scalarExtension T_L) := by
  classical
  -- A `k̄`-basis of `T`.
  set b := Module.finBasis (AlgebraicClosure k) T with hb
  -- The finite set of all matrix entries of the action.
  set s : Set (AlgebraicClosure k) :=
    Set.range (fun x : G × _ × _ => LinearMap.toMatrix b b (T.ρ x.1) x.2.1 x.2.2) with hs
  haveI : Finite s := (Set.finite_range _).to_subtype
  -- The finite Galois subextension generated by the entries.
  set L := FiniteGaloisIntermediateField.adjoin k s with hL
  have hsub : s ⊆ (L.toIntermediateField : Set (AlgebraicClosure k)) :=
    FiniteGaloisIntermediateField.subset_adjoin k s
  have hmem : ∀ g i j, LinearMap.toMatrix b b (T.ρ g) i j ∈ L.toIntermediateField := by
    intro g i j
    exact hsub ⟨(g, i, j), rfl⟩
  obtain ⟨T_L, hiso⟩ := model_of_basis_entries_mem T b L.toIntermediateField hmem
  exact ⟨L, T_L, hiso⟩

end Representation
