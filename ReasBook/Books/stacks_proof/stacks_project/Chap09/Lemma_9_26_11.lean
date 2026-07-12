import Mathlib
import StacksProject_2024.Chap09.Lemma_9_26_10

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open IntermediateField
open scoped algebraAdjoinAdjoin

attribute [local instance] MvPolynomial.algebraMvPolynomial

variable (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]

/- Domain-style sampling for Lemma 9.26.11:
- primary domain: finitely generated field extensions and their relative algebraic closures;
- sampled owner declarations:
  `Algebra.EssFiniteType`,
  `fg_top_iff`,
  `algebraicClosure`,
  `mem_algebraicClosure_iff`;
- owner abstraction: `Algebra.EssFiniteType k K` for finite generation, together with the
  canonical intermediate field `algebraicClosure k K`;
- primitive data: no new local data, since the theorem is about the existing owner object
  `algebraicClosure k K`;
- derived API: only the source-facing finite-dimensionality statement below.

Source/core/bridge triage:
- `source-facing`: Lemma 9.26.11 itself, asserting that the relative algebraic closure is finite
  over the base field for finitely generated extensions;
- `core/canonical`: the owner hypothesis `Algebra.EssFiniteType k K` and the canonical relative
  algebraic closure `algebraicClosure k K`;
- `bridge/view`: the identification of the textbook `FG` formulation with the owner hypothesis via
  `fg_top_iff`, already provided upstream.

The refined file keeps the theorem directly on `algebraicClosure k K`, without introducing any
parallel local wrapper for the same intermediate field, and reuses the upstream bridge from
`(⊤ : IntermediateField k K).FG` to `Algebra.EssFiniteType k K`. -/

/-- Helper for Lemma 9.26.11: a finitely generated field extension admits a finite
transcendence basis whose generated intermediate field has finite residual degree in `K`. -/
lemma exists_finTranscendenceBasis_finiteDimensional_over_adjoin
    [Algebra.EssFiniteType k K] :
    ∃ r, ∃ x : Fin r → K, IsTranscendenceBasis k x ∧
      FiniteDimensional (IntermediateField.adjoin k (Set.range x)) K := by
  classical
  obtain ⟨s, hs_fin, hs_top⟩ :=
    (IntermediateField.fg_def (S := (⊤ : IntermediateField k K))).mp
      (IntermediateField.fg_top k K)
  have hs_alg_field : Algebra.IsAlgebraic (IntermediateField.adjoin k s) K := by
    exact ⟨fun x ↦ by
      have hx_mem : x ∈ IntermediateField.adjoin k s := by
        simpa [hs_top] using (show x ∈ (⊤ : IntermediateField k K) from trivial)
      simpa using isAlgebraic_algebraMap (⟨x, hx_mem⟩ : IntermediateField.adjoin k s)⟩
  have hs_alg_ring : Algebra.IsAlgebraic (Algebra.adjoin k s) K := by
    exact
      (IntermediateField.isAlgebraic_adjoin_iff_top (F := k) (s := s)).mp hs_alg_field
  letI : Algebra.IsAlgebraic (Algebra.adjoin k s) K := hs_alg_ring
  obtain ⟨t, hts, ht⟩ := exists_isTranscendenceBasis_subset (R := k) s
  have ht_fin : t.Finite := hs_fin.subset hts
  letI : Fintype t := ht_fin.fintype
  let r := Fintype.card t
  let e : Fin r ≃ t := (Fintype.equivFin t).symm
  let x : Fin r → K := fun i ↦ (e i : K)
  have hx : IsTranscendenceBasis k x := by
    -- Reindex the finite transcendence basis by `Fin r` once and keep that spelling.
    simpa [x, Function.comp] using
      ((isTranscendenceBasis_equiv e (f := ((↑) : t → K))).2 ht)
  have hx_range : Set.range x = t := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).2
    · intro hy
      refine ⟨e.symm ⟨y, hy⟩, ?_⟩
      simp [x]
  have hx_alg : Algebra.IsAlgebraic (IntermediateField.adjoin k (Set.range x)) K := by
    simpa [hx_range] using hx.isAlgebraic_field
  letI : Algebra.IsAlgebraic (IntermediateField.adjoin k (Set.range x)) K := hx_alg
  letI : Algebra.EssFiniteType (IntermediateField.adjoin k (Set.range x)) K :=
    Algebra.EssFiniteType.of_comp k (IntermediateField.adjoin k (Set.range x)) K
  letI : Module.Finite (IntermediateField.adjoin k (Set.range x)) K :=
    Algebra.finite_of_essFiniteType_of_isAlgebraic
  refine ⟨r, x, hx, ?_⟩
  -- Finite generation plus algebraicity over the basis field upgrades to finite-dimensionality.
  infer_instance

/-- Helper for Lemma 9.26.11: constant polynomials attached to a `k`-basis of `L` remain
linearly independent over the polynomial ring in the transcendence variables. -/
lemma constantBasisLinearIndependentOverPolynomial
    {L : Type v} [Field L] [Algebra k L] {r : ℕ} {ι : Type*} (b : Module.Basis ι k L) :
    LinearIndependent (MvPolynomial (Fin r) k)
      (fun i ↦ (MvPolynomial.C (b i) : MvPolynomial (Fin r) L)) := by
  classical
  -- Apply coefficient extraction monomial-by-monomial to reduce polynomial relations to
  -- coefficient relations in the original `k`-basis of `L`.
  rw [linearIndependent_iff]
  intro l hl
  ext i d
  have hcoeff :
      Finsupp.linearCombination k b
        (l.mapRange (fun p ↦ MvPolynomial.coeff d p) (by simp)) = 0 := by
    have hcoeff := congrArg (MvPolynomial.coeff d) hl
    rw [Finsupp.linearCombination_apply] at hcoeff
    simp only [Finsupp.sum, Algebra.smul_def, mul_comm] at hcoeff
    rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_zero] at hcoeff
    simp only [MvPolynomial.coeff_C_mul] at hcoeff
    have hcoeff' : l.sum (fun a b_1 ↦ MvPolynomial.coeff d b_1 • b a) = 0 := by
      simpa [Finsupp.sum, Algebra.smul_def, mul_comm] using hcoeff
    simpa [Finsupp.linearCombination_apply, Finsupp.sum] using
      (show (l.mapRange (fun p ↦ MvPolynomial.coeff d p) (by simp)).sum (fun x a ↦ a • b x) = 0 by
        rw [Finsupp.sum_mapRange_index]
        · exact hcoeff'
        · intro a
          simp)
  have hzero := (linearIndependent_iff.mp b.linearIndependent)
    (l.mapRange (fun p ↦ MvPolynomial.coeff d p) (by simp)) hcoeff
  exact congrArg (fun f => f i) hzero

/-- Lemma 9.26.11: the basis field generated by a transcendence basis is linearly disjoint from a
finite algebraic coefficient field. This is the bridge used by the final finite-dimensionality
argument in the same file. -/
@[stacks 037J]
lemma basisFieldLinearDisjointOfAlgebraic
    {L : Type v} [Field L] [Algebra k L] [Algebra L K] [IsScalarTower k L K]
    [FiniteDimensional k L] [Algebra.IsAlgebraic k L]
    {r : ℕ} {x : Fin r → K} (hx : IsTranscendenceBasis k x) :
    (IntermediateField.adjoin k (Set.range x)).LinearDisjoint L := by
  classical
  let kX := FractionRing (MvPolynomial (Fin r) k)
  let LX := FractionRing (MvPolynomial (Fin r) L)
  letI : Algebra kX LX := FractionRing.liftAlgebra (MvPolynomial (Fin r) k) LX
  letI : Module kX LX := (FractionRing.liftAlgebra (MvPolynomial (Fin r) k) LX).toModule
  let b := Module.finBasis k L
  let hxL : IsTranscendenceBasis L x :=
    (Algebra.IsAlgebraic.isTranscendenceBasis_iff (R := k) (S := L) (x := x)).mp hx
  -- Route correction: transport only the basis-independence witness from `L(X)` into `K`,
  -- and compute the image of `k(X)` once at the end.
  have hconst : LinearIndependent kX (fun i ↦ algebraMap L LX (b i)) := by
    -- Localize the polynomial-basis independence from `k[X]` to the rational function field.
    simpa [kX, LX] using
      (LinearIndependent.localization_localization
        (R := MvPolynomial (Fin r) k)
        (A := MvPolynomial (Fin r) L)
        (Rₛ := kX)
        (Aₛ := LX)
        (S := nonZeroDivisors (MvPolynomial (Fin r) k))
        (v := fun i ↦ (MvPolynomial.C (b i) : MvPolynomial (Fin r) L))
        (constantBasisLinearIndependentOverPolynomial (k := k) (L := L) (r := r) b))
  let eL : LX →ₐ[L] ↥(IntermediateField.adjoin L (Set.range x)) :=
    hxL.1.aevalEquivField.toAlgHom
  let jLt : LX →ₐ[L] ↥(⊤ : IntermediateField L K) :=
    (IntermediateField.inclusion (show IntermediateField.adjoin L (Set.range x) ≤ ⊤ by
      exact le_top)).comp eL
  let jL : LX →ₐ[L] K := IntermediateField.topEquiv.toAlgHom.comp jLt
  let j : kX →ₐ[k] K :=
    (jL.restrictScalars k).comp (IsScalarTower.toAlgHom k kX LX)
  let ej := AlgEquiv.ofInjectiveField j
  have hfrac (q : MvPolynomial (Fin r) k) :
      (algebraMap kX LX) ((algebraMap (MvPolynomial (Fin r) k) kX) q) =
        algebraMap (MvPolynomial (Fin r) k) LX q := by
    -- Rewrite the `k(X) -> L(X)` map as the canonical fraction-ring lift on `k[X]`.
    rw [FractionRing.algebraMap_liftAlgebra (R := MvPolynomial (Fin r) k) (K := LX)]
    simpa [kX, LX] using
      (IsFractionRing.lift_algebraMap
        (A := MvPolynomial (Fin r) k)
        (K := kX)
        (L := LX)
        (g := algebraMap (MvPolynomial (Fin r) k) LX)
        (FaithfulSMul.algebraMap_injective (MvPolynomial (Fin r) k) LX) q)
  have hpolyMap :
      algebraMap (MvPolynomial (Fin r) k) LX =
        ((algebraMap (MvPolynomial (Fin r) L) LX).comp
          (MvPolynomial.map (algebraMap k L))) := by
    -- Identify the polynomial coefficient extension `k[X] -> L[X] -> L(X)`.
    apply MvPolynomial.ringHom_ext
    · intro a
      rfl
    · intro i
      rfl
  have hmapAeval (p : MvPolynomial (Fin r) k) :
      jL (((algebraMap (MvPolynomial (Fin r) L) LX).comp
          (MvPolynomial.map (algebraMap k L))) p) =
        (MvPolynomial.aeval x) p := by
    -- Push the coefficient-extended polynomial through the `L`-based `aevalEquivField`,
    -- then collapse the coefficient extension by the tower `k -> L -> K`.
    let q : MvPolynomial (Fin r) L := MvPolynomial.map (algebraMap k L) p
    have hq :
        (((algebraMap (MvPolynomial (Fin r) L) LX).comp
            (MvPolynomial.map (algebraMap k L))) p) =
          algebraMap (MvPolynomial (Fin r) L) LX q := by
      rfl
    rw [hq]
    calc
      jL ((algebraMap (MvPolynomial (Fin r) L) LX) q) = (MvPolynomial.aeval x) q := by
        -- Unfold the composite `L(X) -> K` only once, down to the computation rule for
        -- `aevalEquivField` on coefficient-extended polynomials.
        change ↑(hxL.1.aevalEquivField ((algebraMap (MvPolynomial (Fin r) L) LX) q)) =
          (MvPolynomial.aeval x) q
        exact AlgebraicIndependent.aevalEquivField_algebraMap_apply_coe (hx := hxL.1) (a := q)
      _ = (MvPolynomial.aeval x) p := by
        simpa [q] using (MvPolynomial.aeval_map_algebraMap (A := L) (x := x) p)
  have hj :
      RingHom.comp (j : kX →+* K) (algebraMap (MvPolynomial (Fin r) k) kX) =
        ((MvPolynomial.aeval x : MvPolynomial (Fin r) k →ₐ[k] K) :
          MvPolynomial (Fin r) k →+* K) := by
    -- Compare the two fraction-field lifts by reducing both to the same polynomial map.
    apply MvPolynomial.ringHom_ext
    · intro a
      calc
        j ((algebraMap (MvPolynomial (Fin r) k) kX) (MvPolynomial.C a))
            = jL ((algebraMap (MvPolynomial (Fin r) k) LX) (MvPolynomial.C a)) := by
                simp [j, hfrac (MvPolynomial.C a)]
        _ = jL (((algebraMap (MvPolynomial (Fin r) L) LX).comp
              (MvPolynomial.map (algebraMap k L))) (MvPolynomial.C a)) := by
                rw [hpolyMap]
        _ = (MvPolynomial.aeval x) (MvPolynomial.C a) := by
          exact hmapAeval (MvPolynomial.C a)
    · intro i
      calc
        j ((algebraMap (MvPolynomial (Fin r) k) kX) (MvPolynomial.X i))
            = jL ((algebraMap (MvPolynomial (Fin r) k) LX) (MvPolynomial.X i)) := by
                simp [j, hfrac (MvPolynomial.X i)]
        _ = jL (((algebraMap (MvPolynomial (Fin r) L) LX).comp
              (MvPolynomial.map (algebraMap k L))) (MvPolynomial.X i)) := by
                rw [hpolyMap]
        _ = (MvPolynomial.aeval x) (MvPolynomial.X i) := by
          exact hmapAeval (MvPolynomial.X i)
  have hjRange : j.fieldRange = IntermediateField.adjoin k (Set.range x) := by
    -- Compute the image of `k(X)` in `K` from the polynomial map `aeval x`.
    exact IsFractionRing.algHom_fieldRange_eq_of_comp_eq_of_range_eq
      (f := j) (g := MvPolynomial.aeval x) hj
      (Algebra.adjoin_range_eq_range_aeval k x).symm
  have hmap :
      LinearIndependent j.fieldRange
        (jL.toRingHom.toAddMonoidHom ∘ fun i ↦ algebraMap L LX (b i)) := by
    -- Change scalars from `k(X)` to the actual image field `j.fieldRange`.
    refine LinearIndependent.map_of_injective_injectiveₛ hconst ej.symm
      jL.toRingHom.toAddMonoidHom ej.symm.injective jL.injective ?_
    intro z m
    change jL ((algebraMap kX LX (ej.symm z)) * m) = z * jL m
    rw [map_mul]
    have hz : jL (algebraMap kX LX (ej.symm z)) = z := by
      change j (ej.symm z) = ↑z
      exact congrArg Subtype.val (ej.apply_symm_apply z)
    simpa [Algebra.smul_def, hz]
  have hK : LinearIndependent (IntermediateField.adjoin k (Set.range x)) (algebraMap L K ∘ b) := by
    -- The transported family is exactly the image of the original `k`-basis of `L` inside `K`.
    rw [← hjRange]
    convert hmap using 1
    ext i
    exact (jL.commutes (b i)).symm
  -- The basis criterion now closes linear disjointness over the actual basis field `k(x)`.
  exact IntermediateField.LinearDisjoint.of_basis_right' b hK

/-- Helper for Lemma 9.26.11: once the basis field is linearly disjoint from `L`, the standard
adjoin-rank formula bounds `[L : k]` by the residual degree over the basis field. -/
lemma finrankLeOfBasisFieldLinearDisjoint
    {L : Type v} [Field L] [Algebra k L] [Algebra L K] [IsScalarTower k L K]
    [FiniteDimensional k L] [Algebra.IsAlgebraic k L]
    {r : ℕ} {x : Fin r → K}
    [FiniteDimensional (IntermediateField.adjoin k (Set.range x)) K]
    (hld : (IntermediateField.adjoin k (Set.range x)).LinearDisjoint L) :
    Module.finrank k L ≤ Module.finrank (IntermediateField.adjoin k (Set.range x)) K := by
  let F := IntermediateField.adjoin k (Set.range x)
  let G : IntermediateField F K :=
    IntermediateField.extendScalars
      (show F ≤ (IntermediateField.adjoin L (F : Set K)).restrictScalars k from
        IntermediateField.subset_adjoin L (F : Set K))
  -- Convert linear disjointness into an exact rank computation for the adjoined coefficient field.
  have hG_rank : Module.rank F G = Module.rank k L := by
    simpa [F, G] using
      IntermediateField.LinearDisjoint.adjoin_rank_eq_rank_right_of_isAlgebraic_right
        (A := F) (E := K) (L := L) hld
  have hG_finrank : Module.finrank F G = Module.finrank k L := by
    apply Nat.cast_injective (R := Cardinal)
    rw [Module.finrank_eq_rank, Module.finrank_eq_rank]
    exact hG_rank
  -- The tower law then bounds the degree of `L / k` by the residual degree of `K / F`.
  have : FiniteDimensional G K := FiniteDimensional.right F G K
  have hmul : Module.finrank F G * Module.finrank G K = Module.finrank F K :=
    Module.finrank_mul_finrank F G K
  have hpos : 0 < Module.finrank G K := Module.finrank_pos
  have hle : Module.finrank F G ≤ Module.finrank F K := by
    rw [← hmul]
    exact Nat.le_mul_of_pos_right _ hpos
  simpa [F] using hG_finrank ▸ hle

/-- Helper for Lemma 9.26.11: after adjoining a finite transcendence basis, every finite
algebraic extension of `k` acting on `K` has degree bounded by the residual degree of `K` over the
basis field. -/
lemma finrank_algebraicField_le_finrank_over_basis
    {L : Type v} [Field L] [Algebra k L] [Algebra L K] [IsScalarTower k L K]
    [FiniteDimensional k L] [Algebra.IsAlgebraic k L]
    {r : ℕ} {x : Fin r → K} (hx : IsTranscendenceBasis k x)
    [FiniteDimensional (IntermediateField.adjoin k (Set.range x)) K] :
    Module.finrank k L ≤ Module.finrank (IntermediateField.adjoin k (Set.range x)) K := by
  -- Reduce the source statement to the single remaining linearly disjointness bridge.
  exact finrankLeOfBasisFieldLinearDisjoint
    (k := k) (K := K) (L := L) (x := x)
    (basisFieldLinearDisjointOfAlgebraic (k := k) (K := K) (L := L) hx)

/-- Final conclusion for Lemma 9.26.11: if `K/k` is a finitely generated field extension, then the
relative algebraic closure of `k` in `K` is finite over `k`. The source-facing theorem uses the
canonical owner `[Algebra.EssFiniteType k K]` for finite generation. -/
-- Proof sketch: choose a transcendence basis of `K/k`; then Lemma 9.26.10 identifies every finite
-- subextension of `algebraicClosure k K` with a finite extension of the corresponding rational
-- function field of uniformly bounded degree. This bounds the degrees of all finite intermediate
-- subextensions of `algebraicClosure k K / k`, from which finite-dimensionality follows.
lemma finiteDimensional_algebraicClosure [Algebra.EssFiniteType k K] :
    FiniteDimensional k (algebraicClosure k K) := by
  classical
  obtain ⟨r, x, hx, hfdK⟩ :=
    exists_finTranscendenceBasis_finiteDimensional_over_adjoin (k := k) (K := K)
  let F := IntermediateField.adjoin k (Set.range x)
  by_contra hnfd
  letI : Algebra.IsAlgebraic k ↥(algebraicClosure k K) := algebraicClosure.isAlgebraic k K
  obtain ⟨L0, hL0fd, hL0gt⟩ :=
    IntermediateField.exists_lt_finrank_of_infinite_dimensional
      (F := k) (E := ↥(algebraicClosure k K)) hnfd (Module.finrank F K)
  let f0 : ↥L0 →ₐ[k] ↥(⊤ : IntermediateField k ↥(algebraicClosure k K)) :=
    IntermediateField.inclusion (show L0 ≤ ⊤ by exact le_top)
  let f1 : ↥(⊤ : IntermediateField k ↥(algebraicClosure k K)) →ₐ[k] ↥(algebraicClosure k K) :=
    IntermediateField.topEquiv.toAlgHom
  let f2 : ↥(algebraicClosure k K) →ₐ[k] ↥(⊤ : IntermediateField k K) :=
    IntermediateField.inclusion (show algebraicClosure k K ≤ ⊤ by exact le_top)
  let f3 : ↥(⊤ : IntermediateField k K) →ₐ[k] K := IntermediateField.topEquiv.toAlgHom
  let f : ↥L0 →ₐ[k] K := f3.comp (f2.comp (f1.comp f0))
  letI : Algebra ↥L0 K := f.toAlgebra
  letI : IsScalarTower k ↥L0 K := by
    refine IsScalarTower.of_algebraMap_eq ?_
    intro a
    rfl
  letI : FiniteDimensional k ↥L0 := hL0fd
  have hbound :
      Module.finrank k ↥L0 ≤ Module.finrank F K := by
    -- Route correction: once the finite algebraic witness is viewed inside `K`,
    -- the source proof reduces to the single bounded-degree lemma above.
    simpa [F] using
      finrank_algebraicField_le_finrank_over_basis
        (k := k) (K := K) (L := ↥L0) (x := x) hx
  exact (not_lt_of_ge hbound) hL0gt

end
