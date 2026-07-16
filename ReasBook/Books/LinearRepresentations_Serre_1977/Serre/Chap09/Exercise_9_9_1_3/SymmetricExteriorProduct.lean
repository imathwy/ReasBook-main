import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import LinearRepresentations_Serre_1977.Serre.Chap09.Exercise_9_9_1_3.ExteriorDeterminants
import LinearRepresentations_Serre_1977.Serre.Chap09.Exercise_9_9_1_3.SymmetricBaseChangeFinrank
import LinearRepresentations_Serre_1977.Serre.Chap09.Exercise_9_9_1_3.CharacterSeriesDefs

open scoped Representation
open scoped TensorProduct

noncomputable section

universe u v w

namespace Representation

open PowerSeries

section

-- `SymmetricPower R ι M` (used here via `SymmetricPower k (Fin n) V`, `nthSymmetricPower`, and the
-- symmetric-power character series) forces the base field `k` and the index type `Fin n : Type 0`
-- to share a universe, so we pin `k : Type 0`.  Every consumer instantiates `k` at `Type 0`
-- (e.g. `AlgebraicClosure (ZMod p)`), so no needed generality is lost.
variable {k : Type} [Field k]
variable {G : Type u} [Monoid G]
variable {V : Type v}
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]

theorem geometric_mul_rescale_exterior_trace_series_eq_quotient
    (A : V →ₗ[k] V) {v : V} {μ : k} (hv : v ≠ 0) (hμ : A v = μ • v) :
    let L : Submodule k V := Submodule.span k ({v} : Set V)
    let hL : L ≤ L.comap A := span_singleton_le_comap_of_eigenvector (A := A) hμ
    PowerSeries.mk (fun n : ℕ ↦ μ ^ n) *
      PowerSeries.rescale (-1 : k)
        (PowerSeries.mk
          (fun n ↦ LinearMap.trace k (⋀[k]^n V) (exteriorPower.map n A))) =
      PowerSeries.rescale (-1 : k)
        (PowerSeries.mk
          (fun n ↦
            LinearMap.trace k (⋀[k]^n (V ⧸ L))
              (exteriorPower.map n (L.mapQ L A hL)))) := by
  dsimp
  -- First peel off the eigenline contribution from the exterior series.
  rw [rescale_exterior_trace_series_factor_span_singleton_mapQ (A := A) (hv := hv) (hμ := hμ)]
  -- Then cancel the linear factor with the geometric series coming from the eigenline.
  rw [← mul_assoc, geometric_series_mul_one_sub_C_mul_X, one_mul]

/-- Helper for Exercise 9-9.1-3: once the ambient and quotient symmetric-exterior product
identities are known, the already-proved exterior eigenline factorization determines the
corresponding symmetric factorization by uniqueness of inverses in the power-series ring. -/
theorem symmetric_trace_series_factor_of_product_identities
    (A : V →ₗ[k] V) {v : V} {μ : k} (hv : v ≠ 0) (hμ : A v = μ • v)
    (hprodA :
      PowerSeries.mk
          (fun n ↦
            LinearMap.trace k (SymmetricPower k (Fin n) V) (SymmetricPower.map n A)) *
        PowerSeries.rescale (-1 : k)
          (PowerSeries.mk
            (fun n ↦ LinearMap.trace k (⋀[k]^n V) (exteriorPower.map n A))) = 1)
    (hprodQ :
      let L : Submodule k V := Submodule.span k ({v} : Set V)
      let hL : L ≤ L.comap A := span_singleton_le_comap_of_eigenvector (A := A) hμ
      PowerSeries.mk
          (fun n ↦
            LinearMap.trace k (SymmetricPower k (Fin n) (V ⧸ L))
              (SymmetricPower.map n (L.mapQ L A hL))) *
        PowerSeries.rescale (-1 : k)
          (PowerSeries.mk
            (fun n ↦
              LinearMap.trace k (⋀[k]^n (V ⧸ L))
                (exteriorPower.map n (L.mapQ L A hL)))) = 1) :
    let L : Submodule k V := Submodule.span k ({v} : Set V)
    let hL : L ≤ L.comap A := span_singleton_le_comap_of_eigenvector (A := A) hμ
    PowerSeries.mk
        (fun n ↦
          LinearMap.trace k (SymmetricPower k (Fin n) V) (SymmetricPower.map n A)) =
      PowerSeries.mk (fun n : ℕ ↦ μ ^ n) *
        PowerSeries.mk
          (fun n ↦
            LinearMap.trace k (SymmetricPower k (Fin n) (V ⧸ L))
              (SymmetricPower.map n (L.mapQ L A hL))) := by
  dsimp at hprodQ ⊢
  let L : Submodule k V := Submodule.span k ({v} : Set V)
  let hL : L ≤ L.comap A := span_singleton_le_comap_of_eigenvector (A := A) hμ
  let B : V ⧸ L →ₗ[k] V ⧸ L := L.mapQ L A hL
  let geom : PowerSeries k := PowerSeries.mk fun n : ℕ ↦ μ ^ n
  let symmA : PowerSeries k :=
    PowerSeries.mk fun n ↦
      LinearMap.trace k (SymmetricPower k (Fin n) V) (SymmetricPower.map n A)
  let symmQ : PowerSeries k :=
    PowerSeries.mk fun n ↦
      LinearMap.trace k (SymmetricPower k (Fin n) (V ⧸ L)) (SymmetricPower.map n B)
  let extA : PowerSeries k :=
    PowerSeries.rescale (-1 : k)
      (PowerSeries.mk fun n ↦ LinearMap.trace k (⋀[k]^n V) (exteriorPower.map n A))
  let extQ : PowerSeries k :=
    PowerSeries.rescale (-1 : k)
      (PowerSeries.mk fun n ↦
        LinearMap.trace k (⋀[k]^n (V ⧸ L)) (exteriorPower.map n B))
  have hgeom : geom * extA = extQ := by
    -- The exterior side already splits into the eigenline factor and the quotient factor.
    simpa [geom, extA, extQ, B, L, hL] using
      geometric_mul_rescale_exterior_trace_series_eq_quotient
        (A := A) (v := v) (μ := μ) (hv := hv) (hμ := hμ)
  have hconst : PowerSeries.constantCoeff extA = 1 := by
    -- The exterior series has constant coefficient `1`, so it has a unique inverse.
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [extA, trace_exteriorPower_map_zero]
  have hne : PowerSeries.constantCoeff extA ≠ 0 := by
    rw [hconst]
    simp
  have hcandidate : (geom * symmQ) * extA = 1 := by
    -- The quotient product identity and the exterior factorization make `geom * symmQ`
    -- another inverse of the ambient exterior series.
    calc
      (geom * symmQ) * extA = symmQ * (geom * extA) := by
        rw [mul_assoc, mul_left_comm geom symmQ, ← mul_assoc]
      _ = symmQ * extQ := by rw [hgeom]
      _ = 1 := by simpa [symmQ, extQ, B, L, hL] using hprodQ
  have hsymmA : symmA = extA⁻¹ := by
    -- The ambient product identity identifies the symmetric series as the inverse of `extA`.
    exact (PowerSeries.eq_inv_iff_mul_eq_one hne).2 (by simpa [symmA, extA] using hprodA)
  have hsymmCandidate : geom * symmQ = extA⁻¹ := by
    exact (PowerSeries.eq_inv_iff_mul_eq_one hne).2 hcandidate
  -- Two inverses of the same power series with unit constant term must coincide.
  simpa [symmA, geom, symmQ, B, L, hL] using hsymmA.trans hsymmCandidate.symm

/-- Helper for Exercise 9-9.1-3: once the symmetric trace series factors through an invariant
eigenline and the quotient, the full symmetric-exterior product reduces to the same product on the
quotient. -/
theorem symmetric_exterior_product_eq_quotient_of_factor
    (A : V →ₗ[k] V) {v : V} {μ : k} (hv : v ≠ 0) (hμ : A v = μ • v)
    (hsymm :
      let L : Submodule k V := Submodule.span k ({v} : Set V)
      let hL : L ≤ L.comap A := span_singleton_le_comap_of_eigenvector (A := A) hμ
      PowerSeries.mk
          (fun n ↦
            LinearMap.trace k (SymmetricPower k (Fin n) V) (SymmetricPower.map n A)) =
        PowerSeries.mk (fun n : ℕ ↦ μ ^ n) *
          PowerSeries.mk
            (fun n ↦
              LinearMap.trace k (SymmetricPower k (Fin n) (V ⧸ L))
                (SymmetricPower.map n (L.mapQ L A hL)))) :
    let L : Submodule k V := Submodule.span k ({v} : Set V)
    let hL : L ≤ L.comap A := span_singleton_le_comap_of_eigenvector (A := A) hμ
    PowerSeries.mk
        (fun n ↦
          LinearMap.trace k (SymmetricPower k (Fin n) V) (SymmetricPower.map n A)) *
      PowerSeries.rescale (-1 : k)
        (PowerSeries.mk
          (fun n ↦ LinearMap.trace k (⋀[k]^n V) (exteriorPower.map n A))) =
      PowerSeries.mk
          (fun n ↦
            LinearMap.trace k (SymmetricPower k (Fin n) (V ⧸ L))
              (SymmetricPower.map n (L.mapQ L A hL))) *
        PowerSeries.rescale (-1 : k)
          (PowerSeries.mk
            (fun n ↦
              LinearMap.trace k (⋀[k]^n (V ⧸ L))
                (exteriorPower.map n (L.mapQ L A hL)))) := by
  dsimp at hsymm ⊢
  let L : Submodule k V := Submodule.span k ({v} : Set V)
  let hL : L ≤ L.comap A := span_singleton_le_comap_of_eigenvector (A := A) hμ
  let B : V ⧸ L →ₗ[k] V ⧸ L := L.mapQ L A hL
  let geom : PowerSeries k := PowerSeries.mk fun n : ℕ ↦ μ ^ n
  let symmA : PowerSeries k :=
    PowerSeries.mk fun n ↦
      LinearMap.trace k (SymmetricPower k (Fin n) V) (SymmetricPower.map n A)
  let symmQ : PowerSeries k :=
    PowerSeries.mk fun n ↦
      LinearMap.trace k (SymmetricPower k (Fin n) (V ⧸ L)) (SymmetricPower.map n B)
  let extA : PowerSeries k :=
    PowerSeries.rescale (-1 : k)
      (PowerSeries.mk fun n ↦ LinearMap.trace k (⋀[k]^n V) (exteriorPower.map n A))
  let extQ : PowerSeries k :=
    PowerSeries.rescale (-1 : k)
      (PowerSeries.mk fun n ↦
        LinearMap.trace k (⋀[k]^n (V ⧸ L)) (exteriorPower.map n B))
  have hgeom : geom * extA = extQ := by
    -- The exterior side already factors cleanly through the eigenline and quotient.
    simpa [geom, extA, extQ, B, L, hL] using
      geometric_mul_rescale_exterior_trace_series_eq_quotient
        (A := A) (v := v) (μ := μ) (hv := hv) (hμ := hμ)
  have hsymm' : symmA = geom * symmQ := by
    -- This is the assumed symmetric analogue of the exterior eigenline factorization.
    simpa [symmA, geom, symmQ, B, L, hL] using hsymm
  -- Reassociate so the geometric factor cancels against the exterior contribution.
  have hstep : symmA * extA = symmQ * extQ := by
    calc
      symmA * extA = (geom * symmQ) * extA := by rw [hsymm']
      _ = symmQ * (geom * extA) := by
            rw [mul_assoc, mul_left_comm geom symmQ, ← mul_assoc]
      _ = symmQ * extQ := by rw [hgeom]
  simpa [symmA, symmQ, extA, extQ, B, L, hL] using hstep

/-- Helper for Exercise 9-9.1-3: quotienting by the line spanned by a nonzero vector strictly
lowers the ambient dimension. -/
theorem finrank_quotient_span_singleton_lt
    {v : V} (hv : v ≠ 0) :
    Module.finrank k (V ⧸ Submodule.span k ({v} : Set V)) < Module.finrank k V := by
  have hdim :
      Module.finrank k (V ⧸ Submodule.span k ({v} : Set V)) +
        Module.finrank k (Submodule.span k ({v} : Set V)) =
      Module.finrank k V := by
    -- The quotient-line decomposition is the standard rank formula for a submodule.
    simpa using
      (Submodule.finrank_quotient_add_finrank
        (R := k) (M := V) (Submodule.span k ({v} : Set V)))
  have hline : Module.finrank k (Submodule.span k ({v} : Set V)) = 1 := by
    -- A nonzero vector spans a one-dimensional line.
    simpa using finrank_span_singleton hv
  -- Rewriting the rank formula as `finrank quotient + 1 = finrank ambient` gives strict descent.
  omega

/-- Helper for Exercise 9-9.1-3: in the induction step, the missing symmetric eigenline
factorization and the quotient identity already suffice to close the target product identity. -/
theorem symmetric_exterior_trace_series_mul_rescale_neg_eq_one_of_factor
    (A : V →ₗ[k] V) {v : V} {μ : k} (hv : v ≠ 0) (hμ : A v = μ • v)
    (hsymm :
      let L : Submodule k V := Submodule.span k ({v} : Set V)
      let hL : L ≤ L.comap A := span_singleton_le_comap_of_eigenvector (A := A) hμ
      PowerSeries.mk
          (fun n ↦
            LinearMap.trace k (SymmetricPower k (Fin n) V) (SymmetricPower.map n A)) =
        PowerSeries.mk (fun n : ℕ ↦ μ ^ n) *
          PowerSeries.mk
            (fun n ↦
              LinearMap.trace k (SymmetricPower k (Fin n) (V ⧸ L))
                (SymmetricPower.map n (L.mapQ L A hL))))
    (hquot :
      let L : Submodule k V := Submodule.span k ({v} : Set V)
      let hL : L ≤ L.comap A := span_singleton_le_comap_of_eigenvector (A := A) hμ
      PowerSeries.mk
          (fun n ↦
            LinearMap.trace k (SymmetricPower k (Fin n) (V ⧸ L))
              (SymmetricPower.map n (L.mapQ L A hL))) *
        PowerSeries.rescale (-1 : k)
          (PowerSeries.mk
            (fun n ↦
              LinearMap.trace k (⋀[k]^n (V ⧸ L))
                (exteriorPower.map n (L.mapQ L A hL)))) = 1) :
    PowerSeries.mk
        (fun n ↦
          LinearMap.trace k (SymmetricPower k (Fin n) V) (SymmetricPower.map n A)) *
      PowerSeries.rescale (-1 : k)
        (PowerSeries.mk
          (fun n ↦ LinearMap.trace k (⋀[k]^n V) (exteriorPower.map n A))) = 1 := by
  have hreduce :=
    symmetric_exterior_product_eq_quotient_of_factor
      (A := A) (v := v) (μ := μ) (hv := hv) (hμ := hμ) hsymm
  -- The previous helper reduces the ambient product to the quotient product, so the induction
  -- hypothesis can be applied verbatim once the symmetric factorization is available.
  dsimp at hreduce hquot ⊢
  rw [hreduce, hquot]

/-- Helper for Exercise 9-9.1-3: for `Fin 0`, the symmetric-tensor permutation relation adds no
new identifications, so related tensors are already equal. -/
private theorem symm_zero_rel_eq
    {x y : PiTensorProduct k (fun _ : Fin 0 ↦ V)}
    (h : addConGen (SymmetricPower.Rel k (Fin 0) V) x y) :
    x = y := by
  induction h with
  | of x y h =>
      cases h with
      | perm e f =>
          have hfun : f = fun i : Fin 0 ↦ f (e i) := by
            funext i
            exact Fin.elim0 i
          exact congrArg (PiTensorProduct.tprod k) hfun
  | refl =>
      rfl
  | symm _ ih =>
      exact ih.symm
  | trans _ _ ih₁ ih₂ =>
      exact ih₁.trans ih₂
  | add _ _ ih₁ ih₂ =>
      exact congrArg₂ (· + ·) ih₁ ih₂

/-- Helper for Exercise 9-9.1-3: the `0`th symmetric power is one-dimensional. -/
theorem finrank_symmetricPower_zero :
    Module.finrank k (SymmetricPower k (Fin 0) V) = 1 := by
  let eTensor : PiTensorProduct k (fun _ : Fin 0 ↦ V) ≃ₗ[k] k :=
    PiTensorProduct.isEmptyEquiv (R := k) (ι := Fin 0) (s := fun _ : Fin 0 ↦ V)
  have hmk_injective : Function.Injective (SymmetricPower.mk k (Fin 0) V) := by
    intro x y hxy
    change
      ((x : (addConGen (SymmetricPower.Rel k (Fin 0) V)).Quotient) =
        (y : (addConGen (SymmetricPower.Rel k (Fin 0) V)).Quotient)) at hxy
    -- In degree `0`, the permutation relation is trivial because `Fin 0` has no indices.
    refine symm_zero_rel_eq (((addConGen (SymmetricPower.Rel k (Fin 0) V)).eq).1 hxy)
  let eSymm : PiTensorProduct k (fun _ : Fin 0 ↦ V) ≃ₗ[k] SymmetricPower k (Fin 0) V :=
    LinearEquiv.ofBijective (SymmetricPower.mk k (Fin 0) V)
      ⟨hmk_injective, by
        -- The quotient map onto the symmetric power is always surjective.
        simpa [LinearMap.range_eq_top] using
          (SymmetricPower.range_mk (R := k) (ι := Fin 0) (M := V))⟩
  -- Route correction: identify `Sym^0(V)` with the empty tensor power first, then use the
  -- canonical empty-index tensor-power equivalence with the scalar owner `k`.
  simpa using (eSymm.symm.trans eTensor).finrank_eq

/-- Helper for Exercise 9-9.1-3: every symmetric power has the expected multichoose dimension; the
degree-`0` case is the scalar owner, and positive degrees were reduced in the imported finrank file
to the coordinate counting model. -/
private theorem finrank_symmetricPower_eq_multichoose_all
    (n : ℕ) :
    Module.finrank k (SymmetricPower k (Fin n) V) =
      (Module.finrank k V).multichoose n := by
  cases n with
  | zero =>
      -- Degree `0` is the scalar owner, so its finrank is `1 = multichoose(dim V, 0)`.
      simpa using (finrank_symmetricPower_zero (k := k) (V := V))
  | succ n =>
      -- Positive degrees are already counted in the imported coordinate finrank package.
      simpa [Nat.succ_eq_add_one] using
        (Representation.finrank_symmetricPower_eq_multichoose
          (k := k) (V := V) n)

/-- Helper for Exercise 9-9.1-3: every endomorphism acts trivially on the `0`th symmetric
power because there are no tensor factors to move. -/
theorem symmetricPower_map_zero_eq_id
    (A : V →ₗ[k] V) :
    SymmetricPower.map 0 A =
      (LinearMap.id : SymmetricPower k (Fin 0) V →ₗ[k] SymmetricPower k (Fin 0) V) := by
  let eTensor : PiTensorProduct k (fun _ : Fin 0 ↦ V) ≃ₗ[k] k :=
    PiTensorProduct.isEmptyEquiv (R := k) (ι := Fin 0) (s := fun _ : Fin 0 ↦ V)
  have hmk_injective : Function.Injective (SymmetricPower.mk k (Fin 0) V) := by
    intro x y hxy
    change
      ((x : (addConGen (SymmetricPower.Rel k (Fin 0) V)).Quotient) =
        (y : (addConGen (SymmetricPower.Rel k (Fin 0) V)).Quotient)) at hxy
    -- In degree `0`, the quotient relation is trivial because `Fin 0` has no permutations to add.
    refine symm_zero_rel_eq (((addConGen (SymmetricPower.Rel k (Fin 0) V)).eq).1 hxy)
  let eSymm : PiTensorProduct k (fun _ : Fin 0 ↦ V) ≃ₗ[k] SymmetricPower k (Fin 0) V :=
    LinearEquiv.ofBijective (SymmetricPower.mk k (Fin 0) V)
      ⟨hmk_injective, by
        -- The quotient map onto the symmetric power is always surjective.
        simpa [LinearMap.range_eq_top] using
          (SymmetricPower.range_mk (R := k) (ι := Fin 0) (M := V))⟩
  let e : SymmetricPower k (Fin 0) V ≃ₗ[k] k := eSymm.symm.trans eTensor
  have hone :
      e.symm (1 : k) =
        SymmetricPower.mk k (Fin 0) V
          (PiTensorProduct.tprod k (fun i : Fin 0 ↦ Fin.elim0 i)) := by
    -- The scalar `1` corresponds to the unique empty tensor generator.
    have honeTensor :
        eTensor.symm (1 : k) =
          PiTensorProduct.tprod k (fun i : Fin 0 ↦ Fin.elim0 i) := by
      apply eTensor.injective
      simp [eTensor]
    change eSymm (eTensor.symm (1 : k)) =
      SymmetricPower.mk k (Fin 0) V
        (PiTensorProduct.tprod k (fun i : Fin 0 ↦ Fin.elim0 i))
    rw [honeTensor]
    rfl
  ext x
  apply e.injective
  let c : k := e x
  have hx : x = e.symm c := by
    simp [e, c]
  have hs :
      e.symm c = c • e.symm (1 : k) := by
    -- A one-dimensional vector space is generated by the image of `1`.
    calc
      e.symm c = e.symm (c • (1 : k)) := by simp
      _ = c • e.symm (1 : k) := by simpa using e.symm.map_smul c (1 : k)
  have hgen :
      SymmetricPower.map 0 A
        (SymmetricPower.mk k (Fin 0) V
          (PiTensorProduct.tprod k (fun i : Fin 0 ↦ Fin.elim0 i))) =
      SymmetricPower.mk k (Fin 0) V
        (PiTensorProduct.tprod k (fun i : Fin 0 ↦ Fin.elim0 i)) := by
    -- On the unique empty tensor generator, `SymmetricPower.map` has no factors to modify.
    change
      SymmetricPower.mk k (Fin 0) V
        (PiTensorProduct.map (fun _ : Fin 0 ↦ A)
          (PiTensorProduct.tprod k (fun i : Fin 0 ↦ Fin.elim0 i))) =
        SymmetricPower.mk k (Fin 0) V
          (PiTensorProduct.tprod k (fun i : Fin 0 ↦ Fin.elim0 i))
    rw [PiTensorProduct.map_tprod]
    congr
    funext i
    exact Fin.elim0 i
  have hbase : e (SymmetricPower.map 0 A (e.symm (1 : k))) = 1 := by
    -- The empty symmetric tensor is fixed because `SymmetricPower.map` has no tensor factors to
    -- apply `A` to in degree `0`.
    rw [hone]
    rw [hgen]
    simp [e, eSymm, eTensor]
  -- After transporting to the scalar owner `k`, both sides act as the identity on the generator.
  calc
    e (SymmetricPower.map 0 A x) = e (SymmetricPower.map 0 A (e.symm c)) := by rw [hx]
    _ = e (SymmetricPower.map 0 A (c • e.symm (1 : k))) := by rw [hs]
    _ = c • e (SymmetricPower.map 0 A (e.symm (1 : k))) := by simp [e]
    _ = c := by rw [hbase]; simp
    _ = e x := by simp [c]

/-- Helper for Exercise 9-9.1-3: the `0`th symmetric power contributes trace `1`, independently
of the chosen endomorphism. -/
theorem trace_symmetricPower_map_zero
    (A : V →ₗ[k] V) :
    LinearMap.trace k (SymmetricPower k (Fin 0) V) (SymmetricPower.map 0 A) = 1 := by
  -- Once the degree-`0` action is identified with the identity, the trace is the dimension `1`.
  rw [symmetricPower_map_zero_eq_id (A := A), LinearMap.trace_id]
  simpa [finrank_symmetricPower_zero]

/-- Helper for Exercise 9-9.1-3: if `V` has dimension `0`, then every positive-degree symmetric
power is zero-dimensional, so the symmetric trace series is just `1`. -/
theorem symmetric_trace_series_eq_one_of_finrank_zero
    (A : V →ₗ[k] V) (hV : Module.finrank k V = 0) :
    PowerSeries.mk
        (fun n ↦
          LinearMap.trace k (SymmetricPower k (Fin n) V) (SymmetricPower.map n A)) = 1 := by
  have hA0 : A = 0 := by
    letI : Subsingleton V := Module.finrank_zero_iff.mp hV
    exact Subsingleton.elim _ _
  ext n
  cases n with
  | zero =>
      -- Degree `0` is the scalar owner, so the trace is `1`.
      rw [PowerSeries.coeff_mk, PowerSeries.coeff_one, hA0]
      simpa [finrank_symmetricPower_zero (k := k) (V := V)] using
        (trace_symmetricPower_map_smul_id (V := V) (n := 0) (μ := (0 : k)))
  | succ n =>
      -- Positive degrees see the zero endomorphism, so the trace vanishes.
      rw [PowerSeries.coeff_mk, PowerSeries.coeff_one, hA0]
      simpa using
        (trace_symmetricPower_map_smul_id (V := V) (n := n + 1) (μ := (0 : k)))

/-- Helper for Exercise 9-9.1-3: if `V` has dimension `0`, then the rescaled exterior trace
series is also equal to `1`. -/
theorem rescale_exterior_trace_series_eq_one_of_finrank_zero
    (A : V →ₗ[k] V) (hV : Module.finrank k V = 0) :
    PowerSeries.rescale (-1 : k)
      (PowerSeries.mk
        (fun n ↦ LinearMap.trace k (⋀[k]^n V) (exteriorPower.map n A))) = 1 := by
  ext n
  cases n with
  | zero =>
      -- Degree `0` is again the scalar owner.
      simp [trace_exteriorPower_map_zero]
  | succ n =>
      -- Positive exterior powers vanish because the ambient space has dimension `0`.
      have hlt : Module.finrank k V < n + 1 := by
        omega
      rw [PowerSeries.coeff_rescale, PowerSeries.coeff_mk]
      simp [trace_exteriorPower_map_eq_zero_of_finrank_lt (A := A) hlt]

/-- Helper for Exercise 9-9.1-3: the zero-dimensional case of the symmetric-exterior product
identity is coefficientwise trivial. -/
theorem symmetric_exterior_trace_series_mul_rescale_neg_eq_one_zero_finrank
    (A : V →ₗ[k] V) (hV : Module.finrank k V = 0) :
    PowerSeries.mk
        (fun n ↦
          LinearMap.trace k (SymmetricPower k (Fin n) V) (SymmetricPower.map n A)) *
      PowerSeries.rescale (-1 : k)
        (PowerSeries.mk
          (fun n ↦ LinearMap.trace k (⋀[k]^n V) (exteriorPower.map n A))) = 1 := by
  -- In dimension `0`, both generating series collapse to `1`.
  rw [symmetric_trace_series_eq_one_of_finrank_zero (A := A) hV,
    rescale_exterior_trace_series_eq_one_of_finrank_zero (A := A) hV, one_mul]

/-- Helper for Exercise 9-9.1-3: after choosing a nonzero eigenvector, the symmetric trace series
factors through the corresponding eigenline and quotient. -/
theorem symmetric_trace_series_factor_of_coefficients
    (A : V →ₗ[k] V) {v : V} {μ : k} (hμ : A v = μ • v)
    (hcoeff :
      let L : Submodule k V := Submodule.span k ({v} : Set V)
      let hL : L ≤ L.comap A := span_singleton_le_comap_of_eigenvector (A := A) hμ
      ∀ n : ℕ,
        LinearMap.trace k (SymmetricPower k (Fin n) V) (SymmetricPower.map n A) =
          Finset.sum (Finset.antidiagonal n) fun p ↦
            (μ ^ p.1) *
              LinearMap.trace k (SymmetricPower k (Fin p.2) (V ⧸ L))
                (SymmetricPower.map p.2 (L.mapQ L A hL))) :
    let L : Submodule k V := Submodule.span k ({v} : Set V)
    let hL : L ≤ L.comap A := span_singleton_le_comap_of_eigenvector (A := A) hμ
    PowerSeries.mk
        (fun n ↦
          LinearMap.trace k (SymmetricPower k (Fin n) V) (SymmetricPower.map n A)) =
      PowerSeries.mk (fun n : ℕ ↦ μ ^ n) *
        PowerSeries.mk
          (fun n ↦
            LinearMap.trace k (SymmetricPower k (Fin n) (V ⧸ L))
              (SymmetricPower.map n (L.mapQ L A hL))) := by
  dsimp at hcoeff ⊢
  let L : Submodule k V := Submodule.span k ({v} : Set V)
  let hL : L ≤ L.comap A := span_singleton_le_comap_of_eigenvector (A := A) hμ
  let B : V ⧸ L →ₗ[k] V ⧸ L := L.mapQ L A hL
  ext n
  -- Compare degree `n` coefficients; multiplication of power series is exactly the
  -- antidiagonal convolution appearing in the source proof.
  simpa [PowerSeries.coeff_mul, B, L, hL] using hcoeff n

/-- Helper for Exercise 9-9.1-3: the eigenline-plus-quotient trace decomposition is immediate in
degree `0`, because the only antidiagonal term is `(0, 0)` and both `0`th symmetric traces are
`1`. -/
theorem trace_symmetricPower_map_eq_sum_span_singleton_mapQ_coeff_zero
    (A : V →ₗ[k] V) {v : V} {μ : k} (hμ : A v = μ • v) :
    let L : Submodule k V := Submodule.span k ({v} : Set V)
    let hL : L ≤ L.comap A := span_singleton_le_comap_of_eigenvector (A := A) hμ
    LinearMap.trace k (SymmetricPower k (Fin 0) V) (SymmetricPower.map 0 A) =
      Finset.sum (Finset.antidiagonal 0) fun p ↦
        (μ ^ p.1) *
          LinearMap.trace k (SymmetricPower k (Fin p.2) (V ⧸ L))
            (SymmetricPower.map p.2 (L.mapQ L A hL)) := by
  dsimp
  -- In degree `0`, the source filtration has a single graded piece, so the coefficient formula
  -- is just `1 = 1`.
  simp [trace_symmetricPower_map_zero]

/-- Helper for Exercise 9-9.1-3: the `Fin.cases` description of a function on `Fin (n + 1)`
agrees with the corresponding `Fin.cons` presentation. -/
private theorem fin_cases_eq_fin_cons
    (n : ℕ) (v : V) (f : Fin n → V) :
    (Fin.cases v f : Fin (n + 1) → V) = Fin.cons v f := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    rfl

/-- Helper for Exercise 9-9.1-3: scaling the distinguished left factor of a symmetric pure tensor
scales the whole symmetric tensor by the same scalar. -/
private theorem symmetricPower_tprod_cons_smul
    (n : ℕ) (μ : k) (v : V) (f : Fin n → V) :
    SymmetricPower.tprod k (ι := Fin (n + 1)) (M := V) (Fin.cons (μ • v) f) =
      μ • SymmetricPower.tprod k (ι := Fin (n + 1)) (M := V) (Fin.cons v f) := by
  -- Pull the scalar out of the distinguished coordinate by multilinearity of `SymmetricPower.tprod`.
  simpa [fin_cases_eq_fin_cons (V := V) n v f] using
    (SymmetricPower.tprod k (ι := Fin (n + 1)) (M := V)).map_update_smul (Fin.cons v f) 0 μ v

/-- Helper for Exercise 9-9.1-3: fixing a distinguished left factor `v` gives a linear map from
`Sym^n(V)`-generators to `Sym^(n+1)(V)`-generators. -/
private def symmetricPower_insert_left_tensor
    (n : ℕ) (v : V) :
    PiTensorProduct k (fun _ : Fin n ↦ V) →ₗ[k] SymmetricPower k (Fin (n + 1)) V :=
  PiTensorProduct.lift
    ((SymmetricPower.tprod k (ι := Fin (n + 1)) (M := V)).curryLeft v)

/-- Helper for Exercise 9-9.1-3: a permutation of the tail coordinates extends to a permutation of
`Fin (n + 1)` fixing the distinguished left slot. -/
private def symmetricPower_insert_left_perm
    (n : ℕ) (e : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) where
  toFun i := Fin.cases 0 (fun j => (e j).succ) i
  invFun i := Fin.cases 0 (fun j => (e.symm j).succ) i
  left_inv i := by
    -- The extended permutation fixes `0` and inverts `e` on the tail coordinates.
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro j
      simp
  right_inv i := by
    -- The same description proves the right inverse identity coordinatewise.
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro j
      simp

/-- Helper for Exercise 9-9.1-3: adjoining a distinguished left factor `v` respects the symmetric
relations on the remaining tensor factors, so it descends to symmetric powers. -/
private theorem symmetricPower_insert_left_tensor_wellDefined
    (n : ℕ) (v : V) {x y : PiTensorProduct k (fun _ : Fin n ↦ V)}
    (h : addConGen (SymmetricPower.Rel k (Fin n) V) x y) :
    symmetricPower_insert_left_tensor (k := k) n v x =
      symmetricPower_insert_left_tensor (k := k) n v y := by
  induction h with
  | of x y h =>
      cases h with
      | perm e f =>
          have hperm :=
            SymmetricPower.tprod_equiv (R := k) (ι := Fin (n + 1)) (M := V)
              (symmetricPower_insert_left_perm n e) (Fin.cases v f)
          have htail :
              (fun i : Fin (n + 1) =>
                Fin.cases v f (symmetricPower_insert_left_perm n e i)) =
                Fin.cons v (fun i : Fin n => f (e i)) := by
            -- On the tail, the extended permutation acts by `e`; at `0` it fixes `v`.
            funext i
            refine Fin.cases ?_ ?_ i
            · rfl
            · intro j
              simp [symmetricPower_insert_left_perm]
          -- Reduce the quotient compatibility to the symmetry relation in `Sym^(n+1)(V)`.
          calc
            symmetricPower_insert_left_tensor (k := k) n v (PiTensorProduct.tprod k f) =
                SymmetricPower.tprod k (ι := Fin (n + 1)) (M := V) (Fin.cons v f) := by
                  simp [symmetricPower_insert_left_tensor, MultilinearMap.curryLeft_apply]
            _ = SymmetricPower.tprod k (ι := Fin (n + 1)) (M := V) (Fin.cases v f) := by
                  rw [fin_cases_eq_fin_cons (V := V) n v f]
            _ = SymmetricPower.tprod k (ι := Fin (n + 1)) (M := V)
                  (fun i : Fin (n + 1) =>
                    Fin.cases v f (symmetricPower_insert_left_perm n e i)) := hperm.symm
            _ = SymmetricPower.tprod k (ι := Fin (n + 1)) (M := V)
                  (Fin.cons v fun i => f (e i)) := by
                    rw [htail]
            _ = symmetricPower_insert_left_tensor (k := k) n v
                  (PiTensorProduct.tprod k fun i => f (e i)) := by
                    simp [symmetricPower_insert_left_tensor, MultilinearMap.curryLeft_apply]
  | refl =>
      rfl
  | symm _ ih =>
      simpa using ih.symm
  | trans _ _ ih₁ ih₂ =>
      exact ih₁.trans ih₂
  | add _ _ ih₁ ih₂ =>
      simpa using congrArg₂ (· + ·) ih₁ ih₂

/-- Helper for Exercise 9-9.1-3: the distinguished-factor insertion descends from tensor powers to
the symmetric quotient. -/
private def symmetricPower_insert_left_fun
    (n : ℕ) (v : V) :
    SymmetricPower k (Fin n) V → SymmetricPower k (Fin (n + 1)) V :=
  Quotient.lift (symmetricPower_insert_left_tensor (k := k) n v)
    (fun _ _ h ↦ symmetricPower_insert_left_tensor_wellDefined (k := k) n v h)

/-- Helper for Exercise 9-9.1-3: the descended distinguished-factor insertion is additive. -/
private theorem symmetricPower_insert_left_fun_add
    (n : ℕ) (v : V) (x y : SymmetricPower k (Fin n) V) :
    symmetricPower_insert_left_fun (k := k) n v (x + y) =
      symmetricPower_insert_left_fun (k := k) n v x +
        symmetricPower_insert_left_fun (k := k) n v y := by
  -- After returning to tensor representatives, additivity is exactly `LinearMap.map_add`.
  refine AddCon.induction_on₂ x y ?_
  intro x y
  change symmetricPower_insert_left_tensor (k := k) n v (x + y) = _
  -- On quotient representatives, `Quotient.lift` reduces back to the tensor-level map.
  rw [LinearMap.map_add]
  rfl

/-- Helper for Exercise 9-9.1-3: the descended distinguished-factor insertion is `k`-linear. -/
private theorem symmetricPower_insert_left_fun_smul
    (n : ℕ) (v : V) (a : k) (x : SymmetricPower k (Fin n) V) :
    symmetricPower_insert_left_fun (k := k) n v (a • x) =
      a • symmetricPower_insert_left_fun (k := k) n v x := by
  -- After returning to tensor representatives, scalar compatibility is `LinearMap.map_smul`.
  refine AddCon.induction_on x ?_
  intro x
  change symmetricPower_insert_left_tensor (k := k) n v (a • x) = _
  -- On quotient representatives, `Quotient.lift` again evaluates to the tensor-level map.
  rw [LinearMap.map_smul]
  rfl

/-- Helper for Exercise 9-9.1-3: Serre's first filtration piece is modeled by adjoining the fixed
eigenvector `v` as a distinguished left factor. -/
private def symmetricPower_insert_left
    (n : ℕ) (v : V) :
    SymmetricPower k (Fin n) V →ₗ[k] SymmetricPower k (Fin (n + 1)) V where
  toFun := symmetricPower_insert_left_fun (k := k) n v
  map_add' := symmetricPower_insert_left_fun_add (k := k) n v
  map_smul' := symmetricPower_insert_left_fun_smul (k := k) n v

/-- Helper for Exercise 9-9.1-3: on a pure symmetric generator, the distinguished-factor
insertion literally adjoins `v` as the first tensor factor. -/
private theorem symmetricPower_insert_left_apply_mk
    (n : ℕ) (v : V) (f : Fin n → V) :
    symmetricPower_insert_left (k := k) n v
        (SymmetricPower.mk k (Fin n) V (PiTensorProduct.tprod k f)) =
      SymmetricPower.mk k (Fin (n + 1)) V (PiTensorProduct.tprod k (Fin.cons v f)) := by
  -- Unfold to the tensor-level insertion, evaluate the tensor lift, and then rewrite `tprod`.
  calc
    symmetricPower_insert_left (k := k) n v
        (SymmetricPower.mk k (Fin n) V (PiTensorProduct.tprod k f)) =
      SymmetricPower.tprod k (ι := Fin (n + 1)) (M := V) (Fin.cons v f) := by
          show symmetricPower_insert_left_tensor (k := k) n v (PiTensorProduct.tprod k f) = _
          simp [symmetricPower_insert_left_tensor, MultilinearMap.curryLeft_apply]
    _ = SymmetricPower.mk k (Fin (n + 1)) V (PiTensorProduct.tprod k (Fin.cons v f)) := by
          rfl

/-- Helper for Exercise 9-9.1-3: if a pure symmetric generator already contains the distinguished
vector `v` in one slot, then that generator lies in the first-step range
`range (symmetricPower_insert_left n v)`. -/
private theorem symmetricPower_mk_mem_range_insert_left_of_exists_eq
    (n : ℕ) (v : V) (f : Fin (n + 1) → V) (hvf : ∃ i, f i = v) :
    SymmetricPower.mk k (Fin (n + 1)) V (PiTensorProduct.tprod k f) ∈
      LinearMap.range (symmetricPower_insert_left (k := k) n v) := by
  rcases hvf with ⟨i, hi⟩
  let e : Equiv.Perm (Fin (n + 1)) :=
    (finSuccEquiv n).trans (finSuccEquiv' i).symm
  let g : Fin n → V := fun j ↦ f (i.succAbove j)
  refine ⟨SymmetricPower.mk k (Fin n) V (PiTensorProduct.tprod k g), ?_⟩
  -- Move the chosen copy of `v` to the distinguished `0`th slot, then identify the resulting
  -- tensor with the image of `insert_left`.
  calc
    symmetricPower_insert_left (k := k) n v
        (SymmetricPower.mk k (Fin n) V (PiTensorProduct.tprod k g)) =
      SymmetricPower.mk k (Fin (n + 1)) V (PiTensorProduct.tprod k (Fin.cons v g)) := by
        rw [symmetricPower_insert_left_apply_mk]
    _ =
      SymmetricPower.mk k (Fin (n + 1)) V
        (PiTensorProduct.tprod k fun j ↦ f (e j)) := by
          congr 2
          funext j
          refine Fin.cases ?_ ?_ j
          · simp [e, hi]
          · intro j
            simp [e, g]
    _ = SymmetricPower.mk k (Fin (n + 1)) V (PiTensorProduct.tprod k f) := by
          simpa [SymmetricPower.tprod, e] using
            (SymmetricPower.tprod_equiv (R := k) (ι := Fin (n + 1)) (M := V) e f)

/-- Helper for Exercise 9-9.1-3: if one factor of a pure symmetric generator is a scalar multiple
of the distinguished vector `v`, then the generator still lies in
`range (symmetricPower_insert_left n v)` after pulling that scalar out. -/
private theorem symmetricPower_mk_mem_range_insert_left_of_exists_eq_smul
    (n : ℕ) (v : V) (f : Fin (n + 1) → V) (hvf : ∃ i, ∃ c : k, f i = c • v) :
    SymmetricPower.mk k (Fin (n + 1)) V (PiTensorProduct.tprod k f) ∈
      LinearMap.range (symmetricPower_insert_left (k := k) n v) := by
  rcases hvf with ⟨i, c, hi⟩
  let g : Fin (n + 1) → V := Function.update f i v
  have hupdate : Function.update g i (c • v) = f := by
    -- Replacing the chosen slot by `v` and then by `c • v = f i` recovers the original family.
    funext j
    by_cases hj : j = i
    · subst hj
      simp [g, hi]
    · simp [g, hj]
  have hmul :
      SymmetricPower.mk k (Fin (n + 1)) V (PiTensorProduct.tprod k f) =
        c • SymmetricPower.mk k (Fin (n + 1)) V (PiTensorProduct.tprod k g) := by
    -- Replace the chosen slot by `v`, then use multilinearity to pull the scalar `c` out.
    change SymmetricPower.tprod k (ι := Fin (n + 1)) (M := V) f = _
    calc
      SymmetricPower.tprod k (ι := Fin (n + 1)) (M := V) f =
        SymmetricPower.tprod k (ι := Fin (n + 1)) (M := V)
          (Function.update g i (c • v)) := by
            rw [hupdate]
      _ = c • SymmetricPower.tprod k (ι := Fin (n + 1)) (M := V) g := by
            simpa [g] using
              (SymmetricPower.tprod k (ι := Fin (n + 1)) (M := V)).map_update_smul g i c v
  have hg :
      SymmetricPower.mk k (Fin (n + 1)) V (PiTensorProduct.tprod k g) ∈
        LinearMap.range (symmetricPower_insert_left (k := k) n v) := by
    -- After the replacement, the previous exact-slot lemma applies at the same index `i`.
    exact
      symmetricPower_mk_mem_range_insert_left_of_exists_eq
        (k := k) (n := n) v g ⟨i, by simp [g]⟩
  rw [hmul]
  exact Submodule.smul_mem _ c hg

/-- Helper for Exercise 9-9.1-3: the distinguished-factor insertion intertwines the induced
action on symmetric powers with multiplication by the eigenvalue `μ`. -/
private theorem symmetricPower_insert_left_intertwines
    (A : V →ₗ[k] V) (n : ℕ) {v : V} {μ : k} (hμ : A v = μ • v) :
    (SymmetricPower.map (n + 1) A).comp (symmetricPower_insert_left (k := k) n v) =
      (symmetricPower_insert_left (k := k) n v).comp (μ • SymmetricPower.map n A) := by
  have hcomp :
      ((SymmetricPower.map (n + 1) A).comp (symmetricPower_insert_left (k := k) n v)).comp
          (SymmetricPower.mk k (Fin n) V) =
        (((symmetricPower_insert_left (k := k) n v).comp (μ • SymmetricPower.map n A))).comp
          (SymmetricPower.mk k (Fin n) V) := by
    -- Compare both composites on pure tensor generators of the source tensor power.
    ext x
    calc
      (SymmetricPower.map (n + 1) A)
          (symmetricPower_insert_left (k := k) n v
            (SymmetricPower.mk k (Fin n) V (PiTensorProduct.tprod k x))) =
        SymmetricPower.mk k (Fin (n + 1)) V
          (PiTensorProduct.tprod k (Fin.cons (A v) fun i ↦ A (x i))) := by
            rw [symmetricPower_insert_left_apply_mk]
            change
              SymmetricPower.mk k (Fin (n + 1)) V
                (PiTensorProduct.map (fun _ : Fin (n + 1) ↦ A)
                  (PiTensorProduct.tprod k (Fin.cons v x))) = _
            rw [PiTensorProduct.map_tprod]
            congr
            funext i
            refine Fin.cases ?_ ?_ i
            · rfl
            · intro j
              rfl
      _ = SymmetricPower.mk k (Fin (n + 1)) V
            (PiTensorProduct.tprod k (Fin.cons (μ • v) fun i ↦ A (x i))) := by
              rw [hμ]
      _ = μ • SymmetricPower.mk k (Fin (n + 1)) V
            (PiTensorProduct.tprod k (Fin.cons v fun i ↦ A (x i))) := by
              simpa using
                symmetricPower_tprod_cons_smul (k := k) (V := V) n μ v (fun i ↦ A (x i))
      _ = μ • symmetricPower_insert_left (k := k) n v
            (SymmetricPower.mk k (Fin n) V (PiTensorProduct.tprod k fun i ↦ A (x i))) := by
              rw [symmetricPower_insert_left_apply_mk]
      _ = symmetricPower_insert_left (k := k) n v
            (μ • SymmetricPower.mk k (Fin n) V (PiTensorProduct.tprod k fun i ↦ A (x i))) := by
              rw [LinearMap.map_smul]
      _ = symmetricPower_insert_left (k := k) n v
            (μ • SymmetricPower.map n A
              (SymmetricPower.mk k (Fin n) V (PiTensorProduct.tprod k x))) := by
              congr 1
              -- Rewrite the right-hand symmetric-power image on the same pure generator.
              rw [show
                  SymmetricPower.map n A
                    (SymmetricPower.mk k (Fin n) V (PiTensorProduct.tprod k x)) =
                    SymmetricPower.mk k (Fin n) V
                      (PiTensorProduct.tprod k fun i ↦ A (x i)) by
                    change
                      SymmetricPower.mk k (Fin n) V
                        (PiTensorProduct.map (fun _ : Fin n ↦ A) (PiTensorProduct.tprod k x)) =
                        _
                    rw [PiTensorProduct.map_tprod]]
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ :=
    LinearMap.range_eq_top.mp (SymmetricPower.range_mk (R := k) (ι := Fin n) (M := V)) y
  exact LinearMap.congr_fun hcomp x

/-- Helper for Exercise 9-9.1-3: a nonzero vector admits a dual functional normalized to `1` on
that vector. This is the linear-algebra input needed to split off the eigenline `k · v`. -/
private theorem exists_dual_eq_one_of_nonzero
    {v : V} (hv : v ≠ 0) :
    ∃ φ : Module.Dual k V, φ v = 1 := by
  -- Finite-dimensional vector spaces are projective, so a nonzero vector can be separated by a
  -- dual functional.
  simpa using Module.Projective.exists_dual_eq_one k hv

/-- Helper for Exercise 9-9.1-3: if a dual functional takes the value `1` on `v`, then the line
`k · v` and the kernel of that functional form a complementary pair. This packages the ambient
splitting used in Serre's first filtration step. -/
private theorem span_singleton_isCompl_ker_of_dual_eq_one
    {v : V} {φ : Module.Dual k V} (hφ : φ v = 1) :
    IsCompl (Submodule.span k ({v} : Set V)) (LinearMap.ker φ) := by
  have hv : v ≠ 0 := by
    intro hv
    have hzero : (1 : k) = 0 := by simpa [hv] using hφ
    exact one_ne_zero hzero
  have hnot_mem : v ∉ LinearMap.ker φ := by
    intro hvker
    have hφ_zero : φ v = 0 := by
      simpa [LinearMap.mem_ker] using hvker
    exact one_ne_zero (by rw [← hφ, hφ_zero])
  refine ⟨?_, codisjoint_iff.mpr ?_⟩
  · -- The normalized functional shows that the line `k · v` meets its kernel only at `0`.
    simpa [disjoint_comm] using
      (Submodule.disjoint_span_singleton_of_notMem hnot_mem :
        Disjoint (LinearMap.ker φ) (k ∙ v))
  · -- The standard span-plus-kernel decomposition for a nonvanishing functional gives the
    -- complementary sum decomposition of `V`.
    have hφ_ne : φ v ≠ 0 := by simpa [hφ]
    simpa using LinearMap.span_singleton_sup_ker_eq_top φ hφ_ne

/-- Helper for Exercise 9-9.1-3: a normalized dual functional gives an explicit product
decomposition of `V` into the eigenline `k · v` and the complementary kernel. -/
private noncomputable def span_singleton_ker_dual_prodEquiv
    {v : V} {φ : Module.Dual k V} (hφ : φ v = 1) :
    (Submodule.span k ({v} : Set V) × LinearMap.ker φ) ≃ₗ[k] V :=
  (Submodule.span k ({v} : Set V)).prodEquivOfIsCompl (LinearMap.ker φ)
    (span_singleton_isCompl_ker_of_dual_eq_one (k := k) (V := V) hφ)

/-- Helper for Exercise 9-9.1-3: after splitting `V = (k · v) ⊕ ker φ`, the quotient by the
eigenline is exactly the second component of the split model. -/
private theorem quotient_span_singleton_eq_snd_comp_prodEquiv_symm
    {v : V} {φ : Module.Dual k V} (hφ : φ v = 1) :
    let L : Submodule k V := Submodule.span k ({v} : Set V)
    let W : Submodule k V := LinearMap.ker φ
    let hCompl : IsCompl L W :=
      span_singleton_isCompl_ker_of_dual_eq_one (k := k) (V := V) hφ
    let eVW : (L × W) ≃ₗ[k] V :=
      span_singleton_ker_dual_prodEquiv (k := k) (V := V) hφ
    let qEquiv : (V ⧸ L) ≃ₗ[k] W :=
      Submodule.quotientEquivOfIsCompl L W hCompl
    qEquiv.toLinearMap.comp (Submodule.mkQ L) =
      (LinearMap.snd k L W).comp eVW.symm.toLinearMap := by
  dsimp
  ext x
  let y : (Submodule.span k ({v} : Set V)) × LinearMap.ker φ :=
    (span_singleton_ker_dual_prodEquiv (k := k) (V := V) hφ).symm x
  have hy : x = y.1 + y.2 := by
    -- Expand `x` in the split model so that the quotient kills the line component.
    simpa [y, span_singleton_ker_dual_prodEquiv] using
      ((span_singleton_ker_dual_prodEquiv (k := k) (V := V) hφ).apply_symm_apply x).symm
  have hmk :
      (Submodule.mkQ (Submodule.span k ({v} : Set V))) (↑y.1 + ↑y.2) =
        (Submodule.mkQ (Submodule.span k ({v} : Set V))) ↑y.2 := by
    -- In the quotient, only the complementary kernel component survives.
    change
      ((Submodule.Quotient.mk (↑y.1 + ↑y.2 : V)) :
        V ⧸ Submodule.span k ({v} : Set V)) =
        (Submodule.Quotient.mk (↑y.2 : V) :
          V ⧸ Submodule.span k ({v} : Set V))
    rw [Submodule.Quotient.eq]
    simpa
  -- The quotient equivalence attached to the complement sends the surviving class to `y.2`.
  simp only [LinearMap.comp_apply]
  calc
    ↑(((Submodule.quotientEquivOfIsCompl
        (Submodule.span k ({v} : Set V))
        (LinearMap.ker φ)
        (span_singleton_isCompl_ker_of_dual_eq_one (k := k) (V := V) hφ)).toLinearMap)
        ((Submodule.mkQ (Submodule.span k ({v} : Set V))) x)) =
      ↑(((Submodule.quotientEquivOfIsCompl
          (Submodule.span k ({v} : Set V))
          (LinearMap.ker φ)
          (span_singleton_isCompl_ker_of_dual_eq_one (k := k) (V := V) hφ)).toLinearMap)
          ((Submodule.mkQ (Submodule.span k ({v} : Set V))) ↑y.2)) := by
            rw [hy, hmk]
    _ = (y.2 : V) := by
          simpa using
            (Submodule.quotientEquivOfIsCompl_apply_mk_coe
              (p := Submodule.span k ({v} : Set V))
              (q := LinearMap.ker φ)
              (h := span_singleton_isCompl_ker_of_dual_eq_one (k := k) (V := V) hφ)
              y.2)
    _ = ↑(((LinearMap.snd k
            (Submodule.span k ({v} : Set V))
            (LinearMap.ker φ)).comp
          ((span_singleton_ker_dual_prodEquiv (k := k) (V := V) hφ).symm.toLinearMap)) x) := by
            simp [LinearMap.comp_apply, y]

/-- Helper for Exercise 9-9.1-3: in the split model `V = (k · v) ⊕ ker φ`, the quotient map by
the eigenline becomes the literal second projection. -/
private theorem quotient_span_singleton_comp_prodEquiv_eq_snd
    {v : V} {φ : Module.Dual k V} (hφ : φ v = 1) :
    let L : Submodule k V := Submodule.span k ({v} : Set V)
    let W : Submodule k V := LinearMap.ker φ
    let hCompl : IsCompl L W :=
      span_singleton_isCompl_ker_of_dual_eq_one (k := k) (V := V) hφ
    let eVW : (L × W) ≃ₗ[k] V :=
      span_singleton_ker_dual_prodEquiv (k := k) (V := V) hφ
    let qEquiv : (V ⧸ L) ≃ₗ[k] W :=
      Submodule.quotientEquivOfIsCompl L W hCompl
    (qEquiv.toLinearMap.comp (Submodule.mkQ L)).comp eVW.toLinearMap =
      (LinearMap.snd k L W) := by
  dsimp
  refine LinearMap.ext ?_
  intro x
  -- Compose the previous transport identity with the split-model equivalence on the right.
  have htransport :=
    quotient_span_singleton_eq_snd_comp_prodEquiv_symm
      (k := k) (V := V) (v := v) (φ := φ) hφ
  simpa using LinearMap.congr_fun htransport ((span_singleton_ker_dual_prodEquiv
    (k := k) (V := V) hφ) x)

/-- Helper for Exercise 9-9.1-3: a surjective linear map on the base module induces a surjective
map on every symmetric power. -/
theorem symmetricPower_map_surjective
    {W : Type w} [AddCommGroup W] [Module k W]
    (n : ℕ) (f : V →ₗ[k] W) (hf : Function.Surjective f) :
    Function.Surjective (SymmetricPower.map n f) := by
  intro y
  obtain ⟨x, rfl⟩ :=
    LinearMap.range_eq_top.mp (SymmetricPower.range_mk (R := k) (ι := Fin n) (M := W)) y
  classical
  choose g hg using hf
  -- First induct on a tensor representative, reducing surjectivity to the pure-generator case.
  refine PiTensorProduct.induction_on' x ?_ ?_
  · intro a m
    refine ⟨a • SymmetricPower.mk k (Fin n) V (PiTensorProduct.tprod k fun i ↦ g (m i)), ?_⟩
    -- On a pure generator, functoriality applies `f` coordinatewise.
    have hbase :
        SymmetricPower.map n f
          (SymmetricPower.mk k (Fin n) V (PiTensorProduct.tprod k fun i ↦ g (m i))) =
        SymmetricPower.mk k (Fin n) W (PiTensorProduct.tprod k m) := by
      change
        SymmetricPower.mk k (Fin n) W
          (PiTensorProduct.map (fun _ : Fin n ↦ f)
            (PiTensorProduct.tprod k fun i ↦ g (m i))) =
          SymmetricPower.mk k (Fin n) W (PiTensorProduct.tprod k m)
      rw [PiTensorProduct.map_tprod]
      congr
      funext i
      exact hg (m i)
    -- The `tprodCoeff` representative from `induction_on'` is exactly the scalar multiple of the
    -- pure generator already handled by `hbase`.
    simpa [PiTensorProduct.tprodCoeff_eq_smul_tprod] using congrArg (a • ·) hbase
  · intro x y hx hy
    rcases hx with ⟨ax, hax⟩
    rcases hy with ⟨ay, hay⟩
    refine ⟨ax + ay, by simp [hax, hay]⟩

/-- Helper for Exercise 9-9.1-3: the quotient map `V → V ⧸ L` induces the canonical first
isomorphism-theorem identification
`Sym^n(V) / ker(Sym^n(V) → Sym^n(V ⧸ L)) ≃ Sym^n(V ⧸ L)`. -/
noncomputable def symmetricPower_mapQ_quotKerEquiv
    (n : ℕ) (L : Submodule k V) :
    (SymmetricPower k (Fin n) V ⧸
      LinearMap.ker (SymmetricPower.map n (Submodule.mkQ L))) ≃ₗ[k]
      SymmetricPower k (Fin n) (V ⧸ L) :=
  LinearMap.quotKerEquivOfSurjective (SymmetricPower.map n (Submodule.mkQ L))
    (symmetricPower_map_surjective (k := k) (V := V) (W := V ⧸ L) n
      (Submodule.mkQ L) (Submodule.mkQ_surjective L))

/-- Helper for Exercise 9-9.1-3: the first-stage insertion lands in the kernel of the quotient
map to `Sym^(n+1)(V / (k · v))`, because the distinguished factor `v` dies in the quotient. -/
private theorem symmetricPower_mapQ_span_singleton_comp_insert_left_eq_zero
    (n : ℕ) (v : V) :
    let L : Submodule k V := Submodule.span k ({v} : Set V)
    (SymmetricPower.map (n + 1) (Submodule.mkQ L)).comp
        (symmetricPower_insert_left (k := k) n v) = 0 := by
  dsimp
  have hcomp :
      ((SymmetricPower.map (n + 1)
          (Submodule.mkQ (Submodule.span k ({v} : Set V)))).comp
        (symmetricPower_insert_left (k := k) n v)).comp
          (SymmetricPower.mk k (Fin n) V) = 0 := by
    -- Check the composite on pure generators of the tensor power before descending through the
    -- symmetric quotient.
    ext f
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearMap.zero_apply]
    rw [symmetricPower_insert_left_apply_mk]
    change
      SymmetricPower.mk k (Fin (n + 1))
        (V ⧸ Submodule.span k ({v} : Set V))
        (PiTensorProduct.map
          (fun _ : Fin (n + 1) ↦ Submodule.mkQ (Submodule.span k ({v} : Set V)))
          (PiTensorProduct.tprod k (Fin.cons v f))) = 0
    rw [PiTensorProduct.map_tprod]
    have hvq :
        Submodule.mkQ (Submodule.span k ({v} : Set V)) v = 0 := by
      rw [Submodule.mkQ_apply]
      exact
        (Submodule.Quotient.eq (p := Submodule.span k ({v} : Set V))).2 <|
          by simpa using (Submodule.subset_span (by simp) :
            v ∈ Submodule.span k ({v} : Set V))
    -- Once the distinguished coordinate becomes `0`, multilinearity forces the symmetric tensor to
    -- vanish.
    change
      SymmetricPower.tprod k
        (ι := Fin (n + 1))
        (M := V ⧸ Submodule.span k ({v} : Set V))
        (fun i ↦ (Submodule.span k ({v} : Set V)).mkQ (Fin.cases v f i)) = 0
    simpa using
      (SymmetricPower.tprod k
        (ι := Fin (n + 1))
        (M := V ⧸ Submodule.span k ({v} : Set V))).map_coord_zero 0 <|
          by simpa using hvq
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ :=
    LinearMap.range_eq_top.mp (SymmetricPower.range_mk (R := k) (ι := Fin n) (M := V)) y
  exact LinearMap.congr_fun hcomp x

/-- Helper for Exercise 9-9.1-3: the image of the distinguished-factor insertion already gives
the easy inclusion in Serre's first exact sequence, namely `range(insert_v) ≤ ker(qSym)`. -/
private theorem symmetricPower_insert_left_range_le_ker_mapQ_span_singleton
    (n : ℕ) (v : V) :
    let L : Submodule k V := Submodule.span k ({v} : Set V)
    LinearMap.range (symmetricPower_insert_left (k := k) n v) ≤
      LinearMap.ker (SymmetricPower.map (n + 1) (Submodule.mkQ L)) := by
  dsimp
  intro y hy
  rcases hy with ⟨x, rfl⟩
  -- Evaluate the already-proved zero composite on a chosen preimage in `Sym^n(V)`.
  have hzero :=
    symmetricPower_mapQ_span_singleton_comp_insert_left_eq_zero (k := k) n v
  exact LinearMap.congr_fun hzero x

/-- Helper for Exercise 9-9.1-3: the symmetric power of the quotient map
`V → V ⧸ (k · v)` is surjective in degree `n + 1`. -/
private theorem symmetricPower_mapQ_span_singleton_surjective
    (n : ℕ) (v : V) :
    let L : Submodule k V := Submodule.span k ({v} : Set V)
    Function.Surjective (SymmetricPower.map (n + 1) (Submodule.mkQ L)) := by
  dsimp
  -- Surjectivity is inherited functorially from the base quotient map.
  exact
    symmetricPower_map_surjective
      (k := k) (V := V) (W := V ⧸ Submodule.span k ({v} : Set V))
      (n + 1) (Submodule.mkQ (Submodule.span k ({v} : Set V)))
      (Submodule.mkQ_surjective (Submodule.span k ({v} : Set V)))

/-- Helper for Exercise 9-9.1-3: the first-isomorphism identification for
`Sym^(n+1)(V) → Sym^(n+1)(V ⧸ (k · v))` is just the generic quotient-by-kernel equivalence
specialized to the span of `v`. -/
private noncomputable def symmetricPower_mapQ_span_singleton_quotKerEquiv
    (n : ℕ) (v : V) :
    let L : Submodule k V := Submodule.span k ({v} : Set V)
    (SymmetricPower k (Fin (n + 1)) V ⧸
      LinearMap.ker (SymmetricPower.map (n + 1) (Submodule.mkQ L))) ≃ₗ[k]
      SymmetricPower k (Fin (n + 1)) (V ⧸ L) :=
  symmetricPower_mapQ_quotKerEquiv
    (k := k) (V := V) (n := n + 1) (Submodule.span k ({v} : Set V))

/-- Helper for Exercise 9-9.1-3: Serre's first filtration piece is stable under the symmetric
power action because adjoining the eigenvector `v` intertwines with multiplication by `μ`. -/
private theorem symmetricPower_insert_left_range_le_comap
    (A : V →ₗ[k] V) (n : ℕ) {v : V} {μ : k} (hμ : A v = μ • v) :
    LinearMap.range (symmetricPower_insert_left (k := k) n v) ≤
      (LinearMap.range (symmetricPower_insert_left (k := k) n v)).comap
        (SymmetricPower.map (n + 1) A) := by
  intro y hy
  rcases hy with ⟨x, rfl⟩
  refine ⟨(μ • SymmetricPower.map n A) x, ?_⟩
  -- Evaluate the previously proved intertwining relation on the chosen preimage.
  exact
    LinearMap.congr_fun
      (symmetricPower_insert_left_intertwines
        (k := k) (A := A) n (v := v) (μ := μ) hμ)
      x |>.symm

/-- Helper for Exercise 9-9.1-3: after splitting `V = (k · v) ⊕ ker φ`, the symmetric power of
the quotient map by `k · v` becomes the symmetric power of the second projection. This packages
the transport step in Serre's first filtration argument, leaving only the split-model
kernel-versus-range exactness to prove. -/
private theorem symmetricPower_map_quotient_span_singleton_comp_prodEquiv_eq_map_snd
    {v : V} {φ : Module.Dual k V} (hφ : φ v = 1) (n : ℕ) :
    let L : Submodule k V := Submodule.span k ({v} : Set V)
    let W : Submodule k V := LinearMap.ker φ
    let hCompl : IsCompl L W :=
      span_singleton_isCompl_ker_of_dual_eq_one (k := k) (V := V) hφ
    let eVW : (L × W) ≃ₗ[k] V :=
      span_singleton_ker_dual_prodEquiv (k := k) (V := V) hφ
    let qEquiv : (V ⧸ L) ≃ₗ[k] W :=
      Submodule.quotientEquivOfIsCompl L W hCompl
    (SymmetricPower.map (n + 1) qEquiv.toLinearMap).comp
        ((SymmetricPower.map (n + 1) (Submodule.mkQ L)).comp
          (SymmetricPower.map (n + 1) eVW.toLinearMap)) =
      SymmetricPower.map (n + 1) (LinearMap.snd k L W) := by
  dsimp
  -- First collapse the three symmetric-power maps to the symmetric power of the composed base map.
  calc
    (SymmetricPower.map (n + 1)
        ((Submodule.quotientEquivOfIsCompl
          (Submodule.span k ({v} : Set V))
          (LinearMap.ker φ)
          (span_singleton_isCompl_ker_of_dual_eq_one (k := k) (V := V) hφ)).toLinearMap)).comp
        ((SymmetricPower.map (n + 1)
          (Submodule.mkQ (Submodule.span k ({v} : Set V)))).comp
          (SymmetricPower.map (n + 1)
            (span_singleton_ker_dual_prodEquiv (k := k) (V := V) hφ).toLinearMap)) =
      SymmetricPower.map (n + 1)
        (((Submodule.quotientEquivOfIsCompl
            (Submodule.span k ({v} : Set V))
            (LinearMap.ker φ)
            (span_singleton_isCompl_ker_of_dual_eq_one (k := k) (V := V) hφ)).toLinearMap).comp
          ((Submodule.mkQ (Submodule.span k ({v} : Set V))).comp
            (span_singleton_ker_dual_prodEquiv (k := k) (V := V) hφ).toLinearMap)) := by
            rw [← SymmetricPower.map_comp (n + 1)
              (span_singleton_ker_dual_prodEquiv (k := k) (V := V) hφ).toLinearMap
              (Submodule.mkQ (Submodule.span k ({v} : Set V)))]
            rw [← SymmetricPower.map_comp (n + 1)
              ((Submodule.mkQ (Submodule.span k ({v} : Set V))).comp
                (span_singleton_ker_dual_prodEquiv (k := k) (V := V) hφ).toLinearMap)
              ((Submodule.quotientEquivOfIsCompl
                (Submodule.span k ({v} : Set V))
                (LinearMap.ker φ)
                (span_singleton_isCompl_ker_of_dual_eq_one (k := k) (V := V) hφ)).toLinearMap)]
    -- Then replace that composed base map by `snd` using the already-proved split transport.
    _ = SymmetricPower.map (n + 1)
          (LinearMap.snd k (Submodule.span k ({v} : Set V)) (LinearMap.ker φ)) := by
            congr 1
            exact
              quotient_span_singleton_comp_prodEquiv_eq_snd
                (k := k) (V := V) (v := v) (φ := φ) hφ

/-- Helper for Exercise 9-9.1-3: under the split equivalence
`V ≃ (k · v) × ker φ`, Serre's first-stage insertion by the distinguished line generator
transports to the ambient insertion by `v`. -/
private theorem symmetricPower_insert_left_comp_prodEquiv_eq
    {v : V} {φ : Module.Dual k V} (hφ : φ v = 1) (n : ℕ) :
    let L : Submodule k V := Submodule.span k ({v} : Set V)
    let W : Submodule k V := LinearMap.ker φ
    let eVW : (L × W) ≃ₗ[k] V :=
      span_singleton_ker_dual_prodEquiv (k := k) (V := V) hφ
    let lineVec : L × W :=
      (⟨v, Submodule.subset_span (by simp : v ∈ ({v} : Set V))⟩, 0)
    (SymmetricPower.map (n + 1) eVW.toLinearMap).comp
        (symmetricPower_insert_left (k := k) n lineVec) =
      (symmetricPower_insert_left (k := k) n v).comp
        (SymmetricPower.map n eVW.toLinearMap) := by
  dsimp
  have hcomp :
      ((SymmetricPower.map (n + 1)
          (span_singleton_ker_dual_prodEquiv (k := k) (V := V) hφ).toLinearMap).comp
        (symmetricPower_insert_left (k := k) n
          ((⟨v, Submodule.subset_span (by simp : v ∈ ({v} : Set V))⟩), 0))).comp
          (SymmetricPower.mk k (Fin n)
            ((Submodule.span k ({v} : Set V)) × LinearMap.ker φ)) =
        (((symmetricPower_insert_left (k := k) n v).comp
          (SymmetricPower.map n
            (span_singleton_ker_dual_prodEquiv (k := k) (V := V) hφ).toLinearMap))).comp
          (SymmetricPower.mk k (Fin n)
            ((Submodule.span k ({v} : Set V)) × LinearMap.ker φ)) := by
    -- Compare the two transports on pure generators of the split-model symmetric power.
    ext x
    calc
      (SymmetricPower.map (n + 1)
          (span_singleton_ker_dual_prodEquiv (k := k) (V := V) hφ).toLinearMap)
          (symmetricPower_insert_left (k := k) n
            ((⟨v, Submodule.subset_span (by simp : v ∈ ({v} : Set V))⟩), 0)
            (SymmetricPower.mk k (Fin n)
              ((Submodule.span k ({v} : Set V)) × LinearMap.ker φ)
              (PiTensorProduct.tprod k x))) =
        SymmetricPower.mk k (Fin (n + 1)) V
          (PiTensorProduct.tprod k
            (Fin.cons v
              (fun i ↦
                (span_singleton_ker_dual_prodEquiv (k := k) (V := V) hφ) (x i)))) := by
              rw [symmetricPower_insert_left_apply_mk]
              change
                SymmetricPower.mk k (Fin (n + 1)) V
                  (PiTensorProduct.map
                    (fun _ : Fin (n + 1) ↦
                      (span_singleton_ker_dual_prodEquiv
                        (k := k) (V := V) hφ).toLinearMap)
                    (PiTensorProduct.tprod k
                      (Fin.cons
                        ((⟨v, Submodule.subset_span (by simp : v ∈ ({v} : Set V))⟩), 0) x))) = _
              rw [PiTensorProduct.map_tprod]
              congr
              funext i
              refine Fin.cases ?_ ?_ i
              · simp [span_singleton_ker_dual_prodEquiv]
              · intro j
                rfl
      _ = symmetricPower_insert_left (k := k) n v
            (SymmetricPower.mk k (Fin n) V
              (PiTensorProduct.tprod k
                (fun i ↦
                  (span_singleton_ker_dual_prodEquiv (k := k) (V := V) hφ) (x i)))) := by
              rw [symmetricPower_insert_left_apply_mk]
      _ = symmetricPower_insert_left (k := k) n v
            (SymmetricPower.map n
              (span_singleton_ker_dual_prodEquiv (k := k) (V := V) hφ).toLinearMap
              (SymmetricPower.mk k (Fin n)
                ((Submodule.span k ({v} : Set V)) × LinearMap.ker φ)
                (PiTensorProduct.tprod k x))) := by
              congr 1
              rw [show
                SymmetricPower.map n
                  (span_singleton_ker_dual_prodEquiv (k := k) (V := V) hφ).toLinearMap
                  (SymmetricPower.mk k (Fin n)
                    ((Submodule.span k ({v} : Set V)) × LinearMap.ker φ)
                    (PiTensorProduct.tprod k x)) =
                  SymmetricPower.mk k (Fin n) V
                    (PiTensorProduct.tprod k
                      (fun i ↦
                        (span_singleton_ker_dual_prodEquiv
                          (k := k) (V := V) hφ) (x i))) by
                    change
                      SymmetricPower.mk k (Fin n) V
                        (PiTensorProduct.map
                          (fun _ : Fin n ↦
                            (span_singleton_ker_dual_prodEquiv
                              (k := k) (V := V) hφ).toLinearMap)
                          (PiTensorProduct.tprod k x)) = _
                    rw [PiTensorProduct.map_tprod]
                    rfl]
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ :=
    LinearMap.range_eq_top.mp
      (SymmetricPower.range_mk
        (R := k) (ι := Fin n)
        (M := (Submodule.span k ({v} : Set V)) × LinearMap.ker φ)) y
  exact LinearMap.congr_fun hcomp x

/-- Helper for Exercise 9-9.1-3: the split-model transport step consists of two concrete
identifications, namely that the quotient map becomes `snd` and that the first-stage insertion
is the insertion of the distinguished line generator. -/
private theorem symmetricPower_first_stage_split_transport
    {v : V} {φ : Module.Dual k V} (hφ : φ v = 1) (n : ℕ) :
    let L : Submodule k V := Submodule.span k ({v} : Set V)
    let W : Submodule k V := LinearMap.ker φ
    let hCompl : IsCompl L W :=
      span_singleton_isCompl_ker_of_dual_eq_one (k := k) (V := V) hφ
    let eVW : (L × W) ≃ₗ[k] V :=
      span_singleton_ker_dual_prodEquiv (k := k) (V := V) hφ
    let qEquiv : (V ⧸ L) ≃ₗ[k] W :=
      Submodule.quotientEquivOfIsCompl L W hCompl
    let lineVec : L × W :=
      (⟨v, Submodule.subset_span (by simp : v ∈ ({v} : Set V))⟩, 0)
    ((SymmetricPower.map (n + 1) qEquiv.toLinearMap).comp
        ((SymmetricPower.map (n + 1) (Submodule.mkQ L)).comp
          (SymmetricPower.map (n + 1) eVW.toLinearMap)) =
      SymmetricPower.map (n + 1) (LinearMap.snd k L W)) ∧
    ((SymmetricPower.map (n + 1) eVW.toLinearMap).comp
        (symmetricPower_insert_left (k := k) n lineVec) =
      (symmetricPower_insert_left (k := k) n v).comp
        (SymmetricPower.map n eVW.toLinearMap)) := by
  constructor
  · -- The quotient transport is already the previously isolated `snd`-transport theorem.
    exact
      symmetricPower_map_quotient_span_singleton_comp_prodEquiv_eq_map_snd
        (k := k) (V := V) (v := v) (φ := φ) hφ n
  · -- The insertion transport is the new split-model companion needed for the first stage.
    exact
      symmetricPower_insert_left_comp_prodEquiv_eq
        (k := k) (V := V) (v := v) (φ := φ) hφ n

/-- Helper for Exercise 9-9.1-3: a left inverse on the base linear map induces injectivity on
every symmetric power by functoriality of `SymmetricPower.map`. -/
private theorem symmetricPower_map_injective_of_leftInverse
    {W : Type w} [AddCommGroup W] [Module k W]
    (n : ℕ) (f : V →ₗ[k] W) (g : W →ₗ[k] V)
    (hgf : g.comp f = LinearMap.id) :
    Function.Injective (SymmetricPower.map n f) := by
  -- Apply the left inverse coordinatewise on symmetric powers and collapse the composite back to
  -- `Sym(id) = id`.
  apply LinearMap.injective_of_comp_eq_id
  calc
    (SymmetricPower.map n g).comp (SymmetricPower.map n f) =
        SymmetricPower.map n (g.comp f) := by
          simpa using (SymmetricPower.map_comp n f g).symm
    _ = SymmetricPower.map n (LinearMap.id : V →ₗ[k] V) := by rw [hgf]
    _ = LinearMap.id := SymmetricPower.map_id n

/-- Helper for Exercise 9-9.1-3: once the split-model insertion by `(v, 0)` is known to be
injective, the explicit decomposition `V ≃ (k · v) × ker φ` transports that injectivity back to
the ambient insertion by `v`. -/
private theorem symmetricPower_insert_left_injective_of_split
    {v : V} {φ : Module.Dual k V} (hφ : φ v = 1) (n : ℕ)
    (hinjSplit :
      let L : Submodule k V := Submodule.span k ({v} : Set V)
      let W : Submodule k V := LinearMap.ker φ
      let lineVec : L × W :=
        (⟨v, Submodule.subset_span (by simp : v ∈ ({v} : Set V))⟩, 0)
      Function.Injective (symmetricPower_insert_left (k := k) n lineVec)) :
    Function.Injective (symmetricPower_insert_left (k := k) n v) := by
  dsimp at hinjSplit ⊢
  let L : Submodule k V := Submodule.span k ({v} : Set V)
  let W : Submodule k V := LinearMap.ker φ
  let eVW : (L × W) ≃ₗ[k] V :=
    span_singleton_ker_dual_prodEquiv (k := k) (V := V) hφ
  let lineVec : L × W :=
    (⟨v, Submodule.subset_span (by simp : v ∈ ({v} : Set V))⟩, 0)
  have he_n :
      Function.Injective (SymmetricPower.map n eVW.toLinearMap) := by
    -- The split-model equivalence has an actual inverse, so `Sym(eVW)` is injective.
    exact
      symmetricPower_map_injective_of_leftInverse
        (k := k) (V := L × W) (W := V) n
        eVW.toLinearMap eVW.symm.toLinearMap
        (by
          apply LinearMap.ext
          intro x
          exact eVW.left_inv x)
  have he_succ :
      Function.Injective (SymmetricPower.map (n + 1) eVW.toLinearMap) := by
    -- The same argument applies in degree `n + 1`.
    exact
      symmetricPower_map_injective_of_leftInverse
        (k := k) (V := L × W) (W := V) (n + 1)
        eVW.toLinearMap eVW.symm.toLinearMap
        (by
          apply LinearMap.ext
          intro x
          exact eVW.left_inv x)
  intro x y hxy
  let xSplit : SymmetricPower k (Fin n) (L × W) :=
    SymmetricPower.map n eVW.symm.toLinearMap x
  let ySplit : SymmetricPower k (Fin n) (L × W) :=
    SymmetricPower.map n eVW.symm.toLinearMap y
  have htransport :=
    (symmetricPower_first_stage_split_transport
      (k := k) (V := V) (v := v) (φ := φ) hφ n).2
  have hxback :
      SymmetricPower.map n eVW.toLinearMap xSplit = x := by
    -- Moving `x` to the split model and back along `eVW` recovers `x`.
    dsimp [xSplit]
    calc
      SymmetricPower.map n eVW.toLinearMap
          (SymmetricPower.map n eVW.symm.toLinearMap x) =
        SymmetricPower.map n (eVW.toLinearMap.comp eVW.symm.toLinearMap) x := by
            simpa [LinearMap.comp_apply] using
              (LinearMap.congr_fun
                (SymmetricPower.map_comp n eVW.symm.toLinearMap eVW.toLinearMap)
                x).symm
      _ = SymmetricPower.map n (LinearMap.id : V →ₗ[k] V) x := by
            congr
            ext z
            exact eVW.apply_symm_apply z
      _ = x := by
            simpa using LinearMap.congr_fun (SymmetricPower.map_id n) x
  have hyback :
      SymmetricPower.map n eVW.toLinearMap ySplit = y := by
    -- The same split-then-unsplit simplification holds for `y`.
    dsimp [ySplit]
    calc
      SymmetricPower.map n eVW.toLinearMap
          (SymmetricPower.map n eVW.symm.toLinearMap y) =
        SymmetricPower.map n (eVW.toLinearMap.comp eVW.symm.toLinearMap) y := by
            simpa [LinearMap.comp_apply] using
              (LinearMap.congr_fun
                (SymmetricPower.map_comp n eVW.symm.toLinearMap eVW.toLinearMap)
                y).symm
      _ = SymmetricPower.map n (LinearMap.id : V →ₗ[k] V) y := by
            congr
            ext z
            exact eVW.apply_symm_apply z
      _ = y := by
            simpa using LinearMap.congr_fun (SymmetricPower.map_id n) y
  have hxtransport :
      SymmetricPower.map (n + 1) eVW.toLinearMap
          (symmetricPower_insert_left (k := k) n lineVec xSplit) =
        symmetricPower_insert_left (k := k) n v x := by
    -- Transport the split-model insertion by `lineVec` back to the ambient insertion by `v`.
    calc
      SymmetricPower.map (n + 1) eVW.toLinearMap
          (symmetricPower_insert_left (k := k) n lineVec xSplit) =
        symmetricPower_insert_left (k := k) n v
          (SymmetricPower.map n eVW.toLinearMap xSplit) := by
            simpa [LinearMap.comp_apply] using
              LinearMap.congr_fun htransport xSplit
      _ = symmetricPower_insert_left (k := k) n v x := by rw [hxback]
  have hytransport :
      SymmetricPower.map (n + 1) eVW.toLinearMap
          (symmetricPower_insert_left (k := k) n lineVec ySplit) =
        symmetricPower_insert_left (k := k) n v y := by
    -- The same transport identity holds for `y`.
    calc
      SymmetricPower.map (n + 1) eVW.toLinearMap
          (symmetricPower_insert_left (k := k) n lineVec ySplit) =
        symmetricPower_insert_left (k := k) n v
          (SymmetricPower.map n eVW.toLinearMap ySplit) := by
            simpa [LinearMap.comp_apply] using
              LinearMap.congr_fun htransport ySplit
      _ = symmetricPower_insert_left (k := k) n v y := by rw [hyback]
  have hsplitEq :
      symmetricPower_insert_left (k := k) n lineVec xSplit =
        symmetricPower_insert_left (k := k) n lineVec ySplit := by
    -- After rewriting both ambient images through the split transport, injectivity of
    -- `Sym(eVW)` returns to the split model.
    apply he_succ
    rw [hxtransport, hytransport, hxy]
  have hxySplit : xSplit = ySplit := hinjSplit hsplitEq
  -- Once the split coordinates agree, transport them back to the ambient space.
  calc
    x = SymmetricPower.map n eVW.toLinearMap xSplit := hxback.symm
    _ = SymmetricPower.map n eVW.toLinearMap ySplit := by rw [hxySplit]
    _ = y := hyback

/-- Helper for Exercise 9-9.1-3: in the split model `V = (k · v) ⊕ ker φ`, adjoining the
distinguished line generator lands in the kernel of the symmetric power of `snd`, because that
generator maps to `0` under the projection. -/
private theorem symmetricPower_map_snd_comp_insert_left_eq_zero
    {v : V} {φ : Module.Dual k V} (hφ : φ v = 1) (n : ℕ) :
    let L : Submodule k V := Submodule.span k ({v} : Set V)
    let W : Submodule k V := LinearMap.ker φ
    let lineVec : L × W :=
      (⟨v, Submodule.subset_span (by simp : v ∈ ({v} : Set V))⟩, 0)
    (SymmetricPower.map (n + 1) (LinearMap.snd k L W)).comp
        (symmetricPower_insert_left (k := k) n lineVec) = 0 := by
  dsimp
  have hcomp :
      ((SymmetricPower.map (n + 1)
          (LinearMap.snd k (Submodule.span k ({v} : Set V)) (LinearMap.ker φ))).comp
        (symmetricPower_insert_left (k := k) n
          ((⟨v, Submodule.subset_span (by simp : v ∈ ({v} : Set V))⟩), 0))).comp
          (SymmetricPower.mk k (Fin n)
            ((Submodule.span k ({v} : Set V)) × LinearMap.ker φ)) = 0 := by
    -- Check the split-model composite on pure generators before descending through the quotient.
    ext f
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearMap.zero_apply]
    rw [symmetricPower_insert_left_apply_mk]
    change
      SymmetricPower.mk k (Fin (n + 1)) (LinearMap.ker φ)
        (PiTensorProduct.map
          (fun _ : Fin (n + 1) ↦
            LinearMap.snd k (Submodule.span k ({v} : Set V)) (LinearMap.ker φ))
          (PiTensorProduct.tprod k
            (Fin.cons ((⟨v, Submodule.subset_span (by simp : v ∈ ({v} : Set V))⟩), 0) f))) = 0
    rw [PiTensorProduct.map_tprod]
    have hline :
        LinearMap.snd k (Submodule.span k ({v} : Set V)) (LinearMap.ker φ)
          ((⟨v, Submodule.subset_span (by simp : v ∈ ({v} : Set V))⟩), 0) = 0 := by
      rfl
    -- Once the distinguished coordinate becomes `0`, multilinearity forces the symmetric tensor to
    -- vanish in the split-model quotient term.
    change
      SymmetricPower.tprod k
        (ι := Fin (n + 1))
        (M := LinearMap.ker φ)
        (fun i ↦
          LinearMap.snd k (Submodule.span k ({v} : Set V)) (LinearMap.ker φ)
            (Fin.cases ((⟨v, Submodule.subset_span (by simp : v ∈ ({v} : Set V))⟩), 0) f i)) = 0
    simpa using
      (SymmetricPower.tprod k
        (ι := Fin (n + 1))
        (M := LinearMap.ker φ)).map_coord_zero 0 <|
          by simpa using hline
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ :=
    LinearMap.range_eq_top.mp
      (SymmetricPower.range_mk
        (R := k) (ι := Fin n)
        (M := (Submodule.span k ({v} : Set V)) × LinearMap.ker φ)) y
  exact LinearMap.congr_fun hcomp x

/-- Helper for Exercise 9-9.1-3: in the split model, Serre's first filtration piece gives the easy
inclusion `range(insert_left) ≤ ker(Sym(snd))`; only the reverse inclusion remains open. -/
private theorem symmetricPower_insert_left_range_le_ker_map_snd
    {v : V} {φ : Module.Dual k V} (hφ : φ v = 1) (n : ℕ) :
    let L : Submodule k V := Submodule.span k ({v} : Set V)
    let W : Submodule k V := LinearMap.ker φ
    let lineVec : L × W :=
      (⟨v, Submodule.subset_span (by simp : v ∈ ({v} : Set V))⟩, 0)
    LinearMap.range (symmetricPower_insert_left (k := k) n lineVec) ≤
      LinearMap.ker (SymmetricPower.map (n + 1) (LinearMap.snd k L W)) := by
  dsimp
  intro y hy
  rcases hy with ⟨x, rfl⟩
  -- Evaluate the already-proved zero composite on a chosen preimage in the split model.
  have hzero :=
    symmetricPower_map_snd_comp_insert_left_eq_zero
      (k := k) (V := V) (v := v) (φ := φ) hφ n
  exact LinearMap.congr_fun hzero x

/-- Helper for Exercise 9-9.1-3: in the split model `V = (k · v) ⊕ ker φ`, any pure symmetric
generator with one tensor factor already lying in the line summand `L × 0` belongs to Serre's
first-stage range `range(insert_left)`. -/
private theorem symmetricPower_mk_mem_range_insert_left_of_exists_mem_range_inl
    {v : V} {φ : Module.Dual k V} (hφ : φ v = 1) (n : ℕ)
    (f : Fin (n + 1) → (Submodule.span k ({v} : Set V)) × LinearMap.ker φ)
    (hf :
      ∃ i,
        f i ∈ LinearMap.range
          (LinearMap.inl k (Submodule.span k ({v} : Set V)) (LinearMap.ker φ))) :
    let lineVec :
        (Submodule.span k ({v} : Set V)) × LinearMap.ker φ :=
      (⟨v, Submodule.subset_span (by simp : v ∈ ({v} : Set V))⟩, 0)
    SymmetricPower.mk k (Fin (n + 1))
        ((Submodule.span k ({v} : Set V)) × LinearMap.ker φ)
        (PiTensorProduct.tprod k f) ∈
      LinearMap.range (symmetricPower_insert_left (k := k) n lineVec) := by
  dsimp
  let lineElem : Submodule.span k ({v} : Set V) :=
    ⟨v, Submodule.subset_span (by simp : v ∈ ({v} : Set V))⟩
  let lineVec :
      (Submodule.span k ({v} : Set V)) × LinearMap.ker φ :=
    (lineElem, 0)
  rcases hf with ⟨i, hi⟩
  rcases hi with ⟨x, hx⟩
  have hx_span : ∃ c : k, c • v = (x : V) := by
    -- Any vector of the line summand is a scalar multiple of the distinguished eigenvector `v`.
    simpa [eq_comm] using
      (Submodule.mem_span_singleton : (x : V) ∈ Submodule.span k ({v} : Set V) ↔ _)
  rcases hx_span with ⟨c, hc⟩
  have hx_line : x = c • lineElem := by
    -- Lift the ambient scalar-multiple identity back into the line submodule.
    ext
    exact hc.symm
  have hfactor : f i = c • lineVec := by
    -- Rewrite the chosen line factor as a scalar multiple of the distinguished split-model
    -- generator `(v, 0)`.
    calc
      f i = (x, 0) := by
        simpa [LinearMap.inl] using hx.symm
      _ = (c • lineElem, (0 : LinearMap.ker φ)) := by
            rw [hx_line]
      _ = c • lineVec := by
            simp [lineVec]
  -- Once one factor is a scalar multiple of `(v, 0)`, the earlier scalar-extraction lemma places
  -- the whole symmetric generator inside the first-stage range.
  exact
    symmetricPower_mk_mem_range_insert_left_of_exists_eq_smul
      (k := k) (n := n) lineVec f
      ⟨i, c, hfactor⟩

/-- Helper for Exercise 9-9.1-3: in the split model, `Sym(snd)` has the evident section
`Sym(inr)`, so their composite is the identity on the quotient-side symmetric power. -/
private theorem symmetricPower_map_snd_comp_map_inr_eq_id
    {v : V} {φ : Module.Dual k V} (hφ : φ v = 1) (n : ℕ) :
    let L : Submodule k V := Submodule.span k ({v} : Set V)
    let W : Submodule k V := LinearMap.ker φ
    (SymmetricPower.map (n + 1) (LinearMap.snd k L W)).comp
        (SymmetricPower.map (n + 1) (LinearMap.inr k L W)) = LinearMap.id := by
  dsimp
  -- Collapse the two symmetric-power maps to the symmetric power of `snd ∘ inr = id`.
  calc
    (SymmetricPower.map (n + 1)
        (LinearMap.snd k (Submodule.span k ({v} : Set V)) (LinearMap.ker φ))).comp
        (SymmetricPower.map (n + 1)
          (LinearMap.inr k (Submodule.span k ({v} : Set V)) (LinearMap.ker φ))) =
      SymmetricPower.map (n + 1)
        ((LinearMap.snd k (Submodule.span k ({v} : Set V)) (LinearMap.ker φ)).comp
          (LinearMap.inr k (Submodule.span k ({v} : Set V)) (LinearMap.ker φ))) := by
            rw [← SymmetricPower.map_comp (n + 1)
              (LinearMap.inr k (Submodule.span k ({v} : Set V)) (LinearMap.ker φ))
              (LinearMap.snd k (Submodule.span k ({v} : Set V)) (LinearMap.ker φ))]
    _ = SymmetricPower.map (n + 1) (LinearMap.id : LinearMap.ker φ →ₗ[k] LinearMap.ker φ) := by
          rfl
    _ = LinearMap.id := SymmetricPower.map_id (n + 1)

/-- Helper for Exercise 9-9.1-3: on a pure split-model generator, the section `Sym(inr)` sends
`Sym(snd)` back to the generator obtained by discarding every line coordinate and keeping only the
`W = ker φ` part. -/
private theorem symmetricPower_map_inr_map_snd_apply_mk
    {v : V} {φ : Module.Dual k V} (n : ℕ)
    (f : Fin (n + 1) → (Submodule.span k ({v} : Set V)) × LinearMap.ker φ) :
    let L : Submodule k V := Submodule.span k ({v} : Set V)
    let W : Submodule k V := LinearMap.ker φ
    let q := SymmetricPower.map (n + 1) (LinearMap.snd k L W)
    let sec := SymmetricPower.map (n + 1) (LinearMap.inr k L W)
    sec (q (SymmetricPower.mk k (Fin (n + 1)) (L × W) (PiTensorProduct.tprod k f))) =
      SymmetricPower.mk k (Fin (n + 1)) (L × W)
        (PiTensorProduct.tprod k fun i ↦ (0, (f i).2)) := by
  dsimp
  have hsnd :
      SymmetricPower.map (n + 1)
          (LinearMap.snd k (Submodule.span k ({v} : Set V)) (LinearMap.ker φ))
          (SymmetricPower.mk k (Fin (n + 1))
            ((Submodule.span k ({v} : Set V)) × LinearMap.ker φ)
            (PiTensorProduct.tprod k f)) =
        SymmetricPower.mk k (Fin (n + 1)) (LinearMap.ker φ)
          (PiTensorProduct.map
            (fun _ : Fin (n + 1) ↦
              LinearMap.snd k (Submodule.span k ({v} : Set V)) (LinearMap.ker φ))
            (PiTensorProduct.tprod k f)) := by
    rfl
  have hinr :
      SymmetricPower.map (n + 1)
          (LinearMap.inr k (Submodule.span k ({v} : Set V)) (LinearMap.ker φ))
          (SymmetricPower.mk k (Fin (n + 1)) (LinearMap.ker φ)
            (PiTensorProduct.map
              (fun _ : Fin (n + 1) ↦
                LinearMap.snd k (Submodule.span k ({v} : Set V)) (LinearMap.ker φ))
              (PiTensorProduct.tprod k f))) =
        SymmetricPower.mk k (Fin (n + 1))
          ((Submodule.span k ({v} : Set V)) × LinearMap.ker φ)
          (PiTensorProduct.map
            (fun _ : Fin (n + 1) ↦
              LinearMap.inr k (Submodule.span k ({v} : Set V)) (LinearMap.ker φ))
            (PiTensorProduct.map
              (fun _ : Fin (n + 1) ↦
                LinearMap.snd k (Submodule.span k ({v} : Set V)) (LinearMap.ker φ))
              (PiTensorProduct.tprod k f))) := by
    rfl
  -- First apply `Sym(snd)` to keep only the `W`-coordinates of the pure generator.
  rw [hsnd]
  -- Then reinsert those quotient-side coordinates by `Sym(inr)`.
  rw [hinr]
  simp [PiTensorProduct.map_tprod, LinearMap.inr]

/-- Helper for Exercise 9-9.1-3: each split-model coordinate differs from its pure-`W`
projection by a vector lying entirely in the line summand `L × 0`. -/
private theorem splitModel_sub_projected_coord_eq_inl
    {v : V} {φ : Module.Dual k V} (n : ℕ)
    (f : Fin (n + 1) → (Submodule.span k ({v} : Set V)) × LinearMap.ker φ)
    (i : Fin (n + 1)) :
    f i - (0, (f i).2) =
      LinearMap.inl k (Submodule.span k ({v} : Set V)) (LinearMap.ker φ) ((f i).1) := by
  -- This is the coordinatewise decomposition behind the forthcoming telescoping argument.
  ext <;> simp [LinearMap.inl]

/-- Helper for Exercise 9-9.1-3: the split-model projector `id - Sym(inr) ∘ Sym(snd)` fixes every
element of `ker(Sym(snd))`. -/
private theorem symmetricPower_split_projector_eq_self_of_mem_ker
    {v : V} {φ : Module.Dual k V} (hφ : φ v = 1) (n : ℕ) :
    let L : Submodule k V := Submodule.span k ({v} : Set V)
    let W : Submodule k V := LinearMap.ker φ
    let q := SymmetricPower.map (n + 1) (LinearMap.snd k L W)
    let sec := SymmetricPower.map (n + 1) (LinearMap.inr k L W)
    let P := LinearMap.id - sec.comp q
    ∀ x,
      x ∈ LinearMap.ker q →
        P x = x := by
  dsimp
  intro x hx
  have hx0 :
      SymmetricPower.map (n + 1)
          (LinearMap.snd k (Submodule.span k ({v} : Set V)) (LinearMap.ker φ)) x = 0 := by
    simpa [LinearMap.mem_ker] using hx
  -- On the kernel, the correction term `Sym(inr) (Sym(snd) x)` vanishes.
  simp [hx0]

/-- Helper for Exercise 9-9.1-3: once the explicit split-model projector has image in Serre's
first filtration piece, the kernel of `Sym(snd)` is exactly that filtration piece. -/
private theorem symmetricPower_first_stage_exact_split_via_projector
    {v : V} {φ : Module.Dual k V} (hφ : φ v = 1) (n : ℕ)
    (hprojector :
      let L : Submodule k V := Submodule.span k ({v} : Set V)
      let W : Submodule k V := LinearMap.ker φ
      let lineVec : L × W :=
        (⟨v, Submodule.subset_span (by simp : v ∈ ({v} : Set V))⟩, 0)
      let q := SymmetricPower.map (n + 1) (LinearMap.snd k L W)
      let sec := SymmetricPower.map (n + 1) (LinearMap.inr k L W)
      let P := LinearMap.id - sec.comp q
      LinearMap.range P ≤ LinearMap.range (symmetricPower_insert_left (k := k) n lineVec)) :
    let L : Submodule k V := Submodule.span k ({v} : Set V)
    let W : Submodule k V := LinearMap.ker φ
    let lineVec : L × W :=
      (⟨v, Submodule.subset_span (by simp : v ∈ ({v} : Set V))⟩, 0)
    LinearMap.ker (SymmetricPower.map (n + 1) (LinearMap.snd k L W)) =
      LinearMap.range (symmetricPower_insert_left (k := k) n lineVec) := by
  dsimp at hprojector ⊢
  apply le_antisymm
  · intro x hx
    let P :
        SymmetricPower k (Fin (n + 1))
            ((Submodule.span k ({v} : Set V)) × LinearMap.ker φ) →ₗ[k]
          SymmetricPower k (Fin (n + 1))
            ((Submodule.span k ({v} : Set V)) × LinearMap.ker φ) :=
      LinearMap.id -
        (SymmetricPower.map (n + 1)
          (LinearMap.inr k (Submodule.span k ({v} : Set V)) (LinearMap.ker φ))).comp
        (SymmetricPower.map (n + 1)
          (LinearMap.snd k (Submodule.span k ({v} : Set V)) (LinearMap.ker φ))
    )
    have hxP :
        P x = x := by
      simpa [P] using
        symmetricPower_split_projector_eq_self_of_mem_ker
          (k := k) (V := V) (v := v) (φ := φ) hφ n x hx
    have hxRange : P x ∈ LinearMap.range P := ⟨x, rfl⟩
    -- Every kernel element is fixed by the projector, so the projector-image inclusion already
    -- places it inside the first filtration piece.
    simpa [hxP] using hprojector hxRange
  · -- The easy inclusion was already isolated before introducing the projector.
    exact
      symmetricPower_insert_left_range_le_ker_map_snd
        (k := k) (V := V) (v := v) (φ := φ) hφ n

/-- Helper for Exercise 9-9.1-3: the remaining split-model multilinear step is that the explicit
projector `id - Sym(inr) ∘ Sym(snd)` lands inside Serre's first filtration piece. -/
private theorem symmetricPower_split_projector_range_le_insert_left
    {v : V} {φ : Module.Dual k V} (hφ : φ v = 1) (n : ℕ) :
    let L : Submodule k V := Submodule.span k ({v} : Set V)
    let W : Submodule k V := LinearMap.ker φ
    let lineVec : L × W :=
      (⟨v, Submodule.subset_span (by simp : v ∈ ({v} : Set V))⟩, 0)
    let q := SymmetricPower.map (n + 1) (LinearMap.snd k L W)
    let sec := SymmetricPower.map (n + 1) (LinearMap.inr k L W)
    let P := LinearMap.id - sec.comp q
    LinearMap.range P ≤ LinearMap.range (symmetricPower_insert_left (k := k) n lineVec) := by
  dsimp
  let L : Submodule k V := Submodule.span k ({v} : Set V)
  let W : Submodule k V := LinearMap.ker φ
  let lineVec : L × W :=
    (⟨v, Submodule.subset_span (by simp : v ∈ ({v} : Set V))⟩, 0)
  let q := SymmetricPower.map (n + 1) (LinearMap.snd k L W)
  let sec := SymmetricPower.map (n + 1) (LinearMap.inr k L W)
  let P :
      SymmetricPower k (Fin (n + 1)) (L × W) →ₗ[k]
        SymmetricPower k (Fin (n + 1)) (L × W) :=
    LinearMap.id - sec.comp q
  let Q :
      SymmetricPower k (Fin (n + 1)) (L × W) →ₗ[k]
        (SymmetricPower k (Fin (n + 1)) (L × W) ⧸
          LinearMap.range (symmetricPower_insert_left (k := k) n lineVec)) :=
    Submodule.mkQ (LinearMap.range (symmetricPower_insert_left (k := k) n lineVec))
  have hcomp_mk :
      ((Q.comp P).comp (SymmetricPower.mk k (Fin (n + 1)) (L × W))) = 0 := by
    apply LinearMap.ext
    intro x
    refine PiTensorProduct.induction_on x ?_ ?_
    · intro r f
      let projected : Fin (n + 1) → L × W := fun i ↦ (0, (f i).2)
      let replace : Finset (Fin (n + 1)) → Fin (n + 1) → L × W :=
        fun s i ↦ if i ∈ s then projected i else f i
      have hstep :
          ∀ s : Finset (Fin (n + 1)), ∀ i : Fin (n + 1), i ∉ s →
            Q (SymmetricPower.mk k (Fin (n + 1)) (L × W)
                (PiTensorProduct.tprod k (replace s))) =
              Q (SymmetricPower.mk k (Fin (n + 1)) (L × W)
                (PiTensorProduct.tprod k (replace (insert i s)))) := by
        intro s i hi
        let g : Fin (n + 1) → L × W := replace s
        let linePart : L × W := LinearMap.inl k L W ((g i).1)
        have hcoord :
            g i = linePart + (0, (g i).2) := by
          -- Split the distinguished coordinate into its line part and its `W`-projection.
          ext <;> simp [linePart, LinearMap.inl]
        have hrewrite :
            Function.update g i (0, (g i).2) = replace (insert i s) := by
          -- Replacing one fresh coordinate by its `W`-projection is exactly the next telescoping
          -- stage.
          funext j
          by_cases hji : j = i
          · subst hji
            simp [g, replace, projected, hi]
          · by_cases hjs : j ∈ s
            · simp [g, replace, projected, hji, hjs]
            · simp [g, replace, projected, hji, hjs]
        have hline_mem :
            SymmetricPower.mk k (Fin (n + 1)) (L × W)
                (PiTensorProduct.tprod k (Function.update g i linePart)) ∈
              LinearMap.range (symmetricPower_insert_left (k := k) n lineVec) := by
          -- Once the updated family has a line factor at `i`, the existing first-stage membership
          -- lemma applies immediately.
          exact
            symmetricPower_mk_mem_range_insert_left_of_exists_mem_range_inl
              (k := k) (V := V) (v := v) (φ := φ) hφ n
              (Function.update g i linePart)
              ⟨i, ⟨(g i).1, by simp [linePart, LinearMap.inl]⟩⟩
        have hline_zero :
            Q (SymmetricPower.mk k (Fin (n + 1)) (L × W)
                (PiTensorProduct.tprod k (Function.update g i linePart))) = 0 := by
          -- Modding out by `range(insert_left)` kills every summand with a line factor.
          rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
          exact hline_mem
        have hupdate_sum :
            replace s = Function.update g i (linePart + (0, (g i).2)) := by
          -- Before using multilinearity, rewrite the `i`th coordinate as the sum of its line and
          -- `W` parts.
          funext j
          by_cases hji : j = i
          · subst hji
            simpa [g] using hcoord
          · simpa [g, Function.update, hji]
        -- Replace one coordinate by the decomposition `line part + W-part` and kill the line
        -- summand in the quotient.
        calc
          Q (SymmetricPower.mk k (Fin (n + 1)) (L × W)
              (PiTensorProduct.tprod k (replace s))) =
            Q (SymmetricPower.mk k (Fin (n + 1)) (L × W)
              (PiTensorProduct.tprod k (Function.update g i (linePart + (0, (g i).2))))) := by
                rw [hupdate_sum]
          _ =
            Q (SymmetricPower.mk k (Fin (n + 1)) (L × W)
              (PiTensorProduct.tprod k (Function.update g i linePart))) +
              Q (SymmetricPower.mk k (Fin (n + 1)) (L × W)
                (PiTensorProduct.tprod k (Function.update g i (0, (g i).2)))) := by
                  change
                    Q (SymmetricPower.tprod k (ι := Fin (n + 1)) (M := L × W)
                      (Function.update g i (linePart + (0, (g i).2)))) =
                      Q (SymmetricPower.tprod k (ι := Fin (n + 1)) (M := L × W)
                        (Function.update g i linePart)) +
                        Q (SymmetricPower.tprod k (ι := Fin (n + 1)) (M := L × W)
                          (Function.update g i (0, (g i).2)))
                  rw [MultilinearMap.map_update_add, map_add]
          _ =
            Q (SymmetricPower.mk k (Fin (n + 1)) (L × W)
              (PiTensorProduct.tprod k (Function.update g i (0, (g i).2)))) := by
                rw [hline_zero, zero_add]
          _ =
            Q (SymmetricPower.mk k (Fin (n + 1)) (L × W)
              (PiTensorProduct.tprod k (replace (insert i s)))) := by
                rw [hrewrite]
      have hreplace :
          Q (SymmetricPower.mk k (Fin (n + 1)) (L × W) (PiTensorProduct.tprod k f)) =
            Q (SymmetricPower.mk k (Fin (n + 1)) (L × W)
              (PiTensorProduct.tprod k projected)) := by
        have hreplace_all :
            ∀ s : Finset (Fin (n + 1)),
              Q (SymmetricPower.mk k (Fin (n + 1)) (L × W)
                  (PiTensorProduct.tprod k f)) =
                Q (SymmetricPower.mk k (Fin (n + 1)) (L × W)
                  (PiTensorProduct.tprod k (replace s))) := by
          intro s
          induction s using Finset.induction_on with
          | empty =>
              simp [replace]
          | @insert i s hi hs =>
              calc
                Q (SymmetricPower.mk k (Fin (n + 1)) (L × W)
                    (PiTensorProduct.tprod k f)) =
                Q (SymmetricPower.mk k (Fin (n + 1)) (L × W)
                  (PiTensorProduct.tprod k (replace s))) := hs
                _ =
                  Q (SymmetricPower.mk k (Fin (n + 1)) (L × W)
                    (PiTensorProduct.tprod k (replace (insert i s)))) := hstep s i hi
        simpa [replace, projected] using hreplace_all Finset.univ
      have hproj :
          sec (q (SymmetricPower.mk k (Fin (n + 1)) (L × W)
              (PiTensorProduct.tprod k f))) =
            SymmetricPower.mk k (Fin (n + 1)) (L × W)
              (PiTensorProduct.tprod k projected) := by
        -- `Sym(inr) ∘ Sym(snd)` keeps exactly the pure `W`-part of the generator.
        simpa [q, sec, projected] using
          symmetricPower_map_inr_map_snd_apply_mk
            (k := k) (V := V) (v := v) (φ := φ) n f
      have hpure :
          Q (P (SymmetricPower.mk k (Fin (n + 1)) (L × W)
              (PiTensorProduct.tprod k f))) = 0 := by
        -- In the quotient by the first filtration piece, the projector identifies the generator
        -- with its pure `W`-term, so the difference vanishes.
        calc
          Q (P (SymmetricPower.mk k (Fin (n + 1)) (L × W)
              (PiTensorProduct.tprod k f))) =
            Q (SymmetricPower.mk k (Fin (n + 1)) (L × W)
                (PiTensorProduct.tprod k f) -
              sec (q (SymmetricPower.mk k (Fin (n + 1)) (L × W)
                (PiTensorProduct.tprod k f)))) := by
                  simp [P, q, sec]
          _ =
            Q (SymmetricPower.mk k (Fin (n + 1)) (L × W)
                (PiTensorProduct.tprod k f)) -
              Q (sec (q (SymmetricPower.mk k (Fin (n + 1)) (L × W)
                (PiTensorProduct.tprod k f)))) := by
                  rw [map_sub]
          _ =
            Q (SymmetricPower.mk k (Fin (n + 1)) (L × W)
                (PiTensorProduct.tprod k f)) -
              Q (SymmetricPower.mk k (Fin (n + 1)) (L × W)
                (PiTensorProduct.tprod k projected)) := by
                  rw [hproj]
          _ = 0 := by
                rw [hreplace, sub_self]
      simpa [LinearMap.comp_apply, P, q, sec] using congrArg (fun z ↦ r • z) hpure
    · intro x y hx hy
      -- The quotient-projector composite is linear on tensor sums.
      rw [LinearMap.map_add, LinearMap.map_add, hx, hy]
  have hcomp : Q.comp P = 0 := by
    apply LinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ :=
      LinearMap.range_eq_top.mp
        (SymmetricPower.range_mk (R := k) (ι := Fin (n + 1)) (M := L × W)) y
    exact LinearMap.congr_fun hcomp_mk x
  intro y hy
  rcases hy with ⟨x, rfl⟩
  have hyker : P x ∈ LinearMap.ker Q := by
    -- The quotient map annihilates the whole projector image.
    simpa [LinearMap.mem_ker, LinearMap.comp_apply] using LinearMap.congr_fun hcomp x
  simpa [Q, P, q, sec, lineVec, Submodule.ker_mkQ] using hyker

/-- Helper for Exercise 9-9.1-3: transporting the split-model exactness back along the explicit
line-plus-kernel decomposition identifies Serre's ambient first filtration piece with the kernel of
the quotient map on `Sym^(n + 1)(V)`. -/
theorem symmetricPower_first_stage_exact_span_singleton
    {v : V} (hv : v ≠ 0) (n : ℕ) :
    let L : Submodule k V := Submodule.span k ({v} : Set V)
    LinearMap.ker (SymmetricPower.map (n + 1) (Submodule.mkQ L)) =
      LinearMap.range (symmetricPower_insert_left (k := k) n v) := by
  dsimp
  obtain ⟨φ, hφ⟩ := exists_dual_eq_one_of_nonzero (k := k) (V := V) hv
  let L : Submodule k V := Submodule.span k ({v} : Set V)
  let W : Submodule k V := LinearMap.ker φ
  let hCompl : IsCompl L W :=
    span_singleton_isCompl_ker_of_dual_eq_one (k := k) (V := V) hφ
  let eVW : (L × W) ≃ₗ[k] V :=
    span_singleton_ker_dual_prodEquiv (k := k) (V := V) hφ
  let qEquiv : (V ⧸ L) ≃ₗ[k] W :=
    Submodule.quotientEquivOfIsCompl L W hCompl
  let lineVec : L × W :=
    (⟨v, Submodule.subset_span (by simp : v ∈ ({v} : Set V))⟩, 0)
  have htransport :=
    symmetricPower_first_stage_split_transport
      (k := k) (V := V) (v := v) (φ := φ) hφ n
  have hqtransport :
      ((SymmetricPower.map (n + 1) qEquiv.toLinearMap).comp
          ((SymmetricPower.map (n + 1) (Submodule.mkQ L)).comp
            (SymmetricPower.map (n + 1) eVW.toLinearMap)) =
        SymmetricPower.map (n + 1) (LinearMap.snd k L W)) := by
    -- The quotient map becomes `snd` after transporting to the split model.
    simpa [L, W, hCompl, eVW, qEquiv] using htransport.1
  have hinserttransport :
      ((SymmetricPower.map (n + 1) eVW.toLinearMap).comp
          (symmetricPower_insert_left (k := k) n lineVec) =
        (symmetricPower_insert_left (k := k) n v).comp
          (SymmetricPower.map n eVW.toLinearMap)) := by
    -- The split-model insertion by `(v, 0)` transports back to the ambient insertion by `v`.
    simpa [L, W, hCompl, eVW, lineVec] using htransport.2
  have hsplitExact :
      LinearMap.ker (SymmetricPower.map (n + 1) (LinearMap.snd k L W)) =
        LinearMap.range (symmetricPower_insert_left (k := k) n lineVec) := by
    -- The projector argument already proves the exactness statement in the split model.
    simpa [L, W, lineVec] using
      symmetricPower_first_stage_exact_split_via_projector
        (k := k) (V := V) (v := v) (φ := φ) hφ n
        (by
          simpa [L, W, lineVec] using
            symmetricPower_split_projector_range_le_insert_left
              (k := k) (V := V) (v := v) (φ := φ) hφ n)
  apply le_antisymm
  · intro x hx
    let y : SymmetricPower k (Fin (n + 1)) (L × W) :=
      SymmetricPower.map (n + 1) eVW.symm.toLinearMap x
    have hback :
        SymmetricPower.map (n + 1) eVW.toLinearMap y = x := by
      -- Moving to the split model and back by the transported equivalence recovers the input.
      dsimp [y]
      calc
        SymmetricPower.map (n + 1) eVW.toLinearMap
            (SymmetricPower.map (n + 1) eVW.symm.toLinearMap x) =
          SymmetricPower.map (n + 1)
            (eVW.toLinearMap.comp eVW.symm.toLinearMap) x := by
              simpa [LinearMap.comp_apply] using
                (LinearMap.congr_fun
                  (SymmetricPower.map_comp (n + 1) eVW.symm.toLinearMap eVW.toLinearMap)
                  x).symm
        _ =
          SymmetricPower.map (n + 1) (LinearMap.id : V →ₗ[k] V) x := by
            congr
            ext z
            exact eVW.apply_symm_apply z
        _ = x := by simpa using LinearMap.congr_fun (SymmetricPower.map_id (n + 1)) x
    have hyker : y ∈ LinearMap.ker (SymmetricPower.map (n + 1) (LinearMap.snd k L W)) := by
      have hqy := LinearMap.congr_fun hqtransport y
      have hx0 : SymmetricPower.map (n + 1) (Submodule.mkQ L) x = 0 := by
        simpa [LinearMap.mem_ker] using hx
      have hyzero :
          SymmetricPower.map (n + 1) (LinearMap.snd k L W) y = 0 := by
        -- After transporting to the split model, the ambient kernel condition is exactly the
        -- split-model kernel condition.
        calc
          SymmetricPower.map (n + 1) (LinearMap.snd k L W) y =
              SymmetricPower.map (n + 1) qEquiv.toLinearMap
                ((SymmetricPower.map (n + 1) (Submodule.mkQ L))
                  ((SymmetricPower.map (n + 1) eVW.toLinearMap) y)) := by
                    simpa [LinearMap.comp_apply] using hqy.symm
          _ = 0 := by
                rw [hback, hx0, map_zero]
      simpa [LinearMap.mem_ker] using hyzero
    have hyRange : y ∈ LinearMap.range (symmetricPower_insert_left (k := k) n lineVec) := by
      -- The split-model exactness now sends the transported kernel element into the first-stage
      -- image.
      rw [← hsplitExact]
      exact hyker
    rcases hyRange with ⟨z, hz⟩
    refine ⟨SymmetricPower.map n eVW.toLinearMap z, ?_⟩
    -- Transport the split-model insertion back to the ambient insertion.
    calc
      symmetricPower_insert_left (k := k) n v
          (SymmetricPower.map n eVW.toLinearMap z) =
          SymmetricPower.map (n + 1) eVW.toLinearMap
            (symmetricPower_insert_left (k := k) n lineVec z) := by
              simpa [LinearMap.comp_apply] using
                (LinearMap.congr_fun hinserttransport z).symm
      _ = SymmetricPower.map (n + 1) eVW.toLinearMap y := by
            rw [← hz]
      _ = x := hback
  · -- The ambient easy inclusion was already proved directly before the split transport.
    simpa using
      (symmetricPower_insert_left_range_le_ker_mapQ_span_singleton
        (k := k) (V := V) n v)

/-- Helper for Exercise 9-9.1-3: the kernel of the quotient map on `Sym^(n+1)(V)` is stable under
`Sym^(n+1)(A)` once the line `k · v` is `A`-stable. This isolates the quotient-side transport
needed in Serre's first filtration step. -/
private theorem symmetricPower_mapQ_span_singleton_ker_le_comap
    (A : V →ₗ[k] V) (n : ℕ) {v : V} {μ : k} (hμ : A v = μ • v) :
    let L : Submodule k V := Submodule.span k ({v} : Set V)
    let q := SymmetricPower.map (n + 1) (Submodule.mkQ L)
    LinearMap.ker q ≤ (LinearMap.ker q).comap (SymmetricPower.map (n + 1) A) := by
  dsimp
  let L : Submodule k V := Submodule.span k ({v} : Set V)
  let hL : L ≤ L.comap A := span_singleton_le_comap_of_eigenvector (A := A) hμ
  let q : SymmetricPower k (Fin (n + 1)) V →ₗ[k] SymmetricPower k (Fin (n + 1)) (V ⧸ L) :=
    SymmetricPower.map (n + 1) (Submodule.mkQ L)
  have hqcomp :
      (SymmetricPower.map (n + 1) (L.mapQ L A hL)).comp q =
        q.comp (SymmetricPower.map (n + 1) A) := by
    -- Functoriality turns the quotient intertwining on `V` into the same intertwining on
    -- `Sym^(n + 1)(V)`.
    calc
      (SymmetricPower.map (n + 1) (L.mapQ L A hL)).comp q =
          SymmetricPower.map (n + 1) ((L.mapQ L A hL).comp (Submodule.mkQ L)) := by
            symm
            exact SymmetricPower.map_comp (n + 1) (Submodule.mkQ L) (L.mapQ L A hL)
      _ = SymmetricPower.map (n + 1) ((Submodule.mkQ L).comp A) := by
            rw [Submodule.mapQ_mkQ]
      _ = q.comp (SymmetricPower.map (n + 1) A) := by
            exact SymmetricPower.map_comp (n + 1) A (Submodule.mkQ L)
  intro x hx
  have hx0 : q x = 0 := by
    simpa [LinearMap.mem_ker] using hx
  have himage :
      q (SymmetricPower.map (n + 1) A x) = 0 := by
    -- Once the quotient intertwining is known, the image of a kernel vector is still sent to
    -- zero in the quotient.
    calc
      q (SymmetricPower.map (n + 1) A x) =
          (SymmetricPower.map (n + 1) (L.mapQ L A hL)) (q x) := by
            symm
            exact LinearMap.congr_fun hqcomp x
      _ = 0 := by rw [hx0, map_zero]
  simpa [LinearMap.mem_ker] using himage

/-- Helper for Exercise 9-9.1-3: the first-isomorphism equivalence for the quotient map
`Sym^(n+1)(V) → Sym^(n+1)(V / (k · v))` transports the quotient action to the literal symmetric
power of the induced quotient endomorphism. -/
private theorem trace_symmetricPower_mapQ_span_singleton_quotKer_eq
    (A : V →ₗ[k] V) (n : ℕ) {v : V} {μ : k} (hμ : A v = μ • v) :
    let L : Submodule k V := Submodule.span k ({v} : Set V)
    let hL : L ≤ L.comap A := span_singleton_le_comap_of_eigenvector (A := A) hμ
    let q := SymmetricPower.map (n + 1) (Submodule.mkQ L)
    let hker : LinearMap.ker q ≤ (LinearMap.ker q).comap (SymmetricPower.map (n + 1) A) :=
      symmetricPower_mapQ_span_singleton_ker_le_comap
        (k := k) (V := V) (A := A) n (v := v) (μ := μ) hμ
    LinearMap.trace k (SymmetricPower k (Fin (n + 1)) V ⧸ LinearMap.ker q)
        ((LinearMap.ker q).mapQ (LinearMap.ker q) (SymmetricPower.map (n + 1) A) hker) =
      LinearMap.trace k (SymmetricPower k (Fin (n + 1)) (V ⧸ L))
        (SymmetricPower.map (n + 1) (L.mapQ L A hL)) := by
  dsimp
  let L : Submodule k V := Submodule.span k ({v} : Set V)
  let hL : L ≤ L.comap A := span_singleton_le_comap_of_eigenvector (A := A) hμ
  let q : SymmetricPower k (Fin (n + 1)) V →ₗ[k] SymmetricPower k (Fin (n + 1)) (V ⧸ L) :=
    SymmetricPower.map (n + 1) (Submodule.mkQ L)
  let hker :
      LinearMap.ker q ≤ (LinearMap.ker q).comap (SymmetricPower.map (n + 1) A) :=
    symmetricPower_mapQ_span_singleton_ker_le_comap
      (k := k) (V := V) (A := A) n (v := v) (μ := μ) hμ
  have hqsurj : Function.Surjective q := by
    -- Surjectivity is inherited functorially from the base quotient map.
    simpa [q, L] using
      (symmetricPower_mapQ_span_singleton_surjective (k := k) (V := V) n v)
  let e := symmetricPower_mapQ_span_singleton_quotKerEquiv (k := k) (V := V) n v
  have hqcomp :
      (SymmetricPower.map (n + 1) (L.mapQ L A hL)).comp q =
        q.comp (SymmetricPower.map (n + 1) A) := by
    -- The quotient map intertwines the ambient action with the induced action on the quotient.
    calc
      (SymmetricPower.map (n + 1) (L.mapQ L A hL)).comp q =
          SymmetricPower.map (n + 1) ((L.mapQ L A hL).comp (Submodule.mkQ L)) := by
            symm
            exact SymmetricPower.map_comp (n + 1) (Submodule.mkQ L) (L.mapQ L A hL)
      _ = SymmetricPower.map (n + 1) ((Submodule.mkQ L).comp A) := by
            rw [Submodule.mapQ_mkQ]
      _ = q.comp (SymmetricPower.map (n + 1) A) := by
            exact SymmetricPower.map_comp (n + 1) A (Submodule.mkQ L)
  have hconj :
      e.conj ((LinearMap.ker q).mapQ (LinearMap.ker q) (SymmetricPower.map (n + 1) A) hker) =
        SymmetricPower.map (n + 1) (L.mapQ L A hL) := by
    -- Evaluate both sides on the surjective image of the quotient map `q`.
    ext z
    obtain ⟨y, rfl⟩ := hqsurj z
    change
      e (((LinearMap.ker q).mapQ (LinearMap.ker q) (SymmetricPower.map (n + 1) A) hker)
        (e.symm (q y))) =
        (SymmetricPower.map (n + 1) (L.mapQ L A hL)) (q y)
    have hsymm : e.symm (q y) = Submodule.Quotient.mk y := by
      change
        (((SymmetricPower.map (n + 1) (Submodule.mkQ L)).quotKerEquivOfSurjective hqsurj).symm
          ((SymmetricPower.map (n + 1) (Submodule.mkQ L)) y)) =
            Submodule.Quotient.mk y
      exact
        LinearMap.quotKerEquivOfSurjective_symm_apply
          (SymmetricPower.map (n + 1) (Submodule.mkQ L)) hqsurj y
    rw [hsymm]
    calc
      e (((LinearMap.ker q).mapQ (LinearMap.ker q) (SymmetricPower.map (n + 1) A) hker)
          (Submodule.Quotient.mk y)) =
          e (Submodule.Quotient.mk (SymmetricPower.map (n + 1) A y)) := by
            rw [Submodule.mapQ_apply]
      _ = q (SymmetricPower.map (n + 1) A y) := by
            simp [e, symmetricPower_mapQ_span_singleton_quotKerEquiv,
              symmetricPower_mapQ_quotKerEquiv, q, L]
      _ = (SymmetricPower.map (n + 1) (L.mapQ L A hL)) (q y) := by
            symm
            exact LinearMap.congr_fun hqcomp y
  -- After transporting along the quotient-by-kernel equivalence, the traces agree by conjugacy.
  rw [← LinearMap.trace_conj'
    ((LinearMap.ker q).mapQ (LinearMap.ker q) (SymmetricPower.map (n + 1) A) hker) e, hconj]

/-- Helper for Exercise 9-9.1-3: in the split model `L × W`, the exact first-stage sequence and
the multichoose dimension formula force insertion by the distinguished line generator to be
injective. This is the source-faithful rank argument behind Serre's first filtration step. -/
private theorem symmetricPower_insert_left_split_injective_of_exact_and_finrank
    {v : V} {φ : Module.Dual k V} (hφ : φ v = 1) (n : ℕ) :
    let L : Submodule k V := Submodule.span k ({v} : Set V)
    let W : Submodule k V := LinearMap.ker φ
    let lineVec : L × W :=
      (⟨v, Submodule.subset_span (by simp : v ∈ ({v} : Set V))⟩, 0)
    Function.Injective (symmetricPower_insert_left (k := k) n lineVec) := by
  dsimp
  let L : Submodule k V := Submodule.span k ({v} : Set V)
  let W : Submodule k V := LinearMap.ker φ
  let lineVec : L × W :=
    (⟨v, Submodule.subset_span (by simp : v ∈ ({v} : Set V))⟩, 0)
  let i :
      SymmetricPower k (Fin n) (L × W) →ₗ[k]
        SymmetricPower k (Fin (n + 1)) (L × W) :=
    symmetricPower_insert_left (k := k) n lineVec
  let q :
      SymmetricPower k (Fin (n + 1)) (L × W) →ₗ[k]
        SymmetricPower k (Fin (n + 1)) W :=
    SymmetricPower.map (n + 1) (LinearMap.snd k L W)
  have hv : v ≠ 0 := by
    intro hv
    simpa [hv] using hφ
  have hsplitExact : LinearMap.ker q = LinearMap.range i := by
    -- Route correction: the split exactness is already proved by the projector argument, so the
    -- remaining work is only the finrank comparison turning that exact sequence into injectivity.
    simpa [q, i, L, W, lineVec] using
      (symmetricPower_first_stage_exact_split_via_projector
        (k := k) (V := V) (v := v) (φ := φ) hφ n
        (symmetricPower_split_projector_range_le_insert_left
          (k := k) (V := V) (v := v) (φ := φ) hφ n))
  have hqsurj : Function.Surjective q := by
    let sec :
        SymmetricPower k (Fin (n + 1)) W →ₗ[k]
          SymmetricPower k (Fin (n + 1)) (L × W) :=
      SymmetricPower.map (n + 1) (LinearMap.inr k L W)
    -- `Sym(snd)` is surjective because `snd` has the obvious section `inr`.
    intro y
    refine ⟨sec y, ?_⟩
    simpa [q, sec, L, W] using
      LinearMap.congr_fun
        (symmetricPower_map_snd_comp_map_inr_eq_id
          (k := k) (V := V) (v := v) (φ := φ) hφ n)
        y
  have hkerDim :
      Module.finrank k (LinearMap.ker q) =
        Module.finrank k (SymmetricPower k (Fin n) (L × W)) := by
    have hqRange : LinearMap.range q = ⊤ := LinearMap.range_eq_top.mpr hqsurj
    have hqRangeDim :
        Module.finrank k (LinearMap.range q) =
          Module.finrank k (SymmetricPower k (Fin (n + 1)) W) := by
      rw [hqRange, finrank_top]
    have hrankNull :
        Module.finrank k (SymmetricPower k (Fin (n + 1)) W) +
          Module.finrank k (LinearMap.ker q) =
        Module.finrank k (SymmetricPower k (Fin (n + 1)) (L × W)) := by
      -- Surjectivity replaces the range term in rank-nullity by the whole quotient-side owner.
      calc
        Module.finrank k (SymmetricPower k (Fin (n + 1)) W) +
            Module.finrank k (LinearMap.ker q) =
          Module.finrank k (LinearMap.range q) +
            Module.finrank k (LinearMap.ker q) := by
              rw [hqRangeDim]
        _ = Module.finrank k (SymmetricPower k (Fin (n + 1)) (L × W)) := by
              simpa using
                (LinearMap.finrank_range_add_finrank_ker q)
    have hsplitDim :
        Module.finrank k (SymmetricPower k (Fin (n + 1)) (L × W)) =
          Module.finrank k (SymmetricPower k (Fin (n + 1)) W) +
            Module.finrank k (SymmetricPower k (Fin n) (L × W)) := by
      have hLdim : Module.finrank k L = 1 := by
        -- The distinguished line factor contributes exactly one dimension.
        simpa [L] using finrank_span_singleton hv
      have hcodomainDim :
          (Module.finrank k W).multichoose (n + 1) =
            Module.finrank k (SymmetricPower k (Fin (n + 1)) W) := by
        symm
        simpa using
          finrank_symmetricPower_eq_multichoose_all
            (k := k) (V := W) (n := n + 1)
      have hdomainDim :
          ((Module.finrank k W) + 1).multichoose n =
            Module.finrank k (SymmetricPower k (Fin n) (L × W)) := by
        calc
          ((Module.finrank k W) + 1).multichoose n =
              (Module.finrank k (L × W)).multichoose n := by
                rw [Module.finrank_prod, hLdim, Nat.add_comm]
          _ = Module.finrank k (SymmetricPower k (Fin n) (L × W)) := by
                symm
                simpa using
                  finrank_symmetricPower_eq_multichoose_all
                    (k := k) (V := L × W) (n := n)
      -- Compare the three symmetric-power owners by the multichoose formula and Pascal's rule.
      calc
        Module.finrank k (SymmetricPower k (Fin (n + 1)) (L × W)) =
            (Module.finrank k (L × W)).multichoose (n + 1) := by
              simpa using
                finrank_symmetricPower_eq_multichoose_all
                  (k := k) (V := L × W) (n := n + 1)
        _ = ((Module.finrank k W) + 1).multichoose (n + 1) := by
              rw [Module.finrank_prod, hLdim, Nat.add_comm]
        _ = (Module.finrank k W).multichoose (n + 1) +
              ((Module.finrank k W) + 1).multichoose n := by
              rw [Nat.multichoose_succ_succ]
        _ = Module.finrank k (SymmetricPower k (Fin (n + 1)) W) +
              Module.finrank k (SymmetricPower k (Fin n) (L × W)) := by
              rw [hcodomainDim, hdomainDim]
    omega
  have hrangeDim :
      Module.finrank k (LinearMap.range i) =
        Module.finrank k (SymmetricPower k (Fin n) (L × W)) := by
    -- Exactness identifies the first-stage range with the quotient kernel.
    calc
      Module.finrank k (LinearMap.range i) =
          Module.finrank k (LinearMap.ker q) := by
            rw [← hsplitExact]
      _ = Module.finrank k (SymmetricPower k (Fin n) (L × W)) := hkerDim
  have hinjRange : Function.Injective i.rangeRestrict := by
    -- The range-restricted map is already surjective, and the finrank computation shows that the
    -- source and target have the same dimension.
    exact
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (K := k)
        (V := SymmetricPower k (Fin n) (L × W))
        (V₂ := LinearMap.range i)
        hrangeDim.symm
        (f := i.rangeRestrict)).2
        (LinearMap.surjective_rangeRestrict i)
  -- Forgetting the subtype on the range-restricted map gives injectivity of the original
  -- insertion map.
  intro x y hxy
  apply hinjRange
  exact Subtype.ext hxy

/-- Helper for Exercise 9-9.1-3: once Serre's first-step insertion map is known to be injective,
its image identifies with `Sym^n(V)`, so the restricted action on that image is conjugate to
`μ • Sym^n(A)`. -/
private theorem trace_restrict_symmetricPower_insert_left_range_eq_mul_trace_of_injective
    (A : V →ₗ[k] V) (n : ℕ) {v : V} {μ : k} (hμ : A v = μ • v)
    (hinj : Function.Injective (symmetricPower_insert_left (k := k) n v)) :
    let S := LinearMap.range (symmetricPower_insert_left (k := k) n v)
    let hS : S ≤ S.comap (SymmetricPower.map (n + 1) A) :=
      symmetricPower_insert_left_range_le_comap
        (k := k) (V := V) (A := A) n (v := v) (μ := μ) hμ
    LinearMap.trace k S ((SymmetricPower.map (n + 1) A).restrict hS) =
      μ * LinearMap.trace k (SymmetricPower k (Fin n) V) (SymmetricPower.map n A) := by
  dsimp
  let i := symmetricPower_insert_left (k := k) n v
  let S := LinearMap.range i
  let hS : S ≤ S.comap (SymmetricPower.map (n + 1) A) :=
    symmetricPower_insert_left_range_le_comap
      (k := k) (V := V) (A := A) n (v := v) (μ := μ) hμ
  let e : SymmetricPower k (Fin n) V ≃ₗ[k] S := LinearEquiv.ofInjective i hinj
  have hconj :
      e.conj (μ • SymmetricPower.map n A) =
        (SymmetricPower.map (n + 1) A).restrict hS := by
    ext x
    rcases x with ⟨x, hx⟩
    obtain ⟨y, hy⟩ := e.surjective ⟨x, hx⟩
    have hyVal : i y = x := by
      -- The range equivalence is defined from the insertion map itself.
      simpa [e, i] using congrArg Subtype.val hy
    have hySymm : e.symm ⟨x, hx⟩ = y := by
      -- A surjective witness in the domain is the actual inverse image under the range equivalence.
      apply e.injective
      simpa using hy.symm
    -- Evaluate the transported restriction on a chosen preimage and use the intertwining identity.
    change i ((μ • SymmetricPower.map n A) (e.symm ⟨x, hx⟩)) =
      (SymmetricPower.map (n + 1) A) x
    rw [hySymm, ← hyVal]
    exact
      LinearMap.congr_fun
        (symmetricPower_insert_left_intertwines
          (k := k) (A := A) n (v := v) (μ := μ) hμ)
        y |>.symm
  -- After identifying the invariant range with `Sym^n(V)`, the trace is just the scalar multiple
  -- of the trace of `Sym^n(A)`.
  calc
    LinearMap.trace k S ((SymmetricPower.map (n + 1) A).restrict hS) =
        LinearMap.trace k (SymmetricPower k (Fin n) V) (μ • SymmetricPower.map n A) := by
          rw [← LinearMap.trace_conj' (μ • SymmetricPower.map n A) e, hconj]
    _ =
        μ * LinearMap.trace k (SymmetricPower k (Fin n) V) (SymmetricPower.map n A) := by
          simpa [smul_eq_mul] using
            (LinearMap.trace k (SymmetricPower k (Fin n) V)).map_smul μ
              (SymmetricPower.map n A)

/-- Helper for Exercise 9-9.1-3: the transported first-stage exactness already gives the standard
trace decomposition of `Sym^(n + 1)(A)` into the kernel of the quotient map and the quotient
contribution on `V / (k · v)`. -/
private theorem trace_symmetricPower_map_split_ker_span_singleton
    (A : V →ₗ[k] V) {v : V} {μ : k} (hμ : A v = μ • v)
    (n : ℕ) :
    let L : Submodule k V := Submodule.span k ({v} : Set V)
    let hL : L ≤ L.comap A := span_singleton_le_comap_of_eigenvector (A := A) hμ
    let q : SymmetricPower k (Fin (n + 1)) V →ₗ[k] SymmetricPower k (Fin (n + 1)) (V ⧸ L) :=
      SymmetricPower.map (n + 1) (Submodule.mkQ L)
    let hker : LinearMap.ker q ≤ (LinearMap.ker q).comap (SymmetricPower.map (n + 1) A) :=
      symmetricPower_mapQ_span_singleton_ker_le_comap
        (k := k) (V := V) (A := A) n (v := v) (μ := μ) hμ
    LinearMap.trace k (SymmetricPower k (Fin (n + 1)) V) (SymmetricPower.map (n + 1) A) =
      LinearMap.trace k (LinearMap.ker q) ((SymmetricPower.map (n + 1) A).restrict hker) +
        LinearMap.trace k (SymmetricPower k (Fin (n + 1)) (V ⧸ L))
          (SymmetricPower.map (n + 1) (L.mapQ L A hL)) := by
  dsimp
  let L : Submodule k V := Submodule.span k ({v} : Set V)
  let hL : L ≤ L.comap A := span_singleton_le_comap_of_eigenvector (A := A) hμ
  let q : SymmetricPower k (Fin (n + 1)) V →ₗ[k] SymmetricPower k (Fin (n + 1)) (V ⧸ L) :=
    SymmetricPower.map (n + 1) (Submodule.mkQ L)
  let hker : LinearMap.ker q ≤ (LinearMap.ker q).comap (SymmetricPower.map (n + 1) A) :=
    symmetricPower_mapQ_span_singleton_ker_le_comap
      (k := k) (V := V) (A := A) n (v := v) (μ := μ) hμ
  have hquotTrace :
      LinearMap.trace k (SymmetricPower k (Fin (n + 1)) V ⧸ LinearMap.ker q)
          ((LinearMap.ker q).mapQ (LinearMap.ker q) (SymmetricPower.map (n + 1) A) hker) =
        LinearMap.trace k (SymmetricPower k (Fin (n + 1)) (V ⧸ L))
          (SymmetricPower.map (n + 1) (L.mapQ L A hL)) := by
    -- The quotient action is already transported to the literal symmetric power of
    -- `V / (k · v)` by the quotient-by-kernel equivalence.
    simpa [L, hL, q, hker] using
      trace_symmetricPower_mapQ_span_singleton_quotKer_eq
        (k := k) (V := V) (A := A) n (v := v) (μ := μ) hμ
  -- With the quotient term transported, the ambient trace split is the standard invariant-subspace
  -- trace decomposition applied to the stable kernel of the quotient map.
  calc
    LinearMap.trace k (SymmetricPower k (Fin (n + 1)) V) (SymmetricPower.map (n + 1) A) =
        LinearMap.trace k (LinearMap.ker q) ((SymmetricPower.map (n + 1) A).restrict hker) +
          LinearMap.trace k (SymmetricPower k (Fin (n + 1)) V ⧸ LinearMap.ker q)
            ((LinearMap.ker q).mapQ (LinearMap.ker q) (SymmetricPower.map (n + 1) A) hker) := by
              simpa [q, hker] using
                trace_eq_trace_restrict_add_trace_mapQ
                  (k := k) (V := SymmetricPower k (Fin (n + 1)) V)
                  (f := SymmetricPower.map (n + 1) A) (LinearMap.ker q) hker
    _ =
        LinearMap.trace k (LinearMap.ker q) ((SymmetricPower.map (n + 1) A).restrict hker) +
          LinearMap.trace k (SymmetricPower k (Fin (n + 1)) (V ⧸ L))
            (SymmetricPower.map (n + 1) (L.mapQ L A hL)) := by
              rw [hquotTrace]

/-- Helper for Exercise 9-9.1-3: if two stable submodules are definitionally identified, then the
trace of the restricted endomorphism transports across that identification. -/
private theorem trace_restrict_eq_of_submodule_eq
    {M : Type w} [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    (f : M →ₗ[k] M) {W W' : Submodule k M} (hWW' : W = W')
    (hW : W ≤ W.comap f) (hW' : W' ≤ W'.comap f) :
    LinearMap.trace k W (f.restrict hW) =
      LinearMap.trace k W' (f.restrict hW') := by
  subst hWW'
  have hh : hW = hW' := Subsingleton.elim _ _
  cases hh
  rfl

/-- Helper for Exercise 9-9.1-3: this is the single missing first-step filtration identity from
Serre's source proof. It isolates the contribution of the eigenline `k · v` and the quotient
`V/(k · v)` in degree `n + 1`. -/
theorem trace_symmetricPower_map_step_span_singleton_mapQ
    [IsAlgClosed k] (A : V →ₗ[k] V) {v : V} {μ : k} (hv : v ≠ 0) (hμ : A v = μ • v)
    (n : ℕ) :
    let L : Submodule k V := Submodule.span k ({v} : Set V)
    let hL : L ≤ L.comap A := span_singleton_le_comap_of_eigenvector (A := A) hμ
    LinearMap.trace k (SymmetricPower k (Fin (n + 1)) V) (SymmetricPower.map (n + 1) A) =
      μ * LinearMap.trace k (SymmetricPower k (Fin n) V) (SymmetricPower.map n A) +
        LinearMap.trace k (SymmetricPower k (Fin (n + 1)) (V ⧸ L))
          (SymmetricPower.map (n + 1) (L.mapQ L A hL)) := by
  -- Route correction: the old statement omitted `hv : v ≠ 0`, but for `v = 0` the quotient owner
  -- is just `V` again, so the displayed recurrence is false in general. After repairing the
  -- helper to the genuine eigenline case, the only remaining work is Serre's first filtration
  -- step on `Sym^(n+1)(V)`.
  -- TODO: the quotient side is now packaged by `symmetricPower_mapQ_quotKerEquiv`; the remaining
  -- source-faithful gap is to work in the split model `(k · v) × ker φ`, where the just-added
  -- transport lemmas `quotient_span_singleton_eq_snd_comp_prodEquiv_symm` and
  -- `quotient_span_singleton_comp_prodEquiv_eq_snd` identify the quotient map with `snd`.
  -- The remaining missing step is the split-model exactness
  -- `ker (SymmetricPower.map (n + 1) snd) = range (symmetricPower_insert_left n (v, 0))`.
  -- The forward inclusion is now isolated by
  -- `symmetricPower_insert_left_range_le_ker_map_snd`; only the reverse inclusion on generators
  -- is still missing. The new generator lemmas
  -- `symmetricPower_mk_mem_range_insert_left_of_exists_eq` and
  -- `symmetricPower_mk_mem_range_insert_left_of_exists_eq_smul` reduce that reverse inclusion to
  -- showing that every split-model summand with a line factor is a scalar multiple of the
  -- distinguished line generator. Once that reverse inclusion is proved, the existing range stability lemma
  -- `symmetricPower_insert_left_range_le_comap`, the quotient equivalence
  -- `symmetricPower_mapQ_span_singleton_quotKerEquiv`, and the intertwining identity
  -- `symmetricPower_insert_left_intertwines` finish the trace decomposition by the standard
  -- `trace_eq_trace_restrict_add_trace_mapQ` split.
  let L : Submodule k V := Submodule.span k ({v} : Set V)
  let hL : L ≤ L.comap A := span_singleton_le_comap_of_eigenvector (A := A) hμ
  let S := LinearMap.range (symmetricPower_insert_left (k := k) n v)
  let hS : S ≤ S.comap (SymmetricPower.map (n + 1) A) :=
    symmetricPower_insert_left_range_le_comap
      (k := k) (V := V) (A := A) n (v := v) (μ := μ) hμ
  let q : SymmetricPower k (Fin (n + 1)) V →ₗ[k] SymmetricPower k (Fin (n + 1)) (V ⧸ L) :=
    SymmetricPower.map (n + 1) (Submodule.mkQ L)
  have hfirstStageExact : LinearMap.ker q = S := by
    -- Route correction: the transport from the split model back to the ambient span-singleton
    -- filtration is now closed as a standalone lemma.
    simpa [L, q, S] using
      (symmetricPower_first_stage_exact_span_singleton (k := k) (V := V) (v := v) hv n)
  have hsplitTrace :
      LinearMap.trace k (SymmetricPower k (Fin (n + 1)) V) (SymmetricPower.map (n + 1) A) =
        LinearMap.trace k (LinearMap.ker q)
            ((SymmetricPower.map (n + 1) A).restrict
              (symmetricPower_mapQ_span_singleton_ker_le_comap
                (k := k) (V := V) (A := A) n (v := v) (μ := μ) hμ)) +
          LinearMap.trace k (SymmetricPower k (Fin (n + 1)) (V ⧸ L))
            (SymmetricPower.map (n + 1) (L.mapQ L A hL)) := by
    -- Route correction: the ambient trace split is now a standalone helper, so the remaining gap
    -- is only to transport the kernel restriction to `range(insert_left)` and identify it with
    -- `μ • Sym^n(A)`.
    simpa [L, hL, q] using
      trace_symmetricPower_map_split_ker_span_singleton
        (k := k) (V := V) (A := A) (v := v) (μ := μ) hμ n
  have hrestrictTransport :
      LinearMap.trace k (LinearMap.ker q)
          ((SymmetricPower.map (n + 1) A).restrict
            (symmetricPower_mapQ_span_singleton_ker_le_comap
              (k := k) (V := V) (A := A) n (v := v) (μ := μ) hμ)) =
        LinearMap.trace k S ((SymmetricPower.map (n + 1) A).restrict hS) := by
    -- The transported exactness identifies the kernel owner with the insertion-range owner, so
    -- the restriction trace can be rewritten without changing its value.
    exact
      trace_restrict_eq_of_submodule_eq
        (k := k) (f := SymmetricPower.map (n + 1) A) (hWW' := hfirstStageExact)
        (hW :=
          symmetricPower_mapQ_span_singleton_ker_le_comap
            (k := k) (V := V) (A := A) n (v := v) (μ := μ) hμ)
        (hW' := hS)
  have hsplitTraceRange :
      LinearMap.trace k (SymmetricPower k (Fin (n + 1)) V) (SymmetricPower.map (n + 1) A) =
        LinearMap.trace k S ((SymmetricPower.map (n + 1) A).restrict hS) +
          LinearMap.trace k (SymmetricPower k (Fin (n + 1)) (V ⧸ L))
            (SymmetricPower.map (n + 1) (L.mapQ L A hL)) := by
    -- After transporting the kernel summand to the canonical first-stage range owner, the only
    -- missing source-faithful step is the conjugacy with `μ • Sym^n(A)`.
    calc
      LinearMap.trace k (SymmetricPower k (Fin (n + 1)) V) (SymmetricPower.map (n + 1) A) =
          LinearMap.trace k (LinearMap.ker q)
              ((SymmetricPower.map (n + 1) A).restrict
                (symmetricPower_mapQ_span_singleton_ker_le_comap
                  (k := k) (V := V) (A := A) n (v := v) (μ := μ) hμ)) +
            LinearMap.trace k (SymmetricPower k (Fin (n + 1)) (V ⧸ L))
              (SymmetricPower.map (n + 1) (L.mapQ L A hL)) := hsplitTrace
      _ =
          LinearMap.trace k S ((SymmetricPower.map (n + 1) A).restrict hS) +
            LinearMap.trace k (SymmetricPower k (Fin (n + 1)) (V ⧸ L))
              (SymmetricPower.map (n + 1) (L.mapQ L A hL)) := by
                rw [hrestrictTransport]
  obtain ⟨φ, hφ⟩ := exists_dual_eq_one_of_nonzero (k := k) (V := V) hv
  have hinjAmbient :
      Function.Injective (symmetricPower_insert_left (k := k) n v) := by
    have hinjSplit :
        let L : Submodule k V := Submodule.span k ({v} : Set V)
        let W : Submodule k V := LinearMap.ker φ
        let lineVec : L × W :=
          (⟨v, Submodule.subset_span (by simp : v ∈ ({v} : Set V))⟩, 0)
        Function.Injective (symmetricPower_insert_left (k := k) n lineVec) := by
      -- The split-model exactness plus the multichoose finrank count identifies the first
      -- filtration piece with a copy of `Sym^n(L × W)`, forcing insertion by `(v, 0)` to be
      -- injective.
      exact
        symmetricPower_insert_left_split_injective_of_exact_and_finrank
          (k := k) (V := V) (v := v) (φ := φ) hφ n
    -- The ambient injectivity problem is now reduced to the split model by the explicit
    -- decomposition `V ≃ (k · v) × ker φ`.
    exact
      symmetricPower_insert_left_injective_of_split
        (k := k) (V := V) (v := v) (φ := φ) hφ n hinjSplit
  have hrestrictTrace :
      LinearMap.trace k S ((SymmetricPower.map (n + 1) A).restrict hS) =
        μ * LinearMap.trace k (SymmetricPower k (Fin n) V) (SymmetricPower.map n A) := by
    -- Once injectivity is reduced to the split model, the restriction-side trace is the already
    -- packaged conjugacy with `μ • Sym^n(A)`.
    simpa [S, hS] using
      trace_restrict_symmetricPower_insert_left_range_eq_mul_trace_of_injective
        (k := k) (V := V) (A := A) n (v := v) (μ := μ) hμ hinjAmbient
  -- The only remaining source-faithful gap is the split-model injectivity `hinjSplit`; after that,
  -- the transported trace split and the restriction-side trace identification close the theorem.
  calc
    LinearMap.trace k (SymmetricPower k (Fin (n + 1)) V) (SymmetricPower.map (n + 1) A) =
        LinearMap.trace k S ((SymmetricPower.map (n + 1) A).restrict hS) +
          LinearMap.trace k (SymmetricPower k (Fin (n + 1)) (V ⧸ L))
            (SymmetricPower.map (n + 1) (L.mapQ L A hL)) := hsplitTraceRange
    _ =
        μ * LinearMap.trace k (SymmetricPower k (Fin n) V) (SymmetricPower.map n A) +
          LinearMap.trace k (SymmetricPower k (Fin (n + 1)) (V ⧸ L))
            (SymmetricPower.map (n + 1) (L.mapQ L A hL)) := by
              rw [hrestrictTrace]

/-- Helper for Exercise 9-9.1-3: once the first eigenline-filtration step is isolated, the
positive-degree coefficient identity follows by induction and the standard decomposition of
`Finset.antidiagonal (n + 1)`. -/
theorem trace_symmetricPower_map_eq_sum_span_singleton_mapQ_coeff_pos
    [IsAlgClosed k] (A : V →ₗ[k] V) {v : V} {μ : k} (hv : v ≠ 0) (hμ : A v = μ • v)
    (n : ℕ) :
    let L : Submodule k V := Submodule.span k ({v} : Set V)
    let hL : L ≤ L.comap A := span_singleton_le_comap_of_eigenvector (A := A) hμ
    LinearMap.trace k (SymmetricPower k (Fin (n + 1)) V) (SymmetricPower.map (n + 1) A) =
      Finset.sum (Finset.antidiagonal (n + 1)) fun p ↦
        (μ ^ p.1) *
          LinearMap.trace k (SymmetricPower k (Fin p.2) (V ⧸ L))
            (SymmetricPower.map p.2 (L.mapQ L A hL)) := by
  let L : Submodule k V := Submodule.span k ({v} : Set V)
  let hL : L ≤ L.comap A := span_singleton_le_comap_of_eigenvector (A := A) hμ
  let qtrace : ℕ → k := fun m ↦
    LinearMap.trace k (SymmetricPower k (Fin m) (V ⧸ L))
      (SymmetricPower.map m (L.mapQ L A hL))
  have hstep :
      ∀ m : ℕ,
        LinearMap.trace k (SymmetricPower k (Fin (m + 1)) V) (SymmetricPower.map (m + 1) A) =
          μ * LinearMap.trace k (SymmetricPower k (Fin m) V) (SymmetricPower.map m A) +
            qtrace (m + 1) := by
    intro m
    -- Route correction: the remaining geometric input is now isolated in the one-step
    -- eigenline recurrence, so the coefficient formula itself is just antidiagonal bookkeeping.
    simpa [L, hL, qtrace] using
      trace_symmetricPower_map_step_span_singleton_mapQ
        (A := A) (v := v) (μ := μ) (hv := hv) (hμ := hμ) m
  -- After isolating the eigenline contribution, induction on the symmetric degree matches the
  -- standard recursive decomposition of `Finset.antidiagonal`.
  induction n with
  | zero =>
      calc
        LinearMap.trace k (SymmetricPower k (Fin (0 + 1)) V) (SymmetricPower.map (0 + 1) A) =
            μ * LinearMap.trace k (SymmetricPower k (Fin 0) V) (SymmetricPower.map 0 A) +
              qtrace (0 + 1) := by
                simpa using hstep 0
        _ = μ + qtrace 1 := by
              simp [trace_symmetricPower_map_zero]
        _ = Finset.sum (Finset.antidiagonal (0 + 1)) fun p ↦ (μ ^ p.1) * qtrace p.2 := by
              simpa [qtrace, trace_symmetricPower_map_zero, add_comm, mul_assoc, mul_left_comm,
                mul_comm] using
                (Finset.Nat.sum_antidiagonal_succ
                  (n := 0) (f := fun p : ℕ × ℕ ↦ (μ ^ p.1) * qtrace p.2)).symm
  | succ n ih =>
      calc
        LinearMap.trace k (SymmetricPower k (Fin (n + 1 + 1)) V)
            (SymmetricPower.map (n + 1 + 1) A) =
          μ * LinearMap.trace k (SymmetricPower k (Fin (n + 1)) V)
              (SymmetricPower.map (n + 1) A) +
            qtrace (n + 1 + 1) := by
              simpa [Nat.add_assoc] using hstep (n + 1)
        _ =
          μ * (Finset.sum (Finset.antidiagonal (n + 1)) fun p ↦ (μ ^ p.1) * qtrace p.2) +
            qtrace (n + 1 + 1) := by
              rw [ih]
        _ =
          (∑ p ∈ Finset.antidiagonal (n + 1), (μ ^ (p.1 + 1)) * qtrace p.2) +
            qtrace (n + 2) := by
              rw [Finset.mul_sum]
              congr 1
              refine Finset.sum_congr rfl ?_
              intro p hp
              simp [pow_succ, mul_assoc, mul_left_comm, mul_comm]
        _ =
          qtrace (n + 2) +
            ∑ p ∈ Finset.antidiagonal (n + 1), (μ ^ (p.1 + 1)) * qtrace p.2 := by
              rw [add_comm]
        _ = Finset.sum (Finset.antidiagonal (n + 2)) fun p ↦ (μ ^ p.1) * qtrace p.2 := by
              simpa [qtrace] using
                (Finset.Nat.sum_antidiagonal_succ
                  (n := n + 1) (f := fun p : ℕ × ℕ ↦ (μ ^ p.1) * qtrace p.2)).symm

/-- Helper for Exercise 9-9.1-3: after choosing a nonzero eigenvector, the symmetric trace series
factors through the corresponding eigenline and quotient. -/
theorem symmetric_trace_series_factor_span_singleton_mapQ
    [IsAlgClosed k] (A : V →ₗ[k] V) {v : V} {μ : k} (hv : v ≠ 0) (hμ : A v = μ • v) :
    let L : Submodule k V := Submodule.span k ({v} : Set V)
    let hL : L ≤ L.comap A := span_singleton_le_comap_of_eigenvector (A := A) hμ
    PowerSeries.mk
        (fun n ↦
          LinearMap.trace k (SymmetricPower k (Fin n) V) (SymmetricPower.map n A)) =
      PowerSeries.mk (fun n : ℕ ↦ μ ^ n) *
        PowerSeries.mk
          (fun n ↦
            LinearMap.trace k (SymmetricPower k (Fin n) (V ⧸ L))
              (SymmetricPower.map n (L.mapQ L A hL))) := by
  -- Route correction: the remaining symmetric-power blocker is now isolated as the exact
  -- eigenline-plus-quotient factorization needed by the source proof.
  have hcoeff :
      let L : Submodule k V := Submodule.span k ({v} : Set V)
      let hL : L ≤ L.comap A := span_singleton_le_comap_of_eigenvector (A := A) hμ
      ∀ n : ℕ,
        LinearMap.trace k (SymmetricPower k (Fin n) V) (SymmetricPower.map n A) =
          Finset.sum (Finset.antidiagonal n) fun p ↦
            (μ ^ p.1) *
              LinearMap.trace k (SymmetricPower k (Fin p.2) (V ⧸ L))
                (SymmetricPower.map p.2 (L.mapQ L A hL)) := by
    dsimp
    intro n
    cases n with
    | zero =>
        -- The source filtration starts with the empty symmetric tensor, so the degree-`0`
        -- coefficient already has the required antidiagonal form.
        exact
          trace_symmetricPower_map_eq_sum_span_singleton_mapQ_coeff_zero
            (A := A) (v := v) (μ := μ) hμ
    | succ n =>
        -- The positive-degree branch is now isolated as a named eigenline-filtration lemma.
        exact
          trace_symmetricPower_map_eq_sum_span_singleton_mapQ_coeff_pos
            (A := A) (v := v) (μ := μ) (hv := hv) (hμ := hμ) n
  -- Once the coefficientwise decomposition is available, the power-series identity is formal.
  exact
    symmetric_trace_series_factor_of_coefficients
      (A := A) (v := v) (μ := μ) (hμ := hμ) hcoeff

/-- Helper for Exercise 9-9.1-3: the fixed-endomorphism symmetric and exterior trace series are
inverse after the sign change `T ↦ -T` once the coefficient field is algebraically closed. -/
theorem symmetric_exterior_trace_series_mul_rescale_neg_eq_one_isAlgClosed
    [IsAlgClosed k] (A : V →ₗ[k] V) :
    PowerSeries.mk
        (fun n ↦
          LinearMap.trace k (SymmetricPower k (Fin n) V) (SymmetricPower.map n A)) *
      PowerSeries.rescale (-1 : k)
        (PowerSeries.mk
          (fun n ↦ LinearMap.trace k (⋀[k]^n V) (exteriorPower.map n A))) = 1 :=
  by
    let P : ℕ → Prop := fun n =>
      ∀ (W : Type v) [AddCommGroup W] [Module k W] [FiniteDimensional k W],
        Module.finrank k W = n →
        ∀ (B : W →ₗ[k] W),
          PowerSeries.mk
              (fun m ↦
                LinearMap.trace k (SymmetricPower k (Fin m) W) (SymmetricPower.map m B)) *
            PowerSeries.rescale (-1 : k)
              (PowerSeries.mk
                (fun m ↦ LinearMap.trace k (⋀[k]^m W) (exteriorPower.map m B))) = 1
    have hP : ∀ n, P n := by
      intro n
      refine Nat.strong_induction_on n ?_
      intro n ih W _instWAdd _instWModule _instWFinite hWfin B
      by_cases hzero : n = 0
      · -- The source proof starts from the zero-dimensional case.
        exact symmetric_exterior_trace_series_mul_rescale_neg_eq_one_zero_finrank
          (A := B) (hWfin.trans hzero)
      · haveI : Nontrivial W := (Module.finrank_pos_iff).1 (by
            rw [hWfin]
            exact Nat.pos_of_ne_zero hzero)
        obtain ⟨μ, hμ⟩ : ∃ μ : k, Module.End.HasEigenvalue B μ :=
          Module.End.exists_eigenvalue B
        obtain ⟨v, hv⟩ : ∃ v, Module.End.HasEigenvector B μ v := hμ.exists_hasEigenvector
        let L : Submodule k W := Submodule.span k ({v} : Set W)
        have hL :
            L ≤ L.comap B := span_singleton_le_comap_of_eigenvector
              (V := W) (A := B) (hμ := hv.apply_eq_smul)
        have hQlt : Module.finrank k (W ⧸ L) < n := by
          -- Quotienting by the chosen eigenline strictly lowers the induction rank.
          simpa [L, hWfin] using
            (finrank_quotient_span_singleton_lt
              (k := k) (V := W) (v := v) hv.2)
        have hsymm :
            PowerSeries.mk
                (fun m ↦
                  LinearMap.trace k (SymmetricPower k (Fin m) W) (SymmetricPower.map m B)) =
              PowerSeries.mk (fun m : ℕ ↦ μ ^ m) *
                PowerSeries.mk
                  (fun m ↦
                    LinearMap.trace k (SymmetricPower k (Fin m) (W ⧸ L))
                      (SymmetricPower.map m (L.mapQ L B hL))) := by
          -- This is the remaining symmetric eigenline factorization.
          simpa [L, hL] using
            symmetric_trace_series_factor_span_singleton_mapQ
              (A := B) (v := v) (μ := μ) hv.2 hv.apply_eq_smul
        have hquot :
            PowerSeries.mk
                (fun m ↦
                  LinearMap.trace k (SymmetricPower k (Fin m) (W ⧸ L))
                    (SymmetricPower.map m (L.mapQ L B hL))) *
              PowerSeries.rescale (-1 : k)
                (PowerSeries.mk
                  (fun m ↦
                    LinearMap.trace k (⋀[k]^m (W ⧸ L))
                      (exteriorPower.map m (L.mapQ L B hL)))) = 1 := by
          -- The quotient case is exactly the strong-induction hypothesis.
          simpa [L, hL] using
            ih (Module.finrank k (W ⧸ L)) hQlt
              (W := W ⧸ L) rfl (L.mapQ L B hL)
        -- Once both factorization statements are in place, the ambient identity follows.
        exact
          symmetric_exterior_trace_series_mul_rescale_neg_eq_one_of_factor
            (A := B) (v := v) (μ := μ) hv.2 hv.apply_eq_smul hsymm hquot
    -- Apply the dimension-induction theorem to the original ambient space.
    simpa using hP (Module.finrank k V) (W := V) rfl A

/-- Helper for Exercise 9-9.1-3: a linear equivalence on the base module induces a linear
equivalence on every symmetric power. -/
noncomputable def symmetricPowerLinearEquiv
    {W : Type w} [AddCommGroup W] [Module k W]
    (n : ℕ) (e : V ≃ₗ[k] W) :
    SymmetricPower k (Fin n) V ≃ₗ[k] SymmetricPower k (Fin n) W := by
  let f : SymmetricPower k (Fin n) V →ₗ[k] SymmetricPower k (Fin n) W :=
    SymmetricPower.map n e.toLinearMap
  let g : SymmetricPower k (Fin n) W →ₗ[k] SymmetricPower k (Fin n) V :=
    SymmetricPower.map n e.symm.toLinearMap
  have hleft : g.comp f = LinearMap.id := by
    -- The symmetric-power functor sends inverse linear equivalences to inverse endomorphisms.
    calc
      g.comp f = SymmetricPower.map n (e.symm.toLinearMap.comp e.toLinearMap) := by
        rw [← SymmetricPower.map_comp n e.toLinearMap e.symm.toLinearMap]
      _ = SymmetricPower.map n LinearMap.id := by
        congr
        ext x
        exact e.left_inv x
      _ = LinearMap.id := SymmetricPower.map_id n
  have hright : f.comp g = LinearMap.id := by
    calc
      f.comp g = SymmetricPower.map n (e.toLinearMap.comp e.symm.toLinearMap) := by
        rw [← SymmetricPower.map_comp n e.symm.toLinearMap e.toLinearMap]
      _ = SymmetricPower.map n LinearMap.id := by
        congr
        ext x
        exact e.right_inv x
      _ = LinearMap.id := SymmetricPower.map_id n
  -- The inverse on symmetric powers is obtained by applying `SymmetricPower.map` to `e.symm`.
  exact
    LinearEquiv.ofBijective f
      ⟨by
          intro x y hxy
          calc
            x = g (f x) := by
                symm
                exact LinearMap.congr_fun hleft x
            _ = g (f y) := by rw [hxy]
            _ = y := LinearMap.congr_fun hleft y,
        by
          intro y
          refine ⟨g y, ?_⟩
          exact LinearMap.congr_fun hright y⟩

/-- Helper for Exercise 9-9.1-3: the functorial map on symmetric powers sends a pure symmetric
generator to the generator obtained by applying the base linear map in each tensor factor. -/
theorem symmetricPower_map_apply_mk
    {W : Type w} [AddCommGroup W] [Module k W]
    (n : ℕ) (f : V →ₗ[k] W) (x : Fin n → V) :
    SymmetricPower.map n f
        (SymmetricPower.mk k (Fin n) V (PiTensorProduct.tprod k x)) =
      SymmetricPower.mk k (Fin n) W (PiTensorProduct.tprod k fun i ↦ f (x i)) := by
  have hcomp :
      (SymmetricPower.map n f).comp (SymmetricPower.mk k (Fin n) V) =
        (SymmetricPower.mk k (Fin n) W).comp
          (PiTensorProduct.map fun _ : Fin n ↦ f) := by
    ext y
    rfl
  -- First rewrite the symmetric-power map as a postcomposition with the quotient map.
  calc
    SymmetricPower.map n f
        (SymmetricPower.mk k (Fin n) V (PiTensorProduct.tprod k x)) =
      ((SymmetricPower.map n f).comp (SymmetricPower.mk k (Fin n) V))
        (PiTensorProduct.tprod k x) := by
          rfl
    _ =
      ((SymmetricPower.mk k (Fin n) W).comp
        (PiTensorProduct.map fun _ : Fin n ↦ f))
        (PiTensorProduct.tprod k x) := by
          rw [hcomp]
    -- Then multilinearity applies `f` separately in every tensor coordinate.
    _ =
      SymmetricPower.mk k (Fin n) W (PiTensorProduct.tprod k fun i ↦ f (x i)) := by
        simp [PiTensorProduct.map_tprod]

/-- Helper for Exercise 9-9.1-3: the induced equivalence on symmetric powers sends a pure
symmetric generator to the generator obtained by applying the base equivalence coordinatewise. -/
theorem symmetricPowerLinearEquiv_apply_mk
    {W : Type w} [AddCommGroup W] [Module k W]
    (n : ℕ) (e : V ≃ₗ[k] W) (x : Fin n → V) :
    symmetricPowerLinearEquiv (k := k) (V := V) (W := W) n e
        (SymmetricPower.mk k (Fin n) V (PiTensorProduct.tprod k x)) =
      SymmetricPower.mk k (Fin n) W (PiTensorProduct.tprod k fun i ↦ e (x i)) := by
  -- This is the general generator formula specialized to the linear equivalence map.
  simpa [symmetricPowerLinearEquiv] using
    symmetricPower_map_apply_mk (k := k) (V := V) (W := W) n e.toLinearMap x

/-- Helper for Exercise 9-9.1-3: on a pure symmetric generator, the inverse induced equivalence
recovers the same class as applying the inverse base linear equivalence inside
`SymmetricPower.map`. -/
theorem symmetricPowerLinearEquiv_symm_apply_mk
    {W : Type w} [AddCommGroup W] [Module k W]
    (n : ℕ) (e : V ≃ₗ[k] W) (x : PiTensorProduct k (fun _ : Fin n ↦ W)) :
    (symmetricPowerLinearEquiv (k := k) (V := V) (W := W) n e).symm
        (SymmetricPower.mk k (Fin n) W x) =
      SymmetricPower.map n e.symm.toLinearMap (SymmetricPower.mk k (Fin n) W x) := by
  apply (symmetricPowerLinearEquiv (k := k) (V := V) (W := W) n e).injective
  -- Apply the forward equivalence and use the functoriality of `SymmetricPower.map`.
  calc
    symmetricPowerLinearEquiv (k := k) (V := V) (W := W) n e
        ((symmetricPowerLinearEquiv (k := k) (V := V) (W := W) n e).symm
          (SymmetricPower.mk k (Fin n) W x)) =
      SymmetricPower.mk k (Fin n) W x := by
        simp
    _ = symmetricPowerLinearEquiv (k := k) (V := V) (W := W) n e
          (SymmetricPower.map n e.symm.toLinearMap
            (SymmetricPower.mk k (Fin n) W x)) := by
          calc
            SymmetricPower.mk k (Fin n) W x =
                SymmetricPower.map n LinearMap.id (SymmetricPower.mk k (Fin n) W x) := by
                  simp [SymmetricPower.map_id]
            _ = SymmetricPower.map n (e.toLinearMap.comp e.symm.toLinearMap)
                  (SymmetricPower.mk k (Fin n) W x) := by
                  congr
                  ext w
                  exact (e.apply_symm_apply w).symm
            _ = SymmetricPower.map n e.toLinearMap
                  (SymmetricPower.map n e.symm.toLinearMap
                    (SymmetricPower.mk k (Fin n) W x)) := by
                  rw [SymmetricPower.map_comp n e.symm.toLinearMap e.toLinearMap]
                  rfl

/-- Helper for Exercise 9-9.1-3: passing an endomorphism through a linear equivalence and then
taking symmetric powers agrees with conjugating the symmetric-power endomorphism by the induced
equivalence. -/
theorem symmetricPowerLinearEquiv_conj_map
    {W : Type w} [AddCommGroup W] [Module k W]
    (n : ℕ) (e : V ≃ₗ[k] W) (A : V →ₗ[k] V) :
    (symmetricPowerLinearEquiv (k := k) (V := V) (W := W) n e).conj (SymmetricPower.map n A) =
      SymmetricPower.map n (e.conj A) := by
  ext y
  rcases (LinearMap.range_eq_top.mp
      (SymmetricPower.range_mk (R := k) (ι := Fin n) (M := W))) y with ⟨x, rfl⟩
  have hs :=
    symmetricPowerLinearEquiv_symm_apply_mk (k := k) (V := V) (W := W) n e x
  -- Route correction: work directly on an arbitrary quotient representative and then reduce the
  -- conjugacy statement to functoriality of `SymmetricPower.map`.
  change
    symmetricPowerLinearEquiv (k := k) (V := V) (W := W) n e
        (SymmetricPower.map n A
          ((symmetricPowerLinearEquiv (k := k) (V := V) (W := W) n e).symm
            (SymmetricPower.mk k (Fin n) W x))) =
      SymmetricPower.map n (e.conj A) (SymmetricPower.mk k (Fin n) W x)
  rw [hs]
  simp [symmetricPowerLinearEquiv, LinearEquiv.conj_apply, SymmetricPower.map_comp]

/-- Helper for Exercise 9-9.1-3: the coefficientwise inclusion `v ↦ 1 ⊗ v` induces an injective
map from `Sym^n_k(V)` to `Sym^n_k(K ⊗ V)`. -/
theorem symmetricPower_map_includeRight_injective
    (n : ℕ) :
    Function.Injective
      (SymmetricPower.map n
        (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
          V →ₗ[k] TensorProduct k (AlgebraicClosure k) V)) := by
  have hinj :
      Function.Injective
        (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
          V →ₗ[k] TensorProduct k (AlgebraicClosure k) V) := by
    -- The canonical `v ↦ 1 ⊗ v` map is injective over a field extension.
    exact Module.FaithfullyFlat.tensorProduct_mk_injective
      (A := k) (B := AlgebraicClosure k) V
  obtain ⟨g, hg⟩ :=
    LinearMap.exists_leftInverse_of_injective
      (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
        V →ₗ[k] TensorProduct k (AlgebraicClosure k) V)
      (LinearMap.ker_eq_bot.2 hinj)
  -- Apply the left inverse coordinatewise on symmetric powers.
  apply LinearMap.injective_of_comp_eq_id
  change
    (SymmetricPower.map n g).comp
        (SymmetricPower.map n
          (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
            V →ₗ[k] TensorProduct k (AlgebraicClosure k) V)) =
      LinearMap.id
  rw [← SymmetricPower.map_comp n
    (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
      V →ₗ[k] TensorProduct k (AlgebraicClosure k) V) g]
  rw [hg, SymmetricPower.map_id]

/-- Helper for Exercise 9-9.1-3: before converting from the `k`-symmetric power to the desired
`K`-symmetric power, the coefficientwise inclusion already intertwines `Sym^n(A)` with the
base-changed endomorphism on `K ⊗ V`. -/
theorem symmetricPower_map_includeRight_intertwines
    (A : V →ₗ[k] V) (n : ℕ) :
    (SymmetricPower.map n
        (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
          V →ₗ[k] TensorProduct k (AlgebraicClosure k) V)).comp
        (SymmetricPower.map n A) =
      (SymmetricPower.map n
          ((((A.baseChange (AlgebraicClosure k)).restrictScalars k) :
            TensorProduct k (AlgebraicClosure k) V →ₗ[k]
              TensorProduct k (AlgebraicClosure k) V))).comp
        (SymmetricPower.map n
          (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
            V →ₗ[k] TensorProduct k (AlgebraicClosure k) V)) := by
  -- First fold both composites back into a single `SymmetricPower.map`, then compare the
  -- underlying linear maps on `V`.
  rw [← SymmetricPower.map_comp n A
    (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
      V →ₗ[k] TensorProduct k (AlgebraicClosure k) V)]
  rw [← SymmetricPower.map_comp n
    (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
      V →ₗ[k] TensorProduct k (AlgebraicClosure k) V)
    ((((A.baseChange (AlgebraicClosure k)).restrictScalars k) :
      TensorProduct k (AlgebraicClosure k) V →ₗ[k]
        TensorProduct k (AlgebraicClosure k) V))]
  -- On `V`, both composites are literally `v ↦ 1 ⊗ A v`.
  congr 1

/-- Helper for Exercise 9-9.1-3: the image of the coefficientwise inclusion on `k`-symmetric
powers is stable under the base-changed endomorphism before the final `k`- to `K`-symmetric-power
transport. -/
theorem symmetricPower_includeRight_range_le_comap
    (A : V →ₗ[k] V) (n : ℕ) :
    LinearMap.range
        (SymmetricPower.map n
          (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
            V →ₗ[k] TensorProduct k (AlgebraicClosure k) V)) ≤
      (LinearMap.range
        (SymmetricPower.map n
          (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
            V →ₗ[k] TensorProduct k (AlgebraicClosure k) V))).comap
        (SymmetricPower.map n
          ((((A.baseChange (AlgebraicClosure k)).restrictScalars k) :
            TensorProduct k (AlgebraicClosure k) V →ₗ[k]
              TensorProduct k (AlgebraicClosure k) V))) := by
  intro y hy
  rcases hy with ⟨x, rfl⟩
  refine ⟨SymmetricPower.map n A x, ?_⟩
  -- The intertwining identity shows that applying the base-changed map keeps us inside the image.
  have hintertwine :=
    symmetricPower_map_includeRight_intertwines (k := k) (V := V) (A := A) n
  exact LinearMap.congr_fun hintertwine x

/-- Helper for Exercise 9-9.1-3: the coefficientwise inclusion identifies `Sym^n_k(V)` with its
invariant image inside `Sym^n_k(K ⊗ V)`. -/
noncomputable def symmetricPower_includeRight_range_equiv
    (n : ℕ) :
    SymmetricPower k (Fin n) V ≃ₗ[k]
      ↥(LinearMap.range
        (SymmetricPower.map n
          (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
            V →ₗ[k] TensorProduct k (AlgebraicClosure k) V))) :=
  LinearEquiv.ofInjective
    (SymmetricPower.map n
      (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
        V →ₗ[k] TensorProduct k (AlgebraicClosure k) V))
    (symmetricPower_map_includeRight_injective (k := k) (V := V) n)

/-- Helper for Exercise 9-9.1-3: on a pure symmetric generator, the coefficientwise inclusion
`v ↦ 1 ⊗ v` acts by applying that inclusion in each tensor factor. -/
theorem symmetricPower_map_includeRight_apply_mk
    (n : ℕ) (f : Fin n → V) :
    SymmetricPower.map n
        (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
          V →ₗ[k] TensorProduct k (AlgebraicClosure k) V)
        (SymmetricPower.mk k (Fin n) V (PiTensorProduct.tprod k f)) =
      SymmetricPower.mk k (Fin n) (TensorProduct k (AlgebraicClosure k) V)
        (PiTensorProduct.tprod k
          (fun i ↦ ((TensorProduct.mk k (AlgebraicClosure k) V) 1) (f i))) := by
  have hcomp :
      (SymmetricPower.map n
          (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
            V →ₗ[k] TensorProduct k (AlgebraicClosure k) V)).comp
        (SymmetricPower.mk k (Fin n) V) =
      (SymmetricPower.mk k (Fin n) (TensorProduct k (AlgebraicClosure k) V)).comp
        (PiTensorProduct.map
          (fun _ : Fin n ↦
            (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
              V →ₗ[k] TensorProduct k (AlgebraicClosure k) V))) := by
    ext x
    rfl
  calc
    SymmetricPower.map n
        (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
          V →ₗ[k] TensorProduct k (AlgebraicClosure k) V)
        (SymmetricPower.mk k (Fin n) V (PiTensorProduct.tprod k f)) =
      ((SymmetricPower.map n
          (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
            V →ₗ[k] TensorProduct k (AlgebraicClosure k) V)).comp
        (SymmetricPower.mk k (Fin n) V))
          (PiTensorProduct.tprod k f) := by
            rfl
    _ =
      ((SymmetricPower.mk k (Fin n) (TensorProduct k (AlgebraicClosure k) V)).comp
        (PiTensorProduct.map
          (fun _ : Fin n ↦
            (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
              V →ₗ[k] TensorProduct k (AlgebraicClosure k) V))))
          (PiTensorProduct.tprod k f) := by
            rw [hcomp]
    _ =
      SymmetricPower.mk k (Fin n) (TensorProduct k (AlgebraicClosure k) V)
        (PiTensorProduct.tprod k
          (fun i ↦ ((TensorProduct.mk k (AlgebraicClosure k) V) 1) (f i))) := by
            simp [PiTensorProduct.map_tprod]

/-- Helper for Exercise 9-9.1-3: the invariant-image equivalence sends a symmetric generator to
the corresponding included generator, now regarded as a point of the stable range. -/
theorem symmetricPower_includeRight_range_equiv_apply_mk
    (n : ℕ) (f : Fin n → V) :
    (symmetricPower_includeRight_range_equiv (k := k) (V := V) n)
      (SymmetricPower.mk k (Fin n) V (PiTensorProduct.tprod k f)) =
      ⟨SymmetricPower.mk k (Fin n) (TensorProduct k (AlgebraicClosure k) V)
          (PiTensorProduct.tprod k
            (fun i ↦ ((TensorProduct.mk k (AlgebraicClosure k) V) 1) (f i))),
        by
          refine ⟨SymmetricPower.mk k (Fin n) V (PiTensorProduct.tprod k f), ?_⟩
          simpa using symmetricPower_map_includeRight_apply_mk (k := k) (V := V) n f⟩ := by
  -- The range equivalence is defined from the inclusion itself, so on generators we only need the
  -- previously computed image formula on the ambient symmetric power.
  apply Subtype.ext
  simpa [symmetricPower_includeRight_range_equiv] using
    symmetricPower_map_includeRight_apply_mk (k := k) (V := V) n f

/-- Helper for Exercise 9-9.1-3: in the scalar-extended symmetric power, a generator built from
pure tensors `a i ⊗ f i` differs from the included generator `1 ⊗ f i` only by the scalar
`∏ i, a i`. -/
theorem symmetricPower_mk_tmul_eq_prod_smul_includeRight
    (n : ℕ) (a : Fin n → AlgebraicClosure k) (f : Fin n → V) :
    SymmetricPower.mk (AlgebraicClosure k) (Fin n)
        (TensorProduct k (AlgebraicClosure k) V)
        (PiTensorProduct.tprod (AlgebraicClosure k) fun i ↦ a i ⊗ₜ[k] f i) =
      (∏ i, a i) •
        SymmetricPower.mk (AlgebraicClosure k) (Fin n)
          (TensorProduct k (AlgebraicClosure k) V)
          (PiTensorProduct.tprod (AlgebraicClosure k) fun i ↦ (1 : AlgebraicClosure k) ⊗ₜ[k] f i) := by
  -- Rewrite each tensor factor as `a i • (1 ⊗ f i)` and then use multilinearity of the symmetric
  -- generator to factor out the product of all scalar coefficients.
  change
    SymmetricPower.tprod (AlgebraicClosure k) (fun i ↦ a i ⊗ₜ[k] f i) =
      (∏ i, a i) •
        SymmetricPower.tprod (AlgebraicClosure k) (fun i ↦ (1 : AlgebraicClosure k) ⊗ₜ[k] f i)
  rw [show (fun i ↦ a i ⊗ₜ[k] f i) =
      fun i ↦ a i • ((1 : AlgebraicClosure k) ⊗ₜ[k] f i) by
        funext i
        simpa using
          (TensorProduct.tmul_eq_smul_one_tmul (R := k)
            (S := AlgebraicClosure k) (s := a i) (m := f i))]
  simpa using
    (SymmetricPower.tprod (AlgebraicClosure k)
      (ι := Fin n) (M := TensorProduct k (AlgebraicClosure k) V)).map_smul_univ a
      (fun i ↦ (1 : AlgebraicClosure k) ⊗ₜ[k] f i)

/-- Helper for Exercise 9-9.1-3: every symmetric generator built from pure tensors already lies
in the span of the included generators `1 ⊗ f i`, so only the multilinear tensor-to-pure-tensor
reduction remains in the positive-degree base-change step. -/
theorem symmetricPower_mk_tmul_mem_span_includeRight
    (n : ℕ) (a : Fin n → AlgebraicClosure k) (f : Fin n → V) :
    SymmetricPower.mk (AlgebraicClosure k) (Fin n)
        (TensorProduct k (AlgebraicClosure k) V)
        (PiTensorProduct.tprod (AlgebraicClosure k) fun i ↦ a i ⊗ₜ[k] f i) ∈
      Submodule.span (AlgebraicClosure k)
        (Set.range fun g : Fin n → V ↦
          SymmetricPower.mk (AlgebraicClosure k) (Fin n)
            (TensorProduct k (AlgebraicClosure k) V)
            (PiTensorProduct.tprod (AlgebraicClosure k)
              fun i ↦ (1 : AlgebraicClosure k) ⊗ₜ[k] g i)) := by
  -- Rewrite the pure-tensor generator as a scalar multiple of an included generator and use the
  -- defining generators of the span.
  rw [symmetricPower_mk_tmul_eq_prod_smul_includeRight (k := k) (V := V) n a f]
  exact Submodule.smul_mem _ _ <| Submodule.subset_span ⟨f, rfl⟩

/-- Helper for Exercise 9-9.1-3: the existing inclusion intertwining identity is already explicit
on the spanning generators of `Sym^n_k(V)`. -/
theorem symmetricPower_map_includeRight_intertwines_apply_mk
    (A : V →ₗ[k] V) (n : ℕ) (f : Fin n → V) :
    (SymmetricPower.map n
        (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
          V →ₗ[k] TensorProduct k (AlgebraicClosure k) V))
        ((SymmetricPower.map n A)
          (SymmetricPower.mk k (Fin n) V (PiTensorProduct.tprod k f))) =
      (SymmetricPower.map n
          ((((A.baseChange (AlgebraicClosure k)).restrictScalars k) :
            TensorProduct k (AlgebraicClosure k) V →ₗ[k]
              TensorProduct k (AlgebraicClosure k) V)))
        ((SymmetricPower.map n
            (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
              V →ₗ[k] TensorProduct k (AlgebraicClosure k) V))
          (SymmetricPower.mk k (Fin n) V (PiTensorProduct.tprod k f))) := by
  -- Evaluate the previously isolated map-level intertwining identity on a symmetric generator.
  exact
    LinearMap.congr_fun
      (symmetricPower_map_includeRight_intertwines (k := k) (V := V) (A := A) n)
      (SymmetricPower.mk k (Fin n) V (PiTensorProduct.tprod k f))

/-- Helper for Exercise 9-9.1-3: the invariant-image model already conjugates `Sym^n(A)` to the
restriction of the scalar-extended action on the stable image of the coefficientwise inclusion. -/
theorem symmetricPower_includeRight_range_conj
    (A : V →ₗ[k] V) (n : ℕ) :
    let i :=
      (SymmetricPower.map n
        (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
          V →ₗ[k] TensorProduct k (AlgebraicClosure k) V))
    let S := LinearMap.range i
    let hS : S ≤ S.comap
        (SymmetricPower.map n
          ((((A.baseChange (AlgebraicClosure k)).restrictScalars k) :
            TensorProduct k (AlgebraicClosure k) V →ₗ[k]
              TensorProduct k (AlgebraicClosure k) V))) :=
      symmetricPower_includeRight_range_le_comap (k := k) (V := V) (A := A) n
    (symmetricPower_includeRight_range_equiv (k := k) (V := V) n).conj
        (SymmetricPower.map n A) =
      (SymmetricPower.map n
          ((((A.baseChange (AlgebraicClosure k)).restrictScalars k) :
            TensorProduct k (AlgebraicClosure k) V →ₗ[k]
              TensorProduct k (AlgebraicClosure k) V))).restrict hS := by
  dsimp
  -- The range equivalence is defined from the coefficientwise inclusion itself, so on a range
  -- vector both sides reduce to the same explicit image under the stable restricted action.
  ext x
  rcases x with ⟨x, hx⟩
  obtain ⟨y, hy⟩ :=
    (symmetricPower_includeRight_range_equiv (k := k) (V := V) n).surjective ⟨x, hx⟩
  have hyVal :
      SymmetricPower.map n
          (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
            V →ₗ[k] TensorProduct k (AlgebraicClosure k) V) y = x := by
    simpa [symmetricPower_includeRight_range_equiv] using congrArg Subtype.val hy
  have hySymm :
      (symmetricPower_includeRight_range_equiv (k := k) (V := V) n).symm ⟨x, hx⟩ = y := by
    apply (symmetricPower_includeRight_range_equiv (k := k) (V := V) n).injective
    simpa using hy.symm
  change
    (SymmetricPower.map n
        (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
          V →ₗ[k] TensorProduct k (AlgebraicClosure k) V))
      (SymmetricPower.map n A
        ((symmetricPower_includeRight_range_equiv (k := k) (V := V) n).symm ⟨x, hx⟩)) =
      (SymmetricPower.map n
        ((((A.baseChange (AlgebraicClosure k)).restrictScalars k) :
          TensorProduct k (AlgebraicClosure k) V →ₗ[k]
            TensorProduct k (AlgebraicClosure k) V))) x
  rw [hySymm]
  have h :=
    LinearMap.congr_fun
      (symmetricPower_map_includeRight_intertwines (k := k) (V := V) (A := A) n) y
  simpa [hyVal] using h

/-- Helper for Exercise 9-9.1-3: after scalar extension, the invariant-image model still
conjugates the literal base change of `Sym^n(A)` to the scalar extension of the restricted action
on the stable range. -/
theorem symmetricPower_includeRight_range_baseChange_conj
    (A : V →ₗ[k] V) (n : ℕ) :
    let i :=
      (SymmetricPower.map n
        (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
          V →ₗ[k] TensorProduct k (AlgebraicClosure k) V))
    let S := LinearMap.range i
    let hS : S ≤ S.comap
        (SymmetricPower.map n
          ((((A.baseChange (AlgebraicClosure k)).restrictScalars k) :
            TensorProduct k (AlgebraicClosure k) V →ₗ[k]
              TensorProduct k (AlgebraicClosure k) V))) :=
      symmetricPower_includeRight_range_le_comap (k := k) (V := V) (A := A) n
    ((symmetricPower_includeRight_range_equiv (k := k) (V := V) n).baseChange k
        (AlgebraicClosure k)).conj
        ((SymmetricPower.map n A).baseChange (AlgebraicClosure k)) =
      ((SymmetricPower.map n
          ((((A.baseChange (AlgebraicClosure k)).restrictScalars k) :
            TensorProduct k (AlgebraicClosure k) V →ₗ[k]
              TensorProduct k (AlgebraicClosure k) V))).restrict hS).baseChange
        (AlgebraicClosure k) := by
  dsimp
  -- Route correction: instead of normalizing a generic conjugacy-under-base-change theorem, work
  -- directly on pure tensors in the stabilized range model and reuse the already proved
  -- generator-level conjugacy on `S`.
  apply TensorProduct.AlgebraTensorModule.ext
  intro a s
  have hconj :=
    LinearMap.congr_fun
      (symmetricPower_includeRight_range_conj (k := k) (V := V) (A := A) n) s
  simpa [LinearEquiv.conj_apply, LinearMap.baseChange_tmul,
    LinearEquiv.baseChange_tmul, LinearEquiv.baseChange_symm_tmul] using
    congrArg (fun y ↦ a ⊗ₜ[k] y) hconj

/-- Helper for Exercise 9-9.1-3: the genuine `K`-symmetric power on `K ⊗ V` is viewed as a
`k`-module by restricting scalars along `k → K`. -/
local instance symmetricPower_baseChange_targetModule (n : ℕ) :
    Module k
      (SymmetricPower (AlgebraicClosure k) (Fin n)
        (TensorProduct k (AlgebraicClosure k) V)) :=
  Module.compHom _ (algebraMap k (AlgebraicClosure k))

/-- Helper for Exercise 9-9.1-3: the restricted-scalar `k`-action and the native `K`-action on
the genuine `K`-symmetric power form the expected scalar tower. -/
local instance symmetricPower_baseChange_targetIsScalarTower (n : ℕ) :
    IsScalarTower k (AlgebraicClosure k)
      (SymmetricPower (AlgebraicClosure k) (Fin n)
        (TensorProduct k (AlgebraicClosure k) V)) :=
  IsScalarTower.of_compHom k (AlgebraicClosure k)
    (SymmetricPower (AlgebraicClosure k) (Fin n)
      (TensorProduct k (AlgebraicClosure k) V))

/-- Helper for Exercise 9-9.1-3: after scalar extension, the ambient module
`K ⊗ V` is generated over `K` by the included vectors `1 ⊗ v`. This is the
basic spanning input needed before lifting the source argument to symmetric
powers. -/
theorem tensorProduct_includeRight_span_eq_top :
    Submodule.span (AlgebraicClosure k)
      (Set.range (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
        V →ₗ[k] TensorProduct k (AlgebraicClosure k) V)) = ⊤ := by
  let i : V →ₗ[k] TensorProduct k (AlgebraicClosure k) V :=
    ((TensorProduct.mk k (AlgebraicClosure k) V) 1)
  have hrange :
      Set.range i =
        (((⊤ : Submodule k V).map i : Submodule k
          (TensorProduct k (AlgebraicClosure k) V)) :
          Set (TensorProduct k (AlgebraicClosure k) V)) := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨v, by simp, rfl⟩
    · rintro ⟨v, -, rfl⟩
      exact ⟨v, rfl⟩
  -- Rewrite the base change of the top submodule as the span of the included
  -- generators, then note that base change preserves the top submodule.
  calc
    Submodule.span (AlgebraicClosure k) (Set.range i) =
        Submodule.span (AlgebraicClosure k)
          (((⊤ : Submodule k V).map i : Submodule k
            (TensorProduct k (AlgebraicClosure k) V)) :
            Set (TensorProduct k (AlgebraicClosure k) V)) := by
              rw [hrange]
    _ = (⊤ : Submodule k V).baseChange (AlgebraicClosure k) := by
          symm
          simpa [i] using
            (Submodule.baseChange_eq_span
              (R := k) (A := AlgebraicClosure k) (M := V) (p := (⊤ : Submodule k V)))
    _ = ⊤ := by simp

/-- Helper for Exercise 9-9.1-3: after restricting scalars on `K ⊗ V`, the `k`-symmetric power
maps canonically to the genuine `K`-symmetric power by sending each symmetric generator to the
same tensor family, now interpreted over `K`. -/
noncomputable def symmetricPower_baseChange_targetMap
    (n : ℕ) :
    SymmetricPower k (Fin n) (TensorProduct k (AlgebraicClosure k) V) →ₗ[k]
      SymmetricPower (AlgebraicClosure k) (Fin n)
        (TensorProduct k (AlgebraicClosure k) V) := by
  let φ₀ :
      MultilinearMap k (fun _ : Fin n ↦ TensorProduct k (AlgebraicClosure k) V)
        (SymmetricPower (AlgebraicClosure k) (Fin n)
          (TensorProduct k (AlgebraicClosure k) V)) :=
    (SymmetricPower.tprod (AlgebraicClosure k)
      (ι := Fin n) (M := TensorProduct k (AlgebraicClosure k) V)).restrictScalars k
  let φ :
      PiTensorProduct k (fun _ : Fin n ↦ TensorProduct k (AlgebraicClosure k) V) →ₗ[k]
        SymmetricPower (AlgebraicClosure k) (Fin n)
          (TensorProduct k (AlgebraicClosure k) V) :=
    PiTensorProduct.lift φ₀
  refine
    { toFun := Quotient.lift φ ?_
      map_add' := ?_
      map_smul' := ?_ }
  · intro x y h
    induction h with
    | of x y h =>
        cases h with
        | perm e f =>
            -- The codomain is already symmetric, so permuting the tensor factors does not change
            -- the resulting symmetric tensor.
            simpa [φ, φ₀] using
              (SymmetricPower.tprod_equiv
                (R := AlgebraicClosure k) (ι := Fin n)
                (M := TensorProduct k (AlgebraicClosure k) V) e f).symm
    | refl =>
        rfl
    | symm _ ih =>
        simpa using ih.symm
    | trans _ _ ih₁ ih₂ =>
        exact ih₁.trans ih₂
    | add _ _ ih₁ ih₂ =>
        simpa using congrArg₂ (· + ·) ih₁ ih₂
  · intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro a b
    exact φ.map_add a b
  · intro a x
    refine Quotient.inductionOn x ?_
    intro z
    exact φ.map_smul a z

/-- Helper for Exercise 9-9.1-3: the canonical comparison from the `k`-symmetric power of
`K ⊗ V` to the genuine `K`-symmetric power is explicit on symmetric generators. -/
theorem symmetricPower_baseChange_targetMap_apply_mk
    (n : ℕ) (f : Fin n → TensorProduct k (AlgebraicClosure k) V) :
    symmetricPower_baseChange_targetMap (k := k) (V := V) n
      (SymmetricPower.mk k (Fin n) (TensorProduct k (AlgebraicClosure k) V)
        (PiTensorProduct.tprod k f)) =
      SymmetricPower.mk (AlgebraicClosure k) (Fin n)
        (TensorProduct k (AlgebraicClosure k) V)
        (PiTensorProduct.tprod (AlgebraicClosure k) f) := by
  -- Unfold the quotient lift and evaluate the underlying tensor-product lift on a pure tensor.
  change
    PiTensorProduct.lift
        ((SymmetricPower.tprod (AlgebraicClosure k)
            (ι := Fin n) (M := TensorProduct k (AlgebraicClosure k) V)).restrictScalars k)
        (PiTensorProduct.tprod k f) =
      SymmetricPower.mk (AlgebraicClosure k) (Fin n)
        (TensorProduct k (AlgebraicClosure k) V)
        (PiTensorProduct.tprod (AlgebraicClosure k) f)
  rw [PiTensorProduct.lift.tprod]
  rfl

/-- Helper for Exercise 9-9.1-3: in positive degree, the canonical comparison from the
`k`-symmetric power of `K ⊗ V` to the genuine `K`-symmetric power is surjective. The source
reason is that a scalar coefficient in a symmetric generator can be absorbed into one tensor
factor because there is at least one factor. -/
theorem symmetricPower_baseChange_targetMap_surjective
    (n : ℕ) :
    Function.Surjective
      (symmetricPower_baseChange_targetMap (k := k) (V := V) (n + 1)) := by
  intro y
  rcases (LinearMap.range_eq_top.mp
      (SymmetricPower.range_mk
        (R := AlgebraicClosure k)
        (ι := Fin (n + 1))
        (M := TensorProduct k (AlgebraicClosure k) V)) y) with ⟨x, rfl⟩
  -- Reduce to proving surjectivity on a spanning symmetric generator of the target.
  refine PiTensorProduct.induction_on' x ?_ ?_
  · intro a f
    let g : Fin (n + 1) → TensorProduct k (AlgebraicClosure k) V :=
      Function.update f 0 (a • f 0)
    refine ⟨SymmetricPower.mk k (Fin (n + 1))
        (TensorProduct k (AlgebraicClosure k) V)
        (PiTensorProduct.tprod k g), ?_⟩
    -- In positive degree, move the scalar coefficient into the `0`th tensor factor and then
    -- apply the explicit generator formula for `symmetricPower_baseChange_targetMap`.
    calc
      symmetricPower_baseChange_targetMap (k := k) (V := V) (n + 1)
          (SymmetricPower.mk k (Fin (n + 1))
            (TensorProduct k (AlgebraicClosure k) V)
            (PiTensorProduct.tprod k g)) =
        SymmetricPower.mk (AlgebraicClosure k) (Fin (n + 1))
          (TensorProduct k (AlgebraicClosure k) V)
          (PiTensorProduct.tprod (AlgebraicClosure k) g) := by
            simpa [g] using
              symmetricPower_baseChange_targetMap_apply_mk
                (k := k) (V := V) (n := n + 1) g
      _ =
        SymmetricPower.mk (AlgebraicClosure k) (Fin (n + 1))
          (TensorProduct k (AlgebraicClosure k) V)
          (PiTensorProduct.tprodCoeff (AlgebraicClosure k) a f) := by
            congr 1
            change
              PiTensorProduct.tprodCoeff (AlgebraicClosure k) (1 : AlgebraicClosure k) g =
                PiTensorProduct.tprodCoeff (AlgebraicClosure k) a f
            simpa [g] using
              (PiTensorProduct.smul_tprodCoeff
                (R := AlgebraicClosure k)
                (z := (1 : AlgebraicClosure k))
                (f := f)
                (i := (0 : Fin (n + 1)))
                (r := a))
      _ = SymmetricPower.mk (AlgebraicClosure k) (Fin (n + 1))
          (TensorProduct k (AlgebraicClosure k) V) (PiTensorProduct.tprodCoeff (AlgebraicClosure k) a f) := rfl
  · intro x₁ x₂ hx₁ hx₂
    rcases hx₁ with ⟨y₁, hy₁⟩
    rcases hx₂ with ⟨y₂, hy₂⟩
    refine ⟨y₁ + y₂, ?_⟩
    -- The target comparison is linear, so preimages add.
    simp [hy₁, hy₂]

/-- Helper for Exercise 9-9.1-3: the canonical comparison to the genuine `K`-symmetric power
intertwines the restricted-scalar action of `A.baseChange K` with the native `K`-linear action. -/
theorem symmetricPower_baseChange_targetMap_intertwines
    (A : V →ₗ[k] V) (n : ℕ) :
    (symmetricPower_baseChange_targetMap (k := k) (V := V) n).comp
        (SymmetricPower.map n
          ((((A.baseChange (AlgebraicClosure k)).restrictScalars k) :
            TensorProduct k (AlgebraicClosure k) V →ₗ[k]
              TensorProduct k (AlgebraicClosure k) V))) =
      ((SymmetricPower.map n (A.baseChange (AlgebraicClosure k))).restrictScalars k).comp
        (symmetricPower_baseChange_targetMap (k := k) (V := V) n) := by
  ext y
  rcases (LinearMap.range_eq_top.mp
      (SymmetricPower.range_mk
        (R := k)
        (ι := Fin n)
        (M := TensorProduct k (AlgebraicClosure k) V)) y) with ⟨x, rfl⟩
  -- Reduce to pure tensor generators in the `k`-indexed tensor product and use linearity.
  refine PiTensorProduct.induction_on' x ?_ ?_
  · intro a f
    -- On a basic tensor coefficient, both sides are the same scalar multiple of the generator
    -- formula obtained by applying `A.baseChange K` coordinatewise.
    rw [PiTensorProduct.tprodCoeff_eq_smul_tprod]
    simp only [LinearMap.map_smul]
    congr 1
    calc
      symmetricPower_baseChange_targetMap (k := k) (V := V) n
          ((SymmetricPower.map n
              ((((A.baseChange (AlgebraicClosure k)).restrictScalars k) :
                TensorProduct k (AlgebraicClosure k) V →ₗ[k]
                  TensorProduct k (AlgebraicClosure k) V)))
            (SymmetricPower.mk k (Fin n) (TensorProduct k (AlgebraicClosure k) V)
              (PiTensorProduct.tprod k f))) =
        SymmetricPower.mk (AlgebraicClosure k) (Fin n)
          (TensorProduct k (AlgebraicClosure k) V)
          (PiTensorProduct.tprod (AlgebraicClosure k)
            fun i ↦ (A.baseChange (AlgebraicClosure k)) (f i)) := by
              change
                symmetricPower_baseChange_targetMap (k := k) (V := V) n
                  (SymmetricPower.mk k (Fin n) (TensorProduct k (AlgebraicClosure k) V)
                    (PiTensorProduct.map
                      (fun _ : Fin n ↦
                        ((((A.baseChange (AlgebraicClosure k)).restrictScalars k) :
                          TensorProduct k (AlgebraicClosure k) V →ₗ[k]
                            TensorProduct k (AlgebraicClosure k) V)))
                      (PiTensorProduct.tprod k f))) =
                  SymmetricPower.mk (AlgebraicClosure k) (Fin n)
                    (TensorProduct k (AlgebraicClosure k) V)
                    (PiTensorProduct.tprod (AlgebraicClosure k)
                      fun i ↦ (A.baseChange (AlgebraicClosure k)) (f i))
              rw [PiTensorProduct.map_tprod, symmetricPower_baseChange_targetMap_apply_mk]
              have hfun :
                  (fun i ↦
                    ((((A.baseChange (AlgebraicClosure k)).restrictScalars k) :
                      TensorProduct k (AlgebraicClosure k) V →ₗ[k]
                        TensorProduct k (AlgebraicClosure k) V)) (f i)) =
                    fun i ↦ (LinearMap.baseChange (AlgebraicClosure k) A) (f i) := by
                funext i
                rfl
              rw [hfun]
      _ =
        (SymmetricPower.map n (A.baseChange (AlgebraicClosure k)))
          (symmetricPower_baseChange_targetMap (k := k) (V := V) n
            (SymmetricPower.mk k (Fin n) (TensorProduct k (AlgebraicClosure k) V)
              (PiTensorProduct.tprod k f))) := by
              rw [symmetricPower_baseChange_targetMap_apply_mk]
              change
                SymmetricPower.mk (AlgebraicClosure k) (Fin n)
                  (TensorProduct k (AlgebraicClosure k) V)
                  (PiTensorProduct.tprod (AlgebraicClosure k)
                    fun i ↦ (A.baseChange (AlgebraicClosure k)) (f i)) =
                  SymmetricPower.map n (A.baseChange (AlgebraicClosure k))
                    (SymmetricPower.mk (AlgebraicClosure k) (Fin n)
                      (TensorProduct k (AlgebraicClosure k) V)
                      (PiTensorProduct.tprod (AlgebraicClosure k) f))
              change
                SymmetricPower.mk (AlgebraicClosure k) (Fin n)
                  (TensorProduct k (AlgebraicClosure k) V)
                  (PiTensorProduct.tprod (AlgebraicClosure k)
                    fun i ↦ (A.baseChange (AlgebraicClosure k)) (f i)) =
                  SymmetricPower.mk (AlgebraicClosure k) (Fin n)
                    (TensorProduct k (AlgebraicClosure k) V)
                    (PiTensorProduct.map
                      (fun _ : Fin n ↦
                        (A.baseChange (AlgebraicClosure k)))
                      (PiTensorProduct.tprod (AlgebraicClosure k) f))
              rw [PiTensorProduct.map_tprod]
  · intro x₁ x₂ hx₁ hx₂
    -- The intertwining identity is linear in the tensor argument.
    simpa [LinearMap.map_add, hx₁, hx₂]

/-- Helper for Exercise 9-9.1-3: tensoring the stabilized range inside
`Sym^{n+1}_k(K ⊗ V)` gives a canonical `K`-linear comparison map to the genuine
`K`-symmetric power by applying the already-constructed target map on the range vector and letting
the left tensor factor act by scalar multiplication. -/
noncomputable def symmetricPower_baseChange_rangeTargetMap
    (n : ℕ)
    (S :
      Submodule k
        (SymmetricPower k (Fin (n + 1))
          (TensorProduct k (AlgebraicClosure k) V))) :
    TensorProduct k (AlgebraicClosure k) S →ₗ[AlgebraicClosure k]
      SymmetricPower (AlgebraicClosure k) (Fin (n + 1))
        (TensorProduct k (AlgebraicClosure k) V) :=
  let φ :
      S →ₗ[k]
        SymmetricPower (AlgebraicClosure k) (Fin (n + 1))
          (TensorProduct k (AlgebraicClosure k) V) :=
    (symmetricPower_baseChange_targetMap (k := k) (V := V) (n + 1)).comp S.subtype
  TensorProduct.AlgebraTensorModule.lift <|
    LinearMap.smulRight
      (LinearMap.id :
        AlgebraicClosure k →ₗ[AlgebraicClosure k] AlgebraicClosure k)
      φ

/-- Helper for Exercise 9-9.1-3: on a simple tensor `a ⊗ x` from the scalar extension of the
stabilized range, the range-to-target comparison is just `a` times the ambient target map applied
to the range vector `x`. -/
@[simp] theorem symmetricPower_baseChange_rangeTargetMap_tmul
    (n : ℕ)
    (S :
      Submodule k
        (SymmetricPower k (Fin (n + 1))
          (TensorProduct k (AlgebraicClosure k) V)))
    (a : AlgebraicClosure k) (x : S) :
    symmetricPower_baseChange_rangeTargetMap (k := k) (V := V) n S (a ⊗ₜ[k] x) =
      a •
        symmetricPower_baseChange_targetMap (k := k) (V := V) (n + 1)
          ((x : SymmetricPower k (Fin (n + 1))
            (TensorProduct k (AlgebraicClosure k) V))) := by
  -- The comparison map was defined by tensor-lifting scalar multiplication of the restricted
  -- target map, so its action on simple tensors is immediate from the lift formula.
  simp [symmetricPower_baseChange_rangeTargetMap]

/-- Helper for Exercise 9-9.1-3: the range-to-target comparison already hits the included
generators coming from `v ↦ 1 ⊗ v`, which isolates the remaining surjectivity packaging needed in
the positive-degree base-change step. -/
theorem symmetricPower_baseChange_rangeTargetMap_tmul_includeRight_mk
    (n : ℕ) (a : AlgebraicClosure k) (f : Fin (n + 1) → V) :
    let i :=
      SymmetricPower.map (n + 1)
        (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
          V →ₗ[k] TensorProduct k (AlgebraicClosure k) V)
    let S := LinearMap.range i
    let x : S :=
      (symmetricPower_includeRight_range_equiv (k := k) (V := V) (n + 1))
        (SymmetricPower.mk k (Fin (n + 1)) V (PiTensorProduct.tprod k f))
    symmetricPower_baseChange_rangeTargetMap (k := k) (V := V) n S (a ⊗ₜ[k] x) =
      a •
        SymmetricPower.mk (AlgebraicClosure k) (Fin (n + 1))
          (TensorProduct k (AlgebraicClosure k) V)
          (PiTensorProduct.tprod (AlgebraicClosure k)
            fun j ↦ ((TensorProduct.mk k (AlgebraicClosure k) V) 1) (f j)) := by
  dsimp
  -- First rewrite the tensor comparison on the chosen range generator.
  rw [symmetricPower_baseChange_rangeTargetMap_tmul]
  rw [symmetricPower_includeRight_range_equiv_apply_mk]
  -- Then the ambient target map sends the included `k`-symmetric generator to the matching
  -- genuine `K`-symmetric generator.
  simpa using
    congrArg (fun y ↦ a • y)
      (symmetricPower_baseChange_targetMap_apply_mk
        (k := k) (V := V) (n := n + 1)
        (fun j ↦ ((TensorProduct.mk k (AlgebraicClosure k) V) 1) (f j)))

/-- Helper for Exercise 9-9.1-3: after scalar-extending the invariant-image equivalence,
composing with the range-to-target comparison sends a simple tensor of a symmetric generator to the
matching genuine `K`-symmetric generator. -/
theorem symmetricPower_baseChange_comparison_apply_tmul_mk
    (n : ℕ) (a : AlgebraicClosure k) (f : Fin (n + 1) → V) :
    let i :=
      SymmetricPower.map (n + 1)
        (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
          V →ₗ[k] TensorProduct k (AlgebraicClosure k) V)
    let S := LinearMap.range i
    let eRange := symmetricPower_includeRight_range_equiv (k := k) (V := V) (n + 1)
    symmetricPower_baseChange_rangeTargetMap (k := k) (V := V) n S
      ((eRange.baseChange k (AlgebraicClosure k))
        (a ⊗ₜ[k] (SymmetricPower.mk k (Fin (n + 1)) V (PiTensorProduct.tprod k f)))) =
      a •
        SymmetricPower.mk (AlgebraicClosure k) (Fin (n + 1))
          (TensorProduct k (AlgebraicClosure k) V)
          (PiTensorProduct.tprod (AlgebraicClosure k)
            fun j ↦ ((TensorProduct.mk k (AlgebraicClosure k) V) 1) (f j)) := by
  dsimp
  -- First evaluate the tensor-lift on a simple tensor in the stabilized range.
  rw [symmetricPower_baseChange_rangeTargetMap_tmul]
  -- Then rewrite the range vector to its ambient included symmetric generator.
  calc
    a •
        symmetricPower_baseChange_targetMap (k := k) (V := V) (n + 1)
          ↑((symmetricPower_includeRight_range_equiv (k := k) (V := V) (n + 1))
            (SymmetricPower.mk k (Fin (n + 1)) V (PiTensorProduct.tprod k f))) =
      a •
        symmetricPower_baseChange_targetMap (k := k) (V := V) (n + 1)
          (SymmetricPower.mk k (Fin (n + 1))
            (TensorProduct k (AlgebraicClosure k) V)
            (PiTensorProduct.tprod k
              fun i ↦ ((TensorProduct.mk k (AlgebraicClosure k) V) 1) (f i))) := by
            congr 1
            exact
              congrArg
                (symmetricPower_baseChange_targetMap (k := k) (V := V) (n + 1))
                (by
                  simpa using
                    congrArg Subtype.val
                      (symmetricPower_includeRight_range_equiv_apply_mk
                        (k := k) (V := V) (n := n + 1) f))
    _ =
      a •
        SymmetricPower.mk (AlgebraicClosure k) (Fin (n + 1))
          (TensorProduct k (AlgebraicClosure k) V)
          (PiTensorProduct.tprod (AlgebraicClosure k)
            fun j ↦ ((TensorProduct.mk k (AlgebraicClosure k) V) 1) (f j)) := by
              congr 1
              simpa using
                symmetricPower_baseChange_targetMap_apply_mk
                  (k := k) (V := V) (n := n + 1)
                  (fun j ↦ ((TensorProduct.mk k (AlgebraicClosure k) V) 1) (f j))

/-- Helper for Exercise 9-9.1-3: if the included generators already span the genuine
`K`-symmetric power, then the range-to-target comparison is surjective because it hits each of
those generators explicitly. -/
theorem symmetricPower_baseChange_rangeTargetMap_surjective_of_generator_span
    (n : ℕ)
    (hspan :
      Submodule.span (AlgebraicClosure k)
        (Set.range fun f : Fin (n + 1) → V ↦
          SymmetricPower.mk (AlgebraicClosure k) (Fin (n + 1))
            (TensorProduct k (AlgebraicClosure k) V)
            (PiTensorProduct.tprod (AlgebraicClosure k)
              fun i ↦ ((TensorProduct.mk k (AlgebraicClosure k) V) 1) (f i))) = ⊤) :
    let i :=
      SymmetricPower.map (n + 1)
        (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
          V →ₗ[k] TensorProduct k (AlgebraicClosure k) V)
    let S := LinearMap.range i
    Function.Surjective
      (symmetricPower_baseChange_rangeTargetMap (k := k) (V := V) n S) := by
  dsimp at hspan ⊢
  let i :=
    SymmetricPower.map (n + 1)
      (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
        V →ₗ[k] TensorProduct k (AlgebraicClosure k) V)
  let S := LinearMap.range i
  let G :
      Set
        (SymmetricPower (AlgebraicClosure k) (Fin (n + 1))
          (TensorProduct k (AlgebraicClosure k) V)) :=
    Set.range fun f : Fin (n + 1) → V ↦
      SymmetricPower.mk (AlgebraicClosure k) (Fin (n + 1))
        (TensorProduct k (AlgebraicClosure k) V)
        (PiTensorProduct.tprod (AlgebraicClosure k)
          fun j ↦ ((TensorProduct.mk k (AlgebraicClosure k) V) 1) (f j))
  have hspan' : Submodule.span (AlgebraicClosure k) G = ⊤ := by
    simpa [G] using hspan
  have hsurj_mem :
      ∀ y ∈ Submodule.span (AlgebraicClosure k) G,
        ∃ a, symmetricPower_baseChange_rangeTargetMap (k := k) (V := V) n S a = y := by
    intro y hy
    let P :
        (z :
          SymmetricPower (AlgebraicClosure k) (Fin (n + 1))
            (TensorProduct k (AlgebraicClosure k) V)) →
          z ∈ Submodule.span (AlgebraicClosure k) G → Prop :=
      fun z _ ↦ ∃ a, symmetricPower_baseChange_rangeTargetMap (k := k) (V := V) n S a = z
    refine (Submodule.span_induction (s := G) (p := P) ?_ ?_ ?_ ?_ hy)
    · intro z hz
      rcases hz with ⟨f, rfl⟩
      refine
        ⟨((symmetricPower_includeRight_range_equiv (k := k) (V := V) (n + 1)).baseChange
            k (AlgebraicClosure k))
            (1 ⊗ₜ[k] SymmetricPower.mk k (Fin (n + 1)) V (PiTensorProduct.tprod k f)),
          ?_⟩
      -- Each included generator is already the image of the explicit tensor-lifted range generator.
      simpa [i, S] using
        symmetricPower_baseChange_comparison_apply_tmul_mk
          (k := k) (V := V) n (1 : AlgebraicClosure k) f
    · exact ⟨0, by simp [S]⟩
    · intro y₁ y₂ hy₁ hy₂ hy₁_pre hy₂_pre
      rcases hy₁_pre with ⟨x₁, rfl⟩
      rcases hy₂_pre with ⟨x₂, rfl⟩
      -- Surjectivity is stable under addition because the comparison map is linear.
      exact ⟨x₁ + x₂, by simp [S]⟩
    · intro a y hy hy_pre
      rcases hy_pre with ⟨x, rfl⟩
      -- Surjectivity is also stable under scalar multiplication.
      exact ⟨a • x, by simp [S]⟩
  intro y
  have hy : y ∈ Submodule.span (AlgebraicClosure k) G := by
    rw [hspan']
    simp
  exact hsurj_mem y hy

/-- Helper for Exercise 9-9.1-3: to show that the included generators span the genuine
`K`-symmetric power, it is enough to prove the same span-membership statement for every pure
symmetric generator `⨂ₛ f`. The global span-top conclusion then follows from
`SymmetricPower.span_tprod_eq_top`. -/
theorem symmetricPower_includeRight_generators_span_top_of_tprod_mem
    (n : ℕ)
    (hmem :
      ∀ f : Fin (n + 1) → TensorProduct k (AlgebraicClosure k) V,
        SymmetricPower.mk (AlgebraicClosure k) (Fin (n + 1))
            (TensorProduct k (AlgebraicClosure k) V)
            (PiTensorProduct.tprod (AlgebraicClosure k) f) ∈
          Submodule.span (AlgebraicClosure k)
            (Set.range fun g : Fin (n + 1) → V ↦
              SymmetricPower.mk (AlgebraicClosure k) (Fin (n + 1))
                (TensorProduct k (AlgebraicClosure k) V)
                (PiTensorProduct.tprod (AlgebraicClosure k)
                  fun i ↦ ((TensorProduct.mk k (AlgebraicClosure k) V) 1) (g i)))) :
    Submodule.span (AlgebraicClosure k)
      (Set.range fun g : Fin (n + 1) → V ↦
        SymmetricPower.mk (AlgebraicClosure k) (Fin (n + 1))
          (TensorProduct k (AlgebraicClosure k) V)
          (PiTensorProduct.tprod (AlgebraicClosure k)
            fun i ↦ ((TensorProduct.mk k (AlgebraicClosure k) V) 1) (g i))) = ⊤ := by
  let T :
      Submodule (AlgebraicClosure k)
        (SymmetricPower (AlgebraicClosure k) (Fin (n + 1))
          (TensorProduct k (AlgebraicClosure k) V)) :=
    Submodule.span (AlgebraicClosure k)
      (Set.range fun g : Fin (n + 1) → V ↦
        SymmetricPower.mk (AlgebraicClosure k) (Fin (n + 1))
          (TensorProduct k (AlgebraicClosure k) V)
          (PiTensorProduct.tprod (AlgebraicClosure k)
            fun i ↦ ((TensorProduct.mk k (AlgebraicClosure k) V) 1) (g i)))
  have hle :
      Submodule.span (AlgebraicClosure k)
          (Set.range
            (SymmetricPower.tprod (AlgebraicClosure k)
              (ι := Fin (n + 1))
              (M := TensorProduct k (AlgebraicClosure k) V))) ≤
        T := by
    -- Once every pure symmetric generator lands in `T`, the span of all such generators also
    -- lands in `T`.
    rw [Submodule.span_le]
    rintro _ ⟨f, rfl⟩
    simpa [SymmetricPower.tprod] using hmem f
  -- Route correction: the only remaining work is to prove `hmem` for arbitrary tensor factors;
  -- the top-level span statement is then formal from the standard spanning theorem.
  apply Submodule.eq_top_iff'.2
  intro y
  have hy :
      y ∈
        Submodule.span (AlgebraicClosure k)
          (Set.range
            (SymmetricPower.tprod (AlgebraicClosure k)
              (ι := Fin (n + 1))
              (M := TensorProduct k (AlgebraicClosure k) V))) := by
    rw [SymmetricPower.span_tprod_eq_top
      (R := AlgebraicClosure k)
      (ι := Fin (n + 1))
      (M := TensorProduct k (AlgebraicClosure k) V)]
    simp
  exact hle hy

/-- Helper for Exercise 9-9.1-3: scalar extension preserves the dimension of the stabilized range,
and that dimension is the same as the original `k`-symmetric power because the range model is a
linear equivalence. -/
theorem finrank_symmetricPower_includeRight_range_baseChange
    (n : ℕ) :
    let i :=
      SymmetricPower.map (n + 1)
        (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
          V →ₗ[k] TensorProduct k (AlgebraicClosure k) V)
    let S := LinearMap.range i
    Module.finrank (AlgebraicClosure k) (TensorProduct k (AlgebraicClosure k) S) =
      Module.finrank k (SymmetricPower k (Fin (n + 1)) V) := by
  dsimp
  let i :=
    SymmetricPower.map (n + 1)
      (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
        V →ₗ[k] TensorProduct k (AlgebraicClosure k) V)
  let S := LinearMap.range i
  let eRange := symmetricPower_includeRight_range_equiv (k := k) (V := V) (n + 1)
  calc
    Module.finrank (AlgebraicClosure k) (TensorProduct k (AlgebraicClosure k) S) =
        Module.finrank (AlgebraicClosure k)
          (TensorProduct k (AlgebraicClosure k) (SymmetricPower k (Fin (n + 1)) V)) := by
          -- Compare the scalar-extended range with the scalar extension of the original symmetric
          -- power using the base change of the range equivalence.
          simpa [eRange] using
            (LinearEquiv.baseChange k (AlgebraicClosure k)
              (SymmetricPower k (Fin (n + 1)) V) S eRange).symm.finrank_eq
    _ = Module.finrank k (SymmetricPower k (Fin (n + 1)) V) := by
          simpa using
            (Module.finrank_baseChange
              (R := AlgebraicClosure k) (S := k)
              (M' := SymmetricPower k (Fin (n + 1)) V))

/-- Helper for Exercise 9-9.1-3: the range-to-target comparison intertwines the scalar-extended
restricted action on the stabilized range with the genuine `K`-symmetric-power action on the
target. -/
theorem symmetricPower_baseChange_rangeTargetMap_intertwines
    (A : V →ₗ[k] V) (n : ℕ) :
    let S :
        Submodule k
          (SymmetricPower k (Fin (n + 1))
            (TensorProduct k (AlgebraicClosure k) V)) :=
      LinearMap.range
        (SymmetricPower.map (n + 1)
          (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
            V →ₗ[k] TensorProduct k (AlgebraicClosure k) V))
    let hS :
        S ≤ S.comap
          (SymmetricPower.map (n + 1)
            ((((A.baseChange (AlgebraicClosure k)).restrictScalars k) :
              TensorProduct k (AlgebraicClosure k) V →ₗ[k]
                TensorProduct k (AlgebraicClosure k) V))) :=
      symmetricPower_includeRight_range_le_comap (k := k) (V := V) (A := A) (n + 1)
    (symmetricPower_baseChange_rangeTargetMap (k := k) (V := V) n S).comp
        (((SymmetricPower.map (n + 1)
            ((((A.baseChange (AlgebraicClosure k)).restrictScalars k) :
              TensorProduct k (AlgebraicClosure k) V →ₗ[k]
                TensorProduct k (AlgebraicClosure k) V))).restrict hS).baseChange
          (AlgebraicClosure k)) =
      (SymmetricPower.map (n + 1) (A.baseChange (AlgebraicClosure k))).comp
        (symmetricPower_baseChange_rangeTargetMap (k := k) (V := V) n S) := by
  dsimp
  -- Compare both sides on simple tensors in the scalar extension of the stabilized range.
  apply TensorProduct.AlgebraTensorModule.ext
  intro a x
  simp [symmetricPower_baseChange_rangeTargetMap_tmul, LinearMap.baseChange_tmul]
  have h :=
    LinearMap.congr_fun
      (symmetricPower_baseChange_targetMap_intertwines
        (k := k) (V := V) (A := A) (n := n + 1))
      ((x : SymmetricPower k (Fin (n + 1))
        (TensorProduct k (AlgebraicClosure k) V)))
  -- The ambient target-map intertwining identity already contains the needed formula on the
  -- underlying range vector, so only scalar extension bookkeeping remains.
  simp only [LinearMap.comp_apply] at h
  simpa using congrArg (fun y ↦ a • y) h

/-- Helper for Exercise 9-9.1-3: in degree `0`, scalar extension already identifies the two
one-dimensional symmetric powers, and both induced endomorphisms are the identity. -/
theorem symmetricPower_baseChange_conj_zero
    (A : V →ₗ[k] V) :
    ∃ e :
        TensorProduct k (AlgebraicClosure k) (SymmetricPower k (Fin 0) V) ≃ₗ[AlgebraicClosure k]
          SymmetricPower (AlgebraicClosure k) (Fin 0)
            (TensorProduct k (AlgebraicClosure k) V),
      e.conj ((SymmetricPower.map 0 A).baseChange (AlgebraicClosure k)) =
        SymmetricPower.map 0 (A.baseChange (AlgebraicClosure k)) := by
  let e :
      TensorProduct k (AlgebraicClosure k) (SymmetricPower k (Fin 0) V) ≃ₗ[AlgebraicClosure k]
        SymmetricPower (AlgebraicClosure k) (Fin 0)
          (TensorProduct k (AlgebraicClosure k) V) :=
    LinearEquiv.ofFinrankEq _ _ <| by
      calc
        Module.finrank (AlgebraicClosure k)
            (TensorProduct k (AlgebraicClosure k) (SymmetricPower k (Fin 0) V)) =
            Module.finrank k (SymmetricPower k (Fin 0) V) := by
              simpa using
                (Module.finrank_baseChange
                  (R := AlgebraicClosure k) (S := k)
                  (M' := SymmetricPower k (Fin 0) V))
        _ = 1 := by
              simpa using (finrank_symmetricPower_zero (k := k) (V := V))
        _ =
            Module.finrank (AlgebraicClosure k)
              (SymmetricPower (AlgebraicClosure k) (Fin 0)
                (TensorProduct k (AlgebraicClosure k) V)) := by
              symm
              simpa using
                (finrank_symmetricPower_zero
                  (k := AlgebraicClosure k)
                  (V := TensorProduct k (AlgebraicClosure k) V))
  refine ⟨e, ?_⟩
  -- In degree `0`, both actions are identities, so any equivalence conjugates them.
  rw [symmetricPower_map_zero_eq_id (k := k) (V := V) (A := A), LinearMap.baseChange_id,
    symmetricPower_map_zero_eq_id (k := AlgebraicClosure k)
      (V := TensorProduct k (AlgebraicClosure k) V)
      (A := A.baseChange (AlgebraicClosure k))]
  ext x
  simp [e, LinearEquiv.conj_apply]

/-- Helper for Exercise 9-9.1-3: once the positive-degree comparison from the scalar-extended
stabilized range to the genuine `K`-symmetric power is bijective, the range-model conjugacy
upgrades to the required conjugacy on the genuine target. -/
theorem symmetricPower_baseChange_rangeTargetMap_bijective_of_finrank_eq
    (n : ℕ)
    (hdim :
      let S :
          Submodule k
            (SymmetricPower k (Fin (n + 1))
              (TensorProduct k (AlgebraicClosure k) V)) :=
        LinearMap.range
          (SymmetricPower.map (n + 1)
            (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
              V →ₗ[k] TensorProduct k (AlgebraicClosure k) V))
      Module.finrank (AlgebraicClosure k) (TensorProduct k (AlgebraicClosure k) S) =
        Module.finrank (AlgebraicClosure k)
          (SymmetricPower (AlgebraicClosure k) (Fin (n + 1))
            (TensorProduct k (AlgebraicClosure k) V)))
    (hsurj :
      let S :
          Submodule k
            (SymmetricPower k (Fin (n + 1))
              (TensorProduct k (AlgebraicClosure k) V)) :=
        LinearMap.range
          (SymmetricPower.map (n + 1)
            (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
              V →ₗ[k] TensorProduct k (AlgebraicClosure k) V))
      Function.Surjective
        (symmetricPower_baseChange_rangeTargetMap (k := k) (V := V) n S)) :
    let S :
        Submodule k
          (SymmetricPower k (Fin (n + 1))
            (TensorProduct k (AlgebraicClosure k) V)) :=
      LinearMap.range
        (SymmetricPower.map (n + 1)
          (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
            V →ₗ[k] TensorProduct k (AlgebraicClosure k) V))
    Function.Bijective
      (symmetricPower_baseChange_rangeTargetMap (k := k) (V := V) n S) := by
  dsimp at hdim hsurj ⊢
  let S :
      Submodule k
        (SymmetricPower k (Fin (n + 1))
          (TensorProduct k (AlgebraicClosure k) V)) :=
    LinearMap.range
      (SymmetricPower.map (n + 1)
        (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
          V →ₗ[k] TensorProduct k (AlgebraicClosure k) V))
  refine ⟨?_, hsurj⟩
  -- Equal source and target finrank convert the existing surjectivity into injectivity.
  exact
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := symmetricPower_baseChange_rangeTargetMap (k := k) (V := V) n S)
      hdim).2 hsurj

/-- Helper for Exercise 9-9.1-3: once Serre's included generators span the genuine target and the
scalar-extended stabilized range has the same finrank as that target, the range-to-target
comparison is bijective. This isolates the positive-degree base-change hole to the exact span and
dimension inputs still missing from the source proof. -/
theorem symmetricPower_baseChange_rangeTargetMap_bijective_of_generator_span_and_finrank
    (n : ℕ)
    (hspan :
      Submodule.span (AlgebraicClosure k)
        (Set.range fun f : Fin (n + 1) → V ↦
          SymmetricPower.mk (AlgebraicClosure k) (Fin (n + 1))
            (TensorProduct k (AlgebraicClosure k) V)
            (PiTensorProduct.tprod (AlgebraicClosure k)
              fun i ↦ ((TensorProduct.mk k (AlgebraicClosure k) V) 1) (f i))) = ⊤)
    (hdim :
      let S :
          Submodule k
            (SymmetricPower k (Fin (n + 1))
              (TensorProduct k (AlgebraicClosure k) V)) :=
        LinearMap.range
          (SymmetricPower.map (n + 1)
            (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
              V →ₗ[k] TensorProduct k (AlgebraicClosure k) V))
      Module.finrank (AlgebraicClosure k) (TensorProduct k (AlgebraicClosure k) S) =
        Module.finrank (AlgebraicClosure k)
          (SymmetricPower (AlgebraicClosure k) (Fin (n + 1))
            (TensorProduct k (AlgebraicClosure k) V))) :
    let S :
        Submodule k
          (SymmetricPower k (Fin (n + 1))
            (TensorProduct k (AlgebraicClosure k) V)) :=
      LinearMap.range
        (SymmetricPower.map (n + 1)
          (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
            V →ₗ[k] TensorProduct k (AlgebraicClosure k) V))
    Function.Bijective
      (symmetricPower_baseChange_rangeTargetMap (k := k) (V := V) n S) := by
  have hsurj :
      let S :
          Submodule k
            (SymmetricPower k (Fin (n + 1))
              (TensorProduct k (AlgebraicClosure k) V)) :=
        LinearMap.range
          (SymmetricPower.map (n + 1)
            (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
              V →ₗ[k] TensorProduct k (AlgebraicClosure k) V))
      Function.Surjective
        (symmetricPower_baseChange_rangeTargetMap (k := k) (V := V) n S) := by
    -- The source-faithful spanning statement already gives surjectivity on the genuine target.
    exact
      symmetricPower_baseChange_rangeTargetMap_surjective_of_generator_span
        (k := k) (V := V) n hspan
  -- With surjectivity in hand, the remaining finrank equality upgrades the comparison to a
  -- bijection by the standard finite-dimensional rank argument.
  exact
    symmetricPower_baseChange_rangeTargetMap_bijective_of_finrank_eq
      (k := k) (V := V) n hdim hsurj

/-- Helper for Exercise 9-9.1-3: the positive-degree base-change comparison becomes bijective as
soon as every pure symmetric generator belongs to the span of the included generators and the
source and target have the same finrank. This packages the remaining span-top step into the exact
pure-generator membership statement still missing from Serre's source route. -/
theorem symmetricPower_baseChange_rangeTargetMap_bijective_of_tprod_mem_and_finrank
    (n : ℕ)
    (hmem :
      ∀ f : Fin (n + 1) → TensorProduct k (AlgebraicClosure k) V,
        SymmetricPower.mk (AlgebraicClosure k) (Fin (n + 1))
            (TensorProduct k (AlgebraicClosure k) V)
            (PiTensorProduct.tprod (AlgebraicClosure k) f) ∈
          Submodule.span (AlgebraicClosure k)
            (Set.range fun g : Fin (n + 1) → V ↦
              SymmetricPower.mk (AlgebraicClosure k) (Fin (n + 1))
                (TensorProduct k (AlgebraicClosure k) V)
                (PiTensorProduct.tprod (AlgebraicClosure k)
                  fun i ↦ ((TensorProduct.mk k (AlgebraicClosure k) V) 1) (g i))))
    (hdim :
      let S :
          Submodule k
            (SymmetricPower k (Fin (n + 1))
              (TensorProduct k (AlgebraicClosure k) V)) :=
        LinearMap.range
          (SymmetricPower.map (n + 1)
            (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
              V →ₗ[k] TensorProduct k (AlgebraicClosure k) V))
      Module.finrank (AlgebraicClosure k) (TensorProduct k (AlgebraicClosure k) S) =
        Module.finrank (AlgebraicClosure k)
          (SymmetricPower (AlgebraicClosure k) (Fin (n + 1))
            (TensorProduct k (AlgebraicClosure k) V))) :
    let S :
        Submodule k
          (SymmetricPower k (Fin (n + 1))
            (TensorProduct k (AlgebraicClosure k) V)) :=
      LinearMap.range
        (SymmetricPower.map (n + 1)
          (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
            V →ₗ[k] TensorProduct k (AlgebraicClosure k) V))
    Function.Bijective
      (symmetricPower_baseChange_rangeTargetMap (k := k) (V := V) n S) := by
  have hspan :
      Submodule.span (AlgebraicClosure k)
        (Set.range fun g : Fin (n + 1) → V ↦
          SymmetricPower.mk (AlgebraicClosure k) (Fin (n + 1))
            (TensorProduct k (AlgebraicClosure k) V)
            (PiTensorProduct.tprod (AlgebraicClosure k)
              fun i ↦ ((TensorProduct.mk k (AlgebraicClosure k) V) 1) (g i))) = ⊤ := by
    -- The previous helper turns the global span-top statement into the pure-generator
    -- membership statement `hmem`.
    exact
      symmetricPower_includeRight_generators_span_top_of_tprod_mem
        (k := k) (V := V) n hmem
  exact
    symmetricPower_baseChange_rangeTargetMap_bijective_of_generator_span_and_finrank
      (k := k) (V := V) n hspan hdim

/-- Helper for Exercise 9-9.1-3: once the pure-generator membership statement is known, the only
remaining dimension input for the positive-degree comparison is the genuine target finrank
equality. This packages that target equality into the `hdim` shape used by the existing
bijection theorem. -/
theorem symmetricPower_baseChange_rangeTargetMap_bijective_of_tprod_mem_and_target_finrank
    (n : ℕ)
    (hmem :
      ∀ f : Fin (n + 1) → TensorProduct k (AlgebraicClosure k) V,
        SymmetricPower.mk (AlgebraicClosure k) (Fin (n + 1))
            (TensorProduct k (AlgebraicClosure k) V)
            (PiTensorProduct.tprod (AlgebraicClosure k) f) ∈
          Submodule.span (AlgebraicClosure k)
            (Set.range fun g : Fin (n + 1) → V ↦
              SymmetricPower.mk (AlgebraicClosure k) (Fin (n + 1))
                (TensorProduct k (AlgebraicClosure k) V)
                (PiTensorProduct.tprod (AlgebraicClosure k)
                  fun i ↦ ((TensorProduct.mk k (AlgebraicClosure k) V) 1) (g i))))
    (htarget :
      Module.finrank (AlgebraicClosure k)
        (SymmetricPower (AlgebraicClosure k) (Fin (n + 1))
          (TensorProduct k (AlgebraicClosure k) V)) =
        Module.finrank k (SymmetricPower k (Fin (n + 1)) V)) :
    let S :
        Submodule k
          (SymmetricPower k (Fin (n + 1))
            (TensorProduct k (AlgebraicClosure k) V)) :=
      LinearMap.range
        (SymmetricPower.map (n + 1)
          (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
            V →ₗ[k] TensorProduct k (AlgebraicClosure k) V))
    Function.Bijective
      (symmetricPower_baseChange_rangeTargetMap (k := k) (V := V) n S) := by
  have hdim :
      let S :
          Submodule k
            (SymmetricPower k (Fin (n + 1))
              (TensorProduct k (AlgebraicClosure k) V)) :=
        LinearMap.range
          (SymmetricPower.map (n + 1)
            (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
              V →ₗ[k] TensorProduct k (AlgebraicClosure k) V))
      Module.finrank (AlgebraicClosure k) (TensorProduct k (AlgebraicClosure k) S) =
        Module.finrank (AlgebraicClosure k)
          (SymmetricPower (AlgebraicClosure k) (Fin (n + 1))
            (TensorProduct k (AlgebraicClosure k) V)) := by
    dsimp
    -- Replace the source finrank by the already computed stabilized-range finrank, then use the
    -- target finrank equality `htarget`.
    calc
      Module.finrank (AlgebraicClosure k)
          (TensorProduct k (AlgebraicClosure k)
            (LinearMap.range
              (SymmetricPower.map (n + 1)
                (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
                  V →ₗ[k] TensorProduct k (AlgebraicClosure k) V)))) =
        Module.finrank k (SymmetricPower k (Fin (n + 1)) V) := by
            simpa using
              finrank_symmetricPower_includeRight_range_baseChange
                (k := k) (V := V) n
      _ =
        Module.finrank (AlgebraicClosure k)
          (SymmetricPower (AlgebraicClosure k) (Fin (n + 1))
            (TensorProduct k (AlgebraicClosure k) V)) := by
              simpa using htarget.symm
  -- The old package now applies with the target finrank equality inserted as `hdim`.
  exact
    symmetricPower_baseChange_rangeTargetMap_bijective_of_tprod_mem_and_finrank
      (k := k) (V := V) n hmem hdim

/-- Helper for Exercise 9-9.1-3: once the positive-degree comparison from the scalar-extended
stabilized range to the genuine `K`-symmetric power is bijective, the range-model conjugacy
upgrades to the required conjugacy on the genuine target. -/
theorem symmetricPower_baseChange_conj_of_bijective_rangeTargetMap
    (A : V →ₗ[k] V) (n : ℕ)
    (hbij :
      let S :
          Submodule k
            (SymmetricPower k (Fin (n + 1))
              (TensorProduct k (AlgebraicClosure k) V)) :=
        LinearMap.range
          (SymmetricPower.map (n + 1)
            (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
              V →ₗ[k] TensorProduct k (AlgebraicClosure k) V))
      Function.Bijective
        (symmetricPower_baseChange_rangeTargetMap (k := k) (V := V) n S)) :
    ∃ e :
        TensorProduct k (AlgebraicClosure k) (SymmetricPower k (Fin (n + 1)) V) ≃ₗ[AlgebraicClosure k]
          SymmetricPower (AlgebraicClosure k) (Fin (n + 1))
            (TensorProduct k (AlgebraicClosure k) V),
      e.conj ((SymmetricPower.map (n + 1) A).baseChange (AlgebraicClosure k)) =
        SymmetricPower.map (n + 1) (A.baseChange (AlgebraicClosure k)) := by
  let S :
      Submodule k
        (SymmetricPower k (Fin (n + 1))
          (TensorProduct k (AlgebraicClosure k) V)) :=
    LinearMap.range
      (SymmetricPower.map (n + 1)
        (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
          V →ₗ[k] TensorProduct k (AlgebraicClosure k) V))
  let hS :
      S ≤ S.comap
        (SymmetricPower.map (n + 1)
          ((((A.baseChange (AlgebraicClosure k)).restrictScalars k) :
            TensorProduct k (AlgebraicClosure k) V →ₗ[k]
              TensorProduct k (AlgebraicClosure k) V))) :=
    symmetricPower_includeRight_range_le_comap (k := k) (V := V) (A := A) (n + 1)
  let eRange :
      SymmetricPower k (Fin (n + 1)) V ≃ₗ[k] S :=
    symmetricPower_includeRight_range_equiv (k := k) (V := V) (n + 1)
  let eTarget :
      TensorProduct k (AlgebraicClosure k) S ≃ₗ[AlgebraicClosure k]
        SymmetricPower (AlgebraicClosure k) (Fin (n + 1))
          (TensorProduct k (AlgebraicClosure k) V) :=
    LinearEquiv.ofBijective
      (symmetricPower_baseChange_rangeTargetMap (k := k) (V := V) n S) (by
        simpa [S] using hbij)
  let eRangeBase :=
    eRange.baseChange k (AlgebraicClosure k)
  let e :=
    eRangeBase.trans eTarget
  refine ⟨e, ?_⟩
  have hRange :
      eRangeBase.conj ((SymmetricPower.map (n + 1) A).baseChange (AlgebraicClosure k)) =
        ((SymmetricPower.map (n + 1)
            ((((A.baseChange (AlgebraicClosure k)).restrictScalars k) :
              TensorProduct k (AlgebraicClosure k) V →ₗ[k]
                TensorProduct k (AlgebraicClosure k) V))).restrict hS).baseChange
          (AlgebraicClosure k) := by
    -- The scalar-extended range model already conjugates the literal base change of `Sym^(n+1) A`
    -- to the restricted action on the stabilized range.
    simpa [eRangeBase, eRange, S, hS] using
      symmetricPower_includeRight_range_baseChange_conj
        (k := k) (V := V) (A := A) (n := n + 1)
  have hTarget :
      eTarget.conj
          (((SymmetricPower.map (n + 1)
              ((((A.baseChange (AlgebraicClosure k)).restrictScalars k) :
                TensorProduct k (AlgebraicClosure k) V →ₗ[k]
                  TensorProduct k (AlgebraicClosure k) V))).restrict hS).baseChange
            (AlgebraicClosure k)) =
        SymmetricPower.map (n + 1) (A.baseChange (AlgebraicClosure k)) := by
    -- The bijective comparison map upgrades the restricted-range intertwining identity to an
    -- actual conjugacy on the genuine `K`-symmetric power.
    ext x
    have hintertwine :=
      symmetricPower_baseChange_rangeTargetMap_intertwines
        (k := k) (V := V) (A := A) n
    dsimp [S, hS] at hintertwine
    have h :=
      LinearMap.congr_fun
        hintertwine
        (eTarget.symm x)
    simp only [LinearMap.comp_apply] at h
    have hx :
        symmetricPower_baseChange_rangeTargetMap (k := k) (V := V) n S (eTarget.symm x) = x := by
      simp [eTarget]
    change
      symmetricPower_baseChange_rangeTargetMap (k := k) (V := V) n S
          ((((SymmetricPower.map (n + 1)
                ((((A.baseChange (AlgebraicClosure k)).restrictScalars k) :
                  TensorProduct k (AlgebraicClosure k) V →ₗ[k]
                    TensorProduct k (AlgebraicClosure k) V))).restrict hS).baseChange
              (AlgebraicClosure k)) (eTarget.symm x)) =
        (SymmetricPower.map (n + 1) (A.baseChange (AlgebraicClosure k))) x
    simpa [S, hS, hx] using h
  -- Route correction: the final conjugacy is obtained by composing the stabilized-range conjugacy
  -- with the now-bijective range-to-target comparison.
  calc
    e.conj ((SymmetricPower.map (n + 1) A).baseChange (AlgebraicClosure k)) =
        eTarget.conj
          (eRangeBase.conj
            ((SymmetricPower.map (n + 1) A).baseChange (AlgebraicClosure k))) := by
              ext x
              rfl
    _ = eTarget.conj
          (((SymmetricPower.map (n + 1)
              ((((A.baseChange (AlgebraicClosure k)).restrictScalars k) :
                TensorProduct k (AlgebraicClosure k) V →ₗ[k]
                  TensorProduct k (AlgebraicClosure k) V))).restrict hS).baseChange
            (AlgebraicClosure k)) := by
              rw [hRange]
    _ = SymmetricPower.map (n + 1) (A.baseChange (AlgebraicClosure k)) := hTarget

/-- Helper for Exercise 9-9.1-3: once the remaining source-faithful pure-generator membership
statement and the target finrank equality are available, the positive-degree scalar-extension
conjugacy follows immediately from the bijective comparison map. -/
theorem symmetricPower_baseChange_conj_pos_of_tprod_mem_and_finrank
    (A : V →ₗ[k] V) (n : ℕ)
    (hmem :
      ∀ f : Fin (n + 1) → TensorProduct k (AlgebraicClosure k) V,
        SymmetricPower.mk (AlgebraicClosure k) (Fin (n + 1))
            (TensorProduct k (AlgebraicClosure k) V)
            (PiTensorProduct.tprod (AlgebraicClosure k) f) ∈
          Submodule.span (AlgebraicClosure k)
            (Set.range fun g : Fin (n + 1) → V ↦
              SymmetricPower.mk (AlgebraicClosure k) (Fin (n + 1))
                (TensorProduct k (AlgebraicClosure k) V)
                (PiTensorProduct.tprod (AlgebraicClosure k)
                  fun i ↦ ((TensorProduct.mk k (AlgebraicClosure k) V) 1) (g i))))
    (hdim :
      let S :
          Submodule k
            (SymmetricPower k (Fin (n + 1))
              (TensorProduct k (AlgebraicClosure k) V)) :=
        LinearMap.range
          (SymmetricPower.map (n + 1)
            (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
              V →ₗ[k] TensorProduct k (AlgebraicClosure k) V))
      Module.finrank (AlgebraicClosure k) (TensorProduct k (AlgebraicClosure k) S) =
        Module.finrank (AlgebraicClosure k)
          (SymmetricPower (AlgebraicClosure k) (Fin (n + 1))
            (TensorProduct k (AlgebraicClosure k) V))) :
    ∃ e :
        TensorProduct k (AlgebraicClosure k) (SymmetricPower k (Fin (n + 1)) V) ≃ₗ[AlgebraicClosure k]
          SymmetricPower (AlgebraicClosure k) (Fin (n + 1))
            (TensorProduct k (AlgebraicClosure k) V),
      e.conj ((SymmetricPower.map (n + 1) A).baseChange (AlgebraicClosure k)) =
        SymmetricPower.map (n + 1) (A.baseChange (AlgebraicClosure k)) := by
  have hbij :
      let S :
          Submodule k
            (SymmetricPower k (Fin (n + 1))
              (TensorProduct k (AlgebraicClosure k) V)) :=
        LinearMap.range
          (SymmetricPower.map (n + 1)
            (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
              V →ₗ[k] TensorProduct k (AlgebraicClosure k) V))
      Function.Bijective
        (symmetricPower_baseChange_rangeTargetMap (k := k) (V := V) n S) := by
    -- The previous packaging theorem isolates the remaining positive-degree work in the exact
    -- source-faithful inputs `hmem` and `hdim`.
    exact
      symmetricPower_baseChange_rangeTargetMap_bijective_of_tprod_mem_and_finrank
        (k := k) (V := V) n hmem hdim
  -- Once the comparison map is bijective, the already constructed range-model conjugacy upgrades
  -- to the genuine scalar-extended symmetric power.
  exact
    symmetricPower_baseChange_conj_of_bijective_rangeTargetMap
      (k := k) (V := V) (A := A) n hbij

/-- Helper for Exercise 9-9.1-3: once the remaining source-faithful pure-generator membership
statement and the genuine target finrank equality are available, the positive-degree
scalar-extension conjugacy follows immediately. This keeps the final proof focused on Serre's two
missing inputs rather than re-expanding the bijectivity packaging. -/
theorem symmetricPower_baseChange_conj_pos_of_tprod_mem_and_target_finrank
    (A : V →ₗ[k] V) (n : ℕ)
    (hmem :
      ∀ f : Fin (n + 1) → TensorProduct k (AlgebraicClosure k) V,
        SymmetricPower.mk (AlgebraicClosure k) (Fin (n + 1))
            (TensorProduct k (AlgebraicClosure k) V)
            (PiTensorProduct.tprod (AlgebraicClosure k) f) ∈
          Submodule.span (AlgebraicClosure k)
            (Set.range fun g : Fin (n + 1) → V ↦
              SymmetricPower.mk (AlgebraicClosure k) (Fin (n + 1))
                (TensorProduct k (AlgebraicClosure k) V)
                (PiTensorProduct.tprod (AlgebraicClosure k)
                  fun i ↦ ((TensorProduct.mk k (AlgebraicClosure k) V) 1) (g i))))
    (htarget :
      Module.finrank (AlgebraicClosure k)
        (SymmetricPower (AlgebraicClosure k) (Fin (n + 1))
          (TensorProduct k (AlgebraicClosure k) V)) =
        Module.finrank k (SymmetricPower k (Fin (n + 1)) V)) :
    ∃ e :
        TensorProduct k (AlgebraicClosure k) (SymmetricPower k (Fin (n + 1)) V) ≃ₗ[AlgebraicClosure k]
          SymmetricPower (AlgebraicClosure k) (Fin (n + 1))
            (TensorProduct k (AlgebraicClosure k) V),
      e.conj ((SymmetricPower.map (n + 1) A).baseChange (AlgebraicClosure k)) =
        SymmetricPower.map (n + 1) (A.baseChange (AlgebraicClosure k)) := by
  have hbij :
      let S :
          Submodule k
            (SymmetricPower k (Fin (n + 1))
              (TensorProduct k (AlgebraicClosure k) V)) :=
        LinearMap.range
          (SymmetricPower.map (n + 1)
            (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
              V →ₗ[k] TensorProduct k (AlgebraicClosure k) V))
      Function.Bijective
        (symmetricPower_baseChange_rangeTargetMap (k := k) (V := V) n S) := by
    -- The previous package already converts the exact missing source inputs `hmem` and `htarget`
    -- into bijectivity of the comparison map.
    exact
      symmetricPower_baseChange_rangeTargetMap_bijective_of_tprod_mem_and_target_finrank
        (k := k) (V := V) n hmem htarget
  -- With the comparison map now bijective, the existing range-model conjugacy upgrades directly
  -- to the genuine `K`-symmetric power.
  exact
    symmetricPower_baseChange_conj_of_bijective_rangeTargetMap
      (k := k) (V := V) (A := A) n hbij

/-- Helper for Exercise 9-9.1-3: once the included generators span the genuine target and the
scalar-extended stabilized range has the same finrank as that target, the positive-degree
scalar-extension conjugacy follows immediately from the packaged bijectivity step. -/
theorem symmetricPower_baseChange_conj_pos_of_generator_span_and_finrank
    (A : V →ₗ[k] V) (n : ℕ)
    (hspan :
      Submodule.span (AlgebraicClosure k)
        (Set.range fun g : Fin (n + 1) → V ↦
          SymmetricPower.mk (AlgebraicClosure k) (Fin (n + 1))
            (TensorProduct k (AlgebraicClosure k) V)
            (PiTensorProduct.tprod (AlgebraicClosure k)
              fun i ↦ ((TensorProduct.mk k (AlgebraicClosure k) V) 1) (g i))) = ⊤)
    (hdim :
      let S :
          Submodule k
            (SymmetricPower k (Fin (n + 1))
              (TensorProduct k (AlgebraicClosure k) V)) :=
        LinearMap.range
          (SymmetricPower.map (n + 1)
            (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
              V →ₗ[k] TensorProduct k (AlgebraicClosure k) V))
      Module.finrank (AlgebraicClosure k) (TensorProduct k (AlgebraicClosure k) S) =
        Module.finrank (AlgebraicClosure k)
          (SymmetricPower (AlgebraicClosure k) (Fin (n + 1))
            (TensorProduct k (AlgebraicClosure k) V))) :
    ∃ e :
        TensorProduct k (AlgebraicClosure k) (SymmetricPower k (Fin (n + 1)) V) ≃ₗ[AlgebraicClosure k]
          SymmetricPower (AlgebraicClosure k) (Fin (n + 1))
            (TensorProduct k (AlgebraicClosure k) V),
      e.conj ((SymmetricPower.map (n + 1) A).baseChange (AlgebraicClosure k)) =
        SymmetricPower.map (n + 1) (A.baseChange (AlgebraicClosure k)) := by
  have hbij :
      let S :
          Submodule k
            (SymmetricPower k (Fin (n + 1))
              (TensorProduct k (AlgebraicClosure k) V)) :=
        LinearMap.range
          (SymmetricPower.map (n + 1)
            (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
              V →ₗ[k] TensorProduct k (AlgebraicClosure k) V))
      Function.Bijective
        (symmetricPower_baseChange_rangeTargetMap (k := k) (V := V) n S) := by
    -- The earlier generator-span and finrank package is exactly the positive-degree input needed
    -- for the final comparison map.
    exact
      symmetricPower_baseChange_rangeTargetMap_bijective_of_generator_span_and_finrank
        (k := k) (V := V) n hspan hdim
  exact
    symmetricPower_baseChange_conj_of_bijective_rangeTargetMap
      (k := k) (V := V) (A := A) n hbij

/-- Helper for Exercise 9-9.1-3: if each tensor factor already lies in the span of the included
vectors `1 ⊗ v`, then multilinearity expands the pure symmetric generator into a finite sum of the
corresponding included symmetric generators. -/
theorem symmetricPower_mk_mem_span_includeRight_of_factor_mem_span
    (n : ℕ)
    (f : Fin (n + 1) → TensorProduct k (AlgebraicClosure k) V)
    (hf :
      ∀ i, f i ∈
        Submodule.span (AlgebraicClosure k)
          (Set.range (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
            V →ₗ[k] TensorProduct k (AlgebraicClosure k) V))) :
    SymmetricPower.mk (AlgebraicClosure k) (Fin (n + 1))
        (TensorProduct k (AlgebraicClosure k) V)
        (PiTensorProduct.tprod (AlgebraicClosure k) f) ∈
      Submodule.span (AlgebraicClosure k)
        (Set.range fun g : Fin (n + 1) → V ↦
          SymmetricPower.mk (AlgebraicClosure k) (Fin (n + 1))
            (TensorProduct k (AlgebraicClosure k) V)
            (PiTensorProduct.tprod (AlgebraicClosure k)
              fun i ↦ ((TensorProduct.mk k (AlgebraicClosure k) V) 1) (g i))) := by
  let includeRight : V →ₗ[k] TensorProduct k (AlgebraicClosure k) V :=
    ((TensorProduct.mk k (AlgebraicClosure k) V) 1)
  classical
  choose coeff supp hsubset hsupport hsum using fun i =>
    (Submodule.mem_span_iff_exists_finset_subset).1 (hf i)
  have hf_eq : f = fun i ↦ ∑ x ∈ supp i, coeff i x • x := by
    -- Rewrite each tensor factor as a finite linear combination of included vectors.
    funext i
    symm
    exact hsum i
  change
    SymmetricPower.tprod (AlgebraicClosure k)
        (ι := Fin (n + 1))
        (M := TensorProduct k (AlgebraicClosure k) V) f ∈
      Submodule.span (AlgebraicClosure k)
        (Set.range fun g : Fin (n + 1) → V ↦
          SymmetricPower.tprod (AlgebraicClosure k)
            (ι := Fin (n + 1))
            (M := TensorProduct k (AlgebraicClosure k) V)
            (fun i ↦ ((TensorProduct.mk k (AlgebraicClosure k) V) 1) (g i)))
  rw [hf_eq]
  rw [(SymmetricPower.tprod (AlgebraicClosure k)
      (ι := Fin (n + 1))
      (M := TensorProduct k (AlgebraicClosure k) V)).map_sum_finset
        (g := fun i x ↦ coeff i x • x) (A := supp)]
  refine sum_mem ?_
  intro r hr
  let g : Fin (n + 1) → V := fun i ↦
    Classical.choose (hsubset i ((Fintype.mem_piFinset.1 hr) i))
  have hg : ∀ i, includeRight (g i) = r i := by
    intro i
    exact Classical.choose_spec (hsubset i ((Fintype.mem_piFinset.1 hr) i))
  have hterm :
      (fun i ↦ coeff i (r i) • r i) = fun i ↦ (coeff i (r i)) ⊗ₜ[k] g i := by
    -- After choosing generators for the finite coordinate expansions, each selected summand is a
    -- pure-tensor symmetric generator of the shape handled by the earlier scalar-extraction lemma.
    funext i
    calc
      coeff i (r i) • r i = coeff i (r i) • includeRight (g i) := by rw [hg i]
      _ = (coeff i (r i)) ⊗ₜ[k] g i := by
            simpa [includeRight] using
              (TensorProduct.tmul_eq_smul_one_tmul
                (R := k) (S := AlgebraicClosure k) (s := coeff i (r i)) (m := g i)).symm
  -- Each expanded summand is now one of the already-controlled pure-tensor generators.
  simpa [SymmetricPower.tprod, hterm] using
    symmetricPower_mk_tmul_mem_span_includeRight
      (k := k) (V := V) (n := n + 1)
      (a := fun i ↦ coeff i (r i)) (f := g)

/-- Helper for Exercise 9-9.1-3: once every pure symmetric generator of the genuine target lies in
the span of the included generators, the direct comparison
`K ⊗ Sym^(n+1)_k(V) → Sym^(n+1)_K(K ⊗ V)` is already surjective. This packages the range-model
surjectivity together with the scalar-extended invariant-image equivalence. -/
theorem symmetricPower_baseChange_comparison_surjective_of_tprod_mem
    (n : ℕ)
    (hmem :
      ∀ f : Fin (n + 1) → TensorProduct k (AlgebraicClosure k) V,
        SymmetricPower.mk (AlgebraicClosure k) (Fin (n + 1))
            (TensorProduct k (AlgebraicClosure k) V)
            (PiTensorProduct.tprod (AlgebraicClosure k) f) ∈
          Submodule.span (AlgebraicClosure k)
            (Set.range fun g : Fin (n + 1) → V ↦
              SymmetricPower.mk (AlgebraicClosure k) (Fin (n + 1))
                (TensorProduct k (AlgebraicClosure k) V)
                (PiTensorProduct.tprod (AlgebraicClosure k)
                  fun i ↦ ((TensorProduct.mk k (AlgebraicClosure k) V) 1) (g i)))) :
    Function.Surjective
      (let eRange := symmetricPower_includeRight_range_equiv (k := k) (V := V) (n + 1)
       let i :=
          SymmetricPower.map (n + 1)
            (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
              V →ₗ[k] TensorProduct k (AlgebraicClosure k) V)
       let S := LinearMap.range i
       (symmetricPower_baseChange_rangeTargetMap (k := k) (V := V) n S).comp
        ((eRange.baseChange k (AlgebraicClosure k)).toLinearMap)) := by
  let eRange := symmetricPower_includeRight_range_equiv (k := k) (V := V) (n + 1)
  let i :=
    SymmetricPower.map (n + 1)
      (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
        V →ₗ[k] TensorProduct k (AlgebraicClosure k) V)
  let S := LinearMap.range i
  have hspan :
      Submodule.span (AlgebraicClosure k)
        (Set.range fun g : Fin (n + 1) → V ↦
          SymmetricPower.mk (AlgebraicClosure k) (Fin (n + 1))
            (TensorProduct k (AlgebraicClosure k) V)
            (PiTensorProduct.tprod (AlgebraicClosure k)
              fun i ↦ ((TensorProduct.mk k (AlgebraicClosure k) V) 1) (g i))) = ⊤ := by
    -- The coordinatewise pure-generator hypothesis upgrades to the global generator span needed by
    -- the range-to-target comparison.
    exact
      symmetricPower_includeRight_generators_span_top_of_tprod_mem
        (k := k) (V := V) n hmem
  have hsurjRange :
      Function.Surjective
        (symmetricPower_baseChange_rangeTargetMap (k := k) (V := V) n S) := by
    -- The range-model comparison is therefore already surjective on the genuine target.
    simpa [S] using
      symmetricPower_baseChange_rangeTargetMap_surjective_of_generator_span
        (k := k) (V := V) n hspan
  intro y
  rcases hsurjRange y with ⟨x, hx⟩
  rcases (eRange.baseChange k (AlgebraicClosure k)).surjective x with ⟨z, rfl⟩
  -- Pull the preimage back through the scalar-extended invariant-image equivalence.
  exact ⟨z, by simpa [eRange, i, S] using hx⟩

/-- Helper for Exercise 9-9.1-3: once every pure symmetric generator belongs to the span of the
included generators, the range-to-target comparison is already surjective. Hence the genuine
`K`-symmetric power has `K`-dimension at most the original `k`-symmetric power. -/
theorem finrank_symmetricPower_baseChange_target_le_of_tprod_mem
    (n : ℕ)
    (hmem :
      ∀ f : Fin (n + 1) → TensorProduct k (AlgebraicClosure k) V,
        SymmetricPower.mk (AlgebraicClosure k) (Fin (n + 1))
            (TensorProduct k (AlgebraicClosure k) V)
            (PiTensorProduct.tprod (AlgebraicClosure k) f) ∈
          Submodule.span (AlgebraicClosure k)
            (Set.range fun g : Fin (n + 1) → V ↦
              SymmetricPower.mk (AlgebraicClosure k) (Fin (n + 1))
                (TensorProduct k (AlgebraicClosure k) V)
                (PiTensorProduct.tprod (AlgebraicClosure k)
                  fun i ↦ ((TensorProduct.mk k (AlgebraicClosure k) V) 1) (g i)))) :
    Module.finrank (AlgebraicClosure k)
      (SymmetricPower (AlgebraicClosure k) (Fin (n + 1))
        (TensorProduct k (AlgebraicClosure k) V)) ≤
      Module.finrank k (SymmetricPower k (Fin (n + 1)) V) := by
  have hsurj :
      Function.Surjective
        (let eRange := symmetricPower_includeRight_range_equiv (k := k) (V := V) (n + 1)
         let i :=
            SymmetricPower.map (n + 1)
              (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
                V →ₗ[k] TensorProduct k (AlgebraicClosure k) V)
         let S := LinearMap.range i
         (symmetricPower_baseChange_rangeTargetMap (k := k) (V := V) n S).comp
          ((eRange.baseChange k (AlgebraicClosure k)).toLinearMap)) := by
    -- Route correction: package the range-model surjectivity and the scalar-extended invariant
    -- image equivalence into one direct comparison map from `K ⊗ Sym^(n+1)_k(V)`.
    exact
      symmetricPower_baseChange_comparison_surjective_of_tprod_mem
        (k := k) (V := V) n hmem
  -- Compare the target with the already computed scalar extension of the stabilized range.
  calc
    Module.finrank (AlgebraicClosure k)
        (SymmetricPower (AlgebraicClosure k) (Fin (n + 1))
          (TensorProduct k (AlgebraicClosure k) V)) ≤
      Module.finrank (AlgebraicClosure k)
        (TensorProduct k (AlgebraicClosure k) (SymmetricPower k (Fin (n + 1)) V)) := by
        exact
          LinearMap.finrank_le_finrank_of_surjective
            (f := let eRange := symmetricPower_includeRight_range_equiv (k := k) (V := V) (n + 1)
                  let i :=
                    SymmetricPower.map (n + 1)
                      (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
                        V →ₗ[k] TensorProduct k (AlgebraicClosure k) V)
                  let S := LinearMap.range i
                  (symmetricPower_baseChange_rangeTargetMap (k := k) (V := V) n S).comp
                    ((eRange.baseChange k (AlgebraicClosure k)).toLinearMap))
            hsurj
    _ = Module.finrank k (SymmetricPower k (Fin (n + 1)) V) := by
        simpa using
          (Module.finrank_baseChange
            (R := AlgebraicClosure k) (S := k)
            (M' := SymmetricPower k (Fin (n + 1)) V))

/-- Helper for Exercise 9-9.1-3: once the pure-generator span step is known, the remaining
dimension comparison is exactly the injectivity of the already-constructed scalar-extension
comparison `K ⊗ Sym^(n+1)_k(V) → Sym^(n+1)_K(K ⊗ V)`. -/
theorem finrank_symmetricPower_baseChange_target_eq_of_tprod_mem_and_comparison_injective
    (n : ℕ)
    (hmem :
      ∀ f : Fin (n + 1) → TensorProduct k (AlgebraicClosure k) V,
        SymmetricPower.mk (AlgebraicClosure k) (Fin (n + 1))
            (TensorProduct k (AlgebraicClosure k) V)
            (PiTensorProduct.tprod (AlgebraicClosure k) f) ∈
          Submodule.span (AlgebraicClosure k)
            (Set.range fun g : Fin (n + 1) → V ↦
              SymmetricPower.mk (AlgebraicClosure k) (Fin (n + 1))
                (TensorProduct k (AlgebraicClosure k) V)
                (PiTensorProduct.tprod (AlgebraicClosure k)
                  fun i ↦ ((TensorProduct.mk k (AlgebraicClosure k) V) 1) (g i))))
    (hinj :
      Function.Injective
        (let eRange := symmetricPower_includeRight_range_equiv (k := k) (V := V) (n + 1)
         let i :=
            SymmetricPower.map (n + 1)
              (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
                V →ₗ[k] TensorProduct k (AlgebraicClosure k) V)
         let S := LinearMap.range i
         (symmetricPower_baseChange_rangeTargetMap (k := k) (V := V) n S).comp
          ((eRange.baseChange k (AlgebraicClosure k)).toLinearMap))) :
    Module.finrank (AlgebraicClosure k)
      (SymmetricPower (AlgebraicClosure k) (Fin (n + 1))
        (TensorProduct k (AlgebraicClosure k) V)) =
      Module.finrank k (SymmetricPower k (Fin (n + 1)) V) := by
  have htarget_le :
      Module.finrank (AlgebraicClosure k)
        (SymmetricPower (AlgebraicClosure k) (Fin (n + 1))
          (TensorProduct k (AlgebraicClosure k) V)) ≤
        Module.finrank k (SymmetricPower k (Fin (n + 1)) V) := by
    -- The already proved surjectivity package supplies the upper bound on the target finrank.
    exact
      finrank_symmetricPower_baseChange_target_le_of_tprod_mem
        (k := k) (V := V) n hmem
  have htarget_ge :
      Module.finrank k (SymmetricPower k (Fin (n + 1)) V) ≤
        Module.finrank (AlgebraicClosure k)
          (SymmetricPower (AlgebraicClosure k) (Fin (n + 1))
            (TensorProduct k (AlgebraicClosure k) V)) := by
    -- Route correction: the reverse inequality is not a new counting argument once the direct
    -- comparison map is injective; it is just the finite-dimensional rank inequality for that map.
    have hK :
        Module.finrank (AlgebraicClosure k)
          (TensorProduct k (AlgebraicClosure k) (SymmetricPower k (Fin (n + 1)) V)) ≤
          Module.finrank (AlgebraicClosure k)
            (SymmetricPower (AlgebraicClosure k) (Fin (n + 1))
              (TensorProduct k (AlgebraicClosure k) V)) := by
      exact
        LinearMap.finrank_le_finrank_of_injective
          (f := let eRange := symmetricPower_includeRight_range_equiv (k := k) (V := V) (n + 1)
                let i :=
                  SymmetricPower.map (n + 1)
                    (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
                      V →ₗ[k] TensorProduct k (AlgebraicClosure k) V)
                let S := LinearMap.range i
                (symmetricPower_baseChange_rangeTargetMap (k := k) (V := V) n S).comp
                  ((eRange.baseChange k (AlgebraicClosure k)).toLinearMap))
          hinj
    simpa using hK
  exact le_antisymm htarget_le htarget_ge

/-- Helper for Exercise 9-9.1-3: the positive-degree base-change comparison is reduced to the last
explicit equivalence between `K ⊗ Sym^n_k(V)` and `Sym^n_K(K ⊗ V)`. -/
theorem symmetricPower_baseChange_conj_pos
    (A : V →ₗ[k] V) (n : ℕ) :
    ∃ e :
        TensorProduct k (AlgebraicClosure k) (SymmetricPower k (Fin (n + 1)) V) ≃ₗ[AlgebraicClosure k]
          SymmetricPower (AlgebraicClosure k) (Fin (n + 1))
            (TensorProduct k (AlgebraicClosure k) V),
      e.conj ((SymmetricPower.map (n + 1) A).baseChange (AlgebraicClosure k)) =
        SymmetricPower.map (n + 1) (A.baseChange (AlgebraicClosure k)) := by
  have hmem :
      ∀ f : Fin (n + 1) → TensorProduct k (AlgebraicClosure k) V,
        SymmetricPower.tprod (AlgebraicClosure k)
            (ι := Fin (n + 1))
            (M := TensorProduct k (AlgebraicClosure k) V) f ∈
          Submodule.span (AlgebraicClosure k)
            (Set.range fun g : Fin (n + 1) → V ↦
              SymmetricPower.tprod (AlgebraicClosure k)
                (ι := Fin (n + 1))
                (M := TensorProduct k (AlgebraicClosure k) V)
                (fun i ↦ ((TensorProduct.mk k (AlgebraicClosure k) V) 1) (g i))) := by
    intro f
    -- The ambient tensor product is already spanned by the included vectors `1 ⊗ v`, so the new
    -- multilinear helper turns each pure symmetric generator into a finite sum of included ones.
    simpa [SymmetricPower.tprod] using
      symmetricPower_mk_mem_span_includeRight_of_factor_mem_span
        (k := k) (V := V) (n := n) f
        (fun i ↦ by
          rw [tensorProduct_includeRight_span_eq_top (k := k) (V := V)]
          simp)
  have htarget :
      Module.finrank (AlgebraicClosure k)
        (SymmetricPower (AlgebraicClosure k) (Fin (n + 1))
          (TensorProduct k (AlgebraicClosure k) V)) =
        Module.finrank k (SymmetricPower k (Fin (n + 1)) V) := by
    -- The target finrank equality is already the canonical basis-counting identity for symmetric
    -- powers, so no extra injectivity argument is needed here.
    exact finrank_symmetricPower_baseChange_target_eq (k := k) (V := V) n
  -- Route correction: the pure-generator membership step is now proved directly, so the positive
  -- degree base-change conjugacy is reduced to the remaining multichoose finrank identity.
  exact
    symmetricPower_baseChange_conj_pos_of_tprod_mem_and_target_finrank
      (k := k) (V := V) (A := A) n
      (by
        intro f
        simpa [SymmetricPower.tprod] using hmem f)
      htarget

/-- Helper for Exercise 9-9.1-3: for positive degree, the already-constructed invariant-image
model survives scalar extension and packages the stabilized `K ⊗ range` conjugacy data needed for
the final comparison with the genuine `K`-symmetric power. -/
theorem symmetricPower_baseChange_range_model
    (A : V →ₗ[k] V) (n : ℕ) :
    ∃ S :
        Submodule k
          (SymmetricPower k (Fin (n + 1))
            (TensorProduct k (AlgebraicClosure k) V)),
      ∃ hS :
          S ≤ S.comap
            (SymmetricPower.map (n + 1)
              ((((A.baseChange (AlgebraicClosure k)).restrictScalars k) :
                TensorProduct k (AlgebraicClosure k) V →ₗ[k]
                  TensorProduct k (AlgebraicClosure k) V))),
        ∃ eRange :
            SymmetricPower k (Fin (n + 1)) V ≃ₗ[k] S,
          ((eRange.baseChange k (AlgebraicClosure k)).conj
              ((SymmetricPower.map (n + 1) A).baseChange (AlgebraicClosure k))) =
            ((SymmetricPower.map (n + 1)
                ((((A.baseChange (AlgebraicClosure k)).restrictScalars k) :
                  TensorProduct k (AlgebraicClosure k) V →ₗ[k]
                    TensorProduct k (AlgebraicClosure k) V))).restrict hS).baseChange
              (AlgebraicClosure k) := by
  let S :
      Submodule k
        (SymmetricPower k (Fin (n + 1))
          (TensorProduct k (AlgebraicClosure k) V)) :=
    LinearMap.range
      (SymmetricPower.map (n + 1)
        (((TensorProduct.mk k (AlgebraicClosure k) V) 1) :
          V →ₗ[k] TensorProduct k (AlgebraicClosure k) V))
  let hS :
      S ≤ S.comap
        (SymmetricPower.map (n + 1)
          ((((A.baseChange (AlgebraicClosure k)).restrictScalars k) :
            TensorProduct k (AlgebraicClosure k) V →ₗ[k]
              TensorProduct k (AlgebraicClosure k) V))) :=
    symmetricPower_includeRight_range_le_comap (k := k) (V := V) (A := A) (n + 1)
  let eRange :
      SymmetricPower k (Fin (n + 1)) V ≃ₗ[k] S :=
    symmetricPower_includeRight_range_equiv (k := k) (V := V) (n + 1)
  refine ⟨S, hS, eRange, ?_⟩
  -- This is exactly the scalar-extended range-model conjugacy isolated earlier in the file.
  simpa [S, hS, eRange] using
    symmetricPower_includeRight_range_baseChange_conj
      (k := k) (V := V) (A := A) (n := n + 1)

/-- Helper for Exercise 9-9.1-3: scalar extension identifies the base change of `Sym^n(V)` with
`Sym^n` of the scalar-extended module, and this identification conjugates the induced maps. -/
theorem symmetricPower_baseChange_conj
    (A : V →ₗ[k] V) (n : ℕ) :
    ∃ e :
        TensorProduct k (AlgebraicClosure k) (SymmetricPower k (Fin n) V) ≃ₗ[AlgebraicClosure k]
          SymmetricPower (AlgebraicClosure k) (Fin n)
            (TensorProduct k (AlgebraicClosure k) V),
      e.conj ((SymmetricPower.map n A).baseChange (AlgebraicClosure k)) =
        SymmetricPower.map n (A.baseChange (AlgebraicClosure k)) := by
  cases n with
  | zero =>
      -- The degree-`0` branch is rigid: both symmetric-power endomorphisms are identities on
      -- one-dimensional spaces, so the conjugacy is immediate.
      exact symmetricPower_baseChange_conj_zero (k := k) (V := V) (A := A)
  | succ n =>
      -- The positive-degree branch is now isolated as the final scalar-extension comparison.
      exact symmetricPower_baseChange_conj_pos (A := A) n

/-- Helper for Exercise 9-9.1-3: once a scalar-extension equivalence conjugates the literal base
change of `Sym^n(A)` to the induced endomorphism on `Sym^n` of the scalar-extended module, the
trace coefficient transports across base change by the standard trace lemmas. -/
theorem trace_symmetricPower_map_baseChange_coeff_of_conj
    (A : V →ₗ[k] V) (n : ℕ)
    {e :
      TensorProduct k (AlgebraicClosure k) (SymmetricPower k (Fin n) V) ≃ₗ[AlgebraicClosure k]
        SymmetricPower (AlgebraicClosure k) (Fin n)
          (TensorProduct k (AlgebraicClosure k) V)}
    (he :
      e.conj ((SymmetricPower.map n A).baseChange (AlgebraicClosure k)) =
        SymmetricPower.map n (A.baseChange (AlgebraicClosure k))) :
    algebraMap k (AlgebraicClosure k)
      (LinearMap.trace k (SymmetricPower k (Fin n) V) (SymmetricPower.map n A)) =
      LinearMap.trace (AlgebraicClosure k)
        (SymmetricPower (AlgebraicClosure k) (Fin n) (TensorProduct k (AlgebraicClosure k) V))
        (SymmetricPower.map n (A.baseChange (AlgebraicClosure k))) := by
  -- First pass to the literal base change of `Sym^n(A)`, then transport across the chosen
  -- scalar-extension equivalence.
  calc
    algebraMap k (AlgebraicClosure k)
        (LinearMap.trace k (SymmetricPower k (Fin n) V) (SymmetricPower.map n A)) =
          LinearMap.trace (AlgebraicClosure k)
            (TensorProduct k (AlgebraicClosure k) (SymmetricPower k (Fin n) V))
            ((SymmetricPower.map n A).baseChange (AlgebraicClosure k)) := by
              symm
              simpa using
                (LinearMap.trace_baseChange
                  (f := SymmetricPower.map n A) (A := AlgebraicClosure k))
    _ =
        LinearMap.trace (AlgebraicClosure k)
          (SymmetricPower (AlgebraicClosure k) (Fin n)
            (TensorProduct k (AlgebraicClosure k) V))
          (e.conj ((SymmetricPower.map n A).baseChange (AlgebraicClosure k))) := by
            symm
            simpa using
              (LinearMap.trace_conj'
                ((SymmetricPower.map n A).baseChange (AlgebraicClosure k)) e)
    _ =
        LinearMap.trace (AlgebraicClosure k)
          (SymmetricPower (AlgebraicClosure k) (Fin n)
            (TensorProduct k (AlgebraicClosure k) V))
          (SymmetricPower.map n (A.baseChange (AlgebraicClosure k))) := by
            rw [he]

/-- Helper for Exercise 9-9.1-3: base change to the algebraic closure preserves the symmetric-power
trace coefficients. -/
theorem trace_symmetricPower_map_baseChange_coeff
    (A : V →ₗ[k] V) (n : ℕ) :
    algebraMap k (AlgebraicClosure k)
      (LinearMap.trace k (SymmetricPower k (Fin n) V) (SymmetricPower.map n A)) =
      LinearMap.trace (AlgebraicClosure k)
        (SymmetricPower (AlgebraicClosure k) (Fin n) (TensorProduct k (AlgebraicClosure k) V))
        (SymmetricPower.map n (A.baseChange (AlgebraicClosure k))) := by
  cases n with
  | zero =>
      -- Degree `0` is already rigid: both sides are the trace of the identity on a
      -- one-dimensional space.
      simp [trace_symmetricPower_map_zero]
  | succ n =>
      obtain ⟨e, he⟩ := symmetricPower_baseChange_conj (A := A) (n + 1)
      -- The remaining work is exactly the positive-degree scalar-extension conjugacy.
      exact trace_symmetricPower_map_baseChange_coeff_of_conj (A := A) (n := n + 1) he

/-- Helper for Exercise 9-9.1-3: the fixed-endomorphism symmetric and exterior trace series are
inverse after the sign change `T ↦ -T`. -/
theorem symmetric_exterior_trace_series_mul_rescale_neg_eq_one
    (A : V →ₗ[k] V) :
    PowerSeries.mk
        (fun n ↦
          LinearMap.trace k (SymmetricPower k (Fin n) V) (SymmetricPower.map n A)) *
      PowerSeries.rescale (-1 : k)
        (PowerSeries.mk
          (fun n ↦ LinearMap.trace k (⋀[k]^n V) (exteriorPower.map n A))) = 1 := by
  -- Route correction: instead of leaving the whole theorem opaque, first descend the target to the
  -- algebraic closure. This isolates the two genuine missing bridges: the algebraically closed
  -- induction theorem and the symmetric-power base-change coefficient comparison.
  apply PowerSeries.map_injective
    (f := algebraMap k (AlgebraicClosure k))
    (algebraMap k (AlgebraicClosure k)).injective
  have hsymm :
      PowerSeries.map (algebraMap k (AlgebraicClosure k))
        (PowerSeries.mk
          (fun n ↦
            LinearMap.trace k (SymmetricPower k (Fin n) V) (SymmetricPower.map n A))) =
        PowerSeries.mk
          (fun n ↦
            LinearMap.trace (AlgebraicClosure k)
              (SymmetricPower (AlgebraicClosure k) (Fin n)
                (TensorProduct k (AlgebraicClosure k) V))
              (SymmetricPower.map n (A.baseChange (AlgebraicClosure k)))) := by
    -- Compare the symmetric coefficients after scalar extension term by term.
    ext n
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
    simpa using trace_symmetricPower_map_baseChange_coeff (A := A) n
  have hext :
      PowerSeries.map (algebraMap k (AlgebraicClosure k))
        (PowerSeries.rescale (-1 : k)
          (PowerSeries.mk
            (fun n ↦ LinearMap.trace k (⋀[k]^n V) (exteriorPower.map n A)))) =
        PowerSeries.rescale (-1 : AlgebraicClosure k)
          (PowerSeries.mk
            (fun n ↦
              LinearMap.trace (AlgebraicClosure k)
                (⋀[AlgebraicClosure k]^n (TensorProduct k (AlgebraicClosure k) V))
                (exteriorPower.map n (A.baseChange (AlgebraicClosure k)))) ) := by
    -- The exterior coefficients already identify with the reversed characteristic polynomial, so
    -- the existing base-change lemma for those coefficients gives the needed transport.
    ext n
    rw [PowerSeries.coeff_map, PowerSeries.coeff_rescale, PowerSeries.coeff_mk,
      PowerSeries.coeff_rescale, PowerSeries.coeff_mk]
    calc
      algebraMap k (AlgebraicClosure k)
          (((-1 : k) ^ n) *
            LinearMap.trace k (⋀[k]^n V) (exteriorPower.map n A))
          = algebraMap k (AlgebraicClosure k)
              (((-1 : k) ^ n) *
                (((-A).charpoly.reverse : Polynomial k).coeff n)) := by
                  rw [trace_exteriorPower_map_eq_coeff_neg_charpoly_reverse]
      _ = algebraMap k (AlgebraicClosure k) (((-1 : k) ^ n)) *
            (((-(A.baseChange (AlgebraicClosure k))).charpoly.reverse :
              Polynomial (AlgebraicClosure k)).coeff n) := by
            rw [map_mul, coeff_neg_charpoly_reverse_baseChange]
      _ = ((-1 : AlgebraicClosure k) ^ n) *
            (((-(A.baseChange (AlgebraicClosure k))).charpoly.reverse :
              Polynomial (AlgebraicClosure k)).coeff n) := by
            simp
      _ = ((-1 : AlgebraicClosure k) ^ n) *
            LinearMap.trace (AlgebraicClosure k)
              (⋀[AlgebraicClosure k]^n (TensorProduct k (AlgebraicClosure k) V))
              (exteriorPower.map n (A.baseChange (AlgebraicClosure k))) := by
            rw [trace_exteriorPower_map_eq_coeff_neg_charpoly_reverse]
  -- After transport to the algebraic closure, apply the algebraically closed theorem to the
  -- base-changed endomorphism.
  calc
    PowerSeries.map (algebraMap k (AlgebraicClosure k))
        (PowerSeries.mk
          (fun n ↦
            LinearMap.trace k (SymmetricPower k (Fin n) V) (SymmetricPower.map n A)) *
          PowerSeries.rescale (-1 : k)
            (PowerSeries.mk
              (fun n ↦ LinearMap.trace k (⋀[k]^n V) (exteriorPower.map n A))))
        =
          PowerSeries.map (algebraMap k (AlgebraicClosure k))
            (PowerSeries.mk
              (fun n ↦
                LinearMap.trace k (SymmetricPower k (Fin n) V) (SymmetricPower.map n A))) *
          PowerSeries.map (algebraMap k (AlgebraicClosure k))
            (PowerSeries.rescale (-1 : k)
              (PowerSeries.mk
                (fun n ↦ LinearMap.trace k (⋀[k]^n V) (exteriorPower.map n A)))) := by
            rw [RingHom.map_mul]
    _ =
        PowerSeries.mk
          (fun n ↦
            LinearMap.trace (AlgebraicClosure k)
              (SymmetricPower (AlgebraicClosure k) (Fin n)
                (TensorProduct k (AlgebraicClosure k) V))
              (SymmetricPower.map n (A.baseChange (AlgebraicClosure k)))) *
        PowerSeries.rescale (-1 : AlgebraicClosure k)
          (PowerSeries.mk
            (fun n ↦
              LinearMap.trace (AlgebraicClosure k)
                (⋀[AlgebraicClosure k]^n (TensorProduct k (AlgebraicClosure k) V))
                (exteriorPower.map n (A.baseChange (AlgebraicClosure k)))) ) := by
          rw [hsymm, hext]
    _ = 1 := by
          simpa using
            symmetric_exterior_trace_series_mul_rescale_neg_eq_one_isAlgClosed
              (k := AlgebraicClosure k)
              (V := TensorProduct k (AlgebraicClosure k) V)
              (A := A.baseChange (AlgebraicClosure k))
    _ = PowerSeries.map (algebraMap k (AlgebraicClosure k)) (1 : PowerSeries k) := by
          simp

/-- Exercise 9-9.1-3: evaluating the symmetric-power character series at `s` gives the inverse
of the basis-free polynomial `((ρ s).charpoly.reverse : k[T]) = det(1 - ρ(s) T)`. -/
theorem symmetricPowerCharacterSeries_eval_eq_det_inv_aux
    (ρ : Representation k G V) (s : G) :
    PowerSeries.map (Pi.evalRingHom _ s) σ_T(ρ) =
      (((ρ s).charpoly.reverse : Polynomial k) : PowerSeries k)⁻¹ := by
  let symmTrace : PowerSeries k :=
    PowerSeries.mk fun n ↦
      LinearMap.trace k (SymmetricPower k (Fin n) V) (SymmetricPower.map n (ρ s))
  let extTrace : PowerSeries k :=
    PowerSeries.mk fun n ↦
      LinearMap.trace k (⋀[k]^n V) (exteriorPower.map n (ρ s))
  have hsymm :
      PowerSeries.map (Pi.evalRingHom _ s) σ_T(ρ) = symmTrace := by
    -- Evaluating the coefficient-wise character series produces the symmetric-power trace series.
    ext n
    simpa [symmTrace] using coeff_map_symmetricPowerCharacterSeries_eval (ρ := ρ) (s := s) n
  have hext :
      PowerSeries.map (Pi.evalRingHom _ s) λ_T(ρ) = extTrace := by
    -- The same coefficient comparison identifies the evaluated exterior series with its trace model.
    ext n
    simpa [extTrace] using coeff_map_exteriorPowerCharacterSeries_eval (ρ := ρ) (s := s) n
  have hext_det :
      extTrace = ((((-ρ s).charpoly.reverse : Polynomial k) : PowerSeries k)) := by
    -- Route correction: the determinant owner for the exterior side is now the primary scalar
    -- bridge, so we rewrite the exterior trace coefficients directly into `(-ρ s).charpoly.reverse`.
    ext n
    simpa [extTrace] using trace_exteriorPower_map_eq_coeff_neg_charpoly_reverse (A := ρ s) n
  have hrescale :
      PowerSeries.rescale (-1 : k) (PowerSeries.map (Pi.evalRingHom _ s) λ_T(ρ)) =
        (((ρ s).charpoly.reverse : Polynomial k) : PowerSeries k) := by
    -- The determinant polynomial for `-ρ s` becomes the characteristic power series of `ρ s`
    -- after the sign change `T ↦ -T`.
    calc
      PowerSeries.rescale (-1 : k) (PowerSeries.map (Pi.evalRingHom _ s) λ_T(ρ))
          = PowerSeries.rescale (-1 : k) extTrace := by rw [hext]
      _ = PowerSeries.rescale (-1 : k)
            ((((-ρ s).charpoly.reverse : Polynomial k) : PowerSeries k)) := by rw [hext_det]
      _ = (((ρ s).charpoly.reverse : Polynomial k) : PowerSeries k) := by
            simpa using rescale_neg_charpoly_reverse (A := ρ s)
  have hmul :
      PowerSeries.map (Pi.evalRingHom _ s) σ_T(ρ) *
        (((ρ s).charpoly.reverse : Polynomial k) : PowerSeries k) = 1 := by
    -- The evaluated symmetric series and the rescaled exterior determinant have the same
    -- fixed-endomorphism product identity.
    calc
      PowerSeries.map (Pi.evalRingHom _ s) σ_T(ρ) *
          (((ρ s).charpoly.reverse : Polynomial k) : PowerSeries k)
          = PowerSeries.map (Pi.evalRingHom _ s) σ_T(ρ) *
              PowerSeries.rescale (-1 : k)
                (PowerSeries.map (Pi.evalRingHom _ s) λ_T(ρ)) := by
                  rw [hrescale]
      _ = symmTrace * PowerSeries.rescale (-1 : k) extTrace := by rw [hsymm, hext]
      _ = 1 := by
            simpa [symmTrace, extTrace] using
              symmetric_exterior_trace_series_mul_rescale_neg_eq_one (A := ρ s)
  have hq :
      PowerSeries.constantCoeff
          ((((ρ s).charpoly.reverse : Polynomial k) : PowerSeries k)) ≠ 0 := by
    -- The reversed characteristic polynomial has constant term `1`, so inverse uniqueness applies.
    rw [constantCoeff_charpoly_reverse_powerSeries (A := ρ s)]
    simp
  exact (PowerSeries.eq_inv_iff_mul_eq_one hq).2 hmul

/-- Evaluating the exterior-power character series at `s` gives the determinant
`det(1 + ρ(s) T)`, encoded basis-freely as `(-ρ s).charpoly.reverse`. -/
theorem exteriorPowerCharacterSeries_eval_eq_det_aux
    (ρ : Representation k G V) (s : G) :
    PowerSeries.map (Pi.evalRingHom _ s) λ_T(ρ) =
      (((-ρ s).charpoly.reverse : Polynomial k) : PowerSeries k) := by
  -- Compare coefficients after evaluation; the exterior trace series is exactly the coefficient
  -- expansion of the determinant polynomial `det (1 + ρ(s) T)`.
  ext n
  rw [PowerSeries.coeff_map]
  simpa [coeff_map_exteriorPowerCharacterSeries_eval] using
    trace_exteriorPower_map_eq_coeff_neg_charpoly_reverse (A := ρ s) n
end

end Representation
