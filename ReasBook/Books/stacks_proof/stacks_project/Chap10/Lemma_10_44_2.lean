import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_42_1
import stacks_proof.stacks_project.Chap10.Lemma_10_43_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra

universe u v

section

variable (k : Type u) [Field k] (p : ℕ) [ExpChar k p]

/-- The subfield of `AlgebraicClosure k` consisting of elements whose `p`-th power lies in the
image of `k`; this is a concrete model for `k^{1/p}`. -/
private noncomputable def onePthRootSubfield : Subfield (AlgebraicClosure k) :=
  let _ : ExpChar (AlgebraicClosure k) p :=
    expChar_of_injective_algebraMap (algebraMap k (AlgebraicClosure k)).injective p
  Subfield.comap (frobenius (AlgebraicClosure k) p) ((algebraMap k (AlgebraicClosure k)).fieldRange)

-- Proof sketch: an element of `k` maps into the Frobenius preimage of the base field because
-- `(algebraMap k (AlgebraicClosure k) x) ^ p = algebraMap k (AlgebraicClosure k) (x ^ p)`.
/-- The image of `k` is contained in the chosen model of `k^{1/p}` inside `AlgebraicClosure k`. -/
private theorem onePthRootSubfield_algebraMap_mem (x : k) :
    algebraMap k (AlgebraicClosure k) x ∈ onePthRootSubfield k p := by
  -- The witness is `x ^ p`, whose image has `p`-th root `algebraMap x`.
  refine Subfield.mem_comap.2 ?_
  rw [RingHom.mem_fieldRange]
  refine ⟨x ^ p, ?_⟩
  simp [frobenius_def]

/-- The intermediate field of `AlgebraicClosure k` modeling the extension `k^{1/p} / k`. -/
noncomputable def onePthRootExtension : IntermediateField k (AlgebraicClosure k) :=
  (onePthRootSubfield k p).toIntermediateField (onePthRootSubfield_algebraMap_mem k p)

-- Proof sketch: unfold `onePthRootExtension` and `onePthRootSubfield`; membership in the Frobenius
-- comap is exactly the condition that the `p`-th power lies in the image of `k`.
/-- An element of `AlgebraicClosure k` belongs to the chosen `k^{1/p}` exactly when its `p`-th
power comes from `k`. -/
theorem mem_onePthRootExtension_iff {x : AlgebraicClosure k} :
    x ∈ onePthRootExtension k p ↔
      x ^ p ∈ (algebraMap k (AlgebraicClosure k)).fieldRange := by
  -- Membership in the intermediate field is definitional membership in the Frobenius preimage.
  change x ∈ (onePthRootSubfield k p : Set (AlgebraicClosure k)) ↔
    x ^ p ∈ (algebraMap k (AlgebraicClosure k)).fieldRange
  dsimp [onePthRootSubfield]
  rw [Set.mem_preimage, RingHom.mem_fieldRange]
  simp [frobenius_def]

end

section

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
variable {p : ℕ} [Fact p.Prime] [CharP k p]

/-- Helper for Lemma 10.44.2: every coefficient from `k` admits a chosen `p`-th root in the
concrete model `onePthRootExtension k p` of `k^{1/p}`. -/
private lemma exists_pth_root_in_onePthRootExtension (c : k) :
    ∃ μ : onePthRootExtension k p,
      ((μ : AlgebraicClosure k) ^ p = algebraMap k (AlgebraicClosure k) c) := by
  letI : ExpChar (AlgebraicClosure k) p :=
    expChar_of_injective_algebraMap (algebraMap k (AlgebraicClosure k)).injective p
  have hsurj : Function.Surjective (frobenius (AlgebraicClosure k) p) :=
    surjective_frobenius (AlgebraicClosure k) p
  rcases hsurj (algebraMap k (AlgebraicClosure k) c) with ⟨x, hx⟩
  refine ⟨⟨x, ?_⟩, ?_⟩
  · -- The Frobenius preimage condition is exactly the defining membership criterion.
    rw [mem_onePthRootExtension_iff]
    rw [frobenius_def] at hx
    rw [hx, RingHom.mem_fieldRange]
    exact ⟨c, rfl⟩
  · -- The chosen element maps back to the prescribed coefficient after raising to the `p`-th power.
    simpa [frobenius_def] using hx

/-- Helper for Lemma 10.44.2: the chosen `p`-th root can be expressed as an equality inside
`onePthRootExtension k p` itself. -/
private lemma exists_pth_root_eq_algebraMap_in_onePthRootExtension (c : k) :
    ∃ μ : onePthRootExtension k p, μ ^ p = algebraMap k (onePthRootExtension k p) c := by
  rcases exists_pth_root_in_onePthRootExtension (k := k) (p := p) c with ⟨μ, hμ⟩
  -- Coercion to `AlgebraicClosure k` is injective on the intermediate field.
  refine ⟨μ, ?_⟩
  ext
  simpa using hμ

omit [Fact p.Prime] [CharP k p] in
/-- Helper for Lemma 10.44.2: the Frobenius linear-independence condition on `K` restricts to
every intermediate field of `K / k`. -/
private lemma linearIndepOn_pow_on_intermediateField
    (hpow : ∀ s : Finset K,
      LinearIndepOn k _root_.id (s : Set K) → LinearIndepOn k (fun x ↦ x ^ p) (s : Set K))
    (L : IntermediateField k K) :
    ∀ s : Finset L,
      LinearIndepOn k _root_.id (s : Set L) → LinearIndepOn k (fun x ↦ x ^ p) (s : Set L) := by
  classical
  intro s hs
  have hValInj :
      Set.InjOn (L.val.toLinearMap : L →ₗ[k] K)
        (Submodule.span k ((_root_.id : L → L) '' (s : Set L))) := by
    intro x hx y hy hxy
    exact Subtype.ext hxy
  have hsVal : LinearIndepOn k (fun x : L ↦ (x : K)) (s : Set L) := by
    -- First view the `L`-linear independent family as a family in `K`.
    simpa using hs.map_injOn (L.val.toLinearMap : L →ₗ[k] K) hValInj
  have hsK :
      LinearIndepOn k _root_.id ((s.image ((↑) : L → K) : Finset K) : Set K) := by
    -- Then move from the subtype-indexed family to the corresponding image set in `K`.
    simpa using hsVal.id_image
  have hpowK :
      LinearIndepOn k (fun x : K ↦ x ^ p) ((s.image ((↑) : L → K) : Finset K) : Set K) :=
    hpow (s.image ((↑) : L → K)) hsK
  have hpowK' : LinearIndepOn k (fun x : K ↦ x ^ p) (((↑) : L → K) '' (s : Set L)) := by
    simpa using hpowK
  have hpowComp : LinearIndepOn k (fun x : L ↦ ((x : K) ^ p)) (s : Set L) := by
    -- Pull the independence statement back along the embedding `L ↪ K`.
    simpa using
      (LinearIndepOn.comp_of_image (v := fun x : K ↦ x ^ p) (f := ((↑) : L → K)) hpowK'
        (by
          intro x hx y hy hxy
          exact Subtype.ext hxy))
  have hPowInj :
      Set.InjOn (L.val.toLinearMap : L →ₗ[k] K)
        (Submodule.span k ((fun x : L ↦ x ^ p) '' (s : Set L))) := by
    intro x hx y hy hxy
    exact Subtype.ext hxy
  -- Finally transport the conclusion back from the carrier `K` to the field `L`.
  exact
    (LinearMap.linearIndepOn_iff_of_injOn (f := (L.val.toLinearMap : L →ₗ[k] K))
      (v := fun x : L ↦ x ^ p) (s := (s : Set L)) hPowInj).mp <| by
      simpa using hpowComp

/-- Helper for Lemma 10.44.2: Frobenius preserving linear independence on every finite subset
forces `K / k` to be separable in the sense of Definition `10.42.1`. -/
private lemma isSeparableOver_of_linearIndepOn_pow
    (hpow : ∀ s : Finset K,
      LinearIndepOn k _root_.id (s : Set K) → LinearIndepOn k (fun x ↦ x ^ p) (s : Set K)) :
    IsSeparableOver k K := by
  classical
  refine ⟨fun L hL ↦ ?_⟩
  letI : Algebra.EssFiniteType k L := (IntermediateField.essFiniteType_iff).2 hL
  obtain ⟨s, hs, hsep⟩ :=
    exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_essFiniteType
      (k := k) (K := L) (p := p) (hp := Fact.out)
      (linearIndepOn_pow_on_intermediateField (k := k) (K := K) (p := p) hpow L)
  -- The mathlib theorem already gives the required separably generated finite-stage witness.
  exact ⟨(s : Set L), hs, by simpa using hsep⟩

/-- Helper for Lemma 10.44.2: a base-field coefficient on the left tensor factor can be read as
the corresponding scalar multiple of `1 ⊗ x`. -/
private lemma algebraMap_tmul_eq_smul_one_tmul
    (c : k) (x : K) :
    (((algebraMap k (onePthRootExtension k p) c) ⊗ₜ[k] x :
      onePthRootExtension k p ⊗[k] K)) =
      c • (((1 : onePthRootExtension k p) ⊗ₜ[k] x :
        onePthRootExtension k p ⊗[k] K)) := by
  -- Rewrite the left factor `algebraMap c` as `c • 1` and move that scalar outside the tensor.
  rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul']

/-- Helper for Lemma 10.44.2: a relation among the `p`-th powers produces a nilpotent tensor in
`k^{1/p} ⊗[k] K`, exactly as in the source proof. -/
private lemma sum_one_tmul_pth_root_pow_eq_zero_of_pow_relation
    (s : Finset K)
    (c : ↥(s : Set K) → k)
    (μ : ↥(s : Set K) → onePthRootExtension k p)
    (hμ : ∀ i : ↥(s : Set K), μ i ^ p = algebraMap k (onePthRootExtension k p) (c i))
    (hc : ∑ i : ↥(s : Set K), c i • ((i : K) ^ p) = 0) :
    (∑ i : ↥(s : Set K),
        ((μ i) ⊗ₜ[k] (i : K) : onePthRootExtension k p ⊗[k] K)) ^ p = 0 := by
  letI : FaithfulSMul k (onePthRootExtension k p ⊗[k] K) := by infer_instance
  letI : CharP (onePthRootExtension k p ⊗[k] K) p := charP_of_injective_algebraMap' k p
  letI : ExpChar (onePthRootExtension k p ⊗[k] K) p :=
    ExpChar.of_injective_algebraMap' k p
  -- Expand Frobenius across the finite sum and normalize each pure tensor summand.
  have hsum_pow :
      (∑ i : ↥(s : Set K),
          ((μ i) ⊗ₜ[k] (i : K) : onePthRootExtension k p ⊗[k] K)) ^ p =
        ∑ i : ↥(s : Set K),
          ((((μ i) ⊗ₜ[k] (i : K) : onePthRootExtension k p ⊗[k] K) ^ p)) := by
    simpa using
      (sum_pow_char
        (p := p)
        (s := Finset.univ)
        (f := fun i : ↥(s : Set K) ↦
          ((μ i) ⊗ₜ[k] (i : K) : onePthRootExtension k p ⊗[k] K)))
  rw [hsum_pow]
  simp_rw [Algebra.TensorProduct.tmul_pow, hμ]
  calc
    ∑ i : ↥(s : Set K),
        ((algebraMap k (onePthRootExtension k p) (c i)) ⊗ₜ[k] ((i : K) ^ p) :
          onePthRootExtension k p ⊗[k] K)
      =
        ∑ i : ↥(s : Set K),
          c i •
            (((1 : onePthRootExtension k p) ⊗ₜ[k] ((i : K) ^ p) :
              onePthRootExtension k p ⊗[k] K)) := by
      -- Move each coefficient from the left tensor factor to the scalar action.
      apply Finset.sum_congr rfl
      intro i hi
      simpa using
        algebraMap_tmul_eq_smul_one_tmul
          (k := k) (K := K) (p := p) (c i) ((i : K) ^ p)
    _ =
        ∑ i : ↥(s : Set K),
          (((1 : onePthRootExtension k p) ⊗ₜ[k] (c i • ((i : K) ^ p)) :
            onePthRootExtension k p ⊗[k] K)) := by
      -- Rewrite the ambient scalar action by moving `cᵢ` across the tensor.
      apply Finset.sum_congr rfl
      intro i hi
      calc
        c i •
            (((1 : onePthRootExtension k p) ⊗ₜ[k] ((i : K) ^ p) :
              onePthRootExtension k p ⊗[k] K))
          =
            (((c i • (1 : onePthRootExtension k p)) ⊗ₜ[k] ((i : K) ^ p) :
              onePthRootExtension k p ⊗[k] K)) := by
            rw [TensorProduct.smul_tmul']
        _ =
            (((1 : onePthRootExtension k p) ⊗ₜ[k] (c i • ((i : K) ^ p)) :
              onePthRootExtension k p ⊗[k] K)) := by
            simpa using
              (TensorProduct.smul_tmul
                (R := k)
                (r := c i)
                (m := (1 : onePthRootExtension k p))
                (n := ((i : K) ^ p)))
    _ =
        (((1 : onePthRootExtension k p) ⊗ₜ[k]
          (∑ i : ↥(s : Set K), c i • ((i : K) ^ p)) :
            onePthRootExtension k p ⊗[k] K)) := by
      -- Fold the tensor sum back to the original linear relation on `K`.
      simpa using
        (TensorProduct.tmul_sum
          (R := k)
          (m := (1 : onePthRootExtension k p))
          (s := Finset.univ)
          (n := fun i : ↥(s : Set K) ↦ c i • ((i : K) ^ p))).symm
    _ = 0 := by
      rw [hc, TensorProduct.tmul_zero]

/-- Helper for Lemma 10.44.2: if a finite `k`-linearly independent family in `K` gives a zero
tensor combination in `k^{1/p} ⊗[k] K`, then every coefficient in `k^{1/p}` vanishes. -/
private lemma coefficients_zero_of_sum_one_tmul_eq_zero
    (s : Finset K)
    (hs : LinearIndepOn k _root_.id (s : Set K))
    (μ : ↥(s : Set K) → onePthRootExtension k p)
    (hzero : ∑ i : ↥(s : Set K),
        ((μ i) ⊗ₜ[k] (i : K) : onePthRootExtension k p ⊗[k] K) = 0) :
    ∀ i : ↥(s : Set K), μ i = 0 := by
  classical
  let b : Module.Basis (hs.extend (Set.subset_univ (s : Set K))) k K := Module.Basis.extend hs
  intro i
  let bi : hs.extend (Set.subset_univ (s : Set K)) :=
    ⟨(i : K), hs.subset_extend (Set.subset_univ (s : Set K)) i.2⟩
  let e :
      (onePthRootExtension k p ⊗[k] K) →ₗ[k]
        (hs.extend (Set.subset_univ (s : Set K)) →₀ onePthRootExtension k p) :=
    (TensorProduct.equivFinsuppOfBasisRight b).toLinearMap
  have hcoord_zero :
      e (∑ j : ↥(s : Set K),
          (((μ j) ⊗ₜ[k] (j : K) : onePthRootExtension k p ⊗[k] K))) = 0 := by
    -- First map the zero tensor relation through the coordinate linear equivalence.
    simpa [hzero] using
      congrArg (fun x : onePthRootExtension k p ⊗[k] K ↦ e x) hzero
  have hcoord :
      ∑ j : ↥(s : Set K),
        e
          (((μ j) ⊗ₜ[k] (j : K) : onePthRootExtension k p ⊗[k] K)) = 0 := by
    -- Apply the basis-coordinate equivalence to the tensor relation before reading one coordinate.
    simpa [e, map_sum] using hcoord_zero
  have hcoeff :
      ∑ j : ↥(s : Set K), b.repr (j : K) bi • μ j = 0 := by
    -- Evaluating at the basis vector containing `i` isolates the coefficient of `i`.
    simpa [e, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply] using
      congrArg
        (fun f : hs.extend (Set.subset_univ (s : Set K)) →₀ onePthRootExtension k p ↦ f bi)
        hcoord
  have hrepr :
      ∀ j : ↥(s : Set K), b.repr (j : K) bi = if j = i then 1 else 0 := by
    intro j
    let bj : hs.extend (Set.subset_univ (s : Set K)) :=
      ⟨(j : K), hs.subset_extend (Set.subset_univ (s : Set K)) j.2⟩
    have hbj : b bj = (j : K) := by
      simpa [b, bj] using (Module.Basis.extend_apply_self hs bj)
    have hbi : b bi = (i : K) := by
      simpa [b, bi] using (Module.Basis.extend_apply_self hs bi)
    by_cases hji : j = i
    · have hbji : bj = bi := by
        apply Subtype.ext
        exact congrArg (fun x : ↥(s : Set K) ↦ (x : K)) hji
      calc
        b.repr (j : K) bi = b.repr (b bj) bi := by rw [hbj]
        _ = if bj = bi then 1 else 0 := by
          simpa using (b.repr_self_apply (i := bj) bi)
        _ = 1 := by simp [hbji]
        _ = if j = i then 1 else 0 := by simp [hji]
    · have hbji : bj ≠ bi := by
        intro hEq
        apply hji
        apply Subtype.ext
        exact congrArg (fun x : hs.extend (Set.subset_univ (s : Set K)) ↦ (x : K)) hEq
      calc
        b.repr (j : K) bi = b.repr (b bj) bi := by rw [hbj]
        _ = if bj = bi then 1 else 0 := by
          simpa using (b.repr_self_apply (i := bj) bi)
        _ = 0 := by simp [hbji]
        _ = if j = i then 1 else 0 := by simp [hji]
  -- The basis coordinate supported at `i` is exactly `μ i`, so it must be zero.
  have hsingle :
      (∑ j : ↥(s : Set K), b.repr (j : K) bi • μ j) = μ i := by
    rw [Fintype.sum_eq_single i]
    · simp [hrepr]
    · intro j hij
      simp [hrepr, hij]
  rw [hsingle] at hcoeff
  exact hcoeff

private lemma linearIndepOn_pow_of_isReduced_tensorProduct_onePthRootExtension
    [IsReduced (K ⊗[k] onePthRootExtension k p)] :
    ∀ s : Finset K,
      LinearIndepOn k _root_.id (s : Set K) → LinearIndepOn k (fun x ↦ x ^ p) (s : Set K) := by
  classical
  intro s hs
  letI : IsReduced (onePthRootExtension k p ⊗[k] K) :=
    isReduced_of_injective
      (Algebra.TensorProduct.comm k (onePthRootExtension k p) K)
      (Algebra.TensorProduct.comm k (onePthRootExtension k p) K).injective
  -- Route correction: keep the source tensor `∑ μᵢ ⊗ aᵢ` in `k^{1/p} ⊗[k] K`, use reducedness to
  -- kill it from `x ^ p = 0`, and then read off each coefficient in a basis extending `s`.
  change LinearIndependent k (fun i : ↥(s : Set K) ↦ ((i : K) ^ p))
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  choose μ hμ using
    (fun j : ↥(s : Set K) ↦
      exists_pth_root_eq_algebraMap_in_onePthRootExtension (k := k) (p := p) (c j))
  let x : onePthRootExtension k p ⊗[k] K :=
    ∑ j : ↥(s : Set K), ((μ j) ⊗ₜ[k] (j : K) : onePthRootExtension k p ⊗[k] K)
  have hxpow : x ^ p = 0 := by
    -- The Frobenius computation turns the relation on `aᵢ ^ p` into a nilpotent tensor.
    simpa [x] using
      sum_one_tmul_pth_root_pow_eq_zero_of_pow_relation
        (k := k) (K := K) (p := p) s c μ hμ hc
  have hx : x = 0 := eq_zero_of_pow_eq_zero hxpow
  have hμzero :
      ∀ j : ↥(s : Set K), μ j = 0 := by
    -- Coordinates in a basis extending `s` recover the original tensor coefficients.
    simpa [x] using
      coefficients_zero_of_sum_one_tmul_eq_zero
        (k := k) (K := K) (p := p) s hs μ hx
  have hci : algebraMap k (onePthRootExtension k p) (c i) = 0 := by
    -- Raising the zero root to the `p`-th power sends the original coefficient to zero.
    have hμi := hμ i
    rw [hμzero i, zero_pow (Nat.Prime.ne_zero (Fact.out : p.Prime))] at hμi
    exact hμi.symm
  have hci_zero : c i = 0 :=
    (algebraMap k (onePthRootExtension k p)).injective (by simpa using hci)
  exact hci_zero

-- Proof sketch: `(1) → (4)` is the separable-implies-geometrically-reduced direction from the
-- previous section; `(4) → (3)` is obtained by base change to the chosen model of `k^{1/p}`;
-- `(3) → (2)` uses the Frobenius-induced multiplication map on `K ⊗[k] k^{1/p}` and reducedness
-- to deduce injectivity; `(2) → (1)` reduces to the finitely generated case and applies the
-- separating-transcendence-basis criterion from Lemma `10.44.1`.
/-- Lemma 10.44.2: for a field extension `K / k` of characteristic `p > 0`, the following are
equivalent: `K` is separable over `k` in the sense of Definition `10.42.1`, Frobenius preserves
`k`-linear independence on finite subsets of `K`, the base change `K ⊗[k] k^{1/p}` is reduced,
and `K` is geometrically reduced over `k`. -/
@[stacks 030W]
theorem isSeparableOver_tfae_linearIndepOn_pow_reduced_onePthRoot_geometricallyReduced :
    List.TFAE [
      IsSeparableOver k K,
      ∀ s : Finset K,
        LinearIndepOn k _root_.id (s : Set K) → LinearIndepOn k (fun x ↦ x ^ p) (s : Set K),
      IsReduced (K ⊗[k] onePthRootExtension k p),
      IsGeometricallyReduced k K
    ] := by
  tfae_have 1 → 4 := by
    intro hsep
    -- The separable-to-geometrically-reduced direction is exactly Lemma `10.43.6`.
    letI : IsSeparableOver k K := hsep
    exact isGeometricallyReduced_of_isSeparableOver
  tfae_have 4 → 3 := by
    intro hgeom
    -- Then specialize geometric reducedness to the chosen model of `k^{1/p}`.
    letI : IsGeometricallyReduced k K := hgeom
    exact
      isReduced_tensorProduct_of_geometricallyReduced_field
        (k := k) (K := K) (S := onePthRootExtension k p)
  tfae_have 3 → 2 := by
    intro hred
    -- Reduce the hard implication to the isolated tensor-product helper.
    letI : IsReduced (K ⊗[k] onePthRootExtension k p) := hred
    exact
      linearIndepOn_pow_of_isReduced_tensorProduct_onePthRootExtension
        (k := k) (K := K) (p := p)
  tfae_have 2 → 1 := by
    intro hpow
    -- The finitely generated criterion upgrades the Frobenius condition to Stacks-separability.
    exact isSeparableOver_of_linearIndepOn_pow (k := k) (K := K) (p := p) hpow
  tfae_finish

/-- Lemma 10.44.2, clauses `(1) ↔ (2)`: Frobenius preserves `k`-linear independence on every
finite subset of `K` iff `K / k` is separable in the sense of Definition `10.42.1 (2)`. -/
@[stacks 030W]
theorem isSeparableOver_iff_linearIndepOn_pow :
    IsSeparableOver k K ↔
      ∀ s : Finset K,
        LinearIndepOn k _root_.id (s : Set K) → LinearIndepOn k (fun x ↦ x ^ p) (s : Set K) := by
  let l : List Prop := [
    IsSeparableOver k K,
    ∀ s : Finset K,
      LinearIndepOn k _root_.id (s : Set K) → LinearIndepOn k (fun x ↦ x ^ p) (s : Set K),
    IsReduced (K ⊗[k] onePthRootExtension k p),
    IsGeometricallyReduced k K
  ]
  have htfae : List.TFAE l := by
    simpa [l] using isSeparableOver_tfae_linearIndepOn_pow_reduced_onePthRoot_geometricallyReduced
  simpa [l] using (htfae.out 0 1 (by simp [l]) (by simp [l]))

/-- Lemma 10.44.2, clauses `(1) ↔ (3)`: reducedness after base change to the chosen model
`onePthRootExtension k p` of `k^{1/p}` is equivalent to separability of `K / k`. -/
@[stacks 030W]
theorem isSeparableOver_iff_isReduced_tensorProduct_onePthRootExtension :
    IsSeparableOver k K ↔ IsReduced (K ⊗[k] onePthRootExtension k p) := by
  let l : List Prop := [
    IsSeparableOver k K,
    ∀ s : Finset K,
      LinearIndepOn k _root_.id (s : Set K) → LinearIndepOn k (fun x ↦ x ^ p) (s : Set K),
    IsReduced (K ⊗[k] onePthRootExtension k p),
    IsGeometricallyReduced k K
  ]
  have htfae : List.TFAE l := by
    simpa [l] using isSeparableOver_tfae_linearIndepOn_pow_reduced_onePthRoot_geometricallyReduced
  simpa [l] using (htfae.out 0 2 (by simp [l]) (by simp [l]))

/-- Lemma 10.44.2, clauses `(1) ↔ (4)`: for field extensions in characteristic `p`, geometric
reducedness is equivalent to separability in the sense of Definition `10.42.1 (2)`. -/
@[stacks 030W]
theorem isSeparableOver_iff_isGeometricallyReduced_of_charP
    (p : ℕ) [Fact p.Prime] [CharP k p] :
    IsSeparableOver k K ↔ IsGeometricallyReduced k K := by
  let l : List Prop := [
    IsSeparableOver k K,
    ∀ s : Finset K,
      LinearIndepOn k _root_.id (s : Set K) → LinearIndepOn k (fun x ↦ x ^ p) (s : Set K),
    IsReduced (K ⊗[k] onePthRootExtension k p),
    IsGeometricallyReduced k K
  ]
  have htfae : List.TFAE l := by
    simpa [l] using isSeparableOver_tfae_linearIndepOn_pow_reduced_onePthRoot_geometricallyReduced
  simpa [l] using (htfae.out 0 3 (by simp [l]) (by simp [l]))

end

section

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

-- Proof sketch: in positive characteristic, specialize
-- `isSeparableOver_iff_isGeometricallyReduced_of_charP` to `p := ringChar k`; in characteristic
-- zero, separability and geometric reducedness both follow from the characteristic-zero case of
-- the chapter.
/-- Lemma 10.44.2, clauses `(1) ↔ (4)`: for any field extension `K / k`, geometric reducedness is
equivalent to separability in the sense of Definition `10.42.1 (2)`. -/
@[stacks 030W]
theorem isSeparableOver_iff_isGeometricallyReduced :
    IsSeparableOver k K ↔ IsGeometricallyReduced k K := by
  have hzero : ringChar k = 0 ↔ CharZero k := CharP.ringChar_zero_iff_CharZero k
  constructor
  · intro hsep
    letI : IsSeparableOver k K := hsep
    exact isGeometricallyReduced_of_isSeparableOver
  · intro hgeom
    by_cases h0 : ringChar k = 0
    · letI : CharZero k := hzero.1 h0
      exact ⟨fun L hL ↦ by
        letI : Algebra.EssFiniteType k L := (IntermediateField.essFiniteType_iff).2 hL
        infer_instance⟩
    · letI : CharP k (ringChar k) := inferInstance
      have hprime : (ringChar k).Prime := CharP.char_prime_of_ne_zero k h0
      letI : Fact (ringChar k).Prime := ⟨hprime⟩
      let hchar : IsSeparableOver k K ↔ IsGeometricallyReduced k K :=
        isSeparableOver_iff_isGeometricallyReduced_of_charP (ringChar k)
      exact hchar.2 hgeom

end
