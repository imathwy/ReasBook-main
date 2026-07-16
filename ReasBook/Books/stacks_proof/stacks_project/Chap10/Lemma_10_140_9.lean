import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_42_1
import stacks_proof.stacks_project.Chap10.Lemma_10_42_4
import stacks_proof.stacks_project.Chap10.Lemma_10_158_2
import stacks_proof.stacks_project.Chap10.Lemma_10_158_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

namespace Algebra

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [IsDomain R] [IsDomain S] [Algebra R S]

/-- Helper for Chap10 Lemma 10 140 9: vanishing of `H₁(L_{K/k})` forces the Jacobi-Zariski
base-change map on Kähler differentials to be injective. -/
lemma kaehlerDifferentialMapBaseChange_injective_of_subsingletonH1
    {k : Type u} {K : Type v} {A : Type w}
    [Field k] [Field K] [CommRing A] [Algebra k K]
    [Algebra A k] [Algebra A K] [IsScalarTower A k K]
    [Subsingleton (Algebra.H1Cotangent k K)] :
    Function.Injective (KaehlerDifferential.mapBaseChange A k K) := by
  have hδ_zero : Algebra.H1Cotangent.δ A k K = 0 := by
    -- Proof comment: the connecting map has subsingleton source, so every value is zero.
    ext x
    have hx : x = 0 := Subsingleton.elim _ _
    simp [hx]
  have hker :
      LinearMap.ker (KaehlerDifferential.mapBaseChange A k K) = ⊥ := by
    -- Proof comment: exactness identifies the kernel of the comparison map with the range of the
    -- zero connecting map.
    rw [(Algebra.H1Cotangent.exact_δ_mapBaseChange A k K).linearMap_ker_eq,
      hδ_zero, LinearMap.range_zero]
  exact LinearMap.ker_eq_bot.mp hker

/-- Helper for Chap10 Lemma 10 140 9: a Frobenius linear-independence criterion on an ambient
field restricts to every intermediate field. -/
lemma linearIndepOn_pow_restrict_intermediateField
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K] {p : ℕ}
    (hpow : ∀ s : Finset K,
      LinearIndepOn k _root_.id (s : Set K) →
        LinearIndepOn k (fun x ↦ x ^ p) (s : Set K))
    (L : IntermediateField k K) :
    ∀ s : Finset L,
      LinearIndepOn k _root_.id (s : Set L) →
        LinearIndepOn k (fun x ↦ x ^ p) (s : Set L) := by
  classical
  intro s hs
  have hValInj :
      Set.InjOn (L.val.toLinearMap : L →ₗ[k] K)
        (Submodule.span k ((_root_.id : L → L) '' (s : Set L))) := by
    -- Proof comment: the inclusion of an intermediate field is injective on every subspace.
    intro x _ y _ hxy
    exact Subtype.ext hxy
  have hsVal : LinearIndepOn k (fun x : L ↦ (x : K)) (s : Set L) := by
    -- Proof comment: move the independent family from `L` into the ambient field.
    simpa using hs.map_injOn (L.val.toLinearMap : L →ₗ[k] K) hValInj
  have hsK :
      LinearIndepOn k _root_.id ((s.image ((↑) : L → K) : Finset K) : Set K) := by
    -- Proof comment: reindex the ambient family by the corresponding finite image subset.
    simpa using hsVal.id_image
  have hpowK :
      LinearIndepOn k (fun x : K ↦ x ^ p) ((s.image ((↑) : L → K) : Finset K) : Set K) :=
    hpow (s.image ((↑) : L → K)) hsK
  have hpowK' :
      LinearIndepOn k (fun x : K ↦ x ^ p) (((↑) : L → K) '' (s : Set L)) := by
    -- Proof comment: rewrite the finite-image statement as a statement on the image set.
    simpa using hpowK
  have hpowComp : LinearIndepOn k (fun x : L ↦ ((x : K) ^ p)) (s : Set L) := by
    -- Proof comment: pull the ambient Frobenius-twisted independence back along the inclusion.
    simpa using
      (LinearIndepOn.comp_of_image (v := fun x : K ↦ x ^ p) (f := ((↑) : L → K)) hpowK'
        (by
          intro x _ y _ hxy
          exact Subtype.ext hxy))
  have hPowInj :
      Set.InjOn (L.val.toLinearMap : L →ₗ[k] K)
        (Submodule.span k ((fun x : L ↦ x ^ p) '' (s : Set L))) := by
    -- Proof comment: the same inclusion injectivity descends the Frobenius-twisted conclusion.
    intro x _ y _ hxy
    exact Subtype.ext hxy
  exact
    (LinearMap.linearIndepOn_iff_of_injOn (f := (L.val.toLinearMap : L →ₗ[k] K))
      (v := fun x : L ↦ x ^ p) (s := (s : Set L)) hPowInj).mp <| by
      simpa using hpowComp

/-- Helper for Chap10 Lemma 10 140 9: the Frobenius linear-independence criterion implies
Stacks-project separability by checking finitely generated intermediate fields. -/
lemma isSeparableOver_of_linearIndepOn_pow_charP
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    {p : ℕ} [Fact p.Prime] [CharP k p]
    (hpow : ∀ s : Finset K,
      LinearIndepOn k _root_.id (s : Set K) →
        LinearIndepOn k (fun x ↦ x ^ p) (s : Set K)) :
    Algebra.IsSeparableOver k K := by
  refine ⟨fun L hL ↦ ?_⟩
  -- Proof comment: the chapter Frobenius criterion applies to each finitely generated
  -- intermediate field after restricting the finite-set criterion along `L ↪ K`.
  letI : Algebra.EssFiniteType k L := (IntermediateField.essFiniteType_iff).2 hL
  exact
    isSeparablyGenerated_of_linearIndepOn_pow (k := k) (K := L) (p := p)
      (linearIndepOn_pow_restrict_intermediateField (k := k) (K := K) (p := p) hpow L)

/-- Helper for Chap10 Lemma 10 140 9: once the coefficient differentials of a relation have a
common slope, every coefficient ratio is a `p`th power in the base field. -/
private theorem coeffRatio_isPthPower_ofCommonSlope
    {k : Type u} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    {ι : Type*} (c : ι → k) (i0 : ι) (ω : KaehlerDifferential (ZMod p) k)
    (hslope : ∀ i, KaehlerDifferential.D (ZMod p) k (c i) = c i • ω) :
    ∀ i, ∃ b : k, b ^ p = c i / c i0 := by
  letI : PerfectField (ZMod p) := inferInstance
  intro i
  have hratio_zero :
      KaehlerDifferential.D (ZMod p) k (c i / c i0) = 0 := by
    -- Proof comment: the quotient rule collapses because both coefficients have the same
    -- differential slope.
    rw [Derivation.leibniz_div]
    have hnumerator :
        c i0 • KaehlerDifferential.D (ZMod p) k (c i) -
          c i • KaehlerDifferential.D (ZMod p) k (c i0) = 0 := by
      rw [hslope i, hslope i0]
      rw [smul_smul, smul_smul, mul_comm (c i0) (c i)]
      exact sub_self _
    rw [hnumerator]
    simp
  obtain ⟨b, hb⟩ :=
    (kaehlerDifferential_eq_zero_iff_exists_pth_root
      (k := ZMod p) (K := k) (p := p) (a := c i / c i0)).1 hratio_zero
  -- Proof comment: the prime-field differential criterion converts `D(cᵢ / cᵢ₀) = 0` into
  -- the required Frobenius root.
  exact ⟨b, hb⟩

/-- Helper for Chap10 Lemma 10 140 9: a minimal-support relation among the `p`th powers is
one-dimensional inside the space of relations supported on the same finite set. -/
private theorem supportedPowRelation_eq_smul_of_minSupport
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K] {p : ℕ}
    {s : Finset K} (c d : ↥(s : Set K) → k) (i0 : ↥(s : Set K))
    (hc_rel : ∑ i, c i • ((i : K) ^ p) = 0)
    (hi0 : c i0 ≠ 0)
    (hmin :
      ∀ e : ↥(s : Set K) → k,
        (∑ i, e i • ((i : K) ^ p) = 0) →
          e ≠ 0 → Nat.card (Function.support c) ≤ Nat.card (Function.support e))
    (hd_rel : ∑ i, d i • ((i : K) ^ p) = 0)
    (hdsub : Function.support d ⊆ Function.support c) :
    d = (d i0 / c i0) • c := by
  let a : k := d i0 / c i0
  let e : ↥(s : Set K) → k := d - a • c
  have he_rel : ∑ i, e i • ((i : K) ^ p) = 0 := by
    -- Proof comment: subtract the matching scalar multiple to produce another relation among the
    -- same `p`th powers.
    calc
      ∑ i, e i • ((i : K) ^ p)
          = ∑ i, (d i • ((i : K) ^ p) - a • (c i • ((i : K) ^ p))) := by
              simp [e, a, sub_smul, smul_smul, mul_comm]
      _ = (∑ i, d i • ((i : K) ^ p)) - a • ∑ i, c i • ((i : K) ^ p) := by
            simp [Finset.sum_sub_distrib, Finset.smul_sum]
      _ = 0 := by
            have hd_rel' : ∑ i ∈ s.attach, d i • ((i : K) ^ p) = 0 := by
              simpa using hd_rel
            have hc_rel' : ∑ i ∈ s.attach, c i • ((i : K) ^ p) = 0 := by
              simpa using hc_rel
            simp [hc_rel', hd_rel']
  have hei0 : e i0 = 0 := by
    -- Proof comment: the chosen scalar multiple cancels the pivot coefficient.
    simp [e, a, hi0]
  have he_support_subset : Function.support e ⊆ Function.support c := by
    -- Proof comment: each summand of the adjusted relation is supported inside `support c`.
    intro i hi
    have hi' : i ∈ Function.support d ∪ Function.support (a • c) :=
      Function.support_sub d (a • c) hi
    rcases hi' with hid | hic
    · exact hdsub hid
    · exact Function.support_const_smul_subset a c hic
  have hi0_mem_c : i0 ∈ Function.support c := by
    simpa [Function.support] using hi0
  have hi0_not_e : i0 ∉ Function.support e := by
    simp [Function.support, hei0]
  have hssub : Function.support e ⊂ Function.support c := by
    -- Proof comment: the adjusted support is proper because the pivot remains in `support c` but
    -- has been removed from `support e`.
    refine ⟨he_support_subset, ?_⟩
    intro hEq
    exact hi0_not_e (hEq hi0_mem_c)
  have he_zero : e = 0 := by
    by_contra he_nonzero
    have hle := hmin e he_rel he_nonzero
    have hlt : Nat.card (Function.support e) < Nat.card (Function.support c) := by
      exact (Set.toFinite (Function.support c)).card_lt_card hssub
    exact (not_lt_of_ge hle) hlt
  ext i
  -- Proof comment: the adjusted relation is zero, so the second relation is the chosen scalar
  -- multiple of the minimal one.
  have hi := congrFun he_zero i
  change d i - a * c i = 0 at hi
  simpa [a] using sub_eq_zero.mp hi

/-- Helper for Chap10 Lemma 10 140 9: evaluate a tensor by applying a dual functional to the
Kähler-differential factor and multiplying the resulting scalar into the field factor. -/
private def tensorDualEvalMap
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    {p : ℕ} [Algebra (ZMod p) k]
    (ell : Module.Dual k (KaehlerDifferential (ZMod p) k)) :
    _root_.TensorProduct k K (KaehlerDifferential (ZMod p) k) →ₗ[k] K :=
  ((_root_.TensorProduct.rid k K : _root_.TensorProduct k K k ≃ₗ[k] K) :
    _root_.TensorProduct k K k →ₗ[k] K).comp
    (_root_.TensorProduct.map (R := k) (f := (LinearMap.id : K →ₗ[k] K)) (g := ell))

/-- Helper for Chap10 Lemma 10 140 9: the tensor evaluator sends a pure tensor to the expected
scalar multiple. -/
private lemma tensorDualEvalMap_tmul
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    {p : ℕ} [Algebra (ZMod p) k]
    (ell : Module.Dual k (KaehlerDifferential (ZMod p) k))
    (x : K) (omega : KaehlerDifferential (ZMod p) k) :
    tensorDualEvalMap (K := K) (p := p) ell (_root_.TensorProduct.tmul k x omega) =
      ell omega • x := by
  -- Proof comment: unfold the evaluator once, then use the canonical tensor-map and right-unit
  -- computation rules.
  simp [tensorDualEvalMap]

/-- Helper for Chap10 Lemma 10 140 9: projecting a tensor differential relation by any dual
functional gives the corresponding scalar relation among the `p`th powers. -/
private theorem dualEvaluation_powRelation_of_tensorDifferential
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    {p : ℕ} [Algebra (ZMod p) k]
    {s : Finset K} (c : ↥(s : Set K) → k)
    (hT : ∑ i : ↥(s : Set K), _root_.TensorProduct.tmul k ((i : K) ^ p)
        (KaehlerDifferential.D (ZMod p) k (c i)) = 0)
    (ell : Module.Dual k (KaehlerDifferential (ZMod p) k)) :
    ∑ i : ↥(s : Set K), ell (KaehlerDifferential.D (ZMod p) k (c i)) • ((i : K) ^ p) =
      0 := by
  have hmap := congrArg (tensorDualEvalMap (K := K) (p := p) ell) hT
  -- Proof comment: linearity turns the tensor sum into the scalar relation seen by `ell`.
  simpa [map_sum, tensorDualEvalMap_tmul] using hmap

/-- Helper for Chap10 Lemma 10 140 9: the dual-evaluated differential coefficients are supported
inside the original coefficient support. -/
private theorem dualDifferential_support_subset
    {k : Type u} {K : Type v} [Field k] [Field K]
    {p : ℕ} [Algebra (ZMod p) k]
    {s : Finset K} (c : ↥(s : Set K) → k)
    (ell : Module.Dual k (KaehlerDifferential (ZMod p) k)) :
    Function.support (fun i ↦ ell (KaehlerDifferential.D (ZMod p) k (c i))) ⊆
      Function.support c := by
  intro i hi
  -- Proof comment: outside the support of `c`, the universal derivation and then `ell` both
  -- vanish, so the dual coefficient cannot be supported there.
  by_contra hc
  have hci : c i = 0 := by
    simpa [Function.support] using hc
  have hdual : ell (KaehlerDifferential.D (ZMod p) k (c i)) = 0 := by
    simp [hci]
  exact hi hdual

/-- Helper for Chap10 Lemma 10 140 9: scalar relations obtained from every dual functional force
the coefficient differentials to share a common slope. -/
private theorem commonSlope_of_dualPowRelations
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    {p : ℕ} [Algebra (ZMod p) k]
    {s : Finset K} (c : ↥(s : Set K) → k) (i0 : ↥(s : Set K))
    (hc_rel : ∑ i, c i • ((i : K) ^ p) = 0)
    (hi0 : c i0 ≠ 0)
    (hmin :
      ∀ e : ↥(s : Set K) → k,
        (∑ i, e i • ((i : K) ^ p) = 0) →
          e ≠ 0 → Nat.card (Function.support c) ≤ Nat.card (Function.support e))
    (hdual :
      ∀ ell : Module.Dual k (KaehlerDifferential (ZMod p) k),
        ∑ i : ↥(s : Set K),
          ell (KaehlerDifferential.D (ZMod p) k (c i)) • ((i : K) ^ p) = 0) :
    ∃ omega : KaehlerDifferential (ZMod p) k,
      ∀ i, KaehlerDifferential.D (ZMod p) k (c i) = c i • omega := by
  refine ⟨(c i0)⁻¹ • KaehlerDifferential.D (ZMod p) k (c i0), ?_⟩
  intro i
  have hsep :
      ∀ ell : Module.Dual k (KaehlerDifferential (ZMod p) k),
        ell (KaehlerDifferential.D (ZMod p) k (c i) -
          c i • ((c i0)⁻¹ • KaehlerDifferential.D (ZMod p) k (c i0))) = 0 := by
    intro ell
    let d : ↥(s : Set K) → k :=
      fun j ↦ ell (KaehlerDifferential.D (ZMod p) k (c j))
    have hd_eq :
        d = (d i0 / c i0) • c := by
      -- Proof comment: minimality makes the dual-projected relation proportional to the original
      -- relation, because its support is contained in the original support.
      exact
        supportedPowRelation_eq_smul_of_minSupport (K := K) (p := p) c d i0
          hc_rel hi0 hmin (hdual ell)
          (dualDifferential_support_subset (K := K) (p := p) c ell)
    have hcoeff : ell (KaehlerDifferential.D (ZMod p) k (c i)) =
        (ell (KaehlerDifferential.D (ZMod p) k (c i0)) / c i0) * c i := by
      simpa [d, Pi.smul_apply] using congrFun hd_eq i
    -- Proof comment: the proportionality coefficient is exactly evaluation on the chosen slope.
    simp [map_sub, hcoeff, div_eq_mul_inv, smul_smul, mul_comm, mul_assoc]
  have hzero :
      KaehlerDifferential.D (ZMod p) k (c i) -
        c i • ((c i0)⁻¹ • KaehlerDifferential.D (ZMod p) k (c i0)) = 0 :=
    (Module.forall_dual_apply_eq_zero_iff k
      (KaehlerDifferential.D (ZMod p) k (c i) -
        c i • ((c i0)⁻¹ • KaehlerDifferential.D (ZMod p) k (c i0)))).1 hsep
  -- Proof comment: dual separation turns the evaluated equality into the desired equality in
  -- the Kähler module itself.
  exact sub_eq_zero.mp hzero

/-- Helper for Chap10 Lemma 10 140 9: coefficient-ratio `p`th roots turn a `p`th-power relation
into a nonzero ordinary linear relation. -/
private theorem linearRelation_of_powRelation_coeffRoots
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    {p : ℕ} [Fact p.Prime] [CharP K p]
    {s : Finset K} (c b : ↥(s : Set K) → k) (i0 : ↥(s : Set K))
    (hc_rel : ∑ i, c i • ((i : K) ^ p) = 0)
    (hi0 : c i0 ≠ 0)
    (hroot : ∀ i, b i ^ p = c i / c i0) :
    (∑ i, b i • (i : K) = 0) ∧ b i0 ≠ 0 := by
  have hsum_pow : (∑ i : ↥(s : Set K), b i • (i : K)) ^ p = 0 := by
    -- Proof comment: in characteristic `p`, Frobenius converts the ordinary relation candidate
    -- into the given relation after substituting the chosen coefficient roots.
    calc
      (∑ i : ↥(s : Set K), b i • (i : K)) ^ p
          = ∑ i : ↥(s : Set K), (b i • (i : K)) ^ p := by
              simpa using
                (sum_pow_char p Finset.univ (fun i : ↥(s : Set K) ↦ b i • (i : K)))
      _ = ∑ i : ↥(s : Set K), (b i ^ p) • ((i : K) ^ p) := by
            simp [Algebra.smul_def, mul_pow, map_pow]
      _ = ∑ i : ↥(s : Set K), (c i / c i0) • ((i : K) ^ p) := by
            simp [hroot]
      _ = ∑ i : ↥(s : Set K), (c i0)⁻¹ • (c i • ((i : K) ^ p)) := by
            simp [div_eq_mul_inv, smul_smul, mul_comm]
      _ = (c i0)⁻¹ • ∑ i : ↥(s : Set K), c i • ((i : K) ^ p) := by
            simp [Finset.smul_sum]
      _ = (c i0)⁻¹ • (0 : K) := by
            rw [hc_rel]
      _ = 0 := by
            simp
  constructor
  · -- Proof comment: fields are reduced, so vanishing of the `p`th power forces the relation
    -- candidate itself to vanish.
    exact eq_zero_of_pow_eq_zero hsum_pow
  · intro hb0
    have hbpow : b i0 ^ p = 1 := by
      simpa [hi0] using hroot i0
    have hzero : b i0 ^ p = 0 := by
      rw [hb0]
      exact zero_pow ((Fact.out : Nat.Prime p).ne_zero)
    exact zero_ne_one (by rw [← hbpow, hzero])

/-- Helper for Chap10 Lemma 10 140 9: in characteristic `p`, differentiating a scalar multiple
of a `p`th power leaves only the differential of the scalar. -/
private lemma kaehlerDifferential_D_smul_pow_eq_pow_smul_D_algebraMap
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    {p : ℕ} [Fact p.Prime] [CharP k p] [CharP K p]
    [Algebra (ZMod p) k] [Algebra (ZMod p) K] [IsScalarTower (ZMod p) k K]
    (c : k) (x : K) :
    KaehlerDifferential.D (ZMod p) K (c • x ^ p) =
      x ^ p • KaehlerDifferential.D (ZMod p) K (algebraMap k K c) := by
  have hDxpow : KaehlerDifferential.D (ZMod p) K (x ^ p) = 0 := by
    -- Proof comment: the power rule gives a factor `p`, which is zero in characteristic `p`.
    rw [Derivation.leibniz_pow]
    rw [← Nat.cast_smul_eq_nsmul K p]
    simp
  -- Proof comment: expand the product rule and discard the vanished `D(x^p)` term.
  rw [Algebra.smul_def, Derivation.leibniz, hDxpow]
  simp

/-- Helper for Chap10 Lemma 10 140 9: differentiating a relation among `p`th powers gives the
tensor relation among coefficient differentials. -/
private theorem powRelation_tensorDifferential_eq_zero
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    {p : ℕ} [Fact p.Prime] [CharP k p] [CharP K p]
    [Algebra (ZMod p) k] [Algebra (ZMod p) K] [IsScalarTower (ZMod p) k K]
    (hinj : Function.Injective (KaehlerDifferential.mapBaseChange (ZMod p) k K))
    {s : Finset K} (c : ↥(s : Set K) → k)
    (hc_rel : ∑ i, c i • ((i : K) ^ p) = 0) :
    ∑ i : ↥(s : Set K), _root_.TensorProduct.tmul k ((i : K) ^ p)
        (KaehlerDifferential.D (ZMod p) k (c i)) = 0 := by
  apply hinj
  rw [map_zero]
  -- Proof comment: apply the base-change map and identify the result with the derivative of the
  -- original scalar relation.
  calc
    KaehlerDifferential.mapBaseChange (ZMod p) k K
        (∑ i : ↥(s : Set K), _root_.TensorProduct.tmul k ((i : K) ^ p)
          (KaehlerDifferential.D (ZMod p) k (c i)))
        = ∑ i : ↥(s : Set K), ((i : K) ^ p) •
            KaehlerDifferential.D (ZMod p) K (algebraMap k K (c i)) := by
          simp [map_sum, KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D]
    _ = ∑ i : ↥(s : Set K), KaehlerDifferential.D (ZMod p) K
          (c i • ((i : K) ^ p)) := by
          simp [kaehlerDifferential_D_smul_pow_eq_pow_smul_D_algebraMap]
    _ = KaehlerDifferential.D (ZMod p) K
          (∑ i : ↥(s : Set K), c i • ((i : K) ^ p)) := by
          simp [map_sum]
    _ = 0 := by
          rw [hc_rel]
          simp

/-- Helper for Chap10 Lemma 10 140 9: a finite dependent family admits a nonzero relation with
minimal support cardinality. -/
private theorem exists_minimal_linearRelation
    {k : Type u} {K : Type v} [Field k] [AddCommGroup K] [Module k K]
    {ι : Type*} [Fintype ι] {v : ι → K}
    (hdep : ¬ LinearIndependent k v) :
    ∃ (c : ι → k) (i0 : ι),
      (∑ i, c i • v i = 0) ∧ c i0 ≠ 0 ∧
        ∀ e : ι → k,
          (∑ i, e i • v i = 0) →
            e ≠ 0 → Nat.card (Function.support c) ≤ Nat.card (Function.support e) := by
  classical
  obtain ⟨c₀, hc₀_rel, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.mp hdep
  have hc₀_ne : c₀ ≠ 0 := by
    -- Proof comment: the coefficient nonvanishing supplied by dependence makes the relation
    -- genuinely nonzero.
    intro hc₀
    exact hi₀ (congrFun hc₀ i₀)
  let P : ℕ → Prop := fun n ↦
    ∃ c : ι → k, (∑ i, c i • v i = 0) ∧ c ≠ 0 ∧
      Nat.card (Function.support c) = n
  have hP : ∃ n, P n :=
    ⟨Nat.card (Function.support c₀), c₀, hc₀_rel, hc₀_ne, rfl⟩
  obtain ⟨c, hc_rel, hc_ne, hcard⟩ := Nat.find_spec hP
  obtain ⟨i0, hi0⟩ : ∃ i, c i ≠ 0 := by
    -- Proof comment: a nonzero function has at least one nonzero coefficient to use as pivot.
    by_contra hnone
    push Not at hnone
    exact hc_ne (funext hnone)
  refine ⟨c, i0, hc_rel, hi0, ?_⟩
  intro e he_rel he_ne
  have hPe : P (Nat.card (Function.support e)) :=
    ⟨e, he_rel, he_ne, rfl⟩
  -- Proof comment: minimality of `Nat.find` gives the desired cardinal inequality.
  rw [hcard]
  exact Nat.find_min' hP hPe

/-- Helper for Chap10 Lemma 10 140 9: a minimal `p`th-power relation contradicts ordinary
linear independence once the Kähler base-change map is injective. -/
private theorem minimalPowRelation_false_of_kaehlerMapBaseChange_injective
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    {p : ℕ} [Fact p.Prime] [CharP k p] [CharP K p]
    [Algebra (ZMod p) k] [Algebra (ZMod p) K] [IsScalarTower (ZMod p) k K]
    (hinj : Function.Injective (KaehlerDifferential.mapBaseChange (ZMod p) k K))
    {s : Finset K} (hs : LinearIndependent k (fun i : ↥(s : Set K) ↦ (i : K)))
    (c : ↥(s : Set K) → k) (i0 : ↥(s : Set K))
    (hc_rel : ∑ i, c i • ((i : K) ^ p) = 0)
    (hi0 : c i0 ≠ 0)
    (hmin :
      ∀ e : ↥(s : Set K) → k,
        (∑ i, e i • ((i : K) ^ p) = 0) →
          e ≠ 0 → Nat.card (Function.support c) ≤ Nat.card (Function.support e)) :
    False := by
  classical
  have hT :
      ∑ i : ↥(s : Set K), _root_.TensorProduct.tmul k ((i : K) ^ p)
        (KaehlerDifferential.D (ZMod p) k (c i)) = 0 :=
    powRelation_tensorDifferential_eq_zero (k := k) (K := K) (p := p) hinj c hc_rel
  have hdual :
      ∀ ell : Module.Dual k (KaehlerDifferential (ZMod p) k),
        ∑ i : ↥(s : Set K),
          ell (KaehlerDifferential.D (ZMod p) k (c i)) • ((i : K) ^ p) = 0 := by
    -- Proof comment: dual evaluation turns the tensor relation into scalar relations.
    intro ell
    exact dualEvaluation_powRelation_of_tensorDifferential (K := K) (p := p) c hT ell
  obtain ⟨omega, hslope⟩ :=
    commonSlope_of_dualPowRelations (K := K) (p := p) c i0 hc_rel hi0 hmin hdual
  have hroots : ∀ i, ∃ b : k, b ^ p = c i / c i0 :=
    coeffRatio_isPthPower_ofCommonSlope (p := p) c i0 omega hslope
  let b : ↥(s : Set K) → k := fun i ↦ Classical.choose (hroots i)
  have hroot : ∀ i, b i ^ p = c i / c i0 := fun i ↦ Classical.choose_spec (hroots i)
  have hbrel :
      (∑ i, b i • (i : K) = 0) ∧ b i0 ≠ 0 :=
    linearRelation_of_powRelation_coeffRoots (p := p) c b i0 hc_rel hi0 hroot
  have hbzero : b i0 = 0 :=
    Fintype.linearIndependent_iff.mp hs b hbrel.1 i0
  -- Proof comment: the constructed ordinary relation has a nonzero pivot, contradicting `hs`.
  exact hbrel.2 hbzero

/-- Helper for Chap10 Lemma 10 140 9: Kähler base-change injectivity forces Frobenius to preserve
linear independence on every finite subset of the field extension. -/
private theorem linearIndepOn_pow_of_kaehlerMapBaseChange_injective
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    {p : ℕ} [Fact p.Prime] [CharP k p] [CharP K p]
    [Algebra (ZMod p) k] [Algebra (ZMod p) K] [IsScalarTower (ZMod p) k K]
    (hinj : Function.Injective (KaehlerDifferential.mapBaseChange (ZMod p) k K)) :
    ∀ s : Finset K,
      LinearIndepOn k _root_.id (s : Set K) →
        LinearIndepOn k (fun x ↦ x ^ p) (s : Set K) := by
  classical
  intro s hs
  by_contra hdepOn
  have hs_subtype :
      LinearIndependent k (fun i : ↥(s : Set K) ↦ (i : K)) := by
    -- Proof comment: work on the finite subtype where all sums are over `Finset.univ`.
    simpa [LinearIndepOn] using hs
  have hdep_subtype :
      ¬ LinearIndependent k (fun i : ↥(s : Set K) ↦ ((i : K) ^ p)) := by
    simpa [LinearIndepOn] using hdepOn
  obtain ⟨c, i0, hc_rel, hi0, hmin⟩ :=
    exists_minimal_linearRelation (k := k) (K := K)
      (v := fun i : ↥(s : Set K) ↦ ((i : K) ^ p)) hdep_subtype
  -- Proof comment: the minimal relation is impossible by the Kähler bridge and coefficient-root
  -- argument, so the Frobenius-twisted family is independent.
  exact
    minimalPowRelation_false_of_kaehlerMapBaseChange_injective
      (k := k) (K := K) (p := p) hinj hs_subtype c i0 hc_rel hi0 hmin

/-- Helper for Chap10 Lemma 10 140 9: formal smoothness of a field extension gives
Stacks-project separability. -/
lemma isSeparableOver_of_formallySmooth_fieldExtension
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    (h : Algebra.FormallySmooth k K) :
    Algebra.IsSeparableOver k K := by
  rcases CharP.exists' k with hchar0 | ⟨p, hp, hcharp⟩
  · -- Proof comment: in characteristic zero the base is perfect, so every extension is
    -- Stacks-project separable.
    letI : CharZero k := hchar0
    letI : PerfectField k := PerfectField.ofCharZero
    exact Algebra.IsSeparableOver.of_perfectField
  · -- Proof comment: in positive characteristic, formal smoothness gives vanishing of `H₁`, and
    -- Jacobi-Zariski exactness turns this into injectivity of the prime-field Kähler comparison.
    letI : Fact p.Prime := hp
    letI : CharP k p := hcharp
    letI : Algebra.FormallySmooth k K := h
    letI : CharP K p :=
      CharP.of_ringHom_of_ne_zero (algebraMap k K) p hp.out.ne_zero
    letI : Algebra (ZMod p) k := ZMod.algebra k p
    letI : Algebra (ZMod p) K := ZMod.algebra K p
    letI : IsScalarTower (ZMod p) k K := by infer_instance
    letI : Subsingleton (Algebra.H1Cotangent k K) :=
      (Algebra.formallySmooth_iff_subsingleton_h1Cotangent_of_field k K).1 h
    have hkaehler :
        Function.Injective (KaehlerDifferential.mapBaseChange (ZMod p) k K) :=
      kaehlerDifferentialMapBaseChange_injective_of_subsingletonH1
        (A := ZMod p) (k := k) (K := K)
    have hpow :
        ∀ s : Finset K,
          LinearIndepOn k _root_.id (s : Set K) →
            LinearIndepOn k (fun x ↦ x ^ p) (s : Set K) :=
      linearIndepOn_pow_of_kaehlerMapBaseChange_injective
        (k := k) (K := K) (p := p) hkaehler
    -- Proof comment: once the finite-set criterion is available, the separability owner predicate
    -- follows by checking finitely generated intermediate fields.
    exact isSeparableOver_of_linearIndepOn_pow_charP (k := k) (K := K) (p := p) hpow

/-- Helper for Chap10 Lemma 10 140 9: the localization of `S` at its generic point is a
fraction ring of `S`. -/
lemma isFractionRing_localizationAtPrime_bot :
    IsFractionRing S (Localization.AtPrime (⊥ : Ideal S)) := by
  -- Proof comment: at the zero prime of a domain, the prime complement is exactly the
  -- non-zero-divisors, so the existing prime-localization instance is the fraction-ring instance.
  have hloc :
      IsLocalization (nonZeroDivisors S) (Localization.AtPrime (⊥ : Ideal S)) := by
    convert
      (inferInstance :
        IsLocalization (⊥ : Ideal S).primeCompl (Localization.AtPrime (⊥ : Ideal S)))
    ext s
    simp [Ideal.primeCompl]
  exact hloc

omit [IsDomain R] in
/-- Helper for Chap10 Lemma 10 140 9: generic-point smoothness is formal smoothness of the
fraction ring. -/
lemma isSmoothAt_bot_iff_formallySmooth_fractionRing :
    IsSmoothAt R (⊥ : Ideal S) ↔ Algebra.FormallySmooth R (FractionRing S) := by
  -- Proof comment: replace the local ring at `(0)` by the canonical fraction-ring model and
  -- transport formal smoothness across the resulting `R`-algebra equivalence.
  letI : IsFractionRing S (Localization.AtPrime (⊥ : Ideal S)) :=
    isFractionRing_localizationAtPrime_bot (S := S)
  exact
    (Algebra.FormallySmooth.iff_of_equiv
      ((FractionRing.algEquiv S (Localization.AtPrime (⊥ : Ideal S))).restrictScalars R)).symm

omit [IsDomain R] [IsDomain S] in
/-- Helper for Chap10 Lemma 10 140 9: formal smoothness over `R` of `FractionRing S` is
equivalent to formal smoothness over `FractionRing R`. -/
lemma fractionRing_formallySmooth_base_iff [FaithfulSMul R S]
    [Algebra (FractionRing R) (FractionRing S)]
    [IsScalarTower R (FractionRing R) (FractionRing S)] :
    Algebra.FormallySmooth R (FractionRing S) ↔
      Algebra.FormallySmooth (FractionRing R) (FractionRing S) := by
  -- Proof comment: the forward direction localizes the base at `R⁰`; the reverse direction
  -- composes the smooth localization `R → FractionRing R` with the fraction-field algebra.
  constructor
  · intro h
    letI : Algebra.FormallySmooth R (FractionRing S) := h
    exact
      Algebra.FormallySmooth.localization_base
        (R := R) (Rₘ := FractionRing R) (Sₘ := FractionRing S) (nonZeroDivisors R)
  · intro h
    letI : Algebra.FormallySmooth (FractionRing R) (FractionRing S) := h
    have hbase : Algebra.FormallySmooth R (FractionRing R) :=
      Algebra.FormallySmooth.of_isLocalization (nonZeroDivisors R)
    letI : Algebra.FormallySmooth R (FractionRing R) := hbase
    exact Algebra.FormallySmooth.comp R (FractionRing R) (FractionRing S)

/-- Helper for Chap10 Lemma 10 140 9: formal smoothness over the source domain is equivalent to
Stacks-project separability of the induced fraction-field extension. -/
lemma fractionRing_formallySmooth_iff_isSeparableOver [FaithfulSMul R S]
    [Algebra (FractionRing R) (FractionRing S)]
    [IsScalarTower R (FractionRing R) (FractionRing S)] :
    Algebra.FormallySmooth R (FractionRing S) ↔
      Algebra.IsSeparableOver (FractionRing R) (FractionRing S) := by
  -- Proof comment: first move the base to `FractionRing R`, then invoke the field-extension
  -- criterion. The reverse direction is available from Lemma `10.158.7`; the forward direction is
  -- exactly the missing field bridge whose later owner module currently does not compile.
  constructor
  · intro h
    have hfieldSmooth :
        Algebra.FormallySmooth (FractionRing R) (FractionRing S) :=
      (fractionRing_formallySmooth_base_iff (R := R) (S := S)).mp h
    -- Proof comment: after base-changing to the fraction field, the field-extension owner theorem
    -- converts formal smoothness into Stacks-project separability.
    exact isSeparableOver_of_formallySmooth_fieldExtension hfieldSmooth
  · intro hsep
    letI : Algebra.IsSeparableOver (FractionRing R) (FractionRing S) := hsep
    have hfieldSmooth :
        Algebra.FormallySmooth (FractionRing R) (FractionRing S) :=
      Algebra.formallySmooth_of_isSeparableOver
    exact (fractionRing_formallySmooth_base_iff (R := R) (S := S)).mpr hfieldSmooth

variable [Algebra.FiniteType R S]

/-- Bridge/view: the Stacks-project separability predicate on the induced fraction-field extension
attached to an injective finite-type map of domains. The only non-source-facing data are the
derived faithful action of `R` on `S` and the canonical induced algebra `FractionRing R →
FractionRing S`, both kept internal to this bridge. -/
noncomputable abbrev fractionRingIsSeparableOver
    (hinj : Function.Injective (algebraMap R S)) : Prop :=
  let _ : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hinj
  let _ : Algebra (FractionRing R) (FractionRing S) :=
    FractionRing.liftAlgebra R (FractionRing S)
  IsSeparableOver (FractionRing R) (FractionRing S)

-- Proof sketch: for the forward implication, replace the smooth-at-`(0)` hypothesis by a smooth
-- localization `S_g`, base change along `R → FractionRing R`, and use the field case together with
-- geometric reducedness to deduce that `FractionRing S / FractionRing R` is separable in the
-- Stacks Project sense. For the reverse implication, first localize so the map is of finite
-- presentation, apply smooth-locus base change to the generic fiber over `FractionRing R`, and
-- then use the field criterion from Lemma `10.140.5` at the generic point.
/-- Chap10 Lemma 10 140 9 (Lemma 10.140.9): let `R → S` be an injective finite type ring map of domains. Then `R → S` is
smooth at the generic point `q = (0)` if and only if the induced extension of fraction fields
`FractionRing S / FractionRing R` is separable in the Stacks Project sense. -/
@[stacks 07ND]
theorem isSmoothAt_zero_iff_isSeparableOver_fractionRing
    (hinj : Function.Injective (algebraMap R S)) :
    IsSmoothAt R (⊥ : Ideal S) ↔ fractionRingIsSeparableOver hinj := by
  -- Proof comment: retain the finite-type hypothesis from the source statement in the proof
  -- context before passing to the generic local and fraction-field criteria.
  have hfiniteType : Algebra.FiniteType R S := inferInstance
  -- Proof comment: install the canonical fraction-field algebra induced by the injective map,
  -- then compose the generic-local and field-extension equivalences.
  letI : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hinj
  letI : Algebra (FractionRing R) (FractionRing S) :=
    FractionRing.liftAlgebra R (FractionRing S)
  have hfield :
      Algebra.FormallySmooth R (FractionRing S) ↔ fractionRingIsSeparableOver hinj := by
    simpa [fractionRingIsSeparableOver] using
      fractionRing_formallySmooth_iff_isSeparableOver (R := R) (S := S)
  exact (isSmoothAt_bot_iff_formallySmooth_fractionRing (R := R) (S := S)).trans hfield

end

end Algebra
