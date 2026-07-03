import Mathlib
import stacks_project.Chap10.Definition_10_69_1
import stacks_project.Chap10.«10_69_0_1»
import stacks_project.Chap10.Lemma_10_68_10

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open RingTheory
open Function
open Lean Elab Term Meta
open scoped TensorProduct BigOperators

namespace RingTheory.Sequence

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Helper for Lemma 10.69.2: recover the imported private declarations from `10.69.0.1` by their
compiled names so this item can reuse the owner proof route without reimplementing the transport
chain locally. -/
private def chap10_69_0_1_private_name (decl : String) : Lean.Name :=
  Lean.Name.str
    (Lean.Name.str
      (Lean.Name.str
        (Lean.Name.num
          (Lean.Name.str
            (Lean.Name.str
              (Lean.Name.str
                (Lean.Name.str Lean.Name.anonymous "_private")
                "stacks_project")
              "Chap10")
            "10_69_0_1")
          0)
        "RingTheory")
      "Sequence")
    decl

/-- Helper for Lemma 10.69.2: elaborate one imported private declaration from `10.69.0.1` using
its compiled name, so the current proof can call the owner lemmas directly. -/
elab "chap10_69_0_1_private%" s:str : term => do
  mkConstWithFreshMVarLevels (chap10_69_0_1_private_name s.getString)

/-
Domain triage:
* primary domain: regular and quasi-regular sequences in commutative algebra;
* sampled owner API:
  `RingTheory.Sequence.IsRegular`,
  `RingTheory.Sequence.isRegular_cons_iff`,
  `RingTheory.Sequence.IsWeaklyRegular`,
  `RingTheory.Sequence.IsQuasiRegular`;
* core/canonical owner: `RingTheory.Sequence.IsRegular M rs`;
* layer split: regularity on successive quotients is primitive owner data, while quasi-regularity
  is the source-facing graded comparison notion of `Definition 10.69.1`, and Lemma `10.69.2` is
  the derived bridge from the owner regularity theorem to that source-facing notion.
-/

/-- Helper for Lemma 10.69.2: every source tensor is a finite sum of monomial simple tensors with
quotient-module coefficients. -/
private theorem tensor_monomial_expansion
    (rs : List R)
    (z : (M ⧸ ((Ideal.ofList rs) • (⊤ : Submodule R M))) ⊗[R ⧸ Ideal.ofList rs]
      MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs)) :
    ∃ coeffs : (Fin rs.length →₀ ℕ) →₀ (M ⧸ ((Ideal.ofList rs) • (⊤ : Submodule R M))),
      z =
        coeffs.sum fun e q ↦
          (q ⊗ₜ[R ⧸ Ideal.ofList rs]
            MvPolynomial.monomial e (1 : R ⧸ Ideal.ofList rs)) := by
  let comm :=
    TensorProduct.comm (R ⧸ Ideal.ofList rs)
      (M ⧸ ((Ideal.ofList rs) • (⊤ : Submodule R M)))
      (MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs))
  let scalar :=
    MvPolynomial.scalarRTensor
      (R := R ⧸ Ideal.ofList rs)
      (σ := Fin rs.length)
      (N := M ⧸ ((Ideal.ofList rs) • (⊤ : Submodule R M)))
  let coeffs :
      (Fin rs.length →₀ ℕ) →₀ (M ⧸ ((Ideal.ofList rs) • (⊤ : Submodule R M))) :=
    scalar (comm z)
  refine ⟨coeffs, ?_⟩
  -- Pass to the commuted tensor product, where `scalarRTensor` identifies the source with a
  -- finitely supported coefficient family.
  apply comm.injective
  calc
    comm z = scalar.symm coeffs := by
      simp [coeffs]
    _ = scalar.symm (coeffs.sum fun e q ↦ Finsupp.single e q) := by
      simp
    _ = coeffs.sum fun e q ↦ scalar.symm (Finsupp.single e q) := by
      simp [Finsupp.sum]
    _ = coeffs.sum fun e q ↦
          (MvPolynomial.monomial e (1 : R ⧸ Ideal.ofList rs) ⊗ₜ[R ⧸ Ideal.ofList rs] q) := by
      refine Finsupp.sum_congr ?_
      intro e q
      rw [MvPolynomial.scalarRTensor_symm_apply_single]
    _ = comm
          (coeffs.sum fun e q ↦
            (q ⊗ₜ[R ⧸ Ideal.ofList rs]
              MvPolynomial.monomial e (1 : R ⧸ Ideal.ofList rs))) := by
      simp only [Finsupp.sum, map_sum]
      refine Finset.sum_congr rfl ?_
      intro e he
      rw [TensorProduct.comm_tmul]

/-- Helper for Lemma 10.69.2: rewrite a monomial `Finsupp.sum` as the corresponding support-indexed
finite sum of simple tensors. -/
private theorem monomial_tensor_family_sum_eq_support_sum
    {rs : List R} (a : (Fin rs.length →₀ ℕ) →₀ M) :
    (a.sum fun e m ↦
      ((Submodule.Quotient.mk m :
          M ⧸ ((Ideal.ofList rs) • (⊤ : Submodule R M))) ⊗ₜ[R ⧸ Ideal.ofList rs]
        MvPolynomial.monomial e (1 : R ⧸ Ideal.ofList rs))) =
      Finset.sum a.support fun e ↦
        ((Submodule.Quotient.mk (a e) :
            M ⧸ ((Ideal.ofList rs) • (⊤ : Submodule R M))) ⊗ₜ[R ⧸ Ideal.ofList rs]
          MvPolynomial.monomial e (1 : R ⧸ Ideal.ofList rs)) := by
  -- `Finsupp.sum` is definitionally the support-indexed finite sum.
  rw [Finsupp.sum]

/-- Helper for Lemma 10.69.2: rewrite the homogeneous `Finsupp.filter` slice as the corresponding
filtered support sum. -/
private theorem monomial_tensor_filtered_sum_eq_support_filter_sum
    {rs : List R} (a : (Fin rs.length →₀ ℕ) →₀ M) (n : ℕ) :
    ((a.filter fun e ↦ e.degree = n).sum fun e m ↦
      ((Submodule.Quotient.mk m :
          M ⧸ ((Ideal.ofList rs) • (⊤ : Submodule R M))) ⊗ₜ[R ⧸ Ideal.ofList rs]
        MvPolynomial.monomial e (1 : R ⧸ Ideal.ofList rs))) =
      Finset.sum (a.support.filter fun e ↦ e.degree = n) fun e ↦
        ((Submodule.Quotient.mk (a e) :
            M ⧸ ((Ideal.ofList rs) • (⊤ : Submodule R M))) ⊗ₜ[R ⧸ Ideal.ofList rs]
          MvPolynomial.monomial e (1 : R ⧸ Ideal.ofList rs)) := by
  -- On the filtered support, the filtered coefficient agrees with the original one.
  rw [Finsupp.sum]
  refine Finset.sum_congr rfl ?_
  intro e he
  have hdeg : e.degree = n := (Finset.mem_filter.mp he).2
  simp [hdeg]

/-- Helper for Lemma 10.69.2: the monomial weight attached to an exponent vector lies in the
matching power of `Ideal.ofList rs`. -/
private theorem ofList_monomial_weight_mem_pow
    (rs : List R) (e : Fin rs.length →₀ ℕ) :
    (∏ i : Fin rs.length, rs.get i ^ e i) ∈ (Ideal.ofList rs) ^ e.degree := by
  -- Each factor already lies in the corresponding ideal power, so the full product lands in the
  -- total-degree power after normalizing the product of powers.
  have hprod :
      (∏ i : Fin rs.length, rs.get i ^ e i) ∈
        ∏ i : Fin rs.length, (Ideal.ofList rs) ^ e i := by
    refine Ideal.prod_mem_prod ?_
    intro i hi
    exact Ideal.pow_mem_pow
      (Ideal.subset_span (by simpa using List.getElem_mem rs i))
      (e i)
  simpa [Finsupp.degree_eq_sum, Finset.prod_pow_eq_pow_sum] using hprod

/-- Helper for Lemma 10.69.2: a homogeneous weighted monomial term of total degree `n` lies in the
`n`th filtration stage. -/
private theorem ofList_monomial_weight_smul_mem_of_degree
    (rs : List R) (n : ℕ) (m : M) (e : Fin rs.length →₀ ℕ) (hdeg : e.degree = n) :
    (∏ i : Fin rs.length, rs.get i ^ e i) • m ∈
      idealAssociatedGradedStage (Ideal.ofList rs) M n := by
  -- Rewrite the stage as `J ^ n • ⊤` and combine monomial-weight membership with the trivial
  -- membership of `m` in the top submodule.
  simpa [idealAssociatedGradedStage, hdeg] using
    (Submodule.smul_mem_smul
      (ofList_monomial_weight_mem_pow rs e)
      (by simp : m ∈ (⊤ : Submodule R M)))

/-- Helper for Lemma 10.69.2: reinserting the degree-`n` component of a monomial image keeps the
same image exactly in degree `n` and vanishes in every other degree. -/
private theorem quasiRegularSequenceAssociatedGradedMap_tmul_monomial_eq_lof
    {rs : List R} (m : M) (e : Fin rs.length →₀ ℕ) :
    let J : Ideal R := Ideal.ofList rs
    quasiRegularSequenceAssociatedGradedMap M rs
      (((Submodule.Quotient.mk m : M ⧸ (J • (⊤ : Submodule R M))) ⊗ₜ[R ⧸ J]
        MvPolynomial.monomial e (1 : R ⧸ J))) =
      DirectSum.lof (R ⧸ J) ℕ (idealAssociatedGradedPiece J M) e.degree
        (Submodule.Quotient.mk
          (⟨(∏ i : Fin rs.length, rs.get i ^ e i) • m,
            ofList_monomial_weight_smul_mem_of_degree (M := M) rs e.degree m e rfl⟩ :
            idealAssociatedGradedStage J M e.degree)) := by
  -- Route correction: instead of rebuilding the owner transport chain here, reuse the imported
  -- `10.69.0.1` computation on the source commutation map, the auxiliary base-change lift, the
  -- direct-sum identification, and the textbook quotient-piece comparison.
  dsimp [quasiRegularSequenceAssociatedGradedMap]
  have hcomm :=
    (chap10_69_0_1_private%"quasiRegularSequenceAssociatedGradedSourceComm_tmul")
      (N := M) (rs := rs) m e
  have haux :=
    (chap10_69_0_1_private%"quasiRegularSequenceAssociatedGradedMapAux_tmul_monomial")
      (N := M) (rs := rs) m e
  let z :=
    (chap10_69_0_1_private%"quasiRegularAssociatedGradedInternalMonomialClass")
      (M := M) rs m e
  have hlof :=
    (chap10_69_0_1_private%"quasiRegularAssociatedGradedAddEquiv_lof")
      (N := M) (rs := rs) e.degree z
  have hlof' :
      ((chap10_69_0_1_private%"quasiRegularAssociatedGradedAddEquiv")
          (rs := rs) (M := M)).symm
        (DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
          ((chap10_69_0_1_private%"quasiRegularAssociatedGradedInternalPiece")
            (M := M) rs) e.degree z) =
      DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
        (idealAssociatedGradedPiece (Ideal.ofList rs) M) e.degree
        (((chap10_69_0_1_private%"quasiRegularAssociatedGradedInternalPieceEquiv")
          (rs := rs) (M := M) e.degree) z) := by
    simpa [z] using hlof
  have hpiece :=
    (chap10_69_0_1_private%"quasiRegularAssociatedGradedInternalPieceEquiv_monomialClass")
      (N := M) (rs := rs) m e
  -- Each owner-level rewrite now lands exactly on the textbook degree-`e.degree` class.
  rw [hcomm, haux, hlof', hpiece]
  rfl

/-- Helper for Lemma 10.69.2: reinserting the degree-`n` component of a monomial image keeps the
same image exactly in degree `n` and vanishes in every other degree. -/
private theorem lof_component_quasiRegularSequenceAssociatedGradedMap_tmul_monomial_eq
    {rs : List R} (n : ℕ) (m : M) (e : Fin rs.length →₀ ℕ) :
    let J : Ideal R := Ideal.ofList rs
    let term :
        (M ⧸ (J • (⊤ : Submodule R M))) ⊗[R ⧸ J]
          MvPolynomial (Fin rs.length) (R ⧸ J) :=
      ((Submodule.Quotient.mk m : M ⧸ (J • (⊤ : Submodule R M))) ⊗ₜ[R ⧸ J]
        MvPolynomial.monomial e (1 : R ⧸ J))
    let image := quasiRegularSequenceAssociatedGradedMap M rs term
    let componentN := DirectSum.component (R ⧸ J) ℕ (idealAssociatedGradedPiece J M) n
    DirectSum.lof (R ⧸ J) ℕ (idealAssociatedGradedPiece J M) n (componentN image) =
      if e.degree = n then image else 0 := by
  dsimp
  have hmon :=
    quasiRegularSequenceAssociatedGradedMap_tmul_monomial_eq_lof
      (M := M) (rs := rs) m e
  dsimp at hmon
  -- Normalize the monomial image to a single homogeneous `DirectSum.lof` term and then project
  -- back to degree `n`.
  by_cases hdeg : e.degree = n
  · subst n
    rw [hmon]
    simp
  · have hcomponent :
        DirectSum.component (R ⧸ Ideal.ofList rs) ℕ
          (idealAssociatedGradedPiece (Ideal.ofList rs) M) n
          (quasiRegularSequenceAssociatedGradedMap M rs
            ((Submodule.Quotient.mk m :
                M ⧸ ((Ideal.ofList rs) • (⊤ : Submodule R M))) ⊗ₜ[
                  R ⧸ Ideal.ofList rs]
              MvPolynomial.monomial e
                (1 : R ⧸ Ideal.ofList rs))) = 0 := by
      -- The off-degree component already vanishes after projecting the normalized monomial image.
      calc
        DirectSum.component (R ⧸ Ideal.ofList rs) ℕ
            (idealAssociatedGradedPiece (Ideal.ofList rs) M) n
            (quasiRegularSequenceAssociatedGradedMap M rs
              ((Submodule.Quotient.mk m :
                  M ⧸ ((Ideal.ofList rs) • (⊤ : Submodule R M))) ⊗ₜ[
                    R ⧸ Ideal.ofList rs]
                MvPolynomial.monomial e
                  (1 : R ⧸ Ideal.ofList rs))) =
          DirectSum.component (R ⧸ Ideal.ofList rs) ℕ
            (idealAssociatedGradedPiece (Ideal.ofList rs) M) n
            ((DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
              (idealAssociatedGradedPiece (Ideal.ofList rs) M) e.degree)
              (Submodule.Quotient.mk
                (⟨(∏ i : Fin rs.length, rs.get i ^ e i) • m,
                  ofList_monomial_weight_smul_mem_of_degree
                    (M := M) rs e.degree m e rfl⟩ :
                  idealAssociatedGradedStage (Ideal.ofList rs) M e.degree))) := by
                simpa using congrArg
                  (DirectSum.component (R ⧸ Ideal.ofList rs) ℕ
                    (idealAssociatedGradedPiece (Ideal.ofList rs) M) n)
                  hmon
        _ = 0 := by
          simp [DirectSum.component.of, hdeg]
    simp [hdeg, hcomponent]

/-- Helper for Lemma 10.69.2: the degree-`n` component of a monomial image vanishes away from total
degree `n`. -/
private theorem component_quasiRegularSequenceAssociatedGradedMap_tmul_monomial_eq_zero_of_ne
    {rs : List R} {n : ℕ} (m : M) (e : Fin rs.length →₀ ℕ) (h : e.degree ≠ n) :
    let J : Ideal R := Ideal.ofList rs
    let term :
        (M ⧸ (J • (⊤ : Submodule R M))) ⊗[R ⧸ J]
          MvPolynomial (Fin rs.length) (R ⧸ J) :=
      ((Submodule.Quotient.mk m : M ⧸ (J • (⊤ : Submodule R M))) ⊗ₜ[R ⧸ J]
        MvPolynomial.monomial e (1 : R ⧸ J))
    let componentN := DirectSum.component (R ⧸ J) ℕ (idealAssociatedGradedPiece J M) n
    componentN (quasiRegularSequenceAssociatedGradedMap M rs term) = 0 := by
  dsimp
  have hmon :=
    quasiRegularSequenceAssociatedGradedMap_tmul_monomial_eq_lof
      (M := M) (rs := rs) m e
  dsimp at hmon
  -- After the monomial image is identified with a single `DirectSum.lof` term, the wrong-degree
  -- component vanishes by `DirectSum.component.of` with `e.degree ≠ n`.
  calc
    DirectSum.component (R ⧸ Ideal.ofList rs) ℕ
        (idealAssociatedGradedPiece (Ideal.ofList rs) M) n
        (quasiRegularSequenceAssociatedGradedMap M rs
          ((Submodule.Quotient.mk m :
              M ⧸ ((Ideal.ofList rs) • (⊤ : Submodule R M))) ⊗ₜ[
                R ⧸ Ideal.ofList rs]
            MvPolynomial.monomial e
              (1 : R ⧸ Ideal.ofList rs))) =
      DirectSum.component (R ⧸ Ideal.ofList rs) ℕ
        (idealAssociatedGradedPiece (Ideal.ofList rs) M) n
        ((DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
          (idealAssociatedGradedPiece (Ideal.ofList rs) M) e.degree)
          (Submodule.Quotient.mk
            (⟨(∏ i : Fin rs.length, rs.get i ^ e i) • m,
              ofList_monomial_weight_smul_mem_of_degree
                (M := M) rs e.degree m e rfl⟩ :
              idealAssociatedGradedStage (Ideal.ofList rs) M e.degree))) := by
            simpa using congrArg
              (DirectSum.component (R ⧸ Ideal.ofList rs) ℕ
                (idealAssociatedGradedPiece (Ideal.ofList rs) M) n)
              hmon
    _ = 0 := by
      simp [DirectSum.component.of, h]

/-- Helper for Lemma 10.69.2: projecting a monomial kernel relation to one fixed total degree
keeps a kernel relation. -/
private theorem kernel_family_split_by_degree
    {rs : List R} {a : (Fin rs.length →₀ ℕ) →₀ M} (n : ℕ)
    (hker :
      quasiRegularSequenceAssociatedGradedMap M rs
        (a.sum fun e m ↦
          ((Submodule.Quotient.mk m :
              M ⧸ ((Ideal.ofList rs) • (⊤ : Submodule R M))) ⊗ₜ[R ⧸ Ideal.ofList rs]
            MvPolynomial.monomial e (1 : R ⧸ Ideal.ofList rs))) = 0) :
    quasiRegularSequenceAssociatedGradedMap M rs
      ((a.filter fun e ↦ e.degree = n).sum fun e m ↦
        ((Submodule.Quotient.mk m :
            M ⧸ ((Ideal.ofList rs) • (⊤ : Submodule R M))) ⊗ₜ[R ⧸ Ideal.ofList rs]
          MvPolynomial.monomial e (1 : R ⧸ Ideal.ofList rs))) = 0 := by
  let J : Ideal R := Ideal.ofList rs
  let fullSource :=
    Finset.sum a.support fun e ↦
      ((Submodule.Quotient.mk (a e) : M ⧸ (J • (⊤ : Submodule R M))) ⊗ₜ[R ⧸ J]
        MvPolynomial.monomial e (1 : R ⧸ J))
  let degreeSource :=
    Finset.sum (a.support.filter fun e ↦ e.degree = n) fun e ↦
      ((Submodule.Quotient.mk (a e) : M ⧸ (J • (⊤ : Submodule R M))) ⊗ₜ[R ⧸ J]
        MvPolynomial.monomial e (1 : R ⧸ J))
  let componentN :=
    DirectSum.component (R ⧸ J) ℕ (idealAssociatedGradedPiece J M) n
  -- Rewrite the kernel relation into support-indexed sums so the degree slice can be projected
  -- termwise, exactly as in the quotient-tail model.
  rw [monomial_tensor_family_sum_eq_support_sum (rs := rs) a] at hker
  rw [monomial_tensor_filtered_sum_eq_support_filter_sum (rs := rs) a n]
  have hdegree :
      quasiRegularSequenceAssociatedGradedMap M rs degreeSource =
        DirectSum.lof (R ⧸ J) ℕ (idealAssociatedGradedPiece J M) n
          (componentN
            (quasiRegularSequenceAssociatedGradedMap M rs fullSource)) := by
    let filteredSupport := a.support.filter (fun e ↦ e.degree = n)
    have hfilter :
        quasiRegularSequenceAssociatedGradedMap M rs degreeSource =
          Finset.sum filteredSupport fun e ↦
            quasiRegularSequenceAssociatedGradedMap M rs
              ((Submodule.Quotient.mk (a e) : M ⧸ (J • (⊤ : Submodule R M))) ⊗ₜ[R ⧸ J]
                MvPolynomial.monomial e (1 : R ⧸ J)) := by
      simp [degreeSource, filteredSupport, map_sum]
    have hreinsert :
        Finset.sum filteredSupport (fun e ↦
          quasiRegularSequenceAssociatedGradedMap M rs
            ((Submodule.Quotient.mk (a e) : M ⧸ (J • (⊤ : Submodule R M))) ⊗ₜ[R ⧸ J]
              MvPolynomial.monomial e (1 : R ⧸ J))) =
          Finset.sum filteredSupport (fun e ↦
            DirectSum.lof (R ⧸ J) ℕ (idealAssociatedGradedPiece J M) n
              (componentN
                (quasiRegularSequenceAssociatedGradedMap M rs
                  ((Submodule.Quotient.mk (a e) : M ⧸ (J • (⊤ : Submodule R M))) ⊗ₜ[R ⧸ J]
                    MvPolynomial.monomial e (1 : R ⧸ J))))) := by
      refine Finset.sum_congr rfl ?_
      intro e he
      have hdeg : e.degree = n := by
        simpa [filteredSupport] using (Finset.mem_filter.mp he).2
      simpa [J, componentN, hdeg] using
        (lof_component_quasiRegularSequenceAssociatedGradedMap_tmul_monomial_eq
          (M := M) (rs := rs) n (a e) e).symm
    have hsum_lof :
        Finset.sum filteredSupport (fun e ↦
          DirectSum.lof (R ⧸ J) ℕ (idealAssociatedGradedPiece J M) n
            (componentN
              (quasiRegularSequenceAssociatedGradedMap M rs
                ((Submodule.Quotient.mk (a e) : M ⧸ (J • (⊤ : Submodule R M))) ⊗ₜ[R ⧸ J]
                  MvPolynomial.monomial e (1 : R ⧸ J))))) =
          DirectSum.lof (R ⧸ J) ℕ (idealAssociatedGradedPiece J M) n
            (Finset.sum filteredSupport fun e ↦
              componentN
                (quasiRegularSequenceAssociatedGradedMap M rs
                  ((Submodule.Quotient.mk (a e) : M ⧸ (J • (⊤ : Submodule R M))) ⊗ₜ[R ⧸ J]
                    MvPolynomial.monomial e (1 : R ⧸ J)))) := by
      simp [map_sum]
    have hcomponent_full :
        (Finset.sum filteredSupport (fun e ↦
          componentN
            (quasiRegularSequenceAssociatedGradedMap M rs
              ((Submodule.Quotient.mk (a e) : M ⧸ (J • (⊤ : Submodule R M))) ⊗ₜ[R ⧸ J]
                MvPolynomial.monomial e (1 : R ⧸ J)))) =
          componentN
            (quasiRegularSequenceAssociatedGradedMap M rs fullSource)) := by
      dsimp [filteredSupport]
      rw [Finset.sum_filter]
      have hfull_expand :
          componentN
              (quasiRegularSequenceAssociatedGradedMap M rs fullSource) =
            Finset.sum a.support (fun e ↦
              componentN
                (quasiRegularSequenceAssociatedGradedMap M rs
                  ((Submodule.Quotient.mk (a e) : M ⧸ (J • (⊤ : Submodule R M))) ⊗ₜ[R ⧸ J]
                    MvPolynomial.monomial e (1 : R ⧸ J)))) := by
        simp [fullSource, map_sum]
      rw [hfull_expand]
      refine Finset.sum_congr rfl ?_
      intro e he
      by_cases hdeg : e.degree = n
      · simp [hdeg]
      · simp [hdeg, J, componentN,
          component_quasiRegularSequenceAssociatedGradedMap_tmul_monomial_eq_zero_of_ne
            (M := M) (rs := rs) (m := a e) (e := e) hdeg]
    exact hfilter.trans <| hreinsert.trans <| hsum_lof.trans <| by rw [hcomponent_full]
  -- The `n`-component of a zero relation is zero, so the degree slice is also zero.
  have hker_full :
      quasiRegularSequenceAssociatedGradedMap M rs fullSource = 0 := by
    simpa [fullSource] using hker
  have hslice : quasiRegularSequenceAssociatedGradedMap M rs degreeSource = 0 := by
    rw [hdegree, hker_full]
    simp [componentN]
  simpa [degreeSource] using hslice

/-- Helper for Lemma 10.69.2: if every coefficient lies in `Ideal.ofList rs • ⊤`, then the
corresponding source tensor sum is already zero. -/
private theorem source_tensor_sum_eq_zero_of_coeff_mem_ideal
    {rs : List R} {a : (Fin rs.length →₀ ℕ) →₀ M}
    (hcoeff :
      ∀ e ∈ a.support, a e ∈ Ideal.ofList rs • (⊤ : Submodule R M)) :
    (a.sum fun e m ↦
        ((Submodule.Quotient.mk m :
            M ⧸ ((Ideal.ofList rs) • (⊤ : Submodule R M))) ⊗ₜ[R ⧸ Ideal.ofList rs]
          MvPolynomial.monomial e (1 : R ⧸ Ideal.ofList rs))) = 0 := by
  classical
  -- Each simple tensor vanishes because its quotient coefficient is already zero.
  rw [Finsupp.sum]
  refine Finset.sum_eq_zero ?_
  intro e he
  have hmk :
      (Submodule.Quotient.mk (a e) :
        M ⧸ ((Ideal.ofList rs) • (⊤ : Submodule R M))) = 0 := by
    exact (Submodule.Quotient.mk_eq_zero _).2 (hcoeff e he)
  simp [hmk]

/-- Helper for Lemma 10.69.2: the prefix ideal submodule is contained in the snoc ideal
submodule. -/
private theorem prefix_ideal_smul_le_snoc_ideal_smul (fs : List R) (r : R) :
    Ideal.ofList fs • (⊤ : Submodule R M) ≤
      Ideal.ofList (fs ++ [r]) • (⊤ : Submodule R M) := by
  -- Appending one generator enlarges the ideal, so the corresponding smul-top submodule grows.
  rw [Ideal.ofList_append]
  exact Submodule.smul_mono_left le_sup_left

/-- Helper for Lemma 10.69.2: after splitting `rs = fs ++ [r]`, a power of the last regular
element can be cancelled modulo the prefix ideal. -/
private theorem last_exponent_coeff_mem_prefix_ideal_of_pow_smul_mem
    {fs : List R} {r : R} (hreg : IsRegular M (fs ++ [r])) (l : ℕ) {m : M}
    (hmem : (r ^ l) • m ∈ Ideal.ofList fs • (⊤ : Submodule R M)) :
    m ∈ Ideal.ofList fs • (⊤ : Submodule R M) := by
  let N : Submodule R M := Ideal.ofList fs • (⊤ : Submodule R M)
  by_cases hl : l = 0
  · -- For exponent `0` there is nothing to cancel: the hypothesis is already the target.
    subst hl
    simpa [N] using hmem
  · -- Pass to the quotient by the prefix ideal and use regularity of the snoc tail there.
    have htail_reg :
        IsRegular (M ⧸ N) [r] :=
      isRegular_singleton_on_prefix_quotient_of_isRegular_append_singleton
        (M := M) (rs := fs) (r := r) hreg
    have hr :
        IsSMulRegular (M ⧸ N) r := by
      exact ((isRegular_cons_iff (M := M ⧸ N) r []).mp htail_reg).1
    have hpow :
        IsSMulRegular (M ⧸ N) (r ^ l) :=
      IsSMulRegular.pow (M := M ⧸ N) l hr
    -- The quotient criterion for `IsSMulRegular` is exactly the desired cancellation statement.
    exact
      (isSMulRegular_quotient_iff_mem_of_smul_mem (M := M) (N := N) (r := r ^ l)).mp
        hpow m <| by
          simpa [N] using hmem

/-- Helper for Lemma 10.69.2: append one final exponent coordinate using the `Fin.snoc`
description of exponents. -/
private noncomputable def snoc_exponent {α : Type*} {fs : List α}
    (e : Fin fs.length →₀ ℕ) (l : ℕ) : Fin (fs.length + 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (Fin.snoc e l)

/-- Helper for Lemma 10.69.2: the appended exponent agrees with the prefix exponent on
`castSucc` coordinates. -/
private theorem snoc_exponent_castSucc {α : Type*} {fs : List α}
    (e : Fin fs.length →₀ ℕ) (l : ℕ) (i : Fin fs.length) :
    snoc_exponent (fs := fs) e l i.castSucc = e i := by
  -- Read the appended exponent through the finite-function equivalence, then evaluate the snoc.
  simp [snoc_exponent, Fin.snoc_castSucc]

/-- Helper for Lemma 10.69.2: the appended exponent has last coordinate equal to the chosen tail
value. -/
private theorem snoc_exponent_last {α : Type*} {fs : List α}
    (e : Fin fs.length →₀ ℕ) (l : ℕ) :
    snoc_exponent (fs := fs) e l (Fin.last fs.length) = l := by
  -- The last coordinate is exactly the snoc tail entry.
  simp [snoc_exponent, Fin.snoc_last]

/-- Helper for Lemma 10.69.2: the appended list `fs ++ [r]` has length `fs.length + 1`. -/
private theorem snoc_length_eq {α : Type*} (fs : List α) (r : α) :
    (fs ++ [r]).length = fs.length + 1 := by
  simp

/-- Helper for Lemma 10.69.2: cast the standard snoc index type `Fin (fs.length + 1)` to the
index type of the appended list `fs ++ [r]`. -/
private abbrev snoc_index_cast {α : Type*} (fs : List α) (r : α) :
    Fin (fs.length + 1) → Fin (fs ++ [r]).length :=
  Fin.cast (snoc_length_eq fs r).symm

/-- Helper for Lemma 10.69.2: the last coordinate index of `fs ++ [r]`, expressed through the
standard `Fin.last fs.length` on the snoc presentation. -/
private abbrev snoc_last_index {α : Type*} (fs : List α) (r : α) :
    Fin (fs ++ [r]).length :=
  snoc_index_cast fs r (Fin.last fs.length)

/-- Helper for Lemma 10.69.2: fixing the last coordinate makes `snoc_exponent` injective on
prefix exponents. -/
private theorem snoc_exponent_injective {α : Type*} {fs : List α} (l : ℕ) :
    Function.Injective (fun e : Fin fs.length →₀ ℕ ↦ snoc_exponent (fs := fs) e l) := by
  intro e₁ e₂ h
  ext i
  -- Compare the two appended exponents on the prefix coordinates.
  have hcast :
      snoc_exponent (fs := fs) e₁ l i.castSucc =
        snoc_exponent (fs := fs) e₂ l i.castSucc := by
    exact congrArg (fun f : Fin (fs.length + 1) →₀ ℕ ↦ f i.castSucc) h
  simpa [snoc_exponent_castSucc] using hcast

/-- Helper for Lemma 10.69.2: appending a last coordinate raises total degree by that coordinate.
-/
private theorem snoc_exponent_degree {α : Type*} {fs : List α}
    (e : Fin fs.length →₀ ℕ) (l : ℕ) :
    (snoc_exponent (fs := fs) e l).degree = e.degree + l := by
  -- Expand both degrees as sums over coordinates and split the appended finite index.
  rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum, Fin.sum_univ_castSucc]
  simp [snoc_exponent, Fin.snoc_castSucc, Fin.snoc_last, Nat.add_comm]

/-- Helper for Lemma 10.69.2: the monomial weight of an appended exponent is the prefix monomial
weight times the final generator power. -/
private theorem snoc_exponent_weight {fs : List R} (r : R)
    (e : Fin fs.length →₀ ℕ) (l : ℕ) :
    (∏ i : Fin (fs.length + 1),
        (fs ++ [r]).get (snoc_index_cast fs r i) ^ snoc_exponent (fs := fs) e l i) =
      (∏ i : Fin fs.length, fs.get i ^ e i) * r ^ l := by
  -- Split the appended product into prefix and last factors, then simplify each coordinate.
  rw [Fin.prod_univ_castSucc]
  simp [snoc_index_cast, snoc_length_eq, snoc_exponent_castSucc, snoc_exponent_last]

/-- Helper for Lemma 10.69.2: the exact-last-coordinate slice is the filtered family pulled back
along `snoc_exponent`. -/
private noncomputable def last_exponent_slice {β : Type*} {fs : List β} {α : Type*} [Zero α]
    (a : (Fin (fs.length + 1) →₀ ℕ) →₀ α) (l : ℕ) :
    (Fin fs.length →₀ ℕ) →₀ α :=
  (a.filter fun e ↦ e (Fin.last fs.length) = l).comapDomain
    (fun e ↦ snoc_exponent (fs := fs) e l)
    ((snoc_exponent_injective (fs := fs) l).injOn)

/-- Helper for Lemma 10.69.2: evaluating the pulled-back exact-last-coordinate slice at a prefix
exponent recovers the original filtered coefficient. -/
private theorem last_exponent_slice_apply {β : Type*} {fs : List β} {α : Type*} [Zero α]
    (a : (Fin (fs.length + 1) →₀ ℕ) →₀ α) (l : ℕ) (e : Fin fs.length →₀ ℕ) :
    last_exponent_slice (fs := fs) a l e =
      (a.filter fun d ↦ d (Fin.last fs.length) = l) (snoc_exponent (fs := fs) e l) := by
  -- `comapDomain` turns the full-family slice into the prefix-indexed family expected later.
  rw [last_exponent_slice, Finsupp.comapDomain_apply]

/-- Helper for Lemma 10.69.2: the exact-last-coordinate slice of a homogeneous snoc family is
homogeneous of the complementary prefix degree. -/
private theorem last_exponent_slice_homogeneous
    {fs : List R} {a : (Fin (fs.length + 1) →₀ ℕ) →₀ M} {n l : ℕ}
    (hdeg : ∀ e ∈ a.support, e.degree = n) :
    ∀ d ∈ (last_exponent_slice (fs := fs) a l).support, d.degree = n - l := by
  intro d hd
  have hslice :
      snoc_exponent (fs := fs) d l ∈
        (a.filter fun e ↦ e (Fin.last fs.length) = l).support := by
    rw [Finsupp.mem_support_iff] at hd ⊢
    simpa [last_exponent_slice_apply] using hd
  have hsupport :
      snoc_exponent (fs := fs) d l ∈ a.support := by
    rw [Finsupp.support_filter] at hslice
    exact (Finset.mem_filter.mp hslice).1
  have hsnoc_degree :
      (snoc_exponent (fs := fs) d l).degree = n := hdeg _ hsupport
  have hsum : d.degree + l = n := by
    simpa [snoc_exponent_degree] using hsnoc_degree
  exact Nat.eq_sub_of_add_eq hsum

/-- Helper for Lemma 10.69.2: restricting an exponent on `Fin (fs.length + 1)` to the prefix
coordinates and then reattaching the recorded last coordinate recovers the original exponent. -/
private theorem snoc_exponent_comap_castSucc_eq {fs : List R}
    (e : Fin (fs.length + 1) →₀ ℕ) {l : ℕ} (hl : e (Fin.last fs.length) = l) :
    snoc_exponent
      (fs := fs)
      (e.comapDomain Fin.castSucc ((Fin.castSucc_injective _).injOn)) l = e := by
  -- Compare the reconstructed snoc exponent on the prefix coordinates and on the final coordinate.
  ext i
  cases i using Fin.lastCases <;> simp [snoc_exponent, hl, Finsupp.comapDomain_apply]

/-- Helper for Lemma 10.69.2: the exact-`l` last-exponent slice carries exactly the weighted part
of the support sum with final exponent equal to `l`. -/
private theorem exact_last_exponent_weighted_sum_eq_slice_sum
    {fs : List R} {r : R} {a : (Fin (fs.length + 1) →₀ ℕ) →₀ M} (l : ℕ) :
    ((a.filter fun e ↦ e (Fin.last fs.length) = l).sum fun e m ↦
      (∏ i : Fin (fs.length + 1), (fs ++ [r]).get (snoc_index_cast fs r i) ^ e i) • m) =
        ((last_exponent_slice (fs := fs) a l).sum fun d m ↦
          (∏ i : Fin fs.length, fs.get i ^ d i) • ((r ^ l) • m)) := by
  let exactFamily : (Fin (fs.length + 1) →₀ ℕ) →₀ M :=
    a.filter fun e ↦ e (Fin.last fs.length) = l
  have hbij :
      Set.BijOn
        (fun d : Fin fs.length →₀ ℕ ↦ snoc_exponent (fs := fs) d l)
        ((fun d : Fin fs.length →₀ ℕ ↦ snoc_exponent (fs := fs) d l) ⁻¹'
          ↑exactFamily.support)
        ↑exactFamily.support := by
    refine ⟨?_, (snoc_exponent_injective (fs := fs) l).injOn, ?_⟩
    · intro d hd
      exact hd
    · intro e he
      have hl :
          e (Fin.last fs.length) = l := by
        change e ∈ (a.filter fun e ↦ e (Fin.last fs.length) = l).support at he
        rw [Finsupp.support_filter] at he
        exact (Finset.mem_filter.mp he).2
      refine ⟨e.comapDomain Fin.castSucc ((Fin.castSucc_injective _).injOn), ?_, ?_⟩
      · simpa [Set.mem_preimage, snoc_exponent_comap_castSucc_eq (fs := fs) e hl]
          using he
      · exact snoc_exponent_comap_castSucc_eq (fs := fs) e hl
  have hsum :
      (last_exponent_slice (fs := fs) a l).sum
          (fun d m ↦
            (∏ i : Fin (fs.length + 1),
                (fs ++ [r]).get (snoc_index_cast fs r i) ^
                  snoc_exponent (fs := fs) d l i) • m) =
        exactFamily.sum
          (fun e m ↦
            (∏ i : Fin (fs.length + 1), (fs ++ [r]).get (snoc_index_cast fs r i) ^ e i) • m) := by
    -- `last_exponent_slice` is exactly the `comapDomain` reindexing of the exact-`l` family.
    simpa [last_exponent_slice, exactFamily] using
      (Finsupp.sum_comapDomain
        (f := fun d ↦ snoc_exponent (fs := fs) d l)
        (l := exactFamily)
        (g := fun e m ↦
          (∏ i : Fin (fs.length + 1), (fs ++ [r]).get (snoc_index_cast fs r i) ^ e i) • m)
        hbij)
  -- Normalize the appended monomial weight to the prefix weight times `r ^ l`.
  calc
    exactFamily.sum
        (fun e m ↦
          (∏ i : Fin (fs.length + 1), (fs ++ [r]).get (snoc_index_cast fs r i) ^ e i) • m) =
      (last_exponent_slice (fs := fs) a l).sum
        (fun d m ↦
          (∏ i : Fin (fs.length + 1),
              (fs ++ [r]).get (snoc_index_cast fs r i) ^
                snoc_exponent (fs := fs) d l i) • m) := hsum.symm
    _ =
      (last_exponent_slice (fs := fs) a l).sum fun d m ↦
        (∏ i : Fin fs.length, fs.get i ^ d i) • ((r ^ l) • m) := by
          rw [Finsupp.sum]
          refine Finset.sum_congr rfl ?_
          intro d hd
          rw [snoc_exponent_weight (fs := fs) (r := r) d l]
          simp [smul_smul]

/-- Helper for Lemma 10.69.2: truncating by the last exponent splits the weighted sum into the
exact-`l` slice and the strict-lower-last-exponent remainder. -/
private theorem truncated_last_exponent_weighted_sum_split
    {fs : List R} {r : R} {a : (Fin (fs.length + 1) →₀ ℕ) →₀ M} (l : ℕ) :
    let atrunc : (Fin (fs.length + 1) →₀ ℕ) →₀ M :=
      a.filter fun e ↦ e (Fin.last fs.length) ≤ l
    let lower : (Fin (fs.length + 1) →₀ ℕ) →₀ M :=
      atrunc.filter fun e ↦ e (Fin.last fs.length) < l
    (atrunc.sum fun e m ↦
      (∏ i : Fin (fs.length + 1), (fs ++ [r]).get (snoc_index_cast fs r i) ^ e i) • m) =
        ((last_exponent_slice (fs := fs) atrunc l).sum fun d m ↦
          (∏ i : Fin fs.length, fs.get i ^ d i) • ((r ^ l) • m)) +
        (lower.sum fun e m ↦
          (∏ i : Fin (fs.length + 1), (fs ++ [r]).get (snoc_index_cast fs r i) ^ e i) • m) := by
  let atrunc : (Fin (fs.length + 1) →₀ ℕ) →₀ M :=
    a.filter fun e ↦ e (Fin.last fs.length) ≤ l
  let exactFamily : (Fin (fs.length + 1) →₀ ℕ) →₀ M :=
    atrunc.filter fun e ↦ e (Fin.last fs.length) = l
  let lower : (Fin (fs.length + 1) →₀ ℕ) →₀ M :=
    atrunc.filter fun e ↦ e (Fin.last fs.length) < l
  have hneg_eq_lower :
      atrunc.filter (fun e ↦ ¬ e (Fin.last fs.length) = l) = lower := by
    -- On the `≤ l` truncation, being different from `l` is equivalent to being strictly below `l`.
    ext e
    by_cases hle : e (Fin.last fs.length) ≤ l
    · by_cases hEq : e (Fin.last fs.length) = l
      · simp [atrunc, lower, hle, hEq]
      · have hlt : e (Fin.last fs.length) < l := Nat.lt_of_le_of_ne hle fun h' ↦ hEq h'
        simp [atrunc, lower, hle, hEq, hlt]
    · have hzero : atrunc e = 0 := by
        simp [atrunc, hle]
      rw [show (atrunc.filter (fun e ↦ ¬ e (Fin.last fs.length) = l)) e = 0 by
        rw [Finsupp.filter_apply]
        by_cases hneq : ¬ e (Fin.last fs.length) = l
        · simp [hneq, hzero]
        · simp [hneq]]
      by_cases hlt : e (Fin.last fs.length) < l
      · simp [lower, hlt, hzero]
      · simp [lower, hlt]
  have hsplit_family : atrunc = exactFamily + lower := by
    -- Split the truncated family into the exact-`l` slice and its strict-lower complement.
    calc
      atrunc = atrunc.filter (fun e ↦ e (Fin.last fs.length) = l) +
          atrunc.filter (fun e ↦ ¬ e (Fin.last fs.length) = l) := by
            simpa [exactFamily] using
              (Finsupp.filter_pos_add_filter_neg
                (f := atrunc) (p := fun e ↦ e (Fin.last fs.length) = l)).symm
      _ = exactFamily + lower := by rw [hneg_eq_lower]
  have hsum_split :
      (exactFamily + lower).sum
          (fun e m ↦
            (∏ i : Fin (fs.length + 1), (fs ++ [r]).get (snoc_index_cast fs r i) ^ e i) • m) =
        exactFamily.sum
            (fun e m ↦
              (∏ i : Fin (fs.length + 1), (fs ++ [r]).get (snoc_index_cast fs r i) ^ e i) • m) +
          lower.sum
            (fun e m ↦
              (∏ i : Fin (fs.length + 1), (fs ++ [r]).get (snoc_index_cast fs r i) ^ e i) • m) := by
    -- The weighted sum is additive in the coefficient family.
    rw [Finsupp.sum_add_index] <;> simp [smul_add]
  -- Replace the exact slice by its prefix-indexed `last_exponent_slice` description.
  calc
    (atrunc.sum fun e m ↦
      (∏ i : Fin (fs.length + 1), (fs ++ [r]).get (snoc_index_cast fs r i) ^ e i) • m) =
        ((exactFamily + lower).sum fun e m ↦
          (∏ i : Fin (fs.length + 1), (fs ++ [r]).get (snoc_index_cast fs r i) ^ e i) • m) := by
            rw [hsplit_family]
    _ =
        exactFamily.sum
            (fun e m ↦
              (∏ i : Fin (fs.length + 1), (fs ++ [r]).get (snoc_index_cast fs r i) ^ e i) • m) +
          lower.sum
            (fun e m ↦
              (∏ i : Fin (fs.length + 1), (fs ++ [r]).get (snoc_index_cast fs r i) ^ e i) • m) :=
          hsum_split
    _ =
        ((last_exponent_slice (fs := fs) atrunc l).sum fun d m ↦
          (∏ i : Fin fs.length, fs.get i ^ d i) • ((r ^ l) • m)) +
          lower.sum
            (fun e m ↦
              (∏ i : Fin (fs.length + 1), (fs ++ [r]).get (snoc_index_cast fs r i) ^ e i) • m) := by
          rw [exact_last_exponent_weighted_sum_eq_slice_sum (fs := fs) (r := r) (a := atrunc)
            (l := l)]

/-- Helper for Lemma 10.69.2: filtering a homogeneous family by a last-exponent bound preserves
the same total degree on the remaining support. -/
private theorem homogeneous_filter_last_exponent
    {fs : List R} {r : R} {a : (Fin (fs ++ [r]).length →₀ ℕ) →₀ M} {n l : ℕ}
    (hdeg : ∀ e ∈ a.support, e.degree = n) :
    ∀ e ∈ (a.filter fun d ↦ d (snoc_last_index fs r) ≤ l).support, e.degree = n := by
  intro e he
  -- The filtered support is a subset of the original support, so the original homogeneity applies.
  rw [Finsupp.support_filter] at he
  exact hdeg e (Finset.mem_filter.mp he).1

/-- Helper for Lemma 10.69.2: in a homogeneous family of total degree `n`, the last exponent is at
most `n`. -/
private theorem homogeneous_last_exponent_le_degree
    {fs : List R} {r : R} {a : (Fin (fs ++ [r]).length →₀ ℕ) →₀ M} {n : ℕ}
    (hdeg : ∀ e ∈ a.support, e.degree = n) :
    ∀ e ∈ a.support, e (snoc_last_index fs r) ≤ n := by
  intro e he
  -- Each coordinate is bounded by the total degree, and the homogeneous hypothesis identifies that
  -- total degree with the fixed value `n`.
  rw [← hdeg e he]
  exact Finsupp.le_degree (snoc_last_index fs r) e

/-- Helper for Lemma 10.69.2: once all coefficients with last exponent strictly larger than `l`
already lie in the snoc ideal, the family truncated to last exponent at most `l` still satisfies
the kernel relation. -/
private theorem kernel_family_truncate_last_exponent
    {fs : List R} {r : R} {a : (Fin (fs ++ [r]).length →₀ ℕ) →₀ M} (l : ℕ)
    (hker :
      quasiRegularSequenceAssociatedGradedMap M (fs ++ [r])
        (a.sum fun e m ↦
          ((Submodule.Quotient.mk m :
              M ⧸ ((Ideal.ofList (fs ++ [r])) • (⊤ : Submodule R M))) ⊗ₜ[
                R ⧸ Ideal.ofList (fs ++ [r])]
            MvPolynomial.monomial e
              (1 : R ⧸ Ideal.ofList (fs ++ [r])))) = 0)
    (hhigh :
      ∀ e ∈ a.support, l < e (snoc_last_index fs r) →
        a e ∈ Ideal.ofList (fs ++ [r]) • (⊤ : Submodule R M)) :
    quasiRegularSequenceAssociatedGradedMap M (fs ++ [r])
      ((a.filter fun e ↦ e (snoc_last_index fs r) ≤ l).sum fun e m ↦
        ((Submodule.Quotient.mk m :
            M ⧸ ((Ideal.ofList (fs ++ [r])) • (⊤ : Submodule R M))) ⊗ₜ[
              R ⧸ Ideal.ofList (fs ++ [r])]
          MvPolynomial.monomial e
            (1 : R ⧸ Ideal.ofList (fs ++ [r])))) = 0 := by
  classical
  let J : Ideal R := Ideal.ofList (fs ++ [r])
  let low : (Fin (fs ++ [r]).length →₀ ℕ) →₀ M :=
    a.filter fun e ↦ e (snoc_last_index fs r) ≤ l
  let high : (Fin (fs ++ [r]).length →₀ ℕ) →₀ M :=
    a.filter fun e ↦ ¬ e (snoc_last_index fs r) ≤ l
  let term :
      (Fin (fs ++ [r]).length →₀ ℕ) →
        M →
          (M ⧸ (J • (⊤ : Submodule R M))) ⊗[R ⧸ J]
            MvPolynomial (Fin (fs ++ [r]).length) (R ⧸ J) :=
    fun e m ↦
      ((Submodule.Quotient.mk m : M ⧸ (J • (⊤ : Submodule R M))) ⊗ₜ[R ⧸ J]
        MvPolynomial.monomial e (1 : R ⧸ J))
  have hsplit : low + high = a := by
    -- Split the family into the last-exponent-`≤ l` and last-exponent-`> l` slices.
    simpa [low, high, Nat.not_le] using
      (Finsupp.filter_pos_add_filter_neg
        (f := a) (p := fun e ↦ e (snoc_last_index fs r) ≤ l))
  have hhigh_coeff :
      ∀ e ∈ high.support, high e ∈ J • (⊤ : Submodule R M) := by
    intro e he
    change e ∈ (a.filter fun d ↦ ¬ d (snoc_last_index fs r) ≤ l).support at he
    rw [Finsupp.support_filter] at he
    obtain ⟨he_support, he_high⟩ := Finset.mem_filter.mp he
    have hlt : l < e (snoc_last_index fs r) := Nat.lt_of_not_ge he_high
    have hmem : a e ∈ J • (⊤ : Submodule R M) := by
      simpa [J] using hhigh e he_support hlt
    -- On the filtered support, the coefficient agrees with the original family.
    have hhigh_apply : high e = a e := by
      have : (a.filter fun d ↦ l < d (snoc_last_index fs r)) e = a e := by
        simp [hlt]
      simpa [high, Nat.not_le] using this
    rw [hhigh_apply]
    exact hmem
  have hhigh_zero : high.sum term = 0 := by
    -- The higher slices already vanish in the quotient source because all of their coefficients are
    -- in the defining ideal submodule.
    simpa [J, high, term] using
      source_tensor_sum_eq_zero_of_coeff_mem_ideal (M := M) (rs := fs ++ [r]) (a := high)
        hhigh_coeff
  have hsource_split : low.sum term + high.sum term = a.sum term := by
    -- The source tensor sum is additive in the coefficient family, so the support split lifts to a
    -- decomposition of the source term.
    rw [← Finsupp.sum_add_index' (h := term)]
    · simpa [hsplit]
    · intro e
      simp [term]
    · intro e m₁ m₂
      simpa [term] using
        TensorProduct.add_tmul (R := R ⧸ J)
          (Submodule.Quotient.mk m₁ : M ⧸ (J • (⊤ : Submodule R M)))
          (Submodule.Quotient.mk m₂ : M ⧸ (J • (⊤ : Submodule R M)))
          (MvPolynomial.monomial e (1 : R ⧸ J))
  have hmap_split :
      quasiRegularSequenceAssociatedGradedMap M (fs ++ [r]) (low.sum term) +
        quasiRegularSequenceAssociatedGradedMap M (fs ++ [r]) (high.sum term) = 0 := by
    -- Apply the associated-graded map to the source decomposition and use the original kernel
    -- relation.
    calc
      quasiRegularSequenceAssociatedGradedMap M (fs ++ [r]) (low.sum term) +
          quasiRegularSequenceAssociatedGradedMap M (fs ++ [r]) (high.sum term) =
        quasiRegularSequenceAssociatedGradedMap M (fs ++ [r]) (low.sum term + high.sum term) := by
            rw [map_add]
      _ = quasiRegularSequenceAssociatedGradedMap M (fs ++ [r]) (a.sum term) := by
            rw [hsource_split]
      _ = 0 := hker
  -- The high slice is already zero, so the truncated family still lies in the kernel.
  simpa [J, low, term, hhigh_zero] using hmap_split

/-- Helper for Lemma 10.69.2: the strict-lower-last-exponent remainder already lies in the
required prefix filtration stage. -/
private theorem lower_last_exponent_weighted_sum_mem_prefix_stage
    {fs : List R} {r : R} {a : (Fin (fs.length + 1) →₀ ℕ) →₀ M} {n l : ℕ}
    (hdeg : ∀ e ∈ a.support, e.degree = n) (hl : l ≤ n) :
    let atrunc : (Fin (fs.length + 1) →₀ ℕ) →₀ M :=
      a.filter fun e ↦ e (Fin.last fs.length) ≤ l
    let lower : (Fin (fs.length + 1) →₀ ℕ) →₀ M :=
      atrunc.filter fun e ↦ e (Fin.last fs.length) < l
    (lower.sum fun e m ↦
      (∏ i : Fin (fs.length + 1), (fs ++ [r]).get (snoc_index_cast fs r i) ^ e i) • m) ∈
        ((Ideal.ofList fs) ^ (n - l + 1)) • (⊤ : Submodule R M) := by
  let atrunc : (Fin (fs.length + 1) →₀ ℕ) →₀ M :=
    a.filter fun e ↦ e (Fin.last fs.length) ≤ l
  let lower : (Fin (fs.length + 1) →₀ ℕ) →₀ M :=
    atrunc.filter fun e ↦ e (Fin.last fs.length) < l
  -- Normalize every strict-lower support term to a prefix exponent and estimate it termwise in the
  -- prefix ideal powers.
  refine Submodule.sum_mem _ ?_
  intro e he
  change ((∏ i : Fin (fs.length + 1), (fs ++ [r]).get (snoc_index_cast fs r i) ^ e i) • lower e) ∈
    ((Ideal.ofList fs) ^ (n - l + 1)) • (⊤ : Submodule R M)
  have he_data : (a e ≠ 0 ∧ e (Fin.last fs.length) ≤ l) ∧ e (Fin.last fs.length) < l := by
    -- Expanding the two nested filters exposes the original support condition together with both
    -- last-exponent bounds.
    simpa [lower, atrunc, Finsupp.support_filter, Finsupp.mem_support_iff] using he
  have he_a : e ∈ a.support := Finsupp.mem_support_iff.mpr he_data.1.1
  have hk_le : e (Fin.last fs.length) ≤ l := he_data.1.2
  have hk_lt : e (Fin.last fs.length) < l := he_data.2
  let k : ℕ := e (Fin.last fs.length)
  let d : Fin fs.length →₀ ℕ :=
    e.comapDomain Fin.castSucc ((Fin.castSucc_injective _).injOn)
  have hsnoc :
      snoc_exponent (fs := fs) d k = e := by
    -- Reattach the recorded last coordinate after restricting to the prefix coordinates.
    simpa [d, k] using
      (snoc_exponent_comap_castSucc_eq (fs := fs) (e := e) (l := k) (by simp [k]))
  have hdeg_e : e.degree = n := hdeg e he_a
  have hk_le_n : k ≤ n := by
    -- Homogeneity bounds the last coordinate by the total degree.
    rw [show k = e (Fin.last fs.length) by rfl]
    rw [← hdeg_e]
    exact Finsupp.le_degree (Fin.last fs.length) e
  have hd_degree : d.degree = n - k := by
    -- The snoc degree formula identifies the prefix degree with the complementary amount.
    have hsnoc_degree : (snoc_exponent (fs := fs) d k).degree = n := by
      simpa [hsnoc] using hdeg_e
    have hsum : d.degree + k = n := by
      simpa [snoc_exponent_degree] using hsnoc_degree
    exact Nat.eq_sub_of_add_eq hsum
  have hk_lt' : k < l := by
    simpa [k] using hk_lt
  have hpow : n - l + 1 ≤ n - k := by
    omega
  have hterm_mem :
      ((∏ i : Fin fs.length, fs.get i ^ d i) • ((r ^ k) • lower e)) ∈
        ((Ideal.ofList fs) ^ (n - k)) • (⊤ : Submodule R M) := by
    -- The prefix monomial weight contributes the required ideal power, and the remaining factor is
    -- absorbed by the top submodule.
    have hweight_mem :
        (∏ i : Fin fs.length, fs.get i ^ d i) ∈ (Ideal.ofList fs) ^ (n - k) := by
      simpa [hd_degree] using ofList_monomial_weight_mem_pow (R := R) fs d
    exact Submodule.smul_mem_smul hweight_mem (by simp)
  have hweight :
      (∏ i : Fin (fs.length + 1), (fs ++ [r]).get (snoc_index_cast fs r i) ^ e i) =
        (∏ i : Fin fs.length, fs.get i ^ d i) * r ^ k := by
    -- Rewrite the snoc monomial weight as the prefix weight times the final generator power.
    simpa [d, k, hsnoc] using snoc_exponent_weight (fs := fs) (r := r) d k
  -- After normalizing the term, ideal-power monotonicity lowers the stage to `n - l + 1`.
  rw [hweight, mul_smul]
  exact (Submodule.smul_mono_left (Ideal.pow_le_pow_right hpow)) hterm_mem

/-- Helper for Lemma 10.69.2: once the truncated weighted sum is already known to lie in the
prefix stage, subtracting the strict-lower remainder isolates the exact-`l` slice in that same
stage. -/
private theorem last_exponent_slice_weighted_sum_mem_prefix_stage
    {fs : List R} {r : R} {a : (Fin (fs.length + 1) →₀ ℕ) →₀ M} {n l : ℕ}
    (hdeg : ∀ e ∈ a.support, e.degree = n) (hl : l ≤ n)
    (htrunc :
      let atrunc : (Fin (fs.length + 1) →₀ ℕ) →₀ M :=
        a.filter fun e ↦ e (Fin.last fs.length) ≤ l
      (atrunc.sum fun e m ↦
        (∏ i : Fin (fs.length + 1), (fs ++ [r]).get (snoc_index_cast fs r i) ^ e i) • m) ∈
          ((Ideal.ofList fs) ^ (n - l + 1)) • (⊤ : Submodule R M)) :
    let atrunc : (Fin (fs.length + 1) →₀ ℕ) →₀ M :=
      a.filter fun e ↦ e (Fin.last fs.length) ≤ l
    ((last_exponent_slice (fs := fs) atrunc l).sum fun d m ↦
      (∏ i : Fin fs.length, fs.get i ^ d i) • ((r ^ l) • m)) ∈
        ((Ideal.ofList fs) ^ (n - l + 1)) • (⊤ : Submodule R M) := by
  let atrunc : (Fin (fs.length + 1) →₀ ℕ) →₀ M :=
    a.filter fun e ↦ e (Fin.last fs.length) ≤ l
  let lower : (Fin (fs.length + 1) →₀ ℕ) →₀ M :=
    atrunc.filter fun e ↦ e (Fin.last fs.length) < l
  have hsplit :=
    truncated_last_exponent_weighted_sum_split (M := M) (fs := fs) (r := r) (a := a) (l := l)
  have hlower :
      (lower.sum fun e m ↦
        (∏ i : Fin (fs.length + 1), (fs ++ [r]).get (snoc_index_cast fs r i) ^ e i) • m) ∈
          ((Ideal.ofList fs) ^ (n - l + 1)) • (⊤ : Submodule R M) := by
    -- The lower-last-exponent remainder is already controlled termwise.
    simpa [atrunc, lower] using
      lower_last_exponent_weighted_sum_mem_prefix_stage
        (M := M) (fs := fs) (r := r) (a := a) (n := n) (l := l) hdeg hl
  have hsum :
      ((last_exponent_slice (fs := fs) atrunc l).sum fun d m ↦
        (∏ i : Fin fs.length, fs.get i ^ d i) • ((r ^ l) • m)) +
        (lower.sum fun e m ↦
          (∏ i : Fin (fs.length + 1), (fs ++ [r]).get (snoc_index_cast fs r i) ^ e i) • m) ∈
          ((Ideal.ofList fs) ^ (n - l + 1)) • (⊤ : Submodule R M) := by
    -- Rewrite the truncated stage hypothesis as the exact slice plus the lower remainder.
    have htrunc' :
      (atrunc.sum fun e m ↦
        (∏ i : Fin (fs.length + 1), (fs ++ [r]).get (snoc_index_cast fs r i) ^ e i) • m) ∈
          ((Ideal.ofList fs) ^ (n - l + 1)) • (⊤ : Submodule R M) := by
      simpa [atrunc] using htrunc
    convert htrunc' using 1
    symm
    exact hsplit
  -- Subtract the already-controlled lower remainder to isolate the exact slice.
  simpa [atrunc] using (Submodule.sub_mem _ hsum hlower)

/-- Helper for Lemma 10.69.2: the weighted support sum of a homogeneous family already lies in the
matching filtration stage. -/
private theorem weighted_support_sum_mem_stage_of_homogeneous
    {rs : List R} {n : ℕ} {a : (Fin rs.length →₀ ℕ) →₀ M}
    (hdeg : ∀ e ∈ a.support, e.degree = n) :
    (Finset.sum a.support fun e ↦ (∏ i : Fin rs.length, rs.get i ^ e i) • a e) ∈
      idealAssociatedGradedStage (Ideal.ofList rs) M n := by
  -- Every homogeneous monomial term already lies in the `n`th stage, so their finite sum does as
  -- well.
  refine Submodule.sum_mem _ ?_
  intro e he
  exact ofList_monomial_weight_smul_mem_of_degree rs n (a e) e (hdeg e he)

/-- Helper for Lemma 10.69.2: a homogeneous support-indexed source sum maps to the degree-`n`
class of its weighted coefficient sum. -/
private theorem quasiRegularSequenceAssociatedGradedMap_support_sum_of_homogeneous
    {rs : List R} {n : ℕ} {a : (Fin rs.length →₀ ℕ) →₀ M}
    (hdeg : ∀ e ∈ a.support, e.degree = n) :
    let J : Ideal R := Ideal.ofList rs
    let source :=
      Finset.sum a.support fun e ↦
        ((Submodule.Quotient.mk (a e) : M ⧸ (J • (⊤ : Submodule R M))) ⊗ₜ[R ⧸ J]
          MvPolynomial.monomial e (1 : R ⧸ J))
    quasiRegularSequenceAssociatedGradedMap M rs source =
      DirectSum.lof (R ⧸ J) ℕ (idealAssociatedGradedPiece J M) n
        (Submodule.Quotient.mk
          (⟨Finset.sum a.support fun e ↦ (∏ i : Fin rs.length, rs.get i ^ e i) • a e,
            weighted_support_sum_mem_stage_of_homogeneous (M := M) (rs := rs) (a := a) hdeg⟩ :
            idealAssociatedGradedStage J M n)) := by
  let J : Ideal R := Ideal.ofList rs
  let source :=
    Finset.sum a.support fun e ↦
      ((Submodule.Quotient.mk (a e) : M ⧸ (J • (⊤ : Submodule R M))) ⊗ₜ[R ⧸ J]
        MvPolynomial.monomial e (1 : R ⧸ J))
  let stageTerm :
      (Fin rs.length →₀ ℕ) → idealAssociatedGradedStage J M n :=
    fun e ↦
      if he : e ∈ a.support then
        ⟨(∏ i : Fin rs.length, rs.get i ^ e i) • a e,
          ofList_monomial_weight_smul_mem_of_degree rs n (a e) e (hdeg e he)⟩
      else
        0
  let pieceMk :
      idealAssociatedGradedStage J M n →+ idealAssociatedGradedPiece J M n :=
    (((idealAssociatedGradedStage J M (n + 1)).submoduleOf
      (idealAssociatedGradedStage J M n)).mkQ).toAddMonoidHom
  have hmap_terms :
      quasiRegularSequenceAssociatedGradedMap M rs source =
        Finset.sum a.support fun e ↦
          DirectSum.lof (R ⧸ J) ℕ (idealAssociatedGradedPiece J M) n
            (pieceMk (stageTerm e)) := by
    -- Rewrite the source sum termwise, then replace each monomial image by the normalized
    -- degree-`n` `DirectSum.lof` term given by the monomial computation theorem.
    simp only [source, map_sum]
    refine Finset.sum_congr rfl ?_
    intro e he
    have hmon :=
      quasiRegularSequenceAssociatedGradedMap_tmul_monomial_eq_lof
        (M := M) (rs := rs) (m := a e) (e := e)
    have hde : e.degree = n := hdeg e he
    cases hde
    simpa [J, pieceMk, stageTerm, he, Submodule.mkQ_apply] using hmon
  have hlof_sum :
      (Finset.sum a.support fun e ↦
        DirectSum.lof (R ⧸ J) ℕ (idealAssociatedGradedPiece J M) n
          (pieceMk (stageTerm e))) =
        DirectSum.lof (R ⧸ J) ℕ (idealAssociatedGradedPiece J M) n
          (Finset.sum a.support fun e ↦ pieceMk (stageTerm e)) := by
    -- `DirectSum.lof` is linear in the degree-`n` component, so it passes through the finite sum.
    symm
    exact map_sum (DirectSum.lof (R ⧸ J) ℕ (idealAssociatedGradedPiece J M) n)
      (fun e ↦ pieceMk (stageTerm e)) a.support
  have hstage_sum :
      (Finset.sum a.support fun e ↦ stageTerm e) =
        (⟨Finset.sum a.support fun e ↦ (∏ i : Fin rs.length, rs.get i ^ e i) • a e,
          weighted_support_sum_mem_stage_of_homogeneous (M := M) (rs := rs) (a := a) hdeg⟩ :
          idealAssociatedGradedStage J M n) := by
    -- The stage-valued support sum is the canonical subtype whose carrier is the weighted sum.
    apply Subtype.ext
    calc
      (((Finset.sum a.support fun e ↦ stageTerm e : idealAssociatedGradedStage J M n) : M)) =
        Finset.sum a.support fun e ↦ ((stageTerm e : idealAssociatedGradedStage J M n) : M) := by
          simpa using
            (map_sum (idealAssociatedGradedStage J M n).subtype
              (fun e ↦ stageTerm e) a.support)
      _ = Finset.sum a.support (fun e ↦ (∏ i : Fin rs.length, rs.get i ^ e i) • a e) := by
          refine Finset.sum_congr rfl ?_
          intro e he
          simp [stageTerm, he]
  have hpiece_sum :
      (Finset.sum a.support fun e ↦ pieceMk (stageTerm e)) =
        (Submodule.Quotient.mk
          (⟨Finset.sum a.support fun e ↦ (∏ i : Fin rs.length, rs.get i ^ e i) • a e,
            weighted_support_sum_mem_stage_of_homogeneous (M := M) (rs := rs) (a := a) hdeg⟩ :
            idealAssociatedGradedStage J M n) :
          idealAssociatedGradedPiece J M n) := by
    -- Package the finite sum in the stage quotient as the quotient class of the total weighted
    -- support sum.
    calc
      Finset.sum a.support (fun e ↦ pieceMk (stageTerm e)) =
          pieceMk (Finset.sum a.support fun e ↦ stageTerm e) := by
            symm
            exact map_sum pieceMk
              (fun e ↦ stageTerm e) a.support
      _ = pieceMk
            (⟨Finset.sum a.support fun e ↦ (∏ i : Fin rs.length, rs.get i ^ e i) • a e,
              weighted_support_sum_mem_stage_of_homogeneous (M := M) (rs := rs) (a := a) hdeg⟩ :
              idealAssociatedGradedStage J M n) := by
            rw [hstage_sum]
      _ =
          (Submodule.Quotient.mk
            (⟨Finset.sum a.support fun e ↦ (∏ i : Fin rs.length, rs.get i ^ e i) • a e,
              weighted_support_sum_mem_stage_of_homogeneous (M := M) (rs := rs) (a := a) hdeg⟩ :
              idealAssociatedGradedStage J M n) :
            idealAssociatedGradedPiece J M n) := by
            simp [pieceMk, Submodule.mkQ_apply]
  -- Combine the termwise normalization with additivity of `DirectSum.lof` and of the quotient
  -- projection on the homogeneous stage.
  calc
    quasiRegularSequenceAssociatedGradedMap M rs source =
      Finset.sum a.support fun e ↦
        DirectSum.lof (R ⧸ J) ℕ (idealAssociatedGradedPiece J M) n
          (pieceMk (stageTerm e)) := hmap_terms
    _ =
      DirectSum.lof (R ⧸ J) ℕ (idealAssociatedGradedPiece J M) n
        (Finset.sum a.support fun e ↦ pieceMk (stageTerm e)) := hlof_sum
    _ =
      DirectSum.lof (R ⧸ J) ℕ (idealAssociatedGradedPiece J M) n
        (Submodule.Quotient.mk
          (⟨Finset.sum a.support fun e ↦ (∏ i : Fin rs.length, rs.get i ^ e i) • a e,
            weighted_support_sum_mem_stage_of_homogeneous (M := M) (rs := rs) (a := a) hdeg⟩ :
            idealAssociatedGradedStage J M n)) := by
          rw [hpiece_sum]

/-- Helper for Lemma 10.69.2: the degree-`n` component of a homogeneous support-indexed source sum
is the quotient class of its weighted coefficient sum. -/
private theorem degree_component_of_homogeneous_support_sum
    {rs : List R} {n : ℕ} {a : (Fin rs.length →₀ ℕ) →₀ M}
    (hdeg : ∀ e ∈ a.support, e.degree = n) :
    let J : Ideal R := Ideal.ofList rs
    let source :=
      Finset.sum a.support fun e ↦
        ((Submodule.Quotient.mk (a e) : M ⧸ (J • (⊤ : Submodule R M))) ⊗ₜ[R ⧸ J]
          MvPolynomial.monomial e (1 : R ⧸ J))
    let componentN := DirectSum.component (R ⧸ J) ℕ (idealAssociatedGradedPiece J M) n
    componentN (quasiRegularSequenceAssociatedGradedMap M rs source) =
      (Submodule.Quotient.mk
        (⟨Finset.sum a.support fun e ↦ (∏ i : Fin rs.length, rs.get i ^ e i) • a e,
          weighted_support_sum_mem_stage_of_homogeneous (M := M) (rs := rs) (a := a) hdeg⟩ :
          idealAssociatedGradedStage J M n) :
        idealAssociatedGradedPiece J M n) := by
  -- Project the normalized homogeneous image back to the `n`th direct-sum component.
  dsimp
  have hmap :=
    quasiRegularSequenceAssociatedGradedMap_support_sum_of_homogeneous
      (M := M) (rs := rs) (n := n) (a := a) hdeg
  exact by
    simpa using congrArg
      (DirectSum.component (R ⧸ Ideal.ofList rs) ℕ
        (idealAssociatedGradedPiece (Ideal.ofList rs) M) n)
      hmap

/-- Helper for Lemma 10.69.2: a homogeneous kernel relation yields the textbook stage relation
`∑ weight(e) • a e ∈ (Ideal.ofList rs) ^ (n + 1) • ⊤`. -/
private theorem homogeneous_weighted_sum_mem_next_stage_of_kernel
    {rs : List R} {n : ℕ} {a : (Fin rs.length →₀ ℕ) →₀ M}
    (hdeg : ∀ e ∈ a.support, e.degree = n)
    (hker :
      quasiRegularSequenceAssociatedGradedMap M rs
        (a.sum fun e m ↦
          ((Submodule.Quotient.mk m :
              M ⧸ ((Ideal.ofList rs) • (⊤ : Submodule R M))) ⊗ₜ[R ⧸ Ideal.ofList rs]
            MvPolynomial.monomial e (1 : R ⧸ Ideal.ofList rs))) = 0) :
    (Finset.sum a.support fun e ↦ (∏ i : Fin rs.length, rs.get i ^ e i) • a e) ∈
      ((Ideal.ofList rs) ^ (n + 1)) • (⊤ : Submodule R M) := by
  let J : Ideal R := Ideal.ofList rs
  let source :=
    Finset.sum a.support fun e ↦
      ((Submodule.Quotient.mk (a e) : M ⧸ (J • (⊤ : Submodule R M))) ⊗ₜ[R ⧸ J]
        MvPolynomial.monomial e (1 : R ⧸ J))
  let componentN := DirectSum.component (R ⧸ J) ℕ (idealAssociatedGradedPiece J M) n
  -- Rewrite the kernel relation into the support-indexed source sum used by the normalization
  -- lemmas, then project to the homogeneous degree `n`.
  rw [monomial_tensor_family_sum_eq_support_sum (rs := rs) a] at hker
  have hcomponent_zero :
      componentN (quasiRegularSequenceAssociatedGradedMap M rs source) = 0 := by
    simpa [source, componentN] using congrArg componentN hker
  have hcomponent_eq :
      componentN (quasiRegularSequenceAssociatedGradedMap M rs source) =
        (Submodule.Quotient.mk
          (⟨Finset.sum a.support fun e ↦ (∏ i : Fin rs.length, rs.get i ^ e i) • a e,
            weighted_support_sum_mem_stage_of_homogeneous (M := M) (rs := rs) (a := a) hdeg⟩ :
            idealAssociatedGradedStage J M n) :
          idealAssociatedGradedPiece J M n) := by
    simpa [source, componentN] using
      degree_component_of_homogeneous_support_sum
        (M := M) (rs := rs) (n := n) (a := a) hdeg
  rw [hcomponent_eq] at hcomponent_zero
  have hmem_sub :
      (⟨Finset.sum a.support fun e ↦ (∏ i : Fin rs.length, rs.get i ^ e i) • a e,
        weighted_support_sum_mem_stage_of_homogeneous (M := M) (rs := rs) (a := a) hdeg⟩ :
        idealAssociatedGradedStage J M n) ∈
        (idealAssociatedGradedStage J M (n + 1)).submoduleOf
          (idealAssociatedGradedStage J M n) := by
    exact (Submodule.Quotient.mk_eq_zero _).1 hcomponent_zero
  -- Vanishing in the degree-`n` quotient piece is exactly membership in the next filtration stage.
  simpa [idealAssociatedGradedStage, J] using hmem_sub

/-- Helper for Lemma 10.69.2: the stage relation for a homogeneous family already implies the
corresponding kernel relation for the associated-graded map. -/
private theorem homogeneous_kernel_of_weighted_sum_mem_next_stage
    {rs : List R} {n : ℕ} {a : (Fin rs.length →₀ ℕ) →₀ M}
    (hdeg : ∀ e ∈ a.support, e.degree = n)
    (hstage :
      (Finset.sum a.support fun e ↦ (∏ i : Fin rs.length, rs.get i ^ e i) • a e) ∈
        ((Ideal.ofList rs) ^ (n + 1)) • (⊤ : Submodule R M)) :
    quasiRegularSequenceAssociatedGradedMap M rs
      (a.sum fun e m ↦
        ((Submodule.Quotient.mk m :
            M ⧸ ((Ideal.ofList rs) • (⊤ : Submodule R M))) ⊗ₜ[R ⧸ Ideal.ofList rs]
          MvPolynomial.monomial e (1 : R ⧸ Ideal.ofList rs))) = 0 := by
  let J : Ideal R := Ideal.ofList rs
  let piece :
      idealAssociatedGradedPiece J M n :=
    Submodule.Quotient.mk
      (⟨Finset.sum a.support fun e ↦ (∏ i : Fin rs.length, rs.get i ^ e i) • a e,
        weighted_support_sum_mem_stage_of_homogeneous (M := M) (rs := rs) (a := a) hdeg⟩ :
        idealAssociatedGradedStage J M n)
  have hpiece_zero : piece = 0 := by
    -- The stage hypothesis says exactly that the degree-`n` class dies in the quotient by the next
    -- stage.
    apply (Submodule.Quotient.mk_eq_zero _).2
    simpa [piece, idealAssociatedGradedStage, J] using hstage
  -- Normalize the homogeneous source sum to a single graded piece and then kill that piece by the
  -- stage hypothesis.
  rw [monomial_tensor_family_sum_eq_support_sum (rs := rs) a]
  have hmap :
      quasiRegularSequenceAssociatedGradedMap M rs
        (Finset.sum a.support fun e ↦
          ((Submodule.Quotient.mk (a e) : M ⧸ (J • (⊤ : Submodule R M))) ⊗ₜ[R ⧸ J]
            MvPolynomial.monomial e (1 : R ⧸ J))) =
        DirectSum.lof (R ⧸ J) ℕ (idealAssociatedGradedPiece J M) n piece := by
    -- The support-sum normalization proved above is the exact converse bridge needed here.
    simpa [piece, J] using
      quasiRegularSequenceAssociatedGradedMap_support_sum_of_homogeneous
        (M := M) (rs := rs) (n := n) (a := a) hdeg
  rw [hmap, hpiece_zero]
  simp

/-- Helper for Lemma 10.69.2: the empty sequence case of the homogeneous coefficient criterion is
already forced by the stage relation. -/
private theorem homogeneous_kernel_coeff_mem_ideal_nil
    {n : ℕ} {a : (Fin ([] : List R).length →₀ ℕ) →₀ M}
    (hdeg : ∀ e ∈ a.support, e.degree = n)
    (hker :
      quasiRegularSequenceAssociatedGradedMap M []
        (a.sum fun e m ↦
          ((Submodule.Quotient.mk m :
              M ⧸ ((Ideal.ofList ([] : List R)) • (⊤ : Submodule R M))) ⊗ₜ[
                R ⧸ Ideal.ofList ([] : List R)]
            MvPolynomial.monomial e
              (1 : R ⧸ Ideal.ofList ([] : List R)))) = 0) :
    ∀ e ∈ a.support, a e ∈ Ideal.ofList ([] : List R) • (⊤ : Submodule R M) := by
  let J : Ideal R := Ideal.ofList ([] : List R)
  have hstage :
      (Finset.sum a.support fun d ↦ (∏ i : Fin ([] : List R).length, ([] : List R).get i ^ d i) • a d) ∈
        (J ^ (n + 1)) • (⊤ : Submodule R M) := by
    -- The empty-sequence kernel relation first becomes the corresponding stage relation.
    exact homogeneous_weighted_sum_mem_next_stage_of_kernel
      (M := M) (rs := []) (n := n) (a := a) hdeg hker
  intro e he
  have heq :
      e = (0 : Fin ([] : List R).length →₀ ℕ) := by
    ext i
    exact Fin.elim0 i
  subst e
  have hsupp : a.support = {0} := by
    -- On the empty index type, every exponent is the unique zero exponent.
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨he, ?_⟩
    intro d hd
    ext i
    exact Fin.elim0 i
  -- Rewrite the weighted support sum as the unique empty-index term and simplify the empty product.
  rw [hsupp] at hstage
  simpa [J] using hstage

/-- Helper for Lemma 10.69.2: subtracting a same-degree correction family preserves homogeneity in
the common degree. -/
private theorem homogeneous_sub_of_same_degree
    {rs : List R} {n : ℕ} {a c : (Fin rs.length →₀ ℕ) →₀ M}
    (ha : ∀ e ∈ a.support, e.degree = n)
    (hc : ∀ e ∈ c.support, e.degree = n) :
    ∀ e ∈ (a - c).support, e.degree = n := by
  intro e he
  -- Any nonzero coefficient of `a - c` comes from a support point of either `a` or `c`, so one of
  -- the two homogeneous hypotheses supplies the common total degree.
  by_cases hea : e ∈ a.support
  · exact ha e hea
  · have hce : e ∈ c.support := by
      rw [Finsupp.mem_support_iff] at he hea ⊢
      have hazero : a e = 0 := by
        simpa using hea
      intro hzero
      apply he
      simp [hazero, hzero]
    exact hc e hce

/-- Helper for Lemma 10.69.2: adding two same-degree families preserves homogeneity in that
common degree. -/
private theorem homogeneous_add_of_same_degree
    {rs : List R} {n : ℕ} {a b : (Fin rs.length →₀ ℕ) →₀ M}
    (ha : ∀ e ∈ a.support, e.degree = n)
    (hb : ∀ e ∈ b.support, e.degree = n) :
    ∀ e ∈ (a + b).support, e.degree = n := by
  intro e he
  by_cases hea : e ∈ a.support
  · exact ha e hea
  · have hbe : e ∈ b.support := by
      rw [Finsupp.mem_support_iff] at he hea ⊢
      have hazero : a e = 0 := by
        simpa using hea
      intro hzero
      apply he
      simp [hazero, hzero]
    exact hb e hbe

/-- Helper for Lemma 10.69.2: a support-indexed coefficient condition extends to every index
because coefficients outside the support are zero. -/
private theorem coeff_mem_submodule_of_support
    {rs : List R} (S : Submodule R M) {a : (Fin rs.length →₀ ℕ) →₀ M}
    (ha : ∀ e ∈ a.support, a e ∈ S) :
    ∀ e, a e ∈ S := by
  intro e
  by_cases he : e ∈ a.support
  · exact ha e he
  · simpa [Finsupp.notMem_support_iff.mp he] using (zero_mem S)

/-- Helper for Lemma 10.69.2: scaling a homogeneous family preserves its common degree on the
remaining support. -/
private theorem homogeneous_smul_of_same_degree
    {rs : List R} {n : ℕ} {a : (Fin rs.length →₀ ℕ) →₀ M} (r : R)
    (ha : ∀ e ∈ a.support, e.degree = n) :
    ∀ e ∈ (r • a).support, e.degree = n := by
  intro e he
  exact ha e (Finsupp.support_smul he)

/-- Helper for Lemma 10.69.2: the weighted support sum of a scaled family is the corresponding
scalar multiple of the original weighted support sum. -/
private theorem weighted_sum_smul_family
    {rs : List R} (r : R) (a : (Fin rs.length →₀ ℕ) →₀ M) :
    (Finset.sum (r • a).support fun e ↦ (∏ i : Fin rs.length, rs.get i ^ e i) • ((r • a) e)) =
      r • (Finset.sum a.support fun e ↦ (∏ i : Fin rs.length, rs.get i ^ e i) • a e) := by
  classical
  -- Expand both support sums over `a.support`; outside `(r • a).support` the scaled coefficient
  -- vanishes, so only the visible support contributes.
  calc
    Finset.sum (r • a).support (fun e ↦ (∏ i : Fin rs.length, rs.get i ^ e i) • ((r • a) e)) =
        Finset.sum a.support (fun e ↦ (∏ i : Fin rs.length, rs.get i ^ e i) • ((r • a) e)) := by
          refine Finset.sum_subset Finsupp.support_smul ?_
          intro e heA heSmul
          have hzero : (r • a) e = 0 := Finsupp.notMem_support_iff.mp heSmul
          simp [hzero]
    _ = Finset.sum a.support (fun e ↦ r • ((∏ i : Fin rs.length, rs.get i ^ e i) • a e)) := by
          refine Finset.sum_congr rfl ?_
          intro e he
          simp [smul_smul, mul_comm, mul_left_comm, mul_assoc]
    _ = r • (Finset.sum a.support fun e ↦ (∏ i : Fin rs.length, rs.get i ^ e i) • a e) := by
          rw [Finset.smul_sum]

/-- Helper for Lemma 10.69.2: weighted support sums are additive in the coefficient family. -/
private theorem weighted_support_sum_add
    {rs : List R} (a b : (Fin rs.length →₀ ℕ) →₀ M) :
    (Finset.sum (a + b).support fun e ↦ (∏ i : Fin rs.length, rs.get i ^ e i) • (a + b) e) =
      (Finset.sum a.support fun e ↦ (∏ i : Fin rs.length, rs.get i ^ e i) • a e) +
        (Finset.sum b.support fun e ↦ (∏ i : Fin rs.length, rs.get i ^ e i) • b e) := by
  -- Rewrite each support sum as `Finsupp.sum` and then use additivity in the coefficient family.
  rw [show (Finset.sum (a + b).support fun e ↦ (∏ i : Fin rs.length, rs.get i ^ e i) • (a + b) e) =
      (a + b).sum (fun e m ↦ (∏ i : Fin rs.length, rs.get i ^ e i) • m) by
      rw [Finsupp.sum]]
  rw [show (Finset.sum a.support fun e ↦ (∏ i : Fin rs.length, rs.get i ^ e i) • a e) =
      a.sum (fun e m ↦ (∏ i : Fin rs.length, rs.get i ^ e i) • m) by
      rw [Finsupp.sum]]
  rw [show (Finset.sum b.support fun e ↦ (∏ i : Fin rs.length, rs.get i ^ e i) • b e) =
      b.sum (fun e m ↦ (∏ i : Fin rs.length, rs.get i ^ e i) • m) by
      rw [Finsupp.sum]]
  rw [Finsupp.sum_add_index]
  · intro e
    simp
  · intro e m₁ m₂
    simp [smul_add]

/-- Helper for Lemma 10.69.2: a correction family with coefficients in `Ideal.ofList rs • ⊤`
contributes zero to the source tensor sum, so subtracting it preserves the kernel relation. -/
private theorem kernel_family_sub_of_coeff_mem_ideal
    {rs : List R} {a c : (Fin rs.length →₀ ℕ) →₀ M}
    (hker :
      quasiRegularSequenceAssociatedGradedMap M rs
        (a.sum fun e m ↦
          ((Submodule.Quotient.mk m :
              M ⧸ ((Ideal.ofList rs) • (⊤ : Submodule R M))) ⊗ₜ[R ⧸ Ideal.ofList rs]
            MvPolynomial.monomial e (1 : R ⧸ Ideal.ofList rs))) = 0)
    (hcoeff :
      ∀ e ∈ c.support, c e ∈ Ideal.ofList rs • (⊤ : Submodule R M)) :
    quasiRegularSequenceAssociatedGradedMap M rs
      ((a - c).sum fun e m ↦
        ((Submodule.Quotient.mk m :
            M ⧸ ((Ideal.ofList rs) • (⊤ : Submodule R M))) ⊗ₜ[R ⧸ Ideal.ofList rs]
          MvPolynomial.monomial e (1 : R ⧸ Ideal.ofList rs))) = 0 := by
  let J : Ideal R := Ideal.ofList rs
  let term :
      (Fin rs.length →₀ ℕ) →
        M →
          (M ⧸ (J • (⊤ : Submodule R M))) ⊗[R ⧸ J]
            MvPolynomial (Fin rs.length) (R ⧸ J) :=
    fun e m ↦
      ((Submodule.Quotient.mk m : M ⧸ (J • (⊤ : Submodule R M))) ⊗ₜ[R ⧸ J]
        MvPolynomial.monomial e (1 : R ⧸ J))
  have hzero : c.sum term = 0 := by
    -- Ideal-valued correction coefficients already die in the quotient source.
    simpa [J, term] using
      source_tensor_sum_eq_zero_of_coeff_mem_ideal (M := M) (rs := rs) (a := c) hcoeff
  have hsum :
      (a - c).sum term = a.sum term - c.sum term := by
    -- The monomial source construction is additive in the coefficient family.
    rw [Finsupp.sum_sub_index]
    intro e b₁ b₂
    simpa [term] using
      (TensorProduct.sub_tmul
        (R := R ⧸ J)
        (m₁ := (Submodule.Quotient.mk b₁ : M ⧸ (J • (⊤ : Submodule R M))))
        (m₂ := (Submodule.Quotient.mk b₂ : M ⧸ (J • (⊤ : Submodule R M))))
        (n := MvPolynomial.monomial e (1 : R ⧸ J)))
  -- Replace the corrected source by the original kernel element minus the zero correction.
  rw [hsum, map_sub, hker, hzero]
  simp

/-- Helper for Lemma 10.69.2: once the corrected family is known to have all coefficients in
`Ideal.ofList rs • ⊤`, the same holds for the original family because the correction coefficients
already lie in that ideal. -/
private theorem coeff_mem_ideal_of_sub_correction
    {rs : List R} {a c : (Fin rs.length →₀ ℕ) →₀ M}
    (hsub :
      ∀ e ∈ (a - c).support, (a - c) e ∈ Ideal.ofList rs • (⊤ : Submodule R M))
    (hcoeff :
      ∀ e ∈ c.support, c e ∈ Ideal.ofList rs • (⊤ : Submodule R M)) :
    ∀ e ∈ a.support, a e ∈ Ideal.ofList rs • (⊤ : Submodule R M) := by
  intro e he
  have hc :
      c e ∈ Ideal.ofList rs • (⊤ : Submodule R M) := by
    by_cases hce : e ∈ c.support
    · exact hcoeff e hce
    · have hzero : c e = 0 := Finsupp.notMem_support_iff.mp hce
      simpa [hzero]
  by_cases hsube : e ∈ (a - c).support
  · have hsub_mem :
        (a - c) e ∈ Ideal.ofList rs • (⊤ : Submodule R M) := hsub e hsube
    -- Rewrite the original coefficient as the corrected coefficient plus the correction.
    have hsplit : a e = (a - c) e + c e := by
      simp [sub_eq_add_neg, add_assoc]
    rw [hsplit]
    exact Submodule.add_mem _ hsub_mem hc
  · have hzero : (a - c) e = 0 := Finsupp.notMem_support_iff.mp hsube
    -- Outside the corrected support, the original and correction coefficients agree.
    have hEq : a e = c e := by
      have := congrArg (fun m : M ↦ m + c e) hzero
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
    simpa [hEq] using hc

/-- Helper for Lemma 10.69.2: if a homogeneous family already has coefficients in
`Ideal.ofList rs • ⊤`, then its weighted support sum lies one stage deeper in the
`Ideal.ofList rs`-adic filtration. -/
private theorem weighted_support_sum_mem_next_stage_of_homogeneous_coeff_mem_ideal
    {rs : List R} {n : ℕ} {a : (Fin rs.length →₀ ℕ) →₀ M}
    (hdeg : ∀ e ∈ a.support, e.degree = n)
    (hcoeff : ∀ e ∈ a.support, a e ∈ Ideal.ofList rs • (⊤ : Submodule R M)) :
    (Finset.sum a.support fun e ↦ (∏ i : Fin rs.length, rs.get i ^ e i) • a e) ∈
      ((Ideal.ofList rs) ^ (n + 1)) • (⊤ : Submodule R M) := by
  -- Estimate each homogeneous monomial term separately in `J ^ n • (J • ⊤) = J ^ (n + 1) • ⊤`.
  refine Submodule.sum_mem _ ?_
  intro e he
  have hweight :
      (∏ i : Fin rs.length, rs.get i ^ e i) ∈ (Ideal.ofList rs) ^ n := by
    simpa [hdeg e he] using ofList_monomial_weight_mem_pow (R := R) rs e
  have hterm :
      (∏ i : Fin rs.length, rs.get i ^ e i) • a e ∈
        ((Ideal.ofList rs) ^ n) • (Ideal.ofList rs • (⊤ : Submodule R M)) := by
    exact Submodule.smul_mem_smul hweight (hcoeff e he)
  have hterm' :
      (∏ i : Fin rs.length, rs.get i ^ e i) • a e ∈
        (((Ideal.ofList rs) ^ n) * Ideal.ofList rs) • (⊤ : Submodule R M) := by
    simpa [smul_smul, Ideal.mul_assoc] using hterm
  simpa [pow_succ] using hterm'

/-- Helper for Lemma 10.69.2: `Ideal.ofList rs` is the span of the finitely indexed family
`rs.get`. -/
private theorem ofList_eq_span_range_get (rs : List R) :
    Ideal.ofList rs = Ideal.span (Set.range fun i : Fin rs.length ↦ rs.get i) := by
  -- Replace list-membership generators by the equivalent finite-indexed family `rs.get`.
  rw [Ideal.ofList]
  congr
  ext x
  constructor
  · intro hx
    rcases List.mem_iff_get.mp hx with ⟨i, rfl⟩
    exact Set.mem_range_self i
  · rintro ⟨i, rfl⟩
    exact List.get_mem rs i

/-- Helper for Lemma 10.69.2: an element of `Ideal.ofList rs` is a finite linear combination of
the generators `rs.get i`. -/
private theorem exists_sum_get_of_mem_ofList
    {rs : List R} {x : R} (hx : x ∈ Ideal.ofList rs) :
    ∃ c : Fin rs.length →₀ R, c.sum (fun i a ↦ a * rs.get i) = x := by
  -- Rewrite the list-generated ideal as the span of the finite family `rs.get` and extract an
  -- explicit finite linear combination.
  have hx' : x ∈ Submodule.span R (Set.range fun i : Fin rs.length ↦ rs.get i) := by
    simpa [ofList_eq_span_range_get (R := R) rs] using hx
  rcases Finsupp.mem_span_range_iff_exists_finsupp.mp hx' with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  simpa [smul_eq_mul] using hc

/-- Helper for Lemma 10.69.2: increment one exponent coordinate by one. -/
private noncomputable def bump_exponent {rs : List R} (e : Fin rs.length →₀ ℕ) (i : Fin rs.length) :
    Fin rs.length →₀ ℕ :=
  e + Finsupp.single i 1

/-- Helper for Lemma 10.69.2: incrementing one exponent coordinate raises the total degree by
one. -/
private theorem bump_exponent_degree {rs : List R}
    (e : Fin rs.length →₀ ℕ) (i : Fin rs.length) :
    (bump_exponent (rs := rs) e i).degree = e.degree + 1 := by
  -- Expand the degree through `bump_exponent = e + single i 1`; the singleton contributes exactly
  -- one to the total degree.
  simp [bump_exponent, Finsupp.degree_eq_sum, Finset.sum_add_distrib]

/-- Helper for Lemma 10.69.2: incrementing coordinate `i` multiplies the monomial weight by the
corresponding generator `rs.get i`. -/
private theorem bump_exponent_weight {rs : List R}
    (e : Fin rs.length →₀ ℕ) (i : Fin rs.length) :
    (∏ j : Fin rs.length, rs.get j ^ bump_exponent (rs := rs) e i j) =
      (∏ j : Fin rs.length, rs.get j ^ e j) * rs.get i := by
  -- Expand the bumped exponent coordinatewise, then isolate the unique extra generator factor at
  -- coordinate `i`.
  rw [bump_exponent]
  simp_rw [Finsupp.add_apply, Finsupp.single_apply, pow_add]
  rw [Finset.prod_mul_distrib]
  have hpow :
      ∀ j : Fin rs.length, rs.get j ^ (if i = j then 1 else 0) = if i = j then rs.get j else 1 := by
    intro j
    by_cases h : i = j
    · simp [h]
    · simp [h]
  simp_rw [hpow]
  have htail : (∏ j : Fin rs.length, if i = j then rs.get j else 1) = rs.get i := by
    simpa using
      (Finset.prod_ite_eq (s := Finset.univ) (a := i) (b := fun j : Fin rs.length ↦ rs.get j))
  rw [htail]

/-- Helper for Lemma 10.69.2: incrementing one exponent coordinate is injective. -/
private theorem bump_exponent_injective {rs : List R} (i : Fin rs.length) :
    Function.Injective (fun e : Fin rs.length →₀ ℕ ↦ bump_exponent (rs := rs) e i) := by
  intro e₁ e₂ h
  ext j
  by_cases hij : j = i
  · subst hij
    have hcoord := congrArg (fun f : Fin rs.length →₀ ℕ ↦ f j) h
    simpa [bump_exponent] using hcoord
  · have hcoord := congrArg (fun f : Fin rs.length →₀ ℕ ↦ f j) h
    simp [bump_exponent, hij] at hcoord
    exact hcoord

/-- Helper for Lemma 10.69.2: one generator factor can be absorbed into the exponent vector while
preserving homogeneity and the weighted support sum. -/
private theorem same_degree_single_generator_bump
    {rs : List R} {n : ℕ} {b : (Fin rs.length →₀ ℕ) →₀ M}
    (hb : ∀ e ∈ b.support, e.degree = n) (i : Fin rs.length) (r : R) :
    ∃ B : (Fin rs.length →₀ ℕ) →₀ M,
      (∀ e ∈ B.support, e.degree = n + 1) ∧
      Finset.sum B.support (fun e ↦ (∏ j : Fin rs.length, rs.get j ^ e j) • B e) =
        r • (rs.get i • Finset.sum b.support fun e ↦ (∏ j : Fin rs.length, rs.get j ^ e j) • b e) := by
  classical
  let f : (Fin rs.length →₀ ℕ) ↪ (Fin rs.length →₀ ℕ) :=
    ⟨fun e ↦ bump_exponent (rs := rs) e i, bump_exponent_injective (rs := rs) i⟩
  let B : (Fin rs.length →₀ ℕ) →₀ M := (r • b).embDomain f
  refine ⟨B, ?_, ?_⟩
  · intro e he
    -- The bumped family is supported exactly on exponents obtained by adding one copy of the
    -- chosen generator, so the common degree rises from `n` to `n + 1`.
    have he' : e ∈ (r • b).support.map f := by
      simpa [B] using he
    rcases Finset.mem_map.mp he' with ⟨e₀, he₀, rfl⟩
    have hb₀ : e₀.degree = n := hb e₀ (Finsupp.support_smul he₀)
    simpa [f, bump_exponent_degree, hb₀]
  · -- Rewrite the bumped family sum back over the original support and evaluate the extra
    -- generator factor through `bump_exponent_weight`.
    calc
      Finset.sum B.support (fun e ↦ (∏ j : Fin rs.length, rs.get j ^ e j) • B e)
          = (r • b).sum (fun e m ↦
              (∏ j : Fin rs.length, rs.get j ^ bump_exponent (rs := rs) e i j) • m) := by
              rw [show Finset.sum B.support (fun e ↦ (∏ j : Fin rs.length, rs.get j ^ e j) • B e) =
                  B.sum (fun e m ↦ (∏ j : Fin rs.length, rs.get j ^ e j) • m) by
                    rw [Finsupp.sum]]
              simpa [B, f] using
                (Finsupp.sum_embDomain
                  (v := r • b)
                  (f := f)
                  (g := fun e m ↦ (∏ j : Fin rs.length, rs.get j ^ e j) • m))
      _ = Finset.sum (r • b).support (fun e ↦
            (∏ j : Fin rs.length, rs.get j ^ bump_exponent (rs := rs) e i j) • ((r • b) e)) := by
              rw [Finsupp.sum]
      _ = Finset.sum (r • b).support (fun e ↦
            rs.get i • ((∏ j : Fin rs.length, rs.get j ^ e j) • ((r • b) e))) := by
              refine Finset.sum_congr rfl ?_
              intro e he
              rw [bump_exponent_weight]
              simp [smul_smul, mul_assoc, mul_left_comm, mul_comm]
      _ = rs.get i • (Finset.sum (r • b).support fun e ↦
            (∏ j : Fin rs.length, rs.get j ^ e j) • ((r • b) e)) := by
              rw [Finset.smul_sum]
      _ = rs.get i •
            (r • Finset.sum b.support fun e ↦ (∏ j : Fin rs.length, rs.get j ^ e j) • b e) := by
              rw [weighted_sum_smul_family (M := M) (rs := rs) r b]
      _ = r • (rs.get i • Finset.sum b.support fun e ↦
            (∏ j : Fin rs.length, rs.get j ^ e j) • b e) := by
              simp [smul_smul, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Lemma 10.69.2: a finite linear combination of the generators `rs.get i` can be
absorbed into a same-degree family, raising the common degree by one. -/
private theorem same_degree_family_of_generator_combination
    {rs : List R} {n : ℕ} {b : (Fin rs.length →₀ ℕ) →₀ M}
    (hb : ∀ e ∈ b.support, e.degree = n) (c : Fin rs.length →₀ R) :
    ∃ B : (Fin rs.length →₀ ℕ) →₀ M,
      (∀ e ∈ B.support, e.degree = n + 1) ∧
      Finset.sum B.support (fun e ↦ (∏ j : Fin rs.length, rs.get j ^ e j) • B e) =
        (c.sum fun i a ↦ a * rs.get i) •
          Finset.sum b.support (fun e ↦ (∏ j : Fin rs.length, rs.get j ^ e j) • b e) := by
  classical
  induction c using Finsupp.induction with
  | zero =>
      refine ⟨0, ?_, ?_⟩
      · intro e he
        simpa using he
      · simp
  | single_add i a c hi ha ih =>
      rcases same_degree_single_generator_bump (M := M) (rs := rs) (n := n) (b := b) hb i a with
        ⟨Ba, hBa_deg, hBa_sum⟩
      rcases ih with ⟨Bc, hBc_deg, hBc_sum⟩
      refine ⟨Ba + Bc, ?_, ?_⟩
      · -- Both summands are homogeneous of degree `n + 1`, so their sum stays homogeneous.
        exact homogeneous_add_of_same_degree (M := M) (rs := rs) (n := n + 1) hBa_deg hBc_deg
      · -- Add the one-generator bump to the inductive family and rewrite the coefficient sum.
        calc
          Finset.sum (Ba + Bc).support (fun e ↦ (∏ j : Fin rs.length, rs.get j ^ e j) • (Ba + Bc) e)
              =
            (Finset.sum Ba.support fun e ↦ (∏ j : Fin rs.length, rs.get j ^ e j) • Ba e) +
              (Finset.sum Bc.support fun e ↦ (∏ j : Fin rs.length, rs.get j ^ e j) • Bc e) := by
                rw [weighted_support_sum_add]
          _ =
            a • (rs.get i • Finset.sum b.support fun e ↦ (∏ j : Fin rs.length, rs.get j ^ e j) • b e) +
              (c.sum fun i a ↦ a * rs.get i) •
                Finset.sum b.support (fun e ↦ (∏ j : Fin rs.length, rs.get j ^ e j) • b e) := by
                  rw [hBa_sum, hBc_sum]
          _ =
            ((a * rs.get i) + c.sum fun i a ↦ a * rs.get i) •
              Finset.sum b.support (fun e ↦ (∏ j : Fin rs.length, rs.get j ^ e j) • b e) := by
                simp [add_smul, smul_smul, mul_assoc, mul_left_comm, mul_comm]
          _ =
            (((Finsupp.single i a : Fin rs.length →₀ R) + c).sum fun i a ↦ a * rs.get i) •
              Finset.sum b.support (fun e ↦ (∏ j : Fin rs.length, rs.get j ^ e j) • b e) := by
                congr 1
                rw [Finsupp.sum_add_index]
                · simp [Finsupp.sum_single_index, ha]
                · intro i
                  simp
                · intro i a₁ a₂
                  simp [add_mul]

/-- Helper for Lemma 10.69.2: every stage element admits a finite homogeneous monomial-family
representation in its exact degree. -/
private theorem same_degree_family_of_mem_stage
    {rs : List R} {n : ℕ} {x : M}
    (hx : x ∈ idealAssociatedGradedStage (Ideal.ofList rs) M n) :
    ∃ b : (Fin rs.length →₀ ℕ) →₀ M,
      (∀ e ∈ b.support, e.degree = n) ∧
      Finset.sum b.support (fun e ↦ (∏ i : Fin rs.length, rs.get i ^ e i) • b e) = x := by
  classical
  -- Route correction: the reindexing step is now isolated in
  -- `same_degree_single_generator_bump`; what remains is the source-proof induction on `n`,
  -- using `Submodule.smul_induction_on'` together with `exists_sum_get_of_mem_ofList`.
  induction n generalizing x with
  | zero =>
      by_cases hx0 : x = 0
      · subst hx0
        refine ⟨0, ?_, ?_⟩
        · intro e he
          simpa using he
        · simp
      · refine ⟨Finsupp.single 0 x, ?_, ?_⟩
        · intro e he
          have he0 : e = 0 := by
            simpa [Finsupp.support_single_ne_zero _ hx0] using he
          subst he0
          simp
        · simp [Finsupp.support_single_ne_zero _ hx0]
  | succ n ih =>
      let J : Ideal R := Ideal.ofList rs
      have hx' : x ∈ J • idealAssociatedGradedStage J M n := by
        -- Rewrite the `(n + 1)`-st stage as `J • (J ^ n M)` before applying smul induction.
        simpa [J, idealAssociatedGradedStage, pow_succ, Ideal.mul_comm, mul_smul] using hx
      refine Submodule.smul_induction_on' hx' ?_ ?_
      · intro r hr y hy
        rcases ih hy with ⟨b, hb_deg, hb_sum⟩
        rcases exists_sum_get_of_mem_ofList (R := R) (rs := rs) hr with ⟨c, hc_sum⟩
        rcases same_degree_family_of_generator_combination
            (M := M) (rs := rs) (n := n) (b := b) hb_deg c with ⟨B, hB_deg, hB_sum⟩
        refine ⟨B, hB_deg, ?_⟩
        -- Substitute the coefficient decomposition of `r` and the stage-`n` family sum.
        calc
          Finset.sum B.support (fun e ↦ (∏ i : Fin rs.length, rs.get i ^ e i) • B e)
              =
            (c.sum fun i a ↦ a * rs.get i) •
              Finset.sum b.support (fun e ↦ (∏ i : Fin rs.length, rs.get i ^ e i) • b e) := hB_sum
          _ = r • Finset.sum b.support (fun e ↦ (∏ i : Fin rs.length, rs.get i ^ e i) • b e) := by
                rw [hc_sum]
          _ = r • y := by rw [hb_sum]
      · intro x₁ hx₁ y₁ hy₁ hx_family hy_family
        rcases hx_family with ⟨bx, hbx_deg, hbx_sum⟩
        rcases hy_family with ⟨byFamily, hby_deg, hby_sum⟩
        refine ⟨bx + byFamily, ?_, ?_⟩
        · -- Both stage families are homogeneous in degree `n + 1`, so their sum is as well.
          exact homogeneous_add_of_same_degree (M := M) (rs := rs) (n := n + 1) hbx_deg hby_deg
        · -- The weighted support sum of the combined family is the sum of the two stage elements.
          calc
            Finset.sum (bx + byFamily).support
                (fun e ↦ (∏ i : Fin rs.length, rs.get i ^ e i) • (bx + byFamily) e)
                =
              (Finset.sum bx.support fun e ↦ (∏ i : Fin rs.length, rs.get i ^ e i) • bx e) +
                (Finset.sum byFamily.support fun e ↦
                  (∏ i : Fin rs.length, rs.get i ^ e i) • byFamily e) := by
                  rw [weighted_support_sum_add]
            _ = x₁ + y₁ := by rw [hbx_sum, hby_sum]

/-- Helper for Lemma 10.69.2: a homogeneous weighted sum in the next filtration stage admits a
same-degree correction family with ideal-valued coefficients and the same weighted sum. -/
private theorem same_degree_ideal_correction_of_weighted_sum_mem_next_stage
    {rs : List R} {n : ℕ} {a : (Fin rs.length →₀ ℕ) →₀ M}
    (hdeg : ∀ e ∈ a.support, e.degree = n)
    (hstage :
      (Finset.sum a.support fun e ↦ (∏ i : Fin rs.length, rs.get i ^ e i) • a e) ∈
        ((Ideal.ofList rs) ^ (n + 1)) • (⊤ : Submodule R M)) :
    ∃ c : (Fin rs.length →₀ ℕ) →₀ M,
      (∀ e ∈ c.support, e.degree = n) ∧
      (∀ e ∈ c.support, c e ∈ Ideal.ofList rs • (⊤ : Submodule R M)) ∧
      Finset.sum c.support (fun e ↦ (∏ i : Fin rs.length, rs.get i ^ e i) • c e) =
        Finset.sum a.support fun e ↦ (∏ i : Fin rs.length, rs.get i ^ e i) • a e := by
  classical
  -- TODO: rewrite the stage condition as membership in `Ideal.ofList rs • stage n`, expand by
  -- `Submodule.smul_induction_on'`, represent the stage-`n` summands by
  -- `same_degree_family_of_mem_stage`, and keep the coefficients inside `Ideal.ofList rs • ⊤`
  -- by scaling those families.
  let J : Ideal R := Ideal.ofList rs
  let x :=
    Finset.sum a.support fun e ↦ (∏ i : Fin rs.length, rs.get i ^ e i) • a e
  have hx : x ∈ J • idealAssociatedGradedStage J M n := by
    -- Rewrite the next stage `J ^ (n + 1) M` as `J • (J ^ n M)`.
    simpa [J, x, idealAssociatedGradedStage, pow_succ, Ideal.mul_comm, mul_smul] using hstage
  have hcorr :
      ∃ c : (Fin rs.length →₀ ℕ) →₀ M,
        (∀ e ∈ c.support, e.degree = n) ∧
        (∀ e ∈ c.support, c e ∈ J • (⊤ : Submodule R M)) ∧
        Finset.sum c.support (fun e ↦ (∏ i : Fin rs.length, rs.get i ^ e i) • c e) = x := by
    refine Submodule.smul_induction_on' hx ?_ ?_
    · intro r hr y hy
      rcases same_degree_family_of_mem_stage (M := M) (rs := rs) (n := n) hy with
        ⟨b, hb_deg, hb_sum⟩
      refine ⟨r • b, ?_, ?_, ?_⟩
      · -- Scaling the stage-`n` family does not change its common degree.
        exact homogeneous_smul_of_same_degree (M := M) (rs := rs) (n := n) r hb_deg
      · intro e he
        -- Every scaled coefficient lies in `J • ⊤` because `r ∈ J`.
        exact Submodule.smul_mem_smul hr (by simp : b e ∈ (⊤ : Submodule R M))
      · -- The weighted sum scales by the same scalar.
        rw [weighted_sum_smul_family, hb_sum]
    · intro x hx y hy hx_corr hy_corr
      rcases hx_corr with ⟨cx, hcx_deg, hcx_coeff, hcx_sum⟩
      rcases hy_corr with ⟨cy, hcy_deg, hcy_coeff, hcy_sum⟩
      refine ⟨cx + cy, ?_, ?_, ?_⟩
      · -- Homogeneity survives addition of the two correction families.
        exact homogeneous_add_of_same_degree (M := M) (rs := rs) (n := n) hcx_deg hcy_deg
      · -- Extend coefficient control off support so the sum family inherits it pointwise.
        have hcx_all :=
          coeff_mem_submodule_of_support (M := M) (rs := rs) (S := J • (⊤ : Submodule R M))
            hcx_coeff
        have hcy_all :=
          coeff_mem_submodule_of_support (M := M) (rs := rs) (S := J • (⊤ : Submodule R M))
            hcy_coeff
        intro e he
        exact Submodule.add_mem _ (hcx_all e) (hcy_all e)
      · -- Weighted sums are additive across the correction families.
        rw [weighted_support_sum_add, hcx_sum, hcy_sum]
  simpa [J, x] using hcorr

/-- Helper for Lemma 10.69.2: lift a prefix-indexed family to a snoc family concentrated in last
exponent `k`. -/
private noncomputable def snoc_family_lift {fs : List R} (k : ℕ)
    (b : (Fin fs.length →₀ ℕ) →₀ M) :
    (Fin (fs.length + 1) →₀ ℕ) →₀ M :=
  b.embDomain ⟨fun e ↦ snoc_exponent (fs := fs) e k, snoc_exponent_injective (fs := fs) k⟩

/-- Helper for Lemma 10.69.2: the weighted sum of a lifted snoc family is the corresponding prefix
weighted sum with the expected factor `r ^ k`. -/
private theorem snoc_family_lift_weighted_sum
    {fs : List R} {r : R} (k : ℕ) (b : (Fin fs.length →₀ ℕ) →₀ M) :
    (snoc_family_lift (M := M) (fs := fs) k b).sum
        (fun e m ↦
          (∏ i : Fin (fs.length + 1), (fs ++ [r]).get (snoc_index_cast fs r i) ^ e i) • m) =
      b.sum
        (fun d m ↦ (∏ i : Fin fs.length, fs.get i ^ d i) • ((r ^ k) • m)) := by
  let f : (Fin fs.length →₀ ℕ) ↪ (Fin (fs.length + 1) →₀ ℕ) :=
    ⟨fun e ↦ snoc_exponent (fs := fs) e k, snoc_exponent_injective (fs := fs) k⟩
  -- Reindex the lifted family back to the prefix support, then normalize the snoc monomial weight.
  calc
    (snoc_family_lift (M := M) (fs := fs) k b).sum
        (fun e m ↦
          (∏ i : Fin (fs.length + 1), (fs ++ [r]).get (snoc_index_cast fs r i) ^ e i) • m) =
      b.sum
        (fun d m ↦
          (∏ i : Fin (fs.length + 1),
            (fs ++ [r]).get (snoc_index_cast fs r i) ^ snoc_exponent (fs := fs) d k i) • m) := by
            simpa [snoc_family_lift, f] using
              (Finsupp.sum_embDomain
                (v := b)
                (f := f)
                (g := fun e m ↦
                  (∏ i : Fin (fs.length + 1),
                    (fs ++ [r]).get (snoc_index_cast fs r i) ^ e i) • m))
    _ =
      b.sum (fun d m ↦ (∏ i : Fin fs.length, fs.get i ^ d i) • ((r ^ k) • m)) := by
        refine Finsupp.sum_congr ?_
        intro d m
        rw [snoc_exponent_weight (fs := fs) (r := r) d k]
        simp [smul_smul]

/-- Helper for Lemma 10.69.2: lifting the exact last-exponent slice back to the snoc index type
recovers exactly the filtered family with that last exponent. -/
private theorem snoc_family_lift_last_exponent_slice
    {fs : List R} {a : (Fin (fs.length + 1) →₀ ℕ) →₀ M} (l : ℕ) :
    snoc_family_lift (M := M) (fs := fs) l (last_exponent_slice (fs := fs) a l) =
      a.filter fun e ↦ e (Fin.last fs.length) = l := by
  let f : (Fin fs.length →₀ ℕ) ↪ (Fin (fs.length + 1) →₀ ℕ) :=
    ⟨fun e ↦ snoc_exponent (fs := fs) e l, snoc_exponent_injective (fs := fs) l⟩
  let exactFamily : (Fin (fs.length + 1) →₀ ℕ) →₀ M :=
    a.filter fun e ↦ e (Fin.last fs.length) = l
  have hrange : (↑exactFamily.support : Set (Fin (fs.length + 1) →₀ ℕ)) ⊆ Set.range f := by
    intro e he
    have hl : e (Fin.last fs.length) = l := by
      change e ∈ (a.filter fun e ↦ e (Fin.last fs.length) = l).support at he
      rw [Finsupp.support_filter] at he
      exact (Finset.mem_filter.mp he).2
    refine ⟨e.comapDomain Fin.castSucc ((Fin.castSucc_injective _).injOn), ?_⟩
    simpa [f] using snoc_exponent_comap_castSucc_eq (fs := fs) (e := e) hl
  -- The slice is defined by `comapDomain` along the snoc embedding, so `embDomain` inverts it on
  -- the exact-last-exponent support.
  simpa [snoc_family_lift, last_exponent_slice, exactFamily, f] using
    (Finsupp.embDomain_comapDomain (f := f) (g := exactFamily) hrange)

/-- Helper for Lemma 10.69.2: lifting a homogeneous prefix family to last exponent `k` raises the
common degree by exactly `k`. -/
private theorem snoc_family_lift_homogeneous
    {fs : List R} {m k : ℕ} {b : (Fin fs.length →₀ ℕ) →₀ M}
    (hb : ∀ d ∈ b.support, d.degree = m) :
    ∀ e ∈ (snoc_family_lift (M := M) (fs := fs) k b).support, e.degree = m + k := by
  let f : (Fin fs.length →₀ ℕ) ↪ (Fin (fs.length + 1) →₀ ℕ) :=
    ⟨fun d ↦ snoc_exponent (fs := fs) d k, snoc_exponent_injective (fs := fs) k⟩
  intro e he
  -- Every lifted support exponent comes from a unique prefix exponent, so the degree transport is
  -- exactly `snoc_exponent_degree`.
  have he' : e ∈ b.support.map f := by
    simpa [snoc_family_lift, f] using he
  rcases Finset.mem_map.mp he' with ⟨d, hd, rfl⟩
  have hddeg : d.degree = m := hb d hd
  simpa [f, hddeg] using snoc_exponent_degree (fs := fs) d k

/-- Helper for Lemma 10.69.2: every support exponent of a lifted snoc family has the prescribed
last coordinate. -/
private theorem snoc_family_lift_last_exponent_eq
    {fs : List R} {k : ℕ} {b : (Fin fs.length →₀ ℕ) →₀ M} :
    ∀ e ∈ (snoc_family_lift (M := M) (fs := fs) k b).support, e (Fin.last fs.length) = k := by
  let f : (Fin fs.length →₀ ℕ) ↪ (Fin (fs.length + 1) →₀ ℕ) :=
    ⟨fun d ↦ snoc_exponent (fs := fs) d k, snoc_exponent_injective (fs := fs) k⟩
  intro e he
  -- Every lifted support element is obtained from a snoc exponent with tail `k`.
  have he' : e ∈ b.support.map f := by
    simpa [snoc_family_lift, f] using he
  rcases Finset.mem_map.mp he' with ⟨d, hd, rfl⟩
  simpa using snoc_exponent_last (fs := fs) d k

/-- Helper for Lemma 10.69.2: evaluating a lifted snoc family on the image of a prefix exponent
recovers the original coefficient. -/
private theorem snoc_family_lift_coeff_apply
    {fs : List R} {k : ℕ} {b : (Fin fs.length →₀ ℕ) →₀ M}
    (d : Fin fs.length →₀ ℕ) :
    snoc_family_lift (M := M) (fs := fs) k b (snoc_exponent (fs := fs) d k) = b d := by
  let f : (Fin fs.length →₀ ℕ) ↪ (Fin (fs.length + 1) →₀ ℕ) :=
    ⟨fun e ↦ snoc_exponent (fs := fs) e k, snoc_exponent_injective (fs := fs) k⟩
  -- `snoc_family_lift` is just `embDomain` along the snoc embedding, so its coefficient at an
  -- embedded exponent is the original coefficient.
  simpa [snoc_family_lift, f] using Finsupp.embDomain_apply_self f b d

/-- Helper for Lemma 10.69.2: the snoc-weighted support sum of a difference is the corresponding
difference of snoc-weighted support sums. -/
private theorem snoc_weighted_support_sum_sub
    {fs : List R} {r : R}
    (a b : (Fin (fs.length + 1) →₀ ℕ) →₀ M) :
    (Finset.sum (a - b).support fun e ↦
      (∏ i : Fin (fs.length + 1), (fs ++ [r]).get (snoc_index_cast fs r i) ^ e i) • (a - b) e) =
        (Finset.sum a.support fun e ↦
          (∏ i : Fin (fs.length + 1), (fs ++ [r]).get (snoc_index_cast fs r i) ^ e i) • a e) -
        (Finset.sum b.support fun e ↦
          (∏ i : Fin (fs.length + 1), (fs ++ [r]).get (snoc_index_cast fs r i) ^ e i) • b e) := by
  -- Rewrite each support-indexed sum as `Finsupp.sum`, then use additivity of the coefficient
  -- family under subtraction.
  rw [show (Finset.sum (a - b).support fun e ↦
      (∏ i : Fin (fs.length + 1), (fs ++ [r]).get (snoc_index_cast fs r i) ^ e i) • (a - b) e) =
      (a - b).sum (fun e m ↦
        (∏ i : Fin (fs.length + 1), (fs ++ [r]).get (snoc_index_cast fs r i) ^ e i) • m) by
      rw [Finsupp.sum]]
  rw [show (Finset.sum a.support fun e ↦
      (∏ i : Fin (fs.length + 1), (fs ++ [r]).get (snoc_index_cast fs r i) ^ e i) • a e) =
      a.sum (fun e m ↦
        (∏ i : Fin (fs.length + 1), (fs ++ [r]).get (snoc_index_cast fs r i) ^ e i) • m) by
      rw [Finsupp.sum]]
  rw [show (Finset.sum b.support fun e ↦
      (∏ i : Fin (fs.length + 1), (fs ++ [r]).get (snoc_index_cast fs r i) ^ e i) • b e) =
      b.sum (fun e m ↦
        (∏ i : Fin (fs.length + 1), (fs ++ [r]).get (snoc_index_cast fs r i) ^ e i) • m) by
      rw [Finsupp.sum]]
  rw [Finsupp.sum_sub_index]
  · intro e m₁ m₂
    simp [smul_sub]

/-- Helper for Lemma 10.69.2: in a bounded homogeneous zero-weighted snoc family, the explicit
prefix coefficient criterion forces every coefficient of the exact last-exponent slice into the
prefix ideal submodule. -/
private theorem last_exponent_slice_coeff_mem_prefix_ideal_from_prefix_kernel
    {fs : List R} {r : R} (hreg : IsRegular M (fs ++ [r]))
    (hprefix_coeff :
      ∀ {m : ℕ} {b : (Fin fs.length →₀ ℕ) →₀ M},
        (∀ d ∈ b.support, d.degree = m) →
        quasiRegularSequenceAssociatedGradedMap M fs
          (b.sum fun d x ↦
            ((Submodule.Quotient.mk x :
                M ⧸ ((Ideal.ofList fs) • (⊤ : Submodule R M))) ⊗ₜ[R ⧸ Ideal.ofList fs]
              MvPolynomial.monomial d (1 : R ⧸ Ideal.ofList fs))) = 0 →
        ∀ d ∈ b.support, b d ∈ Ideal.ofList fs • (⊤ : Submodule R M))
    {n l : ℕ}
    {a : (Fin (fs.length + 1) →₀ ℕ) →₀ M}
    (hdeg : ∀ e ∈ a.support, e.degree = n)
    (hl : l ≤ n)
    (hbound : ∀ e ∈ a.support, e (Fin.last fs.length) ≤ l)
    (hzero :
      (a.sum fun e m ↦
        (∏ i : Fin (fs.length + 1), (fs ++ [r]).get (snoc_index_cast fs r i) ^ e i) • m) = 0) :
    ∀ d ∈ (last_exponent_slice (fs := fs) a l).support,
      last_exponent_slice (fs := fs) a l d ∈ Ideal.ofList fs • (⊤ : Submodule R M) := by
  classical
  let slice : (Fin fs.length →₀ ℕ) →₀ M := last_exponent_slice (fs := fs) a l
  let scaled : (Fin fs.length →₀ ℕ) →₀ M := (r ^ l) • slice
  have hatrunc :
      (a.filter fun e ↦ e (Fin.last fs.length) ≤ l) = a := by
    -- The support bound says the truncation at level `l` does not remove any coefficient.
    ext e
    by_cases he : e ∈ a.support
    · have hle : e (Fin.last fs.length) ≤ l := hbound e he
      simp [Finsupp.filter_apply, hle]
    · have hzero' : a e = 0 := Finsupp.notMem_support_iff.mp he
      simp [Finsupp.filter_apply, hzero']
  have hslice_deg :
      ∀ d ∈ slice.support, d.degree = n - l := by
    -- The exact-`l` slice has complementary degree `n - l`.
    simpa [slice] using
      last_exponent_slice_homogeneous (M := M) (fs := fs) (a := a) (n := n) (l := l) hdeg
  have htrunc_stage :
      let atrunc : (Fin (fs.length + 1) →₀ ℕ) →₀ M :=
        a.filter fun e ↦ e (Fin.last fs.length) ≤ l
      (atrunc.sum fun e m ↦
        (∏ i : Fin (fs.length + 1), (fs ++ [r]).get (snoc_index_cast fs r i) ^ e i) • m) ∈
          ((Ideal.ofList fs) ^ (n - l + 1)) • (⊤ : Submodule R M) := by
    -- After truncation nothing changes, so the weighted sum is still zero and hence in every
    -- stage.
    simpa [hatrunc] using
      (show (a.sum fun e m ↦
          (∏ i : Fin (fs.length + 1), (fs ++ [r]).get (snoc_index_cast fs r i) ^ e i) • m) ∈
            ((Ideal.ofList fs) ^ (n - l + 1)) • (⊤ : Submodule R M) from by
          rw [hzero]
          simp)
  have hslice_stage :
      (slice.sum fun d m ↦
        (∏ i : Fin fs.length, fs.get i ^ d i) • ((r ^ l) • m)) ∈
          ((Ideal.ofList fs) ^ (n - l + 1)) • (⊤ : Submodule R M) := by
    -- The truncated weighted sum isolates the exact-`l` slice in the prefix stage.
    simpa [slice, hatrunc] using
      last_exponent_slice_weighted_sum_mem_prefix_stage
        (M := M) (fs := fs) (r := r) (a := a) (n := n) (l := l) hdeg hl htrunc_stage
  have hscaled_deg :
      ∀ d ∈ scaled.support, d.degree = n - l := by
    -- Scaling the slice by `r ^ l` does not change its degree support.
    simpa [scaled] using
      homogeneous_smul_of_same_degree (M := M) (rs := fs) (r := r ^ l) hslice_deg
  have hscaled_stage :
      (Finset.sum scaled.support fun d ↦
        (∏ i : Fin fs.length, fs.get i ^ d i) • scaled d) ∈
          ((Ideal.ofList fs) ^ (n - l + 1)) • (⊤ : Submodule R M) := by
    have hscaled_sum :
        (Finset.sum scaled.support fun d ↦
          (∏ i : Fin fs.length, fs.get i ^ d i) • scaled d) =
          slice.sum fun d m ↦
            (∏ i : Fin fs.length, fs.get i ^ d i) • ((r ^ l) • m) := by
      -- Repackage the scaled slice as the weighted sum of the scaled family itself.
      calc
        (Finset.sum scaled.support fun d ↦
          (∏ i : Fin fs.length, fs.get i ^ d i) • scaled d) =
            (r ^ l) •
              (Finset.sum slice.support fun d ↦
                (∏ i : Fin fs.length, fs.get i ^ d i) • slice d) := by
              simpa [scaled] using
                weighted_sum_smul_family (M := M) (rs := fs) (r := r ^ l) slice
        _ = slice.sum fun d m ↦
              (∏ i : Fin fs.length, fs.get i ^ d i) • ((r ^ l) • m) := by
              rw [Finsupp.sum, Finset.smul_sum]
              refine Finset.sum_congr rfl ?_
              intro d hd
              simp [smul_smul, mul_assoc, mul_left_comm, mul_comm]
    rw [hscaled_sum]
    exact hslice_stage
  have hscaled_kernel :
      quasiRegularSequenceAssociatedGradedMap M fs
        (scaled.sum fun d x ↦
          ((Submodule.Quotient.mk x :
              M ⧸ ((Ideal.ofList fs) • (⊤ : Submodule R M))) ⊗ₜ[R ⧸ Ideal.ofList fs]
            MvPolynomial.monomial d (1 : R ⧸ Ideal.ofList fs))) = 0 := by
    -- The scaled slice now satisfies the homogeneous kernel criterion on the prefix sequence.
    exact homogeneous_kernel_of_weighted_sum_mem_next_stage
      (M := M) (rs := fs) (n := n - l) (a := scaled) hscaled_deg hscaled_stage
  have hscaled_coeff_support :
      ∀ d ∈ scaled.support, scaled d ∈ Ideal.ofList fs • (⊤ : Submodule R M) :=
    hprefix_coeff hscaled_deg hscaled_kernel
  have hscaled_coeff :
      ∀ d, scaled d ∈ Ideal.ofList fs • (⊤ : Submodule R M) :=
    coeff_mem_submodule_of_support
      (M := M) (rs := fs) (S := Ideal.ofList fs • (⊤ : Submodule R M)) hscaled_coeff_support
  intro d hd
  have hpow_mem :
      (r ^ l) • slice d ∈ Ideal.ofList fs • (⊤ : Submodule R M) := by
    simpa [scaled, slice] using hscaled_coeff d
  -- Cancel the factor `r ^ l` modulo the prefix ideal using regularity of the final element.
  simpa [slice] using
    last_exponent_coeff_mem_prefix_ideal_of_pow_smul_mem
      (M := M) (fs := fs) (r := r) hreg l hpow_mem

/-- Helper for Lemma 10.69.2: once the exact top slice is known to lie in the prefix ideal, it can
be replaced by a lower last-exponent correction with the same snoc-weighted sum. -/
private theorem snoc_exact_slice_lowering_weighted_sum_eq
    {fs : List R} {r : R} {l : ℕ}
    {slice b : (Fin fs.length →₀ ℕ) →₀ M}
    (hlpos : 0 < l)
    (hb_sum :
      Finset.sum b.support (fun d ↦ (∏ i : Fin fs.length, fs.get i ^ d i) • b d) =
        Finset.sum slice.support fun d ↦ (∏ i : Fin fs.length, fs.get i ^ d i) • slice d) :
    let top := snoc_family_lift (M := M) (fs := fs) l slice
    let lower := snoc_family_lift (M := M) (fs := fs) (l - 1) ((r : R) • b)
    (Finset.sum top.support fun e ↦
      (∏ i : Fin (fs.length + 1), (fs ++ [r]).get (snoc_index_cast fs r i) ^ e i) • top e) =
      (Finset.sum lower.support fun e ↦
        (∏ i : Fin (fs.length + 1), (fs ++ [r]).get (snoc_index_cast fs r i) ^ e i) • lower e) := by
  let top := snoc_family_lift (M := M) (fs := fs) l slice
  let lower := snoc_family_lift (M := M) (fs := fs) (l - 1) ((r : R) • b)
  have htop :
      Finset.sum top.support (fun e ↦
        (∏ i : Fin (fs.length + 1), (fs ++ [r]).get (snoc_index_cast fs r i) ^ e i) • top e) =
        slice.sum (fun d m ↦ (∏ i : Fin fs.length, fs.get i ^ d i) • ((r ^ l) • m)) := by
    -- Normalize the exact-top slice by the snoc lifting formula.
    simpa [top] using
      snoc_family_lift_weighted_sum (M := M) (fs := fs) (r := r) l slice
  have hlower :
      Finset.sum lower.support (fun e ↦
        (∏ i : Fin (fs.length + 1), (fs ++ [r]).get (snoc_index_cast fs r i) ^ e i) • lower e) =
        ((r : R) • b).sum
          (fun d m ↦ (∏ i : Fin fs.length, fs.get i ^ d i) • ((r ^ (l - 1)) • m)) := by
    -- The lower correction is another snoc lift, now at last exponent `l - 1`.
    simpa [lower] using
      snoc_family_lift_weighted_sum (M := M) (fs := fs) (r := r) (l - 1) ((r : R) • b)
  have hpow : r ^ l = r ^ (l - 1) * r := by
    -- Rewrite `l` as `(l - 1) + 1` so the last generator factor can be peeled off once.
    cases l with
    | zero =>
        cases Nat.lt_asymm hlpos hlpos
    | succ k =>
        simpa using pow_succ r k
  calc
    Finset.sum top.support (fun e ↦
      (∏ i : Fin (fs.length + 1), (fs ++ [r]).get (snoc_index_cast fs r i) ^ e i) • top e) =
        slice.sum (fun d m ↦ (∏ i : Fin fs.length, fs.get i ^ d i) • ((r ^ l) • m)) := htop
    _ = (r ^ l) • (Finset.sum slice.support fun d ↦ (∏ i : Fin fs.length, fs.get i ^ d i) • slice d) := by
      -- Pull the common factor `r ^ l` out of the prefix weighted sum.
      rw [Finsupp.sum, Finset.smul_sum]
      refine Finset.sum_congr rfl ?_
      intro d hd
      simp [smul_smul, mul_assoc, mul_left_comm, mul_comm]
    _ = (r ^ l) • (Finset.sum b.support fun d ↦ (∏ i : Fin fs.length, fs.get i ^ d i) • b d) := by
      rw [← hb_sum]
    _ = (r ^ (l - 1)) •
          (r • (Finset.sum b.support fun d ↦ (∏ i : Fin fs.length, fs.get i ^ d i) • b d)) := by
      -- Split off exactly one copy of `r` from `r ^ l`.
      rw [hpow, mul_smul]
    _ = (r ^ (l - 1)) •
          (Finset.sum ((r : R) • b).support fun d ↦ (∏ i : Fin fs.length, fs.get i ^ d i) • ((r : R) • b) d) := by
      rw [weighted_sum_smul_family (M := M) (rs := fs) r b]
    _ = ((r : R) • b).sum
          (fun d m ↦ (∏ i : Fin fs.length, fs.get i ^ d i) • ((r ^ (l - 1)) • m)) := by
      -- Reinsert the factor `r ^ (l - 1)` into the weighted sum over the scaled family.
      rw [Finsupp.sum, Finset.smul_sum]
      refine (Finset.sum_congr rfl ?_).symm
      intro d hd
      simp [smul_smul, mul_assoc, mul_left_comm, mul_comm]
    _ =
        Finset.sum lower.support (fun e ↦
          (∏ i : Fin (fs.length + 1), (fs ++ [r]).get (snoc_index_cast fs r i) ^ e i) • lower e) := by
      exact hlower.symm

/-- Helper for Lemma 10.69.2: subtracting the exact top slice and adding the lowered correction
forces every remaining support exponent to have strictly smaller last coordinate. -/
private theorem snoc_exact_slice_lowering_support_lt
    {fs : List R} {r : R} {l : ℕ}
    {a : (Fin (fs.length + 1) →₀ ℕ) →₀ M}
    {b : (Fin fs.length →₀ ℕ) →₀ M}
    (hlpos : 0 < l)
    (hbound : ∀ e ∈ a.support, e (Fin.last fs.length) ≤ l) :
    let top := snoc_family_lift (M := M) (fs := fs) l (last_exponent_slice (fs := fs) a l)
    let lower := snoc_family_lift (M := M) (fs := fs) (l - 1) ((r : R) • b)
    let c := top - lower
    ∀ e ∈ (a - c).support, e (Fin.last fs.length) < l := by
  -- TODO: prove the source-faithful support lowering `a - (top - lower) = (a - top) + lower`
  -- transport-stably, showing that `(a - top)` removes the exact-`l` slice while `lower` is
  -- concentrated in last exponent `l - 1`.
  sorry

/-- Helper for Lemma 10.69.2: once the exact top slice is known to lie in the prefix ideal, it can
be replaced by a lower last-exponent correction with the same snoc-weighted sum. -/
private theorem snoc_exact_slice_lowering_correction
    {fs : List R} {r : R} {n l : ℕ}
    {a : (Fin (fs.length + 1) →₀ ℕ) →₀ M}
    (hlpos : 0 < l) (hl : l ≤ n)
    (hdeg : ∀ e ∈ a.support, e.degree = n)
    (hbound : ∀ e ∈ a.support, e (Fin.last fs.length) ≤ l)
    (hexact_coeff :
      ∀ d ∈ (last_exponent_slice (fs := fs) a l).support,
        last_exponent_slice (fs := fs) a l d ∈ Ideal.ofList fs • (⊤ : Submodule R M)) :
    ∃ c : (Fin (fs.length + 1) →₀ ℕ) →₀ M,
      (∀ e ∈ c.support, e.degree = n) ∧
      (∀ e ∈ c.support, c e ∈ Ideal.ofList (fs ++ [r]) • (⊤ : Submodule R M)) ∧
      (Finset.sum c.support fun e ↦
        (∏ i : Fin (fs.length + 1), (fs ++ [r]).get (snoc_index_cast fs r i) ^ e i) • c e) = 0 ∧
      (∀ e ∈ (a - c).support, e (Fin.last fs.length) < l) := by
  -- TODO: construct `c = top - lower` from the exact slice `slice := last_exponent_slice a l`,
  -- prove coefficient control in the snoc ideal, use
  -- `snoc_exact_slice_lowering_weighted_sum_eq` for the zero weighted sum, and finish with
  -- `snoc_exact_slice_lowering_support_lt`.
  sorry

/-- Helper for Lemma 10.69.2: a corrected homogeneous snoc family with zero weighted sum has all
coefficients in the snoc ideal. -/
private theorem snoc_bounded_zero_weighted_sum_descent_on_append_length
    {fs : List R} {r : R} (hreg : IsRegular M (fs ++ [r]))
    (hprefix_coeff :
      ∀ {m : ℕ} {b : (Fin fs.length →₀ ℕ) →₀ M},
        (∀ d ∈ b.support, d.degree = m) →
        quasiRegularSequenceAssociatedGradedMap M fs
          (b.sum fun d x ↦
            ((Submodule.Quotient.mk x :
                M ⧸ ((Ideal.ofList fs) • (⊤ : Submodule R M))) ⊗ₜ[R ⧸ Ideal.ofList fs]
              MvPolynomial.monomial d (1 : R ⧸ Ideal.ofList fs))) = 0 →
        ∀ d ∈ b.support, b d ∈ Ideal.ofList fs • (⊤ : Submodule R M))
    {n l : ℕ} {a : (Fin (fs.length + 1) →₀ ℕ) →₀ M}
    (hdeg : ∀ e ∈ a.support, e.degree = n)
    (hzero :
      (a.sum fun e m ↦
        (∏ i : Fin (fs.length + 1), (fs ++ [r]).get (snoc_index_cast fs r i) ^ e i) • m) = 0)
    (hl : l ≤ n)
    (hbound : ∀ e ∈ a.support, e (Fin.last fs.length) ≤ l) :
    ∀ e ∈ a.support, a e ∈ Ideal.ofList (fs ++ [r]) • (⊤ : Submodule R M) := by
  classical
  induction l generalizing a with
  | zero =>
      intro e he
      have hlast : e (Fin.last fs.length) = 0 := by
        exact Nat.eq_zero_of_le_zero (hbound e he)
      have hexact_coeff :=
        last_exponent_slice_coeff_mem_prefix_ideal_from_prefix_kernel
          (M := M) (fs := fs) (r := r) hreg hprefix_coeff hdeg (l := 0) (by simp) hbound hzero
      let d : Fin fs.length →₀ ℕ :=
        e.comapDomain Fin.castSucc ((Fin.castSucc_injective _).injOn)
      have hsnoc : snoc_exponent (fs := fs) d 0 = e := by
        simpa [d] using snoc_exponent_comap_castSucc_eq (fs := fs) (e := e) hlast
      have hd_support : d ∈ (last_exponent_slice (fs := fs) a 0).support := by
        rw [Finsupp.mem_support_iff]
        rw [last_exponent_slice_apply, hsnoc]
        simpa [hlast] using Finsupp.mem_support_iff.mp he
      have hd_mem :
          last_exponent_slice (fs := fs) a 0 d ∈ Ideal.ofList fs • (⊤ : Submodule R M) :=
        hexact_coeff d hd_support
      have hcoeff :
          a e = last_exponent_slice (fs := fs) a 0 d := by
        rw [last_exponent_slice_apply, hsnoc]
        simp [hlast]
      have ha_prefix :
          a e ∈ Ideal.ofList fs • (⊤ : Submodule R M) := by
        simpa [hcoeff] using hd_mem
      exact prefix_ideal_smul_le_snoc_ideal_smul (M := M) fs r ha_prefix
  | succ l ih =>
      have hexact_coeff :=
        last_exponent_slice_coeff_mem_prefix_ideal_from_prefix_kernel
          (M := M) (fs := fs) (r := r) hreg hprefix_coeff hdeg
          (l := l + 1) hl hbound hzero
      rcases snoc_exact_slice_lowering_correction
          (M := M) (fs := fs) (r := r) (n := n) (l := l + 1) (a := a)
          (Nat.succ_pos l) hl hdeg hbound hexact_coeff with
          ⟨c, hcdeg, hccoeff, hczero, hclt⟩
      have hsub_deg :
          ∀ e ∈ (a - c).support, e.degree = n := by
        -- Subtracting a same-degree correction preserves homogeneity.
        intro e he
        by_cases hea : e ∈ a.support
        · exact hdeg e hea
        · have hce : e ∈ c.support := by
            rw [Finsupp.mem_support_iff] at he hea ⊢
            have haZero : a e = 0 := by
              simpa using hea
            intro hzero
            apply he
            simp [haZero, hzero]
          exact hcdeg e hce
      have hsub_bound :
          ∀ e ∈ (a - c).support, e (Fin.last fs.length) ≤ l := by
        intro e heSub
        exact Nat.le_of_lt_succ (hclt e heSub)
      have hsub_zero :
          ((a - c).sum fun e m ↦
            (∏ i : Fin (fs.length + 1), (fs ++ [r]).get (snoc_index_cast fs r i) ^ e i) • m) = 0 := by
        -- Both the original family and the correction have zero weighted sum, so their difference
        -- still has zero weighted sum.
        rw [Finsupp.sum, snoc_weighted_support_sum_sub]
        rw [Finsupp.sum] at hzero
        rw [hzero, hczero]
        simp
      have hsub_coeff :
          ∀ e ∈ (a - c).support, (a - c) e ∈ Ideal.ofList (fs ++ [r]) • (⊤ : Submodule R M) := by
        -- The correction lowers the last-exponent bound from `l + 1` to `l`, so the inductive
        -- hypothesis applies to `a - c`.
        exact ih hsub_deg hsub_zero (Nat.le_of_succ_le hl) hsub_bound
      intro e he
      have hc :
          c e ∈ Ideal.ofList (fs ++ [r]) • (⊤ : Submodule R M) := by
        by_cases hce : e ∈ c.support
        · exact hccoeff e hce
        · have hzero : c e = 0 := Finsupp.notMem_support_iff.mp hce
          simpa [hzero]
      by_cases hsube : e ∈ (a - c).support
      · have hsub_mem :
            (a - c) e ∈ Ideal.ofList (fs ++ [r]) • (⊤ : Submodule R M) := hsub_coeff e hsube
        have hsplit : a e = (a - c) e + c e := by
          simp [sub_eq_add_neg, add_assoc]
        rw [hsplit]
        exact Submodule.add_mem _ hsub_mem hc
      · have hzero : (a - c) e = 0 := Finsupp.notMem_support_iff.mp hsube
        have hEq : a e = c e := by
          have := congrArg (fun m : M ↦ m + c e) hzero
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
        simpa [hEq] using hc

/-- Helper for Lemma 10.69.2: the bounded snoc descent closes the zero-weighted case by starting
from the a priori bound `last exponent ≤ n`. -/
private abbrev snoc_append_length_index_equiv {fs : List R} (r : R) :
    Fin (fs.length + 1) ≃ Fin (fs ++ [r]).length :=
  finCongr (snoc_length_eq fs r).symm

/-- Helper for Lemma 10.69.2: reindex exponent vectors between the custom snoc model
`Fin (fs.length + 1)` and the append-length model `Fin (fs ++ [r]).length`. -/
private abbrev snoc_append_length_exponent_equiv {fs : List R} (r : R) :
    (Fin (fs.length + 1) →₀ ℕ) ≃+ (Fin (fs ++ [r]).length →₀ ℕ) :=
  Finsupp.domCongr (snoc_append_length_index_equiv (fs := fs) r)

/-- Helper for Lemma 10.69.2: reindexing exponent vectors between the two snoc presentations
preserves total degree. -/
private theorem snoc_append_length_exponent_degree
    {fs : List R} {r : R} (e : Fin (fs.length + 1) →₀ ℕ) :
    (snoc_append_length_exponent_equiv (fs := fs) r e).degree = e.degree := by
  -- TODO: package the append-length/custom-snoc exponent transport so total degree is preserved
  -- definitionally enough for the final descent adapter.
  sorry

/-- Helper for Lemma 10.69.2: the inverse reindexing between the append-length and custom snoc
presentations also preserves total degree. -/
private theorem snoc_append_length_exponent_symm_degree
    {fs : List R} {r : R} (e : Fin (fs ++ [r]).length →₀ ℕ) :
    ((snoc_append_length_exponent_equiv (fs := fs) r).symm e).degree = e.degree := by
  -- TODO: prove the inverse degree-preservation lemma for the same transport package.
  sorry

/-- Helper for Lemma 10.69.2: the snoc monomial weight in the custom model matches the ordinary
append-length monomial weight after reindexing exponents. -/
private theorem snoc_append_length_exponent_weight
    {fs : List R} (r : R) (e : Fin (fs.length + 1) →₀ ℕ) :
    (∏ i : Fin (fs.length + 1), (fs ++ [r]).get (snoc_index_cast fs r i) ^ e i) =
      (∏ j : Fin (fs ++ [r]).length,
        (fs ++ [r]).get j ^ (snoc_append_length_exponent_equiv (fs := fs) r e) j) := by
  -- TODO: show that the monomial product computed in the custom snoc model matches the ordinary
  -- append-length product after reindexing exponents.
  sorry

/-- Helper for Lemma 10.69.2: the monomial-weight identity remains true after transporting an
append-length exponent vector back to the custom snoc model. -/
private theorem snoc_append_length_exponent_symm_weight
    {fs : List R} (r : R) (e : Fin (fs ++ [r]).length →₀ ℕ) :
    (∏ i : Fin (fs.length + 1),
        (fs ++ [r]).get (snoc_index_cast fs r i) ^
          ((snoc_append_length_exponent_equiv (fs := fs) r).symm e) i) =
      (∏ j : Fin (fs ++ [r]).length, (fs ++ [r]).get j ^ e j) := by
  simpa using
    snoc_append_length_exponent_weight (fs := fs) (r := r)
      ((snoc_append_length_exponent_equiv (fs := fs) r).symm e)

/-- Helper for Lemma 10.69.2: the bounded snoc descent closes the zero-weighted case by starting
from the a priori bound `last exponent ≤ n`. -/
private theorem zero_weighted_sum_snoc_coeff_mem_ideal
    {fs : List R} {r : R} (hreg : IsRegular M (fs ++ [r]))
    (hprefix_coeff :
      ∀ {m : ℕ} {b : (Fin fs.length →₀ ℕ) →₀ M},
        (∀ d ∈ b.support, d.degree = m) →
        quasiRegularSequenceAssociatedGradedMap M fs
          (b.sum fun d x ↦
            ((Submodule.Quotient.mk x :
                M ⧸ ((Ideal.ofList fs) • (⊤ : Submodule R M))) ⊗ₜ[R ⧸ Ideal.ofList fs]
              MvPolynomial.monomial d (1 : R ⧸ Ideal.ofList fs))) = 0 →
        ∀ d ∈ b.support, b d ∈ Ideal.ofList fs • (⊤ : Submodule R M))
    {n : ℕ} {a : (Fin (fs ++ [r]).length →₀ ℕ) →₀ M}
    (hdeg : ∀ e ∈ a.support, e.degree = n)
    (hzero :
      (Finset.sum a.support fun e ↦
        (∏ i : Fin (fs ++ [r]).length, (fs ++ [r]).get i ^ e i) • a e) = 0) :
    ∀ e ∈ a.support, a e ∈ Ideal.ofList (fs ++ [r]) • (⊤ : Submodule R M) := by
  -- TODO: transport the append-length family to the custom snoc model, apply
  -- `snoc_bounded_zero_weighted_sum_descent_on_append_length` at bound `l = n`, and transport the
  -- coefficient conclusion back through the explicit exponent equivalence package.
  sorry

/-- Helper for Lemma 10.69.2: after replacing a homogeneous kernel family by a same-degree
correction with ideal-valued coefficients and the same weighted sum, the corrected family remains
homogeneous, stays in the source kernel, and has zero weighted support sum. -/
private theorem sub_correction_zero_weighted_sum
    {rs : List R} {n : ℕ} {a c : (Fin rs.length →₀ ℕ) →₀ M}
    (ha : ∀ e ∈ a.support, e.degree = n)
    (hc : ∀ e ∈ c.support, e.degree = n)
    (hker :
      quasiRegularSequenceAssociatedGradedMap M rs
        (a.sum fun e m ↦
          ((Submodule.Quotient.mk m :
              M ⧸ ((Ideal.ofList rs) • (⊤ : Submodule R M))) ⊗ₜ[R ⧸ Ideal.ofList rs]
            MvPolynomial.monomial e (1 : R ⧸ Ideal.ofList rs))) = 0)
    (hcoeff : ∀ e ∈ c.support, c e ∈ Ideal.ofList rs • (⊤ : Submodule R M))
    (hsum :
      (Finset.sum c.support fun e ↦ (∏ i : Fin rs.length, rs.get i ^ e i) • c e) =
        Finset.sum a.support fun e ↦ (∏ i : Fin rs.length, rs.get i ^ e i) • a e) :
    let a₀ := a - c
    (∀ e ∈ a₀.support, e.degree = n) ∧
      quasiRegularSequenceAssociatedGradedMap M rs
        (a₀.sum fun e m ↦
          ((Submodule.Quotient.mk m :
              M ⧸ ((Ideal.ofList rs) • (⊤ : Submodule R M))) ⊗ₜ[R ⧸ Ideal.ofList rs]
            MvPolynomial.monomial e (1 : R ⧸ Ideal.ofList rs))) = 0 ∧
      (Finset.sum a₀.support fun e ↦ (∏ i : Fin rs.length, rs.get i ^ e i) • a₀ e) = 0 := by
  let a₀ : (Fin rs.length →₀ ℕ) →₀ M := a - c
  have hkernel_a₀ :
      quasiRegularSequenceAssociatedGradedMap M rs
        (a₀.sum fun e m ↦
          ((Submodule.Quotient.mk m :
              M ⧸ ((Ideal.ofList rs) • (⊤ : Submodule R M))) ⊗ₜ[R ⧸ Ideal.ofList rs]
            MvPolynomial.monomial e (1 : R ⧸ Ideal.ofList rs))) = 0 := by
    -- The correction already vanishes in the quotient source, so subtracting it preserves the
    -- kernel relation.
    simpa [a₀] using
      kernel_family_sub_of_coeff_mem_ideal (M := M) (rs := rs) (a := a) (c := c) hker hcoeff
  have hsum_a₀ :
      (Finset.sum a₀.support fun e ↦ (∏ i : Fin rs.length, rs.get i ^ e i) • a₀ e) = 0 := by
    -- The weighted support sum is additive in the coefficient family, so equal weighted sums
    -- cancel after subtraction.
    have hsub :
        a₀.sum (fun e m ↦ (∏ i : Fin rs.length, rs.get i ^ e i) • m) =
          a.sum (fun e m ↦ (∏ i : Fin rs.length, rs.get i ^ e i) • m) -
            c.sum (fun e m ↦ (∏ i : Fin rs.length, rs.get i ^ e i) • m) := by
      rw [show a₀ = a - c by rfl, Finsupp.sum_sub_index]
      intro e m₁ m₂
      simp [smul_sub]
    have hsum' :
        c.sum (fun e m ↦ (∏ i : Fin rs.length, rs.get i ^ e i) • m) =
          a.sum (fun e m ↦ (∏ i : Fin rs.length, rs.get i ^ e i) • m) := by
      simpa [Finsupp.sum] using hsum
    rw [show (Finset.sum a₀.support fun e ↦ (∏ i : Fin rs.length, rs.get i ^ e i) • a₀ e) =
        a₀.sum (fun e m ↦ (∏ i : Fin rs.length, rs.get i ^ e i) • m) by
        rw [Finsupp.sum]]
    rw [hsub, hsum']
    simp
  refine ⟨?_, hkernel_a₀, hsum_a₀⟩
  -- The corrected family stays homogeneous because both summands are homogeneous of degree `n`.
  simpa [a₀] using homogeneous_sub_of_same_degree (M := M) (rs := rs) (n := n) ha hc

/-- Helper for Lemma 10.69.2: a homogeneous kernel relation for the associated-graded map has all
coefficients in `Ideal.ofList rs • ⊤`. -/
private theorem homogeneous_kernel_coeff_mem_ideal
    {rs : List R} (hreg : IsRegular M rs) {n : ℕ}
    {a : (Fin rs.length →₀ ℕ) →₀ M}
    (hdeg : ∀ e ∈ a.support, e.degree = n)
    (hker :
      quasiRegularSequenceAssociatedGradedMap M rs
        (a.sum fun e m ↦
          ((Submodule.Quotient.mk m :
              M ⧸ ((Ideal.ofList rs) • (⊤ : Submodule R M))) ⊗ₜ[R ⧸ Ideal.ofList rs]
            MvPolynomial.monomial e (1 : R ⧸ Ideal.ofList rs))) = 0) :
    ∀ e ∈ a.support, a e ∈ Ideal.ofList rs • (⊤ : Submodule R M) := by
  classical
  -- Route correction: the proof is organized exactly as in the source, by reverse recursion on
  -- `rs` and then descending on the last exponent in the snoc case.
  induction rs using List.reverseRecOn generalizing n with
  | nil =>
      -- The empty sequence case is already isolated above.
      exact homogeneous_kernel_coeff_mem_ideal_nil (M := M) hdeg hker
  | append_singleton fs r ih =>
      have hprefix_reg : IsRegular M fs := by
        -- Forgetting the final regular element preserves regularity of the prefix.
        exact isRegular_left_of_isRegular_append (M := M) hreg
      have hstage :
          (Finset.sum a.support fun e ↦
            (∏ i : Fin (fs ++ [r]).length, (fs ++ [r]).get i ^ e i) • a e) ∈
            ((Ideal.ofList (fs ++ [r])) ^ (n + 1)) • (⊤ : Submodule R M) := by
        -- The homogeneous kernel relation first becomes the textbook stage relation.
        exact homogeneous_weighted_sum_mem_next_stage_of_kernel
          (M := M) (rs := fs ++ [r]) (n := n) (a := a) hdeg hker
      -- Route correction: the remaining snoc argument should first replace `a` by a same-degree
      -- correction `a₀ = a - c` with `c e ∈ (f₁, ..., f_c)M` and zero weighted sum, and only then
      -- run the descending last-exponent induction on `a₀`.
      have htransfer :
          ∀ {c : (Fin (fs ++ [r]).length →₀ ℕ) →₀ M},
            (∀ e ∈ c.support,
              c e ∈ Ideal.ofList (fs ++ [r]) • (⊤ : Submodule R M)) →
            (∀ e ∈ (a - c).support,
              (a - c) e ∈ Ideal.ofList (fs ++ [r]) • (⊤ : Submodule R M)) →
            ∀ e ∈ a.support, a e ∈ Ideal.ofList (fs ++ [r]) • (⊤ : Submodule R M) := by
        intro c hcoeff hsub
        exact coeff_mem_ideal_of_sub_correction (M := M) (rs := fs ++ [r]) hsub hcoeff
      rcases same_degree_ideal_correction_of_weighted_sum_mem_next_stage
          (M := M) (rs := fs ++ [r]) (n := n) (a := a) hdeg hstage with
          ⟨c, hcdeg, hccoeff, hcsum⟩
      obtain ⟨ha0deg, ha0ker, ha0zero⟩ :=
        sub_correction_zero_weighted_sum
          (M := M) (rs := fs ++ [r]) (n := n) (a := a) (c := c)
          hdeg hcdeg hker hccoeff hcsum
      have hprefix_coeff :
          ∀ {m : ℕ} {b : (Fin fs.length →₀ ℕ) →₀ M},
            (∀ d ∈ b.support, d.degree = m) →
            quasiRegularSequenceAssociatedGradedMap M fs
              (b.sum fun d x ↦
                ((Submodule.Quotient.mk x :
                    M ⧸ ((Ideal.ofList fs) • (⊤ : Submodule R M))) ⊗ₜ[R ⧸ Ideal.ofList fs]
                  MvPolynomial.monomial d (1 : R ⧸ Ideal.ofList fs))) = 0 →
            ∀ d ∈ b.support, b d ∈ Ideal.ofList fs • (⊤ : Submodule R M) := by
        intro m b hbdeg hbker d hd
        exact ih hprefix_reg hbdeg hbker d hd
      have ha0coeff :
          ∀ e ∈ (a - c).support, (a - c) e ∈ Ideal.ofList (fs ++ [r]) • (⊤ : Submodule R M) := by
        -- After the correction step, only the source-faithful zero-weighted-sum snoc descent
        -- remains.
        exact zero_weighted_sum_snoc_coeff_mem_ideal
          (M := M) (fs := fs) (r := r) (n := n) (a := a - c) hreg hprefix_coeff ha0deg
          ha0zero
      exact htransfer hccoeff ha0coeff

/-- Lemma 10.69.2 (2): every `M`-regular sequence is `M`-quasi-regular. -/
theorem IsRegular.isQuasiRegular {rs : List R} (hreg : IsRegular M rs) :
    IsQuasiRegular M rs := by
  classical
  rw [isQuasiRegular_iff_injective]
  let J : Ideal R := Ideal.ofList rs
  let Q : Type v := M ⧸ (J • (⊤ : Submodule R M))
  let map := quasiRegularSequenceAssociatedGradedMap M rs
  have hkernel_trivial : ∀ z, map z = 0 → z = 0 := by
    intro z hz
    obtain ⟨coeffs, hcoeffs⟩ := tensor_monomial_expansion (M := M) rs z
    let lift : (Fin rs.length →₀ ℕ) → M := fun e ↦
      (Submodule.Quotient.mk_surjective (J • (⊤ : Submodule R M)) (coeffs e)).choose
    have hlift : ∀ e, (Submodule.Quotient.mk (lift e) : Q) = coeffs e := by
      intro e
      exact
        (Submodule.Quotient.mk_surjective (J • (⊤ : Submodule R M)) (coeffs e)).choose_spec
    let lifted : (Fin rs.length →₀ ℕ) →₀ M :=
      Finsupp.onFinset coeffs.support
        (fun e ↦ if e ∈ coeffs.support then lift e else 0)
        (by
          intro e hne
          by_cases he : e ∈ coeffs.support
          · exact he
          · simp [he] at hne)
    have hlifted_apply :
        ∀ e, (Submodule.Quotient.mk (lifted e) : Q) = coeffs e := by
      intro e
      by_cases he : e ∈ coeffs.support
      · -- On the visible support, `lifted` is the chosen coefficient lift.
        have hne : coeffs e ≠ 0 := Finsupp.mem_support_iff.mp he
        simp [lifted, hne, hlift e]
      · -- Outside the support, both the coefficient and the chosen lift vanish.
        have hzero : coeffs e = 0 := Finsupp.notMem_support_iff.mp he
        simp [lifted, hzero]
    have hlifted_support : lifted.support = coeffs.support := by
      refine Finset.ext fun e ↦ ?_
      constructor
      · intro he
        simpa [lifted] using
          (Finsupp.support_onFinset_subset
            (s := coeffs.support)
            (f := fun e ↦ if e ∈ coeffs.support then lift e else 0)
            (hf := by
              intro e hne
              by_cases he' : e ∈ coeffs.support
              · exact he'
              · simp [he'] at hne)
            he)
      · intro he
        have hcoeff_ne : coeffs e ≠ 0 := Finsupp.mem_support_iff.mp he
        have hlifted_ne : lifted e ≠ 0 := by
          intro hzero
          have hquot_zero : (Submodule.Quotient.mk (lifted e) : Q) = 0 := by
            simpa [hzero]
          exact hcoeff_ne (by simpa [hlifted_apply e] using hquot_zero)
        exact Finsupp.mem_support_iff.mpr hlifted_ne
    let source :=
      lifted.sum fun e m ↦
        ((Submodule.Quotient.mk m : Q) ⊗ₜ[R ⧸ J]
          MvPolynomial.monomial e (1 : R ⧸ J))
    have hsource_coeffs :
        source =
          coeffs.sum fun e q ↦
            (q ⊗ₜ[R ⧸ J] MvPolynomial.monomial e (1 : R ⧸ J)) := by
      -- Replace each chosen lift by its quotient class after identifying the supports.
      dsimp [source]
      rw [Finsupp.sum, Finsupp.sum, hlifted_support]
      refine Finset.sum_congr rfl ?_
      intro e he
      simp [hlifted_apply e]
    have hsource_eq : source = z := by
      calc
        source =
            coeffs.sum fun e q ↦
              (q ⊗ₜ[R ⧸ J] MvPolynomial.monomial e (1 : R ⧸ J)) := hsource_coeffs
        _ = z := hcoeffs.symm
    have hsource_ker : map source = 0 := by
      simpa [map, hsource_eq] using hz
    have hcoeff_zero : ∀ e, (Submodule.Quotient.mk (lifted e) : Q) = 0 := by
      intro e
      by_cases he : e ∈ lifted.support
      · let homogeneous : (Fin rs.length →₀ ℕ) →₀ M :=
          lifted.filter fun d ↦ d.degree = e.degree
        have hhomogeneous_support :
            homogeneous.support = lifted.support.filter (fun d ↦ d.degree = e.degree) := by
          simp [homogeneous, Finsupp.support_filter]
        have hhomogeneous_ker :
            map
              (homogeneous.sum fun d m ↦
                ((Submodule.Quotient.mk m : Q) ⊗ₜ[R ⧸ J]
                  MvPolynomial.monomial d (1 : R ⧸ J))) = 0 := by
          -- Project the full kernel relation to the homogeneous slice of degree `e.degree`.
          simpa [map, source, homogeneous, hhomogeneous_support] using
            kernel_family_split_by_degree (M := M) (a := lifted) e.degree hsource_ker
        have hhomogeneous_deg :
            ∀ d ∈ homogeneous.support, d.degree = e.degree := by
          intro d hd
          rw [hhomogeneous_support] at hd
          exact (Finset.mem_filter.mp hd).2
        have he_homogeneous : e ∈ homogeneous.support := by
          rw [hhomogeneous_support]
          exact Finset.mem_filter.mpr ⟨he, rfl⟩
        have hcoeff_mem :
            homogeneous e ∈ J • (⊤ : Submodule R M) := by
          exact homogeneous_kernel_coeff_mem_ideal
            (M := M) (rs := rs) hreg hhomogeneous_deg hhomogeneous_ker e he_homogeneous
        have hcoeff_eq : homogeneous e = lifted e := by
          simp [homogeneous]
        exact (Submodule.Quotient.mk_eq_zero _).2 (by simpa [Q, hcoeff_eq] using hcoeff_mem)
      · simp [Finsupp.notMem_support_iff.mp he]
    have hlifted_mem :
        ∀ e ∈ lifted.support, lifted e ∈ J • (⊤ : Submodule R M) := by
      intro e he
      exact (Submodule.Quotient.mk_eq_zero _).1 (by simpa [Q] using hcoeff_zero e)
    have hsource_zero : source = 0 := by
      -- Once every lifted coefficient lies in `J • ⊤`, each simple tensor has zero quotient class.
      exact source_tensor_sum_eq_zero_of_coeff_mem_ideal (M := M) (a := lifted) hlifted_mem
    simpa [hsource_eq] using hsource_zero
  intro z₁ z₂ hz
  have hsub : map (z₁ - z₂) = 0 := by
    simpa [map_sub] using show map z₁ - map z₂ = 0 from sub_eq_zero.mpr hz
  exact sub_eq_zero.mp (hkernel_trivial (z₁ - z₂) hsub)

/- Lemma 10.69.2 (1): the ring-valued statement is the specialization of
`IsRegular.isQuasiRegular` to the owner module `R`, so no parallel wrapper theorem is needed. -/
#check (IsRegular.isQuasiRegular : ∀ {rs : List R}, IsRegular R rs → IsQuasiRegularSequence rs)

end RingTheory.Sequence
