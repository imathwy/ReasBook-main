import Mathlib
import BauschkeLean.Chap01.Text_1_0_57
import BauschkeLean.Chap06.Fact_6_14
import BauschkeLean.Chap06.Proposition_6_21
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap09.Proposition_9_18
import BauschkeLean.Chap09.Proposition_9_30
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap13.Example_13_3
import BauschkeLean.Chap13.GammaZeroConjugate
import BauschkeLean.Chap13.Proposition_13_10
import BauschkeLean.Chap13.Proposition_13_24
import BauschkeLean.Chap13.Proposition_13_23
import BauschkeLean.Chap15.FenchelSameSpaceAttainment
import BauschkeLean.Chap15.Definition_15_19
import BauschkeLean.Chap15.Proposition_15_18
import BauschkeLean.Chap15.Proposition_15_9

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Pointwise translate InnerProductSpace

noncomputable section

universe u v

namespace ERealFunction

section FenchelRockafellarDuality

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/- 
Source/core/bridge triage:
- `source-facing`: Theorem 15.23 is the chapter's composite Fenchel--Rockafellar attainment
  theorem under the textbook regularity hypothesis
  `0 ∈ sri (effectiveDomain g - L '' effectiveDomain f)`.
- `core/canonical`: the owner objects are the Chapter 15 declarations
  `compositePrimalObjective`, `compositePrimalOptimalValue`, and `compositeDualObjective` from
  Definition 15.19.
- `bridge/view`: Proposition 15.22 and Fact 15.25 are downstream bridge results converting other
  regularity packages (`core`, polyhedral hypotheses) to this owner `sri` hypothesis.
-/

/-- Helper for Theorem 15 23: the pullback of `f` along the first projection belongs to
`Γ₀(H × K)`. -/
lemma fst_projection_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    (fun p : H × K ↦ f p.1) ∈ Γ₀(H × K) := by
  rw [mem_gammaZero_iff] at hf ⊢
  constructor
  · -- Lower semicontinuity is preserved by the continuous first projection.
    simpa using hf.1.comp continuous_fst
  · refine ⟨?_, subset_rfl, ?_⟩
    · -- A domain point of `f` lifts to a product-domain point by adjoining a zero second
      -- coordinate.
      obtain ⟨x, hx⟩ := hf.2.nonempty
      refine ⟨(x, 0), ?_⟩
      simpa [mem_effectiveDomain_iff] using hx
    · -- Convexity of the lifted function is exactly convexity of `f` on first coordinates.
      intro p hp q hq a ha0 ha1
      have hp' : p.1 ∈ effectiveDomain f := by
        simpa [mem_effectiveDomain_iff] using hp
      have hq' : q.1 ∈ effectiveDomain f := by
        simpa [mem_effectiveDomain_iff] using hq
      simpa using hf.2.ineq hp' hq' ha0 ha1

/-- Helper for Theorem 15 23: the pullback of `g` along the second projection belongs to
`Γ₀(H × K)`. -/
lemma snd_projection_mem_gammaZero
    (g : K → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(K)) :
    (fun p : H × K ↦ g p.2) ∈ Γ₀(H × K) := by
  rw [mem_gammaZero_iff] at hg ⊢
  constructor
  · -- Lower semicontinuity is preserved by the continuous second projection.
    simpa using hg.1.comp continuous_snd
  · refine ⟨?_, subset_rfl, ?_⟩
    · -- A domain point of `g` lifts to a product-domain point by adjoining a zero first
      -- coordinate.
      obtain ⟨y, hy⟩ := hg.2.nonempty
      refine ⟨(0, y), ?_⟩
      simpa [mem_effectiveDomain_iff] using hy
    · -- Convexity of the lifted function is exactly convexity of `g` on second coordinates.
      intro p hp q hq a ha0 ha1
      have hp' : p.2 ∈ effectiveDomain g := by
        simpa [mem_effectiveDomain_iff] using hp
      have hq' : q.2 ∈ effectiveDomain g := by
        simpa [mem_effectiveDomain_iff] using hq
      simpa using hg.2.ineq hp' hq' ha0 ha1

/-- Helper for Theorem 15 23: the separable product objective
`(x, y) ↦ f x + g y` belongs to `Γ₀(H × K)`. -/
lemma separable_sum_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (g : K → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(K)) :
    ((fun p : H × K ↦ f p.1) + fun p ↦ g p.2) ∈ Γ₀(H × K) := by
  have hfst : (fun p : H × K ↦ f p.1) ∈ Γ₀(H × K) :=
    fst_projection_mem_gammaZero (H := H) (K := K) f hf
  have hsnd : (fun p : H × K ↦ g p.2) ∈ Γ₀(H × K) :=
    snd_projection_mem_gammaZero (H := H) (K := K) g hg
  obtain ⟨x, hx⟩ := hf.2.nonempty
  obtain ⟨y, hy⟩ := hg.2.nonempty
  -- The two lifted effective domains intersect at a product of domain witnesses.
  refine pointwiseAdd_mem_gammaZero (fun p : H × K ↦ f p.1) (fun p ↦ g p.2) hfst hsnd ?_
  refine ⟨(x, y), ?_, ?_⟩
  · simpa [mem_effectiveDomain_iff] using hx
  · simpa [mem_effectiveDomain_iff] using hy

/-- Helper for Theorem 15 23: the textbook `sri` hypothesis on
`effectiveDomain g - L '' effectiveDomain f` is equivalent to the corresponding product-space graph
regularity hypothesis. -/
lemma zero_mem_sri_prod_sub_graph_of_zero_mem_sri_sub_image_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (g : K → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K)
    (hsri : (0 : K) ∈ sri (effectiveDomain g - L '' effectiveDomain f)) :
    (0 : H × K) ∈ sri (effectiveDomain f ×ˢ effectiveDomain g - (L.toLinearMap.graph : Set (H × K))) := by
  obtain ⟨x, hx⟩ := hf.2.nonempty
  obtain ⟨y, hy⟩ := hg.2.nonempty
  -- Proposition 6.21 is exactly the textbook bridge from the image-difference regularity
  -- condition to the product-space graph regularity condition.
  exact
    (zero_mem_strongRelativeInterior_sub_image_iff_zero_mem_strongRelativeInterior_prod_sub_graph
      (C := effectiveDomain f) (D := effectiveDomain g)
      ⟨x, hx⟩ ⟨y, hy⟩
      hf.2.convex_effectiveDomain
      hg.2.convex_effectiveDomain
      L).1 hsri

/-- Helper for Theorem 15 23: the product-space primal owner for the graph reduction has the same
optimal value as the composite primal owner. -/
lemma product_primalOptimalValue_eq_compositePrimalOptimalValue
    (f : H → Set.Ioi (⊥ : EReal))
    (g : K → Set.Ioi (⊥ : EReal))
    (L : H →L[ℝ] K) :
    primalOptimalValue
        ((fun p : H × K ↦ f p.1) + fun p ↦ g p.2)
        (ι[(L.toLinearMap.graph : Set (H × K))]) =
      compositePrimalOptimalValue f g L := by
  let F : H × K → Set.Ioi (⊥ : EReal) := (fun p : H × K ↦ f p.1) + fun p ↦ g p.2
  let G : H × K → Set.Ioi (⊥ : EReal) := ι[(L.toLinearMap.graph : Set (H × K))]
  rw [primalOptimalValue_eq_iInf_primalObjective, compositePrimalOptimalValue,
    primalOptimalValue_eq_iInf_primalObjective]
  refine le_antisymm ?_ ?_
  · -- Restrict the product infimum to the graph points `(x, L x)`.
    refine le_iInf fun x ↦ ?_
    calc
      (⨅ p : H × K, primalObjective F G p) ≤ primalObjective F G (x, L x) := iInf_le _ (x, L x)
      _ = compositePrimalObjective f g L x := by
        simp [F, G, primalObjective, compositePrimalObjective, LinearMap.mem_graph_iff]
  · -- Every product-space value dominates the composite value at its first coordinate.
    refine le_iInf fun p ↦ ?_
    by_cases hp : p.2 = L p.1
    · calc
        (⨅ x : H, compositePrimalObjective f g L x) ≤ compositePrimalObjective f g L p.1 :=
          iInf_le _ p.1
        _ = primalObjective F G p := by
          simp [F, G, primalObjective, compositePrimalObjective, LinearMap.mem_graph_iff, hp]
    · calc
        (⨅ x : H, compositePrimalObjective f g L x) ≤ ⊤ := le_top
        _ = primalObjective F G p := by
          have hF_ne_bot : (F p : EReal) ≠ ⊥ := ne_of_gt (F p).2
          have htop : ((F p : EReal) + ⊤) = ⊤ := EReal.add_top_of_ne_bot hF_ne_bot
          simpa [F, G, primalObjective, LinearMap.mem_graph_iff, hp] using htop.symm

/-- Helper for Theorem 15 23: the strong-relative-interior hypothesis already supplies
domain witnesses `a ∈ effectiveDomain f` and `b ∈ effectiveDomain g` with `b = L a`. -/
lemma exists_domain_pair_eq_image_of_zero_mem_sri_sub_image_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal))
    (g : K → Set.Ioi (⊥ : EReal))
    (L : H →L[ℝ] K)
    (hsri : (0 : K) ∈ sri (effectiveDomain g - L '' effectiveDomain f)) :
    ∃ a ∈ effectiveDomain f, ∃ b ∈ effectiveDomain g, b = L a := by
  -- Membership in `sri` first gives actual membership in the translated domain-difference set.
  rcases Set.mem_strongRelativeInterior_iff.mp hsri with ⟨hzero, _⟩
  rcases Set.mem_sub.mp hzero with ⟨b, hb, z, hz, hbz⟩
  rcases hz with ⟨a, ha, rfl⟩
  refine ⟨a, ha, b, hb, ?_⟩
  simpa using sub_eq_zero.mp hbz

/-- Helper for Theorem 15 23: for a nonempty convex set, algebraic core membership at the origin
already implies strong relative interior membership at the origin. This is the Chapter 6
`core → sri` bridge used to return from the support theorem to the source regularity hypothesis.
-/
lemma zero_mem_sri_of_zero_mem_core_of_nonempty_convex
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {S : Set E}
    (hS_nonempty : S.Nonempty) (hS_convex : Convex ℝ S)
    (hcore : (0 : E) ∈ Set.core S) :
    (0 : E) ∈ sri S := by
  rcases Set.mem_core_iff.mp hcore with ⟨hzeroS, hcone_univ⟩
  have hsub_zero : S - ({0} : Set E) = S := by
    -- Subtracting the origin does not change the regularity set at the source origin.
    ext x
    constructor
    · rintro ⟨y, hy, z, hz, hyz⟩
      rcases Set.mem_singleton_iff.mp hz with rfl
      have hyx : y = x := by simpa using hyz
      simpa [hyx] using hy
    · intro hx
      exact Set.mem_sub.mpr ⟨x, hx, 0, by simp, by simp⟩
  have hconeS : cone S = (univ : Set E) := by
    simpa [hsub_zero] using hcone_univ
  have hclosure_span :
      ((Submodule.span ℝ S).topologicalClosure : Set E) = univ := by
    apply Set.Subset.antisymm
    · simp
    · intro x hx
      have hxCone : x ∈ cone S := by simpa [hconeS]
      exact cone_subset_topologicalClosure_span S hxCone
  -- Rewrite the core criterion into the cone-equals-closed-span criterion from Proposition 6.21.
  refine
    (zero_mem_strongRelativeInterior_iff_cone_eq_closure_span_of_nonempty_convex
      hS_nonempty hS_convex).2 ?_
  calc
    cone S = (univ : Set E) := hconeS
    _ = ((Submodule.span ℝ S).topologicalClosure : Set E) := hclosure_span.symm

/-- Helper for Theorem 15 23: the algebraic-core regularity hypothesis already supplies domain
witnesses `a ∈ effectiveDomain F` and `b ∈ effectiveDomain G` with `b = M a`. This is the
source-level nonempty-intersection witness needed before translating to the zero-domain case. -/
lemma exists_domain_pair_eq_image_of_zero_mem_core_sub_image_effectiveDomain
    {X : Type*} {Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (F : X → Set.Ioi (⊥ : EReal))
    (G : Y → Set.Ioi (⊥ : EReal))
    (M : X →L[ℝ] Y)
    (hcore : (0 : Y) ∈ Set.core (effectiveDomain G - M '' effectiveDomain F)) :
    ∃ a ∈ effectiveDomain F, ∃ b ∈ effectiveDomain G, b = M a := by
  rcases Set.mem_core_iff.mp hcore with ⟨hzero, _⟩
  rcases Set.mem_sub.mp hzero with ⟨b, hb, z, hz, hbz⟩
  rcases hz with ⟨a, ha, rfl⟩
  refine ⟨a, ha, b, hb, ?_⟩
  simpa using sub_eq_zero.mp hbz

/-- Helper for Theorem 15.23: weak duality against a fixed dual vector already bounds the
composite primal optimal value from below. This packages Proposition 15.18 into the exact
pointwise form needed to certify a later minimizing dual witness. -/
lemma compositePrimalOptimalValue_ge_neg_compositeDualObjective
    {X : Type*} {Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (F : X → Set.Ioi (⊥ : EReal))
    (G : Y → Set.Ioi (⊥ : EReal))
    (M : X →L[ℝ] Y)
    (v : Y) :
    compositePrimalOptimalValue F G M ≥ -(compositeDualObjective F G M v) := by
  rw [compositePrimalOptimalValue, primalOptimalValue_eq_iInf_primalObjective]
  -- Infimize the pointwise weak-duality inequality from Proposition 15.18 over the primal variable.
  refine le_iInf fun x ↦ ?_
  simpa [compositePrimalObjective] using
    compositePrimalObjective_ge_neg_compositeDualObjective F G M x v

/-- Helper for Theorem 15 23: translating the argument of a `Γ₀` function preserves membership in
`Γ₀`. -/
lemma translate_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (a : H) :
    (fun x : H ↦ f (x + a)) ∈ Γ₀(H) := by
  rw [mem_gammaZero_iff] at hf ⊢
  constructor
  · -- Lower semicontinuity is preserved by the continuous translation `x ↦ x + a`.
    simpa using hf.1.comp (continuous_id.add continuous_const)
  · refine ⟨?_, subset_rfl, ?_⟩
    · -- Translate a domain witness of `f` back by `-a` to obtain a domain witness of the shift.
      obtain ⟨x, hx⟩ := hf.2.nonempty
      refine ⟨x - a, ?_⟩
      simpa [mem_effectiveDomain_iff, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hx
    · intro x hx y hy α hα0 hα1
      have hx' : x + a ∈ effectiveDomain f := by
        simpa [mem_effectiveDomain_iff, add_assoc, add_left_comm, add_comm] using hx
      have hy' : y + a ∈ effectiveDomain f := by
        simpa [mem_effectiveDomain_iff, add_assoc, add_left_comm, add_comm] using hy
      have hsum :
          α • a + (1 - α) • a = a := by
        rw [← add_smul, show α + (1 - α) = (1 : ℝ) by ring, one_smul]
      have harg :
          α • x + α • a + ((1 - α) • y + (1 - α) • a) =
            (α • x + (1 - α) • y) + a := by
        calc
          α • x + α • a + ((1 - α) • y + (1 - α) • a)
              = (α • x + (1 - α) • y) + (α • a + (1 - α) • a) := by
                abel
          _ = (α • x + (1 - α) • y) + a := by rw [hsum]
      -- Rewrite the convexity step at the translated points and then fold the translation back.
      simpa [smul_add, harg, add_assoc] using hf.2.ineq hx' hy' hα0 hα1

/-- Helper for Theorem 15 23: translating both primal summands by witnesses `a` and `b = L a`
does not change the owner primal optimal value. -/
lemma translated_compositePrimalOptimalValue_eq_original_of_image_domain_witness
    (f : H → Set.Ioi (⊥ : EReal))
    (g : K → Set.Ioi (⊥ : EReal))
    (L : H →L[ℝ] K)
    (a : H) (b : K)
    (hba : b = L a) :
    let φ : H → Set.Ioi (⊥ : EReal) := fun x ↦ f (x + a)
    let ψ : K → Set.Ioi (⊥ : EReal) := fun y ↦ g (y + b)
    compositePrimalOptimalValue φ ψ L = compositePrimalOptimalValue f g L := by
  dsimp
  rw [compositePrimalOptimalValue, primalOptimalValue_eq_iInf_primalObjective,
    compositePrimalOptimalValue, primalOptimalValue_eq_iInf_primalObjective]
  refine le_antisymm ?_ ?_
  · -- Reindex the translated infimum by sending `z` to `z - a`.
    refine le_iInf fun z ↦ ?_
    calc
      (⨅ x : H, primalObjective (fun x : H ↦ f (x + a)) ((fun y : K ↦ g (y + b)) ∘ L) x)
          ≤ primalObjective (fun x : H ↦ f (x + a)) ((fun y : K ↦ g (y + b)) ∘ L) (z - a) :=
            iInf_le _ (z - a)
      _ = primalObjective f (g ∘ L) z := by
            simp [primalObjective, hba, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  · -- Reindex the ambient infimum by sending `x` to `x + a`.
    refine le_iInf fun x ↦ ?_
    calc
      (⨅ z : H, primalObjective f (g ∘ L) z) ≤ primalObjective f (g ∘ L) (x + a) :=
        iInf_le _ (x + a)
      _ =
          primalObjective (fun z : H ↦ f (z + a)) ((fun y : K ↦ g (y + b)) ∘ L) x := by
            simp [primalObjective, ContinuousLinearMap.map_add, hba, add_assoc, add_left_comm,
              add_comm]

/-- Helper for Theorem 15 23: translating both primal terms by witnesses `a` and `b = L a` does
not change the owner dual objective. -/
lemma translated_compositeDualObjective_eq_original_of_image_domain_witness
    (f : H → Set.Ioi (⊥ : EReal))
    (g : K → Set.Ioi (⊥ : EReal))
    (L : H →L[ℝ] K)
    (a : H) (b : K)
    (hba : b = L a) :
    let φ : H → Set.Ioi (⊥ : EReal) := fun x ↦ f (x + a)
    let ψ : K → Set.Ioi (⊥ : EReal) := fun y ↦ g (y + b)
    compositeDualObjective φ ψ L = compositeDualObjective f g L := by
  dsimp
  funext v
  have hφeval :
      ((Function.asEReal (fun x : H ↦ f (x + a)))∗ᵛ ∘ L.adjoint) v =
        ((f.asEReal∗ᵛ ∘ L.adjoint) v) + (((⟪a, L.adjoint v⟫_ℝ : ℝ) : EReal)) := by
    simpa [Function.asEReal_apply, Function.comp, Pi.add_apply, translate_apply, sub_eq_add_neg,
      add_assoc, add_left_comm, add_comm] using
      congrFun
      (conjugate_translate_add_inner_add_const
        (f := f.asEReal) (y := -a) (v := (0 : H)) (β := 0))
      (-(L.adjoint v))
  have hψeval :
      (Function.asEReal (fun y : K ↦ g (y + b)))∗ v =
        g.asEReal∗ v - (((⟪b, v⟫_ℝ : ℝ) : EReal)) := by
    simpa [Function.asEReal_apply, Pi.add_apply, translate_apply, sub_eq_add_neg, add_assoc,
      add_left_comm, add_comm] using
      congrFun
      (conjugate_translate_add_inner_add_const
        (f := g.asEReal) (y := -b) (v := (0 : K)) (β := 0))
      v
  have hadj :
      (((⟪a, L.adjoint v⟫_ℝ : ℝ) : EReal)) = (((⟪b, v⟫_ℝ : ℝ) : EReal)) := by
    rw [hba, ContinuousLinearMap.adjoint_inner_right]
  -- Rewrite both translated conjugates, then cancel the affine correction through `b = L a`.
  rw [Pi.add_apply, Pi.add_apply, hφeval, hψeval]
  let X : EReal :=
    (Function.asEReal g)∗ v + ((Function.asEReal f)∗ᵛ ∘ L.adjoint) v
  have hcancel :
      (((⟪b, v⟫_ℝ : ℝ) : EReal)) + -(((⟪b, v⟫_ℝ : ℝ) : EReal)) = 0 := by
    change (((⟪b, v⟫_ℝ : ℝ) + -⟪b, v⟫_ℝ : ℝ) : EReal) = 0
    norm_num
  calc
    (((f.asEReal∗ᵛ ∘ L.adjoint) v + (((⟪a, L.adjoint v⟫_ℝ : ℝ) : EReal))) +
        (g.asEReal∗ v - (((⟪b, v⟫_ℝ : ℝ) : EReal)))) =
        (((⟪b, v⟫_ℝ : ℝ) : EReal)) + (-(((⟪b, v⟫_ℝ : ℝ) : EReal)) + X) := by
          simp [X, hadj, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    _ = ((((⟪b, v⟫_ℝ : ℝ) : EReal)) + -(((⟪b, v⟫_ℝ : ℝ) : EReal))) + X := by
          simp [add_assoc]
    _ = X := by rw [hcancel]; simp
    _ = ((f.asEReal∗ᵛ ∘ L.adjoint) + g.asEReal∗) v := by
          simp [X, add_comm, add_left_comm, add_assoc]

/-- Helper for Theorem 15 23: translating by domain witnesses preserves the regularity set and
does not change the composite dual objective once the affine correction cancels through `b = L a`.
-/
lemma translated_composite_data_preserves_regular_set
    (f : H → Set.Ioi (⊥ : EReal))
    (g : K → Set.Ioi (⊥ : EReal))
    (L : H →L[ℝ] K)
    (a : H) (ha : a ∈ effectiveDomain f)
    (b : K) (hb : b ∈ effectiveDomain g)
    (hba : b = L a) :
    let φ : H → Set.Ioi (⊥ : EReal) := fun x ↦ f (x + a)
    let ψ : K → Set.Ioi (⊥ : EReal) := fun y ↦ g (y + b)
    effectiveDomain ψ - L '' effectiveDomain φ = effectiveDomain g - L '' effectiveDomain f ∧
      (0 : H) ∈ effectiveDomain φ ∧
      (0 : K) ∈ effectiveDomain ψ ∧
      ∀ v : K, compositeDualObjective φ ψ L v = compositeDualObjective f g L v := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Translate both domain-difference witnesses by `a` and `b = L a`.
    ext u
    constructor
    · intro hu
      rcases Set.mem_sub.mp hu with ⟨y, hy, z, hz, hyz⟩
      rcases hz with ⟨x, hx, rfl⟩
      have hy' : y + b ∈ effectiveDomain g := by
        simpa [mem_effectiveDomain_iff, add_assoc, add_left_comm, add_comm] using hy
      have hx' : x + a ∈ effectiveDomain f := by
        simpa [mem_effectiveDomain_iff, add_assoc, add_left_comm, add_comm] using hx
      refine Set.mem_sub.mpr ⟨y + b, hy', L (x + a), ?_, ?_⟩
      · refine ⟨x + a, hx', by simp [ContinuousLinearMap.map_add, hba]⟩
      · calc
          (y + b) - L (x + a) = y - L x := by
            simp [ContinuousLinearMap.map_add, hba, sub_eq_add_neg, add_assoc, add_left_comm,
              add_comm]
          _ = u := hyz
    · intro hu
      rcases Set.mem_sub.mp hu with ⟨y, hy, z, hz, hyz⟩
      rcases hz with ⟨x, hx, rfl⟩
      have hy' : y - b ∈ effectiveDomain (fun y : K ↦ g (y + b)) := by
        simpa [mem_effectiveDomain_iff, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
          using hy
      have hx' : x - a ∈ effectiveDomain (fun x : H ↦ f (x + a)) := by
        simpa [mem_effectiveDomain_iff, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
          using hx
      refine Set.mem_sub.mpr ⟨y - b, hy', L (x - a), ?_, ?_⟩
      · refine ⟨x - a, hx', by simp [map_sub, hba]⟩
      · calc
          (y - b) - L (x - a) = y - L x := by
            simp [map_sub, hba, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
          _ = u := hyz
  · -- The chosen witness `a` moves to the origin for the translated `f`.
    simpa [mem_effectiveDomain_iff]
      using ha
  · -- The chosen witness `b` moves to the origin for the translated `g`.
    simpa [mem_effectiveDomain_iff]
      using hb
  · intro v
    -- Freeze the translated-dual owner equality once, then read off the pointwise identity.
    exact congrFun
      (translated_compositeDualObjective_eq_original_of_image_domain_witness
        (f := f) (g := g) (L := L) (a := a) (b := b) hba)
      v

/-- Helper for Theorem 15 23: when `0 ∈ dom f`, every point of `dom g` already lies in the closed
span of `dom g - L '' dom f`. -/
lemma effectiveDomain_subset_closedSpan_sub_image_difference
    (f : H → Set.Ioi (⊥ : EReal))
    (g : K → Set.Ioi (⊥ : EReal))
    (L : H →L[ℝ] K)
    (hzero_f : (0 : H) ∈ effectiveDomain f) :
    effectiveDomain g ⊆
      (((Submodule.span ℝ (effectiveDomain g - L '' effectiveDomain f)).topologicalClosure :
        Submodule ℝ K) : Set K) := by
  intro y hy
  -- Insert `y` into the source difference set using the zero domain witness for `f`.
  have hyS : y ∈ effectiveDomain g - L '' effectiveDomain f := by
    refine Set.mem_sub.mpr ?_
    refine ⟨y, hy, L 0, ?_, ?_⟩
    · exact ⟨0, hzero_f, by simp⟩
    · simp
  -- The closed span contains the generating difference set.
  exact
    (Submodule.span ℝ (effectiveDomain g - L '' effectiveDomain f)).le_topologicalClosure
      (Submodule.subset_span hyS)

/-- Helper for Theorem 15 23: when `0 ∈ dom g`, every image point `L x` with `x ∈ dom f` lies in
the closed span of `dom g - L '' dom f`. -/
lemma image_effectiveDomain_subset_closedSpan_sub_image_difference
    (f : H → Set.Ioi (⊥ : EReal))
    (g : K → Set.Ioi (⊥ : EReal))
    (L : H →L[ℝ] K)
    (hzero_g : (0 : K) ∈ effectiveDomain g) :
    L '' effectiveDomain f ⊆
      (((Submodule.span ℝ (effectiveDomain g - L '' effectiveDomain f)).topologicalClosure :
        Submodule ℝ K) : Set K) := by
  rintro _ ⟨x, hx, rfl⟩
  -- Insert `-L x` into the source difference set using the zero domain witness for `g`.
  have hnegS : -L x ∈ effectiveDomain g - L '' effectiveDomain f := by
    refine Set.mem_sub.mpr ?_
    refine ⟨0, hzero_g, L x, ?_, ?_⟩
    · exact ⟨x, hx, rfl⟩
    · simp
  have hneg_mem :
      -L x ∈
        ((Submodule.span ℝ (effectiveDomain g - L '' effectiveDomain f)).topologicalClosure :
          Submodule ℝ K) := by
    exact
      (Submodule.span ℝ (effectiveDomain g - L '' effectiveDomain f)).le_topologicalClosure
        (Submodule.subset_span hnegS)
  -- Closed subspaces are submodules, so negating returns to `L x`.
  simpa using
    (((Submodule.span ℝ (effectiveDomain g - L '' effectiveDomain f)).topologicalClosure :
      Submodule ℝ K).neg_mem hneg_mem)

/-- Helper for Theorem 15 23: in the zero-domain case, the restricted difference set on the closed
spans is exactly the subtype preimage of the ambient difference set, written pointwise to avoid
set-level subtraction on the subtype. -/
lemma restricted_difference_eq_preimage_sub_image_difference
    (f : H → Set.Ioi (⊥ : EReal))
    (g : K → Set.Ioi (⊥ : EReal))
    (L : H →L[ℝ] K)
    (hzero_f : (0 : H) ∈ effectiveDomain f)
    (hzero_g : (0 : K) ∈ effectiveDomain g) :
    let S : Set K := effectiveDomain g - L '' effectiveDomain f
    let A : ClosedSubmodule ℝ H :=
      ⟨(Submodule.span ℝ (effectiveDomain f)).topologicalClosure,
        Submodule.isClosed_topologicalClosure _⟩
    let B : ClosedSubmodule ℝ K :=
      ⟨(Submodule.span ℝ S).topologicalClosure, Submodule.isClosed_topologicalClosure _⟩
    let A0 : Submodule ℝ H := (A : Submodule ℝ H)
    let B0 : Submodule ℝ K := (B : Submodule ℝ K)
    let fA : A0 → Set.Ioi (⊥ : EReal) := fun x ↦ f x
    let gB : B0 → Set.Ioi (⊥ : EReal) := fun y ↦ g y
    let LAB : A0 →L[ℝ] B0 := B0.orthogonalProjection.comp (L.comp A0.subtypeL)
    ∀ y : B0,
      (∃ yB ∈ effectiveDomain gB, ∃ xA ∈ effectiveDomain fA,
        ((yB : K) - (LAB xA : K) = (y : K))) ↔
        ((y : K) ∈ S) := by
  let S : Set K := effectiveDomain g - L '' effectiveDomain f
  let A : ClosedSubmodule ℝ H :=
    ⟨(Submodule.span ℝ (effectiveDomain f)).topologicalClosure,
      Submodule.isClosed_topologicalClosure _⟩
  let B : ClosedSubmodule ℝ K :=
    ⟨(Submodule.span ℝ S).topologicalClosure, Submodule.isClosed_topologicalClosure _⟩
  let A0 : Submodule ℝ H := (A : Submodule ℝ H)
  let B0 : Submodule ℝ K := (B : Submodule ℝ K)
  let fA : A0 → Set.Ioi (⊥ : EReal) := fun x ↦ f x
  let gB : B0 → Set.Ioi (⊥ : EReal) := fun y ↦ g y
  let LAB : A0 →L[ℝ] B0 := B0.orthogonalProjection.comp (L.comp A0.subtypeL)
  -- Route correction: freeze the textbook closed spans `A` and `B` first, then compare the
  -- restricted witness equation in the ambient space `K` to avoid subtype subtraction noise.
  change ∀ y : B0,
      (∃ yB ∈ effectiveDomain gB, ∃ xA ∈ effectiveDomain fA,
        ((yB : K) - (LAB xA : K) = (y : K))) ↔
        ((y : K) ∈ S)
  intro y
  constructor
  · intro hy
    rcases hy with ⟨yB, hyB, xA, hxA, hy_eq⟩
    -- Read the restricted domain hypotheses back in the ambient spaces.
    have hy_dom : (yB : K) ∈ effectiveDomain g := by
      simpa [mem_effectiveDomain_iff] using hyB
    have hx_dom : (xA : H) ∈ effectiveDomain f := by
      simpa [mem_effectiveDomain_iff] using hxA
    have hL_mem_B : L (xA : H) ∈ (B0 : Set K) :=
      image_effectiveDomain_subset_closedSpan_sub_image_difference
        (f := f) (g := g) (L := L) hzero_g ⟨(xA : H), hx_dom, rfl⟩
    have hproj :
        ((B0.orthogonalProjection (L (xA : H))) : K) = L (xA : H) := by
      simpa using (Submodule.starProjection_eq_self_iff.2 hL_mem_B)
    -- Replace the restricted projection by the ambient vector because the image already lies in `B`.
    refine Set.mem_sub.mpr ⟨(yB : K), hy_dom, L (xA : H), ?_, ?_⟩
    · exact ⟨(xA : H), hx_dom, rfl⟩
    · calc
        (yB : K) - L (xA : H) =
            (yB : K) - ((LAB xA : B0) : K) := by rw [show ((LAB xA : B0) : K) = L (xA : H) by
              simpa [LAB] using hproj]
        _ = (y : K) := hy_eq
  · intro hy
    rcases Set.mem_sub.mp hy with ⟨y0, hy0, z, hz, hy_eq⟩
    rcases hz with ⟨x, hx, rfl⟩
    have hy_mem_B : y0 ∈ (B0 : Set K) :=
      effectiveDomain_subset_closedSpan_sub_image_difference
        (f := f) (g := g) (L := L) hzero_f hy0
    have hx_mem_A : x ∈ (A0 : Set H) := by
      exact (Submodule.span ℝ (effectiveDomain f)).le_topologicalClosure (Submodule.subset_span hx)
    let yB : B0 := ⟨y0, hy_mem_B⟩
    let xA : A0 := ⟨x, hx_mem_A⟩
    have hxA_dom : xA ∈ effectiveDomain fA := by
      simpa [xA, mem_effectiveDomain_iff] using hx
    have hyB_dom : yB ∈ effectiveDomain gB := by
      simpa [yB, mem_effectiveDomain_iff] using hy0
    have hL_mem_B : L x ∈ (B0 : Set K) :=
      image_effectiveDomain_subset_closedSpan_sub_image_difference
        (f := f) (g := g) (L := L) hzero_g ⟨x, hx, rfl⟩
    have hproj : ((B0.orthogonalProjection (L x)) : K) = L x := by
      simpa using (Submodule.starProjection_eq_self_iff.2 hL_mem_B)
    -- Repackage the ambient decomposition inside the subtype `B`.
    refine ⟨yB, hyB_dom, xA, hxA_dom, ?_⟩
    calc
      ((yB : K) - (LAB xA : K)) = y0 - L x := by
        simpa [LAB, yB, xA, hproj]
      _ = (y : K) := hy_eq

/-- Helper for Theorem 15 23: in the zero-domain case, the restricted difference set on the
textbook closed span `B` agrees setwise with the subtype preimage of the ambient difference set. -/
lemma restrictedDifference_eq_subtypePreimage_onClosedSpans
    (f : H → Set.Ioi (⊥ : EReal))
    (g : K → Set.Ioi (⊥ : EReal))
    (L : H →L[ℝ] K)
    (hzero_f : (0 : H) ∈ effectiveDomain f)
    (hzero_g : (0 : K) ∈ effectiveDomain g) :
    let S : Set K := effectiveDomain g - L '' effectiveDomain f
    let A : ClosedSubmodule ℝ H :=
      ⟨(Submodule.span ℝ (effectiveDomain f)).topologicalClosure,
        Submodule.isClosed_topologicalClosure _⟩
    let B : ClosedSubmodule ℝ K :=
      ⟨(Submodule.span ℝ S).topologicalClosure, Submodule.isClosed_topologicalClosure _⟩
    let A0 : Submodule ℝ H := (A : Submodule ℝ H)
    let B0 : Submodule ℝ K := (B : Submodule ℝ K)
    let fA : A0 → Set.Ioi (⊥ : EReal) := fun x ↦ f x
    let gB : B0 → Set.Ioi (⊥ : EReal) := fun y ↦ g y
    let LAB : A0 →L[ℝ] B0 := B0.orthogonalProjection.comp (L.comp A0.subtypeL)
    ∀ y : B0, y ∈ effectiveDomain gB - LAB '' effectiveDomain fA ↔ ((y : K) ∈ S) := by
  let S : Set K := effectiveDomain g - L '' effectiveDomain f
  let A : ClosedSubmodule ℝ H :=
    ⟨(Submodule.span ℝ (effectiveDomain f)).topologicalClosure,
      Submodule.isClosed_topologicalClosure _⟩
  let B : ClosedSubmodule ℝ K :=
    ⟨(Submodule.span ℝ S).topologicalClosure, Submodule.isClosed_topologicalClosure _⟩
  let A0 : Submodule ℝ H := (A : Submodule ℝ H)
  let B0 : Submodule ℝ K := (B : Submodule ℝ K)
  let fA : A0 → Set.Ioi (⊥ : EReal) := fun x ↦ f x
  let gB : B0 → Set.Ioi (⊥ : EReal) := fun y ↦ g y
  let LAB : A0 →L[ℝ] B0 := B0.orthogonalProjection.comp (L.comp A0.subtypeL)
  change ∀ y : B0, y ∈ effectiveDomain gB - LAB '' effectiveDomain fA ↔ ((y : K) ∈ S)
  intro y
  constructor
  · intro hy
    -- Convert the subtype difference membership into the ambient witness equation already proved
    -- in `restricted_difference_eq_preimage_sub_image_difference`.
    have hy' :
        ∃ yB ∈ effectiveDomain gB, ∃ xA ∈ effectiveDomain fA,
          ((yB : K) - (LAB xA : K) = (y : K)) := by
      rcases Set.mem_sub.mp hy with ⟨yB, hyB, z, hz, hyz⟩
      rcases hz with ⟨xA, hxA, rfl⟩
      refine ⟨yB, hyB, xA, hxA, ?_⟩
      exact congrArg (fun t : B0 => (t : K)) hyz
    exact
      (restricted_difference_eq_preimage_sub_image_difference
        (f := f) (g := g) (L := L) hzero_f hzero_g y).1 hy'
  · intro hy
    -- Repackage the ambient difference witness back inside the subtype `B`.
    have hy' :
        ∃ yB ∈ effectiveDomain gB, ∃ xA ∈ effectiveDomain fA,
          ((yB : K) - (LAB xA : K) = (y : K)) :=
      (restricted_difference_eq_preimage_sub_image_difference
        (f := f) (g := g) (L := L) hzero_f hzero_g y).2 hy
    rcases hy' with ⟨yB, hyB, xA, hxA, hy_eq⟩
    refine Set.mem_sub.mpr ⟨yB, hyB, LAB xA, ⟨xA, hxA, rfl⟩, ?_⟩
    apply Subtype.ext
    simpa using hy_eq

/-- Helper for Theorem 15 23: on the closed-span subtype
`B = closure(span (effectiveDomain g - L '' effectiveDomain f))`, the cone of the subtype
preimage of the ambient difference set is read pointwise in `K`. -/
lemma mem_cone_subtype_preimage_sub_image_difference_iff
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (g : K → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K) :
    let S : Set K := effectiveDomain g - L '' effectiveDomain f
    let B : ClosedSubmodule ℝ K :=
      ⟨(Submodule.span ℝ S).topologicalClosure, Submodule.isClosed_topologicalClosure _⟩
    let T : Set (B : Submodule ℝ K) := ((↑) ⁻¹' S)
    ∀ {v : (B : Submodule ℝ K)}, v ∈ cone T ↔ ((v : K) ∈ cone S) := by
  let S : Set K := effectiveDomain g - L '' effectiveDomain f
  let B : ClosedSubmodule ℝ K :=
    ⟨(Submodule.span ℝ S).topologicalClosure, Submodule.isClosed_topologicalClosure _⟩
  let T : Set (B : Submodule ℝ K) := ((↑) ⁻¹' S)
  let V : Submodule ℝ K := (B : Submodule ℝ K)
  change ∀ {v : (B : Submodule ℝ K)}, v ∈ cone T ↔ ((v : K) ∈ cone S)
  have hS_convex : Convex ℝ S := by
    -- The ambient difference set is convex because both effective domains are convex.
    simpa [S] using
      hg.2.convex_effectiveDomain.sub (hf.2.convex_effectiveDomain.linear_image L.toLinearMap)
  have hT_convex : Convex ℝ T := by
    -- Pull convexity back along the subtype inclusion of the closed span carrier.
    simpa [T, V] using hS_convex.affine_preimage V.subtype.toAffineMap
  intro v
  -- Compare both cone predicates through the positive-multiple description of convex cones.
  rw [cone_eq_toCone_of_convex_aux hT_convex, cone_eq_toCone_of_convex_aux hS_convex]
  constructor
  · intro hv
    rcases (Convex.mem_toCone hT_convex).1 hv with ⟨c, hc, y, hy, rfl⟩
    exact (Convex.mem_toCone hS_convex).2 ⟨c, hc, (y : K), hy, rfl⟩
  · intro hv
    rcases (Convex.mem_toCone hS_convex).1 hv with ⟨c, hc, y, hy, hyv⟩
    have hyB : y ∈ (B : Set K) := by
      -- The closed span `B` contains the generators `S`.
      change y ∈ (((Submodule.span ℝ S).topologicalClosure : Submodule ℝ K) : Set K)
      exact (Submodule.span ℝ S).le_topologicalClosure (Submodule.subset_span hy)
    refine (Convex.mem_toCone hT_convex).2 ?_
    refine ⟨c, hc, ⟨y, hyB⟩, hy, ?_⟩
    apply Subtype.ext
    simpa using hyv

/-- Helper for Theorem 15 23: after restricting to the textbook closed span
`B = closure(span (effectiveDomain g - L '' effectiveDomain f))`, the cone of the subtype
preimage fills the whole ambient subtype `B`. This is the closed-span form of line `(15.36)`. -/
lemma restricted_subtype_preimage_cone_eq_univ_on_closed_span
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (g : K → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K)
    (hsri : (0 : K) ∈ sri (effectiveDomain g - L '' effectiveDomain f)) :
    let S : Set K := effectiveDomain g - L '' effectiveDomain f
    let B : ClosedSubmodule ℝ K :=
      ⟨(Submodule.span ℝ S).topologicalClosure, Submodule.isClosed_topologicalClosure _⟩
    let T : Set (B : Submodule ℝ K) := ((↑) ⁻¹' S)
    cone T = (univ : Set (B : Submodule ℝ K)) := by
  let S : Set K := effectiveDomain g - L '' effectiveDomain f
  let B : ClosedSubmodule ℝ K :=
    ⟨(Submodule.span ℝ S).topologicalClosure, Submodule.isClosed_topologicalClosure _⟩
  let T : Set (B : Submodule ℝ K) := ((↑) ⁻¹' S)
  change cone T = (univ : Set (B : Submodule ℝ K))
  have hS_convex : Convex ℝ S := by
    -- The regularity set is the difference of two convex effective domains.
    simpa [S] using
      hg.2.convex_effectiveDomain.sub (hf.2.convex_effectiveDomain.linear_image L.toLinearMap)
  have h0S : (0 : K) ∈ S := (Set.mem_strongRelativeInterior_iff.mp hsri).1
  have hS_nonempty : S.Nonempty := ⟨0, h0S⟩
  have hconeS :
      cone S = (((Submodule.span ℝ S).topologicalClosure : Submodule ℝ K) : Set K) := by
    -- Proposition 6.21 turns the ambient `sri` hypothesis into the cone-equals-closed-span
    -- identity.
    exact
      (zero_mem_strongRelativeInterior_iff_cone_eq_closure_span_of_nonempty_convex
        hS_nonempty hS_convex).mp hsri
  ext v
  constructor
  · intro _
    simp
  · intro _
    -- Every point of the closed span lies in the ambient cone, hence in the subtype cone.
    have hvCone : ((v : (B : Submodule ℝ K)) : K) ∈ cone S := by
      rw [hconeS]
      exact v.property
    exact
      (mem_cone_subtype_preimage_sub_image_difference_iff
        (f := f) (hf := hf) (g := g) (hg := hg) (L := L)).2 hvCone

/-- Helper for Theorem 15 23: the ambient `sri` hypothesis transports to the subtype preimage of
the textbook closed span `B = closure(span (effectiveDomain g - L '' effectiveDomain f))`. -/
lemma restricted_zero_mem_sri_subtype_preimage_on_closed_span
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (g : K → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K)
    (hsri : (0 : K) ∈ sri (effectiveDomain g - L '' effectiveDomain f)) :
    let S : Set K := effectiveDomain g - L '' effectiveDomain f
    let B : ClosedSubmodule ℝ K :=
      ⟨(Submodule.span ℝ S).topologicalClosure, Submodule.isClosed_topologicalClosure _⟩
    let T : Set (B : Submodule ℝ K) := ((↑) ⁻¹' S)
    (0 : (B : Submodule ℝ K)) ∈ sri T := by
  let S : Set K := effectiveDomain g - L '' effectiveDomain f
  let B : ClosedSubmodule ℝ K :=
    ⟨(Submodule.span ℝ S).topologicalClosure, Submodule.isClosed_topologicalClosure _⟩
  let T : Set (B : Submodule ℝ K) := ((↑) ⁻¹' S)
  let V : Submodule ℝ K := (B : Submodule ℝ K)
  change (0 : (B : Submodule ℝ K)) ∈ sri T
  have h0S : (0 : K) ∈ S := (Set.mem_strongRelativeInterior_iff.mp hsri).1
  have hT_nonempty : T.Nonempty := by
    -- The ambient origin witness lifts to the closed-span subtype.
    refine ⟨0, ?_⟩
    simpa [T] using h0S
  have hS_convex : Convex ℝ S := by
    -- The ambient difference set is convex.
    simpa [S] using
      hg.2.convex_effectiveDomain.sub (hf.2.convex_effectiveDomain.linear_image L.toLinearMap)
  have hT_convex : Convex ℝ T := by
    -- Pull convexity back to the subtype preimage.
    simpa [T, V] using hS_convex.affine_preimage V.subtype.toAffineMap
  have hconeT : cone T = (univ : Set (B : Submodule ℝ K)) := by
    -- The repaired cone comparison yields the closed-span form of line `(15.36)`.
    exact
      restricted_subtype_preimage_cone_eq_univ_on_closed_span
        (f := f) (hf := hf) (g := g) (hg := hg) (L := L) hsri
  have hspanT :
      ((Submodule.span ℝ T).topologicalClosure : Set (B : Submodule ℝ K)) = univ := by
    apply Set.Subset.antisymm
    · simp
    · intro v hv
      have hvCone : v ∈ cone T := by simpa [hconeT]
      exact cone_subset_topologicalClosure_span T hvCone
  -- Proposition 6.21 now applies inside the closed-span subtype.
  exact
    (zero_mem_strongRelativeInterior_iff_cone_eq_closure_span_of_nonempty_convex
      hT_nonempty hT_convex).2 <|
      calc
        cone T = (univ : Set (B : Submodule ℝ K)) := hconeT
        _ = ((Submodule.span ℝ T).topologicalClosure : Set (B : Submodule ℝ K)) := hspanT.symm

/-- Helper for Theorem 15 23: the same closed-span subtype preimage also contains the origin in
its algebraic core. This is the source-facing `core` form of line `(15.36)`. -/
lemma restricted_zero_mem_core_subtype_preimage_on_closed_span
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (g : K → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K)
    (hsri : (0 : K) ∈ sri (effectiveDomain g - L '' effectiveDomain f)) :
    let S : Set K := effectiveDomain g - L '' effectiveDomain f
    let B : ClosedSubmodule ℝ K :=
      ⟨(Submodule.span ℝ S).topologicalClosure, Submodule.isClosed_topologicalClosure _⟩
    let T : Set (B : Submodule ℝ K) := ((↑) ⁻¹' S)
    (0 : (B : Submodule ℝ K)) ∈ Set.core T := by
  let S : Set K := effectiveDomain g - L '' effectiveDomain f
  let B : ClosedSubmodule ℝ K :=
    ⟨(Submodule.span ℝ S).topologicalClosure, Submodule.isClosed_topologicalClosure _⟩
  let T : Set (B : Submodule ℝ K) := ((↑) ⁻¹' S)
  change (0 : (B : Submodule ℝ K)) ∈ Set.core T
  have h0S : (0 : K) ∈ S := (Set.mem_strongRelativeInterior_iff.mp hsri).1
  have h0T : (0 : (B : Submodule ℝ K)) ∈ T := by
    -- The source origin witness becomes the subtype origin witness.
    simpa [T] using h0S
  have hTsub : T - ({(0 : (B : Submodule ℝ K))} : Set (B : Submodule ℝ K)) = T := by
    -- Subtracting the origin does not change the subtype preimage.
    ext v
    constructor
    · rintro ⟨u, hu, w, hw, huw⟩
      rcases Set.mem_singleton_iff.mp hw with rfl
      have huv : u = v := by simpa using huw
      simpa [huv] using hu
    · intro hv
      exact Set.mem_sub.mpr ⟨v, hv, 0, by simp, by simp⟩
  have hconeT : cone T = (univ : Set (B : Submodule ℝ K)) := by
    -- The core statement uses the same cone computation as the `sri` bridge.
    exact
      restricted_subtype_preimage_cone_eq_univ_on_closed_span
        (f := f) (hf := hf) (g := g) (hg := hg) (L := L) hsri
  -- Rewrite the core predicate at the origin to the cone criterion from Fact 6.14.
  rw [Set.mem_core_iff]
  refine ⟨h0T, ?_⟩
  simpa [hTsub] using hconeT

/-- Helper for Theorem 15 23: the closed-span restricted difference set itself contains the
origin in its algebraic core. This is the owner-form rewrite of line `(15.36)`. -/
lemma restrictedZeroMemCore_difference_onClosedSpans
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (g : K → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K)
    (hsri : (0 : K) ∈ sri (effectiveDomain g - L '' effectiveDomain f))
    (hzero_f : (0 : H) ∈ effectiveDomain f)
    (hzero_g : (0 : K) ∈ effectiveDomain g) :
    let S : Set K := effectiveDomain g - L '' effectiveDomain f
    let A : ClosedSubmodule ℝ H :=
      ⟨(Submodule.span ℝ (effectiveDomain f)).topologicalClosure,
        Submodule.isClosed_topologicalClosure _⟩
    let B : ClosedSubmodule ℝ K :=
      ⟨(Submodule.span ℝ S).topologicalClosure, Submodule.isClosed_topologicalClosure _⟩
    let A0 : Submodule ℝ H := (A : Submodule ℝ H)
    let B0 : Submodule ℝ K := (B : Submodule ℝ K)
    let fA : A0 → Set.Ioi (⊥ : EReal) := fun x ↦ f x
    let gB : B0 → Set.Ioi (⊥ : EReal) := fun y ↦ g y
    let LAB : A0 →L[ℝ] B0 := B0.orthogonalProjection.comp (L.comp A0.subtypeL)
    (0 : B0) ∈ Set.core (effectiveDomain gB - LAB '' effectiveDomain fA) := by
  let S : Set K := effectiveDomain g - L '' effectiveDomain f
  let A : ClosedSubmodule ℝ H :=
    ⟨(Submodule.span ℝ (effectiveDomain f)).topologicalClosure,
      Submodule.isClosed_topologicalClosure _⟩
  let B : ClosedSubmodule ℝ K :=
    ⟨(Submodule.span ℝ S).topologicalClosure, Submodule.isClosed_topologicalClosure _⟩
  let A0 : Submodule ℝ H := (A : Submodule ℝ H)
  let B0 : Submodule ℝ K := (B : Submodule ℝ K)
  let fA : A0 → Set.Ioi (⊥ : EReal) := fun x ↦ f x
  let gB : B0 → Set.Ioi (⊥ : EReal) := fun y ↦ g y
  let LAB : A0 →L[ℝ] B0 := B0.orthogonalProjection.comp (L.comp A0.subtypeL)
  change (0 : B0) ∈ Set.core (effectiveDomain gB - LAB '' effectiveDomain fA)
  -- First reuse the already-proved subtype-preimage core statement on the carrier of `B`.
  have hcore_preimage :
      (0 : B0) ∈ Set.core (((↑) ⁻¹' S) : Set B0) := by
    simpa [S, B0] using
      restricted_zero_mem_core_subtype_preimage_on_closed_span
        (f := f) (hf := hf) (g := g) (hg := hg) (L := L) hsri
  have hset :
      effectiveDomain gB - LAB '' effectiveDomain fA = (((↑) ⁻¹' S) : Set B0) := by
    ext y
    -- The restricted difference set agrees pointwise with the ambient difference-set preimage.
    simpa [S, A0, B0, fA, gB, LAB] using
      (restrictedDifference_eq_subtypePreimage_onClosedSpans
        (f := f) (g := g) (L := L) hzero_f hzero_g y)
  -- Repackage the subtype-preimage core statement in the owner form used by the restricted dual.
  simpa [hset] using hcore_preimage

/-- Helper for Theorem 15 23: in the zero-domain case, `L` maps the textbook closed span
`A = closure(span(dom f))` into `B = closure(span(dom g - L '' dom f))`. -/
lemma image_restricted_closedSpan_subset_closedSpan_sub_image_difference
    (f : H → Set.Ioi (⊥ : EReal))
    (g : K → Set.Ioi (⊥ : EReal))
    (L : H →L[ℝ] K)
    (hzero_g : (0 : K) ∈ effectiveDomain g) :
    let A : ClosedSubmodule ℝ H :=
      ⟨(Submodule.span ℝ (effectiveDomain f)).topologicalClosure,
        Submodule.isClosed_topologicalClosure _⟩
    let B : ClosedSubmodule ℝ K :=
      ⟨(Submodule.span ℝ (effectiveDomain g - L '' effectiveDomain f)).topologicalClosure,
        Submodule.isClosed_topologicalClosure _⟩
    ∀ x : A, (L x : K) ∈ (B : Set K) := by
  let A : ClosedSubmodule ℝ H :=
    ⟨(Submodule.span ℝ (effectiveDomain f)).topologicalClosure,
      Submodule.isClosed_topologicalClosure _⟩
  let B : ClosedSubmodule ℝ K :=
    ⟨(Submodule.span ℝ (effectiveDomain g - L '' effectiveDomain f)).topologicalClosure,
      Submodule.isClosed_topologicalClosure _⟩
  let F : H →L[ℝ] K := B.starProjection.comp L
  let G : H →L[ℝ] K := L
  change ∀ x : A, (L x : K) ∈ (B : Set K)
  have hEq : Set.EqOn F G (effectiveDomain f) := by
    intro x hx
    -- The image-domain generator step places `L x` inside `B`, so the projection fixes it.
    have hLxB : L x ∈ (B : Set K) :=
      image_effectiveDomain_subset_closedSpan_sub_image_difference
        (f := f) (g := g) (L := L) hzero_g ⟨x, hx, rfl⟩
    simpa [F, G] using (Submodule.starProjection_eq_self_iff.2 hLxB)
  have hEqClosure := ContinuousLinearMap.eqOn_closure_span hEq
  intro x
  -- Extend the generator identity from `effectiveDomain f` to the full closed span `A`.
  have hxEq : B.starProjection (L x) = L x := by
    exact hEqClosure (by simpa [A] using x.property)
  exact (Submodule.starProjection_eq_self_iff.1 hxEq)

/-- Helper for Theorem 15 23: source equations (15.34) and (15.35) in Lean form. The adjoint part
of the dual owner already factors through the closed span `B`. -/
lemma restricted_adjoint_apply_eq_projected_adjoint_of_zero_domain_data
    (f : H → Set.Ioi (⊥ : EReal))
    (g : K → Set.Ioi (⊥ : EReal))
    (L : H →L[ℝ] K)
    (hzero_g : (0 : K) ∈ effectiveDomain g) :
    let A : ClosedSubmodule ℝ H :=
      ⟨(Submodule.span ℝ (effectiveDomain f)).topologicalClosure,
        Submodule.isClosed_topologicalClosure _⟩
    let B : ClosedSubmodule ℝ K :=
      ⟨(Submodule.span ℝ (effectiveDomain g - L '' effectiveDomain f)).topologicalClosure,
        Submodule.isClosed_topologicalClosure _⟩
    ∀ v : K, A.starProjection (L.adjoint v) = A.starProjection (L.adjoint (B.starProjection v)) := by
  let A : ClosedSubmodule ℝ H :=
    ⟨(Submodule.span ℝ (effectiveDomain f)).topologicalClosure,
      Submodule.isClosed_topologicalClosure _⟩
  let B : ClosedSubmodule ℝ K :=
    ⟨(Submodule.span ℝ (effectiveDomain g - L '' effectiveDomain f)).topologicalClosure,
      Submodule.isClosed_topologicalClosure _⟩
  change ∀ v : K, A.starProjection (L.adjoint v) = A.starProjection (L.adjoint (B.starProjection v))
  have hL_mem_B : ∀ {x : H}, x ∈ (A : Set H) → L x ∈ (B : Set K) := by
    intro x hx
    let xA : A := ⟨x, hx⟩
    -- The previous helper transports the image-domain containment from generators to the closed
    -- span `A`.
    simpa [A, B] using
      image_restricted_closedSpan_subset_closedSpan_sub_image_difference
        (f := f) (g := g) (L := L) hzero_g xA
  have hkill_orthogonal :
      ∀ {v : K}, v ∈ (B : Submodule ℝ K)ᗮ → (A.starProjection.comp L.adjoint) v = 0 := by
    intro v hv
    have hAdj_mem : L.adjoint v ∈ (A : Submodule ℝ H)ᗮ := by
      rw [Submodule.mem_orthogonal']
      intro x hx
      have hLxB : L x ∈ (B : Set K) := hL_mem_B hx
      have hinner : ⟪v, L x⟫_ℝ = 0 := (Submodule.mem_orthogonal' _ _).1 hv (L x) hLxB
      simpa [ContinuousLinearMap.adjoint_inner_left] using hinner
    -- Once `L† v` is orthogonal to `A`, the projection onto `A` vanishes.
    exact (Submodule.starProjection_apply_eq_zero_iff (K := (A : Submodule ℝ H))).2 hAdj_mem
  intro v
  -- Decompose `v` into its `B` and `Bᗮ` parts; the orthogonal component is killed by the
  -- previous step.
  have hresidual :
      A.starProjection (L.adjoint (v - B.starProjection v)) = 0 :=
    hkill_orthogonal
      ((Submodule.sub_starProjection_mem_orthogonal (K := (B : Submodule ℝ K)) v))
  have hv_split : v = B.starProjection v + (v - B.starProjection v) := by
    abel
  calc
    A.starProjection (L.adjoint v)
        = A.starProjection (L.adjoint (B.starProjection v + (v - B.starProjection v))) := by
            nth_rw 1 [hv_split]
    _ = A.starProjection (L.adjoint (B.starProjection v) + L.adjoint (v - B.starProjection v)) := by
          rw [map_add]
    _ = A.starProjection (L.adjoint (B.starProjection v)) +
          A.starProjection (L.adjoint (v - B.starProjection v)) := by
            simp
    _ = A.starProjection (L.adjoint (B.starProjection v)) := by rw [hresidual, add_zero]

/-- Helper for Theorem 15 23: restricting the primal problem to the textbook closed spans does not
change its optimal value in the zero-domain case. -/
lemma ambientCompositePrimalOptimalValue_eq_restrictedOnClosedSpans
    (f : H → Set.Ioi (⊥ : EReal))
    (g : K → Set.Ioi (⊥ : EReal))
    (L : H →L[ℝ] K)
    (hzero_f : (0 : H) ∈ effectiveDomain f)
    (hzero_g : (0 : K) ∈ effectiveDomain g) :
    let A : ClosedSubmodule ℝ H :=
      ⟨(Submodule.span ℝ (effectiveDomain f)).topologicalClosure,
        Submodule.isClosed_topologicalClosure _⟩
    let B : ClosedSubmodule ℝ K :=
      ⟨(Submodule.span ℝ (effectiveDomain g - L '' effectiveDomain f)).topologicalClosure,
        Submodule.isClosed_topologicalClosure _⟩
    let A0 : Submodule ℝ H := (A : Submodule ℝ H)
    let B0 : Submodule ℝ K := (B : Submodule ℝ K)
    let fA : A0 → Set.Ioi (⊥ : EReal) := fun x ↦ f x
    let gB : B0 → Set.Ioi (⊥ : EReal) := fun y ↦ g y
    let LAB : A0 →L[ℝ] B0 := B0.orthogonalProjection.comp (L.comp A0.subtypeL)
    compositePrimalOptimalValue f g L = compositePrimalOptimalValue fA gB LAB := by
  let A : ClosedSubmodule ℝ H :=
    ⟨(Submodule.span ℝ (effectiveDomain f)).topologicalClosure,
      Submodule.isClosed_topologicalClosure _⟩
  let B : ClosedSubmodule ℝ K :=
    ⟨(Submodule.span ℝ (effectiveDomain g - L '' effectiveDomain f)).topologicalClosure,
      Submodule.isClosed_topologicalClosure _⟩
  let A0 : Submodule ℝ H := (A : Submodule ℝ H)
  let B0 : Submodule ℝ K := (B : Submodule ℝ K)
  let fA : A0 → Set.Ioi (⊥ : EReal) := fun x ↦ f x
  let gB : B0 → Set.Ioi (⊥ : EReal) := fun y ↦ g y
  let LAB : A0 →L[ℝ] B0 := B0.orthogonalProjection.comp (L.comp A0.subtypeL)
  change primalOptimalValue f (g ∘ L) = primalOptimalValue fA (gB ∘ LAB)
  rw [primalOptimalValue_eq_iInf_primalObjective, primalOptimalValue_eq_iInf_primalObjective]
  refine le_antisymm ?_ ?_
  · refine le_iInf fun xA ↦ ?_
    have hLxA_mem_B : L (xA : H) ∈ (B0 : Set K) := by
      simpa [A0, B0] using
        image_restricted_closedSpan_subset_closedSpan_sub_image_difference
          (f := f) (g := g) (L := L) hzero_g xA
    have hproj : ((B0.orthogonalProjection (L (xA : H))) : K) = L (xA : H) := by
      simpa using (Submodule.starProjection_eq_self_iff.2 hLxA_mem_B)
    -- Evaluate the ambient objective on the same primal point because `L xA` already lies in `B`.
    calc
      (⨅ x : H, compositePrimalObjective f g L x) ≤ compositePrimalObjective f g L (xA : H) :=
        iInf_le _ (xA : H)
      _ = compositePrimalObjective fA gB LAB xA := by
          rw [compositePrimalObjective_apply, compositePrimalObjective_apply]
          congr 1
          simpa [gB, LAB] using congrArg (fun t : K => (g t : EReal)) hproj.symm
  · refine le_iInf fun x ↦ ?_
    by_cases hxA : x ∈ (A0 : Set H)
    · let xA : A0 := ⟨x, hxA⟩
      have hLx_mem_B : L x ∈ (B0 : Set K) := by
        simpa [A0, B0, xA] using
          image_restricted_closedSpan_subset_closedSpan_sub_image_difference
            (f := f) (g := g) (L := L) hzero_g xA
      have hproj : ((B0.orthogonalProjection (L x)) : K) = L x := by
        simpa using (Submodule.starProjection_eq_self_iff.2 hLx_mem_B)
      -- For ambient points already in `A`, compare the two objectives on the corresponding subtype
      -- point.
      calc
        (⨅ xA : A0, compositePrimalObjective fA gB LAB xA) ≤ compositePrimalObjective fA gB LAB xA :=
          iInf_le _ xA
        _ = compositePrimalObjective f g L x := by
            rw [compositePrimalObjective_apply, compositePrimalObjective_apply]
            congr 1
            simpa [gB, LAB, xA] using congrArg (fun t : K => (g t : EReal)) hproj
    · have hx_not_dom : x ∉ effectiveDomain f := by
        intro hxdom
        exact hxA <|
          (Submodule.span ℝ (effectiveDomain f)).le_topologicalClosure (Submodule.subset_span hxdom)
      have hfx_top : (f x : EReal) = ⊤ := by
        simpa [mem_effectiveDomain_iff] using hx_not_dom
      -- Outside `A`, the point cannot lie in the effective domain of `f`, so the ambient primal
      -- value is `⊤`.
      calc
        (⨅ xA : A0, compositePrimalObjective fA gB LAB xA) ≤ ⊤ := le_top
        _ = compositePrimalObjective f g L x := by
            rw [compositePrimalObjective_apply, hfx_top]
            exact (EReal.top_add_of_ne_bot (ne_of_gt (g (L x)).2)).symm

/-- Helper for Theorem 15 23: the indicator of a nonempty closed convex set belongs to `Γ₀`.
This keeps the graph-indicator packaging local to the current proof file instead of importing a
broken downstream statement wrapper. -/
lemma indicator_mem_gammaZero_of_nonempty_isClosed_convex_local
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    {C : Set X}
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    ι[C] ∈ Γ₀(X) := by
  have hindicator_lsc :
      LowerSemicontinuous (fun y ↦ ((ι[C]) y : EReal)) := by
    -- Closedness of `C` is exactly lower semicontinuity of its indicator.
    simpa using (lowerSemicontinuous_indicator_compl_top_iff_isClosed C).2 hC_closed
  have hindicator_dom : effectiveDomain (ι[C]) = C := by
    -- The indicator is finite exactly on its defining set.
    ext y
    by_cases hy : y ∈ C <;> simp [ERealFunction.effectiveDomain, ERealFunction.indicator, hy]
  refine ⟨hindicator_lsc, ?_⟩
  refine ⟨by simpa [hindicator_dom] using hC_nonempty, fun _ hy ↦ hy, ?_⟩
  intro y hy z hz a ha0 ha1
  have hyC : y ∈ C := by
    simpa [hindicator_dom] using hy
  have hzC : z ∈ C := by
    simpa [hindicator_dom] using hz
  have hayzC : a • y + (1 - a) • z ∈ C :=
    hC_convex hyC hzC ha0.le (sub_nonneg.mpr ha1.le) (by ring)
  -- Once the convex combination stays in `C`, the indicator inequality is immediate.
  simp [ERealFunction.indicator, hyC, hzC, hayzC]

/-- Helper for Theorem 15 23: the graph of a continuous linear map, packaged as a plain set on the
product space. This freezes the graph term in a stable normal form before applying indicator
lemmas. -/
private def linearGraphSet
    {A : Type*} {B : Type*}
    [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
    [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B]
    (LAB : A →L[ℝ] B) : Set (A × B) :=
  (LAB.toLinearMap.graph : Set (A × B))

/-- Helper for Theorem 15 23: the graph of a continuous linear map is closed in the product
space. -/
lemma linearGraphSet_isClosed
    {A : Type*} {B : Type*}
    [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
    [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B]
    (LAB : A →L[ℝ] B) :
    IsClosed (linearGraphSet LAB) := by
  -- Freeze the graph as the equalizer of the second projection and the first projection composed
  -- with `LAB`.
  simpa [linearGraphSet, eq_comm, LinearMap.mem_graph_iff] using
    isClosed_eq continuous_snd (LAB.continuous.comp continuous_fst)

/-- Helper for Theorem 15 23: the graph of a continuous linear map contains the origin. -/
lemma linearGraphSet_nonempty
    {A : Type*} {B : Type*}
    [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
    [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B]
    (LAB : A →L[ℝ] B) :
    (linearGraphSet LAB).Nonempty := by
  -- The origin satisfies the graph equation.
  refine ⟨(0, 0), ?_⟩
  simp [linearGraphSet, LinearMap.mem_graph_iff]

/-- Helper for Theorem 15 23: the graph of a continuous linear map is convex. -/
lemma linearGraphSet_convex
    {A : Type*} {B : Type*}
    [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
    [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B]
    (LAB : A →L[ℝ] B) :
    Convex ℝ (linearGraphSet LAB) := by
  -- Convexity is inherited from the linear graph submodule.
  simpa [linearGraphSet] using LAB.toLinearMap.graph.convex

/-- Helper for Theorem 15.23: the graph of a continuous linear map is a cone in the textbook
positive-scaling sense. This is the source-side cone structure used when passing between
orthogonality and cone duality. -/
lemma linearGraphSet_isCone
    {A : Type*} {B : Type*}
    [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
    [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B]
    (LAB : A →L[ℝ] B) :
    IsCone (linearGraphSet LAB) := by
  rw [isCone_iff]
  ext z
  constructor
  · intro hz
    -- The unit scalar already witnesses every graph point as a positive multiple of itself.
    exact Set.mem_smul.mpr ⟨1, by simp, z, hz, by simp⟩
  · rintro ⟨a, ha, y, hy, rfl⟩
    -- Positive scaling preserves the graph equation because `LAB` is linear.
    have hy_graph : y.2 = LAB y.1 := by
      simpa [linearGraphSet, LinearMap.mem_graph_iff] using hy
    simpa [linearGraphSet, LinearMap.mem_graph_iff] using
      congrArg (fun t : B ↦ a • t) hy_graph

/-- Helper for Theorem 15.23: for the linear graph cone, the source polar-cone condition is
equivalent to vanishing of the inner product against every graph vector. This is the exact
orthogonality bridge from Corollary 15.14 used later in the graph reduction. -/
lemma mem_polarCone_linearGraphSet_iff_forall_inner_eq_zero
    {A : Type*} {B : Type*}
    [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
    [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B]
    [InnerProductSpace ℝ (A × B)]
    (LAB : A →L[ℝ] B) (u : A × B) :
    u ∈ (linearGraphSet LAB)ᵒ⊖ ↔
      ∀ z ∈ linearGraphSet LAB, ⟪z, u⟫_ℝ = 0 := by
  constructor
  · intro hu
    rw [Set.mem_polarCone_iff_forall_inner_nonpos] at hu
    intro z hz
    have hnonpos : ⟪z, u⟫_ℝ ≤ 0 := by
      exact hu z hz
    have hzneg : -z ∈ linearGraphSet LAB := by
      simpa [linearGraphSet, LinearMap.mem_graph_iff] using hz
    have hneg_nonpos : ⟪-z, u⟫_ℝ ≤ 0 := hu (-z) hzneg
    have hnonneg : 0 ≤ ⟪z, u⟫_ℝ := by
      simpa [inner_neg_left] using hneg_nonpos
    exact le_antisymm hnonpos hnonneg
  · intro hu
    rw [Set.mem_polarCone_iff_forall_inner_nonpos]
    intro z hz
    exact (hu z hz).le

/-- Helper for Theorem 15.23: for the linear graph cone, the source dual cone is the same
orthogonality condition as the polar cone, because the graph is a subspace and hence symmetric
under negation. -/
lemma mem_dualCone_linearGraphSet_iff_forall_inner_eq_zero
    {A : Type*} {B : Type*}
    [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
    [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B]
    [InnerProductSpace ℝ (A × B)]
    (LAB : A →L[ℝ] B) (u : A × B) :
    u ∈ (linearGraphSet LAB)ᵒ⊕ ↔
      ∀ z ∈ linearGraphSet LAB, ⟪z, u⟫_ℝ = 0 := by
  rw [Set.mem_dualCone_iff, mem_polarCone_linearGraphSet_iff_forall_inner_eq_zero]
  constructor
  · intro hneg
    intro z hz
    simpa [inner_neg_right] using hneg z hz
  · intro hu
    intro z hz
    simpa [inner_neg_right] using hu z hz

/-- Helper for Theorem 15 23: the indicator of the restricted graph `gra LAB` belongs to
`Γ₀(A × B)`. This packages the graph term used in the closed-span product reduction. -/
lemma graphIndicator_mem_gammaZero
    {A : Type*} {B : Type*}
    [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
    [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B]
    (LAB : A →L[ℝ] B) :
    ι[linearGraphSet LAB] ∈ Γ₀(A × B) := by
  rw [mem_gammaZero_iff]
  have hindicator_lsc :
      LowerSemicontinuous (fun y : A × B ↦ ((ι[linearGraphSet LAB]) y : EReal)) := by
    -- Closedness of the graph is exactly lower semicontinuity of its indicator.
    simpa using
      (lowerSemicontinuous_indicator_compl_top_iff_isClosed (linearGraphSet LAB)).2
        (linearGraphSet_isClosed LAB)
  have hindicator_dom :
      effectiveDomain (ι[linearGraphSet LAB]) = linearGraphSet LAB := by
    -- The indicator is finite exactly on the graph.
    simpa using effectiveDomain_indicator (linearGraphSet LAB)
  refine ⟨hindicator_lsc, ?_⟩
  refine ⟨by simpa [hindicator_dom] using linearGraphSet_nonempty LAB, subset_rfl, ?_⟩
  intro y hy z hz a ha0 ha1
  have hyGraph : y ∈ linearGraphSet LAB := by
    simpa [hindicator_dom] using hy
  have hzGraph : z ∈ linearGraphSet LAB := by
    simpa [hindicator_dom] using hz
  have hayzGraph : a • y + (1 - a) • z ∈ linearGraphSet LAB :=
    linearGraphSet_convex LAB hyGraph hzGraph ha0.le (sub_nonneg.mpr ha1.le) (by ring)
  -- Once the convex combination stays on the graph, the indicator inequality is immediate.
  simp [ERealFunction.indicator, hyGraph, hzGraph, hayzGraph]

/-- Helper for Theorem 15 23: `dom (f.asEReal)` lies in the closed span of `effectiveDomain f`.
This packages the domain-to-closed-span bridge without reopening the dual transport layer. -/
lemma dom_asEReal_subset_closedSpan_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) :
    dom f.asEReal ⊆
      (((Submodule.span ℝ (effectiveDomain f)).topologicalClosure : Submodule ℝ H) : Set H) := by
  intro x hx
  -- Read `x ∈ dom (f.asEReal)` as finiteness of `f x`, then place that point in the closed span.
  have hx_eff : x ∈ effectiveDomain f := by
    rw [mem_effectiveDomain_iff]
    exact lt_of_le_of_ne le_top ((mem_dom_iff_ne_top _ _).1 hx)
  exact
    (Submodule.span ℝ (effectiveDomain f)).le_topologicalClosure
      (Submodule.subset_span hx_eff)

/-- Helper for Theorem 15 23: when `0 ∈ effectiveDomain f`, points of `dom (g.asEReal)` already
lie in the closed span of `effectiveDomain g - L '' effectiveDomain f`. -/
lemma dom_asEReal_subset_closedSpan_sub_image_difference
    (f : H → Set.Ioi (⊥ : EReal))
    (g : K → Set.Ioi (⊥ : EReal))
    (L : H →L[ℝ] K)
    (hzero_f : (0 : H) ∈ effectiveDomain f) :
    dom g.asEReal ⊆
      (((Submodule.span ℝ (effectiveDomain g - L '' effectiveDomain f)).topologicalClosure :
        Submodule ℝ K) : Set K) := by
  intro y hy
  -- Convert the `dom` witness back to the `effectiveDomain` owner and reuse the closed-span lemma.
  have hy_eff : y ∈ effectiveDomain g := by
    rw [mem_effectiveDomain_iff]
    exact lt_of_le_of_ne le_top ((mem_dom_iff_ne_top _ _).1 hy)
  exact
    effectiveDomain_subset_closedSpan_sub_image_difference
      (f := f) (g := g) (L := L) hzero_f hy_eff

/-- Helper for Theorem 15 23: if `L(A) ⊆ B`, then the `A`-projection of `L† v` only depends on
the `B`-projection of `v`. This is the abstract closed-submodule form of source lines `(15.34)` and
`(15.35)`. -/
lemma projectedAdjoint_eq_of_image_subset_closedSubmodule
    {A : ClosedSubmodule ℝ H} {B : ClosedSubmodule ℝ K}
    (L : H →L[ℝ] K)
    (hImage : ∀ x : (A : Submodule ℝ H), L x ∈ (B : Set K))
    (v : K) :
    A.starProjection (L.adjoint v) = A.starProjection (L.adjoint (B.starProjection v)) := by
  have hkill_orthogonal :
      ∀ {w : K}, w ∈ (B : Submodule ℝ K)ᗮ → (A.starProjection.comp L.adjoint) w = 0 := by
    intro w hw
    have hAdj_mem : L.adjoint w ∈ (A : Submodule ℝ H)ᗮ := by
      rw [Submodule.mem_orthogonal']
      intro x hx
      have hLxB : L x ∈ (B : Set K) := hImage ⟨x, hx⟩
      have hinner : ⟪w, L x⟫_ℝ = 0 := (Submodule.mem_orthogonal' _ _).1 hw (L x) hLxB
      simpa [ContinuousLinearMap.adjoint_inner_left] using hinner
    -- Once `L† w` is orthogonal to `A`, its `A`-projection vanishes.
    exact (Submodule.starProjection_apply_eq_zero_iff (K := (A : Submodule ℝ H))).2 hAdj_mem
  have hresidual :
      A.starProjection (L.adjoint (v - B.starProjection v)) = 0 :=
    hkill_orthogonal
      ((Submodule.sub_starProjection_mem_orthogonal (K := (B : Submodule ℝ K)) v))
  have hv_split : v = B.starProjection v + (v - B.starProjection v) := by
    abel
  -- Decompose `v` into its `B` and `Bᗮ` parts and kill the orthogonal component.
  calc
    A.starProjection (L.adjoint v)
        = A.starProjection (L.adjoint (B.starProjection v + (v - B.starProjection v))) := by
            nth_rw 1 [hv_split]
    _ = A.starProjection (L.adjoint (B.starProjection v) + L.adjoint (v - B.starProjection v)) := by
          rw [map_add]
    _ = A.starProjection (L.adjoint (B.starProjection v)) +
          A.starProjection (L.adjoint (v - B.starProjection v)) := by
            simp
    _ = A.starProjection (L.adjoint (B.starProjection v)) := by rw [hresidual, add_zero]

/-- Helper for Theorem 15.23: the orthogonal projection onto a closed subspace fixes subtype
vectors of that subspace. This is the closed-span coercion adapter needed in the later dual
transport. -/
lemma orthogonalProjection_subtype_eq_self
    {B : ClosedSubmodule ℝ K} (vB : B) :
    B.orthogonalProjection (vB : K) = vB := by
  -- Read the subtype point as an ambient vector already lying in `B`, so the projection is fixed.
  simpa using
    (Submodule.orthogonalProjection_mem_subspace_eq_self (B.orthogonalProjection (vB : K)))

/-- Helper for Theorem 15.23: when a closed subspace is viewed through its underlying submodule,
its carrier still inherits completeness. This restores the typeclass bridge needed by the
restricted dual owners built on closed spans. -/
instance completeSpace_submodule_of_closedSubmodule
    {X : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    {V : ClosedSubmodule ℝ X} :
    CompleteSpace ((V : Submodule ℝ X)) := by
  simpa using (instCompleteSpaceSubtypeMemClosedSubmodule V : CompleteSpace ↥V)

/-- Helper for Theorem 15.23: the carrier of a closed subspace inherits the ambient normed-group
structure. This lets later dual-owner statements stay on the visible carrier type `V`. -/
instance normedAddCommGroup_closedSubmodule
    {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {V : ClosedSubmodule ℝ X} :
    NormedAddCommGroup ↥V := by
  simpa using (inferInstance : NormedAddCommGroup ↥(V : Submodule ℝ X))

/-- Helper for Theorem 15.23: the carrier of a closed subspace inherits the ambient scalar-norm
structure. -/
instance normedSpace_closedSubmodule
    {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {V : ClosedSubmodule ℝ X} :
    NormedSpace ℝ ↥V := by
  simpa using (inferInstance : NormedSpace ℝ ↥(V : Submodule ℝ X))

/-- Helper for Theorem 15.23: the carrier of a closed subspace inherits the ambient inner-product
structure. -/
instance innerProductSpace_closedSubmodule
    {X : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    {V : ClosedSubmodule ℝ X} :
    InnerProductSpace ℝ ↥V := by
  simpa using (inferInstance : InnerProductSpace ℝ ↥(V : Submodule ℝ X))

/-- Helper for Theorem 15.23: the visible carrier type of a closed subspace is complete. This is
the carrier-visible counterpart of `completeSpace_submodule_of_closedSubmodule`. -/
instance completeSpace_closedSubmodule
    {X : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    {V : ClosedSubmodule ℝ X} :
    CompleteSpace ↥V := by
  simpa using (instCompleteSpaceSubtypeMemClosedSubmodule V : CompleteSpace ↥V)

/-- Helper for Theorem 15.23: the textbook closed span generated by `effectiveDomain f`. -/
abbrev effectiveDomainClosedSpan (f : H → Set.Ioi (⊥ : EReal)) : ClosedSubmodule ℝ H :=
  ⟨(Submodule.span ℝ (effectiveDomain f)).topologicalClosure,
    Submodule.isClosed_topologicalClosure _⟩

/-- Helper for Theorem 15.23: the textbook closed span generated by
`effectiveDomain g - L '' effectiveDomain f`. -/
abbrev subImageDifferenceClosedSpan
    (f : H → Set.Ioi (⊥ : EReal))
    (g : K → Set.Ioi (⊥ : EReal))
    (L : H →L[ℝ] K) :
    ClosedSubmodule ℝ K :=
  ⟨(Submodule.span ℝ (effectiveDomain g - L '' effectiveDomain f)).topologicalClosure,
    Submodule.isClosed_topologicalClosure _⟩

/-- Helper for Theorem 15.23: `f` restricted to the closed span of its effective domain. -/
abbrev restrictToEffectiveDomainClosedSpan
    (f : H → Set.Ioi (⊥ : EReal)) :
    effectiveDomainClosedSpan f → Set.Ioi (⊥ : EReal) := fun x ↦ f x

/-- Helper for Theorem 15.23: `g` restricted to the closed span of
`effectiveDomain g - L '' effectiveDomain f`. -/
abbrev restrictToSubImageDifferenceClosedSpan
    (f : H → Set.Ioi (⊥ : EReal))
    (g : K → Set.Ioi (⊥ : EReal))
    (L : H →L[ℝ] K) :
    subImageDifferenceClosedSpan f g L → Set.Ioi (⊥ : EReal) := fun y ↦ g y

/-- Helper for Theorem 15.23: the restriction of `L` between the textbook closed spans. -/
abbrev restrictedMapOnClosedSpans
    (f : H → Set.Ioi (⊥ : EReal))
    (g : K → Set.Ioi (⊥ : EReal))
    (L : H →L[ℝ] K) :
    effectiveDomainClosedSpan f →L[ℝ] subImageDifferenceClosedSpan f g L :=
  (subImageDifferenceClosedSpan f g L).orthogonalProjection.comp
    (L.comp (effectiveDomainClosedSpan f).subtypeL)

/-- Helper for Theorem 15.23: the closed span of `effectiveDomain f` is complete. -/
instance effectiveDomainClosedSpan_completeSpace
    (f : H → Set.Ioi (⊥ : EReal)) :
    CompleteSpace ↥(effectiveDomainClosedSpan f) := by
  exact completeSpace_closedSubmodule (V := effectiveDomainClosedSpan f)

/-- Helper for Theorem 15.23: the closed span of
`effectiveDomain g - L '' effectiveDomain f` is complete. -/
instance subImageDifferenceClosedSpan_completeSpace
    (f : H → Set.Ioi (⊥ : EReal))
    (g : K → Set.Ioi (⊥ : EReal))
    (L : H →L[ℝ] K) :
    CompleteSpace ↥(subImageDifferenceClosedSpan f g L) := by
  exact completeSpace_closedSubmodule (V := subImageDifferenceClosedSpan f g L)

/-- Helper for Theorem 15.23: the dual owner of the closed-span restriction with the subtype
completeness instances frozen explicitly. This keeps later attainment statements from redoing the
same expensive instance search. -/
abbrev restrictedCompositeDualObjective
    (f : H → Set.Ioi (⊥ : EReal))
    (g : K → Set.Ioi (⊥ : EReal))
    (L : H →L[ℝ] K) :
    subImageDifferenceClosedSpan f g L → EReal :=
  @compositeDualObjective
    (effectiveDomainClosedSpan f)
    (subImageDifferenceClosedSpan f g L)
    inferInstance
    inferInstance
    inferInstance
    inferInstance
    (effectiveDomainClosedSpan_completeSpace f)
    (subImageDifferenceClosedSpan_completeSpace f g L)
    (restrictToEffectiveDomainClosedSpan f)
    (restrictToSubImageDifferenceClosedSpan f g L)
    (restrictedMapOnClosedSpans f g L)

/-- Helper for Theorem 15.23: the primal optimal value of the closed-span restriction. -/
abbrev restrictedCompositePrimalOptimalValue
    (f : H → Set.Ioi (⊥ : EReal))
    (g : K → Set.Ioi (⊥ : EReal))
    (L : H →L[ℝ] K) :
    EReal :=
  compositePrimalOptimalValue
    (restrictToEffectiveDomainClosedSpan f)
    (restrictToSubImageDifferenceClosedSpan f g L)
    (restrictedMapOnClosedSpans f g L)

set_option maxHeartbeats 500000 in
/-- Helper for Theorem 15 23: after freezing the textbook closed spans `A` and `B`, the ambient
dual owner depends only on the orthogonal projection onto `B`. This is the source line `(15.35)`
rewritten directly in the owner notation `compositeDualObjective`. -/
lemma ambient_compositeDualObjective_eq_restricted_compositeDualObjective_comp_starProjection
    (f : H → Set.Ioi (⊥ : EReal))
    (g : K → Set.Ioi (⊥ : EReal))
    (L : H →L[ℝ] K)
    (hzero_f : (0 : H) ∈ effectiveDomain f)
    (hzero_g : (0 : K) ∈ effectiveDomain g)
    (v : K) :
    compositeDualObjective f g L v =
      restrictedCompositeDualObjective f g L
        ((subImageDifferenceClosedSpan f g L).orthogonalProjection v) := by
  let A : ClosedSubmodule ℝ H := effectiveDomainClosedSpan f
  let B : ClosedSubmodule ℝ K := subImageDifferenceClosedSpan f g L
  let fA : A → Set.Ioi (⊥ : EReal) := restrictToEffectiveDomainClosedSpan f
  let gB : B → Set.Ioi (⊥ : EReal) := restrictToSubImageDifferenceClosedSpan f g L
  let M : A →L[ℝ] B := restrictedMapOnClosedSpans f g L
  letI : CompleteSpace ↥A := by
    simpa [A] using effectiveDomainClosedSpan_completeSpace f
  letI : CompleteSpace ↥B := by
    simpa [B] using subImageDifferenceClosedSpan_completeSpace f g L
  letI : CompleteSpace ↥(effectiveDomainClosedSpan f) :=
    effectiveDomainClosedSpan_completeSpace f
  letI : CompleteSpace ↥(subImageDifferenceClosedSpan f g L) :=
    subImageDifferenceClosedSpan_completeSpace f g L
  have hA_complete : CompleteSpace ↥A := by
    infer_instance
  have hB_complete : CompleteSpace ↥B := by
    infer_instance
  let adjAK : (A →L[ℝ] K) → K →L[ℝ] A :=
    @ContinuousLinearMap.adjoint ℝ A K
      inferInstance inferInstance inferInstance inferInstance inferInstance
      hA_complete inferInstance
  let adjAB : (A →L[ℝ] B) → B →L[ℝ] A :=
    @ContinuousLinearMap.adjoint ℝ A B
      inferInstance inferInstance inferInstance inferInstance inferInstance
      hA_complete hB_complete
  let Madj : B →L[ℝ] A :=
    adjAB M
  have hdomA :
      dom f.asEReal ⊆ (A : Set H) := by
    simpa [A, effectiveDomainClosedSpan] using
      dom_asEReal_subset_closedSpan_effectiveDomain (f := f)
  have hdomB :
      dom g.asEReal ⊆ (B : Set K) := by
    simpa [B, subImageDifferenceClosedSpan] using
      dom_asEReal_subset_closedSpan_sub_image_difference
        (f := f) (g := g) (L := L) hzero_f
  have hconj_proj_eval (u : H) :
      f.asEReal∗ u = f.asEReal∗ (A.starProjection u) := by
    simpa [Function.comp] using
      congrFun
        (conjugate_eq_conjugate_comp_starProjection_of_dom_subset f.asEReal A hdomA)
        u
  have hAproj :
      A.starProjection (L.adjoint v) =
        A.starProjection (L.adjoint (B.starProjection v)) := by
    simpa [A, B, effectiveDomainClosedSpan, subImageDifferenceClosedSpan] using
      restricted_adjoint_apply_eq_projected_adjoint_of_zero_domain_data
        (f := f) (g := g) (L := L) hzero_g v
  have hAproj_neg :
      A.starProjection (-(L.adjoint v)) =
        A.starProjection (-(L.adjoint (B.starProjection v))) := by
    simpa using congrArg Neg.neg hAproj
  have hf_proj :
      f.asEReal∗ (-(L.adjoint v)) =
        f.asEReal∗ (-(L.adjoint (B.starProjection v))) := by
    calc
      f.asEReal∗ (-(L.adjoint v)) =
          f.asEReal∗ (A.starProjection (-(L.adjoint v))) := by
            exact hconj_proj_eval (-(L.adjoint v))
      _ =
          f.asEReal∗ (A.starProjection (-(L.adjoint (B.starProjection v)))) := by
            rw [hAproj_neg]
      _ = f.asEReal∗ (-(L.adjoint (B.starProjection v))) := by
            exact (hconj_proj_eval (-(L.adjoint (B.starProjection v)))).symm
  have hg_restrict :
      gB.asEReal∗ (B.orthogonalProjection v) = g.asEReal∗ v := by
    -- Restrict the second conjugate directly to the closed span `B`.
    have hleft :
        gB.asEReal∗ (B.orthogonalProjection v) =
          ⨆ x : B, (((⟪(x : K), v⟫_ℝ : ℝ) : EReal) - g x) := by
      rw [ERealFunction.conjugate_apply]
      refine iSup_congr ?_
      intro x
      have hinner :
          ⟪x, B.orthogonalProjection v⟫_ℝ = ⟪(x : K), v⟫_ℝ := by
        exact
          Submodule.inner_orthogonalProjection_eq_of_mem_left
            (K := (B : Submodule ℝ K)) x v
      simp [gB, restrictToSubImageDifferenceClosedSpan, hinner]
    rw [hleft]
    simpa using
      congrFun
        (conjugate_restrict_comp_orthogonalProjection_of_dom_subset g.asEReal B hdomB)
        v
  -- Rewrite both summands through the `B`-projection and then fold them back into the restricted
  -- dual owner.
  calc
    compositeDualObjective f g L v =
        f.asEReal∗ (-(L.adjoint (B.starProjection v))) +
          g.asEReal∗ v := by
          rw [compositeDualObjective_apply, hf_proj]
    _ =
        restrictedCompositeDualObjective f g L
          ((subImageDifferenceClosedSpan f g L).orthogonalProjection v) := by
            change
              f.asEReal∗ (-(L.adjoint (B.starProjection v))) + g.asEReal∗ v =
                fA.asEReal∗ (-(Madj (B.orthogonalProjection v))) +
                  gB.asEReal∗ (B.orthogonalProjection v)
            refine congrArg₂ (fun a b : EReal ↦ a + b) ?_ ?_
            · have hfirst_left :
                  fA.asEReal∗ (A.orthogonalProjection (-(L.adjoint (B.starProjection v)))) =
                    ⨆ x : A, (((⟪(x : H), -(L.adjoint (B.starProjection v))⟫_ℝ : ℝ) : EReal) - f x) := by
                rw [ERealFunction.conjugate_apply]
                refine iSup_congr ?_
                intro x
                have hinner :
                    ⟪x, A.orthogonalProjection (-(L.adjoint (B.starProjection v)))⟫_ℝ =
                      ⟪(x : H), -(L.adjoint (B.starProjection v))⟫_ℝ := by
                  exact
                    Submodule.inner_orthogonalProjection_eq_of_mem_left
                      (K := (A : Submodule ℝ H)) x (-(L.adjoint (B.starProjection v)))
                -- Rewrite the restricted conjugate summand directly through the ambient inner
                -- product identity to avoid the fragile negative/projection simp path.
                simpa [fA, restrictToEffectiveDomainClosedSpan] using
                  congrArg (fun t : ℝ ↦ (((t : ℝ) : EReal) - f x)) hinner
              have hfirst_raw :
                  ⨆ x : A, (((⟪(x : H), -(L.adjoint (B.starProjection v))⟫_ℝ : ℝ) : EReal) - f x) =
                    f.asEReal∗ (-(L.adjoint (B.starProjection v))) := by
                simpa using
                  congrFun
                    (conjugate_restrict_comp_orthogonalProjection_of_dom_subset
                      f.asEReal A hdomA)
                    (-(L.adjoint (B.starProjection v)))
              calc
                f.asEReal∗ (-(L.adjoint (B.starProjection v))) =
                    fA.asEReal∗ (A.orthogonalProjection (-(L.adjoint (B.starProjection v)))) := by
                      rw [hfirst_left]
                      exact hfirst_raw.symm
                _ = fA.asEReal∗
                      (-(Madj (B.orthogonalProjection v))) := by
                      -- TODO: prove the explicit adjoint transport
                      -- `Madj (B.orthogonalProjection v) =
                      --  A.orthogonalProjection (L.adjoint (B.starProjection v))`
                      -- by a coercion-stable inner-product argument on `A`.
                      have hMadj :
                          Madj (B.orthogonalProjection v) =
                            A.orthogonalProjection (L.adjoint (B.starProjection v)) := sorry
                      have hMadj_neg :
                          A.orthogonalProjection (-(L.adjoint (B.starProjection v))) =
                            -(Madj (B.orthogonalProjection v)) := by
                        calc
                          A.orthogonalProjection (-(L.adjoint (B.starProjection v))) =
                              -A.orthogonalProjection (L.adjoint (B.starProjection v)) := by
                                simp
                          _ = -(Madj (B.orthogonalProjection v)) := by
                                rw [hMadj]
                                rfl
                      rw [hMadj_neg]
            · exact hg_restrict.symm

/-- Helper for Theorem 15 23: on subtype vectors of the closed span `B`, the ambient and
restricted dual owners agree pointwise. This is the coercion-free closing rewrite used after a
restricted minimizer has been found. -/
lemma ambient_dual_value_eq_restricted_dual_value_on_subtype_minimizer
    (f : H → Set.Ioi (⊥ : EReal))
    (g : K → Set.Ioi (⊥ : EReal))
    (L : H →L[ℝ] K)
    (hzero_f : (0 : H) ∈ effectiveDomain f)
    (hzero_g : (0 : K) ∈ effectiveDomain g)
    (vB : subImageDifferenceClosedSpan f g L) :
    compositeDualObjective f g L (vB : K) =
      restrictedCompositeDualObjective f g L vB := by
  -- The previous projection formula collapses because the orthogonal projection fixes subtype
  -- points of `B`.
  simpa
      [restrictToEffectiveDomainClosedSpan, restrictToSubImageDifferenceClosedSpan,
        restrictedMapOnClosedSpans, orthogonalProjection_subtype_eq_self] using
    ambient_compositeDualObjective_eq_restricted_compositeDualObjective_comp_starProjection
      (f := f) (g := g) (L := L) hzero_f hzero_g (vB : K)

/-- Helper for Theorem 15 23: if a `Γ₀` function contains the origin in its effective domain, then
its restriction to a closed subspace still belongs to `Γ₀`. This is the properness bridge needed
for the closed-span specialization. -/
lemma restrict_mem_gammaZero_of_zero_mem_effectiveDomain
    {X : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (F : X → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(X))
    (hzero_F : (0 : X) ∈ effectiveDomain F)
    (V : ClosedSubmodule ℝ X) :
    (fun x : (V : Submodule ℝ X) ↦ F x) ∈ Γ₀((V : Submodule ℝ X)) := by
  rw [mem_gammaZero_iff] at hF ⊢
  constructor
  · -- Lower semicontinuity is preserved by the continuous subtype inclusion.
    simpa using hF.1.comp continuous_subtype_val
  · refine ⟨?_, subset_rfl, ?_⟩
    · -- The origin remains a domain witness after restricting to any closed subspace.
      refine ⟨0, ?_⟩
      simpa [mem_effectiveDomain_iff] using hzero_F
    · intro x hx y hy a ha0 ha1
      have hx' : (x : X) ∈ effectiveDomain F := by
        simpa [mem_effectiveDomain_iff] using hx
      have hy' : (y : X) ∈ effectiveDomain F := by
        simpa [mem_effectiveDomain_iff] using hy
      -- Convexity on the subtype is the ambient convexity evaluated on subtype vectors.
      simpa using hF.2.ineq hx' hy' ha0 ha1

section ProductGraphL2

variable {X : Type*} {Y : Type*}
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

/-- Helper for Theorem 15.23: in the product-graph reduction, the raw pair space `X × Y` is
equipped with the transported `ℓ²` seminormed-group structure from `WithLp 2 (X × Y)`. -/
local instance prod_seminormedAddCommGroup_l2_graph : SeminormedAddCommGroup (X × Y) :=
  WithLp.seminormedAddCommGroupToProd (p := 2) X Y

/-- Helper for Theorem 15.23: in the product-graph reduction, the raw pair space `X × Y` carries
the transported `ℓ²` normed-group structure. -/
local instance prod_normedAddCommGroup_l2_graph : NormedAddCommGroup (X × Y) :=
  WithLp.normedAddCommGroupToProd (p := 2) X Y

/-- Helper for Theorem 15.23: the transported `ℓ²` norm on the raw pair space is compatible with
the scalar action of `ℝ`. -/
local instance prod_normedSpace_l2_graph : NormedSpace ℝ (X × Y) := by
  letI : NormedAddCommGroup (X × Y) := prod_normedAddCommGroup_l2_graph (X := X) (Y := Y)
  exact WithLp.normedSpaceSeminormedAddCommGroupToProd 2 X Y

/-- Helper for Theorem 15.23: completeness of the raw pair space is transported from
`WithLp 2 (X × Y)`. -/
local instance prod_completeSpace_l2_graph : CompleteSpace (X × Y) := by
  letI : PseudoMetricSpace (X × Y) := WithLp.pseudoMetricSpaceToProd (p := 2) X Y
  exact (WithLp.uniformEquivProd (p := 2) X Y).completeSpace_iff.1 inferInstance

/-- Helper for Theorem 15.23: in the graph-model block, the raw pair space carries the textbook
`ℓ²` inner product `⟪(x₁,y₁),(x₂,y₂)⟫ = ⟪x₁,x₂⟫ + ⟪y₁,y₂⟫`. -/
local instance prod_innerProductSpace_l2_graph : InnerProductSpace ℝ (X × Y) where
  inner x y := ⟪x.1, y.1⟫_ℝ + ⟪x.2, y.2⟫_ℝ
  norm_sq_eq_re_inner x := by
    have hnorm : ‖x‖ = ‖WithLp.toLp 2 x‖ := by
      simpa using
        (WithLp.norm_seminormedAddCommGroupToProd (p := 2) (α := X) (β := Y) x)
    have hnorm_sq : ‖x‖ ^ 2 = ‖WithLp.toLp 2 x‖ ^ 2 := by
      simpa using congrArg (fun t : ℝ ↦ t ^ 2) hnorm
    exact hnorm_sq.trans <| by
      simpa [sq] using (WithLp.prod_norm_sq_eq_of_L2 (x := WithLp.toLp 2 x))
  conj_inner_symm x y := by
    simp [real_inner_comm]
  add_left x y z := by
    simp [inner_add_left, add_assoc, add_left_comm]
  smul_left x y r := by
    simp [inner_smul_left, mul_add]

/-- Helper for Theorem 15 23: orthogonality to the graph of `M` is exactly the adjoint equation
`w.1 + M† w.2 = 0`. This is the Lean form of the source graph-orthogonality constraint used in the
product-space reduction. -/
lemma mem_orthogonal_graph_iff
    (M : X →L[ℝ] Y) (w : X × Y) :
    w ∈ ((((M.toLinearMap.graph : Submodule ℝ (X × Y))ᗮ :
      Submodule ℝ (X × Y)) : Set (X × Y))) ↔
      w.1 + M.adjoint w.2 = 0 := by
  constructor
  · intro hw
    -- Test orthogonality against the generic graph point `(x, M x)` and read the resulting
    -- pairing identity as the source adjoint equation.
    apply ext_inner_right ℝ
    intro x
    have hgraph :
        ⟪w, (x, M x)⟫_ℝ = 0 :=
      (Submodule.mem_orthogonal' _ _).1 hw (x, M x) (by
        simpa [LinearMap.mem_graph_iff])
    simpa [inner_add_left, ContinuousLinearMap.adjoint_inner_left] using hgraph
  · intro hw
    -- Conversely, rewrite every graph pairing through the adjoint equation and conclude that all
    -- graph points are orthogonal to `w`.
    refine (Submodule.mem_orthogonal' _ _).2 ?_
    intro z hz
    rcases z with ⟨x, y⟩
    rw [LinearMap.mem_graph_iff] at hz
    calc
      ⟪w, (x, y)⟫_ℝ = ⟪w.1, x⟫_ℝ + ⟪w.2, y⟫_ℝ := by
        rfl
      _ = ⟪w.1, x⟫_ℝ + ⟪w.2, M x⟫_ℝ := by
        simpa using congrArg (fun t : Y ↦ ⟪w.2, t⟫_ℝ) hz
      _ = ⟪w.1 + M.adjoint w.2, x⟫_ℝ := by
        simpa [inner_add_left, ContinuousLinearMap.adjoint_inner_left]
      _ = 0 := by simpa [hw]

/-- Helper for Theorem 15 23: the product dual point `(M† v, -v)` lies in the orthogonal
complement of the graph of `M`. This freezes the sign convention used later in the product-space
dual rewrite. -/
lemma pair_adjoint_neg_mem_orthogonal_graph
    (M : X →L[ℝ] Y) (v : Y) :
    (M.adjoint v, -v) ∈
      ((((M.toLinearMap.graph : Submodule ℝ (X × Y))ᗮ :
        Submodule ℝ (X × Y)) : Set (X × Y))) := by
  -- The previous orthogonality characterization collapses to a one-line adjoint cancellation.
  rw [mem_orthogonal_graph_iff]
  simp

/-- Helper for Theorem 15.23: every vector orthogonal to the graph of `M` has the canonical
source form `(M† v, -v)`. This is the product-space parameterization used to return from the raw
Fenchel dual variable to the composite dual variable. -/
lemma orthogonal_graph_point_eq_pair_adjoint_neg
    (M : X →L[ℝ] Y) {u : X × Y}
    (hu : u ∈ ((((M.toLinearMap.graph : Submodule ℝ (X × Y))ᗮ :
      Submodule ℝ (X × Y)) : Set (X × Y)))) :
    ∃ v : Y, u = (M.adjoint v, -v) := by
  refine ⟨-u.2, ?_⟩
  have hu_eq_zero : u.1 + M.adjoint u.2 = 0 :=
    (mem_orthogonal_graph_iff (M := M) (w := u)).1 hu
  have hu_fst : u.1 = -(M.adjoint u.2) := by
    simpa using eq_neg_of_add_eq_zero_left hu_eq_zero
  -- Read the orthogonal vector through the canonical witness `v = -u.2`.
  ext <;> simp [hu_fst]

/-- Helper for Theorem 15.23: the Fenchel conjugate of the separable product objective
`(x, y) ↦ φ x + ψ y` splits into the sum of the coordinatewise conjugates. -/
lemma conjugate_separable_sum_apply_pair
    (φ : X → Set.Ioi (⊥ : EReal))
    (ψ : Y → Set.Ioi (⊥ : EReal))
    (u : X) (v : Y) :
    (((fun p : X × Y ↦ φ p.1) + fun p : X × Y ↦ ψ p.2).asEReal∗) (u, v) =
      φ.asEReal∗ u + ψ.asEReal∗ v := by
  rw [conjugate_apply]
  -- Separate the product supremum into the two coordinate suprema.
  calc
    (⨆ p : X × Y,
        (((⟪p, (u, v)⟫_ℝ : ℝ) : EReal) -
          ((((fun p : X × Y ↦ φ p.1) + fun p : X × Y ↦ ψ p.2) p : Set.Ioi (⊥ : EReal)) :
            EReal))) =
      ⨆ x : X, ⨆ y : Y,
        ((((⟪x, u⟫_ℝ : ℝ) : EReal) - (φ x : EReal)) +
          (((⟪y, v⟫_ℝ : ℝ) : EReal) - (ψ y : EReal))) := by
          rw [iSup_prod]
          refine iSup_congr fun x ↦ ?_
          refine iSup_congr fun y ↦ ?_
          have hφ_ne_bot : (φ x : EReal) ≠ ⊥ := ne_of_gt (φ x).2
          have hψ_ne_bot : (ψ y : EReal) ≠ ⊥ := ne_of_gt (ψ y).2
          -- The product affine defect is the sum of the coordinate defects.
          change
            (((⟪(x, y), (u, v)⟫_ℝ : ℝ) : EReal) - ((φ x : EReal) + (ψ y : EReal))) =
              ((((⟪x, u⟫_ℝ : ℝ) : EReal) - (φ x : EReal)) +
                (((⟪y, v⟫_ℝ : ℝ) : EReal) - (ψ y : EReal)))
          have hinner :
              (((⟪(x, y), (u, v)⟫_ℝ : ℝ) : EReal)) =
                (((⟪x, u⟫_ℝ : ℝ) : EReal) + (((⟪y, v⟫_ℝ : ℝ) : EReal))) := by
            change (((⟪x, u⟫_ℝ + ⟪y, v⟫_ℝ : ℝ) : EReal)) =
              (((⟪x, u⟫_ℝ : ℝ) : EReal) + (((⟪y, v⟫_ℝ : ℝ) : EReal)))
            simp
          rw [hinner]
          rw [sub_eq_add_neg, EReal.neg_add (.inl hφ_ne_bot) (.inr hψ_ne_bot), sub_eq_add_neg,
            sub_eq_add_neg]
          rw [sub_eq_add_neg]
          simpa [add_assoc, add_left_comm, add_comm]
    _ = (⨆ x : X, (((⟪x, u⟫_ℝ : ℝ) : EReal) - (φ x : EReal))) +
          (⨆ y : Y, (((⟪y, v⟫_ℝ : ℝ) : EReal) - (ψ y : EReal))) := by
            simpa using
              ERealFunction.iSup_iSup_add_eq_add_iSup
                (a := fun x : X ↦ (((⟪x, u⟫_ℝ : ℝ) : EReal) - (φ x : EReal)))
                (b := fun y : Y ↦ (((⟪y, v⟫_ℝ : ℝ) : EReal) - (ψ y : EReal)))
    _ = φ.asEReal∗ u + ψ.asEReal∗ v := by
          rw [conjugate_apply, conjugate_apply]

/-- Helper for Theorem 15.23: evaluating the product-space Fenchel dual objective on the
orthogonal-graph parameterization `(M† v, -v)` recovers the owner dual objective
`compositeDualObjective φ ψ M v`. -/
lemma fenchelDualObjective_product_graph_eq_compositeDualObjective_on_adjoint_neg
    (φ : X → Set.Ioi (⊥ : EReal))
    (ψ : Y → Set.Ioi (⊥ : EReal))
    (M : X →L[ℝ] Y)
    (v : Y) :
    fenchelDualObjective
        ((fun p : X × Y ↦ φ p.1) + fun p : X × Y ↦ ψ p.2)
        (ι[linearGraphSet M])
        (M.adjoint v, -v) =
      compositeDualObjective φ ψ M v := by
  have hpair_mem :
      (M.adjoint v, -v) ∈
        ((((M.toLinearMap.graph : Submodule ℝ (X × Y))ᗮ :
          Submodule ℝ (X × Y)) : Set (X × Y))) :=
    pair_adjoint_neg_mem_orthogonal_graph (M := M) v
  have hindicator_zero :
      (((ι[linearGraphSet M]).asEReal)∗) (M.adjoint v, -v) = 0 := by
    -- The graph indicator conjugate vanishes on the orthogonal complement of the graph.
    simpa [linearGraphSet, ERealFunction.indicator, hpair_mem] using
      congrFun (conjugate_indicator_submodule_eq_indicator_orthogonal
        (V := M.toLinearMap.graph)) (M.adjoint v, -v)
  -- Evaluate the reflected separable conjugate at the canonical orthogonal slice.
  rw [fenchelDualObjective_apply, compositeDualObjective_apply, hindicator_zero, add_zero]
  simpa [ERealFunction.reverse_apply] using
    conjugate_separable_sum_apply_pair
      (φ := φ) (ψ := ψ) (u := -(M.adjoint v)) (v := v)

/-- Helper for Theorem 15.23: on the orthogonal complement of `graph(M)`, the graph-indicator
conjugate vanishes, so the raw Fenchel dual objective reduces to the reflected conjugate of the
separable product objective. -/
lemma fenchelDualObjective_separable_graph_eq_reflectedConjugate_on_orthogonal
    (φ : X → Set.Ioi (⊥ : EReal))
    (ψ : Y → Set.Ioi (⊥ : EReal))
    (M : X →L[ℝ] Y)
    {u : X × Y}
    (hu : u ∈ ((((M.toLinearMap.graph : Submodule ℝ (X × Y))ᗮ :
      Submodule ℝ (X × Y)) : Set (X × Y)))) :
    fenchelDualObjective
        ((fun p : X × Y ↦ φ p.1) + fun p : X × Y ↦ ψ p.2)
        (ι[linearGraphSet M])
        u =
      (((fun p : X × Y ↦ φ p.1) + fun p : X × Y ↦ ψ p.2).asEReal∗ᵛ) u := by
  have hindicator_zero :
      (((ι[linearGraphSet M]).asEReal)∗) u = 0 := by
    -- On the orthogonal slice, the indicator conjugate contributes exactly `0`.
    simpa [linearGraphSet, ERealFunction.indicator, hu] using
      congrFun (conjugate_indicator_submodule_eq_indicator_orthogonal
        (V := M.toLinearMap.graph)) u
  -- The raw dual objective is therefore just the reflected conjugate of the separable sum.
  rw [fenchelDualObjective_apply, hindicator_zero, add_zero]
  simp [ERealFunction.reverse_apply]

/-- Helper for Theorem 15.23: away from the orthogonal complement of `graph(M)`, the graph
indicator conjugate is `⊤`, so the raw Fenchel dual objective is infeasible. -/
lemma fenchelDualObjective_separable_graph_eq_top_off_orthogonal
    (φ : X → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(X))
    (ψ : Y → Set.Ioi (⊥ : EReal)) (hψ : ψ ∈ Γ₀(Y))
    (M : X →L[ℝ] Y)
    {u : X × Y}
    (hu : u ∉ ((((M.toLinearMap.graph : Submodule ℝ (X × Y))ᗮ :
      Submodule ℝ (X × Y)) : Set (X × Y)))) :
    fenchelDualObjective
        ((fun p : X × Y ↦ φ p.1) + fun p : X × Y ↦ ψ p.2)
        (ι[linearGraphSet M])
        u = ⊤ := by
  let P : X × Y → Set.Ioi (⊥ : EReal) := (fun p : X × Y ↦ φ p.1) + fun p ↦ ψ p.2
  have hP_gamma : P ∈ Γ₀(X × Y) := by
    -- The separable product objective is proper, so its reflected conjugate is never `⊥`.
    simpa [P] using separable_sum_mem_gammaZero (H := X) (K := Y) φ hφ ψ hψ
  have hP_reverse_ne_bot : P.asEReal∗ᵛ u ≠ ⊥ := by
    simpa [P, ERealFunction.reverse_apply] using
      conjugate_ne_bot_of_isProper (isProper_of_mem_gammaZero hP_gamma) (-u)
  have hindicator_top :
      (((ι[linearGraphSet M]).asEReal)∗) u = ⊤ := by
    -- Off the orthogonal slice, the graph indicator conjugate is infeasible.
    simpa [linearGraphSet, ERealFunction.indicator, hu] using
      congrFun (conjugate_indicator_submodule_eq_indicator_orthogonal
        (V := M.toLinearMap.graph)) u
  -- The `⊤` indicator-conjugate term forces the whole raw dual objective to be `⊤`.
  rw [fenchelDualObjective_apply, hindicator_top]
  exact EReal.add_top_of_ne_bot hP_reverse_ne_bot

/-- Helper for Theorem 15.23: algebraic-core regularity on
`effectiveDomain G - M '' effectiveDomain F` upgrades to the product-space strong-relative-interior
regularity needed for the graph reduction. -/
lemma productGraphZeroMemSRI_of_zeroMemCoreSubImage
    {X : Type*} {Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (F : X → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(X))
    (G : Y → Set.Ioi (⊥ : EReal)) (hG : G ∈ Γ₀(Y))
    (M : X →L[ℝ] Y)
    (hcore : (0 : Y) ∈ Set.core (effectiveDomain G - M '' effectiveDomain F)) :
    (0 : X × Y) ∈ sri (effectiveDomain F ×ˢ effectiveDomain G - linearGraphSet M) := by
  let S : Set Y := effectiveDomain G - M '' effectiveDomain F
  have hS_nonempty : S.Nonempty := by
    -- Core membership at the origin already gives a concrete point of the source difference set.
    rcases Set.mem_core_iff.mp hcore with ⟨hzero, _⟩
    exact ⟨0, hzero⟩
  have hS_convex : Convex ℝ S := by
    -- The source difference set is convex because both effective domains are convex.
    dsimp [S]
    exact
      hG.2.convex_effectiveDomain.sub
        (hF.2.convex_effectiveDomain.linear_image M.toLinearMap)
  have hsri : (0 : Y) ∈ sri S := by
    -- Convert the textbook core hypothesis to the Chapter 6 strong-relative-interior owner.
    exact zero_mem_sri_of_zero_mem_core_of_nonempty_convex hS_nonempty hS_convex hcore
  -- Translate the source regularity statement to the product-space graph model.
  simpa [S, linearGraphSet] using
    zero_mem_sri_prod_sub_graph_of_zero_mem_sri_sub_image_effectiveDomain
      (f := F) (hf := hF) (g := G) (hg := hG) (L := M) hsri

/-- Helper for Theorem 15.23: once one value of an extended-real objective matches a common lower
bound, that point is a global minimizer. -/
lemma mem_argmin_of_valueEq_and_weakDuality
    {X : Type*} (h : X → EReal) {w : X} {a : EReal}
    (hw : h w = a)
    (hlb : ∀ v : X, a ≤ h v) :
    w ∈ Argmin h := by
  rw [mem_argmin_iff_eq_sInf]
  refine le_antisymm ?_ ?_
  · -- The common lower bound is below the infimum of the whole range.
    have ha_le : a ≤ sInf (Set.range h) :=
      (isGLB_sInf (Set.range h)).2 <| by
        intro z hz
        rcases hz with ⟨v, rfl⟩
        exact hlb v
    simpa [hw] using ha_le
  · -- Every point of the range dominates its infimum, in particular the chosen witness.
    exact (isGLB_sInf (Set.range h)).1 (Set.mem_range_self w)

/-- Helper for Theorem 15.23: once the product-graph dual equality is known on the canonical
orthogonal slice `(M† w, -w)`, the source dual variable `w` is already a minimizer of the
composite dual owner. -/
lemma composite_argmin_of_product_graph_valueEq
    {X : Type*} {Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (F : X → Set.Ioi (⊥ : EReal))
    (G : Y → Set.Ioi (⊥ : EReal))
    (M : X →L[ℝ] Y)
    {w : Y}
    (hw :
      primalOptimalValue
          ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
          (ι[linearGraphSet M]) =
        -(fenchelDualObjective
            ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
            (ι[linearGraphSet M])
            (M.adjoint w, -w))) :
    w ∈ Argmin (compositeDualObjective F G M) ∧
      compositePrimalOptimalValue F G M = -(compositeDualObjective F G M w) := by
  let P : X × Y → Set.Ioi (⊥ : EReal) := (fun p : X × Y ↦ F p.1) + fun p ↦ G p.2
  let I : X × Y → Set.Ioi (⊥ : EReal) := ι[linearGraphSet M]
  let D : Y → EReal := compositeDualObjective F G M
  have hwValue :
      compositePrimalOptimalValue F G M = -(D w) := by
    -- Rewrite the product owner value and the canonical orthogonal-slice dual value into the
    -- composite owners.
    calc
      compositePrimalOptimalValue F G M = primalOptimalValue P I := by
        simpa [P, I] using
          (product_primalOptimalValue_eq_compositePrimalOptimalValue F G M).symm
      _ = -(fenchelDualObjective P I (M.adjoint w, -w)) := by
            simpa [P, I] using hw
      _ = -(D w) := by
            rw [fenchelDualObjective_product_graph_eq_compositeDualObjective_on_adjoint_neg
              (φ := F) (ψ := G) (M := M) (v := w)]
  have hwArg : w ∈ Argmin (compositeDualObjective F G M) := by
    -- The attained value saturates the weak-duality lower bound, so it is the global minimum.
    refine
      mem_argmin_of_valueEq_and_weakDuality
        (h := D)
        (w := w)
        (a := D w)
        rfl
        ?_
    intro v
    have hweak := compositePrimalOptimalValue_ge_neg_compositeDualObjective F G M v
    rw [hwValue] at hweak
    exact EReal.neg_le_neg_iff.mp hweak
  exact ⟨by simpa [D] using hwArg, by simpa [D] using hwValue⟩

/-- Helper for Theorem 15 23: any product-graph dual point with finite value already lies in the
orthogonal complement of `graph(M)`. This isolates the graph-side transport from the missing
owner-level attainment theorem. -/
lemma mem_orthogonal_graph_of_product_graph_dual_ne_top
    {X : Type*} {Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (F : X → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(X))
    (G : Y → Set.Ioi (⊥ : EReal)) (hG : G ∈ Γ₀(Y))
    (M : X →L[ℝ] Y)
    {u : X × Y}
    (huTop :
      fenchelDualObjective
          ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
          (ι[linearGraphSet M])
          u ≠ ⊤) :
    u ∈ ((((M.toLinearMap.graph : Submodule ℝ (X × Y))ᗮ :
      Submodule ℝ (X × Y)) : Set (X × Y))) := by
  -- Off the orthogonal slice the graph-indicator dual term is definitionally `⊤`, so any
  -- non-`⊤` point must already lie on `graph(M)ᗮ`.
  by_contra hu_not
  exact huTop <|
    fenchelDualObjective_separable_graph_eq_top_off_orthogonal
      (φ := F) (hφ := hF) (ψ := G) (hψ := hG) (M := M) hu_not

/-- Helper for Theorem 15 23: once the raw product-graph dual has an attained minimizer, the only
remaining graph-specific obstruction is whether that minimizer lies off `graph(M)ᗮ`. Off the
orthogonal slice the dual value is `⊤`, and an attained minimum at `⊤` forces the degenerate
everywhere-`⊤` branch. -/
lemma product_graph_dual_all_top_or_mem_orthogonal_of_mem_argmin
    {X : Type*} {Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (F : X → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(X))
    (G : Y → Set.Ioi (⊥ : EReal)) (hG : G ∈ Γ₀(Y))
    (M : X →L[ℝ] Y)
    {u : X × Y}
    (huArg :
      u ∈ Argmin
        (fenchelDualObjective
          ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
          (ι[linearGraphSet M])))
    (huValue :
      primalOptimalValue
          ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
          (ι[linearGraphSet M]) =
        -(fenchelDualObjective
            ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
            (ι[linearGraphSet M])
            u)) :
    ((∀ z : X × Y,
        fenchelDualObjective
            ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
            (ι[linearGraphSet M])
            z = ⊤) ∧
      primalOptimalValue
          ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
          (ι[linearGraphSet M]) = ⊥) ∨
      u ∈ ((((M.toLinearMap.graph : Submodule ℝ (X × Y))ᗮ :
        Submodule ℝ (X × Y)) : Set (X × Y))) := by
  let I : X × Y → Set.Ioi (⊥ : EReal) := ι[linearGraphSet M]
  let D : X × Y → EReal := fenchelDualObjective ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2) I
  by_cases huOrth :
      u ∈ ((((M.toLinearMap.graph : Submodule ℝ (X × Y))ᗮ :
        Submodule ℝ (X × Y)) : Set (X × Y)))
  · -- On the orthogonal slice, the attained minimizer is already in the canonical graph subspace.
    exact Or.inr huOrth
  · have huTop :
        D u = ⊤ := by
      simpa [D, I] using
        fenchelDualObjective_separable_graph_eq_top_off_orthogonal
          (φ := F) (hφ := hF) (ψ := G) (hψ := hG) (M := M) huOrth
    have hu_sInf :
        D u = sInf (Set.range D) := by
      simpa [D, I] using (mem_argmin_iff_eq_sInf.mp huArg)
    have hsInf_top :
        sInf (Set.range D) = ⊤ := by
      -- The minimizing value is `⊤`, so the infimum of the whole range is also `⊤`.
      calc
        sInf (Set.range D) = D u := hu_sInf.symm
        _ = ⊤ := huTop
    have hall :
        ∀ z : X × Y, D z = ⊤ := by
      intro z
      have hz_ge :
          sInf (Set.range D) ≤ D z :=
        (isGLB_sInf (Set.range D)).1 (Set.mem_range_self z)
      -- Since `⊤` is already the infimum, every value of the dual objective must equal `⊤`.
      exact le_antisymm le_top <| by simpa [hsInf_top] using hz_ge
    have hprimal_bot :
        primalOptimalValue
            ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
            (ι[linearGraphSet M]) = ⊥ := by
      -- Rewriting the attained equality at a `⊤` minimizer produces the exceptional primal value.
      calc
        primalOptimalValue
            ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
            (ι[linearGraphSet M]) =
          -(D u) := by simpa [D, I] using huValue
        _ = ⊥ := by simp [huTop]
    exact Or.inl ⟨by simpa [D, I] using hall, hprimal_bot⟩

/-- Helper for Theorem 15 23: once the missing same-space Fenchel-attainment theorem supplies the
raw product-graph disjunction, the remaining graph-specific work is only to convert the attained
branch into an orthogonal witness. The previous lemma records exactly that adapter step. -/
lemma orthogonal_or_all_top_of_product_graph_dual_attainment
    {X : Type*} {Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (F : X → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(X))
    (G : Y → Set.Ioi (⊥ : EReal)) (hG : G ∈ Γ₀(Y))
    (M : X →L[ℝ] Y)
    (hattain :
      ((∀ u : X × Y,
          fenchelDualObjective
              ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
              (ι[linearGraphSet M])
              u = ⊤) ∧
        primalOptimalValue
            ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
            (ι[linearGraphSet M]) = ⊥) ∨
        ∃ u : X × Y,
          u ∈ Argmin
            (fenchelDualObjective
              ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
              (ι[linearGraphSet M])) ∧
          primalOptimalValue
              ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
              (ι[linearGraphSet M]) =
            -(fenchelDualObjective
                ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
                (ι[linearGraphSet M])
                u)) :
    ((∀ u : X × Y,
        fenchelDualObjective
            ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
            (ι[linearGraphSet M])
            u = ⊤) ∧
      primalOptimalValue
          ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
          (ι[linearGraphSet M]) = ⊥) ∨
      ∃ u : X × Y,
        primalOptimalValue
            ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
            (ι[linearGraphSet M]) =
          -(fenchelDualObjective
              ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
              (ι[linearGraphSet M])
              u) ∧
        u ∈ ((((M.toLinearMap.graph : Submodule ℝ (X × Y))ᗮ :
          Submodule ℝ (X × Y)) : Set (X × Y))) := by
  rcases hattain with htop | ⟨u, huArg, huValue⟩
  · -- The degenerate branch is already in the target shape.
    exact Or.inl htop
  · -- Otherwise the graph adapter either recovers the same degenerate branch or localizes the
    -- minimizer on `graph(M)ᗮ`.
    rcases
        product_graph_dual_all_top_or_mem_orthogonal_of_mem_argmin
          (F := F) (hF := hF) (G := G) (hG := hG) (M := M)
          huArg huValue
      with htop | huOrth
    · exact Or.inl htop
    · exact Or.inr ⟨u, huValue, huOrth⟩

/-- Helper for Theorem 15.23: once the product-graph Fenchel dual problem has an attained finite
minimum, the existing orthogonal-graph transport converts that minimizer into an attained
composite dual minimum. This isolates the already-verified graph-to-composite bridge from the
still-missing product-space attainment input. -/
theorem exists_mem_argmin_compositeDualObjective_of_product_graph_dual_argmin
    {X : Type*} {Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (F : X → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(X))
    (G : Y → Set.Ioi (⊥ : EReal)) (hG : G ∈ Γ₀(Y))
    (M : X →L[ℝ] Y)
    {u : X × Y}
    (huArg :
      u ∈ Argmin
        (fenchelDualObjective
          ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
          (ι[linearGraphSet M])))
    (huTop :
      fenchelDualObjective
          ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
          (ι[linearGraphSet M])
          u ≠ ⊤)
    (huValue :
      primalOptimalValue
          ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
          (ι[linearGraphSet M]) =
        -(fenchelDualObjective
            ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
            (ι[linearGraphSet M])
            u)) :
    ∃ w ∈ Argmin (compositeDualObjective F G M),
      compositePrimalOptimalValue F G M = -(compositeDualObjective F G M w) := by
  have huOrth :
      u ∈ ((((M.toLinearMap.graph : Submodule ℝ (X × Y))ᗮ :
        Submodule ℝ (X × Y)) : Set (X × Y))) :=
    mem_orthogonal_graph_of_product_graph_dual_ne_top
      (F := F) (hF := hF) (G := G) (hG := hG) (M := M) huTop
  rcases orthogonal_graph_point_eq_pair_adjoint_neg (M := M) huOrth with ⟨w, rfl⟩
  -- Rewrite the attained product-graph equality through the canonical orthogonal slice and then
  -- invoke the already-proved graph-to-composite minimizer transport.
  rcases
      composite_argmin_of_product_graph_valueEq
        (F := F) (G := G) (M := M) (w := w) (by simpa using huValue)
    with ⟨hwArg, hwValue⟩
  exact ⟨w, hwArg, hwValue⟩

/-- Helper for Theorem 15.23: evaluating the conjugate of the separable-sum-plus-graph owner at
the origin rewrites it as the negative product-graph primal optimal value. This isolates the
`-μ` side of the zero-slice exactness step from the later attainment argument. -/
lemma product_graph_sum_conjugate_zero_eq_neg_primalOptimalValue
    {X : Type*} {Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (F : X → Set.Ioi (⊥ : EReal))
    (G : Y → Set.Ioi (⊥ : EReal))
    (M : X →L[ℝ] Y) :
    ((((fun p : X × Y ↦ F p.1) + fun p : X × Y ↦ G p.2) + ι[linearGraphSet M]).asEReal∗)
        (0 : X × Y) =
      -primalOptimalValue
          ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
          (ι[linearGraphSet M]) := by
  -- At the origin, Fenchel conjugation is the negative indexed infimum, which is exactly the
  -- primal optimal value of the separable sum plus the graph indicator.
  rw [conjugate_zero_eq_neg_iInf]
  simp [primalOptimalValue_eq_iInf_primalObjective]

/-- Helper for Theorem 15.23: the zero slice of `φ^* □ ψ^*` is the infimum of the Fenchel dual
objective `u ↦ φ^*(-u) + ψ^*(u)`. This freezes the sign convention once before extracting an
`Argmin` witness from an exact zero-slice decomposition. -/
lemma sInf_range_fenchelDualObjective_eq_infimalConvolution_conjugates_zero
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (φ ψ : E → Set.Ioi (⊥ : EReal)) :
    sInf (Set.range (fenchelDualObjective φ ψ)) =
      (φ.asEReal∗ □ ψ.asEReal∗) (0 : E) := by
  -- Rewrite the range infimum as an indexed infimum of the dual objective.
  rw [sInf_range, infimalConvolution_apply]
  calc
    (⨅ u : E, fenchelDualObjective φ ψ u) =
        ⨅ y : E, φ.asEReal∗ y + ψ.asEReal∗ (-y) := by
          -- Reindex the dual variable by the involution `u = -y`.
          exact (Equiv.neg E).iInf_congr fun y ↦ by
            simp [fenchelDualObjective_apply, add_comm]
    _ = ⨅ y : E, φ.asEReal∗ y + ψ.asEReal∗ (0 - y) := by
          -- Normalize the infimal-convolution slice at the origin.
          refine iInf_congr fun y ↦ ?_
          simp

/-- Helper for Theorem 15.23: an exact zero slice of `φ^* □ ψ^*` already gives a minimizing
Fenchel dual vector after the sign normalization `u = -y`. -/
lemma argmin_fenchelDualObjective_of_exactAt_zero
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (φ : E → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(E))
    (ψ : E → Set.Ioi (⊥ : EReal)) (hψ : ψ ∈ Γ₀(E))
    (hexact0 :
      infimalConvolution.ExactAt
        (gammaZeroConjugate φ hφ)
        (gammaZeroConjugate ψ hψ)
        (0 : E)) :
    ∃ u ∈ Argmin (fenchelDualObjective φ ψ),
      (φ.asEReal∗ □ ψ.asEReal∗) (0 : E) = fenchelDualObjective φ ψ u := by
  rcases hexact0 with ⟨y, hy⟩
  refine ⟨-y, ?_, ?_⟩
  · -- The exact zero-slice equality identifies `u = -y` with the infimum of the dual range.
    rw [mem_argmin_iff_eq_sInf]
    calc
      fenchelDualObjective φ ψ (-y) = (φ.asEReal∗ □ ψ.asEReal∗) (0 : E) := by
        simpa [fenchelDualObjective_apply, gammaZeroConjugate_apply] using hy.symm
      _ = sInf (Set.range (fenchelDualObjective φ ψ)) := by
        symm
        exact
          sInf_range_fenchelDualObjective_eq_infimalConvolution_conjugates_zero
            (φ := φ) (ψ := ψ)
  · -- Reuse the same sign-normalized zero-slice equality for the downstream value identity.
    simpa [fenchelDualObjective_apply, gammaZeroConjugate_apply] using hy

/-- Helper for Theorem 15 23: weak duality already bounds the same-space primal optimal value from
below by any fixed Fenchel dual value. This is the owner-form lower bound needed when the
product-pair same-space theorem is finally supplied. -/
lemma primalOptimalValue_ge_neg_fenchelDualObjective
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (φ ψ : E → Set.Ioi (⊥ : EReal))
    (u : E) :
    primalOptimalValue φ ψ ≥ -(fenchelDualObjective φ ψ u) := by
  rw [primalOptimalValue_eq_iInf_primalObjective]
  -- Infimize the pointwise weak-duality inequality over the primal variable.
  refine le_iInf fun x ↦ ?_
  simpa using primalObjective_ge_neg_dualObjective φ ψ x u

/-- Helper for Theorem 15 23: the effective domain of the separable product objective is exactly
the product of the coordinatewise effective domains. -/
lemma effectiveDomain_separable_sum_eq_prod
    {X : Type*} {Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (F : X → Set.Ioi (⊥ : EReal))
    (G : Y → Set.Ioi (⊥ : EReal)) :
    effectiveDomain (((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)) =
      effectiveDomain F ×ˢ effectiveDomain G := by
  ext p
  rw [mem_effectiveDomain_pointwiseAdd_iff]
  constructor
  · -- Finite product-space value means finiteness on each coordinate term.
    intro hp
    constructor
    · simpa [mem_effectiveDomain_iff] using hp.1
    · simpa [mem_effectiveDomain_iff] using hp.2
  · -- Coordinatewise finiteness reconstructs finiteness of the separable sum.
    rintro ⟨hpF, hpG⟩
    constructor
    · simpa [mem_effectiveDomain_iff] using hpF
    · simpa [mem_effectiveDomain_iff] using hpG

/-- Helper for Theorem 15 23: the effective domain of the graph indicator is exactly the linear
graph set. -/
lemma effectiveDomain_graphIndicator_eq_linearGraphSet
    {X : Type*} {Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (M : X →L[ℝ] Y) :
    effectiveDomain (ι[linearGraphSet M]) = linearGraphSet M := by
  -- The indicator-domain identity specializes directly to the graph set.
  simpa using effectiveDomain_indicator (linearGraphSet M)

/-- Helper for Theorem 15 23: after normalizing the product pair to the separable objective and
the graph indicator, the source core hypothesis is already in the same-space owner form
`0 ∈ sri (effectiveDomain P - effectiveDomain I)`. -/
lemma zero_mem_sri_sub_effectiveDomain_product_pair
    {X : Type*} {Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (F : X → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(X))
    (G : Y → Set.Ioi (⊥ : EReal)) (hG : G ∈ Γ₀(Y))
    (M : X →L[ℝ] Y)
    (hcore : (0 : Y) ∈ Set.core (effectiveDomain G - M '' effectiveDomain F)) :
    (0 : X × Y) ∈
      sri
        (effectiveDomain (((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)) -
          effectiveDomain (ι[linearGraphSet M])) := by
  have hsri_prod :
      (0 : X × Y) ∈ sri (effectiveDomain F ×ˢ effectiveDomain G - linearGraphSet M) := by
    -- First transport the source core hypothesis to the product-space graph model.
    exact
      productGraphZeroMemSRI_of_zeroMemCoreSubImage
        (F := F) (hF := hF) (G := G) (hG := hG) (M := M) hcore
  -- Then rewrite both effective domains into the normalized same-space owner pair `(P, I)`.
  simpa [effectiveDomain_separable_sum_eq_prod, effectiveDomain_graphIndicator_eq_linearGraphSet]
    using hsri_prod

namespace Theorem_15_23_Local

/-- Helper for Theorem 15 23: once the product pair has been normalized to the same-space Fenchel
owners `P := ((x, y) ↦ F x + G y)` and `I := ι[graph M]`, the only remaining missing input is the
same-space attainment theorem under `0 ∈ sri (effectiveDomain P - effectiveDomain I)`. Everything
else in the product-graph reduction is now verified locally in this file. -/
theorem product_graph_dual_all_top_or_orthogonal_value_of_zero_mem_core_sub_image_effectiveDomain
    {X : Type*} {Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (F : X → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(X))
    (G : Y → Set.Ioi (⊥ : EReal)) (hG : G ∈ Γ₀(Y))
    (M : X →L[ℝ] Y)
    (hcore : (0 : Y) ∈ Set.core (effectiveDomain G - M '' effectiveDomain F)) :
    ((∀ u : X × Y,
        fenchelDualObjective
            ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
            (ι[linearGraphSet M])
            u = ⊤) ∧
      primalOptimalValue
          ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
          (ι[linearGraphSet M]) = ⊥) ∨
      ∃ u : X × Y,
        primalOptimalValue
            ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
            (ι[linearGraphSet M]) =
          -(fenchelDualObjective
              ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
              (ι[linearGraphSet M])
              u) ∧
        u ∈ ((((M.toLinearMap.graph : Submodule ℝ (X × Y))ᗮ :
          Submodule ℝ (X × Y)) : Set (X × Y))) := by
  let P : X × Y → Set.Ioi (⊥ : EReal) := (fun p : X × Y ↦ F p.1) + fun p ↦ G p.2
  let I : X × Y → Set.Ioi (⊥ : EReal) := ι[linearGraphSet M]
  have hP_gamma : P ∈ Γ₀(X × Y) := by
    -- First normalize the separable product objective into the canonical `Γ₀` owner.
    simpa [P] using separable_sum_mem_gammaZero (f := F) (hf := hF) (g := G) (hg := hG)
  have hI_gamma : I ∈ Γ₀(X × Y) := by
    -- The graph indicator is the canonical `Γ₀` constraint term on the product space.
    simpa [I] using graphIndicator_mem_gammaZero (LAB := M)
  have hsri_owner :
      (0 : X × Y) ∈ sri (effectiveDomain P - effectiveDomain I) := by
    -- The source core hypothesis has now been rewritten into the same-space owner hypothesis.
    simpa [P, I] using
      zero_mem_sri_sub_effectiveDomain_product_pair
        (F := F) (hF := hF) (G := G) (hG := hG) (M := M) hcore
  have hattain_owner :
      ((∀ u : X × Y, fenchelDualObjective P I u = ⊤) ∧ primalOptimalValue P I = ⊥) ∨
        ∃ u ∈ Argmin (fenchelDualObjective P I),
          primalOptimalValue P I = -(fenchelDualObjective P I u) := by
    -- Route correction: once the product pair is normalized to `(P, I)`, the remaining witness
    -- is exactly the shared same-space Fenchel owner. Package it into the older disjunctive
    -- interface expected by the downstream graph-to-orthogonal adapter.
    right
    simpa [P, I] using
      exists_mem_argmin_fenchelDualObjective_eq_neg_primalOptimalValue_of_zero_mem_sri_sub_effectiveDomain_shared
        P I hP_gamma hI_gamma hsri_owner
  -- Once the same-space owner is supplied, the graph-side orthogonal localization is immediate.
  simpa [P, I] using
    orthogonal_or_all_top_of_product_graph_dual_attainment
      (F := F) (hF := hF) (G := G) (hG := hG) (M := M) hattain_owner

end Theorem_15_23_Local

/-- Helper for Theorem 15.23: under the product-graph core hypothesis, the zero slice of the
same-space Fenchel dual problem for the pair `((x, y) ↦ F x + G y, ι[graph M])` either degenerates
to the everywhere-`⊤` branch or yields an attained orthogonal-graph witness. -/
lemma exact_at_zero_for_separable_sum_plus_graphIndicator_or_all_top
    {X : Type*} {Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (F : X → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(X))
    (G : Y → Set.Ioi (⊥ : EReal)) (hG : G ∈ Γ₀(Y))
    (M : X →L[ℝ] Y)
    (hcore : (0 : Y) ∈ Set.core (effectiveDomain G - M '' effectiveDomain F)) :
    ((∀ u : X × Y,
        fenchelDualObjective
            ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
            (ι[linearGraphSet M])
            u = ⊤) ∧
      primalOptimalValue
          ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
          (ι[linearGraphSet M]) = ⊥) ∨
      ∃ u : X × Y,
        primalOptimalValue
            ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
            (ι[linearGraphSet M]) =
          -(fenchelDualObjective
              ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
              (ι[linearGraphSet M])
              u) ∧
        u ∈ ((((M.toLinearMap.graph : Submodule ℝ (X × Y))ᗮ :
          Submodule ℝ (X × Y)) : Set (X × Y))) := by
  -- Route correction: the source-facing product-graph exactness step now lives in the
  -- theorem-local helper layer, so this main-file lemma is only the downstream interface adapter.
  -- The remaining structural blocker is now isolated to the upstream edge
  -- `Proposition_15_13 -> Theorem_15_23`; the redundant direct edge
  -- `Theorem_15_3 -> Theorem_15_23` has been removed.
  simpa using
    Theorem_15_23_Local.product_graph_dual_all_top_or_orthogonal_value_of_zero_mem_core_sub_image_effectiveDomain
      (F := F) (hF := hF) (G := G) (hG := hG) (M := M) hcore

/-- Helper for Theorem 15.23: under the product-graph core hypothesis, the missing product-space
duality step reduces either to the degenerate case where the raw dual objective is identically
`⊤`, or to an equality witness on the canonical orthogonal slice `(M† w, -w)`. -/
lemma product_graph_dual_all_top_or_canonical_slice_value
    {X : Type*} {Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (F : X → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(X))
    (G : Y → Set.Ioi (⊥ : EReal)) (hG : G ∈ Γ₀(Y))
    (M : X →L[ℝ] Y)
    (hcore : (0 : Y) ∈ Set.core (effectiveDomain G - M '' effectiveDomain F)) :
    ((∀ u : X × Y,
        fenchelDualObjective
            ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
            (ι[linearGraphSet M])
            u = ⊤) ∧
      primalOptimalValue
          ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
          (ι[linearGraphSet M]) = ⊥) ∨
      ∃ w : Y,
        primalOptimalValue
            ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
            (ι[linearGraphSet M]) =
          -(fenchelDualObjective
              ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
              (ι[linearGraphSet M])
              (M.adjoint w, -w)) := by
  -- Route correction: the hard same-space exactness step now lives in the previous lemma, while
  -- this theorem only converts an orthogonal-graph witness to the canonical slice `(M† w, -w)`.
  rcases
      exact_at_zero_for_separable_sum_plus_graphIndicator_or_all_top
        (F := F) (hF := hF) (G := G) (hG := hG) (M := M) hcore
    with htop | hwitness
  · exact Or.inl htop
  · rcases hwitness with ⟨u, huValue, huOrth⟩
    rcases orthogonal_graph_point_eq_pair_adjoint_neg (M := M) huOrth with ⟨w, rfl⟩
    -- The only remaining work is to rewrite the orthogonal witness through its canonical
    -- parameterization by a dual vector `w`.
    exact Or.inr ⟨w, huValue⟩

/-- Helper for Theorem 15.23: if the raw product-graph dual objective is identically `⊤`, then
the owner composite dual objective is also identically `⊤`. -/
lemma compositeDualObjective_eq_top_of_product_graph_dual_all_top
    {X : Type*} {Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (F : X → Set.Ioi (⊥ : EReal))
    (G : Y → Set.Ioi (⊥ : EReal))
    (M : X →L[ℝ] Y)
    (hall :
      ∀ u : X × Y,
        fenchelDualObjective
            ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
            (ι[linearGraphSet M])
            u = ⊤) :
    ∀ w : Y, compositeDualObjective F G M w = ⊤ := by
  intro w
  -- Evaluate the raw dual objective on the canonical orthogonal slice `(M† w, -w)`.
  rw [← fenchelDualObjective_product_graph_eq_compositeDualObjective_on_adjoint_neg]
  exact hall (M.adjoint w, -w)

/-- Helper for Theorem 15.23: if the owner composite dual objective is everywhere `⊤`, then the
origin is an `Argmin` witness. -/
lemma zero_mem_argmin_of_compositeDualObjective_eq_top
    {X : Type*} {Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (F : X → Set.Ioi (⊥ : EReal))
    (G : Y → Set.Ioi (⊥ : EReal))
    (M : X →L[ℝ] Y)
    (hall : ∀ w : Y, compositeDualObjective F G M w = ⊤) :
    (0 : Y) ∈ Argmin (compositeDualObjective F G M) := by
  have hrange :
      Set.range (compositeDualObjective F G M) = ({⊤} : Set EReal) := by
    ext a
    constructor
    · rintro ⟨w, rfl⟩
      exact hall w
    · intro ha
      rw [Set.mem_singleton_iff] at ha
      refine ⟨0, ?_⟩
      simpa [ha] using (hall 0)
  -- The range is the singleton `{⊤}`, so the value at the origin matches the infimum.
  rw [mem_argmin_iff_eq_sInf, hall 0, hrange]
  simp

end ProductGraphL2

/-- Helper for Theorem 15 23: the textbook closed-span/core route needs exactly the canonical
Attouch--Brezis attainment theorem on `effectiveDomain G - M '' effectiveDomain F`. This is the
shared owner theorem that Proposition 15.22 should expose without routing back through Theorem
15.23. -/
theorem exists_mem_argmin_compositeDualObjective_of_zero_mem_core_sub_image_effectiveDomain_shared
    {X : Type*} {Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (F : X → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(X))
    (G : Y → Set.Ioi (⊥ : EReal)) (hG : G ∈ Γ₀(Y))
    (M : X →L[ℝ] Y)
    (hcore : (0 : Y) ∈ Set.core (effectiveDomain G - M '' effectiveDomain F)) :
    ∃ w ∈ Argmin (compositeDualObjective F G M),
      compositePrimalOptimalValue F G M = -(compositeDualObjective F G M w) := by
  -- Route correction: branch before transporting to the composite owner, because the raw
  -- product dual can be identically `⊤`.
  rcases
      product_graph_dual_all_top_or_canonical_slice_value
        (F := F) (hF := hF) (G := G) (hG := hG) (M := M) hcore
    with htop | hvalue
  · rcases htop with ⟨hall, hprimal_bot⟩
    have hdual_top : ∀ w : Y, compositeDualObjective F G M w = ⊤ :=
      compositeDualObjective_eq_top_of_product_graph_dual_all_top
        (F := F) (G := G) (M := M) hall
    have hzero_arg :
        (0 : Y) ∈ Argmin (compositeDualObjective F G M) :=
      zero_mem_argmin_of_compositeDualObjective_eq_top
        (F := F) (G := G) (M := M) hdual_top
    refine ⟨0, hzero_arg, ?_⟩
    -- In the degenerate branch, both owners take their exceptional values `⊥` and `⊤`.
    calc
      compositePrimalOptimalValue F G M =
          primalOptimalValue
            ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
            (ι[linearGraphSet M]) := by
              symm
              exact product_primalOptimalValue_eq_compositePrimalOptimalValue F G M
      _ = ⊥ := hprimal_bot
      _ = -(compositeDualObjective F G M 0) := by
            rw [hdual_top 0]
            simp
  · rcases hvalue with ⟨w, hw⟩
    rcases composite_argmin_of_product_graph_valueEq
        (F := F) (G := G) (M := M) (w := w) hw with ⟨hwArg, hwValue⟩
    exact ⟨w, hwArg, hwValue⟩

/-- Helper for Theorem 15 23: core regularity on `effectiveDomain G - M '' effectiveDomain F`
forces attainment of the composite dual owner. This isolates the single abstract Fenchel--Rockafellar
step that the closed-span specialization needs. -/
theorem exists_mem_argmin_compositeDualObjective_of_zero_mem_core_sub_image_effectiveDomain_support
    {X : Type*} {Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (F : X → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(X))
    (G : Y → Set.Ioi (⊥ : EReal)) (hG : G ∈ Γ₀(Y))
    (M : X →L[ℝ] Y)
    (hcore : (0 : Y) ∈ Set.core (effectiveDomain G - M '' effectiveDomain F)) :
    ∃ w ∈ Argmin (compositeDualObjective F G M),
      compositePrimalOptimalValue F G M = -(compositeDualObjective F G M w) := by
  -- The local theorem keeps the same API, but the proof route now goes directly through the
  -- canonical Proposition 15.22-content owner instead of the dead graph-model detour.
  exact
    exists_mem_argmin_compositeDualObjective_of_zero_mem_core_sub_image_effectiveDomain_shared
      (F := F) (hF := hF) (G := G) (hG := hG) (M := M) hcore

/-- Helper for Theorem 15 23: the restricted zero-domain problem on the closed spans `A` and `B`
has an attained dual minimum. This is the file-local replacement for the textbook invocation of
Proposition 15.22 after establishing line `(15.36)`. -/
theorem exists_mem_argmin_restricted_compositeDualObjective_of_zero_mem_core_difference
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (g : K → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K)
    (hsri : (0 : K) ∈ sri (effectiveDomain g - L '' effectiveDomain f))
    (hzero_f : (0 : H) ∈ effectiveDomain f)
    (hzero_g : (0 : K) ∈ effectiveDomain g) :
    ∃ vB ∈ Argmin (restrictedCompositeDualObjective f g L),
      restrictedCompositePrimalOptimalValue f g L =
        -(restrictedCompositeDualObjective f g L vB) := by
  letI : CompleteSpace ↥(effectiveDomainClosedSpan f) :=
    effectiveDomainClosedSpan_completeSpace f
  letI : CompleteSpace ↥(subImageDifferenceClosedSpan f g L) :=
    subImageDifferenceClosedSpan_completeSpace f g L
  have hfA : restrictToEffectiveDomainClosedSpan f ∈ Γ₀(effectiveDomainClosedSpan f) := by
    -- Restrict `f` to the closed span `A`; properness is witnessed by the ambient origin.
    simpa [effectiveDomainClosedSpan, restrictToEffectiveDomainClosedSpan] using
      restrict_mem_gammaZero_of_zero_mem_effectiveDomain
        (F := f) (hF := hf) hzero_f (effectiveDomainClosedSpan f)
  have hgB :
      restrictToSubImageDifferenceClosedSpan f g L ∈
        Γ₀(subImageDifferenceClosedSpan f g L) := by
    -- Restrict `g` to the closed span `B`; properness is again witnessed by the ambient origin.
    simpa [subImageDifferenceClosedSpan, restrictToSubImageDifferenceClosedSpan] using
      restrict_mem_gammaZero_of_zero_mem_effectiveDomain
        (F := g) (hF := hg) hzero_g (subImageDifferenceClosedSpan f g L)
  have hcore :
      (0 : subImageDifferenceClosedSpan f g L) ∈
        Set.core
          (effectiveDomain (restrictToSubImageDifferenceClosedSpan f g L) -
            restrictedMapOnClosedSpans f g L '' effectiveDomain
              (restrictToEffectiveDomainClosedSpan f)) := by
    -- Reuse the already-established owner-form `core` statement for line `(15.36)`.
    simpa
        [effectiveDomainClosedSpan, subImageDifferenceClosedSpan,
          restrictToEffectiveDomainClosedSpan, restrictToSubImageDifferenceClosedSpan,
          restrictedMapOnClosedSpans] using
      restrictedZeroMemCore_difference_onClosedSpans
        (f := f) (hf := hf) (g := g) (hg := hg) (L := L) hsri hzero_f hzero_g
  -- The closed-span theorem is now a direct specialization of the abstract core-attainment step.
  have hattain :=
    @exists_mem_argmin_compositeDualObjective_of_zero_mem_core_sub_image_effectiveDomain_support
      (effectiveDomainClosedSpan f) (subImageDifferenceClosedSpan f g L)
      inferInstance inferInstance (effectiveDomainClosedSpan_completeSpace f)
      inferInstance inferInstance (subImageDifferenceClosedSpan_completeSpace f g L)
      (restrictToEffectiveDomainClosedSpan f) hfA
      (restrictToSubImageDifferenceClosedSpan f g L) hgB
      (restrictedMapOnClosedSpans f g L) hcore
  simpa
      [effectiveDomainClosedSpan, subImageDifferenceClosedSpan,
        restrictToEffectiveDomainClosedSpan, restrictToSubImageDifferenceClosedSpan,
        restrictedMapOnClosedSpans, restrictedCompositeDualObjective,
        restrictedCompositePrimalOptimalValue] using
    hattain

/-- Helper for Theorem 15 23: a minimizer of the restricted dual owner on the closed span `B`
lifts to a minimizer of the ambient dual owner. -/
lemma mem_argmin_ambient_compositeDualObjective_of_mem_argmin_restricted
    (f : H → Set.Ioi (⊥ : EReal))
    (g : K → Set.Ioi (⊥ : EReal))
    (L : H →L[ℝ] K)
    (hzero_f : (0 : H) ∈ effectiveDomain f)
    (hzero_g : (0 : K) ∈ effectiveDomain g) :
    ∀ {vB : subImageDifferenceClosedSpan f g L},
      vB ∈ Argmin (restrictedCompositeDualObjective f g L) →
      (vB : K) ∈ Argmin (compositeDualObjective f g L) := by
  intro vB hvB
  have hrange :
      Set.range (compositeDualObjective f g L) =
        Set.range (restrictedCompositeDualObjective f g L) := by
    ext a
    constructor
    · rintro ⟨v, rfl⟩
      refine ⟨(subImageDifferenceClosedSpan f g L).orthogonalProjection v, ?_⟩
      simpa
          [restrictToEffectiveDomainClosedSpan, restrictToSubImageDifferenceClosedSpan,
            restrictedMapOnClosedSpans] using
        ambient_compositeDualObjective_eq_restricted_compositeDualObjective_comp_starProjection
          (f := f) (g := g) (L := L) hzero_f hzero_g v |>.symm
    · rintro ⟨w, rfl⟩
      refine ⟨(w : K), ?_⟩
      simpa
          [restrictToEffectiveDomainClosedSpan, restrictToSubImageDifferenceClosedSpan,
            restrictedMapOnClosedSpans] using
        ambient_dual_value_eq_restricted_dual_value_on_subtype_minimizer
          (f := f) (g := g) (L := L) hzero_f hzero_g w
  -- Compare the attained restricted value to the common infimum of the equal ranges.
  rw [mem_argmin_iff_eq_sInf]
  calc
    compositeDualObjective f g L (vB : K) =
        restrictedCompositeDualObjective f g L vB := by
      simpa
          [restrictToEffectiveDomainClosedSpan, restrictToSubImageDifferenceClosedSpan,
            restrictedMapOnClosedSpans] using
        ambient_dual_value_eq_restricted_dual_value_on_subtype_minimizer
          (f := f) (g := g) (L := L) hzero_f hzero_g vB
    _ = sInf (Set.range (restrictedCompositeDualObjective f g L)) := by
          exact mem_argmin_iff_eq_sInf.mp hvB
    _ = sInf (Set.range (compositeDualObjective f g L)) := by rw [← hrange]

/-- Helper for Theorem 15 23: the remaining zero-in-domain special case from the textbook proof.
This is the restriction-to-closed-spans attainment step that the general theorem reduces to after
translation. -/
theorem exists_mem_argmin_compositeDualObjective_of_zero_domains
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (g : K → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K)
    (hsri : (0 : K) ∈ sri (effectiveDomain g - L '' effectiveDomain f))
    (hzero_f : (0 : H) ∈ effectiveDomain f)
    (hzero_g : (0 : K) ∈ effectiveDomain g) :
    ∃ v ∈ Argmin (compositeDualObjective f g L),
      compositePrimalOptimalValue f g L = -(compositeDualObjective f g L v) := by
  have hprimal :
      compositePrimalOptimalValue f g L =
        restrictedCompositePrimalOptimalValue f g L := by
    -- The primal owner already agrees with its restriction to the textbook closed spans.
    simpa
        [effectiveDomainClosedSpan, subImageDifferenceClosedSpan,
          restrictToEffectiveDomainClosedSpan, restrictToSubImageDifferenceClosedSpan,
          restrictedMapOnClosedSpans] using
      ambientCompositePrimalOptimalValue_eq_restrictedOnClosedSpans
        (f := f) (g := g) (L := L) hzero_f hzero_g
  obtain ⟨vB, hvBArg, hvBValue⟩ :=
    exists_mem_argmin_restricted_compositeDualObjective_of_zero_mem_core_difference
      (f := f) (hf := hf) (g := g) (hg := hg) (L := L) hsri hzero_f hzero_g
  have hvArg : (vB : K) ∈ Argmin (compositeDualObjective f g L) := by
    -- Lift the restricted minimizer to the ambient dual problem through the projection rewrite.
    simpa
        [restrictToEffectiveDomainClosedSpan, restrictToSubImageDifferenceClosedSpan,
          restrictedMapOnClosedSpans] using
      mem_argmin_ambient_compositeDualObjective_of_mem_argmin_restricted
        (f := f) (g := g) (L := L) hzero_f hzero_g hvBArg
  refine ⟨(vB : K), hvArg, ?_⟩
  -- Finish by combining the primal restriction identity with the ambient/restricted dual value
  -- equality on the chosen subtype minimizer.
  calc
    compositePrimalOptimalValue f g L =
        restrictedCompositePrimalOptimalValue f g L := hprimal
    _ = -(restrictedCompositeDualObjective f g L vB) := hvBValue
    _ = -(compositeDualObjective f g L (vB : K)) := by
          rw [ambient_dual_value_eq_restricted_dual_value_on_subtype_minimizer
            (f := f) (g := g) (L := L) hzero_f hzero_g vB]

-- Proof sketch: package the composite problem through the owner API from Definition 15.19 and
-- perform the standard product-space reduction behind Fenchel--Rockafellar duality. The
-- strong-relative-interior hypothesis `0 ∈ sri (effectiveDomain g - L '' effectiveDomain f)` is
-- the regularity condition that yields strong duality and attainment for the adjoint-based dual
-- objective `compositeDualObjective f g L`.
set_option linter.style.longLine false in
/-- Theorem 15.23: if `f ∈ Γ₀(H)`, `g ∈ Γ₀(K)`, and
`0 ∈ sri (effectiveDomain g - L '' effectiveDomain f)`, then the composite primal optimal value is
the negative of the minimum of the owner dual objective `compositeDualObjective f g L`, i.e.
of `v ↦ f^*(-L^* v) + g^*(v)`. -/
theorem exists_mem_argmin_compositeDualObjective_eq_neg_compositePrimalOptimalValue_of_zero_mem_sri_sub_image_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (g : K → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K)
    (hsri : (0 : K) ∈ sri (effectiveDomain g - L '' effectiveDomain f)) :
    ∃ v ∈ Argmin (compositeDualObjective f g L),
      compositePrimalOptimalValue f g L = -(compositeDualObjective f g L v) := by
  obtain ⟨a, ha, b, hb, hba⟩ :=
    exists_domain_pair_eq_image_of_zero_mem_sri_sub_image_effectiveDomain
      (f := f) (g := g) (L := L) hsri
  let φ : H → Set.Ioi (⊥ : EReal) := fun x ↦ f (x + a)
  let ψ : K → Set.Ioi (⊥ : EReal) := fun y ↦ g (y + b)
  have htranslate :
      effectiveDomain ψ - L '' effectiveDomain φ = effectiveDomain g - L '' effectiveDomain f ∧
        (0 : H) ∈ effectiveDomain φ ∧
        (0 : K) ∈ effectiveDomain ψ ∧
        ∀ v : K, compositeDualObjective φ ψ L v = compositeDualObjective f g L v := by
    -- This is the textbook reduction from the general case to the zero-in-domain special case.
    simpa [φ, ψ] using
      translated_composite_data_preserves_regular_set
        (f := f) (g := g) (L := L) (a := a) ha (b := b) hb hba
  rcases htranslate with ⟨hregular_translate, hzeroφ, hzeroψ, hdual_translate⟩
  have hφ_gamma : φ ∈ Γ₀(H) := by
    -- Translate the source `Γ₀` datum so the selected witness `a` moves to the origin.
    simpa [φ] using translate_mem_gammaZero (f := f) hf a
  have hψ_gamma : ψ ∈ Γ₀(K) := by
    -- Translate the target `Γ₀` datum so the selected witness `b` moves to the origin.
    simpa [ψ] using translate_mem_gammaZero (f := g) hg b
  have hsri_translate : (0 : K) ∈ sri (effectiveDomain ψ - L '' effectiveDomain φ) := by
    -- The domain-difference set is unchanged by the compensating translations.
    rw [hregular_translate]
    exact hsri
  obtain ⟨v, hvArgTranslated, hvEqTranslated⟩ :=
    exists_mem_argmin_compositeDualObjective_of_zero_domains
      φ hφ_gamma ψ hψ_gamma L hsri_translate hzeroφ hzeroψ
  have hdual_funext : compositeDualObjective φ ψ L = compositeDualObjective f g L := by
    -- Freeze the owner rewrite once so the later `Argmin` transport is ordinary equality.
    simpa [φ, ψ] using
      translated_compositeDualObjective_eq_original_of_image_domain_witness
        (f := f) (g := g) (L := L) (a := a) (b := b) hba
  have hprimal_translate :
      compositePrimalOptimalValue φ ψ L = compositePrimalOptimalValue f g L := by
    -- The primal infimum is invariant under the translation `x ↦ x + a` with `b = L a`.
    simpa [φ, ψ] using
      translated_compositePrimalOptimalValue_eq_original_of_image_domain_witness
        (f := f) (g := g) (L := L) (a := a) (b := b) hba
  have hvArg : v ∈ Argmin (compositeDualObjective f g L) := by
    rw [mem_argmin_iff_eq_sInf]
    calc
      compositeDualObjective f g L v = compositeDualObjective φ ψ L v := by
        exact (hdual_translate v).symm
      _ = sInf (Set.range (compositeDualObjective φ ψ L)) := by
            exact mem_argmin_iff_eq_sInf.mp hvArgTranslated
      _ = sInf (Set.range (compositeDualObjective f g L)) := by
            rw [hdual_funext]
  refine ⟨v, hvArg, ?_⟩
  -- Replace the translated primal and dual owners by the original ones via the frozen rewrites.
  calc
    compositePrimalOptimalValue f g L = compositePrimalOptimalValue φ ψ L := hprimal_translate.symm
    _ = -(compositeDualObjective φ ψ L v) := hvEqTranslated
    _ = -(compositeDualObjective f g L v) := by rw [hdual_funext]

-- Proof sketch: the source-facing theorem above supplies a minimizing dual vector `v`. Since
-- `v ∈ Argmin (compositeDualObjective f g L)`, its dual value is exactly
-- `compositeDualOptimalValue f g L`, so the displayed equality rewrites to the owner optimal-value
-- identity.
/-- Companion reformulation of Theorem 15.23: the attained minimum of
`compositeDualObjective f g L` rewrites to the canonical dual optimal value
`compositeDualOptimalValue f g L`. -/
theorem compositePrimalOptimalValue_eq_neg_compositeDualOptimalValue_of_zero_mem_sri_sub_image_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (g : K → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K)
    (hsri : (0 : K) ∈ sri (effectiveDomain g - L '' effectiveDomain f)) :
    compositePrimalOptimalValue f g L = -compositeDualOptimalValue f g L := by
  obtain ⟨v, hvArg, hvEq⟩ :=
    exists_mem_argmin_compositeDualObjective_eq_neg_compositePrimalOptimalValue_of_zero_mem_sri_sub_image_effectiveDomain
      f hf g hg L hsri
  have hvValue : compositeDualObjective f g L v = compositeDualOptimalValue f g L := by
    -- Membership in `Argmin` rewrites the attained dual value to the canonical optimal value.
    simpa [compositeDualOptimalValue_def] using (mem_argmin_iff_eq_sInf.mp hvArg)
  -- Replace the attained dual value by the owner dual optimal value.
  calc
    compositePrimalOptimalValue f g L = -(compositeDualObjective f g L v) := hvEq
    _ = -compositeDualOptimalValue f g L := by rw [hvValue]

end FenchelRockafellarDuality

end ERealFunction
