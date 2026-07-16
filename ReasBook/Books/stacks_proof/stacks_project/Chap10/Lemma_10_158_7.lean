import stacks_proof.stacks_project.Chap09.Definition_9_26_1
import stacks_proof.stacks_project.Chap10.Definition_10_42_1
import stacks_proof.stacks_project.Chap10.Lemma_10_150_4
import stacks_proof.stacks_project.Chap10.Lemma_10_158_6
import stacks_proof.stacks_project.Chap10.Lemma_10_127_9
import stacks_proof.stacks_project.Chap10.Lemma_10_158_7.DirectLimitSupport

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Algebra

section

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
open scoped IntermediateField TensorProduct

/- Domain-style sampling for Lemma 10.158.7:
- primary domain: field extensions and the formal smoothness / separability interface over a base
  field;
- sampled owner declarations:
  `isPurelyTranscendental_iff_exists_algebraicIndependent`,
  `Algebra.FormallySmooth.of_algebraicIndependent`,
  `Algebra.FormallyEtale.of_isSeparable`,
  `Algebra.IsSeparableOver`;
- best owner abstraction: the canonical owner `Algebra.FormallySmooth k K`, with the source-facing
  chapter predicates `IsPurelyTranscendental` and `IsSeparableOver` treated as bridge inputs;
- primitive data: the field extension `K / k` together with the source-facing hypotheses
  `IsPurelyTranscendental k K`, `[Algebra.IsSeparable k K]`, or `[Algebra.IsSeparableOver k K]`;
- derived API: the formal smoothness conclusion and the low-priority instance exported from the
  source-facing theorem in part `(3)`.

Source/core/bridge triage:
- `source-facing`: the three textbook implications in Lemma 10.158.7;
- `core/canonical`: `Algebra.FormallySmooth k K` and the exact mathlib owners
  `Algebra.FormallySmooth.of_algebraicIndependent` and
  `Algebra.FormallyEtale.of_isSeparable`;
- `bridge/view`: the chapter owners `IsPurelyTranscendental` and `IsSeparableOver`.
-/

/-- Chap10 Lemma 10 158 7 (1): if `K` is purely transcendental over `k`, then `K` is formally
smooth over `k`. -/
@[stacks 0320 "(1)"]
theorem formallySmooth_of_purelyTranscendental
    (hK : IsPurelyTranscendental k K) :
    Algebra.FormallySmooth k K := by
  -- Proof comment: unpack the purely transcendental hypothesis into an algebraically independent
  -- generating family and invoke the owner theorem for such extensions.
  have hiff :
      IsPurelyTranscendental k K ↔
        ∃ (ι : Type v) (x : ι → K),
          AlgebraicIndependent k x ∧ IntermediateField.adjoin k (Set.range x) = ⊤ :=
    isPurelyTranscendental_iff_exists_algebraicIndependent
  rcases hiff.1 hK with
    ⟨s, x, hx, htop⟩
  exact Algebra.FormallySmooth.of_algebraicIndependent hx htop

/-- Chap10 Lemma 10 158 7 (2): if `K / k` is separable algebraic, then `K` is formally smooth
over `k`. -/
@[stacks 0320 "(2)"]
theorem formallySmooth_of_isSeparable [Algebra.IsSeparable k K] :
    Algebra.FormallySmooth k K := by
  -- Proof comment: a separable algebraic field extension is formally étale, hence formally
  -- smooth.
  letI : Algebra.FormallyEtale k K := Algebra.FormallyEtale.of_isSeparable k K
  infer_instance

/-- Helper for Chap10 Lemma 10 158 7: the direct limit of a constant `k`-system is `k` as a
`k`-algebra. -/
noncomputable def constantDirectLimitAlgEquiv
    (ι : Type*) [Preorder ι] [Nonempty ι] [IsDirectedOrder ι] :
    Ring.DirectLimit (fun _ : ι ↦ k) (fun _ _ _ ↦ RingHom.id k) ≃ₐ[k] k := by
  classical
  let R : ι → Type u := fun _ ↦ k
  let ρ : ∀ i j, i ≤ j → R i →ₐ[k] R j := fun _ _ _ ↦ AlgHom.id k k
  letI : DirectedSystem R (fun i j h ↦ (ρ i j h).toRingHom) where
    map_self := by
      intro i x
      rfl
    map_map := by
      intro i j l hij hjl x
      rfl
  letI : Algebra k (Ring.DirectLimit R (fun i j h ↦ (ρ i j h).toRingHom)) :=
    Ring.DirectLimit.instAlgebra (R := k) (S := R) (φ := ρ)
  let toK : Ring.DirectLimit R (fun i j h ↦ (ρ i j h).toRingHom) →ₐ[k] k :=
    Ring.DirectLimit.liftAlgHom R ρ (fun _ ↦ AlgHom.id k k) fun _ _ _ ↦ rfl
  have htoK_inj : Function.Injective toK := by
    -- Proof comment: every stage map into `k` is the identity, so the universal direct-limit
    -- lift is injective by the generic `Ring.DirectLimit.lift_injective` criterion.
    simpa [toK, Ring.DirectLimit.liftAlgHom, ρ] using
      (Ring.DirectLimit.lift_injective
        (G := R)
        (f := fun i j h ↦ (ρ i j h).toRingHom)
        (P := k)
        (g := fun _ ↦ RingHom.id k)
        (Hg := fun _ _ _ _ ↦ rfl)
        (injective := fun _ ↦ Function.injective_id))
  have htoK_surj : Function.Surjective toK := by
    -- Proof comment: every scalar already comes from any chosen constant stage.
    intro x
    let i : ι := Classical.arbitrary ι
    refine ⟨Ring.DirectLimit.ofAlgHom R ρ i x, ?_⟩
    change toK (Ring.DirectLimit.ofAlgHom R ρ i x) = x
    simpa [toK, ρ] using
      DFunLike.congr_fun (Ring.DirectLimit.liftAlgHom_of R ρ (fun _ ↦ AlgHom.id k k)
        (fun _ _ _ ↦ rfl) i) x
  exact AlgEquiv.ofBijective toK ⟨htoK_inj, htoK_surj⟩

/-- Helper for Chap10 Lemma 10 158 7: the directed colimit of the finite-adjoin intermediate
fields is `K` as a `k`-algebra. -/
noncomputable def finiteAdjoinDirectLimitAlgEquiv :
    let S : Finset K → Type v := fun s ↦ ↥(IntermediateField.adjoin k (s : Set K))
    let σ : ∀ s t, s ≤ t → S s →ₐ[k] S t := fun s t h ↦
      IntermediateField.inclusion <|
        IntermediateField.adjoin_le_iff.mpr (show (s : Set K) ⊆ t from h)
    Ring.DirectLimit S (fun s t h ↦ (σ s t h).toRingHom) ≃ₐ[k] K := by
  classical
  let S : Finset K → Type v := fun s ↦ ↥(IntermediateField.adjoin k (s : Set K))
  let σ : ∀ s t, s ≤ t → S s →ₐ[k] S t := fun s t h ↦
    IntermediateField.inclusion <|
      IntermediateField.adjoin_le_iff.mpr (show (s : Set K) ⊆ t from h)
  letI : Nonempty (Finset K) := ⟨∅⟩
  letI : IsDirectedOrder (Finset K) := by
    refine ⟨fun s t ↦ ?_⟩
    exact ⟨s ∪ t, Finset.subset_union_left, Finset.subset_union_right⟩
  letI : DirectedSystem S (fun s t h ↦ (σ s t h).toRingHom) where
    map_self := by
      intro s x
      rfl
    map_map := by
      intro i j l hij hjl x
      rfl
  letI : Algebra k (Ring.DirectLimit S (fun s t h ↦ (σ s t h).toRingHom)) :=
    Ring.DirectLimit.instAlgebra (R := k) (S := S) (φ := σ)
  let toK : Ring.DirectLimit S (fun s t h ↦ (σ s t h).toRingHom) →ₐ[k] K :=
    Ring.DirectLimit.liftAlgHom S σ
      (fun s ↦ IsScalarTower.toAlgHom k (S s) K)
      (fun _ _ _ ↦ by ext x; rfl)
  have htoK_inj : Function.Injective toK := by
    -- Proof comment: the colimit map to `K` is injective because every stage inclusion into `K`
    -- is injective.
    simpa [toK, σ, Ring.DirectLimit.liftAlgHom] using
      (Ring.DirectLimit.lift_injective
        (G := S)
        (f := fun s t h ↦ (σ s t h).toRingHom)
        (P := K)
        (g := fun s ↦ (IsScalarTower.toAlgHom k (S s) K).toRingHom)
        (Hg := fun _ _ _ _ ↦ rfl)
        (injective := fun s ↦ (IsScalarTower.toAlgHom k (S s) K).injective))
  have htoK_surj : Function.Surjective toK := by
    -- Proof comment: an element `x : K` already lies in the finite stage adjoined by `{x}`.
    intro x
    let s : Finset K := {x}
    let xs : S s := ⟨x, by
      simpa [s] using IntermediateField.mem_adjoin_simple_self k x⟩
    refine ⟨Ring.DirectLimit.ofAlgHom S σ s xs, ?_⟩
    change toK (Ring.DirectLimit.ofAlgHom S σ s xs) = x
    simpa [toK, xs, s, σ] using
      DFunLike.congr_fun (Ring.DirectLimit.liftAlgHom_of S σ
        (fun t ↦ IsScalarTower.toAlgHom k (S t) K)
        (fun _ _ _ ↦ by ext y; rfl) s) xs
  exact AlgEquiv.ofBijective toK ⟨htoK_inj, htoK_surj⟩

/-- Chap10 Lemma 10 158 7 (3): if `K / k` is separable in the Stacks Project sense, then `K` is
formally smooth over `k`. -/
@[stacks 0320 "(3)"]
theorem formallySmooth_of_isSeparableOver [IsSeparableOver k K] :
    Algebra.FormallySmooth k K := by
  classical
  let I : Type v := Finset K
  let R : I → Type u := fun _ ↦ k
  let S : I → Type v := fun s ↦ ↥(IntermediateField.adjoin k (s : Set K))
  let ρAlg : ∀ s t, s ≤ t → R s →ₐ[k] R t := fun _ _ _ ↦ AlgHom.id k k
  let σAlg : ∀ s t, s ≤ t → S s →ₐ[k] S t := fun s t h ↦
    IntermediateField.inclusion <|
      IntermediateField.adjoin_le_iff.mpr (show (s : Set K) ⊆ t from h)
  let ρ : ∀ s t, s ≤ t → R s →+* R t := fun s t h ↦ (ρAlg s t h).toRingHom
  let σ : ∀ s t, s ≤ t → S s →+* S t := fun s t h ↦ (σAlg s t h).toRingHom
  letI : Nonempty I := ⟨∅⟩
  letI : IsDirectedOrder I := by
    refine ⟨fun s t ↦ ?_⟩
    exact ⟨s ∪ t, Finset.subset_union_left, Finset.subset_union_right⟩
  letI : DirectedSystem R ρ where
    map_self := by
      intro s x
      rfl
    map_map := by
      intro i j l hij hjl x
      rfl
  letI : DirectedSystem S σ where
    map_self := by
      intro s x
      rfl
    map_map := by
      intro i j l hij hjl x
      rfl
  let R∞ : Type u := Ring.DirectLimit R ρ
  let S∞ : Type v := Ring.DirectLimit S σ
  letI : Algebra k R∞ := Ring.DirectLimit.instAlgebra (R := k) (S := R) (φ := ρAlg)
  letI : Algebra k S∞ := Ring.DirectLimit.instAlgebra (R := k) (S := S) (φ := σAlg)
  letI : Algebra R∞ S∞ :=
    (Ring.DirectLimit.map
      (fun s ↦ algebraMap (R s) (S s))
      (fun _ _ _ ↦ by ext x <;> rfl)).toAlgebra
  have eBase : R∞ ≃ₐ[k] k := by
    -- Proof comment: identify the direct limit of the constant base-field system with `k`.
    simpa [I, R, ρAlg, ρ, R∞] using
      (constantDirectLimitAlgEquiv (k := k) I)
  have eTarget : S∞ ≃ₐ[k] K := by
    -- Proof comment: identify the direct limit of the finite-adjoin stages with the ambient
    -- field `K`.
    simpa [I, S, σAlg, σ, S∞] using
      (finiteAdjoinDirectLimitAlgEquiv (k := k) (K := K))
  have hSmoothDirectLimit : Algebra.FormallySmooth R∞ S∞ := by
    -- Route correction: the finite-adjoin direct-limit assembly now lives in the theorem-local
    -- support file, leaving this theorem as the transport/composition wrapper from the source
    -- proof.
    simpa [I, R, S, ρAlg, σAlg, ρ, σ, R∞, S∞] using
      (finiteAdjoinDirectLimitFormallySmooth (k := k) (K := K))
  have hSmoothBase : Algebra.FormallySmooth k R∞ := by
    -- Proof comment: transport the tautological formal smoothness of `k/k` across the constant
    -- direct-limit equivalence.
    exact Algebra.FormallySmooth.of_equiv eBase.symm
  have hSmoothTarget : Algebra.FormallySmooth k S∞ := by
    -- Proof comment: compose the formally smooth base map `k → R∞` with the formally smooth
    -- colimit extension `R∞ → S∞`.
    letI : Algebra.FormallySmooth k R∞ := hSmoothBase
    letI : Algebra.FormallySmooth R∞ S∞ := hSmoothDirectLimit
    exact Algebra.FormallySmooth.comp k R∞ S∞
  -- Proof comment: transport the formal smoothness of the finite-adjoin colimit back to the
  -- ambient field `K`.
  letI : Algebra.FormallySmooth k S∞ := hSmoothTarget
  exact Algebra.FormallySmooth.of_equiv eTarget

/-- Low-priority instance supplied by Lemma 10.158.7 (3). -/
@[instance low] instance [IsSeparableOver k K] : Algebra.FormallySmooth k K :=
  formallySmooth_of_isSeparableOver

end

end Algebra
