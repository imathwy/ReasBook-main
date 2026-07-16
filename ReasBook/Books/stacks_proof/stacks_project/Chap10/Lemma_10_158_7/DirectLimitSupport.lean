import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_42_1
import stacks_proof.stacks_project.Chap10.Lemma_10_134_9
import stacks_proof.stacks_project.Chap10.Lemma_10_158_6
import stacks_proof.stacks_project.Chap10.Lemma_10_127_9

open scoped IntermediateField TensorProduct

universe u v

namespace Algebra

section

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

/-- Helper for Chap10 Lemma 10 158 7: every finite adjoin intermediate field inside a
Stacks-separable extension is formally smooth over the base field. -/
private lemma supportFiniteAdjoinStageFormallySmooth [IsSeparableOver k K] (s : Finset K) :
    Algebra.FormallySmooth k ↥(IntermediateField.adjoin k (s : Set K)) := by
  -- Proof comment: a finite adjoin stage is finitely generated, so Stacks-separability makes it
  -- separably generated over `k`.
  let L : IntermediateField k K := IntermediateField.adjoin k (s : Set K)
  have hSepOver : IsSeparableOver k L :=
    IsSeparableOver.of_intermediateField inferInstance L
  have hL : L.FG := by
    simpa [L] using IntermediateField.fg_adjoin_finset (F := k) (E := K) s
  letI : Algebra.EssFiniteType k L := (IntermediateField.essFiniteType_iff).2 hL
  have hTopSepGen : IsSeparablyGenerated k (⊤ : IntermediateField k L) := by
    exact hSepOver.isSeparablyGenerated_of_fg ⊤ (IntermediateField.fg_top k L)
  have hSepGen : IsSeparablyGenerated k L := by
    simpa using hTopSepGen.of_algEquiv IntermediateField.topEquiv
  rcases hSepGen with ⟨t, ht, hsep⟩
  have htRange : Set.range ((↑) : t → L) = t := by
    ext x
    simp
  letI : Algebra.IsSeparable (IntermediateField.adjoin k (Set.range ((↑) : t → L))) L := by
    rw [htRange]
    exact hsep
  -- Proof comment: apply the canonical formally-smooth theorem for separably generated field
  -- extensions to the chosen transcendence basis.
  exact Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable ht.1

/-- Helper for Chap10 Lemma 10 158 7: each finite adjoin stage has vanishing first cotangent
homology over the base field. -/
private lemma supportFiniteAdjoinStageH1Subsingleton [IsSeparableOver k K] (s : Finset K) :
    Subsingleton (Algebra.H1Cotangent k ↥(IntermediateField.adjoin k (s : Set K))) := by
  -- Proof comment: formal smoothness of the finite stage converts to the field-level `H₁`
  -- criterion from Lemma 10.158.6.
  let L : IntermediateField k K := IntermediateField.adjoin k (s : Set K)
  have hSmoothStage : Algebra.FormallySmooth k L := by
    simpa [L] using supportFiniteAdjoinStageFormallySmooth (k := k) (K := K) s
  simpa [L] using
    (Algebra.formallySmooth_iff_subsingleton_h1Cotangent_of_field k L).1 hSmoothStage

/-- Helper for Chap10 Lemma 10 158 7: flat base change preserves the vanishing of `H₁` for a
finite adjoin stage. -/
private lemma supportFiniteAdjoinStageBaseChangeH1Subsingleton [IsSeparableOver k K]
    {T : Type v} [Field T] [Algebra k T] (s : Finset K) :
    let L : Type v := ↥(IntermediateField.adjoin k (s : Set K))
    let P : Algebra.Extension k L := (Generators.self k L).toExtension
    Subsingleton (P.baseChange (T := T)).H1Cotangent := by
  -- Proof comment: tensoring the stage `H₁` with the flat target field keeps it subsingleton,
  -- and the base-change comparison identifies that tensor product with the target `H₁`.
  intro L P
  haveI : Subsingleton (Algebra.H1Cotangent k L) := by
    simpa [L] using supportFiniteAdjoinStageH1Subsingleton (k := k) (K := K) s
  haveI : Subsingleton (T ⊗[k] Algebra.H1Cotangent k L) := inferInstance
  exact (P.tensorH1CotangentOfFlat T).symm.subsingleton

/-- Helper for Chap10 Lemma 10 158 7: once the base-changed `H₁` of a self-presentation
vanishes, the degree-`1` differential of its base-changed naive cotangent complex is injective. -/
private theorem supportSelfPresentationBaseChangeDifferentialInjective
    {L T : Type*} [Field L] [Field T] [Algebra k L] [Algebra k T] [Algebra L T]
    [IsScalarTower k L T]
    (hH1 :
      Subsingleton (((Generators.self k L).toExtension.baseChange (T := T)).H1Cotangent)) :
    Function.Injective
      ((((ModuleCat.extendScalars (algebraMap L T)).mapHomologicalComplex
            (ComplexShape.down ℕ)).obj
          (Algebra.Extension.naiveCotangentChainComplex
            ((Generators.self k L).toExtension))).d 1 0).hom := by
  let P : Algebra.Extension k L := (Generators.self k L).toExtension
  letI : Subsingleton (P.baseChange (T := T)).H1Cotangent := by
    simpa [P] using hH1
  -- Proof comment: the owner criterion for `H₁`-vanishing turns the base-changed self-presentation
  -- into the desired injective degree-`1` differential.
  simpa [P, Algebra.Extension.naiveCotangentChainComplex] using
    ((Algebra.Extension.subsingleton_h1Cotangent (P.baseChange (T := T))).mp inferInstance)

/-- Helper for Chap10 Lemma 10 158 7: every finite adjoin stage satisfies the injectivity
hypothesis after base change to any field-valued `k`-algebra target. -/
private theorem supportFiniteAdjoinStageBaseChangeDifferentialInjective [IsSeparableOver k K]
    {T : Type v} [Field T] [Algebra k T] (s : Finset K)
    [Algebra ↥(IntermediateField.adjoin k (s : Set K)) T]
    [IsScalarTower k ↥(IntermediateField.adjoin k (s : Set K)) T] :
    Function.Injective
      ((((ModuleCat.extendScalars
            (algebraMap ↥(IntermediateField.adjoin k (s : Set K)) T)).mapHomologicalComplex
            (ComplexShape.down ℕ)).obj
          (Algebra.Extension.naiveCotangentChainComplex
            ((Generators.self k ↥(IntermediateField.adjoin k (s : Set K))).toExtension))).d 1 0).hom := by
  let L : Type v := ↥(IntermediateField.adjoin k (s : Set K))
  have hH1BaseChange :
      Subsingleton (((Generators.self k L).toExtension.baseChange (T := T)).H1Cotangent) := by
    -- Proof comment: finite-stage `H₁` vanishing survives flat base change to the chosen target
    -- field by the dedicated stage lemma proved above.
    simpa [L] using
      supportFiniteAdjoinStageBaseChangeH1Subsingleton (k := k) (K := K) (T := T) s
  -- Proof comment: reduce the stagewise direct-limit injectivity claim to the generic
  -- self-presentation bridge.
  simpa [L] using
    (supportSelfPresentationBaseChangeDifferentialInjective
      (k := k) (L := L) (T := T) hH1BaseChange)

/-- Helper for Chap10 Lemma 10 158 7: the direct limit of a constant `k`-system is `k` as a
`k`-algebra. -/
private noncomputable def supportConstantDirectLimitAlgEquiv
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
private noncomputable def supportFiniteAdjoinDirectLimitAlgEquiv :
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

/-- Helper for Chap10 Lemma 10 158 7: the finite-adjoin direct-limit system satisfies the
stagewise injectivity hypothesis needed for the cotangent direct-limit theorem. -/
lemma finiteAdjoinDirectLimitStagewiseInjective [IsSeparableOver k K] :
    let I : Type v := Finset K
    let S : I → Type v := fun s ↦ ↥(IntermediateField.adjoin k (s : Set K))
    let σAlg : ∀ s t, s ≤ t → S s →ₐ[k] S t := fun s t h ↦
      IntermediateField.inclusion <|
        IntermediateField.adjoin_le_iff.mpr (show (s : Set K) ⊆ t from h)
    let σ : ∀ s t, s ≤ t → S s →+* S t := fun s t h ↦ (σAlg s t h).toRingHom
    let S∞ : Type v := Ring.DirectLimit S σ
    ∀ s : I,
      let Pi : Generators k (S s) (S s) := Generators.self k (S s)
      Function.Injective
        ((((ModuleCat.extendScalars
              (Ring.DirectLimit.of S σ s)).mapHomologicalComplex
              (ComplexShape.down ℕ)).obj
            (Algebra.Extension.naiveCotangentChainComplex Pi.toExtension)).d 1 0).hom) := by
  classical
  intro I S σAlg σ S∞ s
  letI : Algebra (S s) S∞ := (Ring.DirectLimit.of S σ s).toAlgebra
  letI : IsScalarTower k (S s) S∞ := IsScalarTower.of_algebraMap_eq' rfl
  -- Proof comment: the finite-stage base-change injectivity lemma already matches the direct-limit
  -- theorem after specializing the target field to the finite-adjoin colimit.
  simpa [S] using
    (supportFiniteAdjoinStageBaseChangeDifferentialInjective
      (k := k) (K := K) (T := S∞) s)

/-- Helper for Chap10 Lemma 10 158 7: the finite-adjoin direct limit has vanishing first
cotangent homology. -/
lemma finiteAdjoinDirectLimitH1Subsingleton [IsSeparableOver k K] :
    let I : Type v := Finset K
    let R : I → Type u := fun _ ↦ k
    let S : I → Type v := fun s ↦ ↥(IntermediateField.adjoin k (s : Set K))
    let ρAlg : ∀ s t, s ≤ t → R s →ₐ[k] R t := fun _ _ _ ↦ AlgHom.id k k
    let σAlg : ∀ s t, s ≤ t → S s →ₐ[k] S t := fun s t h ↦
      IntermediateField.inclusion <|
        IntermediateField.adjoin_le_iff.mpr (show (s : Set K) ⊆ t from h)
    let ρ : ∀ s t, s ≤ t → R s →+* R t := fun s t h ↦ (ρAlg s t h).toRingHom
    let σ : ∀ s t, s ≤ t → S s →+* S t := fun s t h ↦ (σAlg s t h).toRingHom
    let R∞ : Type u := Ring.DirectLimit R ρ
    let S∞ : Type v := Ring.DirectLimit S σ
    Subsingleton (Algebra.H1Cotangent R∞ S∞) := by
  classical
  intro I R S ρAlg σAlg ρ σ R∞ S∞
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
  letI : Algebra k R∞ := Ring.DirectLimit.instAlgebra (R := k) (S := R) (φ := ρAlg)
  letI : Algebra k S∞ := Ring.DirectLimit.instAlgebra (R := k) (S := S) (φ := σAlg)
  have hcomm :
      ∀ ⦃s t : I⦄ (h : s ≤ t),
        (algebraMap (R t) (S t)).comp (ρ s t h) =
          (σ s t h).comp (algebraMap (R s) (S s)) := by
    intro s t h
    ext x
    rfl
  have hstage :
      ∀ s : I,
        let Pi : Generators (R s) (S s) (S s) := Generators.self (R s) (S s)
        Function.Injective
          ((((ModuleCat.extendScalars
                (Ring.DirectLimit.of S σ s)).mapHomologicalComplex
                (ComplexShape.down ℕ)).obj
              (Algebra.Extension.naiveCotangentChainComplex Pi.toExtension)).d 1 0).hom) := by
    -- Proof comment: specialize the dedicated stagewise bridge to the exact spelling world used
    -- by the direct-limit theorem.
    simpa [I, S, σAlg, σ, S∞] using
      (finiteAdjoinDirectLimitStagewiseInjective (k := k) (K := K))
  -- Proof comment: the general cotangent direct-limit theorem now applies without further
  -- transport work in the main item theorem.
  simpa [I, R, S, ρ, σ, R∞, S∞] using
    (Algebra.naiveCotangentDirectLimit_subsingletonH1_of_stagewiseInjective
      (R := R) (S := S) (ρ := ρ) (σ := σ) hcomm hstage)

/-- Helper for Chap10 Lemma 10 158 7: the finite-adjoin direct limit is formally smooth over the
constant direct-limit base field. -/
lemma finiteAdjoinDirectLimitFormallySmooth [IsSeparableOver k K] :
    let I : Type v := Finset K
    let R : I → Type u := fun _ ↦ k
    let S : I → Type v := fun s ↦ ↥(IntermediateField.adjoin k (s : Set K))
    let ρAlg : ∀ s t, s ≤ t → R s →ₐ[k] R t := fun _ _ _ ↦ AlgHom.id k k
    let σAlg : ∀ s t, s ≤ t → S s →ₐ[k] S t := fun s t h ↦
      IntermediateField.inclusion <|
        IntermediateField.adjoin_le_iff.mpr (show (s : Set K) ⊆ t from h)
    let ρ : ∀ s t, s ≤ t → R s →+* R t := fun s t h ↦ (ρAlg s t h).toRingHom
    let σ : ∀ s t, s ≤ t → S s →+* S t := fun s t h ↦ (σAlg s t h).toRingHom
    let R∞ : Type u := Ring.DirectLimit R ρ
    let S∞ : Type v := Ring.DirectLimit S σ
    Algebra.FormallySmooth R∞ S∞ := by
  classical
  intro I R S ρAlg σAlg ρ σ R∞ S∞
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
  letI : Algebra k R∞ := Ring.DirectLimit.instAlgebra (R := k) (S := R) (φ := ρAlg)
  letI : Algebra k S∞ := Ring.DirectLimit.instAlgebra (R := k) (S := S) (φ := σAlg)
  have eBase : R∞ ≃ₐ[k] k := by
    -- Proof comment: identify the direct limit of the constant base-field system with `k`.
    simpa [I, R, ρAlg, ρ, R∞] using
      (supportConstantDirectLimitAlgEquiv (k := k) I)
  have eTarget : S∞ ≃ₐ[k] K := by
    -- Proof comment: identify the direct limit of the finite-adjoin stages with the ambient
    -- field `K`.
    simpa [I, S, σAlg, σ, S∞] using
      (supportFiniteAdjoinDirectLimitAlgEquiv (k := k) (K := K))
  letI : Field R∞ := Function.Injective.field eBase.toRingHom eBase.injective
  letI : Field S∞ := Function.Injective.field eTarget.toRingHom eTarget.injective
  have hH1 : Subsingleton (Algebra.H1Cotangent R∞ S∞) := by
    -- Proof comment: consume the specialized `H₁`-vanishing theorem rather than rebuilding the
    -- direct-limit assembly inside the final theorem.
    simpa [I, R, S, ρAlg, σAlg, ρ, σ, R∞, S∞] using
      (finiteAdjoinDirectLimitH1Subsingleton (k := k) (K := K))
  -- Proof comment: for field extensions, vanishing `H₁` is exactly the formal smoothness
  -- criterion from Lemma 10.158.6.
  exact (Algebra.formallySmooth_iff_subsingleton_h1Cotangent_of_field R∞ S∞).2 hH1

end

end Algebra
