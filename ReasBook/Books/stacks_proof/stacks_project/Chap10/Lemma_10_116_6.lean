import Mathlib
import stacks_proof.stacks_project.Chap05.Definition_5_10_1
import stacks_proof.stacks_project.Chap10.Lemma_10_112_7
import stacks_proof.stacks_project.Chap10.Lemma_10_116_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v w

section

variable {k : Type u} [Field k]
variable {K : Type v} [Field K] [Algebra k K]

/-- Helper for Chap10 Lemma 10 116 6: the coefficient-extension map gives the canonical algebra
structure on polynomial rings after extending the ground field. -/
noncomputable local instance mvPolynomialFieldExtensionAlgebra {n : ℕ} :
    Algebra (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) K) :=
  (MvPolynomial.mapAlgHom (σ := Fin n) (Algebra.ofId k K)).toAlgebra

variable {S : Type w} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]

local notation "S_K" => K ⊗[k] S
local notation "iSK" => (((includeRight : S →ₐ[k] S_K) : S →+* S_K))

/-- Helper for Chap10 Lemma 10 116 6: on an irreducible affine finite-type spectrum, local
topological Krull dimension is the global ring Krull dimension at every point. -/
lemma topologicalKrullDimAt_eq_ringKrullDim_of_irreducibleSpectrum
    {F : Type u} [Field F] {A : Type v} [CommRing A] [Algebra F A]
    [Algebra.FiniteType F A] [IsDomain A] (z : PrimeSpectrum A) :
    topologicalKrullDimAt z = ringKrullDim A := by
  -- The component formula has only the whole space as an irreducible component.
  rw [topologicalKrullDimAt_eq_iSup_topologicalKrullDim_irreducibleComponents_through
    (k := F) (S := A) z]
  letI : Subsingleton
      { Z : irreducibleComponents (PrimeSpectrum A) // z ∈ (Z : Set (PrimeSpectrum A)) } := by
    refine ⟨fun Z W ↦ Subtype.ext ?_⟩
    apply Subtype.ext
    have hZ : (Z.1 : Set (PrimeSpectrum A)) = Set.univ := by
      simpa [irreducibleComponents_eq_singleton] using Z.1.2
    have hW : (W.1 : Set (PrimeSpectrum A)) = Set.univ := by
      simpa [irreducibleComponents_eq_singleton] using W.1.2
    exact hZ.trans hW.symm
  have hmem_univ : Set.univ ∈ irreducibleComponents (PrimeSpectrum A) := by
    rw [irreducibleComponents_eq_singleton]
    simp
  have hz_univ : z ∈ (Set.univ : Set (PrimeSpectrum A)) := Set.mem_univ z
  let Z0 : { Z : irreducibleComponents (PrimeSpectrum A) // z ∈ (Z : Set (PrimeSpectrum A)) } :=
    ⟨⟨Set.univ, hmem_univ⟩, hz_univ⟩
  have huniv :
      topologicalKrullDim (Set.univ : Set (PrimeSpectrum A)) =
        topologicalKrullDim (PrimeSpectrum A) := by
    simpa using IsHomeomorph.topologicalKrullDim_eq
      (Homeomorph.Set.univ (PrimeSpectrum A))
      (Homeomorph.Set.univ (PrimeSpectrum A)).isHomeomorph
  -- The singleton component supremum is the whole spectrum, whose dimension is the ring dimension.
  calc
    (⨆ Z : { Z : irreducibleComponents (PrimeSpectrum A) // z ∈ (Z : Set (PrimeSpectrum A)) },
        topologicalKrullDim (Z : Set (PrimeSpectrum A))) =
        topologicalKrullDim (Z0 : Set (PrimeSpectrum A)) :=
      ciSup_subsingleton Z0 _
    _ = topologicalKrullDim (Set.univ : Set (PrimeSpectrum A)) := by
      simp [Z0]
    _ = topologicalKrullDim (PrimeSpectrum A) := huniv
    _ = ringKrullDim A := PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A

/-- Helper for Chap10 Lemma 10 116 6: every point of affine `n`-space over a field has local
topological Krull dimension equal to the number of variables. -/
lemma topologicalKrullDimAt_mvPolynomial_eq_nat
    {F : Type u} [Field F] (n : ℕ) (y : PrimeSpectrum (MvPolynomial (Fin n) F)) :
    topologicalKrullDimAt y = (n : WithBot ℕ∞) := by
  -- Affine space is irreducible, so the preceding helper reduces the local computation to the
  -- standard Krull dimension of a polynomial ring over a field.
  calc
    topologicalKrullDimAt y = ringKrullDim (MvPolynomial (Fin n) F) :=
      topologicalKrullDimAt_eq_ringKrullDim_of_irreducibleSpectrum (F := F) y
    _ = (n : WithBot ℕ∞) := by
      simp

omit [Algebra.FiniteType k S] in
/-- Helper for Chap10 Lemma 10 116 6: the polynomial presentation obtained by base change is the
tensor product of the original presentation after the standard polynomial/tensor equivalence. -/
lemma tensorBaseChangePolynomialAlgHom_restrictScalars
    {n : ℕ} (π : MvPolynomial (Fin n) k →ₐ[k] S) :
    (AlgHom.restrictScalars k
      (MvPolynomial.aeval (R := K) (S₁ := S_K)
        fun i ↦ (1 : K) ⊗ₜ[k] π (MvPolynomial.X i) :
          MvPolynomial (Fin n) K →ₐ[K] S_K)) =
      (Algebra.TensorProduct.map (AlgHom.id k K) π).comp
        ((MvPolynomial.algebraTensorAlgEquiv k K).symm.toAlgHom.restrictScalars k) := by
  -- Compare the two `k`-algebra maps on coefficients and variables.
  apply MvPolynomial.algHom_ext'
  · ext c
    simp [MvPolynomial.algebraTensorAlgEquiv]
  · intro i
    simp

omit [Algebra.FiniteType k S] in
/-- Helper for Chap10 Lemma 10 116 6: a surjective polynomial presentation stays surjective after
tensoring with the field extension and identifying the tensor source with a polynomial algebra. -/
lemma tensorBaseChangePolynomialAlgHom_surjective
    {n : ℕ} (π : MvPolynomial (Fin n) k →ₐ[k] S) (hπ : Function.Surjective π) :
    Function.Surjective
      (MvPolynomial.aeval (R := K) (S₁ := S_K)
        fun i ↦ (1 : K) ⊗ₜ[k] π (MvPolynomial.X i) :
          MvPolynomial (Fin n) K →ₐ[K] S_K) := by
  let πK : MvPolynomial (Fin n) K →ₐ[K] S_K :=
    MvPolynomial.aeval fun i ↦ (1 : K) ⊗ₜ[k] π (MvPolynomial.X i)
  have hmap :
      Function.Surjective (Algebra.TensorProduct.map (AlgHom.id k K) π :
        K ⊗[k] MvPolynomial (Fin n) k →ₐ[k] S_K) := by
    -- Tensoring a surjective map with the identity remains surjective.
    exact Algebra.TensorProduct.map_surjective (f := AlgHom.id k K) (g := π)
      Function.surjective_id hπ
  have hraw :
      Function.Surjective
        ((Algebra.TensorProduct.map (AlgHom.id k K) π).comp
          ((MvPolynomial.algebraTensorAlgEquiv k K).symm.toAlgHom.restrictScalars k) :
            MvPolynomial (Fin n) K →ₐ[k] S_K) := by
    -- Precompose with the polynomial/tensor algebra equivalence.
    exact hmap.comp (MvPolynomial.algebraTensorAlgEquiv k K).symm.surjective
  have hrestricted :
      Function.Surjective
        ((AlgHom.restrictScalars k πK) : MvPolynomial (Fin n) K →ₐ[k] S_K) := by
    -- Move from the tensor spelling back to the `aeval` presentation spelling.
    simpa [πK, tensorBaseChangePolynomialAlgHom_restrictScalars (K := K) π] using hraw
  simpa [πK] using hrestricted

omit [Algebra.FiniteType k S] in
/-- Helper for Chap10 Lemma 10 116 6: restricting the base-changed polynomial presentation along
the coefficient-extension map recovers the original presentation followed by `S → K ⊗[k] S`. -/
lemma tensorBaseChangePolynomialPresentation_algHom_comp
    {n : ℕ} (π : MvPolynomial (Fin n) k →ₐ[k] S) :
    (AlgHom.restrictScalars k
      (MvPolynomial.aeval (R := K) (S₁ := S_K)
        fun i ↦ (1 : K) ⊗ₜ[k] π (MvPolynomial.X i) :
          MvPolynomial (Fin n) K →ₐ[K] S_K)).comp
        (MvPolynomial.mapAlgHom (σ := Fin n) (Algebra.ofId k K)) =
      (includeRight : S →ₐ[k] S_K).comp π := by
  -- Compare the two maps from the base polynomial ring on coefficients and variables.
  apply MvPolynomial.algHom_ext
  intro i
  simp

omit [Algebra.FiniteType k S] in
/-- Helper for Chap10 Lemma 10 116 6: the base-changed point over the polynomial presentation
contracts to the original polynomial-presentation point. -/
lemma tensorBaseChangePolynomialPresentation_comap
    {n : ℕ} (π : MvPolynomial (Fin n) k →ₐ[k] S)
    (x : PrimeSpectrum S) (xK : PrimeSpectrum S_K)
    (hxK : PrimeSpectrum.comap iSK xK = x) :
    PrimeSpectrum.comap
        ((MvPolynomial.mapAlgHom (σ := Fin n) (Algebra.ofId k K)).toRingHom)
        (PrimeSpectrum.comap
          ((MvPolynomial.aeval (R := K) (S₁ := S_K)
            fun i ↦ (1 : K) ⊗ₜ[k] π (MvPolynomial.X i) :
              MvPolynomial (Fin n) K →ₐ[K] S_K).toRingHom) xK) =
      PrimeSpectrum.comap π.toRingHom x := by
  let πK : MvPolynomial (Fin n) K →ₐ[K] S_K :=
    MvPolynomial.aeval fun i ↦ (1 : K) ⊗ₜ[k] π (MvPolynomial.X i)
  let β : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin n) K :=
    MvPolynomial.mapAlgHom (σ := Fin n) (Algebra.ofId k K)
  have hcompRing :
      πK.toRingHom.comp β.toRingHom = ((includeRight : S →ₐ[k] S_K).comp π).toRingHom := by
    -- The algebra-hom equality above gives the corresponding equality of ring maps.
    simpa [πK, β] using
      congrArg AlgHom.toRingHom
        (tensorBaseChangePolynomialPresentation_algHom_comp (K := K) π)
  -- Functoriality of `PrimeSpectrum.comap` then transports the contraction equation `hxK`.
  rw [← PrimeSpectrum.comap_comp_apply]
  rw [hcompRing]
  have hincludeRing :
      ((includeRight : S →ₐ[k] S_K).comp π).toRingHom =
        (((includeRight : S →ₐ[k] S_K) : S →+* S_K).comp π.toRingHom) := rfl
  rw [hincludeRing]
  rw [PrimeSpectrum.comap_comp_apply, hxK]

omit [Algebra.FiniteType k S] in
/-- Helper for Chap10 Lemma 10 116 6: the tensor base-change presentation square commutes on
prime-spectrum contractions before specializing to a point lying over a chosen downstairs point. -/
lemma tensorBaseChangePolynomialPresentation_comap_apply
    {n : ℕ} (π : MvPolynomial (Fin n) k →ₐ[k] S) (q : PrimeSpectrum S_K) :
    PrimeSpectrum.comap
        ((MvPolynomial.mapAlgHom (σ := Fin n) (Algebra.ofId k K)).toRingHom)
        (PrimeSpectrum.comap
          ((MvPolynomial.aeval (R := K) (S₁ := S_K)
            fun i ↦ (1 : K) ⊗ₜ[k] π (MvPolynomial.X i) :
              MvPolynomial (Fin n) K →ₐ[K] S_K).toRingHom) q) =
      PrimeSpectrum.comap π.toRingHom (PrimeSpectrum.comap iSK q) := by
  -- Rewrite the square as an equality of ring maps, then apply functoriality of `Spec`.
  let πK : MvPolynomial (Fin n) K →ₐ[K] S_K :=
    MvPolynomial.aeval fun i ↦ (1 : K) ⊗ₜ[k] π (MvPolynomial.X i)
  let β : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin n) K :=
    MvPolynomial.mapAlgHom (σ := Fin n) (Algebra.ofId k K)
  have hcompRing :
      πK.toRingHom.comp β.toRingHom = ((includeRight : S →ₐ[k] S_K).comp π).toRingHom := by
    simpa [πK, β] using
      congrArg AlgHom.toRingHom
        (tensorBaseChangePolynomialPresentation_algHom_comp (K := K) π)
  rw [← PrimeSpectrum.comap_comp_apply]
  rw [hcompRing]
  have hincludeRing :
      ((includeRight : S →ₐ[k] S_K).comp π).toRingHom =
        (((includeRight : S →ₐ[k] S_K) : S →+* S_K).comp π.toRingHom) := rfl
  rw [hincludeRing]
  rw [PrimeSpectrum.comap_comp_apply]

/-- Helper for Chap10 Lemma 10 116 6: Lemma 10.112.7 rewrites the height of a prime under a
Noetherian going-down map as the height of its contraction plus the height of the fiber prime. -/
lemma height_eq_under_add_fiberPrimeHeight_of_hasGoingDown
    {R : Type*} {T : Type*} [CommRing R] [CommRing T] [Algebra R T]
    [IsNoetherianRing R] [IsNoetherianRing T] [Algebra.HasGoingDown R T]
    (q : PrimeSpectrum T) :
    q.asIdeal.height = (q.asIdeal.under R).height + (fiberPrimeAt R T q).asIdeal.height := by
  -- Convert the local-ring dimension formula into the corresponding equality of prime heights.
  have h : ((q.asIdeal.height : ℕ∞) : WithBot ℕ∞) =
      ((q.asIdeal.under R).height : ℕ∞) +
        (((fiberPrimeAt R T q).asIdeal.height : ℕ∞) : WithBot ℕ∞) := by
    calc
      ((q.asIdeal.height : ℕ∞) : WithBot ℕ∞) =
          ringKrullDim (Localization.AtPrime q.asIdeal) := by
            rw [IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal
              (Localization.AtPrime q.asIdeal)]
      _ = ringKrullDim (Localization.AtPrime (q.asIdeal.under R)) +
            ringKrullDim (fiberLocalRingAt R T q) :=
          ringKrullDim_localizationAtPrime_eq_ringKrullDim_localizationAtPrime_under_add_ringKrullDim_fiberLocalRingAt_of_hasGoingDown
            q
      _ = ((q.asIdeal.under R).height : ℕ∞) +
          (((fiberPrimeAt R T q).asIdeal.height : ℕ∞) : WithBot ℕ∞) := by
            rw [IsLocalization.AtPrime.ringKrullDim_eq_height (q.asIdeal.under R)
              (Localization.AtPrime (q.asIdeal.under R))]
            rw [IsLocalization.AtPrime.ringKrullDim_eq_height (fiberPrimeAt R T q).asIdeal
              (fiberLocalRingAt R T q)]
  exact_mod_cast h

/-- Helper for Chap10 Lemma 10 116 6: the going-down height formula can be read after identifying
the contraction prime explicitly. -/
lemma height_eq_comap_add_fiberPrimeHeight_of_hasGoingDown
    {R : Type*} {T : Type*} [CommRing R] [CommRing T] [Algebra R T]
    [IsNoetherianRing R] [IsNoetherianRing T] [Algebra.HasGoingDown R T]
    {p : PrimeSpectrum R} (q : PrimeSpectrum T)
    (hq : PrimeSpectrum.comap (algebraMap R T) q = p) :
    q.asIdeal.height = p.asIdeal.height + (fiberPrimeAt R T q).asIdeal.height := by
  -- Replace the `under` prime in the general formula by the named contraction point.
  have h_under : q.asIdeal.under R = p.asIdeal := by
    simpa [Ideal.under_def, PrimeSpectrum.comap_asIdeal] using
      congrArg PrimeSpectrum.asIdeal hq
  simpa [h_under] using height_eq_under_add_fiberPrimeHeight_of_hasGoingDown (R := R) (T := T) q

omit [Algebra.FiniteType k S] in
/-- Helper for Chap10 Lemma 10 116 6: the kernel of the base-changed polynomial presentation is
the extension of the original presentation kernel along the coefficient-extension map. -/
lemma tensorBaseChangePolynomialAlgHom_ker
    {n : ℕ} (π : MvPolynomial (Fin n) k →ₐ[k] S) (hπ : Function.Surjective π) :
    let πK : MvPolynomial (Fin n) K →ₐ[K] S_K :=
      MvPolynomial.aeval fun i ↦ (1 : K) ⊗ₜ[k] π (MvPolynomial.X i)
    let β : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin n) K :=
      MvPolynomial.mapAlgHom (σ := Fin n) (Algebra.ofId k K)
    RingHom.ker πK.toRingHom = Ideal.map β.toRingHom (RingHom.ker π.toRingHom) := by
  intro πK β
  let e : K ⊗[k] MvPolynomial (Fin n) k ≃ₐ[K] MvPolynomial (Fin n) K :=
    MvPolynomial.algebraTensorAlgEquiv k K
  let raw : K ⊗[k] MvPolynomial (Fin n) k →ₐ[k] S_K :=
    Algebra.TensorProduct.map (AlgHom.id k K) π
  have hraw : RingHom.ker raw.toRingHom =
      Ideal.map (includeRight :
        MvPolynomial (Fin n) k →ₐ[k] K ⊗[k] MvPolynomial (Fin n) k).toRingHom
        (RingHom.ker π.toRingHom) := by
    -- Tensoring the surjective presentation with `K` extends the kernel along `includeRight`.
    simpa [raw] using Algebra.TensorProduct.lTensor_ker (A := K) π hπ
  have hπK : πK.toRingHom = raw.toRingHom.comp e.symm.toRingHom := by
    -- Move from the tensor source to the polynomial source via the standard algebra equivalence.
    simpa [πK, raw, e] using
      congrArg AlgHom.toRingHom
        (tensorBaseChangePolynomialAlgHom_restrictScalars (K := K) π)
  have hβ : β.toRingHom = e.toRingHom.comp
      (includeRight : MvPolynomial (Fin n) k →ₐ[k] K ⊗[k] MvPolynomial (Fin n) k).toRingHom := by
    -- The coefficient-extension map is the tensor inclusion followed by the polynomial/tensor
    -- equivalence.
    have hβAlg : β =
        (e.toAlgHom.restrictScalars k).comp
          (includeRight : MvPolynomial (Fin n) k →ₐ[k] K ⊗[k] MvPolynomial (Fin n) k) := by
      apply MvPolynomial.algHom_ext
      intro i
      simp [β, e]
    simpa using congrArg AlgHom.toRingHom hβAlg
  calc
    RingHom.ker πK.toRingHom = Ideal.comap e.symm.toRingHom (RingHom.ker raw.toRingHom) := by
      rw [hπK]
      exact (RingHom.comap_ker raw.toRingHom e.symm.toRingHom).symm
    _ = Ideal.map e.toRingHom (RingHom.ker raw.toRingHom) := by
      -- Move the ideal across the equivalence by witnesses, avoiding a brittle simp reduction of
      -- `Ideal.comap_symm`.
      exact Ideal.comap_symm (f := e.toRingEquiv) (I := RingHom.ker raw.toRingHom)
    _ = Ideal.map e.toRingHom
          (Ideal.map (includeRight :
            MvPolynomial (Fin n) k →ₐ[k] K ⊗[k] MvPolynomial (Fin n) k).toRingHom
            (RingHom.ker π.toRingHom)) := by
      rw [hraw]
    _ = Ideal.map β.toRingHom (RingHom.ker π.toRingHom) := by
      rw [Ideal.map_map]
      rw [hβ]

omit [Algebra.FiniteType k S] in
/-- Helper for Chap10 Lemma 10 116 6: tensoring a `k`-algebra with the field extension `K`
gives a flat module over the original algebra through the right tensor inclusion. -/
lemma tensorProductIncludeRight_moduleFlat
    (A : Type*) [CommRing A] [Algebra k A] :
    Module.Flat A (K ⊗[k] A) := by
  -- First use flat base change for `A ⊗[k] K`, where the standard flatness instance applies.
  have hflatTensor : Module.Flat A (A ⊗[k] K) := by
    exact Module.Flat.baseChange k A K
  -- The tensor-commutativity equivalence is `A`-linear for the right-inclusion action.
  let e : K ⊗[k] A ≃ₗ[A] A ⊗[k] K := by
    let e0 : K ⊗[k] A ≃ₗ[k] A ⊗[k] K := TensorProduct.comm k K A
    refine
      { toFun := e0
        invFun := e0.symm
        map_add' := e0.map_add
        map_smul' := ?_
        left_inv := e0.left_inv
        right_inv := e0.right_inv }
    intro a x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c b =>
        change (TensorProduct.comm k K A)
            (((includeRight : A →ₐ[k] K ⊗[k] A) a) * (c ⊗ₜ[k] b)) =
          (a * b) ⊗ₜ[k] c
        simp [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
          TensorProduct.comm_tmul]
    | add x y hx hy => simp [hx, hy]
  -- Transport flatness across the explicit linear equivalence.
  exact Module.Flat.of_linearEquiv e

omit [Algebra.FiniteType k S] in
/-- Helper for Chap10 Lemma 10 116 6: the coefficient-extension map on polynomial rings is flat. -/
lemma mvPolynomialFieldExtension_moduleFlat
    {n : ℕ} :
    let P := MvPolynomial (Fin n) k
    let PK := MvPolynomial (Fin n) K
    let β : P →ₐ[k] PK := MvPolynomial.mapAlgHom (σ := Fin n) (Algebra.ofId k K)
    letI : Algebra P PK := β.toAlgebra
    Module.Flat P PK := by
  intro P PK β
  letI : Algebra P PK := β.toAlgebra
  have hflatTensor : Module.Flat P (K ⊗[k] P) :=
    tensorProductIncludeRight_moduleFlat (K := K) P
  -- Identify `PK` with `K ⊗[k] P` and check that this identification is `P`-linear.
  let ePoly : PK ≃ₗ[P] K ⊗[k] P := by
    let eForward : K ⊗[k] P ≃ₐ[K] PK := MvPolynomial.algebraTensorAlgEquiv k K
    let eBackward : PK ≃ₐ[K] K ⊗[k] P := eForward.symm
    have hβAlg :
        β = (eForward.toAlgHom.restrictScalars k).comp
          (includeRight : P →ₐ[k] K ⊗[k] P) := by
      apply MvPolynomial.algHom_ext
      intro i
      calc
        β (MvPolynomial.X i) =
            (MvPolynomial.map (algebraMap k K)) (MvPolynomial.X i) := by
          rfl
        _ = MvPolynomial.X i := MvPolynomial.map_X (algebraMap k K) i
        _ = eForward (1 ⊗ₜ[k] MvPolynomial.X i) := by
          simp [eForward, MvPolynomial.algebraTensorAlgEquiv]
    have hβ_apply (p : P) :
        eBackward (β p) = (includeRight : P →ₐ[k] K ⊗[k] P) p := by
      have hp : eForward ((includeRight : P →ₐ[k] K ⊗[k] P) p) = β p := by
        simpa using congrArg (fun f : P →ₐ[k] PK => f p) hβAlg.symm
      rw [← hp]
      exact eForward.symm_apply_apply ((includeRight : P →ₐ[k] K ⊗[k] P) p)
    let e0 : PK ≃ₗ[K] K ⊗[k] P := eBackward.toLinearEquiv
    refine
      { toFun := e0
        invFun := e0.symm
        map_add' := e0.map_add
        map_smul' := ?_
        left_inv := e0.left_inv
        right_inv := e0.right_inv }
    intro p x
    change eBackward (β p * x) = (includeRight : P →ₐ[k] K ⊗[k] P) p * eBackward x
    rw [map_mul, hβ_apply]
  -- Transport the tensor-product flatness across the polynomial/tensor linear equivalence.
  exact Module.Flat.of_linearEquiv ePoly

/-- Helper for Chap10 Lemma 10 116 6: the height of the canonical fiber prime is the order height
of the corresponding point in the raw prime-spectrum fiber. -/
lemma fiberPrimeAt_height_eq_preimage_height
    {R T : Type*} [CommRing R] [CommRing T] [Algebra R T] (q : PrimeSpectrum T) :
    (fiberPrimeAt R T q).asIdeal.height =
      Order.height
        (⟨q, rfl⟩ :
          (PrimeSpectrum.comap (algebraMap R T)) ⁻¹'
            {PrimeSpectrum.comap (algebraMap R T) q}) := by
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R T) q
  let qOver : ↑(PrimeSpectrum.comap (algebraMap R T) ⁻¹' {p}) := ⟨q, rfl⟩
  let ePre : ↑(PrimeSpectrum.comap (algebraMap R T) ⁻¹' {p}) ≃o
      PrimeSpectrum (p.asIdeal.Fiber T) :=
    PrimeSpectrum.preimageOrderIsoFiber R T p
  have heq : ePre qOver = fiberPrimeAt R T q := rfl
  -- The order isomorphism from the raw fiber to the fiber ring preserves order height.
  calc
    (fiberPrimeAt R T q).asIdeal.height = Order.height (fiberPrimeAt R T q) := by
      rw [Ideal.height_eq_primeHeight]
      rfl
    _ = Order.height (ePre qOver) := by
      exact congrArg Order.height heq.symm
    _ = Order.height qOver := Order.height_orderIso ePre qOver
    _ =
        Order.height
          (⟨q, rfl⟩ :
            (PrimeSpectrum.comap (algebraMap R T)) ⁻¹'
              {PrimeSpectrum.comap (algebraMap R T) q}) := by
      rfl

/-- Helper for Chap10 Lemma 10 116 6: the ideal height of the canonical fiber prime is its
order height as a point of the fiber spectrum. -/
lemma fiberPrimeAt_height_eq_orderHeight
    {R T : Type*} [CommRing R] [CommRing T] [Algebra R T] (q : PrimeSpectrum T) :
    (fiberPrimeAt R T q).asIdeal.height = Order.height (fiberPrimeAt R T q) := by
  -- This is the standard comparison between ideal height and prime-spectrum order height.
  rw [Ideal.height_eq_primeHeight]
  rfl

/-- Helper for Chap10 Lemma 10 116 6: equality of order heights of fiber primes gives equality of
their ideal-height spellings. -/
lemma fiberPrimeAt_asIdeal_height_eq_of_orderHeight_eq
    {R T R' T' : Type*} [CommRing R] [CommRing T] [Algebra R T]
    [CommRing R'] [CommRing T'] [Algebra R' T']
    {q : PrimeSpectrum T} {q' : PrimeSpectrum T'}
    (h : Order.height (fiberPrimeAt R T q) = Order.height (fiberPrimeAt R' T' q')) :
    (fiberPrimeAt R T q).asIdeal.height = (fiberPrimeAt R' T' q').asIdeal.height := by
  -- Move through the canonical order-height spelling once, then apply the supplied comparison.
  calc
    (fiberPrimeAt R T q).asIdeal.height = Order.height (fiberPrimeAt R T q) :=
      fiberPrimeAt_height_eq_orderHeight (R := R) (T := T) q
    _ = Order.height (fiberPrimeAt R' T' q') := h
    _ = (fiberPrimeAt R' T' q').asIdeal.height :=
      (fiberPrimeAt_height_eq_orderHeight (R := R') (T := T') q').symm

/-- Helper for Chap10 Lemma 10 116 6: the order height of the canonical fiber prime is the order
height of the corresponding point in the raw prime-spectrum fiber. -/
lemma fiberPrimeAt_orderHeight_eq_preimage_height
    {R T : Type*} [CommRing R] [CommRing T] [Algebra R T] (q : PrimeSpectrum T) :
    Order.height (fiberPrimeAt R T q) =
      Order.height
        (⟨q, rfl⟩ :
          (PrimeSpectrum.comap (algebraMap R T)) ⁻¹'
            {PrimeSpectrum.comap (algebraMap R T) q}) := by
  -- Convert the ideal-height comparison to the order-height spelling used below.
  calc
    Order.height (fiberPrimeAt R T q) = (fiberPrimeAt R T q).asIdeal.height :=
      (fiberPrimeAt_height_eq_orderHeight (R := R) (T := T) q).symm
    _ =
        Order.height
          (⟨q, rfl⟩ :
            (PrimeSpectrum.comap (algebraMap R T)) ⁻¹'
              {PrimeSpectrum.comap (algebraMap R T) q}) :=
      fiberPrimeAt_height_eq_preimage_height (R := R) (T := T) q

/-- Helper for Chap10 Lemma 10 116 6: the order-height comparison for a fiber prime can be
written over any explicitly equal base point of the raw prime-spectrum fiber. -/
lemma fiberPrimeAt_orderHeight_eq_preimage_height_of_comap_eq
    {R T : Type*} [CommRing R] [CommRing T] [Algebra R T]
    {p : PrimeSpectrum R} (q : PrimeSpectrum T)
    (hq : PrimeSpectrum.comap (algebraMap R T) q = p) :
    Order.height (fiberPrimeAt R T q) =
      Order.height
        (⟨q, hq⟩ : (PrimeSpectrum.comap (algebraMap R T)) ⁻¹' {p}) := by
  -- Replace the chosen base point by the canonical contraction, then reuse the raw-fiber adapter.
  subst p
  simpa using fiberPrimeAt_orderHeight_eq_preimage_height (R := R) (T := T) q

omit [Algebra.FiniteType k S] in
/-- Helper for Chap10 Lemma 10 116 6: a polynomial prime lying over the downstairs presentation
point contains the kernel of the base-changed presentation. -/
lemma tensorProductPresentation_ker_le_of_comap_eq
    {n : ℕ} (π : MvPolynomial (Fin n) k →ₐ[k] S) (hπ : Function.Surjective π)
    (y : PrimeSpectrum (MvPolynomial (Fin n) k))
    (r : PrimeSpectrum (MvPolynomial (Fin n) K))
    (hker_y : RingHom.ker π.toRingHom ≤ y.asIdeal)
    (hr : PrimeSpectrum.comap
        ((MvPolynomial.mapAlgHom (σ := Fin n) (Algebra.ofId k K)).toRingHom) r = y) :
    let πK : MvPolynomial (Fin n) K →ₐ[K] S_K :=
      MvPolynomial.aeval fun i ↦ (1 : K) ⊗ₜ[k] π (MvPolynomial.X i)
    RingHom.ker πK.toRingHom ≤ r.asIdeal := by
  intro πK
  let β : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin n) K :=
    MvPolynomial.mapAlgHom (σ := Fin n) (Algebra.ofId k K)
  have hker :
      RingHom.ker πK.toRingHom = Ideal.map β.toRingHom (RingHom.ker π.toRingHom) := by
    simpa [πK, β] using tensorBaseChangePolynomialAlgHom_ker (K := K) π hπ
  rw [hker, Ideal.map_le_iff_le_comap]
  have hy : y.asIdeal = Ideal.comap β.toRingHom r.asIdeal := by
    simpa [β, PrimeSpectrum.comap_asIdeal] using (congrArg PrimeSpectrum.asIdeal hr).symm
  exact le_trans hker_y hy.le

omit [Algebra.FiniteType k S] in
/-- Helper for Chap10 Lemma 10 116 6: under a surjective presentation, the raw fiber point over
the polynomial base change and the raw fiber point over the quotient have the same order height. -/
lemma tensorProductPresentation_preimageFiber_height_eq
    {n : ℕ} (π : MvPolynomial (Fin n) k →ₐ[k] S) (hπ : Function.Surjective π)
    (x : PrimeSpectrum S) (xK : PrimeSpectrum S_K) (hxK : PrimeSpectrum.comap iSK xK = x) :
    let πK : MvPolynomial (Fin n) K →ₐ[K] S_K :=
      MvPolynomial.aeval fun i ↦ (1 : K) ⊗ₜ[k] π (MvPolynomial.X i)
    let y : PrimeSpectrum (MvPolynomial (Fin n) k) := PrimeSpectrum.comap π.toRingHom x
    let yK : PrimeSpectrum (MvPolynomial (Fin n) K) := PrimeSpectrum.comap πK.toRingHom xK
    let β : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin n) K :=
      MvPolynomial.mapAlgHom (σ := Fin n) (Algebra.ofId k K)
    Order.height
        (⟨yK, tensorBaseChangePolynomialPresentation_comap (K := K) π x xK hxK⟩ :
          (PrimeSpectrum.comap β.toRingHom) ⁻¹' Set.singleton y) =
      Order.height (⟨xK, hxK⟩ : (PrimeSpectrum.comap iSK) ⁻¹' Set.singleton x) := by
  intro πK y yK β
  have hπK : Function.Surjective πK := by
    simpa [πK] using tensorBaseChangePolynomialAlgHom_surjective (K := K) π hπ
  have hker_y : RingHom.ker π.toRingHom ≤ y.asIdeal := by
    intro a ha
    change π.toRingHom a ∈ x.asIdeal
    rw [RingHom.mem_ker.mp ha]
    exact x.asIdeal.zero_mem
  let eQuot := Ideal.primeSpectrumOrderIsoZeroLocusOfSurj πK.toRingHom hπK rfl
  have hQuot_val (s : PrimeSpectrum S_K) :
      (eQuot s).1 = PrimeSpectrum.comap πK.toRingHom s := rfl
  -- The forward map sends a polynomial-fiber prime through the inverse closed embedding.
  let toFun : ((PrimeSpectrum.comap β.toRingHom) ⁻¹' {y}) →
      ((PrimeSpectrum.comap iSK) ⁻¹' {x}) := fun rOver ↦ by
    have hker_r : RingHom.ker πK.toRingHom ≤ rOver.1.asIdeal := by
      simpa [πK, β] using
        tensorProductPresentation_ker_le_of_comap_eq (K := K) (S := S)
          π hπ y rOver.1 hker_y rOver.2
    let s : PrimeSpectrum S_K := eQuot.symm ⟨rOver.1, hker_r⟩
    refine ⟨s, ?_⟩
    have hπK_s : PrimeSpectrum.comap πK.toRingHom s = rOver.1 :=
      congrArg Subtype.val (eQuot.right_inv ⟨rOver.1, hker_r⟩)
    have hcomp : PrimeSpectrum.comap π.toRingHom (PrimeSpectrum.comap iSK s) = y := by
      calc
        PrimeSpectrum.comap π.toRingHom (PrimeSpectrum.comap iSK s) =
            PrimeSpectrum.comap β.toRingHom (PrimeSpectrum.comap πK.toRingHom s) := by
          exact (tensorBaseChangePolynomialPresentation_comap_apply (K := K) π s).symm
        _ = PrimeSpectrum.comap β.toRingHom rOver.1 := by
          rw [hπK_s]
        _ = y := rOver.2
    exact (PrimeSpectrum.comap_injective_of_surjective π.toRingHom hπ) (by simpa [y] using hcomp)
  -- The inverse map is just contraction along the upstairs presentation.
  let invFun : ((PrimeSpectrum.comap iSK) ⁻¹' {x}) →
      ((PrimeSpectrum.comap β.toRingHom) ⁻¹' {y}) := fun sOver ↦ by
    refine ⟨PrimeSpectrum.comap πK.toRingHom sOver.1, ?_⟩
    calc
      PrimeSpectrum.comap β.toRingHom (PrimeSpectrum.comap πK.toRingHom sOver.1) =
          PrimeSpectrum.comap π.toRingHom (PrimeSpectrum.comap iSK sOver.1) :=
        tensorBaseChangePolynomialPresentation_comap_apply (K := K) π sOver.1
      _ = PrimeSpectrum.comap π.toRingHom x := by
        rw [sOver.2]
      _ = y := by
        simp [y]
  have hπK_toFun (rOver : ((PrimeSpectrum.comap β.toRingHom) ⁻¹' {y})) :
      PrimeSpectrum.comap πK.toRingHom (toFun rOver).1 = rOver.1 := by
    dsimp [toFun]
    have hker_r : RingHom.ker πK.toRingHom ≤ rOver.1.asIdeal := by
      simpa [πK, β] using
        tensorProductPresentation_ker_le_of_comap_eq (K := K) (S := S)
          π hπ y rOver.1 hker_y rOver.2
    exact congrArg Subtype.val (eQuot.right_inv ⟨rOver.1, hker_r⟩)
  let eRaw : ((PrimeSpectrum.comap β.toRingHom) ⁻¹' {y}) ≃o
      ((PrimeSpectrum.comap iSK) ⁻¹' {x}) :=
    { toEquiv :=
        { toFun := toFun
          invFun := invFun
          left_inv := by
            intro rOver
            apply Subtype.ext
            exact hπK_toFun rOver
          right_inv := by
            intro sOver
            apply Subtype.ext
            apply PrimeSpectrum.comap_injective_of_surjective πK.toRingHom hπK
            rw [hπK_toFun (invFun sOver)] }
      map_rel_iff' := by
        intro a b
        constructor
        · intro h
          have h' : eQuot (toFun a).1 ≤ eQuot (toFun b).1 := by
            exact (eQuot.map_rel_iff').2 h
          change a.1 ≤ b.1
          change (eQuot (toFun a).1).1 ≤ (eQuot (toFun b).1).1 at h'
          rw [hQuot_val (toFun a).1, hQuot_val (toFun b).1] at h'
          rwa [hπK_toFun a, hπK_toFun b] at h'
        · intro h
          have h' : eQuot (toFun a).1 ≤ eQuot (toFun b).1 := by
            change (eQuot (toFun a).1).1 ≤ (eQuot (toFun b).1).1
            rw [hQuot_val (toFun a).1, hQuot_val (toFun b).1]
            rwa [hπK_toFun a, hπK_toFun b]
          exact (eQuot.map_rel_iff').1 h' }
  let yKOver : ((PrimeSpectrum.comap β.toRingHom) ⁻¹' {y}) :=
    ⟨yK, by
      simpa [πK, y, yK, β] using
        tensorBaseChangePolynomialPresentation_comap (K := K) π x xK hxK⟩
  let xKOver : ((PrimeSpectrum.comap iSK) ⁻¹' {x}) := ⟨xK, hxK⟩
  have hendpoint : eRaw yKOver = xKOver := by
    apply Subtype.ext
    apply PrimeSpectrum.comap_injective_of_surjective πK.toRingHom hπK
    calc
      PrimeSpectrum.comap πK.toRingHom (eRaw yKOver).1 = yKOver.1 :=
        hπK_toFun yKOver
      _ = PrimeSpectrum.comap πK.toRingHom xKOver.1 := rfl
  -- Order isomorphisms preserve the height of the distinguished fiber point.
  calc
    Order.height yKOver = Order.height (eRaw yKOver) :=
      (Order.height_orderIso eRaw yKOver).symm
    _ = Order.height xKOver := by
      rw [hendpoint]

omit [Algebra.FiniteType k S] in
/-- Helper for Chap10 Lemma 10 116 6: the fiber prime above the polynomial presentation and the
fiber prime above the quotient presentation have the same height. -/
lemma tensorProductPresentation_fiberPrimeHeight_eq
    {n : ℕ} (π : MvPolynomial (Fin n) k →ₐ[k] S) (hπ : Function.Surjective π)
    (x : PrimeSpectrum S) (xK : PrimeSpectrum S_K) (hxK : PrimeSpectrum.comap iSK xK = x) :
    let πK : MvPolynomial (Fin n) K →ₐ[K] S_K :=
      MvPolynomial.aeval fun i ↦ (1 : K) ⊗ₜ[k] π (MvPolynomial.X i)
    let yK : PrimeSpectrum (MvPolynomial (Fin n) K) := PrimeSpectrum.comap πK.toRingHom xK
    Order.height (fiberPrimeAt (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) K) yK) =
      Order.height (fiberPrimeAt S S_K xK) := by
  intro πK yK
  let β : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin n) K :=
    MvPolynomial.mapAlgHom (σ := Fin n) (Algebra.ofId k K)
  let y : PrimeSpectrum (MvPolynomial (Fin n) k) := PrimeSpectrum.comap π.toRingHom x
  -- The closed setup lemmas reduce the remaining geometry to a transport-stable order isomorphism
  -- between the two set-theoretic fibers in the surjective presentation square.
  have hπK : Function.Surjective πK := by
    -- The upstairs polynomial presentation is surjective by tensor base change.
    simpa [πK] using tensorBaseChangePolynomialAlgHom_surjective (K := K) π hπ
  have hker : RingHom.ker πK.toRingHom = Ideal.map β.toRingHom (RingHom.ker π.toRingHom) := by
    -- The base-changed presentation kernel is already identified with the extended kernel.
    simpa [πK, β] using tensorBaseChangePolynomialAlgHom_ker (K := K) π hπ
  have hcomap : PrimeSpectrum.comap β.toRingHom yK = y := by
    -- The upstairs polynomial point contracts to the downstairs polynomial point.
    simpa [πK, y, yK, β] using
      tensorBaseChangePolynomialPresentation_comap (K := K) π x xK hxK
  let yKOver : ((PrimeSpectrum.comap β.toRingHom) ⁻¹' {y}) := ⟨yK, hcomap⟩
  let xKOver : ((PrimeSpectrum.comap iSK) ⁻¹' {x}) := ⟨xK, hxK⟩
  have hleft :
      Order.height (fiberPrimeAt (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) K) yK) =
        Order.height yKOver := by
    -- Convert the polynomial fiber prime height to the raw fiber height.
    simpa [yKOver] using
      fiberPrimeAt_orderHeight_eq_preimage_height_of_comap_eq
        (R := MvPolynomial (Fin n) k) (T := MvPolynomial (Fin n) K) yK hcomap
  have hright :
      Order.height (fiberPrimeAt S S_K xK) = Order.height xKOver := by
    -- Convert the quotient fiber prime height to the corresponding raw fiber height.
    simpa [xKOver] using
      fiberPrimeAt_orderHeight_eq_preimage_height_of_comap_eq (R := S) (T := S_K) xK hxK
  have hraw : Order.height yKOver = Order.height xKOver := by
    -- The raw fiber heights agree by the transport-stable interval comparison above.
    simpa [πK, y, yK, β, yKOver, xKOver] using
      tensorProductPresentation_preimageFiber_height_eq (K := K) π hπ x xK hxK
  calc
    Order.height (fiberPrimeAt (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) K) yK) =
        Order.height yKOver := hleft
    _ = Order.height xKOver := hraw
    _ = Order.height (fiberPrimeAt S S_K xK) := hright.symm

/-- Helper for Chap10 Lemma 10 116 6: subtracting two decompositions with a common finite
summand leaves the same `ℕ∞` height defect. -/
lemma enat_sub_eq_sub_of_eq_add_common {x y x' y' c : ℕ∞}
    (hy' : y' = y + c) (hx' : x' = x + c) (hxy : x ≤ y)
    (hx_ne_top : x ≠ ⊤) (hy'_ne_top : y' ≠ ⊤) :
    y' - x' = y - x := by
  -- The top-finiteness hypotheses let us cancel the common summand after decomposing `y`.
  have hc_ne_top : c ≠ ⊤ := by
    intro hc
    apply hy'_ne_top
    calc
      y' = y + c := hy'
      _ = ⊤ := by
        rw [hc]
        simp
  have hxc_ne_top : x + c ≠ ⊤ := by
    have hx_lt_top : x < ⊤ := (lt_top_iff_ne_top).2 hx_ne_top
    have hc_lt_top : c < ⊤ := (lt_top_iff_ne_top).2 hc_ne_top
    exact (lt_top_iff_ne_top).1 ((ENat.add_lt_top).2 ⟨hx_lt_top, hc_lt_top⟩)
  have hdecomp : y + c = (y - x) + (x + c) := by
    calc
      y + c = (y - x + x) + c := by
        rw [tsub_add_cancel_of_le hxy]
      _ = (y - x) + (x + c) := by
        ac_rfl
  rw [hy', hx']
  exact AddLECancellable.tsub_eq_of_eq_add
    (ENat.addLECancellable_of_ne_top hxc_ne_top) hdecomp

omit [Algebra.FiniteType k S] in
/-- Helper for Chap10 Lemma 10 116 6: the base-changed polynomial prime height decomposes as the
height of its contraction plus the common fiber height. -/
lemma tensorProductPresentation_polynomial_height_eq_add_commonFiber
    {n : ℕ} (π : MvPolynomial (Fin n) k →ₐ[k] S)
    (x : PrimeSpectrum S) (xK : PrimeSpectrum S_K) (hxK : PrimeSpectrum.comap iSK xK = x) :
    let πK : MvPolynomial (Fin n) K →ₐ[K] S_K :=
      MvPolynomial.aeval fun i ↦ (1 : K) ⊗ₜ[k] π (MvPolynomial.X i)
    let y : PrimeSpectrum (MvPolynomial (Fin n) k) := PrimeSpectrum.comap π.toRingHom x
    let yK : PrimeSpectrum (MvPolynomial (Fin n) K) := PrimeSpectrum.comap πK.toRingHom xK
    yK.asIdeal.height = y.asIdeal.height +
      (fiberPrimeAt (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) K) yK).asIdeal.height := by
  intro πK y yK
  let β : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin n) K :=
    MvPolynomial.mapAlgHom (σ := Fin n) (Algebra.ofId k K)
  letI : IsNoetherianRing (MvPolynomial (Fin n) k) := inferInstance
  letI : IsNoetherianRing (MvPolynomial (Fin n) K) := inferInstance
  letI : Module.Flat (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) K) :=
    mvPolynomialFieldExtension_moduleFlat (k := k) (K := K) (n := n)
  letI : Algebra.HasGoingDown (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) K) :=
    Algebra.HasGoingDown.of_flat
  have hcomap : PrimeSpectrum.comap β.toRingHom yK = y := by
    -- The polynomial base-change square gives the contraction of the upstairs polynomial point.
    simpa [πK, y, yK, β] using
      tensorBaseChangePolynomialPresentation_comap (K := K) π x xK hxK
  exact height_eq_comap_add_fiberPrimeHeight_of_hasGoingDown
    (R := MvPolynomial (Fin n) k) (T := MvPolynomial (Fin n) K) yK hcomap

/-- Helper for Chap10 Lemma 10 116 6: the quotient prime height decomposes with the same fiber
height as the polynomial presentation. -/
lemma tensorProductPresentation_quotient_height_eq_add_commonFiber
    {n : ℕ} (π : MvPolynomial (Fin n) k →ₐ[k] S) (hπ : Function.Surjective π)
    (x : PrimeSpectrum S) (xK : PrimeSpectrum S_K) (hxK : PrimeSpectrum.comap iSK xK = x) :
    let πK : MvPolynomial (Fin n) K →ₐ[K] S_K :=
      MvPolynomial.aeval fun i ↦ (1 : K) ⊗ₜ[k] π (MvPolynomial.X i)
    let yK : PrimeSpectrum (MvPolynomial (Fin n) K) := PrimeSpectrum.comap πK.toRingHom xK
    xK.asIdeal.height = x.asIdeal.height +
      (fiberPrimeAt (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) K) yK).asIdeal.height := by
  intro πK yK
  letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  letI : Algebra.FiniteType K S_K := inferInstance
  letI : IsNoetherianRing S_K := Algebra.FiniteType.isNoetherianRing K S_K
  letI : Module.Flat S S_K := tensorProductIncludeRight_moduleFlat (K := K) S
  letI : Algebra.HasGoingDown S S_K := Algebra.HasGoingDown.of_flat
  have hfiberOrder :
      Order.height (fiberPrimeAt (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) K) yK) =
        Order.height (fiberPrimeAt S S_K xK) := by
    -- Convert the presentation fiber comparison to the ideal-height spelling needed here.
    simpa [πK, yK] using
      tensorProductPresentation_fiberPrimeHeight_eq (K := K) π hπ x xK hxK
  have hfiberIdeal := fiberPrimeAt_asIdeal_height_eq_of_orderHeight_eq hfiberOrder
  have hquotBase :=
    height_eq_comap_add_fiberPrimeHeight_of_hasGoingDown (R := S) (T := S_K) xK hxK
  exact hquotBase.trans (by rw [← hfiberIdeal])

/-- Helper for Chap10 Lemma 10 116 6: the height defect in a polynomial presentation is unchanged
after tensoring the presentation with the field extension. -/
lemma tensorProductPresentation_heightSub_eq
    {n : ℕ} (π : MvPolynomial (Fin n) k →ₐ[k] S) (hπ : Function.Surjective π)
    (x : PrimeSpectrum S) (xK : PrimeSpectrum S_K) (hxK : PrimeSpectrum.comap iSK xK = x) :
    let πK : MvPolynomial (Fin n) K →ₐ[K] S_K :=
      MvPolynomial.aeval fun i ↦ (1 : K) ⊗ₜ[k] π (MvPolynomial.X i)
    let y : PrimeSpectrum (MvPolynomial (Fin n) k) := PrimeSpectrum.comap π.toRingHom x
    let yK : PrimeSpectrum (MvPolynomial (Fin n) K) := PrimeSpectrum.comap πK.toRingHom xK
    yK.asIdeal.height - xK.asIdeal.height = y.asIdeal.height - x.asIdeal.height := by
  intro πK y yK
  let β : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin n) K :=
    MvPolynomial.mapAlgHom (σ := Fin n) (Algebra.ofId k K)
  letI : IsNoetherianRing (MvPolynomial (Fin n) K) := inferInstance
  letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  have hpoly : yK.asIdeal.height = y.asIdeal.height +
      (fiberPrimeAt (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) K) yK).asIdeal.height := by
    -- The polynomial side of the square has the standard going-down height decomposition.
    simpa [πK, y, yK, β] using
      tensorProductPresentation_polynomial_height_eq_add_commonFiber (K := K) π x xK hxK
  have hquot : xK.asIdeal.height = x.asIdeal.height +
      (fiberPrimeAt (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) K) yK).asIdeal.height := by
    -- The quotient side has the same fiber-height summand by the presentation comparison.
    simpa [πK, y, yK, β] using
      tensorProductPresentation_quotient_height_eq_add_commonFiber (K := K) π hπ x xK hxK
  have hx_le_y : x.asIdeal.height ≤ y.asIdeal.height := by
    simpa [Ideal.height_eq_primeHeight, Ideal.primeHeight, y] using
      (Order.height_le_height_apply_of_strictMono
        (PrimeSpectrum.comap π.toRingHom)
        (RingHom.strictMono_comap_of_surjective hπ)
        x)
  have hyK_ne_top : yK.asIdeal.height ≠ ⊤ :=
    Ideal.height_ne_top (Ideal.IsPrime.ne_top (PrimeSpectrum.isPrime yK))
  have hx_ne_top : x.asIdeal.height ≠ ⊤ :=
    Ideal.height_ne_top (Ideal.IsPrime.ne_top (PrimeSpectrum.isPrime x))
  -- Apply the finite `ℕ∞` cancellation lemma to the two aligned decompositions.
  exact enat_sub_eq_sub_of_eq_add_common hpoly hquot hx_le_y hx_ne_top hyK_ne_top

/-- Helper for Chap10 Lemma 10 116 6: the two polynomial presentations have the same finite
height defect at corresponding primes after tensor base change. -/
lemma commonHeightDefect_of_tensorProductPresentation
    {n : ℕ} (π : MvPolynomial (Fin n) k →ₐ[k] S) (hπ : Function.Surjective π)
    (x : PrimeSpectrum S) (xK : PrimeSpectrum S_K) (hxK : PrimeSpectrum.comap iSK xK = x) :
    let πK : MvPolynomial (Fin n) K →ₐ[K] S_K :=
      MvPolynomial.aeval fun i ↦ (1 : K) ⊗ₜ[k] π (MvPolynomial.X i)
    let y : PrimeSpectrum (MvPolynomial (Fin n) k) := PrimeSpectrum.comap π.toRingHom x
    let yK : PrimeSpectrum (MvPolynomial (Fin n) K) := PrimeSpectrum.comap πK.toRingHom xK
    ∃ d : ℕ,
      (((y.asIdeal.height - x.asIdeal.height : ℕ∞) : WithBot ℕ∞)) = d ∧
        (((yK.asIdeal.height - xK.asIdeal.height : ℕ∞) : WithBot ℕ∞)) = d :=
  by
  intro πK y yK
  have hdefEq : yK.asIdeal.height - xK.asIdeal.height = y.asIdeal.height - x.asIdeal.height := by
    -- The geometric helper isolates the presentation comparison from the finite-defect packaging.
    simpa [πK, y, yK] using
      tensorProductPresentation_heightSub_eq (K := K) π hπ x xK hxK
  let d : ℕ := (y.asIdeal.height - x.asIdeal.height).toNat
  have hy_ne_top : y.asIdeal.height ≠ ⊤ :=
    Ideal.height_ne_top (Ideal.IsPrime.ne_top (PrimeSpectrum.isPrime y))
  have hdef_ne_top : y.asIdeal.height - x.asIdeal.height ≠ ⊤ :=
    ne_top_of_le_ne_top hy_ne_top tsub_le_self
  refine ⟨d, ?_, ?_⟩
  · -- The downstairs defect is finite because it is bounded by the finite polynomial height.
    exact_mod_cast (ENat.coe_toNat hdef_ne_top).symm
  · -- The upstairs defect is the same `ℕ∞` value, hence has the same natural representative.
    calc
      (((yK.asIdeal.height - xK.asIdeal.height : ℕ∞) : WithBot ℕ∞)) =
          (((y.asIdeal.height - x.asIdeal.height : ℕ∞) : WithBot ℕ∞)) := by
        rw [hdefEq]
      _ = d := by
        exact_mod_cast (ENat.coe_toNat hdef_ne_top).symm

/- 
Domain-style sampling:
- primary domain: local Krull dimension on `Spec(S)` for finite type algebras over a field, under
  tensor base change along a field extension;
- sampled owner declarations of the same kind:
  `topologicalKrullDimAt`,
  `topologicalKrullDimAt_eq_ringKrullDim_localizationAtPrime_add_trdeg_residueField`,
  `ringKrullDim_localizationAtPrime_eq_ringKrullDim_localizationAtPrime_under_add_ringKrullDim_fiberLocalRingAt_of_hasGoingDown`,
  `topologicalKrullDimAt_comap_eq_add_height_sub_of_surjective_of_finiteType_over_field`;
- best owner abstraction: the source-facing theorem should remain an equality between the canonical
  local-dimension owner values `topologicalKrullDimAt x` and `topologicalKrullDimAt xK`, while the
  supporting local-ring/fiber calculations are already owned upstream by `Localization.AtPrime`,
  `fiberLocalRingAt`, and the dimension formulas in Lemmas `10.112.7`, `10.116.3`, and `10.116.4`;
- primitive data: only the point `x : PrimeSpectrum S`, the point `xK : PrimeSpectrum S_K`, and
  the canonical contraction witness `hxK : PrimeSpectrum.comap iSK xK = x`;
- derived API: any quotient-presentation or localization comparison used in the proof. No extra
  public wrapper or duplicate local owner should be introduced here.

Source/core/bridge triage:
* `source-facing`: the invariance of `topologicalKrullDimAt` under tensoring a finite type
  `k`-algebra with a field extension `K / k`;
* `core/canonical`: `topologicalKrullDimAt`, `Localization.AtPrime`, `fiberLocalRingAt`, and the
  local dimension formulas from Lemmas `10.112.7`, `10.116.3`, and `10.116.4`;
* `bridge/view`: the tensor base-change morphism `iSK` and the induced prime-spectrum contraction
  equation `PrimeSpectrum.comap iSK xK = x`.
-/

-- Proof sketch: present `S` as a quotient of a polynomial ring over `k`, base change that
-- presentation to `K`, and compare the height differences given by Lemma `10.112.7` for the two
-- vertical flat maps in the resulting square of local rings. Then use the local-dimension formula
-- from Lemma `10.116.4` for the quotient presentations upstairs and downstairs to cancel the same
-- ambient polynomial-ring dimension.
/-- Chap10 Lemma 10 116 6: if `S` is a finite type `k`-algebra, `x : Spec(S)` corresponds to a prime of
`S`, and `xK : Spec(K ⊗[k] S)` corresponds to a prime of `K ⊗[k] S` lying over `x`, then the
local topological Krull dimensions at `x` and `xK` are equal. -/
@[stacks 00P4]
lemma primeSpectrumTopologicalKrullDimAt_eq_of_tensorProduct_fieldExtension
    (x : PrimeSpectrum S) (xK : PrimeSpectrum S_K) (hxK : PrimeSpectrum.comap iSK xK = x) :
    topologicalKrullDimAt x = topologicalKrullDimAt xK := by
  -- Choose a finite polynomial presentation of `S`, then base change it to a presentation of
  -- `K ⊗[k] S`; the remaining missing comparison is the height-defect equality in this square.
  obtain ⟨n, π, hπ⟩ :=
    (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := k) (S := S)).mp inferInstance
  let πK : MvPolynomial (Fin n) K →ₐ[K] S_K :=
    MvPolynomial.aeval fun i ↦ (1 : K) ⊗ₜ[k] π (MvPolynomial.X i)
  let y : PrimeSpectrum (MvPolynomial (Fin n) k) := PrimeSpectrum.comap π.toRingHom x
  let yK : PrimeSpectrum (MvPolynomial (Fin n) K) := PrimeSpectrum.comap πK.toRingHom xK
  have hπK : Function.Surjective πK := by
    -- The tensor-base-change presentation is surjective by the adapter lemma above.
    simpa [πK] using tensorBaseChangePolynomialAlgHom_surjective (K := K) π hπ
  have hy : topologicalKrullDimAt y = (n : WithBot ℕ∞) := by
    -- Affine `n`-space over the base field has local dimension `n` at every point.
    simpa [y] using topologicalKrullDimAt_mvPolynomial_eq_nat (F := k) n y
  have hyK : topologicalKrullDimAt yK = (n : WithBot ℕ∞) := by
    -- The same affine-space computation applies after base change to `K`.
    simpa [yK] using topologicalKrullDimAt_mvPolynomial_eq_nat (F := K) n yK
  have hdown :=
    topologicalKrullDimAt_comap_eq_add_height_sub_of_surjective_of_finiteType_over_field
      (k := k) (S' := MvPolynomial (Fin n) k) (S := S) π hπ x
  have hup :=
    topologicalKrullDimAt_comap_eq_add_height_sub_of_surjective_of_finiteType_over_field
      (k := K) (S' := MvPolynomial (Fin n) K) (S := S_K) πK hπK xK
  obtain ⟨d, hdef, hdefK⟩ :=
    commonHeightDefect_of_tensorProductPresentation (K := K) π hπ x xK hxK
  have hdown' : (n : WithBot ℕ∞) = topologicalKrullDimAt x + (d : WithBot ℕ∞) := by
    -- Rewrite the downstairs presentation formula using the common finite height defect.
    calc
      (n : WithBot ℕ∞) = topologicalKrullDimAt y := hy.symm
      _ = topologicalKrullDimAt x +
          (((y.asIdeal.height - x.asIdeal.height : ℕ∞) : WithBot ℕ∞)) := by
            simpa [y] using hdown
      _ = topologicalKrullDimAt x + (d : WithBot ℕ∞) := by
            rw [hdef]
  have hup' : (n : WithBot ℕ∞) = topologicalKrullDimAt xK + (d : WithBot ℕ∞) := by
    -- The upstairs formula has the same finite defect by the comparison helper.
    calc
      (n : WithBot ℕ∞) = topologicalKrullDimAt yK := hyK.symm
      _ = topologicalKrullDimAt xK +
          (((yK.asIdeal.height - xK.asIdeal.height : ℕ∞) : WithBot ℕ∞)) := by
            simpa [yK] using hup
      _ = topologicalKrullDimAt xK + (d : WithBot ℕ∞) := by
            rw [hdefK]
  have hcancel :
      topologicalKrullDimAt x + (d : WithBot ℕ∞) =
        topologicalKrullDimAt xK + (d : WithBot ℕ∞) :=
    hdown'.symm.trans hup'
  -- Cancel the shared finite defect to obtain equality of the two local dimensions.
  exact ENat.WithBot.add_natCast_cancel.mp hcancel

end
