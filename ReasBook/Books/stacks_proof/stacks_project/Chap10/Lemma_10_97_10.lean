import Mathlib
import StacksProject_2024.Chap10.Lemma_10_20_1_Nakayama_s_lemma
import StacksProject_2024.Chap10.Lemma_10_96_1
import StacksProject_2024.Chap10.Lemma_10_96_8
import StacksProject_2024.Chap10.Lemma_10_96_12
import StacksProject_2024.Chap10.Lemma_10_97_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable {I J : Ideal A}

/-
Domain triage:
- primary domain: adic completeness for Noetherian rings, together with quotient comparison for
  the image ideal on `A ⧸ I`;
- sampled owner-style declarations in this domain:
  `IsAdicComplete`,
  `isAdicComplete_of_le_of_fg`,
  `moduleFinite_of_finite_quotient_of_isHausdorff`,
  `adicCompletion_algebraMap_flat`;
- best owner abstraction: the completeness predicate `IsAdicComplete` on the ring/module owner,
  with `AdicCompletion (I + J) A` as the canonical auxiliary completion object;
- primitive data: the ideals `I`, `J`, the `I`-adic completeness of `A`, and the completeness of
  `A ⧸ I` for the image ideal `J.map (Ideal.Quotient.mk I)`;
- derived API: completeness for the stronger ideal `I + J`, then the final `J`-adic completeness
  recovered by weakening along `J ≤ I + J`.

Layer classification:
- `source-facing`: the theorem below, which matches the textbook propagation statement for adic
  completeness;
- `core/canonical`: `IsAdicComplete` and the completion ring `AdicCompletion (I + J) A`;
- `bridge/view`: the quotient comparison identifying the mod-`I` reduction of the `(I + J)`-adic
  completion with the `J.map (Ideal.Quotient.mk I)`-adic completion of `A ⧸ I`.
-/

-- Proof sketch: let `B := AdicCompletion (I + J) A`. Since `A` is Noetherian, `I` is finitely
-- generated, so `B` is `I`-adically complete by weakening along `I ≤ I + J`. Lemma `10.97.2`
-- identifies `B ⧸ IB` with the `J`-adic completion of `A ⧸ I`, hence with `A ⧸ I` by the quotient
-- hypothesis. Then Lemma `10.96.12` and Nakayama make `A → B` surjective; flatness of the
-- completion map and the Jacobson-radical argument force injectivity. Thus `A ≃ B`, so `A` is
-- `(I + J)`-adically complete, hence `J`-adically complete by Lemma `10.96.8`.
/-- Helper for Lemma 10.97.10: modulo `I`, the image of `I + J` is just the image of `J`. -/
lemma sup_map_quotient_mk_eq :
    (I ⊔ J).map (Ideal.Quotient.mk I) = J.map (Ideal.Quotient.mk I) := by
  -- The `I`-part dies in the quotient, so only the `J`-part survives.
  rw [Ideal.map_sup, Ideal.map_mk_eq_bot_of_le (show I ≤ I by rfl), bot_sup_eq]

/-- Helper for Lemma 10.97.10: the quotient hypothesis can be read as completeness for the image
of `I + J`. -/
lemma quotient_isAdicComplete_sup_map
    (hquot : IsAdicComplete (J.map (Ideal.Quotient.mk I)) (A ⧸ I)) :
    IsAdicComplete ((I ⊔ J).map (Ideal.Quotient.mk I)) (A ⧸ I) := by
  -- Rewrite the quotient ideal into the shape coming from `I + J`.
  rw [sup_map_quotient_mk_eq]
  exact hquot

/-- Helper for Lemma 10.97.10: `I` lies in the Jacobson radical of an `I`-adically complete
ring. -/
lemma ideal_le_ring_jacobson_of_isAdicComplete
    (hA : IsAdicComplete I A) :
    I ≤ Ring.jacobson A := by
  let _ : IsAdicComplete I A := hA
  -- This is the canonical Jacobson-radical consequence of adic completeness.
  simpa [Ideal.jacobson_bot] using (IsAdicComplete.le_jacobson_bot (I := I) (R := A))

/-- Helper for Lemma 10.97.10: quotienting the `K`-adic completion by the extended ideal `I`
matches the `K`-adic completion of `A ⧸ I` as an `A`-module. -/
noncomputable def completionQuotient_moduleCompletion_linearEquiv (K I : Ideal A) :
    (AdicCompletion K A ⧸ Ideal.map (algebraMap A (AdicCompletion K A)) I) ≃ₗ[AdicCompletion K A]
      AdicCompletion K (A ⧸ I) :=
  (Algebra.TensorProduct.quotIdealMapEquivTensorQuot
      (A := A) (B := AdicCompletion K A) I).toLinearEquiv.trans <|
    AdicCompletion.ofTensorProductEquivOfFiniteNoetherian (I := K) (M := A ⧸ I)

/-- Helper for Lemma 10.97.10: on a source representative `a : A`, the quotient-to-completion
comparison sends the class of `algebraMap A B a` to the completed quotient class of `a`. -/
lemma completionQuotient_moduleCompletion_linearEquiv_mk
    (K I : Ideal A) (a : A) :
    completionQuotient_moduleCompletion_linearEquiv (A := A) K I
        (Submodule.Quotient.mk
          (p := (Ideal.map (algebraMap A (AdicCompletion K A)) I : Ideal (AdicCompletion K A)))
          (algebraMap A (AdicCompletion K A) a)) =
      AdicCompletion.of K (A ⧸ I) (Ideal.Quotient.mk I a) := by
  -- Route correction: compute the bridge on quotient representatives first, then recover the
  -- transported square by quotient extensionality.
  -- The tensor-quotient comparison turns the quotient class into a pure tensor.
  rw [completionQuotient_moduleCompletion_linearEquiv, LinearEquiv.trans_apply]
  change
    AdicCompletion.ofTensorProductEquivOfFiniteNoetherian K (A ⧸ I)
        ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot (AdicCompletion K A) I)
          (Ideal.Quotient.mk (Ideal.map (algebraMap A (AdicCompletion K A)) I)
            (algebraMap A (AdicCompletion K A) a))) =
      AdicCompletion.of K (A ⧸ I) (Ideal.Quotient.mk I a)
  rw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk,
    AdicCompletion.ofTensorProductEquivOfFiniteNoetherian_apply,
    AdicCompletion.ofTensorProduct_tmul]
  -- The remaining step is just `A`-linearity of the canonical completion map on the quotient.
  change a • (AdicCompletion.of K (A ⧸ I)) 1 =
    (AdicCompletion.of K (A ⧸ I)) ((Ideal.Quotient.mk I) a)
  calc
    a • (AdicCompletion.of K (A ⧸ I)) 1 =
        (AdicCompletion.of K (A ⧸ I)) (a • (1 : A ⧸ I)) := by
          rw [← (AdicCompletion.of K (A ⧸ I)).map_smul a (1 : A ⧸ I)]
    _ = (AdicCompletion.of K (A ⧸ I)) ((Ideal.Quotient.mk I) a) := by
          congr 1
          change (Ideal.Quotient.mk I a) * (1 : A ⧸ I) = Ideal.Quotient.mk I a
          simp

/-- Helper for Lemma 10.97.10: after transporting the quotient `B / IB` to the module completion
of `A ⧸ I`, the induced map modulo `I` is exactly the canonical completion map. -/
lemma completionQuotient_moduleCompletion_linearEquiv_comp_quotientMapByIdeal
    (K I : Ideal A) :
    let B := AdicCompletion K A
    let e₁ :
        (A ⧸ (I • (⊤ : Submodule A A))) ≃ₗ[A] (A ⧸ I) :=
      Submodule.quotEquivOfEq _ _ (by simpa using (Ideal.smul_top_eq_map (R := A) (S := A) I))
    let e₂ :
        (B ⧸ (I • (⊤ : Submodule A B))) ≃ₗ[A]
          (B ⧸ Submodule.restrictScalars A (Ideal.map (algebraMap A B) I)) :=
      Submodule.quotEquivOfEq _ _ (by simp [Ideal.smul_top_eq_map])
    let e₃ :
        (B ⧸ Submodule.restrictScalars A (Ideal.map (algebraMap A B) I)) ≃ₗ[A]
          AdicCompletion K (A ⧸ I) :=
      (completionQuotient_moduleCompletion_linearEquiv (A := A) K I).restrictScalars A
    e₃.toLinearMap.comp
        (e₂.toLinearMap.comp ((Algebra.linearMap A B).quotientMapByIdeal I)) =
      (AdicCompletion.of K (A ⧸ I)).restrictScalars A ∘ₗ e₁.toLinearMap := by
  let B := AdicCompletion K A
  let e₁ :
      (A ⧸ (I • (⊤ : Submodule A A))) ≃ₗ[A] (A ⧸ I) :=
    Submodule.quotEquivOfEq _ _ (by simpa using (Ideal.smul_top_eq_map (R := A) (S := A) I))
  let e₂ :
      (B ⧸ (I • (⊤ : Submodule A B))) ≃ₗ[A]
        (B ⧸ Submodule.restrictScalars A (Ideal.map (algebraMap A B) I)) :=
    Submodule.quotEquivOfEq _ _ (by simp [Ideal.smul_top_eq_map])
  let e₃ :
      (B ⧸ Submodule.restrictScalars A (Ideal.map (algebraMap A B) I)) ≃ₗ[A]
        AdicCompletion K (A ⧸ I) :=
    (completionQuotient_moduleCompletion_linearEquiv (A := A) K I).restrictScalars A
  -- Re-express the statement with concrete local names so the representative computation matches.
  change e₃.toLinearMap.comp
      (e₂.toLinearMap.comp ((Algebra.linearMap A B).quotientMapByIdeal I)) =
    (AdicCompletion.of K (A ⧸ I)).restrictScalars A ∘ₗ e₁.toLinearMap
  -- Check the transported square on quotient representatives and then extend to the quotient.
  apply Submodule.linearMap_qext
  apply DFunLike.ext
  intro a
  -- Each quotient transport is definitionally the identity on `Submodule.Quotient.mk a`.
  change
    e₃ (e₂ (Submodule.Quotient.mk (p := (I • (⊤ : Submodule A B))) (algebraMap A B a))) =
      (AdicCompletion.of K (A ⧸ I)).restrictScalars A
        (e₁ (Submodule.Quotient.mk (p := (I • (⊤ : Submodule A A))) a))
  simpa [e₁, e₂, e₃] using completionQuotient_moduleCompletion_linearEquiv_mk (A := A) K I a

/-- Helper for Lemma 10.97.10: if `A ⧸ I` is complete for the image of `K`, then the induced map
`A / IA → B / IB` is bijective for `B = AdicCompletion K A`. -/
lemma completion_quotientMapByIdeal_bijective_of_quotient_isAdicComplete
    (K I : Ideal A)
    (hquotK : IsAdicComplete (K.map (Ideal.Quotient.mk I)) (A ⧸ I)) :
    let B := AdicCompletion K A
    Function.Bijective ((Algebra.linearMap A B).quotientMapByIdeal I) := by
  let B := AdicCompletion K A
  let e₁ :
      (A ⧸ (I • (⊤ : Submodule A A))) ≃ₗ[A] (A ⧸ I) :=
    Submodule.quotEquivOfEq _ _ (by simpa using (Ideal.smul_top_eq_map (R := A) (S := A) I))
  let e₂ :
      (B ⧸ (I • (⊤ : Submodule A B))) ≃ₗ[A]
        (B ⧸ Submodule.restrictScalars A (Ideal.map (algebraMap A B) I)) :=
    Submodule.quotEquivOfEq _ _ (by simp [Ideal.smul_top_eq_map])
  let e₃ :
      (B ⧸ Submodule.restrictScalars A (Ideal.map (algebraMap A B) I)) ≃ₗ[A]
        AdicCompletion K (A ⧸ I) :=
    (completionQuotient_moduleCompletion_linearEquiv (A := A) K I).restrictScalars A
  have hquotA : IsAdicComplete K (A ⧸ I) := by
    -- Read the quotient hypothesis back over the source ring `A`.
    exact (IsAdicComplete.map_algebraMap_iff
      (R := A) (S := A ⧸ I) (I := K) (M := A ⧸ I)).1 hquotK
  have hcomp :
      Function.Bijective
        (e₃.toLinearMap.comp (e₂.toLinearMap.comp ((Algebra.linearMap A B).quotientMapByIdeal I))) := by
    -- The transported quotient map is the canonical completion map of `A ⧸ I`.
    rw [completionQuotient_moduleCompletion_linearEquiv_comp_quotientMapByIdeal (A := A) K I]
    simpa using ((AdicCompletion.of_bijective_iff).2 hquotA).comp e₁.bijective
  refine ⟨?_, ?_⟩
  · -- Injectivity descends from the conjugated bijective map because `e₂` and `e₃` are equivalences.
    intro x y hxy
    apply hcomp.1
    simpa [LinearMap.comp_apply, hxy]
  · -- Surjectivity is obtained by solving for the image after applying the two target equivalences.
    intro y
    obtain ⟨x, hx⟩ := hcomp.2 (e₃ (e₂ y))
    refine ⟨x, ?_⟩
    apply e₂.injective
    apply e₃.injective
    simpa [LinearMap.comp_apply] using hx

/-- Lemma 10.97.10: if `A` is Noetherian, `A` is `I`-adically complete, and the quotient `A ⧸ I`
is complete for the adic topology defined by the image of `J`, then `A` is `J`-adically
complete. -/
@[stacks 0DYC]
theorem isAdicComplete_of_quotient_isAdicComplete_of_isAdicComplete
    (hA : IsAdicComplete I A)
    (hquot : IsAdicComplete (J.map (Ideal.Quotient.mk I)) (A ⧸ I)) :
    IsAdicComplete J A := by
  let K : Ideal A := I ⊔ J
  let B := AdicCompletion K A
  have hIjac : I ≤ Ring.jacobson A :=
    ideal_le_ring_jacobson_of_isAdicComplete (I := I) hA
  have hquotK : IsAdicComplete (K.map (Ideal.Quotient.mk I)) (A ⧸ I) := by
    -- The quotient-completion comparison should use `K = I + J` rather than `J` directly.
    simpa [K, sup_map_quotient_mk_eq] using quotient_isAdicComplete_sup_map (I := I) (J := J) hquot
  have hKfg : K.FG := K.fg_of_isNoetherianRing
  have hIfg : I.FG := I.fg_of_isNoetherianRing
  have hJfg : J.FG := J.fg_of_isNoetherianRing
  have hJleK : J ≤ K := by
    exact le_sup_right
  have hKCompleteB : IsAdicComplete K B := AdicCompletion.isAdicComplete hKfg
  have hICompleteB : IsAdicComplete I B := by
    -- Restrict completeness on `B` from the stronger ideal `K` back to `I`.
    exact isAdicComplete_of_le_of_fg (show I ≤ K by exact le_sup_left) hIfg hKCompleteB
  letI : IsHausdorff I B := hICompleteB.toIsHausdorff
  have hquotBij :
      Function.Bijective ((Algebra.linearMap A B).quotientMapByIdeal I) := by
    -- This is the source proof's quotient bridge `B / IB ≃ completion(A / I)`.
    simpa [B] using
      completion_quotientMapByIdeal_bijective_of_quotient_isAdicComplete
        (A := A) K I hquotK
  have hfiniteDom : Module.Finite A (A ⧸ (I • (⊤ : Submodule A A))) := by
    -- The source quotient is generated by the class of `1`.
    exact Module.Finite.of_surjective
      (Submodule.mkQ (I • (⊤ : Submodule A A))) (Submodule.mkQ_surjective _)
  have hfiniteQuot : Module.Finite A (B ⧸ (I • (⊤ : Submodule A B))) := by
    -- Surjectivity of the induced quotient map transports finite generation to `B / IB`.
    exact Module.Finite.of_surjective ((Algebra.linearMap A B).quotientMapByIdeal I)
      hquotBij.surjective
  letI : Module.Finite A (B ⧸ (I • (⊤ : Submodule A B))) := hfiniteQuot
  have hfiniteB : Module.Finite A B := by
    -- Lemma `10.96.12` upgrades finite generation of `B / IB` to finite generation of `B`.
    letI : Module.Finite (A ⧸ I) (B ⧸ (I • (⊤ : Submodule A B))) :=
      Module.Finite.of_restrictScalars_finite A (A ⧸ I) (B ⧸ (I • (⊤ : Submodule A B)))
    exact moduleFinite_of_finite_quotient_of_isHausdorff (I := I) (R := A) (M := B)
  letI : Module.Finite A B := hfiniteB
  have hsurj : Function.Surjective (algebraMap A B) := by
    -- Source step: Nakayama applied to the completion map modulo `I`.
    exact surjective_of_quotientMap_surjective_of_le_ring_jacobson
      (I := I) (g := Algebra.linearMap A B) hquotBij.surjective hIjac
  have hflatRing : (algebraMap A B).Flat := by
    simpa [B] using adicCompletion_algebraMap_flat (I := K) (R := A)
  letI : Module.Flat A B := by
    rw [RingHom.flat_algebraMap_iff] at hflatRing
    exact hflatRing
  let L : Ideal A := RingHom.ker (algebraMap A B)
  have hker_le_I : L ≤ I := by
    -- Injectivity modulo `I` shows that any element killed in the completion already lies in `I`.
    intro a ha
    have hzero :
        ((Algebra.linearMap A B).quotientMapByIdeal I)
            (Submodule.Quotient.mk (p := (I • (⊤ : Submodule A A))) a) = 0 := by
      change
        (Submodule.Quotient.mk (p := (I • (⊤ : Submodule A B))) (algebraMap A B a) :
          B ⧸ (I • (⊤ : Submodule A B))) = 0
      rw [RingHom.mem_ker.mp ha, Submodule.Quotient.mk_eq_zero]
      exact Submodule.zero_mem _
    have hmkzero :
        (Submodule.Quotient.mk (p := (I • (⊤ : Submodule A A))) a :
          A ⧸ (I • (⊤ : Submodule A A))) = 0 :=
      hquotBij.injective hzero
    exact by
      have : a ∈ I * ⊤ := Ideal.Quotient.eq_zero_iff_mem.mp hmkzero
      simpa using this
  have hKerQuotInj :
      Function.Injective (((L : Submodule A A).subtype).quotientMapByIdeal L) := by
    -- Flatness keeps the kernel sequence exact after reduction modulo the kernel ideal itself.
    exact quotientMapByIdeal_injective_of_exact_of_flat
      (R := A) (J := L) (φ := (L : Submodule A A).subtype) (ψ := Algebra.linearMap A B)
      Subtype.coe_injective hsurj (Algebra.linearMap A B).exact_subtype_ker_map
  letI : Module.Finite A L := Module.Finite.of_injective (L : Submodule A A).subtype
    Subtype.coe_injective
  have hLsmulTop : L • (⊤ : Submodule A L) = ⊤ := by
    -- Since the reduced inclusion `L / L² → A / L` is both injective and zero, the quotient vanishes.
    apply top_unique
    intro x hx
    have hxzero :
        (Submodule.Quotient.mk (p := (L • (⊤ : Submodule A L))) x :
          L ⧸ (L • (⊤ : Submodule A L))) = 0 := by
      apply hKerQuotInj
      change
        (Submodule.Quotient.mk (p := (L • (⊤ : Submodule A A))) ((L : Submodule A A).subtype x) :
          A ⧸ (L • (⊤ : Submodule A A))) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      simpa using Submodule.smul_mem_smul x.property (Submodule.mem_top : (1 : A) ∈ (⊤ : Submodule A A))
    exact by simpa using hxzero
  have hIsmulTop : I • (⊤ : Submodule A L) = ⊤ := by
    -- The kernel lies in `I`, so `L = L²` upgrades to `L = IL`.
    have hLI :
        L • (⊤ : Submodule A L) ≤ I • (⊤ : Submodule A L) :=
      Submodule.smul_mono hker_le_I (show (⊤ : Submodule A L) ≤ ⊤ by exact le_rfl)
    exact top_unique (by simpa [hLsmulTop] using hLI)
  have hLsubsingleton : Subsingleton L := by
    -- A second Nakayama application kills the finite kernel inside the Jacobson radical.
    exact subsingleton_of_ideal_smul_top_eq_top_of_le_ring_jacobson
      (I := I) (R := A) (M := L) hIsmulTop hIjac
  have hLbot : L = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    let y : L := ⟨x, hx⟩
    have hy : y = 0 := Subsingleton.elim _ _
    exact Subtype.ext_iff.mp hy
  have hinj : Function.Injective (algebraMap A B) := by
    rw [RingHom.injective_iff_ker_eq_bot]
    simpa [L] using hLbot
  have hKCompleteA : IsAdicComplete K A := by
    -- Bijectivity of the canonical map `A → A^∧_K` is the owner criterion for `K`-adic completeness.
    exact (AdicCompletion.of_bijective_iff).mp ⟨hinj, hsurj⟩
  -- Finish by weakening completeness from `K = I + J` back to `J`.
  exact isAdicComplete_of_le_of_fg hJleK hJfg hKCompleteA

end
