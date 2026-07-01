import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open IsLocalRing

universe u v w

section Length

/-
Domain triage:
* primary domain: finite-length modules under flat local base change and the closed fiber of a
  local homomorphism;
* sampled owner API: `Ideal.Fiber`, `Module.FaithfullyFlat.of_flat_of_isLocalHom`,
  `Module.length_ne_top_iff`, and `IsFiniteLength`;
* source-facing layer: the two textbook statements about the length of `B ⊗[A] M` and the finite
  length criterion after flat local base change;
* core/canonical owners: `Ideal.Fiber` for the closed fiber, `Module.FaithfullyFlat` for
  faithfulness of tensor base change, and `IsFiniteLength` for finiteness of length;
* bridge/view: the file keeps the source-facing length statements while deriving the ambient
  faithful-flat and finite-length notions from the owner abstractions already introduced earlier in
  the chapter.
-/

variable {A : Type u} {B : Type v} {M : Type w}
variable [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
variable [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]
variable [AddCommGroup M] [Module A M]

local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal A) B
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Helper for Lemma 10.52.13: base changing the residue field quotient `A / maximalIdeal A`
identifies with the closed fiber. -/
noncomputable def residue_baseChange_closedFiber_equiv :
    B ⊗[A] (A ⧸ maximalIdeal A) ≃ₐ[B] ClosedFiber :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[B] B)
      (.ofBijective _
        (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal A)))).trans <|
    Algebra.TensorProduct.commRight A B ((maximalIdeal A).ResidueField)

/-- Helper for Lemma 10.52.13: the closed fiber is the quotient `B / maximalIdeal A • B` as a
`B`-algebra. -/
noncomputable def closedFiber_quotient_equiv :
    (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)) ≃ₐ[B] ClosedFiber :=
  (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B (maximalIdeal A)).trans <|
    residue_baseChange_closedFiber_equiv

/-- Helper for Lemma 10.52.13: under the quotient description of the closed fiber, the class of
`b : B` maps to the image of `b` in the closed fiber. -/
@[simp] lemma closedFiber_quotient_equiv_mk (b : B) :
    closedFiber_quotient_equiv
        (Ideal.Quotient.mk (Ideal.map (algebraMap A B) (maximalIdeal A)) b) =
      algebraMap B ClosedFiber b := by
  -- Unfold the composite equivalence and evaluate each standard tensor-product component.
  simp [closedFiber_quotient_equiv, residue_baseChange_closedFiber_equiv,
    Algebra.TensorProduct.right_algebraMap_apply]

/-- Helper for Lemma 10.52.13: the canonical map `B → ClosedFiber` is surjective because the
closed fiber is the quotient `B / maximalIdeal A • B`. -/
lemma closedFiber_algebraMap_surjective :
    Function.Surjective (algebraMap B ClosedFiber) := by
  intro x
  obtain ⟨y, rfl⟩ := closedFiber_quotient_equiv.surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨b, (closedFiber_quotient_equiv_mk b).symm⟩

/-- Helper for Lemma 10.52.13: viewing the closed fiber as a `B`-module or as a module over
itself gives the same length. -/
lemma closedFiber_length_over_base_eq_self :
    Module.length B ClosedFiber = Module.length ClosedFiber ClosedFiber := by
  -- Compare the two scalar actions through the surjective algebra map `B → ClosedFiber`.
  exact Module.length_eq_of_surjective
    closedFiber_algebraMap_surjective

/-- Helper for Lemma 10.52.13: faithful flatness makes the natural map
`M → B ⊗[A] M` induce a strictly monotone map on submodules. -/
lemma tensor_product_mk_submodule_strictMono :
    StrictMono (fun N : Submodule A M => N.map (TensorProduct.mk A B M 1)) := by
  -- The local flat map is faithfully flat, so the tensor-product unit map is injective.
  letI : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact Submodule.map_strictMono_of_injective
    (Module.FaithfullyFlat.tensorProduct_mk_injective (A := A) (B := B) M)

/-- Helper for Lemma 10.52.13: faithful flatness makes scalar extension
`N ↦ N.baseChange B` strictly monotone on submodules. -/
lemma submodule_baseChange_strictMono :
    StrictMono (fun N : Submodule A M => N.baseChange B) := by
  letI : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  intro N P hNP
  let NP : Submodule A P := N.comap P.subtype
  have hNPNeTop : NP ≠ ⊤ := by
    intro htop
    have hmap : NP.map P.subtype = N := by
      dsimp [NP]
      rw [Submodule.map_comap_subtype, inf_of_le_right hNP.le]
    rw [htop, Submodule.map_top] at hmap
    exact hNP.ne (by simpa [Submodule.range_subtype] using hmap.symm)
  have hTensorNontrivial : Nontrivial (B ⊗[A] (P ⧸ NP)) := by
    exact (Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right A B).2
      (Submodule.Quotient.nontrivial_iff.mpr hNPNeTop)
  have hNPBaseChangeNeTop : NP.baseChange B ≠ ⊤ := by
    intro htop
    have hRangeTop : LinearMap.range (LinearMap.baseChange B NP.subtype) = ⊤ := by
      simpa [Submodule.baseChange] using htop
    have hExact : Function.Exact (LinearMap.baseChange B NP.subtype)
        (LinearMap.baseChange B NP.mkQ) := by
      simpa [LinearMap.baseChange_eq_ltensor] using
        (lTensor_exact B (LinearMap.exact_subtype_mkQ NP) (Submodule.mkQ_surjective NP))
    have hSurj : Function.Surjective (LinearMap.baseChange B NP.mkQ) := by
      simpa [LinearMap.baseChange_eq_ltensor] using
        (LinearMap.lTensor_surjective B (Submodule.mkQ_surjective NP))
    have hKerTop : LinearMap.ker (LinearMap.baseChange B NP.mkQ) = ⊤ := by
      rw [hExact.linearMap_ker_eq, hRangeTop]
    have hZero : LinearMap.baseChange B NP.mkQ = 0 := by
      rw [← LinearMap.ker_eq_top]
      exact hKerTop
    have hBotTop : (⊥ : Submodule B (B ⊗[A] (P ⧸ NP))) = ⊤ := by
      simpa [hZero] using (LinearMap.range_eq_top.2 hSurj)
    have hSubsingleton : Subsingleton (B ⊗[A] (P ⧸ NP)) := by
      rw [← Submodule.subsingleton_iff B, ← subsingleton_iff_bot_eq_top]
      simpa using hBotTop
    have : ¬ Subsingleton (B ⊗[A] (P ⧸ NP)) :=
      not_subsingleton_iff_nontrivial.mpr hTensorNontrivial
    exact this hSubsingleton
  let eNP :
      NP ≃ₗ[A] N :=
    (Submodule.equivMapOfInjective P.subtype Subtype.val_injective NP).trans <|
      LinearEquiv.ofEq _ _ (by
        dsimp [NP]
        rw [Submodule.map_comap_subtype, inf_of_le_right hNP.le])
  let iP : B ⊗[A] P →ₗ[B] B ⊗[A] M := LinearMap.baseChange B P.subtype
  have hiP : Function.Injective iP := by
    simpa [LinearMap.baseChange_eq_ltensor] using
      (Module.Flat.lTensor_preserves_injective_linearMap P.subtype Subtype.val_injective)
  have hcomp :
      iP.comp (LinearMap.baseChange B NP.subtype) =
        (LinearMap.baseChange B N.subtype).comp (LinearMap.baseChange B eNP.toLinearMap) := by
    ext b
    rfl
  have hRangeTop :
      LinearMap.range (LinearMap.baseChange B eNP.toLinearMap) = ⊤ := by
    simpa using LinearEquiv.range (LinearEquiv.baseChange A B NP N eNP)
  have hMap :
      (NP.baseChange B).map iP = N.baseChange B := by
    rw [Submodule.baseChange, Submodule.baseChange, ← LinearMap.range_comp, hcomp,
      LinearMap.range_comp_of_range_eq_top _ hRangeTop]
  have hTopMap :
      (⊤ : Submodule B (B ⊗[A] P)).map iP = P.baseChange B := by
    rw [Submodule.map_top, Submodule.baseChange]
  have hltTop : NP.baseChange B < ⊤ := lt_of_le_of_ne le_top hNPBaseChangeNeTop
  have hmaplt :
      (NP.baseChange B).map iP < (⊤ : Submodule B (B ⊗[A] P)).map iP :=
    (Submodule.map_strictMono_of_injective hiP) hltTop
  rw [hMap, hTopMap] at hmaplt
  exact hmaplt

/-- Helper for Lemma 10.52.13: every strict chain of submodules in `M` remains strict after base
change to `B`, so the length can only increase. -/
lemma length_le_length_base_change :
    Module.length A M ≤ Module.length B (B ⊗[A] M) := by
  -- Convert strict monotonicity of base change on submodules into the height inequality.
  simpa [Module.length_eq_height, Submodule.baseChange_top] using
    Order.height_le_height_apply_of_strictMono
      (fun N : Submodule A M => N.baseChange B)
      submodule_baseChange_strictMono ⊤

/-- Helper for Lemma 10.52.13: base change carries every simple `A`-module to a `B`-module whose
length is the length of the closed fiber. -/
lemma simple_baseChange_length_eq_closedFiber_length
    {Q : Type*} [AddCommGroup Q] [Module A Q] [IsSimpleModule A Q] :
    Module.length B (B ⊗[A] Q) = Module.length ClosedFiber ClosedFiber := by
  obtain ⟨I, hImax, ⟨eQ⟩⟩ := isSimpleModule_iff_quot_maximal.mp (inferInstance : IsSimpleModule A Q)
  have hI : I = maximalIdeal A := IsLocalRing.eq_maximalIdeal hImax
  subst hI
  -- Replace the simple module by the residue field quotient and then identify its base change
  -- with the closed fiber.
  calc
    Module.length B (B ⊗[A] Q) =
        Module.length B (B ⊗[A] (A ⧸ maximalIdeal A)) := by
          simpa using (LinearEquiv.baseChange A B Q (A ⧸ maximalIdeal A) eQ).length_eq
    _ = Module.length B ClosedFiber := by
          simpa using residue_baseChange_closedFiber_equiv.toLinearEquiv.length_eq
    _ = Module.length ClosedFiber ClosedFiber := closedFiber_length_over_base_eq_self

/-- Helper for Lemma 10.52.13: for modules of finite length, base change multiplies length by the
length of the closed fiber. -/
lemma length_base_change_eq_mul_closed_fiber_of_isFiniteLength
    (hM : IsFiniteLength A M) :
    Module.length B (B ⊗[A] M) =
      Module.length A M * Module.length ClosedFiber ClosedFiber := by
  induction hM with
  | of_subsingleton =>
      -- The trivial module stays trivial after tensoring, so both lengths are zero.
      simp
  | @of_simple_quotient M _ _ N _ hN ih =>
      have hTensorInj : Function.Injective (LinearMap.baseChange B N.subtype) := by
        simpa [LinearMap.baseChange_eq_ltensor] using
          (Module.Flat.lTensor_preserves_injective_linearMap N.subtype Subtype.val_injective)
      have hTensorSurj : Function.Surjective (LinearMap.baseChange B N.mkQ) := by
        simpa [LinearMap.baseChange_eq_ltensor] using
          (LinearMap.lTensor_surjective B (Submodule.mkQ_surjective N))
      have hTensorExact : Function.Exact (LinearMap.baseChange B N.subtype)
          (LinearMap.baseChange B N.mkQ) := by
        simpa [LinearMap.baseChange_eq_ltensor] using
          (lTensor_exact B (LinearMap.exact_subtype_mkQ N) (Submodule.mkQ_surjective N))
      have hTensorLength :
          Module.length B (B ⊗[A] M) =
            Module.length B (B ⊗[A] N) + Module.length B (B ⊗[A] (M ⧸ N)) := by
        -- Tensor the short exact sequence `0 → N → M → M ⧸ N → 0`.
        simpa using
          (Module.length_eq_add_of_exact (LinearMap.baseChange B N.subtype)
            (LinearMap.baseChange B N.mkQ) hTensorInj hTensorSurj hTensorExact)
      have hSourceLength : Module.length A M = Module.length A N + 1 := by
        -- The simple quotient contributes exactly one to the source-side length.
        simpa using
          (Module.length_eq_add_of_exact N.subtype N.mkQ Subtype.val_injective
            (Submodule.mkQ_surjective N) (LinearMap.exact_subtype_mkQ N))
      -- Combine additivity with the simple-factor computation.
      calc
        Module.length B (B ⊗[A] M) =
            Module.length B (B ⊗[A] N) + Module.length B (B ⊗[A] (M ⧸ N)) :=
              hTensorLength
        _ = Module.length A N * Module.length ClosedFiber ClosedFiber +
              Module.length ClosedFiber ClosedFiber := by
              rw [ih, simple_baseChange_length_eq_closedFiber_length]
        _ = (Module.length A N + 1) * Module.length ClosedFiber ClosedFiber := by
              simp [add_mul]
        _ = Module.length A M * Module.length ClosedFiber ClosedFiber := by
              rw [hSourceLength]

-- Proof sketch: a flat local map of local rings is faithfully flat, so tensoring a composition
-- series of `M` with `B` preserves strict inclusions. Each simple quotient `A / maximalIdeal A`
-- becomes the closed fiber `((maximalIdeal A).Fiber B)`, equivalently
-- `B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)`, and additivity of `Module.length` gives the
-- multiplicative formula.
/-- Lemma 10.52.13 (1): for a flat local homomorphism `A → B`, the length of the base change
`B ⊗[A] M` is the length of `M` times the length of the closed fiber
`((maximalIdeal A).Fiber B)`, equivalently
`B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)`. -/
theorem length_base_change_eq_length_mul_closed_fiber :
    Module.length B (B ⊗[A] M) =
      Module.length A M * Module.length ClosedFiber ClosedFiber := by
  by_cases htop : Module.length A M = ⊤
  · -- If `M` has infinite length, faithful flatness forces the base change to have infinite
    -- length as well, and multiplying by the positive closed-fiber length stays at `⊤`.
    have hTensorTop : Module.length B (B ⊗[A] M) = ⊤ := by
      exact top_le_iff.mp (htop ▸ length_le_length_base_change)
    have hMapLe :
        Ideal.map (algebraMap A B) (maximalIdeal A) ≤ maximalIdeal B := by
      exact ((local_hom_TFAE (algebraMap A B)).out 0 2).mp
        (inferInstance : IsLocalHom (algebraMap A B))
    have hMapNeTop : Ideal.map (algebraMap A B) (maximalIdeal A) ≠ ⊤ := by
      intro htopMap
      exact (Ideal.IsPrime.ne_top (inferInstance : (maximalIdeal B).IsPrime))
        (top_le_iff.mp (htopMap ▸ hMapLe))
    letI : Nontrivial (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)) :=
      Ideal.Quotient.nontrivial_iff.mpr hMapNeTop
    letI : Nontrivial ClosedFiber := closedFiber_quotient_equiv.symm.toRingEquiv.toEquiv.nontrivial
    have hClosedFiberPos : 0 < Module.length ClosedFiber ClosedFiber := Module.length_pos
    rw [hTensorTop, htop, ENat.top_mul hClosedFiberPos.ne']
  · -- In the finite-length branch, use induction on the finite-length structure of `M`.
    exact length_base_change_eq_mul_closed_fiber_of_isFiniteLength
      ((Module.length_ne_top_iff).mp htop)

-- Proof sketch: use the length formula in (1) together with `Module.length_ne_top_iff`.
-- If the closed fiber has finite length, then multiplication by its length preserves finiteness of
-- the other factor, yielding the equivalence of finite-length conditions.
/-- Lemma 10.52.13 (2): if the closed fiber `((maximalIdeal A).Fiber B)`, equivalently
`B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)`, has finite length as a module over itself,
then `M` has finite length over `A` if and only if `B ⊗[A] M` has finite
length over `B`. -/
theorem finite_length_iff_finite_length_base_change
    (hclosedFiber : IsFiniteLength ClosedFiber ClosedFiber) :
    IsFiniteLength A M ↔ IsFiniteLength B (B ⊗[A] M) := by
  constructor
  · intro hM
    -- Apply the length formula and use finiteness of both factors.
    rw [← Module.length_ne_top_iff] at hM hclosedFiber ⊢
    rw [length_base_change_eq_length_mul_closed_fiber (A := A) (B := B) (M := M)]
    exact WithTop.mul_ne_top hM hclosedFiber
  · intro hTensor
    -- Infinite source length would force infinite target length by faithful flatness.
    rw [← Module.length_ne_top_iff] at hTensor ⊢
    intro htop
    have hTensorTop : Module.length B (B ⊗[A] M) = ⊤ := by
      exact top_le_iff.mp (htop ▸ length_le_length_base_change)
    exact hTensor hTensorTop

end Length
