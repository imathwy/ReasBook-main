import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_90_1
import stacks_proof.stacks_project.Chap10.Lemma_10_39_5
import stacks_proof.stacks_project.Chap10.Proposition_10_89_2
import stacks_proof.stacks_project.Chap10.Proposition_10_89_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {R : Type u} [CommRing R]

open scoped TensorProduct

/- Domain triage: this proposition relates coherence of a commutative ring to flatness of
arbitrary products.
- `source-facing`: the TFAE comparing the Stacks ideal-theoretic coherence condition with flatness
  of products.
- `core/canonical`: the chapter owner predicate `IsCoherentRing R`.
- `bridge/view`: the textbook clause "every finitely generated ideal is finitely presented" is a
  source-facing reformulation of `IsCoherentRing R`, not a separate owner abstraction.
Primitive data are only the ring and the chosen family of modules; finite presentation of ideals is
derived API of the owner predicate. -/

-- Proof sketch: `(1) → (2)` uses the ideal-theoretic flatness criterion from Lemma `10.39.5`.
-- For a finitely generated ideal `I`, coherence gives finite presentation, so Proposition
-- `10.89.3` identifies `I ⊗[R] ∏ Mₐ` with `∏ (I ⊗[R] Mₐ)`, and injectivity follows
-- componentwise from the flatness of each factor. `(2) → (3)` is the specialization to the
-- constant family with each factor equal to `R`. For `(3) → (1)`, Proposition `10.89.2`
-- identifies the image of `I ⊗[R] R^A → R^A` with `I^A`, and Proposition `10.89.3` then forces
-- each finitely generated ideal `I` to be finitely presented, i.e. the canonical owner predicate
-- `IsCoherentRing R` holds.
/-- Helper for Proposition 10.90.6: the flatness test map into a product is the canonical
comparison map `TensorProduct.piRightHom` followed by the coordinatewise flatness test maps. -/
lemma ideal_lift_pi_eq_pi_comp_piRightHom {A : Type (max u v)}
    {M : A → Type (max u w)} [∀ a, AddCommGroup (M a)] [∀ a, Module R (M a)] (I : Ideal R) :
    TensorProduct.lift ((LinearMap.lsmul R (∀ a, M a)).comp I.subtype) =
      (LinearMap.piMap fun a ↦ TensorProduct.lift ((LinearMap.lsmul R (M a)).comp I.subtype)) ∘ₗ
        TensorProduct.piRightHom R R I M := by
  -- Compute both linear maps on pure tensors; they agree coordinatewise.
  ext x f a
  simp [TensorProduct.piRightHom_tmul]

/-- Helper for Proposition 10.90.6: if a finitely generated ideal `I` is finitely presented, then
the ideal-test map into a product of flat modules is injective. -/
lemma ideal_lift_pi_injective_of_finitePresentation {A : Type (max u v)}
    {M : A → Type (max u w)} [∀ a, AddCommGroup (M a)] [∀ a, Module R (M a)] (I : Ideal R)
    (hIfg : I.FG) (hI : Module.FinitePresentation R I) (hM : ∀ a, Module.Flat R (M a)) :
    Function.Injective
      (TensorProduct.lift ((LinearMap.lsmul R (∀ a, M a)).comp I.subtype)) := by
  letI : Module.FinitePresentation R I := hI
  have hpi :
      Function.Bijective (TensorProduct.piRightHom R R I M) := by
    have hiff :
        Module.FinitePresentation R I ↔
          ∀ (B : Type (max u v)) (Q : B → Type (max u w))
            [∀ b, AddCommGroup (Q b)] [∀ b, Module R (Q b)],
            Function.Bijective (TensorProduct.piRightHom R R I Q) :=
      show
        Module.FinitePresentation R I ↔
          ∀ (B : Type (max u v)) (Q : B → Type (max u w))
            [∀ b, AddCommGroup (Q b)] [∀ b, Module R (Q b)],
            Function.Bijective (TensorProduct.piRightHom R R I Q)
      from
        module_finitePresentation_tfae_tensorProduct_pi_bijective.{u, u, v, w}
          (R := R) (M := I) |>.out 0 1
    exact hiff.1 hI A M
  have hcoord :
      Function.Injective
        (LinearMap.piMap fun a ↦
          TensorProduct.lift ((LinearMap.lsmul R (M a)).comp I.subtype)) := by
    -- Each coordinate is injective by the flatness criterion on the same finitely generated ideal.
    intro t₁ t₂ hEq
    ext a
    have ha :
        Function.Injective
          (TensorProduct.lift ((LinearMap.lsmul R (M a)).comp I.subtype)) := by
      exact (Module.Flat.iff_lift_lsmul_comp_subtype_injective.mp (hM a)) (I := I) hIfg
    exact ha (congrFun hEq a)
  -- Rewrite the product map through `piRightHom` and combine the injective factors.
  rw [ideal_lift_pi_eq_pi_comp_piRightHom (R := R) (M := M) I]
  exact hcoord.comp hpi.1

/-- Helper for Proposition 10.90.6: the flatness test map into `R^A` factors through the scalar
comparison map `TensorProduct.piScalarRightHom`. -/
lemma ideal_lift_scalar_eq_pi_subtype_comp_piScalarRightHom (I : Ideal R)
    (A : Type (max u v)) :
    TensorProduct.lift ((LinearMap.lsmul R (A → R)).comp I.subtype) =
      (LinearMap.piMap fun _ : A ↦ I.subtype) ∘ₗ TensorProduct.piScalarRightHom R R I A := by
  -- On pure tensors the scalar comparison map records the pointwise scalar multiples in `I`.
  ext x f a
  simp [TensorProduct.piScalarRightHom_tmul, mul_comm]

/-- Helper for Proposition 10.90.6: if every scalar product `R^A` is flat, then every finitely
generated ideal of `R` is finitely presented. -/
lemma finitePresentation_of_fg_ideal_of_flat_scalar_pi (I : Ideal R) (hIfg : I.FG)
    (hflat : ∀ A : Type (max u v), Module.Flat R (A → R)) :
    Module.FinitePresentation R I := by
  letI : Module.Finite R I := Module.Finite.of_fg hIfg
  have hsurj :
      ∀ A : Type (max u v), Function.Surjective (TensorProduct.piScalarRightHom R R I A) := by
    have hiff :
        Module.Finite R I ↔
          ∀ A : Type (max u v), Function.Surjective (TensorProduct.piScalarRightHom R R I A) :=
      show
        Module.Finite R I ↔
          ∀ A : Type (max u v), Function.Surjective (TensorProduct.piScalarRightHom R R I A)
      from
        module_finite_tfae_tensorProduct_pi_surjective.{u, u, v, v}
          (R := R) (M := I) |>.out 0 3
    exact hiff.1 inferInstance
  have hbij :
      ∀ A : Type (max u v), Function.Bijective (TensorProduct.piScalarRightHom R R I A) := by
    intro A
    have hlift :
        Function.Injective
          (TensorProduct.lift ((LinearMap.lsmul R (A → R)).comp I.subtype)) := by
      exact (Module.Flat.iff_lift_lsmul_comp_subtype_injective.mp (hflat A)) (I := I) hIfg
    have hpi :
        Function.Injective
          ((LinearMap.piMap fun _ : A ↦ I.subtype) ∘ TensorProduct.piScalarRightHom R R I A) := by
      simpa [LinearMap.comp_apply,
        ideal_lift_scalar_eq_pi_subtype_comp_piScalarRightHom (R := R) I A] using hlift
    have hinj :
        Function.Injective (TensorProduct.piScalarRightHom R R I A) := hpi.of_comp
    exact ⟨hinj, hsurj A⟩
  -- Proposition `10.89.3` converts bijectivity of the scalar comparison maps into finite
  -- presentation of `I`.
  have hiff :
      Module.FinitePresentation R I ↔
        ∀ A : Type (max u v), Function.Bijective (TensorProduct.piScalarRightHom R R I A) :=
    show
      Module.FinitePresentation R I ↔
        ∀ A : Type (max u v), Function.Bijective (TensorProduct.piScalarRightHom R R I A)
    from
      module_finitePresentation_tfae_tensorProduct_pi_bijective.{u, u, v, v}
        (R := R) (M := I) |>.out 0 3
  exact hiff.2 hbij

/-- Proposition 10.90.6: the following are equivalent for a commutative ring `R`: `R` is coherent
(expressed by the owner predicate `IsCoherentRing R`), arbitrary products of flat `R`-modules are
flat, and for every set `A` the product module `A → R` is flat. -/
@[stacks 05CZ]
theorem coherent_tfae_flat_products :
    List.TFAE
      [ IsCoherentRing R,
        ∀ (A : Type (max u v)) (M : A → Type (max u w))
          [∀ a, AddCommGroup (M a)] [∀ a, Module R (M a)],
          (∀ a, Module.Flat R (M a)) → Module.Flat R (∀ a, M a),
        ∀ A : Type (max u v), Module.Flat R (A → R) ] := by
  -- Route correction: enlarge the quantified index universe so the reverse implication can test
  -- clause `(3)` on arbitrary ideal-indexed products, exactly as in the source proof.
  tfae_have 1 → 2 := by
    intro hcoh A M _ _ hM
    -- Follow Lemma `10.39.5`: test flatness of the product on finitely generated ideals.
    rw [Module.Flat.iff_lift_lsmul_comp_subtype_injective]
    intro I hIfg
    -- Coherence makes every finitely generated ideal finitely presented.
    have hI : Module.FinitePresentation R I := by
      exact hcoh.finitePresentation_submodule I (Module.Finite.of_fg hIfg)
    -- Proposition `10.89.3` identifies the tensor with the product of the tensors.
    exact ideal_lift_pi_injective_of_finitePresentation (R := R) (M := M) I hIfg hI hM
  tfae_have 2 → 3 := by
    intro h A
    -- Specialize to the constant family `ULift R` and transport flatness back along the product
    -- equivalence with `A → R`.
    have hULift : Module.Flat R (A → ULift.{max u w} R) := by
      simpa using
        h A (fun _ : A ↦ ULift.{max u w} R)
          (fun _ ↦ (inferInstance : Module.Flat R (ULift.{max u w} R)))
    exact Module.Flat.of_linearEquiv
      (LinearEquiv.piCongrRight fun _ : A ↦ ULift.moduleEquiv.symm)
  tfae_have 3 → 1 := by
    intro hflat
    refine
      { toCoherent :=
          { toFinite := inferInstance
            finitePresentation_submodule := ?_ } }
    intro I hI
    -- Convert finite generation of the ideal into finite presentation via the scalar products.
    exact finitePresentation_of_fg_ideal_of_flat_scalar_pi (R := R) I Submodule.FG.of_finite hflat
  tfae_finish

end
