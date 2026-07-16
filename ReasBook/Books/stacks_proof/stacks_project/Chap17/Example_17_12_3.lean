import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_6_4
import stacks_proof.stacks_project.Chap10.Definition_10_90_1
import stacks_proof.stacks_project.Chap10.Example_10_161_2
import stacks_proof.stacks_project.Chap10.Lemma_10_90_5
import stacks_proof.stacks_project.Chap15.Lemma_15_4_3

-- Declarations for this item will be appended below by the statement pipeline.

open MvPolynomial
open Module.Finite
open scoped TensorProduct

noncomputable section

local notation "Cinf" => MvPolynomial ℕ+ ℂ

/- Domain-style sampling for Example 17.12.3:
- primary domain: commutative algebra of coherence and Noetherianity for countable-variable
  polynomial rings;
- source-facing owner: the countable polynomial ring `Cinf = MvPolynomial ℕ+ ℂ`;
- inspected owner declarations:
  * `IsCoherentRing R`;
  * `Module.Coherent.finitePresentation_submodule`;
  * `countableVariablePolynomialRing_isN2Ring_and_not_isNoetherian`.
- primitive data: the owner ring `Cinf` and finitely generated ideals in it;
- derived API: finite presentation of finitely generated ideals and the failure of
  `IsNoetherianRing`.

The coherent statement is genuinely source-facing here, so the public surface stays at
`IsCoherentRing Cinf`. The ideal-theoretic clause is a thin companion extracted from that owner
predicate, while part `(2)` is recall-only and should directly reuse the Chapter 10
countable-variable theorem rather than introduce a second local wrapper.
-/

-- Proof sketch: use the canonical countable-variable owner `Cinf`. For a commutative ring,
-- coherence of the self-module is captured by finite presentation of finitely generated ideals.
/-- Helper for Example 17.12.3: a finitely generated ideal of `Cinf` is generated inside some
finite-variable polynomial subring. -/
lemma fg_ideal_descends_to_finite_variable_subring
    (I : Ideal Cinf) (hI : I.FG) :
    ∃ s : Finset ℕ+, ∃ J : Ideal (MvPolynomial s ℂ),
      I = Ideal.map (MvPolynomial.rename (fun i : s => (i : ℕ+))) J := by
  classical
  obtain ⟨t, ht⟩ := hI
  let s : Finset ℕ+ := t.biUnion MvPolynomial.vars
  let hsupp : ∀ p : t, p.1 ∈ MvPolynomial.supported ℂ (↑s : Set ℕ+) := fun p => by
    -- Every chosen generator only uses variables from the finite union `s`.
    rw [MvPolynomial.mem_supported]
    intro i hi
    exact Finset.mem_biUnion.mpr ⟨p.1, p.2, hi⟩
  let lift : t → MvPolynomial s ℂ := fun p =>
    MvPolynomial.supportedEquivMvPolynomial (R := ℂ) (↑s : Set ℕ+) ⟨p.1, hsupp p⟩
  have hrename : ∀ p : t,
      MvPolynomial.rename (fun i : s => (i : ℕ+)) (lift p) = p.1 := by
    intro p
    -- The supported-equivalence inverse recovers the original generator in `Cinf`.
    change (((MvPolynomial.supportedEquivMvPolynomial (R := ℂ) (↑s : Set ℕ+)).symm (lift p) :
      MvPolynomial.supported ℂ (↑s : Set ℕ+)).1 = p.1)
    simp [lift]
  let J : Ideal (MvPolynomial s ℂ) := Ideal.span (Set.range lift)
  refine ⟨s, J, ?_⟩
  -- Mapping the descended generators back along `rename` recovers the original ideal.
  dsimp [J]
  rw [← ht, Ideal.map_span]
  have himage :
      Set.image (MvPolynomial.rename (fun i : s => (i : ℕ+))) (Set.range lift) = (↑t : Set Cinf) := by
    ext x
    constructor
    · rintro ⟨p, ⟨q, rfl⟩, rfl⟩
      simpa [hrename q] using q.2
    · intro hx
      refine ⟨lift ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, ?_⟩
      exact hrename ⟨x, hx⟩
  simpa [himage]

/-- Helper for Example 17.12.3: ideals in a finite-variable complex polynomial ring are finitely
presented. -/
lemma finite_variable_polynomial_ideal_finitePresentation
    (s : Finset ℕ+) (J : Ideal (MvPolynomial s ℂ)) :
    Module.FinitePresentation (MvPolynomial s ℂ) J := by
  letI : IsNoetherianRing (MvPolynomial s ℂ) := inferInstance
  letI : IsCoherentRing (MvPolynomial s ℂ) := noetherianRing_isCoherentRing
  -- Finite-variable polynomial rings are Noetherian, hence coherent, so their ideals are f.p.
  exact
    (inferInstance : Module.Coherent (MvPolynomial s ℂ) (MvPolynomial s ℂ)).finitePresentation_submodule
      J (Module.Finite.of_fg J.fg_of_isNoetherianRing)

/-- Helper for Example 17.12.3: splitting the variables of `Cinf` into `s` and its complement
turns the finite-variable inclusion into the canonical coefficient map. -/
noncomputable def countableVariableSplitAlgEquiv
    (s : Finset ℕ+) :
    MvPolynomial (↥((↑s : Set ℕ+)ᶜ)) (MvPolynomial s ℂ) ≃ₐ[ℂ] Cinf :=
  (MvPolynomial.sumAlgEquiv ℂ (↥((↑s : Set ℕ+)ᶜ)) s).symm.trans
    (MvPolynomial.renameEquiv ℂ <|
      (Equiv.sumComm (↥((↑s : Set ℕ+)ᶜ)) s).trans <| Equiv.Set.sumCompl (↑s : Set ℕ+))

/-- Helper for Example 17.12.3: the split equivalence conjugates `rename Subtype.val`
to the coefficient embedding. -/
lemma countable_variable_split_comp_rename_subtype
    (s : Finset ℕ+) :
    (countableVariableSplitAlgEquiv s).toRingHom.comp
        (MvPolynomial.C :
          MvPolynomial s ℂ →+*
            MvPolynomial (↥((↑s : Set ℕ+)ᶜ)) (MvPolynomial s ℂ)) =
      (MvPolynomial.rename (fun i : s => (i : ℕ+))).toRingHom := by
  classical
  let eqv := countableVariableSplitAlgEquiv s
  have h :
      (MvPolynomial.rename (fun i : s => (i : ℕ+))).toRingHom =
        eqv.toAlgHom.toRingHom.comp
          (MvPolynomial.C :
            MvPolynomial s ℂ →+*
              MvPolynomial (↥((↑s : Set ℕ+)ᶜ)) (MvPolynomial s ℂ)) := by
    -- This is the standard variable-splitting identity from the finite-support `rename` API.
    apply ringHom_ext
    · intro z
      simp only [eqv, countableVariableSplitAlgEquiv, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        rename_C, AlgEquiv.toAlgHom_eq_coe, AlgEquiv.toAlgHom_toRingHom, RingHom.coe_comp,
        AlgEquiv.coe_trans, Function.comp_apply, MvPolynomial.sumAlgEquiv_symm_apply, iterToSum_C_C,
        renameEquiv_apply, Equiv.coe_trans, Equiv.sumComm_apply]
    · intro i
      simp only [eqv, countableVariableSplitAlgEquiv, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        rename_X, AlgEquiv.toAlgHom_eq_coe, AlgEquiv.toAlgHom_toRingHom, RingHom.coe_comp,
        AlgEquiv.coe_trans, Function.comp_apply, MvPolynomial.sumAlgEquiv_symm_apply, iterToSum_C_X,
        renameEquiv_apply, Equiv.coe_trans, Equiv.sumComm_apply, Sum.swap_inr]
      simpa using
        congrArg (fun j : ℕ+ ↦ (X j : Cinf)) (Equiv.Set.sumCompl_apply_inl (↑s : Set ℕ+) i)
  exact h.symm

/-- Helper for Example 17.12.3: after adjoining the complementary variables, the extension of a
finite-variable ideal is finitely presented. -/
lemma baseChange_ideal_finitePresentation
    (s : Finset ℕ+) (J : Ideal (MvPolynomial s ℂ)) :
    Module.FinitePresentation
      (MvPolynomial (↥((↑s : Set ℕ+)ᶜ)) (MvPolynomial s ℂ))
      (J.baseChange (MvPolynomial (↥((↑s : Set ℕ+)ᶜ)) (MvPolynomial s ℂ))) := by
  let A := MvPolynomial s ℂ
  let B := MvPolynomial (↥((↑s : Set ℕ+)ᶜ)) A
  letI : AddCommGroup J := inferInstance
  letI : Module.FinitePresentation A J := finite_variable_polynomial_ideal_finitePresentation s J
  letI : Module B (B ⊗[A] J) := TensorProduct.leftModule
  letI : AddCommGroup (B ⊗[A] J) := inferInstance
  letI : AddCommGroup (TensorProduct A B A) := inferInstance
  letI : Module.FinitePresentation B (B ⊗[A] J) := by
    infer_instance
  -- The canonical base-change equivalence identifies the tensor module with `J.baseChange B`.
  change Module.FinitePresentation B ↥(J.baseChange B)
  letI : AddCommGroup ↥(J.baseChange B) := inferInstance
  let eBase : (B ⊗[A] J) ≃ₗ[B] ↥(J.baseChange B) :=
    Submodule.toBaseChange.toLinearEquiv B J
  exact Module.FinitePresentation.of_equiv eBase

/-- Helper for Example 17.12.3: the tensor right-unit comparison sends the base-changed ideal to
the ideal generated by the coefficient images of `J`. -/
lemma ideal_baseChange_map_rid_eq_map_C
    (s : Finset ℕ+) (J : Ideal (MvPolynomial s ℂ)) :
    let A := MvPolynomial s ℂ
    let B := MvPolynomial (↥((↑s : Set ℕ+)ᶜ)) A
    letI : Module B (B ⊗[A] A) := TensorProduct.leftModule
    Submodule.map (TensorProduct.AlgebraTensorModule.rid A B B).toLinearMap (J.baseChange B) =
      (Ideal.map (MvPolynomial.C : A →+* B) J : Submodule B B) := by
  classical
  dsimp only
  let A := MvPolynomial s ℂ
  let B := MvPolynomial (↥((↑s : Set ℕ+)ᶜ)) A
  letI : Module B (B ⊗[A] A) := TensorProduct.leftModule
  let eRid : B ⊗[A] A ≃ₗ[B] B := TensorProduct.AlgebraTensorModule.rid A B B
  -- Compare both sides after rewriting them as spans of the same image set of generators.
  rw [LinearMap.Submodule.baseChange_eq_span_tmul_mem (B := B) (P := (J : Submodule A A))]
  rw [Submodule.map_span]
  have hmapspan :
      ((Ideal.map (MvPolynomial.C : A →+* B) J : Ideal B) : Submodule B B) =
        Ideal.span ((MvPolynomial.C : A →+* B) '' (↑J : Set A)) := by
    calc
      ((Ideal.map (MvPolynomial.C : A →+* B) J : Ideal B) : Submodule B B) =
          (Ideal.map (MvPolynomial.C : A →+* B) (Ideal.span (↑J : Set A)) : Ideal B) := by
            rw [Ideal.span_eq]
      _ = Ideal.span ((MvPolynomial.C : A →+* B) '' (↑J : Set A)) := by
            rw [Ideal.map_span]
  rw [hmapspan]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, by
      -- The right-unit map sends `1 ⊗ z` to the coefficient image of `z`.
      simpa [eRid, A, B, Algebra.smul_def] using
        (TensorProduct.AlgebraTensorModule.rid_tmul (R := A) (A := B) (M := B) z (1 : B))⟩
  · rintro ⟨z, hz, rfl⟩
    refine ⟨TensorProduct.tmul A (1 : B) z, ⟨z, hz, rfl⟩, ?_⟩
    -- The same pure tensor witnesses the reverse inclusion on generators.
    simpa [eRid, A, B, Algebra.smul_def] using
      (TensorProduct.AlgebraTensorModule.rid_tmul (R := A) (A := B) (M := B) z (1 : B))

/-- Helper for Example 17.12.3: after restricting scalars along the split equivalence, the mapped
ideal is exactly the linear image of the original ideal. -/
lemma ideal_map_splitAlgEquiv_restrictScalars_eq_map
    {B : Type*} [CommRing B] [Algebra ℂ B]
    (e : B ≃ₐ[ℂ] Cinf) (I : Ideal B) :
    letI : Algebra B Cinf := e.toAlgHom.toAlgebra
    ((Ideal.map e.toRingHom I).restrictScalars B : Submodule B Cinf) =
      Submodule.map (Algebra.linearMap B Cinf) (I : Submodule B B) := by
  classical
  letI : Algebra B Cinf := e.toAlgHom.toAlgebra
  let hsurj : Function.Surjective (algebraMap B Cinf) := by
    intro x
    refine ⟨e.symm x, ?_⟩
    change e (e.symm x) = x
    simpa using e.apply_symm_apply x
  letI : RingHomSurjective (algebraMap B Cinf) := ⟨hsurj⟩
  ext x
  constructor
  · intro hx
    change x ∈ Ideal.map e.toRingHom I at hx
    rw [Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective] at hx
    rw [Submodule.mem_map]
    rcases hx with ⟨y, hy, rfl⟩
    -- The split equivalence and the induced algebra map agree on the nose on elements.
    exact ⟨y, hy, by
      change (algebraMap B Cinf) y = e y
      rfl⟩
  · intro hx
    rw [Submodule.mem_map] at hx
    rcases hx with ⟨y, hy, hxy⟩
    change x ∈ Ideal.map e.toRingHom I
    rw [Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective]
    -- Unpack the linear image witness back into the ideal map along `e`.
    exact ⟨y, hy, by
      change algebraMap B Cinf y = x at hxy
      simpa using hxy⟩

lemma finitePresentation_map_of_splitAlgEquiv
    {B : Type*} [CommRing B] [Algebra ℂ B]
    (e : B ≃ₐ[ℂ] Cinf) (I : Ideal B) [Module.FinitePresentation B I] :
    Module.FinitePresentation Cinf (Ideal.map e.toRingHom I) := by
  classical
  letI : Algebra B Cinf := e.toAlgHom.toAlgebra
  let hsurj : Function.Surjective (algebraMap B Cinf) := by
    intro x
    refine ⟨e.symm x, ?_⟩
    change e (e.symm x) = x
    simpa using e.apply_symm_apply x
  letI : Algebra.FiniteType B Cinf := by
    rw [← RingHom.finiteType_algebraMap]
    exact RingHom.FiniteType.of_surjective (algebraMap B Cinf) hsurj
  have hrestrict :
      ((Ideal.map e.toRingHom I).restrictScalars B : Submodule B Cinf) =
        Submodule.map (Algebra.linearMap B Cinf) (I : Submodule B B) :=
    ideal_map_splitAlgEquiv_restrictScalars_eq_map e I
  have hinj : Function.Injective (Algebra.linearMap B Cinf) := by
    intro x y hxy
    change e x = e y at hxy
    exact e.injective hxy
  have hfpMap :
      Module.FinitePresentation B
        ↥(Submodule.map (Algebra.linearMap B Cinf) (I : Submodule B B)) := by
    -- Transport finite presentation across the injective `B`-linear image map.
    exact
      Module.FinitePresentation.of_equiv
        ((I : Submodule B B).equivMapOfInjective (Algebra.linearMap B Cinf) hinj)
  have hfpRestrict :
      Module.FinitePresentation B
        ↥(((Ideal.map e.toRingHom I).restrictScalars B : Submodule B Cinf)) := by
    -- Rewrite the restricted-scalars module to that linear image.
    rw [hrestrict]
    exact hfpMap
  letI : Module.FinitePresentation B ↥(Ideal.map e.toRingHom I) := by
    simpa using hfpRestrict
  -- Once the `B`-module structure is in canonical form, finite type upgrades it to a `Cinf`-proof.
  change Module.FinitePresentation Cinf ↥(Ideal.map e.toRingHom I)
  exact Module.FinitePresentation.of_restrictScalars_finiteType B

/-- Helper for Example 17.12.3: after adjoining the complementary variables, the extension of a
finite-variable ideal is finitely presented. -/
lemma ideal_map_C_finitePresentation
    (s : Finset ℕ+) (J : Ideal (MvPolynomial s ℂ)) :
    Module.FinitePresentation
      (MvPolynomial (↥((↑s : Set ℕ+)ᶜ)) (MvPolynomial s ℂ))
      (Ideal.map
        (MvPolynomial.C :
          MvPolynomial s ℂ →+*
            MvPolynomial (↥((↑s : Set ℕ+)ᶜ)) (MvPolynomial s ℂ)) J) := by
  let A := MvPolynomial s ℂ
  let B := MvPolynomial (↥((↑s : Set ℕ+)ᶜ)) A
  have hbase : Module.FinitePresentation B (J.baseChange B) :=
    baseChange_ideal_finitePresentation s J
  letI : Module B (B ⊗[A] A) := TensorProduct.leftModule
  let eRid : B ⊗[A] A ≃ₗ[B] B := TensorProduct.AlgebraTensorModule.rid A B B
  have hEq :
      Submodule.map eRid.toLinearMap (J.baseChange B) =
        (Ideal.map (MvPolynomial.C : A →+* B) J : Submodule B B) :=
    ideal_baseChange_map_rid_eq_map_C s J
  have hEquiv :
      ↥(J.baseChange B) ≃ₗ[B] ↥(Ideal.map (MvPolynomial.C : A →+* B) J) := by
    -- Compare `J.baseChange B` with its image under the injective `rid` map, then rewrite that image.
    exact
      ((J.baseChange B).equivMapOfInjective eRid.toLinearMap eRid.injective).trans
        (LinearEquiv.ofEq _ _ hEq)
  letI : Module.FinitePresentation B ↥(J.baseChange B) := hbase
  -- Route correction: finish on the canonical base-change module and transport only once via `rid`.
  change Module.FinitePresentation B ↥(Ideal.map (MvPolynomial.C : A →+* B) J)
  exact Module.FinitePresentation.of_equiv hEquiv

/-- Helper for Example 17.12.3: extending a finite-variable ideal along the canonical rename map
to `Cinf` preserves finite presentation. -/
lemma ideal_map_subtype_rename_finitePresentation
    (s : Finset ℕ+) (J : Ideal (MvPolynomial s ℂ)) :
    Module.FinitePresentation Cinf
      (Ideal.map (MvPolynomial.rename (fun i : s => (i : ℕ+))) J) := by
  classical
  let B := MvPolynomial (↥((↑s : Set ℕ+)ᶜ)) (MvPolynomial s ℂ)
  let e : B ≃ₐ[ℂ] Cinf := countableVariableSplitAlgEquiv s
  let I : Ideal B := Ideal.map (MvPolynomial.C : MvPolynomial s ℂ →+* B) J
  have hcomp := countable_variable_split_comp_rename_subtype s
  have hfpB : Module.FinitePresentation B I := ideal_map_C_finitePresentation s J
  letI : Module.FinitePresentation B I := hfpB
  have hfpMap : Module.FinitePresentation Cinf (Ideal.map e.toRingHom I) :=
    finitePresentation_map_of_splitAlgEquiv e I
  have hmap :
      Ideal.map e.toRingHom I =
        Ideal.map (MvPolynomial.rename (fun i : s => (i : ℕ+))) J := by
    -- Rewrite the split transport as a composite map and then use the variable-splitting identity.
    dsimp [I]
    rw [Ideal.map_map]
    simpa [e] using
      congrArg
        (fun φ : MvPolynomial s ℂ →+* Cinf ↦ Ideal.map φ J)
        hcomp
  -- The split equivalence closes the proof once the composite map is rewritten back to `rename`.
  rw [← hmap]
  exact hfpMap

/-- Example 17.12.3 (1): the countable polynomial ring `\mathbf{C}[x_1, x_2, x_3, \ldots]`,
modeled as `Cinf`, is coherent as a module over itself. -/
@[stacks 01BX]
instance complex_countableVariablePolynomialRing_isCoherentRing :
    IsCoherentRing Cinf := by
  refine
    { toCoherent :=
        { toFinite := by infer_instance
          finitePresentation_submodule := by
            intro I hI
            have hI' : I.FG := by
              simpa [Module.Finite.iff_fg] using hI
            -- First descend the finitely generated ideal to a finite-variable polynomial ring.
            obtain ⟨s, J, hIJ⟩ := fg_ideal_descends_to_finite_variable_subring I hI'
            -- The remaining step is the base-change comparison from that subring back to `Cinf`.
            rw [hIJ]
            exact ideal_map_subtype_rename_finitePresentation s J } }

/-- Example 17.12.3 (1), ideal-theoretic form: every finitely generated ideal in
`\mathbf{C}[x_1, x_2, x_3, \ldots]` is finitely presented. -/
@[stacks 01BX]
theorem complex_countableVariablePolynomialRing_fgIdeal_finitePresentation
    (I : Ideal Cinf) (hI : I.FG) :
    Module.FinitePresentation Cinf I := by
  exact
    (inferInstance : Module.Coherent Cinf Cinf).finitePresentation_submodule I (of_fg hI)

-- Proof sketch: this is exactly the non-Noetherian half of the Chapter 10 countable-variable
-- owner theorem specialized to `ℂ`.
/- Example 17.12.3 (2): the countable polynomial ring `\mathbf{C}[x_1, x_2, x_3, \ldots]`,
viewed as a module over itself, is not Noetherian. This is exactly the `.2` projection of the
canonical Chapter 10 theorem `countableVariablePolynomialRing_isN2Ring_and_not_isNoetherian`
specialized to `ℂ`. -/
#check (countableVariablePolynomialRing_isN2Ring_and_not_isNoetherian ℂ).2
