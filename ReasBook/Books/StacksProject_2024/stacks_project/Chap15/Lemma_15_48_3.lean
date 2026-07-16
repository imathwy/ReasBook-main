import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_106_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing
open RingTheory Sequence

noncomputable section

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]
variable {m : ℕ}

local notation "κ" => ResidueField R

/- Domain-style sampling:
* primary domain: regular local rings, chosen families in the maximal ideal, cotangent-space
  criteria, and regular systems of parameters;
* sampled owner declarations upstream in the chapter/project:
  `parameterIdeal`,
  `IsPartOfRegularSystemOfParameters`,
  `IsPartOfRegularSystemOfParameters.isRegular`,
  `IsPartOfRegularSystemOfParameters.isRegularLocalRing_quotient_parameterIdeal`;
* source/core/bridge triage:
  `source-facing`: the Jacobian determinant criterion for the chosen family
  `x : Fin m → maximalIdeal R`;
  `core/canonical`: `IsPartOfRegularSystemOfParameters (maximalIdeal R).spanFinrank x`,
  together with the derived owners `parameterIdeal x` and `IsRegular R (List.ofFn fun i ↦ (x i : R))`;
  `bridge/view`: the two textbook consequences obtained from the Chapter 10 owner API;
* owner abstraction: the main declaration in this file should be exactly the bridge from the
  Jacobian determinant hypothesis to
  `IsPartOfRegularSystemOfParameters (maximalIdeal R).spanFinrank x`. The quotient regularity and
  list regularity statements are then canonical downstream views and should stay thin wrappers
  around the Chapter 10 owner theorems, not parallel local APIs;
* primitive data: the family `x`, the derivations `D`, and the unit Jacobian determinant
  hypothesis;
* derived API: `IsPartOfRegularSystemOfParameters (maximalIdeal R).spanFinrank x`, regularity of
  the quotient by `parameterIdeal x`, and regularity of `List.ofFn fun i ↦ (x i : R)`, with the
  latter two exposed only as direct owner consequences.

The source hypothesis `1 ≤ m` is mathematically redundant here: the empty family case is still a
valid regular sequence and quotient, so the public API keeps only the primitive data used by the
owner-level statements.
-/

-- Proof sketch: use the determinant hypothesis to show the classes of the `x i` are linearly
-- independent in `maximalIdeal R / (maximalIdeal R) ^ 2`, exactly as in the textbook proof. Extend
-- them to a basis of the cotangent space of the regular local ring `R`, lift that basis to a
-- regular system of parameters, and identify the original family `x` with the initial segment.
/-- Helper for Lemma 15.48.3: the residue of a derivation is `R`-linear on the maximal ideal. -/
theorem derivation_residue_linear_map_smul
    (D : Derivation ℤ R R) (a : R) (x : maximalIdeal R) :
    algebraMap R κ (D (a • x : R)) = a • algebraMap R κ (D x : R) := by
  -- The extra Leibniz term vanishes in the residue field because `x` lies in the maximal ideal.
  have hx0 : algebraMap R κ (x : R) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 x.2
  -- Rewrite the scalar multiple as a product and then discard the term multiplied by `x`.
  calc
    algebraMap R κ (D (a • x : R))
        = algebraMap R κ ((a : R) * D (x : R) + (x : R) * D a) := by
          simpa [smul_eq_mul] using congrArg (algebraMap R κ) (D.leibniz a (x : R))
    _ = algebraMap R κ ((a : R) * D (x : R)) +
          algebraMap R κ ((x : R) * D a) := by
          simp
    _ = algebraMap R κ ((a : R) * D (x : R)) + 0 := by
          simp
    _ = algebraMap R κ a * algebraMap R κ (D x : R) := by
          simp
    _ = a • algebraMap R κ (D x : R) := by
          rfl

/-- Helper for Lemma 15.48.3: the residue of a derivation kills products of maximal-ideal
elements. -/
theorem derivation_residue_linear_map_mul
    (D : Derivation ℤ R R) (x y : maximalIdeal R) :
    algebraMap R κ (D (x * y : maximalIdeal R) : R) = 0 := by
  have hx0 : algebraMap R κ (x : R) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 x.2
  have hy0 : algebraMap R κ (y : R) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 y.2
  -- Apply Leibniz and note that both coefficients from the maximal ideal vanish in the residue field.
  calc
    algebraMap R κ (D (x * y : maximalIdeal R) : R)
        = algebraMap R κ ((x : R) * D (y : R) + (y : R) * D (x : R)) := by
          simpa [smul_eq_mul] using congrArg (algebraMap R κ) (D.leibniz (x : R) (y : R))
    _ = algebraMap R κ (x : R) * algebraMap R κ (D y : R) +
          algebraMap R κ (y : R) * algebraMap R κ (D x : R) := by
          simp
    _ = 0 := by
          rw [hx0, hy0]
          simp

/-- Helper for Lemma 15.48.3: the residue of a derivation is additive on the maximal ideal. -/
theorem derivation_residue_linear_map_add
    (D : Derivation ℤ R R) (x y : maximalIdeal R) :
    algebraMap R κ (D (x + y : maximalIdeal R) : R) =
      algebraMap R κ (D x : R) + algebraMap R κ (D y : R) := by
  -- The derivation respects addition before passing to the residue field.
  simp

/-- Helper for Lemma 15.48.3: the residue of a derivation defines an `R`-linear map on the
maximal ideal. -/
noncomputable def derivation_residue_linear
    (D : Derivation ℤ R R) : maximalIdeal R →ₗ[R] κ :=
  { toFun := fun x ↦ algebraMap R κ (D x : R)
    map_add' := derivation_residue_linear_map_add (R := R) D
    map_smul' := derivation_residue_linear_map_smul (R := R) D }

/-- Helper for Lemma 15.48.3: the residue of a derivation descends to an `R`-linear functional on
the cotangent space. -/
noncomputable def derivation_residue_linear_on_cotangent_R
    (D : Derivation ℤ R R) : CotangentSpace R →ₗ[R] κ :=
  Ideal.Cotangent.lift (derivation_residue_linear (R := R) D)
    (derivation_residue_linear_map_mul (R := R) D)

/-- Helper for Lemma 15.48.3: the descended cotangent functional is compatible with residue-field
scalars. -/
theorem derivation_residue_linear_on_cotangent_R_map_smul
    (D : Derivation ℤ R R) (c : κ) (x : CotangentSpace R) :
    derivation_residue_linear_on_cotangent_R (R := R) D (c • x) =
      c • derivation_residue_linear_on_cotangent_R (R := R) D x := by
  -- Reduce both the scalar and the cotangent class to representatives over `R`.
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
  obtain ⟨y, rfl⟩ := Ideal.toCotangent_surjective (maximalIdeal R) x
  -- After choosing representatives, this is just `R`-linearity of the descended map.
  change
    derivation_residue_linear_on_cotangent_R (R := R) D
        (r • (maximalIdeal R).toCotangent y) =
      r •
        derivation_residue_linear_on_cotangent_R (R := R) D ((maximalIdeal R).toCotangent y)
  exact
    (derivation_residue_linear_on_cotangent_R (R := R) D).map_smul r
      ((maximalIdeal R).toCotangent y)

/-- Helper for Lemma 15.48.3: a derivation induces a residue-field linear functional on the
cotangent space. -/
noncomputable def derivation_residue_linear_on_cotangent
    (D : Derivation ℤ R R) : CotangentSpace R →ₗ[κ] κ :=
  { toFun := derivation_residue_linear_on_cotangent_R (R := R) D
    map_add' := (derivation_residue_linear_on_cotangent_R (R := R) D).map_add
    map_smul' := derivation_residue_linear_on_cotangent_R_map_smul (R := R) D }

/-- Helper for Lemma 15.48.3: the descended cotangent functional evaluates on a cotangent class by
taking the residue of the derivation. -/
@[simp] theorem derivation_residue_linear_on_cotangent_toCotangent
    (D : Derivation ℤ R R) (x : maximalIdeal R) :
    derivation_residue_linear_on_cotangent (R := R) D ((maximalIdeal R).toCotangent x) =
      algebraMap R κ (D x : R) := by
  -- The descended functional agrees with its defining map on representatives.
  simpa [derivation_residue_linear_on_cotangent, derivation_residue_linear_on_cotangent_R,
    derivation_residue_linear] using
    Ideal.Cotangent.lift_toCotangent (derivation_residue_linear (R := R) D)
      (derivation_residue_linear_map_mul (R := R) D) x

/-- Helper for Lemma 15.48.3: a unit Jacobian determinant forces the cotangent classes of the
chosen family to be linearly independent. -/
theorem jacobian_det_isUnit_implies_cotangent_linearIndependent
    (x : Fin m → maximalIdeal R) (D : Fin m → Derivation ℤ R R)
    (hdet : IsUnit (Matrix.det fun i j ↦ D i (x j : R))) :
    LinearIndependent κ (fun j ↦ (maximalIdeal R).toCotangent (x j)) := by
  classical
  let A : Matrix (Fin m) (Fin m) κ :=
    fun i j ↦ algebraMap R κ (D i (x j : R))
  have hA_det_unit : IsUnit A.det := by
    -- Map the unit determinant into the residue field.
    simpa [A, RingHom.map_det] using hdet.map (algebraMap R κ)
  have hA_det_ne_zero : A.det ≠ 0 :=
    isUnit_iff_ne_zero.mp hA_det_unit
  rw [Fintype.linearIndependent_iff]
  intro c hc
  -- Apply the descended derivation functionals to the putative linear relation.
  have hmul : Matrix.mulVec A c = 0 := by
    ext i
    have hEval :=
      congrArg (derivation_residue_linear_on_cotangent (R := R) (D i)) hc
    change ∑ j, A i j * c j = 0
    have hEval' : ∑ j, A i j * c j = 0 := by
      simpa [A, derivation_residue_linear_on_cotangent_toCotangent, mul_comm] using hEval
    exact hEval'
  -- Invertibility of the residue Jacobian kills the coefficient vector.
  intro i
  exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero hA_det_ne_zero hmul) i

/-- Helper for Lemma 15.48.3: spanning the cotangent space by `n` cotangent classes yields a
regular system of parameters of length `n`. -/
theorem isRegularSystemOfParameters_of_cotangent_span_top
    {n : ℕ} (z : Fin n → maximalIdeal R)
    (hn : n = (maximalIdeal R).spanFinrank)
    (hspan :
      Submodule.span κ (Set.range fun i ↦ (maximalIdeal R).toCotangent (z i)) = ⊤) :
    IsRegularSystemOfParameters z := by
  -- Translate cotangent spanning back to generation of the maximal ideal.
  have hcot_range :
      (maximalIdeal R).toCotangent '' Set.range z =
        Set.range fun i ↦ (maximalIdeal R).toCotangent (z i) := by
    ext y
    constructor
    · rintro ⟨w, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨z i, ⟨i, rfl⟩, rfl⟩
  have hspanR : Submodule.span R (Set.range z) = ⊤ := by
    have hspanImage :
        Submodule.span κ ((maximalIdeal R).toCotangent '' Set.range z) = ⊤ := by
      simpa [hcot_range] using hspan
    exact
      (IsLocalRing.CotangentSpace.span_image_eq_top_iff
        (R := R) (s := Set.range z)).1 hspanImage
  have hsubtype_range :
      (((↑) : maximalIdeal R → R) '' Set.range z) =
        Set.range fun i ↦ ((z i : maximalIdeal R) : R) := by
    ext r
    constructor
    · rintro ⟨w, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨z i, ⟨i, rfl⟩, rfl⟩
  have hparam : parameterIdeal z = maximalIdeal R := by
    rw [IsLocalRing.parameterIdeal_eq_span]
    have hmap := congrArg (Submodule.map (maximalIdeal R).subtype) hspanR
    simpa [Submodule.map_top, Submodule.map_span, hsubtype_range] using hmap
  have hdim : ringKrullDim R = n := by
    have hregdim : (maximalIdeal R).spanFinrank = ringKrullDim R :=
      (isRegularLocalRing_iff R).1 inferInstance
    simpa [hn] using hregdim.symm
  -- With the dimension fixed, generation of the maximal ideal is the owner criterion.
  exact (IsLocalRing.isRegularSystemOfParameters_iff_of_ringKrullDim_eq hdim z).2 hparam

/-- Helper for Lemma 15.48.3: a linearly independent cotangent family can be completed by extra
cotangent classes whose span is all of `CotangentSpace R`. -/
theorem cotangent_append_span_top_of_linearIndependent
    (x : Fin m → maximalIdeal R)
    (hlin : LinearIndependent κ (fun j ↦ (maximalIdeal R).toCotangent (x j))) :
    ∃ y : Fin ((maximalIdeal R).spanFinrank - m) → maximalIdeal R,
      Submodule.span κ (Set.range fun i ↦ (maximalIdeal R).toCotangent ((Fin.append x y) i)) = ⊤ := by
  -- Route correction: package the quotient-basis extension step here so the closing theorem only
  -- consumes a span-top witness for `Fin.append x y`.
  let v : Fin m → CotangentSpace R := fun j ↦ (maximalIdeal R).toCotangent (x j)
  let V : Submodule κ (CotangentSpace R) := Submodule.span κ (Set.range v)
  let bW : Module.Basis (Fin m) κ V := by
    -- The independent cotangent classes form a basis of their span.
    change Module.Basis (Fin m) κ (Submodule.span κ (Set.range v))
    exact Module.Basis.span hlin
  have hbW_apply : ∀ j, (((bW j : V) : CotangentSpace R)) = v j := by
    -- Coercing the span basis back to the cotangent space recovers the original family.
    intro j
    change ↑((Module.Basis.span hlin) j) = v j
    simp [v]
  have hbW_finrank : Module.finrank κ V = m := by
    -- The span basis has exactly `m` vectors.
    simpa [bW] using Module.finrank_eq_card_basis bW
  have hquot_dim : Module.finrank κ (CotangentSpace R ⧸ V) = (maximalIdeal R).spanFinrank - m := by
    -- The quotient dimension is the cotangent dimension minus the span dimension of `x`.
    have hsum := Submodule.finrank_quotient_add_finrank V
    have hdimR : Module.finrank κ (CotangentSpace R) = (maximalIdeal R).spanFinrank := by
      symm
      exact IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace (R := R)
    rw [hbW_finrank, hdimR] at hsum
    omega
  let bQ0 : Module.Basis (Fin (Module.finrank κ (CotangentSpace R ⧸ V))) κ (CotangentSpace R ⧸ V) :=
    Module.finBasis κ (CotangentSpace R ⧸ V)
  let bQ : Module.Basis (Fin ((maximalIdeal R).spanFinrank - m)) κ (CotangentSpace R ⧸ V) :=
    bQ0.reindex (finCongr hquot_dim)
  let b : Module.Basis (Fin m ⊕ Fin ((maximalIdeal R).spanFinrank - m)) κ (CotangentSpace R) :=
    bW.sumQuot bQ
  have hy :
      ∃ y : Fin ((maximalIdeal R).spanFinrank - m) → maximalIdeal R,
        ∀ j, (maximalIdeal R).toCotangent (y j) = b (Sum.inr j) := by
    -- Surjectivity of `toCotangent` lifts the complementary basis vectors to `maximalIdeal R`.
    choose y hy using fun j ↦ Ideal.toCotangent_surjective (maximalIdeal R) (b (Sum.inr j))
    exact ⟨y, hy⟩
  rcases hy with ⟨y, hy⟩
  refine ⟨y, ?_⟩
  have happend :
      (fun i : Fin (m + ((maximalIdeal R).spanFinrank - m)) ↦
          (maximalIdeal R).toCotangent ((Fin.append x y) i)) =
        b ∘ finSumFinEquiv.symm := by
    -- The appended cotangent family is exactly the `sumQuot` basis after reindexing.
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp only [Function.comp_apply, Fin.append_left]
      rw [show finSumFinEquiv.symm (Fin.castAdd ((maximalIdeal R).spanFinrank - m) j) = Sum.inl j by
        simp]
      rw [Module.Basis.sumQuot_inl]
      symm
      exact hbW_apply j
    · intro j
      simp only [Function.comp_apply, Fin.append_right]
      rw [show finSumFinEquiv.symm (Fin.natAdd m j) = Sum.inr j by simp]
      exact hy j
  have hrangeb : Set.range (b ∘ finSumFinEquiv.symm) = Set.range b := by
    -- Reindexing a family by an equivalence does not change its range.
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨finSumFinEquiv.symm i, rfl⟩
    · rintro ⟨s, rfl⟩
      exact ⟨finSumFinEquiv s, by simp⟩
  -- Since `b` is a basis, the appended family spans all of the cotangent space.
  calc
    Submodule.span κ (Set.range fun i ↦
        (maximalIdeal R).toCotangent ((Fin.append x y) i)) =
      Submodule.span κ (Set.range (b ∘ finSumFinEquiv.symm)) := by
        rw [happend]
    _ = Submodule.span κ (Set.range b) := by
        rw [hrangeb]
    _ = ⊤ := Module.Basis.span_eq b

/-- Helper for Lemma 15.48.3: linearly independent cotangent classes extend to a regular system of
parameters. -/
theorem isPartOfRegularSystemOfParameters_of_cotangent_linearIndependent
    (x : Fin m → maximalIdeal R)
    (hlin : LinearIndependent κ (fun j ↦ (maximalIdeal R).toCotangent (x j))) :
    IsPartOfRegularSystemOfParameters (maximalIdeal R).spanFinrank x := by
  -- First append complementary cotangent lifts so that the combined family spans the cotangent
  -- space, then invoke the span-top criterion for regular systems of parameters.
  obtain ⟨y, hspan⟩ :=
    cotangent_append_span_top_of_linearIndependent (R := R) x hlin
  refine ⟨y, ?_⟩
  -- The appended family has total length `(maximalIdeal R).spanFinrank`.
  apply isRegularSystemOfParameters_of_cotangent_span_top (R := R) (z := Fin.append x y)
  · have hspanFinrank :
        (maximalIdeal R).spanFinrank = Module.finrank κ (CotangentSpace R) :=
      IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace (R := R)
    rw [hspanFinrank]
    exact Nat.add_sub_of_le (show m ≤ Module.finrank κ (CotangentSpace R) by
      simpa using hlin.cardinalMk_le_finrank)
  · simpa using hspan

/-- Lemma 15.48.3 owner bridge: if the Jacobian determinant of the chosen derivations
`det (D i (x j))` is a unit, then `x` is part of a regular system of parameters. -/
theorem isPartOfRegularSystemOfParameters_of_jacobian_det_isUnit
    (x : Fin m → maximalIdeal R) (D : Fin m → Derivation ℤ R R)
    (hdet : IsUnit (Matrix.det fun i j ↦ D i (x j : R))) :
    IsPartOfRegularSystemOfParameters (maximalIdeal R).spanFinrank x := by
  -- First pass to the cotangent space via the Jacobian determinant criterion.
  have hlin :
      LinearIndependent κ (fun j ↦ (maximalIdeal R).toCotangent (x j)) :=
    jacobian_det_isUnit_implies_cotangent_linearIndependent (R := R) x D hdet
  -- Then extend those cotangent classes to a full regular system of parameters.
  exact isPartOfRegularSystemOfParameters_of_cotangent_linearIndependent (R := R) x hlin

/-- Lemma 15.48.3 (1), derived owner view: if the Jacobian determinant of the chosen absolute
derivations `D i : Derivation ℤ R R` is a unit, then `R ⧸ parameterIdeal x` is a regular local
ring. -/
theorem isRegularLocalRing_quotient_parameterIdeal_of_jacobian_det_isUnit
    (x : Fin m → maximalIdeal R) (D : Fin m → Derivation ℤ R R)
    (hdet : IsUnit (Matrix.det fun i j ↦ D i (x j : R))) :
    IsRegularLocalRing (R ⧸ parameterIdeal x) :=
  IsPartOfRegularSystemOfParameters.isRegularLocalRing_quotient_parameterIdeal
    (isPartOfRegularSystemOfParameters_of_jacobian_det_isUnit x D hdet)

/-- Lemma 15.48.3 (2), derived owner view: under the same hypotheses, the underlying list of the
chosen family `x`, encoded as `List.ofFn fun i ↦ (x i : R)`, is a regular sequence in `R`. -/
theorem isRegular_of_jacobian_det_isUnit
    (x : Fin m → maximalIdeal R) (D : Fin m → Derivation ℤ R R)
    (hdet : IsUnit (Matrix.det fun i j ↦ D i (x j : R))) :
    IsRegular R (List.ofFn fun i ↦ (x i : R)) :=
  IsPartOfRegularSystemOfParameters.isRegular
    (isPartOfRegularSystemOfParameters_of_jacobian_det_isUnit x D hdet)

end
