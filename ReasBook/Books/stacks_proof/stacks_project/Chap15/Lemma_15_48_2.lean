import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Localization.Away.Basic
import StacksProject_2024.Chap10.Lemma_10_106_3
import StacksProject_2024.Chap10.Definition_10_60_10
import StacksProject_2024.Chap10.Definition_10_110_7
import StacksProject_2024.Chap15.PrincipalIdeal
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped RightActions

open IsLocalRing

noncomputable section

section

variable {R : Type u} [CommRing R] [IsRegularRing R]
variable {f : R}

/- Domain-style sampling:
* primary domain: regular rings, regular local rings on localizations, and absolute derivations on
  a commutative ring;
* sampled owner declarations:
  `IsRegularRing`,
  `IsRegularLocalRing`,
  `IsLocalRing.IsRegularSystemOfParameters.isRegularLocalRing_quotient_parameterIdeal`,
  `Derivation ℤ R R`;
* owner abstraction: the ambient owner is `IsRegularRing R`, localized in the proof sketch through
  the regular-local owner on prime localizations; the derivation datum is the canonical mathlib
  owner `Derivation ℤ R R`.

Primitive vs. derived:
* primitive data: a concrete derivation `D : Derivation ℤ R R` and the unit condition on the class
  of `D f` in `R ⧸ (f)`;
* derived API: the source-facing existential corollary, which packages the same primitive data in
  the textbook existence form.

Source/core/bridge triage:
* source-facing: `isRegularRing_quotient_principalIdeal_of_exists_derivation`, matching the
  textbook existence hypothesis;
* core/canonical: `IsRegularRing`, `IsRegularLocalRing`, and `Derivation ℤ R R`;
* bridge/view: `Derivation.isRegularRing_quotient_principalIdeal_of_isUnit`, which exposes the
  primitive derivation datum directly from the owner object.
-/

namespace Derivation

omit [IsRegularRing R] in
/-- Helper for Lemma 15.48.2: a derivation on `R` has a unique extension to any localization
`A` of `R` at a submonoid `S`. -/
private theorem existsUnique_localizationExtension_aux
    (D : Derivation ℤ R R) (S : Submonoid R) (A : Type v)
    [CommRing A] [Algebra R A] [IsLocalization S A] :
    ∃! Dloc : Derivation ℤ A A,
        Dloc.compAlgebraMap R = (Algebra.linearMap R A).compDer D := by
  classical
  let φ : R →ₐ[ℤ] TrivSqZeroExt A A := by
    refine
      { toFun := fun r ↦ (algebraMap R A r, algebraMap R A (D r))
        map_one' := ?_
        map_mul' := ?_
        map_zero' := ?_
        map_add' := ?_
        commutes' := ?_ }
    · ext <;> simp
    · intro x y
      ext <;> simp [Derivation.leibniz, mul_comm]
    · ext <;> simp
    · intro x y
      ext <;> simp
    · intro n
      ext <;> simp
  have hφ_units : ∀ y : S, IsUnit (φ y) := by
    intro y
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
    simpa [φ] using (IsLocalization.map_units A y)
  let ψ : A →ₐ[ℤ] TrivSqZeroExt A A := IsLocalization.liftAlgHom (S := A) (f := φ) hφ_units
  have hψ : ψ.comp (IsScalarTower.toAlgHom ℤ R A) = φ := by
    -- The localization lift is characterized by its values on the image of `R`.
    apply AlgHom.ext
    intro r
    change IsLocalization.lift hφ_units ((algebraMap R A) r) = φ r
    simpa [ψ, IsLocalization.liftAlgHom] using IsLocalization.lift_eq hφ_units r
  have hfst_ring : ((TrivSqZeroExt.fstHom ℤ A A).comp ψ).toRingHom = RingHom.id A := by
    -- The first component is the unique ring endomorphism of the localization extending `R → A`.
    apply IsLocalization.ringHom_ext S
    ext r
    simpa [φ] using congrArg TrivSqZeroExt.fst (AlgHom.congr_fun hψ r)
  have hfst_apply (a : A) : TrivSqZeroExt.fst (ψ a) = a := by
    exact RingHom.congr_fun hfst_ring a
  let Dlin : A →ₗ[ℤ] A :=
    (TrivSqZeroExt.sndHom A A).restrictScalars ℤ ∘ₗ ψ.toLinearMap
  have hDlin : ∀ a b : A, Dlin (a * b) = a • Dlin b + b • Dlin a := by
    intro a b
    -- The second component of multiplication in the square-zero extension satisfies Leibniz.
    change TrivSqZeroExt.snd (ψ (a * b)) = a • TrivSqZeroExt.snd (ψ b) + b • TrivSqZeroExt.snd (ψ a)
    rw [map_mul, TrivSqZeroExt.snd_mul, hfst_apply, hfst_apply]
    simp [mul_comm]
  let Dloc : Derivation ℤ A A := Derivation.mk' Dlin hDlin
  refine ⟨Dloc, ?_, ?_⟩
  · -- Restricting the square-zero lift back to `R` recovers the original derivation.
    ext r
    simpa [φ] using congrArg TrivSqZeroExt.snd (AlgHom.congr_fun hψ r)
  · intro D' hD'
    let φ' : A →ₐ[ℤ] TrivSqZeroExt A A := by
      refine
        { toFun := fun a ↦ (a, D' a)
          map_one' := ?_
          map_mul' := ?_
          map_zero' := ?_
          map_add' := ?_
          commutes' := ?_ }
      · ext <;> simp
      · intro x y
        ext <;> simp [D'.leibniz, mul_comm]
      · ext <;> simp
      · intro x y
        ext <;> simp
      · intro n
        ext <;> simp
    have hφ' : φ'.comp (IsScalarTower.toAlgHom ℤ R A) = φ := by
      -- Any other extension with the same restriction agrees on the image of `R`.
      apply AlgHom.ext
      intro r
      ext
      · simp [φ, φ']
      · simpa [φ, φ'] using congr_fun hD' r
    have hφ'_ring : φ'.toRingHom = ψ.toRingHom := by
      -- Ring maps out of a localization are determined by their values on the base ring.
      apply IsLocalization.ringHom_ext S
      apply RingHom.ext
      intro r
      exact (AlgHom.congr_fun hφ' r).trans (AlgHom.congr_fun hψ r).symm
    ext a
    simpa [Dloc, Dlin, φ'] using congrArg TrivSqZeroExt.snd (RingHom.congr_fun hφ'_ring a)

/-- Helper for Lemma 15.48.2: the canonical extension of a derivation to a localization. -/
noncomputable def localizationExtension (D : Derivation ℤ R R) (S : Submonoid R) (A : Type v)
    [CommRing A] [Algebra R A] [IsLocalization S A] :
    Derivation ℤ A A :=
  (existsUnique_localizationExtension_aux (R := R) D S A).choose

omit [IsRegularRing R] in
/-- Helper for Lemma 15.48.2: the localization extension agrees with the original derivation on
the image of `R`. -/
theorem localizationExtension_compAlgebraMap
    (D : Derivation ℤ R R) (S : Submonoid R) (A : Type v)
    [CommRing A] [Algebra R A] [IsLocalization S A] :
    (D.localizationExtension S A).compAlgebraMap R =
      (Algebra.linearMap R A).compDer D :=
  (existsUnique_localizationExtension_aux (R := R) D S A).choose_spec.left

omit [IsRegularRing R] in
/-- Helper for Lemma 15.48.2: the localization extension evaluates on `algebraMap R A r` by
mapping `D r` into the localization. -/
@[simp] theorem localizationExtension_algebraMap
    (D : Derivation ℤ R R) (S : Submonoid R) (A : Type v)
    [CommRing A] [Algebra R A] [IsLocalization S A] (r : R) :
    D.localizationExtension S A (algebraMap R A r) = algebraMap R A (D r) :=
  congr_fun (D.localizationExtension_compAlgebraMap S A) r

end Derivation

section LocalHelpers

variable {A : Type u} [CommRing A] [IsRegularLocalRing A]

local notation "κ" => ResidueField A

/-- Helper for Lemma 15.48.2: the residue of a derivation is `A`-linear on the maximal ideal. -/
theorem derivation_residue_linear_map_smul
    (Δ : Derivation ℤ A A) (a : A) (x : maximalIdeal A) :
    algebraMap A κ (Δ (a • x : A)) = a • algebraMap A κ (Δ x : A) := by
  -- The extra Leibniz term vanishes in the residue field because `x` lies in the maximal ideal.
  have hx0 : algebraMap A κ (x : A) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 x.2
  -- Rewrite the scalar multiple as a product and then discard the term multiplied by `x`.
  calc
    algebraMap A κ (Δ (a • x : A))
        = algebraMap A κ ((a : A) * Δ (x : A) + (x : A) * Δ a) := by
          simpa [smul_eq_mul] using congrArg (algebraMap A κ) (Δ.leibniz a (x : A))
    _ = algebraMap A κ ((a : A) * Δ (x : A)) +
          algebraMap A κ ((x : A) * Δ a) := by
          simp
    _ = algebraMap A κ ((a : A) * Δ (x : A)) + 0 := by
          simp
    _ = algebraMap A κ a * algebraMap A κ (Δ x : A) := by
          simp
    _ = a • algebraMap A κ (Δ x : A) := by
          rfl

/-- Helper for Lemma 15.48.2: the residue of a derivation kills products of maximal-ideal
elements. -/
theorem derivation_residue_linear_map_mul
    (Δ : Derivation ℤ A A) (x y : maximalIdeal A) :
    algebraMap A κ (Δ (x * y : maximalIdeal A) : A) = 0 := by
  have hx0 : algebraMap A κ (x : A) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 x.2
  have hy0 : algebraMap A κ (y : A) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 y.2
  -- Apply Leibniz and note that both coefficients from the maximal ideal vanish in the residue field.
  calc
    algebraMap A κ (Δ (x * y : maximalIdeal A) : A)
        = algebraMap A κ ((x : A) * Δ (y : A) + (y : A) * Δ (x : A)) := by
          simpa [smul_eq_mul] using congrArg (algebraMap A κ) (Δ.leibniz (x : A) (y : A))
    _ = algebraMap A κ (x : A) * algebraMap A κ (Δ y : A) +
          algebraMap A κ (y : A) * algebraMap A κ (Δ x : A) := by
          simp
    _ = 0 := by
          rw [hx0, hy0]
          simp

/-- Helper for Lemma 15.48.2: the residue of a derivation is additive on the maximal ideal. -/
theorem derivation_residue_linear_map_add
    (Δ : Derivation ℤ A A) (x y : maximalIdeal A) :
    algebraMap A κ (Δ (x + y : maximalIdeal A) : A) =
      algebraMap A κ (Δ x : A) + algebraMap A κ (Δ y : A) := by
  -- Additivity survives passage to the residue field unchanged.
  simp

/-- Helper for Lemma 15.48.2: the residue of a derivation defines an `A`-linear map on the
maximal ideal. -/
noncomputable def derivation_residue_linear
    (Δ : Derivation ℤ A A) : maximalIdeal A →ₗ[A] κ :=
  { toFun := fun x ↦ algebraMap A κ (Δ x : A)
    map_add' := derivation_residue_linear_map_add (A := A) Δ
    map_smul' := derivation_residue_linear_map_smul (A := A) Δ }

/-- Helper for Lemma 15.48.2: the residue of a derivation descends to the cotangent space. -/
noncomputable def derivation_residue_linear_on_cotangent_R
    (Δ : Derivation ℤ A A) : CotangentSpace A →ₗ[A] κ :=
  Ideal.Cotangent.lift (derivation_residue_linear (A := A) Δ)
    (derivation_residue_linear_map_mul (A := A) Δ)

/-- Helper for Lemma 15.48.2: the descended cotangent functional is compatible with residue-field
scalars. -/
theorem derivation_residue_linear_on_cotangent_R_map_smul
    (Δ : Derivation ℤ A A) (c : κ) (x : CotangentSpace A) :
    derivation_residue_linear_on_cotangent_R (A := A) Δ (c • x) =
      c • derivation_residue_linear_on_cotangent_R (A := A) Δ x := by
  -- Reduce both the scalar and the cotangent class to representatives over `A`.
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
  obtain ⟨y, rfl⟩ := Ideal.toCotangent_surjective (maximalIdeal A) x
  -- After choosing representatives, this is just `A`-linearity of the descended map.
  change
    derivation_residue_linear_on_cotangent_R (A := A) Δ
        (a • (maximalIdeal A).toCotangent y) =
      a •
        derivation_residue_linear_on_cotangent_R (A := A) Δ ((maximalIdeal A).toCotangent y)
  exact
    (derivation_residue_linear_on_cotangent_R (A := A) Δ).map_smul a
      ((maximalIdeal A).toCotangent y)

/-- Helper for Lemma 15.48.2: a derivation induces a residue-field linear functional on the
cotangent space. -/
noncomputable def derivation_residue_linear_on_cotangent
    (Δ : Derivation ℤ A A) : CotangentSpace A →ₗ[κ] κ :=
  { toFun := derivation_residue_linear_on_cotangent_R (A := A) Δ
    map_add' := (derivation_residue_linear_on_cotangent_R (A := A) Δ).map_add
    map_smul' := derivation_residue_linear_on_cotangent_R_map_smul (A := A) Δ }

/-- Helper for Lemma 15.48.2: the descended cotangent functional evaluates by taking the residue
of the derivation. -/
@[simp] theorem derivation_residue_linear_on_cotangent_toCotangent
    (Δ : Derivation ℤ A A) (x : maximalIdeal A) :
    derivation_residue_linear_on_cotangent (A := A) Δ ((maximalIdeal A).toCotangent x) =
      algebraMap A κ (Δ x : A) := by
  -- The descended functional agrees with its defining map on representatives.
  simpa [derivation_residue_linear_on_cotangent, derivation_residue_linear_on_cotangent_R,
    derivation_residue_linear] using
    Ideal.Cotangent.lift_toCotangent (derivation_residue_linear (A := A) Δ)
      (derivation_residue_linear_map_mul (A := A) Δ) x

/-- Helper for Lemma 15.48.2: a singleton parameter ideal is the corresponding principal ideal. -/
theorem parameterIdeal_fin1_eq_principalIdeal (x : maximalIdeal A) :
    IsLocalRing.parameterIdeal (fun _ : Fin 1 ↦ x) = principalIdeal (x : A) := by
  -- Both ideals are generated by the same singleton subset of `A`.
  rw [IsLocalRing.parameterIdeal_eq_span, principalIdeal]
  congr
  ext y
  constructor
  · rintro ⟨i, rfl⟩
    simp
  · rintro rfl
    exact ⟨0, rfl⟩

/-- Helper for Lemma 15.48.2: cotangent classes spanning the cotangent space give a regular system
of parameters. -/
theorem isRegularSystemOfParameters_of_cotangent_span_top
    {n : ℕ} (z : Fin n → maximalIdeal A)
    (hn : n = (maximalIdeal A).spanFinrank)
    (hspan :
      Submodule.span κ (Set.range fun i ↦ (maximalIdeal A).toCotangent (z i)) = ⊤) :
    IsRegularSystemOfParameters z := by
  -- Translate cotangent spanning back to generation of the maximal ideal.
  have hcot_range :
      (maximalIdeal A).toCotangent '' Set.range z =
        Set.range fun i ↦ (maximalIdeal A).toCotangent (z i) := by
    ext y
    constructor
    · rintro ⟨w, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨z i, ⟨i, rfl⟩, rfl⟩
  have hspanA : Submodule.span A (Set.range z) = ⊤ := by
    have hspanImage :
        Submodule.span κ ((maximalIdeal A).toCotangent '' Set.range z) = ⊤ := by
      simpa [hcot_range] using hspan
    exact
      (IsLocalRing.CotangentSpace.span_image_eq_top_iff
        (R := A) (s := Set.range z)).1 hspanImage
  have hsubtype_range :
      (((↑) : maximalIdeal A → A) '' Set.range z) =
        Set.range fun i ↦ ((z i : maximalIdeal A) : A) := by
    ext r
    constructor
    · rintro ⟨w, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨z i, ⟨i, rfl⟩, rfl⟩
  have hparam : parameterIdeal z = maximalIdeal A := by
    rw [IsLocalRing.parameterIdeal_eq_span]
    have hmap := congrArg (Submodule.map (maximalIdeal A).subtype) hspanA
    simpa [Submodule.map_top, Submodule.map_span, hsubtype_range] using hmap
  have hdim : ringKrullDim A = n := by
    have hregdim : (maximalIdeal A).spanFinrank = ringKrullDim A :=
      (isRegularLocalRing_iff A).1 inferInstance
    simpa [hn] using hregdim.symm
  -- With the dimension fixed, generation of the maximal ideal is the owner criterion.
  exact (IsLocalRing.isRegularSystemOfParameters_iff_of_ringKrullDim_eq hdim z).2 hparam

/-- Helper for Lemma 15.48.2: a linearly independent cotangent family can be completed by extra
cotangent classes whose span is all of `CotangentSpace A`. -/
theorem cotangent_append_span_top_of_linearIndependent
    {m : ℕ} (x : Fin m → maximalIdeal A)
    (hlin : LinearIndependent κ (fun j ↦ (maximalIdeal A).toCotangent (x j))) :
    ∃ y : Fin ((maximalIdeal A).spanFinrank - m) → maximalIdeal A,
      Submodule.span κ (Set.range fun i ↦ (maximalIdeal A).toCotangent ((Fin.append x y) i)) = ⊤ := by
  -- Route correction: complete the given cotangent family to a basis via `sumQuot`, then lift the
  -- complementary basis vectors back through `toCotangent`.
  let v : Fin m → CotangentSpace A := fun j ↦ (maximalIdeal A).toCotangent (x j)
  let V : Submodule κ (CotangentSpace A) := Submodule.span κ (Set.range v)
  let bW : Module.Basis (Fin m) κ V := by
    -- The independent cotangent classes form a basis of their span.
    change Module.Basis (Fin m) κ (Submodule.span κ (Set.range v))
    exact Module.Basis.span hlin
  have hbW_apply : ∀ j, (((bW j : V) : CotangentSpace A)) = v j := by
    -- Coercing the span basis back to the cotangent space recovers the original family.
    intro j
    change ↑((Module.Basis.span hlin) j) = v j
    simp [v]
  have hbW_finrank : Module.finrank κ V = m := by
    -- The span basis has exactly `m` vectors.
    simpa [bW] using Module.finrank_eq_card_basis bW
  have hquot_dim : Module.finrank κ (CotangentSpace A ⧸ V) = (maximalIdeal A).spanFinrank - m := by
    -- The quotient dimension is the cotangent dimension minus the span dimension of `x`.
    have hsum := Submodule.finrank_quotient_add_finrank V
    have hdimA : Module.finrank κ (CotangentSpace A) = (maximalIdeal A).spanFinrank := by
      symm
      exact IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace (R := A)
    rw [hbW_finrank, hdimA] at hsum
    omega
  let bQ0 : Module.Basis (Fin (Module.finrank κ (CotangentSpace A ⧸ V))) κ (CotangentSpace A ⧸ V) :=
    Module.finBasis κ (CotangentSpace A ⧸ V)
  let bQ : Module.Basis (Fin ((maximalIdeal A).spanFinrank - m)) κ (CotangentSpace A ⧸ V) :=
    bQ0.reindex (finCongr hquot_dim)
  let b : Module.Basis (Fin m ⊕ Fin ((maximalIdeal A).spanFinrank - m)) κ (CotangentSpace A) :=
    bW.sumQuot bQ
  have hy :
      ∃ y : Fin ((maximalIdeal A).spanFinrank - m) → maximalIdeal A,
        ∀ j, (maximalIdeal A).toCotangent (y j) = b (Sum.inr j) := by
    -- Surjectivity of `toCotangent` lifts the complementary basis vectors to `maximalIdeal A`.
    choose y hy using fun j ↦ Ideal.toCotangent_surjective (maximalIdeal A) (b (Sum.inr j))
    exact ⟨y, hy⟩
  rcases hy with ⟨y, hy⟩
  refine ⟨y, ?_⟩
  have happend :
      (fun i : Fin (m + ((maximalIdeal A).spanFinrank - m)) ↦
          (maximalIdeal A).toCotangent ((Fin.append x y) i)) =
        b ∘ finSumFinEquiv.symm := by
    -- The appended cotangent family is exactly the `sumQuot` basis after reindexing.
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp only [Function.comp_apply, Fin.append_left]
      rw [show finSumFinEquiv.symm (Fin.castAdd ((maximalIdeal A).spanFinrank - m) j) = Sum.inl j by
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
        (maximalIdeal A).toCotangent ((Fin.append x y) i)) =
      Submodule.span κ (Set.range (b ∘ finSumFinEquiv.symm)) := by
        rw [happend]
    _ = Submodule.span κ (Set.range b) := by
        rw [hrangeb]
    _ = ⊤ := Module.Basis.span_eq b

/-- Helper for Lemma 15.48.2: linearly independent cotangent classes extend to a regular system of
parameters. -/
theorem isPartOfRegularSystemOfParameters_of_cotangent_linearIndependent
    {m : ℕ} (x : Fin m → maximalIdeal A)
    (hlin : LinearIndependent κ (fun j ↦ (maximalIdeal A).toCotangent (x j))) :
    IsPartOfRegularSystemOfParameters (maximalIdeal A).spanFinrank x := by
  -- First complete the independent cotangent family to one spanning the whole cotangent space.
  obtain ⟨y, hspan⟩ :=
    cotangent_append_span_top_of_linearIndependent (A := A) x hlin
  refine ⟨y, ?_⟩
  -- The completed family has the full regular-local length, so the span-top criterion applies.
  apply isRegularSystemOfParameters_of_cotangent_span_top (A := A) (z := Fin.append x y)
  · have hspanFinrank :
        (maximalIdeal A).spanFinrank = Module.finrank κ (CotangentSpace A) :=
      IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace (R := A)
    rw [hspanFinrank]
    exact Nat.add_sub_of_le (by simpa using hlin.cardinalMk_le_finrank)
  · simpa using hspan

/-- Helper for Lemma 15.48.2: an element outside `𝔪²` has nonzero cotangent class. -/
theorem toCotangent_ne_zero_of_not_mem_maximalIdeal_sq
    (x : maximalIdeal A) (hx : (x : A) ∉ maximalIdeal A ^ 2) :
    (maximalIdeal A).toCotangent x ≠ 0 := by
  -- The cotangent zero criterion is exactly the source bridge between `𝔪²` and the cotangent
  -- space.
  intro hzero
  exact hx ((Ideal.toCotangent_eq_zero (maximalIdeal A) x).1 hzero)

/-- Helper for Lemma 15.48.2: a nonzero cotangent class gives a linearly independent singleton
family. -/
theorem cotangent_singleton_linearIndependent_of_ne_zero
    (x : maximalIdeal A) (hx :
      (maximalIdeal A).toCotangent x ≠ 0) :
    LinearIndependent κ (fun _ : Fin 1 ↦ (maximalIdeal A).toCotangent x) := by
  -- In a one-element family, linear independence is the same as nonvanishing of that element.
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  fin_cases i
  have hscalar : c 0 • (maximalIdeal A).toCotangent x = 0 := by
    simpa using hc
  rcases smul_eq_zero.mp hscalar with hc0 | hzero
  · simpa using hc0
  · exact False.elim (hx hzero)

/-- Helper for Lemma 15.48.2: if an element of the maximal ideal is not in `𝔪²`, then the
singleton family is part of a regular system of parameters. -/
theorem isPartOfRegularSystemOfParameters_singleton_of_not_mem_maximalIdeal_sq
    (x : maximalIdeal A) (hx : (x : A) ∉ maximalIdeal A ^ 2) :
    IsPartOfRegularSystemOfParameters (maximalIdeal A).spanFinrank (fun _ : Fin 1 ↦ x) := by
  -- The source proof reduces the singleton case to nonvanishing of the cotangent class.
  have hlin :
      LinearIndependent κ (fun _ : Fin 1 ↦ (maximalIdeal A).toCotangent x) :=
    cotangent_singleton_linearIndependent_of_ne_zero (A := A) x
      (toCotangent_ne_zero_of_not_mem_maximalIdeal_sq (A := A) x hx)
  -- Once the one-element cotangent family is independent, the general extension lemma finishes.
  exact isPartOfRegularSystemOfParameters_of_cotangent_linearIndependent (A := A)
    (x := fun _ : Fin 1 ↦ x) hlin

/-- Helper for Lemma 15.48.2: if `x ∈ 𝔪²`, then every derivation sends `x` into `𝔪`. -/
theorem derivation_apply_mem_maximalIdeal_of_mem_maximalIdeal_sq
    (Δ : Derivation ℤ A A) (x : maximalIdeal A) (hx : (x : A) ∈ maximalIdeal A ^ 2) :
    Δ x ∈ maximalIdeal A := by
  -- The cotangent class of an element of `𝔪²` is zero.
  have htoCotangent : (maximalIdeal A).toCotangent x = 0 :=
    (Ideal.toCotangent_eq_zero (maximalIdeal A) x).2 hx
  -- Evaluating the descended functional on that zero class forces the residue of `Δ x` to vanish.
  have hresidue : algebraMap A κ (Δ x : A) = 0 := by
    simpa using
      congrArg (derivation_residue_linear_on_cotangent (A := A) Δ) htoCotangent
  -- Vanishing in the residue field is equivalent to membership in the maximal ideal.
  exact Ideal.Quotient.eq_zero_iff_mem.1 hresidue

/-- Helper for Lemma 15.48.2: in a regular local ring, quotienting by a principal element whose
derivative is a unit modulo that element again yields a regular local ring. -/
theorem isRegularLocalRing_quotient_principalIdeal_of_isUnit_local
    (Δ : Derivation ℤ A A) (x : maximalIdeal A)
    (hΔx : IsUnit (Ideal.Quotient.mk (principalIdeal (x : A)) (Δ x))) :
    IsRegularLocalRing (A ⧸ principalIdeal (x : A)) := by
  -- Route correction: with the singleton cotangent bridge restored, the source proof closes by
  -- ruling out `x ∈ 𝔪²` and then invoking the owner theorem for quotienting by a parameter ideal.
  have hx_not_sq : (x : A) ∉ maximalIdeal A ^ 2 := by
    intro hx_sq
    have hder_mem : Δ x ∈ maximalIdeal A :=
      derivation_apply_mem_maximalIdeal_of_mem_maximalIdeal_sq (A := A) Δ x hx_sq
    have hx_le_max :
        principalIdeal (x : A) ≤ maximalIdeal A := by
      rw [principalIdeal, Ideal.span_le]
      intro y hy
      rcases Set.mem_singleton_iff.mp hy with rfl
      exact x.2
    have hx_ne_top : principalIdeal (x : A) ≠ ⊤ := by
      intro hx_top
      exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top (top_le_iff.mp (hx_top ▸ hx_le_max))
    let π : A →+* A ⧸ principalIdeal (x : A) := Ideal.Quotient.mk (principalIdeal (x : A))
    letI : Nontrivial (A ⧸ principalIdeal (x : A)) := Ideal.Quotient.nontrivial_iff.2 hx_ne_top
    letI : IsLocalRing (A ⧸ principalIdeal (x : A)) :=
      IsLocalRing.of_surjective' π Ideal.Quotient.mk_surjective
    have hquot_mem : π (Δ x) ∈ maximalIdeal (A ⧸ principalIdeal (x : A)) := by
      -- The quotient map sends `𝔪` onto the maximal ideal of the quotient local ring.
      rw [← IsLocalRing.map_maximalIdeal_of_surjective π Ideal.Quotient.mk_surjective]
      exact Ideal.mem_map_of_mem π hder_mem
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hquot_mem
    exact hquot_mem hΔx
  have hpart :
      IsPartOfRegularSystemOfParameters (maximalIdeal A).spanFinrank (fun _ : Fin 1 ↦ x) :=
    isPartOfRegularSystemOfParameters_singleton_of_not_mem_maximalIdeal_sq (A := A) x hx_not_sq
  have hlocal_param :
      IsRegularLocalRing (A ⧸ IsLocalRing.parameterIdeal (fun _ : Fin 1 ↦ x)) :=
    IsPartOfRegularSystemOfParameters.isRegularLocalRing_quotient_parameterIdeal hpart
  let eParam :
      (A ⧸ IsLocalRing.parameterIdeal (fun _ : Fin 1 ↦ x)) ≃ₐ[A]
        (A ⧸ principalIdeal (x : A)) :=
    Ideal.quotientEquivAlgOfEq A (parameterIdeal_fin1_eq_principalIdeal (A := A) x)
  -- Rewrite the singleton parameter ideal as the principal ideal generated by `x`.
  exact IsRegularLocalRing.of_ringEquiv eParam.toRingEquiv

end LocalHelpers

-- Proof sketch: regularity is local on `Spec R`, so localize at a prime of `R ⧸ (f)` and reduce
-- to the case of a regular local ring. The local hypersurface step is proved above by ruling out
-- membership in `𝔪²` via the cotangent-space functional induced by the derivation.

omit [IsRegularRing R] in
/-- Helper for Lemma 15.48.2: after localizing at a prime, the image of `(f)` is the principal
ideal generated by the localized element `f`. -/
theorem map_principalIdeal_localizationAtPrime (p : PrimeSpectrum R) :
    Ideal.map (algebraMap R (Localization.AtPrime p.asIdeal)) (principalIdeal f) =
      principalIdeal (algebraMap R (Localization.AtPrime p.asIdeal) f) := by
  -- Both ideals are the span of the singleton image of `f`.
  simp [principalIdeal, Ideal.map_span, Set.image_singleton]

namespace Derivation

/-- Primitive-input bridge for Lemma 15.48.2: if `R` is a regular ring and
`D : Derivation ℤ R R` sends `f` to an element whose class in `R ⧸ (f)` is a unit, then
`R ⧸ (f)` is a regular ring. -/
theorem isRegularRing_quotient_principalIdeal_of_isUnit (D : Derivation ℤ R R)
    (hDf : IsUnit (Ideal.Quotient.mk (principalIdeal f) (D f))) :
    IsRegularRing (R ⧸ principalIdeal f) := by
  classical
  refine
    { toIsNoetherian := inferInstance
      isRegularLocalRing_atPrime := fun q ↦ ?_ }
  let p : PrimeSpectrum R := PrimeSpectrum.comap (Ideal.Quotient.mk (principalIdeal f)) q
  let Rp := Localization.AtPrime p.asIdeal
  letI : IsRegularLocalRing Rp :=
    IsRegularRing.isRegularLocalRing_atPrime p
  let Dp := D.localizationExtension p.asIdeal.primeCompl Rp
  let x : maximalIdeal Rp := by
    refine ⟨algebraMap R Rp f, ?_⟩
    -- The image of `f` lies in the maximal ideal because `f` maps to zero in `R ⧸ (f)`.
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p.asIdeal Rp]
    apply Ideal.mem_map_of_mem
    change Ideal.Quotient.mk (principalIdeal f) f ∈ q.asIdeal
    simpa using (q.asIdeal.zero_mem : (0 : R ⧸ principalIdeal f) ∈ q.asIdeal)
  have hDp_apply :
      Dp (algebraMap R Rp f) = algebraMap R Rp (D f) := by
    -- Naming the localized derivation separates the easy localization-of-derivations step from
    -- the quotient/localization comparison used below.
    simpa [Dp, Rp] using
      D.localizationExtension_algebraMap p.asIdeal.primeCompl
        (Localization.AtPrime p.asIdeal) f
  have hDp_unit_mapped :
      IsUnit (Ideal.Quotient.mk
        (Ideal.map (algebraMap R Rp) (principalIdeal f)) (algebraMap R Rp (D f))) := by
    -- Transport the original unit hypothesis into the localized quotient of `R_p`.
    simpa [Rp] using
      IsUnit.map (algebraMap (R ⧸ principalIdeal f)
        (Rp ⧸ Ideal.map (algebraMap R Rp) (principalIdeal f))) hDf
  have hDp_unit :
      IsUnit (Ideal.Quotient.mk (principalIdeal (algebraMap R Rp f))
        (Dp (algebraMap R Rp f))) := by
    let eMap :
        (Rp ⧸ Ideal.map (algebraMap R Rp) (principalIdeal f)) ≃ₐ[Rp]
          (Rp ⧸ principalIdeal (algebraMap R Rp f)) :=
      Ideal.quotientEquivAlgOfEq Rp
        (map_principalIdeal_localizationAtPrime (R := R) (f := f) p)
    -- Rewrite the localized quotient ideal once and then substitute the localized derivative.
    simpa [eMap, Ideal.quotientEquivAlgOfEq_mk, hDp_apply] using
      IsUnit.map eMap.toRingHom hDp_unit_mapped
  have hlocal_principal :
      IsRegularLocalRing (Rp ⧸ principalIdeal (algebraMap R Rp f)) :=
    isRegularLocalRing_quotient_principalIdeal_of_isUnit_local
      (A := Localization.AtPrime p.asIdeal) Dp x hDp_unit
  have hlocal_mapped :
      IsRegularLocalRing (Rp ⧸ Ideal.map (algebraMap R Rp) (principalIdeal f)) := by
    -- Replace the mapped ideal by the explicit principal ideal from the local theorem.
    let eMap :
        (Rp ⧸ Ideal.map (algebraMap R Rp) (principalIdeal f)) ≃ₐ[Rp]
          (Rp ⧸ principalIdeal (algebraMap R Rp f)) :=
      Ideal.quotientEquivAlgOfEq Rp
        (map_principalIdeal_localizationAtPrime (R := R) (f := f) p)
    exact IsRegularLocalRing.of_ringEquiv eMap.symm.toRingEquiv
  let eLoc :
      Localization.AtPrime q.asIdeal ≃ₐ[R ⧸ principalIdeal f]
        (Rp ⧸ Ideal.map (algebraMap R Rp) (principalIdeal f)) := by
    let J : Ideal Rp := Ideal.map (algebraMap R Rp) (principalIdeal f)
    have hcomp :
        (Ideal.Quotient.mk J).comp (algebraMap R Rp) =
          (algebraMap (R ⧸ principalIdeal f) (Rp ⧸ J)).comp
            (Ideal.Quotient.mk (principalIdeal f)) := by
      -- Both quotient maps send `r : R` to the class of its image in `R_p`.
      ext r
      rfl
    have hker :
        RingHom.ker (Ideal.Quotient.mk J) ≤
          Ideal.map (algebraMap R Rp) (RingHom.ker (Ideal.Quotient.mk (principalIdeal f))) := by
      -- The localized quotient kills exactly the image of `(f)`.
      simpa [J, Ideal.mk_ker]
    have hmap_primeCompl :
        Submonoid.map (Ideal.Quotient.mk (principalIdeal f)) p.asIdeal.primeCompl =
          q.asIdeal.primeCompl := by
      -- Route correction: package the prime-complement identification once, so the localization
      -- instance is built by `IsLocalization.of_surjective` rather than a bespoke quotient map.
      ext z
      constructor
      · rintro ⟨r, hr, rfl⟩
        simpa [p, PrimeSpectrum.comap_asIdeal] using hr
      · intro hz
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
        exact ⟨r, by simpa [p, PrimeSpectrum.comap_asIdeal] using hz, rfl⟩
    letI :
        IsLocalization q.asIdeal.primeCompl (Rp ⧸ J) := by
      -- Quotienting commutes with localization because both quotient maps are surjective and
      -- compatible on `R`.
      simpa [hmap_primeCompl] using
        (IsLocalization.of_surjective p.asIdeal.primeCompl Rp
          (Ideal.Quotient.mk (principalIdeal f)) Ideal.Quotient.mk_surjective
          (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
          hcomp hker :
            IsLocalization
              (Submonoid.map (Ideal.Quotient.mk (principalIdeal f)) p.asIdeal.primeCompl)
              (Rp ⧸ J))
    -- Both rings now realize the same at-prime localization of `R ⧸ (f)`.
    exact IsLocalization.algEquiv q.asIdeal.primeCompl (Localization.AtPrime q.asIdeal) (Rp ⧸ J)
  -- Transport the local regularity back across the canonical localization-of-quotient equivalence.
  exact IsRegularLocalRing.of_ringEquiv eLoc.symm.toRingEquiv

end Derivation

/-- Lemma 15.48.2: if `R` is a regular ring and `f` admits a derivation
`D : Derivation ℤ R R` whose value `D f` becomes a unit in `R ⧸ (f)`, then `R ⧸ (f)` is a
regular ring. -/
@[stacks 07PF]
theorem isRegularRing_quotient_principalIdeal_of_exists_derivation
    (hD : ∃ D : Derivation ℤ R R,
      IsUnit (Ideal.Quotient.mk (principalIdeal f) (D f))) :
    IsRegularRing (R ⧸ principalIdeal f) := by
  obtain ⟨D, hDf⟩ := hD
  exact D.isRegularRing_quotient_principalIdeal_of_isUnit hDf

end
