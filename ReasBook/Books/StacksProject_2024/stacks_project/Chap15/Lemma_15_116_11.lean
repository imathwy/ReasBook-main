import Mathlib
import StacksProject_2024.Chap10.Lemma_10_19_1
import StacksProject_2024.Chap09.Lemma_9_15_6
import StacksProject_2024.Chap15.Definition_15_112_1
import StacksProject_2024.Chap15.Definition_15_112_7
import StacksProject_2024.Chap15.Lemma_15_112_4
import StacksProject_2024.Chap15.Lemma_15_116_11.Index
import StacksProject_2024.Chap15.Lemma_15_113_2

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial
open IsLocalRing
open IsExtensionOfDiscreteValuationRings
open scoped IntermediateField

universe u v

section

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {L : Type v} [Field L] [Algebra A L] [Algebra (FractionRing A) L]
variable [IsScalarTower A (FractionRing A) L]
variable {p : ℕ} [Fact p.Prime] [CharP (FractionRing A) p]
variable {ξ : FractionRing A}

local notation "K" => FractionRing A
local notation "κA" => ResidueField A
local notation "B" => integralClosure A L

/- Domain-style sampling:
* primary domain: ramification theory for Artin-Schreier extensions of the fraction field of a
  discrete valuation ring in characteristic `p`;
* sampled owner declarations:
  `IntermediateField.adjoin_simple_eq_top_iff_of_isAlgebraic`,
  `IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic`,
  `IntermediateField.isSeparable_adjoin_simple_iff_isSeparable`,
  `uniformizerRootFractionPolynomial_irreducible`,
  `primitiveRootElimination_weakly_unramified_residue_case_of_uniformizer_denominator`,
  `IsUnramifiedWithRespectTo`,
  `IsTotallyRamifiedWithRespectTo`,
  `WeaklyUnramified`,
  `residueDegree`,
  `residue`;
* best owner abstraction: the chapter ramification owners on `L / FractionRing A` and on the
  induced extension `A ⊆ integralClosure A L`, with the simple intermediate field `K⟮z⟯` as the
  canonical source-facing owner for the Artin-Schreier generator data;
* primitive data: a root `z` of `X ^ p - X - ξ` together with the owner-level generator condition
  `K⟮z⟯ = ⊤`, plus the denominator data `ξ = a / π^n`;
* derived API: the Galois and ramification alternatives, and in the `p ∣ n` branch the single
  existential weakly-unramified residue-field case, along with the finite-dimensionality and
  separability companion lemmas derived from the simple-generator owner.

Layer triage:
* `source-facing`: the Artin-Schreier extension statements in this file;
* `core/canonical`: `IsUnramifiedWithRespectTo`, `IsTotallyRamifiedWithRespectTo`,
  `WeaklyUnramified`, and `residue A`;
* `bridge/view`: the bridge back to `Algebra.adjoin K ({z} : Set L) = ⊤` when an implementation
  needs the subalgebra form, together with the local-extension and residue-field instances for
  `integralClosure A L`.
-/

private theorem finiteDimensional_of_artinSchreier_generator
    (z : L) (hz : z ^ p - z = algebraMap K L ξ)
    (hgen : K⟮z⟯ = ⊤) :
    FiniteDimensional K L := by
  let f : K[X] := X ^ p - X - C ξ
  have hf_monic : f.Monic := by
    -- The Artin-Schreier polynomial is monic of degree `p`.
    have hp_degree : degree (X + C ξ : K[X]) < p := by
      have hp_one : (1 : WithBot ℕ) < p := by
        exact_mod_cast (((Fact.out : Nat.Prime p).one_lt) : 1 < p)
      refine lt_of_le_of_lt (degree_add_le (X : K[X]) (C ξ)) ?_
      simpa using hp_one
    simpa [f, sub_eq_add_neg, add_assoc] using
      (Polynomial.monic_X_pow_sub (p := (X + C ξ : K[X])) (n := p) hp_degree)
  have hz_aeval : aeval z f = 0 := by
    -- Repackage the defining equation of `z` as a polynomial evaluation identity.
    simpa [f, aeval_def, sub_eq_add_neg, add_assoc] using (sub_eq_zero.mpr hz)
  have hz_integral : IsIntegral K z := by
    -- A root of a monic polynomial is integral.
    refine ⟨f, hf_monic, hz_aeval⟩
  have hfd_adjoin : FiniteDimensional K K⟮z⟯ :=
    IntermediateField.adjoin.finiteDimensional hz_integral
  let e : K⟮z⟯ ≃ₐ[K] L :=
    (IntermediateField.equivOfEq hgen).trans IntermediateField.topEquiv
  -- Transport finite-dimensionality across the generator equivalence `K⟮z⟯ ≃ₐ[K] L`.
  exact FiniteDimensional.of_injective e.symm.toLinearMap e.symm.injective

private theorem isSeparable_of_artinSchreier_generator
    (z : L) (hz : z ^ p - z = algebraMap K L ξ)
    (hgen : K⟮z⟯ = ⊤) :
    Algebra.IsSeparable K L := by
  let f : K[X] := X ^ p - X - C ξ
  have hf_deriv : derivative f = -1 := by
    -- In characteristic `p`, the derivative of `X ^ p - X - ξ` is `-1`.
    calc
      derivative f = derivative (X ^ p : K[X]) - derivative X - derivative (C ξ) := by
        simp [f, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      _ = C (p : K) * X ^ (p - 1) - 1 := by
        simp [Polynomial.derivative_X_pow]
      _ = -1 := by
        have hp_cast : (p : K) = 0 := CharP.cast_eq_zero K p
        simp [hp_cast]
  have hf_sep : f.Separable := by
    -- The derivative is a unit, so the polynomial is separable.
    rw [Polynomial.separable_def']
    refine ⟨0, -1, ?_⟩
    simp [hf_deriv]
  have hz_aeval : aeval z f = 0 := by
    -- Repackage the defining Artin-Schreier equation as `f(z) = 0`.
    simpa [f, aeval_def, sub_eq_add_neg, add_assoc] using (sub_eq_zero.mpr hz)
  have hz_sep : IsSeparable K z := by
    -- The minimal polynomial of `z` divides a separable polynomial.
    exact Polynomial.Separable.of_dvd hf_sep (minpoly.dvd K z hz_aeval)
  have hsep_adjoin : Algebra.IsSeparable K K⟮z⟯ :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable K L).2 hz_sep
  let e : K⟮z⟯ ≃ₐ[K] L :=
    (IntermediateField.equivOfEq hgen).trans IntermediateField.topEquiv
  let _ : Algebra.IsSeparable K K⟮z⟯ := hsep_adjoin
  -- Separability is preserved by the generator equivalence.
  exact AlgEquiv.Algebra.isSeparable e.symm

/-- Helper for Lemma 15.116.11: in a finite family of elements of a discrete valuation ring, one
element divides all the others. -/
private lemma exists_mem_finset_dvd_all_coefficients
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → A) (hs : s.Nonempty) :
    ∃ j ∈ s, ∀ i ∈ s, f j ∣ f i := by
  -- Reuse the canonical valuation-ring owner from the support file imported by `Index`.
  exact exists_mem_finset_dvd_all (A := A) s f hs

/-- Helper for Lemma 15.116.11: residue-field linear independence of lifts in the integral closure
already implies `A`-linear independence. -/
private lemma integralClosure_residue_lifts_linearIndependent_over_base
    [IsDiscreteValuationRing B]
    {ι : Type*} (u : ι → B)
    (hu : LinearIndependent κA (fun i ↦ IsLocalRing.residue B (u i))) :
    LinearIndependent A u := by
  let _ : IsExtensionOfDiscreteValuationRings A B := inferInstance
  let _ : IsExtensionOfValuationRings A B := inferInstance
  -- Reuse the canonical valuation-ring lift argument instead of duplicating it locally.
  simpa using residue_lifts_linearIndependent_over_base (A := A) u hu

/-- Helper for Lemma 15.116.11: residue-field linear independence of lifts in the integral closure
implies `K`-linear independence after embedding into `L`. -/
private lemma integralClosure_residue_lifts_linearIndependent
    [IsDiscreteValuationRing B]
    {ι : Type*} (u : ι → B)
    (hu : LinearIndependent κA (fun i ↦ IsLocalRing.residue B (u i))) :
    LinearIndependent K (fun i ↦ algebraMap B L (u i)) := by
  let _ : IsFractionRing B L := integralClosure.isFractionRing_of_finite_extension K L
  have hbase : LinearIndependent A u :=
    integralClosure_residue_lifts_linearIndependent_over_base (A := A) (L := L) u hu
  have hmap : LinearIndependent A (fun i ↦ algebraMap B L (u i)) := by
    refine hbase.map' (IsScalarTower.toAlgHom A B L).toLinearMap ?_
    exact LinearMap.ker_eq_bot.mpr (IsFractionRing.injective B L)
  -- After the lifts are independent over `A`, pass to the fraction field `K`.
  exact (LinearIndependent.iff_fractionRing (R := A) (K := K)).mp hmap

private theorem finiteDimensional_residueField_of_integralClosure
    [FiniteDimensional K L]
    [IsDiscreteValuationRing B] :
    FiniteDimensional κA (ResidueField B) := by
  classical
  let _ : IsFractionRing B L := integralClosure.isFractionRing_of_finite_extension K L
  let ι := Module.Free.ChooseBasisIndex κA (ResidueField B)
  let b : Module.Basis ι κA (ResidueField B) := Module.Free.chooseBasis κA (ResidueField B)
  let u : ι → B := fun i ↦ Classical.choose (IsLocalRing.residue_surjective (b i))
  have hu : ∀ i, IsLocalRing.residue B (u i) = b i := by
    intro i
    exact Classical.choose_spec (IsLocalRing.residue_surjective (b i))
  -- Lift a residue-field basis to the integral closure and transport its independence to `L`.
  have hlin_res : LinearIndependent κA (fun i ↦ IsLocalRing.residue B (u i)) := by
    simpa [hu] using b.linearIndependent
  have hlin_lifts : LinearIndependent K (fun i ↦ algebraMap B L (u i)) :=
    integralClosure_residue_lifts_linearIndependent (A := A) (L := L) u hlin_res
  have hcard : Cardinal.mk ι ≤ Module.finrank K L := hlin_lifts.cardinalMk_le_finrank
  have hrank_lt : Module.rank κA (ResidueField B) < Cardinal.aleph0 := by
    calc
      Module.rank κA (ResidueField B) = Cardinal.mk ι := by
        simpa using b.mk_eq_rank''.symm
      _ ≤ Module.finrank K L := hcard
      _ < Cardinal.aleph0 := Cardinal.natCast_lt_aleph0
  -- Finite rank of the lifted basis index turns the residue extension into a finite-dimensional one.
  letI : Fintype ι := Module.Basis.fintypeIndexOfRankLtAleph0 b hrank_lt
  exact Module.Basis.finiteDimensional_of_finite b

/-- Helper for Lemma 15.116.11: the Artin-Schreier polynomial `X ^ p - X - ξ` is monic. -/
private lemma artin_schreier_polynomial_monic :
    (X ^ p - X - C ξ : K[X]).Monic := by
  have hp_degree : degree (X + C ξ : K[X]) < p := by
    -- The lower-order correction term has degree `1`, hence is strictly smaller than `p`.
    have hp_one : (1 : WithBot ℕ) < p := by
      exact_mod_cast (show 1 < p from (Fact.out : Nat.Prime p).one_lt)
    simpa [Polynomial.degree_X_add_C] using hp_one
  -- Repackage `X ^ p - (X + ξ)` into the standard monic Artin-Schreier form.
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    (Polynomial.monic_X_pow_sub (p := (X + C ξ : K[X])) (n := p) hp_degree)

/-- Helper for Lemma 15.116.11: a root of `X ^ p - X - ξ` is integral over `K`. -/
private lemma artin_schreier_generator_isIntegral
    (z : L) (hz : z ^ p - z = algebraMap K L ξ) :
    IsIntegral K z := by
  let f : K[X] := X ^ p - X - C ξ
  have hz_aeval : aeval z f = 0 := by
    -- Repackage the defining equation as a polynomial relation.
    simpa [f, aeval_def, sub_eq_add_neg, add_assoc] using (sub_eq_zero.mpr hz)
  exact ⟨f, artin_schreier_polynomial_monic (A := A) (p := p) (ξ := ξ), hz_aeval⟩

/-- Helper for Lemma 15.116.11: over `L`, the Artin-Schreier polynomial becomes a translate of
`X ^ p - X`, so it splits. -/
private lemma artin_schreier_polynomial_splits_of_root
    (z : L) (hz : z ^ p - z = algebraMap K L ξ) :
    ((X ^ p - X - C ξ).map (algebraMap K L)).Splits := by
  let f : L[X] := X ^ p - X - C (algebraMap K L ξ)
  letI : CharP L p :=
    charP_of_injective_algebraMap (R := K) (A := L) (algebraMap K L).injective p
  have hsplit_XK : (X ^ p - X : K[X]).Splits := by
    -- The prime-field polynomial `X ^ p - X` already splits over the characteristic-`p` base field.
    simpa using
      (Subfield.splits_bot (F := K) (p := p)).map (Subfield.subtype (⊥ : Subfield K))
  have hsplit_X : (X ^ p - X : L[X]).Splits := by
    -- Transport that splitting statement from `K` to `L`.
    simpa using hsplit_XK.map (algebraMap K L)
  have hcomp : f.comp (X + C z) = (X ^ p - X : L[X]) := by
    -- Translating by the chosen root removes the constant term.
    calc
      f.comp (X + C z)
          = (X + C z) ^ p - (X + C z) - C (algebraMap K L ξ) := by
              simp [f]
      _ = X ^ p + C (z ^ p) - X - C z - C (algebraMap K L ξ) := by
              rw [sub_eq_add_neg, sub_eq_add_neg, add_pow_char]
              simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      _ = X ^ p - X := by
              rw [show C (algebraMap K L ξ) = C (z ^ p - z) by simpa [hz]]
              simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have hsplit_comp : (f.comp (X + C z)).Splits := hcomp ▸ hsplit_X
  have hdeg : (X + C z : L[X]).natDegree = 1 := by
    simp
  have hsplit_f : f.Splits :=
    (splits_iff_comp_splits_of_natDegree_eq_one (f := f) (g := X + C z) hdeg).2 hsplit_comp
  simpa [f]

/-- Helper for Lemma 15.116.11: the mapped minimal polynomial of an Artin-Schreier generator
splits in the ambient field. -/
private lemma artin_schreier_minpoly_splits_of_generator
    (z : L) (hz : z ^ p - z = algebraMap K L ξ) :
    ((minpoly K z).map (algebraMap K L)).Splits := by
  let f : K[X] := X ^ p - X - C ξ
  have hsplit :
      (f.map (algebraMap K L)).Splits :=
    artin_schreier_polynomial_splits_of_root (A := A) (L := L) (p := p) (ξ := ξ) z hz
  have hz_aeval : aeval z f = 0 := by
    -- The Artin-Schreier equation makes the chosen polynomial vanish at `z`.
    simpa [f, aeval_def, sub_eq_add_neg, add_assoc] using (sub_eq_zero.mpr hz)
  have hdvd : (minpoly K z).map (algebraMap K L) ∣ f.map (algebraMap K L) := by
    exact Polynomial.map_dvd (algebraMap K L) (minpoly.dvd K z hz_aeval)
  have hf_ne_zero : f.map (algebraMap K L) ≠ 0 := by
    exact map_ne_zero (artin_schreier_polynomial_monic (A := A) (p := p) (ξ := ξ)).ne_zero
  -- Route correction: pass from the translated Artin-Schreier split polynomial to the mapped
  -- minimal polynomial through the canonical divisibility bridge `minpoly.dvd`.
  exact Polynomial.Splits.of_dvd hsplit hf_ne_zero hdvd

/-- Helper for Lemma 15.116.11: if a single integral generator `z` generates the whole field and
its minimal polynomial splits in the ambient field, then the extension is normal. -/
private theorem normal_of_adjoin_simple_minpoly_splits
    (z : L) (hgen : K⟮z⟯ = ⊤)
    (hint : IsIntegral K z)
    (hsplit : ((minpoly K z).map (algebraMap K L)).Splits) :
    Normal K L := by
  have hgen' : IntermediateField.adjoin K ({z} : Set L) = ⊤ := by
    simpa using hgen
  rw [normal_iff]
  intro x
  have hx : x ∈ IntermediateField.adjoin K ({z} : Set L) := hgen' ▸ by simp
  haveI : Algebra.IsAlgebraic K (IntermediateField.adjoin K ({z} : Set L)) :=
    IntermediateField.isAlgebraic_adjoin fun y hy ↦ by
      rcases Set.mem_singleton_iff.mp hy with rfl
      exact hint
  have hsplit_singleton :
      ∀ y ∈ ({z} : Set L), IsIntegral K y ∧ ((minpoly K y).map (algebraMap K L)).Splits := by
    intro y hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    exact ⟨hint, hsplit⟩
  let x' : IntermediateField.adjoin K ({z} : Set L) := ⟨x, hx⟩
  refine ⟨?_, splits_of_mem_adjoin K L hsplit_singleton hx⟩
  -- Algebraicity inside the simple adjoin gives integrality of every element of `L`.
  simpa [x'] using
    IsIntegral.map (IntermediateField.adjoin K ({z} : Set L)).val
      (Algebra.IsIntegral.isIntegral x')

/-- Helper for Lemma 15.116.11: an Artin-Schreier simple extension generated by a root of
`X ^ p - X - ξ` is Galois once the chosen root generates the whole field. -/
private theorem artin_schreier_isGalois
    (z : L) (hz : z ^ p - z = algebraMap K L ξ)
    (hgen : K⟮z⟯ = ⊤) :
    IsGalois K L := by
  -- Route correction: avoid the old `PUnit`-indexed normality proof and use the simple-generator
  -- owner directly.
  have hz_integral :
      IsIntegral K z :=
    artin_schreier_generator_isIntegral (A := A) (L := L) (p := p) (ξ := ξ) z hz
  have hnormal : Normal K L :=
    normal_of_adjoin_simple_minpoly_splits
      (A := A) (L := L) (p := p) (ξ := ξ) z hgen hz_integral
      (artin_schreier_minpoly_splits_of_generator (A := A) (L := L) (p := p) (ξ := ξ) z hz)
  -- Combine the new normality statement with the earlier separability proof.
  rw [isGalois_iff]
  exact ⟨isSeparable_of_artinSchreier_generator z hz hgen, hnormal⟩

/-- Helper for Lemma 15.116.11: if the Artin-Schreier polynomial already has a root in the base
field, then the simple extension generated by any chosen root is trivial. -/
private lemma artin_schreier_finrank_eq_one_of_base_root
    (z : L) (hz : z ^ p - z = algebraMap K L ξ)
    (hgen : K⟮z⟯ = ⊤)
    {t : K} (ht : t ^ p - t = ξ) :
    Module.finrank K L = 1 := by
  let u : L := z - algebraMap K L t
  have hu_eq : u ^ p = u := by
    -- Subtracting a base root reduces to the split polynomial `X ^ p - X`.
    calc
      u ^ p - u
          = algebraMap K L ξ - (algebraMap K L t ^ p - algebraMap K L t) := by
              dsimp [u]
              rw [sub_eq_add_neg, sub_eq_add_neg, add_pow_char]
              simp [hz, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      _ = algebraMap K L ξ - algebraMap K L (t ^ p - t) := by
              simp [map_sub]
      _ = 0 := by simp [ht]
    exact sub_eq_zero.mp this
  have hu_aeval : aeval u (X ^ p - X : K[X]) = 0 := by
    -- Repackage the translated equation as a polynomial root relation.
    simpa [aeval_def, sub_eq_add_neg, u] using (sub_eq_zero.mpr hu_eq)
  have hmonic_Xpow_sub_X : (X ^ p - X : K[X]).Monic := by
    -- The split Artin-Schreier polynomial is still monic of degree `p`.
    have hp_degree : degree (X : K[X]) < p := by
      have hp_one : (1 : WithBot ℕ) < p := by
        exact_mod_cast (((Fact.out : Nat.Prime p).one_lt) : 1 < p)
      simpa using hp_one
    simpa using (Polynomial.monic_X_pow_sub (p := (X : K[X])) (n := p) hp_degree)
  have hu_integral : IsIntegral K u := by
    -- A root of the monic split polynomial is integral over the base field.
    exact ⟨X ^ p - X, hmonic_Xpow_sub_X, hu_aeval⟩
  have hsplit_X : (X ^ p - X : K[X]).Splits := by
    -- Over characteristic `p`, `X ^ p - X` splits over the base field itself.
    simpa using
      (Subfield.splits_bot (F := K) (p := p)).map (Subfield.subtype (⊥ : Subfield K))
  have hminpoly_split : (minpoly K u).Splits := by
    -- The minimal polynomial inherits splitting from the split Artin-Schreier polynomial.
    exact Polynomial.Splits.of_dvd hsplit_X hmonic_Xpow_sub_X.ne_zero (minpoly.dvd K u hu_aeval)
  have hminpoly_degree : (minpoly K u).degree = 1 := by
    -- An irreducible factor of a split polynomial over a field must be linear.
    exact Polynomial.degree_eq_one_of_irreducible_of_splits hminpoly_split
      (minpoly.irreducible hu_integral)
  have hfin_adjoin_u : Module.finrank K K⟮u⟯ = 1 := by
    -- The translated element therefore generates a degree-one simple extension.
    calc
      Module.finrank K K⟮u⟯ = (minpoly K u).natDegree := IntermediateField.adjoin.finrank hu_integral
      _ = 1 := Polynomial.natDegree_eq_of_degree_eq_some hminpoly_degree
  have htop_u : (⊥ : IntermediateField K K⟮u⟯) = ⊤ := by
    -- Degree one forces the translated simple extension to collapse to the base field.
    exact (IntermediateField.bot_eq_top_iff_finrank_eq_one).2 hfin_adjoin_u
  have hu_mem_bot : u ∈ (⊥ : IntermediateField K L) := by
    -- Interpret that collapse back in the ambient field.
    have hu_mem_top_sub : (⟨u, by
        exact IntermediateField.mem_adjoin_simple_self K u⟩ : K⟮u⟯) ∈
          (⊤ : IntermediateField K K⟮u⟯) := by
      simp
    have hu_mem_bot_sub : (⟨u, by
        exact IntermediateField.mem_adjoin_simple_self K u⟩ : K⟮u⟯) ∈
          (⊥ : IntermediateField K K⟮u⟯) := by
      simpa [htop_u] using hu_mem_top_sub
    rcases IntermediateField.mem_bot.mp hu_mem_bot_sub with ⟨c, hc⟩
    exact IntermediateField.mem_bot.mpr ⟨c, Subtype.ext_iff.mp hc⟩
  have ht_mem_bot : algebraMap K L t ∈ (⊥ : IntermediateField K L) :=
    IntermediateField.mem_bot.mpr ⟨t, rfl⟩
  have hz_mem_bot : z ∈ (⊥ : IntermediateField K L) := by
    -- Undo the translation to bring the original generator back into the base field.
    have hz_eq : z = u + algebraMap K L t := by
      dsimp [u]
      ring
    rw [hz_eq]
    exact (⊥ : IntermediateField K L).add_mem hu_mem_bot ht_mem_bot
  have hz_adjoin_bot : K⟮z⟯ = ⊥ := IntermediateField.adjoin_simple_eq_bot_iff.mpr hz_mem_bot
  have hbot_top : (⊥ : IntermediateField K L) = ⊤ := by
    -- The assumed generator equality then forces the whole extension to be trivial.
    calc
      (⊥ : IntermediateField K L) = K⟮z⟯ := hz_adjoin_bot.symm
      _ = ⊤ := hgen
  exact (IntermediateField.bot_eq_top_iff_finrank_eq_one).1 hbot_top

/-- Helper for Lemma 15.116.11: once the Artin-Schreier polynomial is irreducible, the simple
generator has degree exactly `p`. -/
private lemma artin_schreier_finrank_eq_p_of_irreducible
    (z : L) (hz : z ^ p - z = algebraMap K L ξ)
    (hgen : K⟮z⟯ = ⊤)
    (hirr : Irreducible (X ^ p - X - C ξ : K[X])) :
    Module.finrank K L = p := by
  have hz_integral :
      IsIntegral K z :=
    artin_schreier_generator_isIntegral (A := A) (L := L) (p := p) (ξ := ξ) z hz
  have hz_aeval : aeval z (X ^ p - X - C ξ : K[X]) = 0 := by
    -- Repackage the defining Artin-Schreier equation as `f(z) = 0`.
    simpa [aeval_def, sub_eq_add_neg, add_assoc] using (sub_eq_zero.mpr hz)
  have hminpoly :
      minpoly K z = X ^ p - X - C ξ := by
    -- Irreducibility identifies the minimal polynomial with the Artin-Schreier polynomial.
    symm
    exact minpoly.eq_of_irreducible_of_monic hirr hz_aeval
      (artin_schreier_polynomial_monic (A := A) (p := p) (ξ := ξ))
  let e : K⟮z⟯ ≃ₐ[K] L :=
    (IntermediateField.equivOfEq hgen).trans IntermediateField.topEquiv
  -- Compute the simple-extension degree via the minimal polynomial and transport it along `hgen`.
  calc
    Module.finrank K L = Module.finrank K K⟮z⟯ := by
      simpa using e.toLinearEquiv.finrank_eq.symm
    _ = (minpoly K z).natDegree := IntermediateField.adjoin.finrank hz_integral
    _ = p := by
      rw [hminpoly]
      simp [Fact.out.ne_zero]

/-- Helper for Lemma 15.116.11: every root of `X ^ p - X` in the ambient field comes from the
prime field `ZMod p`. -/
private lemma exists_zmod_of_frobenius_fixed
    {x : L} (hx : x ^ p - x = 0) :
    ∃ c : ZMod p, algebraMap (ZMod p) L c = x := by
  classical
  let _ : Algebra (ZMod p) L := ZMod.algebra L p
  let f : L[X] := X ^ p - X
  let s : Finset L := Finset.univ.image fun c : ZMod p ↦ algebraMap (ZMod p) L c
  have hf_ne_zero : f ≠ 0 := by
    simp [f, Fact.out.ne_zero]
  have hs_subset : s ⊆ f.roots.toFinset := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨c, -, rfl⟩
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hf_ne_zero]
    -- Every prime-field element is a root of `X ^ p - X`.
    simp [Polynomial.IsRoot, f]
  have hs_card : s.card = p := by
    -- The prime-field image has exactly `p` elements because the algebra map is injective.
    rw [Finset.card_image_of_injective]
    · simp
    · exact RingHom.injective (algebraMap (ZMod p) L)
  have hroots_card : f.roots.toFinset.card ≤ p := by
    have hroots_card' : (f.roots.card : ℕ) ≤ p := by
      exact Nat.cast_le.mp <| by
        simpa [f, Fact.out.ne_zero] using Polynomial.card_roots hf_ne_zero
    exact le_trans (Multiset.toFinset_card_le f.roots) hroots_card'
  have hs_eq : s = f.roots.toFinset := by
    apply Finset.eq_of_subset_of_card_le hs_subset
    rw [hs_card]
    exact hroots_card
  have hx_mem : x ∈ f.roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hf_ne_zero]
    simpa [Polynomial.IsRoot, f] using hx
  have hx_mem' : x ∈ s := by
    simpa [hs_eq] using hx_mem
  rcases Finset.mem_image.mp hx_mem' with ⟨c, -, hc⟩
  exact ⟨c, hc⟩

/-- Helper for Lemma 15.116.11: every Galois automorphism acts on the chosen Artin-Schreier
generator by translation by a prime-field constant. -/
private lemma artin_schreier_galois_shift
    (z : L) (hz : z ^ p - z = algebraMap K L ξ)
    (σ : Gal(L/K)) :
    ∃ c : ZMod p, σ z = z + algebraMap (ZMod p) L c := by
  let _ : Algebra (ZMod p) L := ZMod.algebra L p
  have hshift_root : (σ z - z) ^ p - (σ z - z) = 0 := by
    -- The difference `σ z - z` is another root of `X ^ p - X`.
    calc
      (σ z - z) ^ p - (σ z - z)
          = (σ z ^ p - σ z) - (z ^ p - z) := by
              rw [sub_eq_add_neg, sub_eq_add_neg, add_pow_char]
              ring
      _ = σ (z ^ p - z) - (z ^ p - z) := by
              simp [map_sub]
      _ = σ (algebraMap K L ξ) - algebraMap K L ξ := by rw [hz]
      _ = 0 := by simp
  rcases exists_zmod_of_frobenius_fixed (A := A) (L := L) (p := p) (ξ := ξ) hshift_root with
    ⟨c, hc⟩
  refine ⟨c, ?_⟩
  -- Rewrite the difference identity as the source-faithful translation formula.
  calc
    σ z = (σ z - z) + z := by rw [sub_add_cancel]
    _ = algebraMap (ZMod p) L c + z := by rw [hc.symm]
    _ = z + algebraMap (ZMod p) L c := by simp [add_comm]

/-- Helper for Lemma 15.116.11: once `z` generates the whole field, a `K`-automorphism is
determined by its value on `z`. -/
private lemma artin_schreier_algEquiv_eq_of_generator_eq
    (z : L) (hgen : K⟮z⟯ = ⊤)
    {σ τ : Gal(L/K)} (hστ : σ z = τ z) :
    σ = τ := by
  apply AlgEquiv.ext
  intro x
  have hx : x ∈ IntermediateField.adjoin K ({z} : Set L) := by
    simpa [hgen] using (show x ∈ (⊤ : IntermediateField K L) from by simp)
  -- The generator equality propagates through the adjoin-induction API.
  refine IntermediateField.adjoin_induction (F := K) (s := ({z} : Set L))
      (p := fun y _ ↦ σ y = τ y) ?_ ?_ ?_ ?_ ?_ hx
  · intro y hy
    have hyz : y = z := by simpa using hy
    simpa [hyz] using hστ
  · intro a
    simp
  · intro x y hx hy hx_eq hy_eq
    simpa using congrArg₂ (fun a b ↦ a + b) hx_eq hy_eq
  · intro x hx hx_eq
    simpa using congrArg Inv.inv hx_eq
  · intro x y hx hy hx_eq hy_eq
    simpa using congrArg₂ (fun a b ↦ a * b) hx_eq hy_eq

/-- Helper for Lemma 15.116.11: inside the subtype field `K⟮x⟯`, the distinguished element `x`
still generates the whole field. -/
private lemma adjoin_simple_subtype_eq_top
    {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E]
    {x : E} (hx : IsIntegral F x) :
    F⟮(⟨x, IntermediateField.mem_adjoin_simple_self F x⟩ : ↥F⟮x⟯)⟯ = ⊤ := by
  let x' : ↥F⟮x⟯ := ⟨x, IntermediateField.mem_adjoin_simple_self F x⟩
  letI : FiniteDimensional F ↥F⟮x⟯ := IntermediateField.adjoin.finiteDimensional hx
  have hx' : IsAlgebraic F x' := (IsIntegral.of_finite F x').isAlgebraic
  apply IntermediateField.toSubalgebra_injective
  rw [IntermediateField.top_toSubalgebra]
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hx']
  ext y
  constructor
  · intro hy
    simp
  · intro hy
    -- Any element of the ambient simple field is already a polynomial in the distinguished root.
    rw [Algebra.adjoin_singleton_eq_range_aeval]
    have hy' : (y : E) ∈ (F⟮x⟯.toSubalgebra : Set E) := by
      simp [y.property]
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (IsIntegral.isAlgebraic hx)] at hy'
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hy'
    rcases hy' with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    apply Subtype.ext
    -- Apply the ambient inclusion to the subtype evaluation and identify it with `aeval x q`.
    have hmap :=
      (Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom F ↥F⟮x⟯ E) x' q)
    simpa [x'] using hmap.symm.trans hq

/-- Helper for Lemma 15.116.11: any generated Artin-Schreier extension has degree `1` or `p`. -/
private lemma artin_schreier_generator_degree_dichotomy
    {L' : Type*} [Field L'] [Algebra A L'] [Algebra K L']
    [IsScalarTower A K L']
    (z : L') (hz : z ^ p - z = algebraMap K L' ξ)
    (hgen : K⟮z⟯ = ⊤) :
    Module.finrank K L' = 1 ∨ Module.finrank K L' = p := by
  let _ : IsGalois K L' := artin_schreier_isGalois (A := A) (L := L') (p := p) (ξ := ξ) z hz hgen
  let _ : Algebra (ZMod p) K := ZMod.algebra K p
  let _ : Algebra (ZMod p) L' := ZMod.algebra L' p
  let _ : IsScalarTower (ZMod p) K L' := by infer_instance
  classical
  let shiftCoeff : Gal(L'/K) → ZMod p := fun σ ↦
    Classical.choose
      (artin_schreier_galois_shift (A := A) (L := L') (p := p) (ξ := ξ) z hz σ)
  have hshift_eq :
      ∀ σ : Gal(L'/K), σ z = z + algebraMap (ZMod p) L' (shiftCoeff σ) := by
    intro σ
    exact Classical.choose_spec
      (artin_schreier_galois_shift (A := A) (L := L') (p := p) (ξ := ξ) z hz σ)
  have hshift_one : shiftCoeff 1 = 0 := by
    have hone_eq : z + algebraMap (ZMod p) L' (shiftCoeff 1) = z := by
      simpa using (hshift_eq 1).symm
    have hmap_zero :
        algebraMap (ZMod p) L' (shiftCoeff 1) = 0 := by
      exact add_left_cancel hone_eq
    exact RingHom.injective (algebraMap (ZMod p) L') hmap_zero
  have hshift_mul :
      ∀ σ τ : Gal(L'/K), shiftCoeff (σ * τ) = shiftCoeff σ + shiftCoeff τ := by
    intro σ τ
    have hconst :
        σ (algebraMap (ZMod p) L' (shiftCoeff τ)) =
          algebraMap (ZMod p) L' (shiftCoeff τ) := by
      calc
        σ (algebraMap (ZMod p) L' (shiftCoeff τ))
            = σ (algebraMap K L' (algebraMap (ZMod p) K (shiftCoeff τ))) := by
                rw [← IsScalarTower.algebraMap_eq (ZMod p) K L']
        _ = algebraMap K L' (algebraMap (ZMod p) K (shiftCoeff τ)) := by
              simp
        _ = algebraMap (ZMod p) L' (shiftCoeff τ) := by
              rw [IsScalarTower.algebraMap_eq (ZMod p) K L']
    have hmul_eq :
        z + algebraMap (ZMod p) L' (shiftCoeff (σ * τ)) =
          z + algebraMap (ZMod p) L' (shiftCoeff σ + shiftCoeff τ) := by
      calc
        z + algebraMap (ZMod p) L' (shiftCoeff (σ * τ))
            = (σ * τ) z := by simpa using (hshift_eq (σ * τ)).symm
        _ = σ (τ z) := rfl
        _ = σ (z + algebraMap (ZMod p) L' (shiftCoeff τ)) := by
              rw [hshift_eq τ]
        _ = σ z + algebraMap (ZMod p) L' (shiftCoeff τ) := by
              simp [map_add, hconst]
        _ = (z + algebraMap (ZMod p) L' (shiftCoeff σ)) +
              algebraMap (ZMod p) L' (shiftCoeff τ) := by
                rw [hshift_eq σ]
        _ = z + algebraMap (ZMod p) L' (shiftCoeff σ + shiftCoeff τ) := by
              simp [map_add, add_assoc, add_left_comm, add_comm]
    have hmap_eq :
        algebraMap (ZMod p) L' (shiftCoeff (σ * τ)) =
          algebraMap (ZMod p) L' (shiftCoeff σ + shiftCoeff τ) := by
      exact add_left_cancel hmul_eq
    exact RingHom.injective (algebraMap (ZMod p) L') hmap_eq
  let shiftHom : Gal(L'/K) →* Multiplicative (ZMod p) :=
    { toFun := fun σ ↦ Multiplicative.ofAdd (shiftCoeff σ)
      map_one' := by
        change Multiplicative.ofAdd (shiftCoeff 1) = 1
        simpa [hshift_one]
      map_mul' := by
        intro σ τ
        change Multiplicative.ofAdd (shiftCoeff (σ * τ)) =
          Multiplicative.ofAdd (shiftCoeff σ + shiftCoeff τ)
        simp [hshift_mul σ τ] }
  have hshift_injective : Function.Injective shiftHom := by
    intro σ τ hστ
    have hcoeff_eq : shiftCoeff σ = shiftCoeff τ := by
      exact Multiplicative.toAdd.inj hστ
    have hz_eq : σ z = τ z := by
      calc
        σ z = z + algebraMap (ZMod p) L' (shiftCoeff σ) := hshift_eq σ
        _ = z + algebraMap (ZMod p) L' (shiftCoeff τ) := by rw [hcoeff_eq]
        _ = τ z := hshift_eq τ |>.symm
    exact artin_schreier_algEquiv_eq_of_generator_eq (A := A) (L := L') (p := p)
      (ξ := ξ) z hgen hz_eq
  have hcard_dvd : Nat.card Gal(L'/K) ∣ p := by
    let eRange : Gal(L'/K) ≃ shiftHom.range :=
      Equiv.ofInjective shiftHom hshift_injective
    calc
      Nat.card Gal(L'/K) = Nat.card shiftHom.range := Nat.card_congr eRange
      _ ∣ Nat.card (Additive (ZMod p)) := Subgroup.card_subgroup_dvd_card shiftHom.range
      _ = p := by simp
  rcases (Nat.dvd_prime (Fact.out : Nat.Prime p)).mp hcard_dvd with hcard | hcard
  · exact Or.inl <| by
      rw [← IsGalois.card_aut_eq_finrank K L']
      exact hcard
  · exact Or.inr <| by
      rw [← IsGalois.card_aut_eq_finrank K L']
      exact hcard

/-- Helper for Lemma 15.116.11: the Artin-Schreier polynomial either already has a base-field
root or is irreducible. -/
private lemma artin_schreier_root_in_base_or_irreducible :
    (∃ t : K, t ^ p - t = ξ) ∨ Irreducible (X ^ p - X - C ξ : K[X]) := by
  by_cases hroot : ∃ t : K, t ^ p - t = ξ
  · -- If a root already lies in the base field, we are in the trivial branch of the dichotomy.
    exact Or.inl hroot
  · -- Route correction: the remaining branch should follow the source-faithful translated-root
    -- argument in a splitting field, then pass to the simple subextension generated by one root.
    let f : K[X] := X ^ p - X - C ξ
    let M := f.SplittingField
    letI : Field M := inferInstance
    letI : Algebra K M := inferInstance
    letI : IsSplittingField K M f := inferInstance
    have hf_monic : f.Monic :=
      artin_schreier_polynomial_monic (A := A) (p := p) (ξ := ξ)
    have hf_natDegree : f.natDegree = p := by
      refine Polynomial.natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
      · have hX_add : (X + C ξ : K[X]).natDegree ≤ p := by
          have hp_one_le : 1 ≤ p := Nat.succ_le_of_lt (Fact.out.one_lt)
          simpa [Polynomial.natDegree_X_add_C] using hp_one_le
        calc
          f.natDegree = (X ^ p - (X + C ξ : K[X])).natDegree := by
            simp [f, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
          _ ≤ max (X ^ p).natDegree (X + C ξ).natDegree := Polynomial.natDegree_sub_le _ _
          _ ≤ p := max_le (Polynomial.natDegree_X_pow_le p) hX_add
      · have hp_ne_one : p ≠ 1 := (Fact.out : Nat.Prime p).ne_one
        simp [f, hp_ne_one, Fact.out.ne_zero]
    have hf_degree_ne_zero : f.degree ≠ 0 := by
      intro hdeg
      have hdeg_nat :
          f.natDegree = 0 :=
        (Polynomial.degree_eq_iff_natDegree_eq hf_monic.ne_zero).1 hdeg
      exact Fact.out.ne_zero (hf_natDegree.trans hdeg_nat.symm)
    have hsplit : (f.map (algebraMap K M)).Splits :=
      Polynomial.IsSplittingField.splits M f
    have hmap_degree_ne_zero : (f.map (algebraMap K M)).degree ≠ 0 := by
      simpa [Polynomial.degree_map_eq_of_injective (algebraMap K M).injective] using hf_degree_ne_zero
    rcases Polynomial.exists_root_of_splits hsplit hmap_degree_ne_zero with ⟨z, hz_eval⟩
    have hz_aeval : aeval z f = 0 := by
      -- The splitting-field root is a genuine root of the original Artin-Schreier polynomial.
      simpa [Polynomial.aeval_def] using hz_eval
    have hz : z ^ p - z = algebraMap K M ξ := by
      -- Repackage the splitting-field root relation back into Artin-Schreier form.
      simpa [f, Polynomial.aeval_def, sub_eq_add_neg, add_assoc] using hz_aeval
    let E : IntermediateField K M := K⟮z⟯
    let zE : E := ⟨z, IntermediateField.mem_adjoin_simple_self K z⟩
    have hzE : zE ^ p - zE = algebraMap K E ξ := by
      apply Subtype.ext
      simpa [zE] using hz
    have hzE_integral : IsIntegral K zE :=
      artin_schreier_generator_isIntegral (A := A) (L := E) (p := p) (ξ := ξ) zE hzE
    have hgenE : K⟮zE⟯ = (⊤ : IntermediateField K E) :=
      adjoin_simple_subtype_eq_top hzE_integral
    have hdegE :
        Module.finrank K E = 1 ∨ Module.finrank K E = p :=
      artin_schreier_generator_degree_dichotomy
        (A := A) (p := p) (ξ := ξ) zE hzE hgenE
    rcases hdegE with hdegE | hdegE
    · -- Degree `1` would place the chosen root back in `K`, contradicting the no-root branch.
      have hbot_top : (⊥ : IntermediateField K E) = ⊤ :=
        (IntermediateField.bot_eq_top_iff_finrank_eq_one).2 hdegE
      have hzE_bot : zE ∈ (⊥ : IntermediateField K E) := by
        simpa [hbot_top] using (show zE ∈ (⊤ : IntermediateField K E) from by simp)
      rcases IntermediateField.mem_bot.mp hzE_bot with ⟨t, ht⟩
      have ht_map : algebraMap K E (t ^ p - t) = algebraMap K E ξ := by
        calc
          algebraMap K E (t ^ p - t) = zE ^ p - zE := by
            simpa [map_sub, ht]
          _ = algebraMap K E ξ := hzE
      have ht_root : t ^ p - t = ξ := RingHom.injective (algebraMap K E) ht_map
      exact (hroot ⟨t, ht_root⟩).elim
    · have hminpoly_natDegree : (minpoly K zE).natDegree = p := by
        let e : K⟮zE⟯ ≃ₐ[K] E :=
          (IntermediateField.equivOfEq hgenE).trans IntermediateField.topEquiv
        calc
          (minpoly K zE).natDegree = Module.finrank K K⟮zE⟯ := by
            symm
            exact IntermediateField.adjoin.finrank hzE_integral
          _ = Module.finrank K E := by
            simpa using e.toLinearEquiv.finrank_eq
          _ = p := hdegE
      have hminpoly_dvd : minpoly K zE ∣ f :=
        minpoly.dvd K zE hz_aeval
      have hf_eq_minpoly : f = minpoly K zE :=
        Polynomial.eq_of_monic_of_dvd_of_natDegree_le
          (minpoly.monic hzE_integral) hf_monic hminpoly_dvd
          (by simpa [hf_natDegree, hminpoly_natDegree])
      -- With degree `p`, the minimal polynomial fills the whole Artin-Schreier polynomial.
      exact Or.inr <| by
        simpa [f] using (hf_eq_minpoly ▸ minpoly.irreducible hzE_integral)

/-- Helper for Lemma 15.116.11: the degree-one branch of the Artin-Schreier classifier already
comes from an actual root in the base field. -/
private lemma exists_base_root_of_finrank_eq_one
    (z : L) (hz : z ^ p - z = algebraMap K L ξ)
    (hgen : K⟮z⟯ = ⊤)
    (hfinrank : Module.finrank K L = 1) :
    ∃ t : K, t ^ p - t = ξ := by
  rcases artin_schreier_root_in_base_or_irreducible (A := A) (L := L) (p := p) (ξ := ξ) with
      hroot | hirr
  · -- The source-faithful trivial branch is already an explicit base-field root.
    exact hroot
  · -- Route correction: use the existing irreducible-degree computation to contradict the
    -- degree-one hypothesis instead of rebuilding the adjoin-simple collapse.
    have hp : Module.finrank K L = p :=
      artin_schreier_finrank_eq_p_of_irreducible
        (A := A) (L := L) (p := p) (ξ := ξ) z hz hgen hirr
    have hp_eq_one : p = 1 := hp.symm.trans hfinrank
    exact (Fact.out.ne_one hp_eq_one).elim

/-- Helper for Lemma 15.116.11: the remaining degree split is exactly the source-faithful
Artin-Schreier dichotomy between a base-field root and irreducibility. -/
private lemma artin_schreier_finrank_eq_one_or_p
    (z : L) (hz : z ^ p - z = algebraMap K L ξ)
    (hgen : K⟮z⟯ = ⊤) :
    Module.finrank K L = 1 ∨ Module.finrank K L = p := by
  -- Reuse the simple-extension degree dichotomy established above.
  exact artin_schreier_generator_degree_dichotomy
    (A := A) (p := p) (ξ := ξ) z hz hgen

/-- Helper for Lemma 15.116.11: if a prime `p` factors as `g * e * f` with all three factors at
least `1`, then exactly one factor is `p` and the other two are `1`. -/
private lemma prime_degree_factor_cases
    {g e f : ℕ}
    (hg : 1 ≤ g) (he : 1 ≤ e) (hf : 1 ≤ f)
    (hgef : g * (e * f) = p) :
    (g = p ∧ e = 1 ∧ f = 1) ∨
      (g = 1 ∧ e = p ∧ f = 1) ∨
      (g = 1 ∧ e = 1 ∧ f = p) := by
  have hdivg : g ∣ p := ⟨e * f, hgef.symm⟩
  have hdive : e ∣ p := by
    refine ⟨g * f, ?_⟩
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hgef.symm
  have hdivf : f ∣ p := by
    refine ⟨g * e, ?_⟩
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hgef.symm
  have hg_cases : g = 1 ∨ g = p := (Nat.dvd_prime (Fact.out : Nat.Prime p)).mp hdivg
  have he_cases : e = 1 ∨ e = p := (Nat.dvd_prime (Fact.out : Nat.Prime p)).mp hdive
  have hf_cases : f = 1 ∨ f = p := (Nat.dvd_prime (Fact.out : Nat.Prime p)).mp hdivf
  rcases hg_cases with rfl | rfl
  · rcases he_cases with rfl | rfl
    · exact Or.inr <| Or.inr ⟨rfl, rfl, by simpa using hgef⟩
    · exact Or.inr <| Or.inl ⟨rfl, rfl, by simpa using hgef⟩
  · have hef : e * f = 1 := by
      apply Nat.eq_of_mul_eq_mul_left (Fact.out.pos)
      simpa using hgef
    have he_one : e = 1 := Nat.eq_one_of_dvd_one ⟨f, hef.symm⟩
    have hf_one : f = 1 := Nat.eq_one_of_dvd_one ⟨e, by simpa [Nat.mul_comm] using hef.symm⟩
    exact Or.inl ⟨rfl, he_one, hf_one⟩

/-- Helper for Lemma 15.116.11: a finite extension of prime degree `p` that is not separable has
trivial separable closure, hence is purely inseparable. -/
private lemma prime_finrank_not_separable_isPurelyInseparable
    {F : Type*} {E : Type*} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E]
    (hfinrank : Module.finrank F E = p)
    (hsep : ¬ Algebra.IsSeparable F E) :
    IsPurelyInseparable F E := by
  have hfinSep_dvd : Field.finSepDegree F E ∣ p := by
    -- The separable degree always divides the full finite dimension.
    simpa [hfinrank] using (Field.finSepDegree_dvd_finrank F E)
  have hfinSep_ne_p : Field.finSepDegree F E ≠ p := by
    -- Equality with the prime degree would force the whole extension to be separable.
    intro hEq
    have hEq' : Field.finSepDegree F E = Module.finrank F E := by
      simpa [hfinrank] using hEq
    exact hsep ((Field.finSepDegree_eq_finrank_iff F E).mp hEq')
  have hfinSep_one : Field.finSepDegree F E = 1 := by
    -- The prime divisibility leaves only the `1` and `p` cases, and the latter is excluded above.
    rcases (Nat.dvd_prime (Fact.out : Nat.Prime p)).mp hfinSep_dvd with hOne | hP
    · exact hOne
    · exact (hfinSep_ne_p hP).elim
  have halg : Algebra.IsAlgebraic F E := Algebra.IsAlgebraic.of_finite F E
  rw [← separableClosure.eq_bot_iff (F := F) (E := E)]
  apply (IntermediateField.finrank_eq_one_iff (K := separableClosure F E)).mp
  have hfinSep_one' : Cardinal.toNat (Field.sepDegree F E) = 1 := by
    -- Rewrite the finite separable degree as the finite cardinality of the separable closure.
    simpa [Field.finSepDegree_eq F E] using hfinSep_one
  -- With separable degree `1`, the separable closure itself has dimension `1` over the base.
  simpa [Field.sepDegree] using hfinSep_one'

section ArtinSchreierGenerator

variable (z : L) (hz : z ^ p - z = algebraMap K L ξ)
variable (hgen : K⟮z⟯ = ⊤)

local instance : FiniteDimensional K L :=
  finiteDimensional_of_artinSchreier_generator z hz hgen

local instance : Algebra.IsSeparable K L :=
  isSeparable_of_artinSchreier_generator z hz hgen

local instance [IsDiscreteValuationRing B] :
    FiniteDimensional κA (ResidueField B) :=
  finiteDimensional_residueField_of_integralClosure (A := A) (L := L)

local instance [IsDiscreteValuationRing B] :
    IsExtensionOfDiscreteValuationRings A B :=
  inferInstance

/-- Helper for Lemma 15.116.11: every maximal ideal of the integral closure lies over the maximal
ideal of the base discrete valuation ring. -/
private lemma integralClosure_liesOver_maximalIdeal_of_isMaximal
    (P : Ideal B) [P.IsMaximal] :
    P.LiesOver (maximalIdeal A) := by
  -- The integral-closure map is integral, so maximal ideals upstairs contract to the unique
  -- maximal ideal downstairs.
  exact ⟨(IsLocalRing.eq_maximalIdeal
    (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P)).symm⟩

/-- Helper for Lemma 15.116.11: for a branch of the integral closure above `maximalIdeal A`, the
induced residue-field map is the ambient structure map on residue fields. -/
private lemma integralClosure_residueField_map_eq_algebraMap
    (P : Ideal B) [P.IsMaximal] [P.LiesOver (maximalIdeal A)] :
    Ideal.ResidueField.map (maximalIdeal A) P (algebraMap A B)
        (P.over_def (maximalIdeal A)) =
      algebraMap κA P.ResidueField := by
  -- Both residue-field maps agree on the residue classes of elements of `A`.
  ext a
  rfl

/-- Helper for Lemma 15.116.11: inertia degree `1` identifies the branch residue field with the
base residue field. -/
private lemma residueField_bijective_of_inertiaDeg_eq_one
    (P : Ideal B) [P.IsMaximal] [P.LiesOver (maximalIdeal A)]
    (hP : Ideal.inertiaDeg (maximalIdeal A) P = 1) :
    Function.Bijective
      (Ideal.ResidueField.map (maximalIdeal A) P (algebraMap A B)
        (P.over_def (maximalIdeal A))) := by
  let _ : Algebra κA P.ResidueField := ResidueField.instAlgebra
  have hfinrank : Module.finrank κA P.ResidueField = 1 := by
    -- Rewrite the inertia degree as the residue-field extension degree.
    rw [← Ideal.inertiaDeg_algebraMap (p := maximalIdeal A) (P := P)]
    exact hP
  have hAlgBij : Function.Bijective (algebraMap κA P.ResidueField) :=
    (Algebra.finrank_eq_one_iff_bijective_algebraMap).mp hfinrank
  -- Transport the degree-one field identification back to the canonical residue-field map.
  simpa [integralClosure_residueField_map_eq_algebraMap (A := A) (L := L) (P := P)] using hAlgBij

/-- Helper for Lemma 15.116.11: if there is only one branch of the integral closure above the
maximal ideal of `A`, then the integral closure is itself a discrete valuation ring. -/
private theorem integralClosure_isDiscreteValuationRing_of_unique_branch
    (hunique : ((maximalIdeal A).primesOver B).ncard = 1) :
    IsDiscreteValuationRing B := by
  let _ : IsFractionRing B L := integralClosure.isFractionRing_of_finite_extension K L
  let _ : Module.Finite A B := IsIntegralClosure.finite A K L B
  let _ : IsDedekindDomain B :=
    integralClosure_isDedekindDomain_of_ringKrullDim_eq_one
      (IsPrincipalIdealRing.ringKrullDim_eq_one A (IsDiscreteValuationRing.not_a_field A))
  have hlocal : IsLocalRing B := by
    classical
    obtain ⟨M, hMmax, hMover⟩ :=
      Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := B) (maximalIdeal A)
    have hsub :
        Set.Subsingleton ((maximalIdeal A).primesOver B) :=
      (Set.ncard_le_one_iff_subsingleton.mp hunique.le)
    -- Uniqueness of the branch above `maximalIdeal A` forces uniqueness of maximal ideals in `B`.
    refine IsLocalRing.of_unique_max_ideal ?_
    refine ⟨M, hMmax, ?_⟩
    intro I hI
    letI : I.IsMaximal := hI
    letI : I.LiesOver (maximalIdeal A) :=
      integralClosure_liesOver_maximalIdeal_of_isMaximal (A := A) (L := L) I
    let iBranch : (maximalIdeal A).primesOver B :=
      ⟨I, Ideal.IsMaximal.isPrime hI, inferInstance⟩
    let mBranch : (maximalIdeal A).primesOver B :=
      ⟨M, hMmax.isPrime, hMover⟩
    exact Subtype.ext_iff.mp <| by
      apply Subtype.ext
      exact hsub iBranch.2 mBranch.2
  let _ : IsLocalRing B := hlocal
  let hpid : IsPrincipalIdealRing B :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (R := B)).out 2 0) inferInstance
  have hnot_field : ¬ IsField B := by
    intro hB
    let _ : Field B := hB.toField
    obtain ⟨M, hMmax, hMover⟩ :=
      Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := B) (maximalIdeal A)
    have hMbot : M = ⊥ := (eq_bot_or_eq_top M).resolve_right hMmax.ne_top
    have hAB_inj : Function.Injective (algebraMap A B) := by
      intro x y hxy
      apply FaithfulSMul.algebraMap_injective A L
      change algebraMap B L (algebraMap A B x) = algebraMap B L (algebraMap A B y)
      exact congrArg (algebraMap B L) hxy
    -- If `B` were a field, the branch above `maximalIdeal A` would contract to `⊥`, impossible
    -- for a discrete valuation ring.
    have hmax_bot : maximalIdeal A = (⊥ : Ideal A) := by
      calc
        maximalIdeal A = Ideal.comap (algebraMap A B) M := hMover.symm
        _ = RingHom.ker (algebraMap A B) := by simp [hMbot]
        _ = ⊥ := RingHom.ker_eq_bot.2 hAB_inj
    exact IsDiscreteValuationRing.not_a_field A hmax_bot
  -- A local Dedekind domain with nonzero maximal ideal is a discrete valuation ring.
  exact
    { toIsPrincipalIdealRing := hpid
      toIsLocalRing := hlocal
      not_a_field' := (IsLocalRing.isField_iff_maximalIdeal_eq).not.mp hnot_field }

/-- Helper for Lemma 15.116.11: common ramification index `1` and common inertia degree `1`
already package the prime-degree Galois extension into the unramified owner. -/
private lemma unramified_of_ramificationIdxIn_eq_one_and_inertiaDegIn_eq_one
    (hramification : (maximalIdeal A).ramificationIdxIn B = 1)
    (hinertia : (maximalIdeal A).inertiaDegIn B = 1) :
    IsUnramifiedWithRespectTo A L := by
  -- Each branch has ramification index `1` and residue degree `1`, so the residue extension is
  -- identified with the base residue field and is therefore separable.
  refine
    { residueField_separable := ?_
      ramificationIdx_eq_one := ?_ }
  · intro P _ _
    let _ : Algebra κA P.ResidueField := ResidueField.instAlgebra
    let Pbranch : (maximalIdeal A).primesOver B :=
      ⟨P, Ideal.IsMaximal.isPrime inferInstance, inferInstance⟩
    have hP_inertia : Ideal.inertiaDeg (maximalIdeal A) P = 1 := by
      calc
        Ideal.inertiaDeg (maximalIdeal A) P = (maximalIdeal A).inertiaDegIn B := by
          simpa using
            (inertiaDeg_eq_inertiaDegIn_of_mem_primesOver
              (A := A) (L := L) Pbranch)
        _ = 1 := hinertia
    have hbij :
        Function.Bijective
          (Ideal.ResidueField.map (maximalIdeal A) P (algebraMap A B)
            (P.over_def (maximalIdeal A))) :=
      residueField_bijective_of_inertiaDeg_eq_one
        (A := A) (L := L) (P := P) hP_inertia
    have hbij' : Function.Bijective (algebraMap κA P.ResidueField) := by
      simpa [integralClosure_residueField_map_eq_algebraMap (A := A) (L := L) (P := P)] using hbij
    let eκ : κA ≃ₐ[κA] P.ResidueField :=
      AlgEquiv.ofBijective (algebraMap κA P.ResidueField) hbij'
    -- Transport separability across the degree-one residue-field identification.
    exact AlgEquiv.Algebra.isSeparable eκ
  · intro P _ _
    let Pbranch : (maximalIdeal A).primesOver B :=
      ⟨P, Ideal.IsMaximal.isPrime inferInstance, inferInstance⟩
    -- The common ramification index `1` forces branchwise unramifiedness.
    calc
      ramificationIdx (maximalIdeal A) P = (maximalIdeal A).ramificationIdxIn B := by
        simpa using
          (ramificationIdx_eq_ramificationIdxIn_of_mem_primesOver
            (A := A) (L := L) Pbranch)
      _ = 1 := hramification

/-- Helper for Lemma 15.116.11: a unique branch together with common inertia degree `1` packages
the prime-degree Galois extension into the totally ramified owner. -/
private lemma totally_ramified_of_unique_branch_and_inertiaDegIn_eq_one
    (hunique : ((maximalIdeal A).primesOver B).ncard = 1)
    (hinertia : (maximalIdeal A).inertiaDegIn B = 1) :
    IsTotallyRamifiedWithRespectTo A L := by
  classical
  have hsub :
      Set.Subsingleton ((maximalIdeal A).primesOver B) :=
    Set.ncard_le_one_iff_subsingleton.mp hunique.le
  refine
    { unique_maximalIdeal := ?_
      residueField_bijective := ?_ }
  · intro P Q _ _ _ _
    let Pbranch : (maximalIdeal A).primesOver B :=
      ⟨P, Ideal.IsMaximal.isPrime inferInstance, inferInstance⟩
    let Qbranch : (maximalIdeal A).primesOver B :=
      ⟨Q, Ideal.IsMaximal.isPrime inferInstance, inferInstance⟩
    have hbranch_eq : Pbranch = Qbranch := by
      apply Subtype.ext
      exact hsub Pbranch.2 Qbranch.2
    exact congrArg Subtype.val hbranch_eq
  · intro P _ _
    let Pbranch : (maximalIdeal A).primesOver B :=
      ⟨P, Ideal.IsMaximal.isPrime inferInstance, inferInstance⟩
    have hP_inertia : Ideal.inertiaDeg (maximalIdeal A) P = 1 := by
      calc
        Ideal.inertiaDeg (maximalIdeal A) P = (maximalIdeal A).inertiaDegIn B := by
          simpa using
            (inertiaDeg_eq_inertiaDegIn_of_mem_primesOver
              (A := A) (L := L) Pbranch)
        _ = 1 := hinertia
    -- The degree-one residue extension is exactly the residue-field bijection required by the
    -- totally ramified owner.
    exact
      residueField_bijective_of_inertiaDeg_eq_one
        (A := A) (L := L) (P := P) hP_inertia

/-- Helper for Lemma 15.116.11: in the unique-branch case with common ramification index `1` and
common inertia degree `p`, the extension is either unramified or weakly unramified with purely
inseparable residue field of degree `p`. -/
private lemma unramified_or_weakly_unramified_purelyInseparable_of_unique_branch_case
    (hunique : ((maximalIdeal A).primesOver B).ncard = 1)
    (hramification : (maximalIdeal A).ramificationIdxIn B = 1)
    (hinertia : (maximalIdeal A).inertiaDegIn B = p) :
    IsUnramifiedWithRespectTo A L ∨
      ∃ (_ : IsDiscreteValuationRing B),
        WeaklyUnramified A B ∧
          IsPurelyInseparable κA (ResidueField B) ∧
          residueDegree A B = p := by
  letI : IsDiscreteValuationRing B :=
    integralClosure_isDiscreteValuationRing_of_unique_branch
      (A := A) (L := L) hunique
  letI : (maximalIdeal B).LiesOver (maximalIdeal A) :=
    integralClosure_liesOver_maximalIdeal_of_isMaximal
      (A := A) (L := L) (maximalIdeal B)
  let maxBranch : (maximalIdeal A).primesOver B :=
    ⟨maximalIdeal B, Ideal.IsMaximal.isPrime inferInstance, inferInstance⟩
  have hfinrank_residue : Module.finrank κA (ResidueField B) = p := by
    -- On the unique DVR branch, the common inertia degree is the residue-field dimension.
    calc
      Module.finrank κA (ResidueField B) = Ideal.inertiaDeg (maximalIdeal A) (maximalIdeal B) := by
        symm
        rw [← Ideal.inertiaDeg_algebraMap (p := maximalIdeal A) (P := maximalIdeal B)]
      _ = (maximalIdeal A).inertiaDegIn B := by
        simpa using
          (inertiaDeg_eq_inertiaDegIn_of_mem_primesOver
            (A := A) (L := L) maxBranch)
      _ = p := hinertia
  by_cases hsep : Algebra.IsSeparable κA (ResidueField B)
  · -- If the unique residue extension is separable, then every branch is unramified.
    left
    refine
      { residueField_separable := ?_
        ramificationIdx_eq_one := ?_ }
    · intro P _ _
      have hP_eq : P = maximalIdeal B := IsLocalRing.eq_maximalIdeal inferInstance
      simpa [hP_eq] using hsep
    · intro P _ _
      let Pbranch : (maximalIdeal A).primesOver B :=
        ⟨P, Ideal.IsMaximal.isPrime inferInstance, inferInstance⟩
      calc
        ramificationIdx (maximalIdeal A) P = (maximalIdeal A).ramificationIdxIn B := by
          simpa using
            (ramificationIdx_eq_ramificationIdxIn_of_mem_primesOver
              (A := A) (L := L) Pbranch)
        _ = 1 := hramification
  · -- Otherwise the prime-degree residue extension is purely inseparable, while `e = 1` gives the
    -- weakly unramified owner.
    right
    have hramification_branch :
        ramificationIdx (maximalIdeal A) (maximalIdeal B) = 1 := by
      calc
        ramificationIdx (maximalIdeal A) (maximalIdeal B) = (maximalIdeal A).ramificationIdxIn B := by
          simpa using
            (ramificationIdx_eq_ramificationIdxIn_of_mem_primesOver
              (A := A) (L := L) maxBranch)
        _ = 1 := hramification
    have hweak : WeaklyUnramified A B := by
      -- In the DVR owner, `e = 1` is exactly weak unramifiedness.
      exact
        (weaklyUnramified_iff_ramificationIndex_eq_one (A := A) (B := B)).2 <| by
          simpa [ramificationIndex] using hramification_branch
    have hpi :
        IsPurelyInseparable κA (ResidueField B) :=
      prime_finrank_not_separable_isPurelyInseparable
        (p := p) hfinrank_residue hsep
    refine ⟨inferInstance, hweak, hpi, ?_⟩
    simpa [residueDegree_eq_finrank (A := A) (B := B)] using hfinrank_residue

/-- Helper for Lemma 15.116.11: once the Artin-Schreier extension has prime degree, the
fundamental identity `g * e * f = p` reduces the ramification alternatives to the three
source-facing branches. -/
private lemma prime_degree_galois_ramification_cases
    (hGalois : IsGalois K L) (hdeg : Module.finrank K L = p) :
    IsUnramifiedWithRespectTo A L ∨
      IsTotallyRamifiedWithRespectTo A L ∨
      ∃ (_ : IsDiscreteValuationRing B),
        WeaklyUnramified A B ∧
          IsPurelyInseparable κA (ResidueField B) ∧
          residueDegree A B = p := by
  letI : IsGalois K L := hGalois
  let g : ℕ := ((maximalIdeal A).primesOver B).ncard
  let e : ℕ := (maximalIdeal A).ramificationIdxIn B
  let f : ℕ := (maximalIdeal A).inertiaDegIn B
  have hg : 1 ≤ g := by
    obtain ⟨P, hPmax, hPover⟩ :=
      Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := B) (maximalIdeal A)
    have hnonempty : ((maximalIdeal A).primesOver B).Nonempty := by
      refine ⟨⟨P, Ideal.IsMaximal.isPrime hPmax, hPover⟩, ?_⟩
      simp
    exact Nat.succ_le_of_lt hnonempty.ncard_pos
  have he : 1 ≤ e := by
    simpa [e] using (one_le_ramificationIdxIn (A := A) (L := L))
  have hf : 1 ≤ f := by
    simpa [f] using (one_le_inertiaDegIn (A := A) (L := L))
  have hgef : g * (e * f) = p := by
    calc
      g * (e * f) = Module.finrank K L := by
        symm
        simpa [g, e, f] using
          (finrank_eq_ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
            (A := A) (L := L))
      _ = p := hdeg
  rcases prime_degree_factor_cases hg he hf hgef with
    hcase | hcase | hcase
  · rcases hcase with ⟨-, he_one, hf_one⟩
    -- The `g = p`, `e = 1`, `f = 1` branch is precisely the unramified alternative.
    exact Or.inl <|
      unramified_of_ramificationIdxIn_eq_one_and_inertiaDegIn_eq_one
        (A := A) (L := L) (p := p) (z := z) (hz := hz) (hgen := hgen) he_one hf_one
  · rcases hcase with ⟨hg_one, -, hf_one⟩
    -- A unique branch with residue degree `1` is the totally ramified alternative.
    exact Or.inr <| Or.inl <|
      totally_ramified_of_unique_branch_and_inertiaDegIn_eq_one
        (A := A) (L := L) (p := p) (z := z) (hz := hz) (hgen := hgen) hg_one hf_one
  · rcases hcase with ⟨hg_one, he_one, hf_p⟩
    -- The remaining unique-branch case splits according to separability of the residue extension.
    exact Or.inr <| Or.inr <|
      unramified_or_weakly_unramified_purelyInseparable_of_unique_branch_case
        (A := A) (L := L) (p := p) (z := z) (hz := hz) (hgen := hgen) hg_one he_one hf_p

-- Proof sketch: the polynomial `X ^ p - X - ξ` has derivative `-1`, so adjoining a root gives a
-- separable extension of degree dividing `p`; in characteristic `p` this is the Artin-Schreier
-- situation, hence the extension is Galois. The ramification alternatives come from the
-- classification of Artin-Schreier extensions over a discrete valuation ring, with the trivial
-- case recorded by `Module.finrank K L = 1` because the extension field is an arbitrary `K`-algebra
-- rather than literally the same type as `K`.
/-- Lemma 15.116.11: let `A` be a discrete valuation ring with fraction field `K = FractionRing A`
of characteristic `p > 0`, let `ξ : K`, and let `L` be obtained by adjoining to `K` a root `z`
of `z ^ p - z = ξ`. Then `L / K` is Galois and one of the following happens: the extension is
trivial, recorded as `Module.finrank K L = 1`; the extension is unramified of degree `p`; the
extension is totally ramified of degree `p`; or `B = integralClosure A L` is a discrete valuation
ring such that `A ⊆ B` is weakly unramified and the induced residue-field extension
`ResidueField B / ResidueField A` is purely inseparable of degree `p`. -/
theorem artin_schreier_extension_galois_and_has_ramification_case
    (z : L) (hz : z ^ p - z = algebraMap K L ξ)
    (hgen : K⟮z⟯ = ⊤)
    :
    IsGalois K L ∧
      (Module.finrank K L = 1 ∨
        (Module.finrank K L = p ∧ IsUnramifiedWithRespectTo A L) ∨
        (Module.finrank K L = p ∧ IsTotallyRamifiedWithRespectTo A L) ∨
        ∃ (_ : IsDiscreteValuationRing B),
          WeaklyUnramified A B ∧
            IsPurelyInseparable κA (ResidueField B) ∧
            residueDegree A B = p) := by
  have hGalois : IsGalois K L :=
    artin_schreier_isGalois z hz hgen
  have hdeg : Module.finrank K L = 1 ∨ Module.finrank K L = p :=
    artin_schreier_finrank_eq_one_or_p (A := A) (L := L) (p := p) (ξ := ξ) z hz hgen
  refine ⟨hGalois, ?_⟩
  rcases hdeg with hdeg | hdeg
  · exact Or.inl hdeg
  · -- Route correction: the remaining work is now isolated in the prime-degree ramification
    -- splitter instead of being left inline in the main theorem.
    rcases prime_degree_galois_ramification_cases
        (A := A) (L := L) (p := p)
        hGalois hdeg with hunram | hrest
    · exact Or.inr <| Or.inl ⟨hdeg, hunram⟩
    · rcases hrest with htot | hweak
      · exact Or.inr <| Or.inr <| Or.inl ⟨hdeg, htot⟩
      · exact Or.inr <| Or.inr <| Or.inr hweak

-- TODO: prove the source-faithful finite-étale branch argument for `X ^ p - X - a` over `A`.
-- The intended route is to show every branch `P` of the integral closure is
-- `Algebra.IsUnramifiedAt A P` by using the derivative `-1`, then package that with
-- `IsUnramifiedWithRespectTo.iff_isUnramifiedAt`.
/-- Helper for Lemma 15.116.11: when the Artin-Schreier parameter comes from `A`, the minimal
polynomial of the chosen generator over `A` is separable. -/
private lemma artin_schreier_minpoly_separable_of_mem_ring
    (z : L) (hz : z ^ p - z = algebraMap K L ξ)
    {a : A} (ha : algebraMap A K a = ξ) :
    (minpoly A z).Separable := by
  let f : A[X] := X ^ p - X - C a
  have hf_sep : f.Separable := by
    -- The source polynomial has derivative `-1`, so it is separable already over `A`.
    rw [Polynomial.separable_def']
    refine ⟨0, -1, ?_⟩
    calc
      0 * f + (-1) * derivative f
          = -derivative f := by ring
      _ = -(-1 : A[X]) := by
            congr 1
            calc
              derivative f = derivative (X ^ p : A[X]) - derivative X - derivative (C a) := by
                  simp [f, sub_eq_add_neg, add_assoc]
              _ = C (p : A) * X ^ (p - 1) - 1 := by
                  simp [Polynomial.derivative_X_pow]
              _ = -1 := by
                  have hp_cast : (p : A) = 0 := by
                    apply (IsFractionRing.injective A K)
                    simpa using (CharP.cast_eq_zero K p)
                  simp [hp_cast]
      _ = 1 := by simp
  have hz_aeval : aeval z f = 0 := by
    -- Repackage the Artin-Schreier equation with coefficients in `A`.
    simpa [f, ha, Polynomial.aeval_def, sub_eq_add_neg, add_assoc,
      IsScalarTower.algebraMap_eq A K L] using (sub_eq_zero.mpr hz)
  have hz_integral : IsIntegral A z :=
    stacks_project.Chap15.Lemma_15_116_11.artin_schreier_root_isIntegral_over_base_of_mem_ring
      (A := A) (L := L) (p := p) (ξ := ξ) z hz ⟨a, ha⟩
  -- The minimal polynomial inherits separability from the ambient Artin-Schreier polynomial.
  exact Polynomial.Separable.of_dvd hf_sep (minpoly.isIntegrallyClosed_dvd hz_integral hz_aeval)

/-- Helper for Lemma 15.116.11: if the Artin-Schreier parameter comes from `A`, then the chosen
root is integral over `A`. -/
private lemma artin_schreier_generator_isIntegral_over_base_of_mem_ring
    (z : L) (hz : z ^ p - z = algebraMap K L ξ)
    {a : A} (ha : algebraMap A K a = ξ) :
    IsIntegral A z := by
  -- Reuse the normalization-bridge integrality lemma instead of duplicating the polynomial proof.
  simpa using
    stacks_project.Chap15.Lemma_15_116_11.artin_schreier_root_isIntegral_over_base_of_mem_ring
      (A := A) (L := L) (p := p) (ξ := ξ) z hz ⟨a, ha⟩

/-- Helper for Lemma 15.116.11: if `ξ` comes from `A`, then the monogenic owner `A[z]` already
lies in the normalization `integralClosure A L`. -/
private lemma artin_schreier_adjoin_le_integralClosure_of_mem_ring
    (z : L) (hz : z ^ p - z = algebraMap K L ξ)
    {a : A} (ha : algebraMap A K a = ξ) :
    Algebra.adjoin A ({z} : Set L) ≤ integralClosure A L := by
  -- The forward normalization inclusion is the standard adjoin-by-integral-element step.
  exact
    adjoin_le_integralClosure
      (R := A) (A := L) (x := z)
      (artin_schreier_generator_isIntegral_over_base_of_mem_ring
        (A := A) (L := L) (p := p) (ξ := ξ) z hz ha)

/-- Helper for Lemma 15.116.11: in the monogenic `A`-subalgebra generated by the Artin-Schreier
root, the derivative of the minimal polynomial is a unit. -/
private lemma artin_schreier_adjoin_isUnit_minpoly_derivative_of_mem_ring
    (z : L) (hz : z ^ p - z = algebraMap K L ξ)
    {a : A} (ha : algebraMap A K a = ξ) :
    let x : Algebra.adjoin A ({z} : Set L) :=
      ⟨z, Algebra.subset_adjoin (by simp)⟩
    IsUnit (aeval x (minpoly A z).derivative) := by
  let x : Algebra.adjoin A ({z} : Set L) :=
    ⟨z, Algebra.subset_adjoin (by simp)⟩
  letI : Module.IsTorsionFree A L := Module.IsTorsionFree.trans_faithfulSMul A K L
  have hz_integral : IsIntegral A z :=
    stacks_project.Chap15.Lemma_15_116_11.artin_schreier_root_isIntegral_over_base_of_mem_ring
      (A := A) (L := L) (p := p) (ξ := ξ) z hz ⟨a, ha⟩
  have hsep :
      (minpoly A z).Separable :=
    artin_schreier_minpoly_separable_of_mem_ring
      (A := A) (L := L) (p := p) (ξ := ξ) z hz ha
  let f : A[X] := minpoly A z
  have hx_aeval : aeval x f = 0 := by
    -- The adjoined generator satisfies its minimal polynomial inside the monogenic owner.
    apply Subtype.val_injective
    change (aeval x f : L) = 0
    simpa [x, f] using (minpoly.aeval A z)
  rcases (Polynomial.separable_def' f).1 hsep with ⟨u, v, huv⟩
  have huv_eval : aeval x u * aeval x f + aeval x v * aeval x f.derivative = 1 := by
    -- Evaluating the Bézout identity at the adjoined root isolates the derivative term.
    simpa [f, map_add, map_mul] using congrArg (aeval x) huv
  have hmul : aeval x v * aeval x f.derivative = 1 := by
    simpa [hx_aeval] using huv_eval
  -- A right inverse produced by the Bézout identity makes the derivative value a unit.
  exact IsUnit.of_mul_eq_one _ hmul

/-- Helper for Lemma 15.116.11: if the Artin-Schreier parameter `ξ` comes from the base discrete
valuation ring, then the induced fraction-field extension is unramified with respect to `A`. -/
private theorem artin_schreier_isUnramified_of_mem_ring
    (z : L) (hz : z ^ p - z = algebraMap K L ξ)
    (hgen : K⟮z⟯ = ⊤)
    (hξ : ∃ a : A, algebraMap A K a = ξ) :
    IsUnramifiedWithRespectTo A L := by
  -- Route correction: the main theorem now consumes the single owner-change helper from the
  -- scratch normalization bridge file instead of carrying the transport inline.
  refine (IsUnramifiedWithRespectTo.iff_isUnramifiedAt (A := A) (L := L)).2 ?_
  intro P _ _
  -- Once each branch of `integralClosure A L` is unramified, the source-facing owner follows
  -- from the canonical branchwise criterion.
  exact
    stacks_project.Chap15.Lemma_15_116_11.artin_schreier_integralClosure_branch_isUnramifiedAt_of_mem_ring
      (A := A) (L := L) (p := p) (ξ := ξ) z hz hgen hξ P

/-- Helper for Lemma 15.116.11: a prime-degree branch cannot be both totally ramified and
unramified, because the fundamental identity would force degree `1`. -/
private lemma finrank_eq_one_of_totally_ramified_and_unramified
    (hU : IsUnramifiedWithRespectTo A L)
    (hT : IsTotallyRamifiedWithRespectTo A L) :
    Module.finrank K L = 1 := by
  obtain ⟨P, hPmax, hPover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := B) (maximalIdeal A)
  letI : P.IsMaximal := hPmax
  letI : P.LiesOver (maximalIdeal A) := hPover
  let Pbranch : (maximalIdeal A).primesOver B :=
    ⟨P, Ideal.IsMaximal.isPrime hPmax, hPover⟩
  have hsingle :
      (maximalIdeal A).primesOver B = {Pbranch} := by
    ext Q
    constructor
    · intro hQ
      have hQeq : Q = Pbranch := by
        apply Subtype.ext
        exact hT.unique_maximalIdeal Q.1 P
      simpa [hQeq]
    · intro hQ
      simpa using hQ
  have hbranches :
      ((maximalIdeal A).primesOver B).ncard = 1 := by
    simpa [hsingle]
  have hramification :
      (maximalIdeal A).ramificationIdxIn B = 1 := by
    -- The unique branch inherits ramification index `1` from the unramified owner.
    calc
      (maximalIdeal A).ramificationIdxIn B = Ideal.ramificationIdx (maximalIdeal A) P := by
        symm
        simpa using
          (ramificationIdx_eq_ramificationIdxIn_of_mem_primesOver
            (A := A) (L := L) Pbranch)
      _ = 1 := hU.ramificationIdx_eq_one P
  have hinertia :
      (maximalIdeal A).inertiaDegIn B = 1 := by
    let _ : Algebra κA P.ResidueField := ResidueField.instAlgebra
    have hbij :
        Function.Bijective
          (Ideal.ResidueField.map (maximalIdeal A) P (algebraMap A B)
            (P.over_def (maximalIdeal A))) :=
      hT.residueField_bijective P
    have hbij' : Function.Bijective (algebraMap κA P.ResidueField) := by
      simpa [integralClosure_residueField_map_eq_algebraMap (A := A) (L := L) (P := P)] using hbij
    have hfinrank : Module.finrank κA P.ResidueField = 1 := by
      exact (Algebra.finrank_eq_one_iff_bijective_algebraMap).2 hbij'
    -- Degree-one residue fields force inertia degree `1` on the unique branch.
    calc
      (maximalIdeal A).inertiaDegIn B = Ideal.inertiaDeg (maximalIdeal A) P := by
        symm
        simpa using
          (inertiaDeg_eq_inertiaDegIn_of_mem_primesOver
            (A := A) (L := L) Pbranch)
      _ = 1 := by
        rw [← Ideal.inertiaDeg_algebraMap (p := maximalIdeal A) (P := P)]
        exact hfinrank
  -- With a single branch, ramification index `1`, and inertia degree `1`, the field degree is `1`.
  calc
    Module.finrank K L
        = ((maximalIdeal A).primesOver B).ncard *
            ((maximalIdeal A).ramificationIdxIn B * (maximalIdeal A).inertiaDegIn B) := by
            simpa using
              (finrank_eq_ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
                (A := A) (L := L)).symm
    _ = 1 := by simp [hbranches, hramification, hinertia]

/-- Helper for Lemma 15.116.11: a residue-field extension that is both purely inseparable and
separable has degree `1`. -/
private lemma residueDegree_eq_one_of_purelyInseparable_and_separable
    [IsDiscreteValuationRing B]
    (hpi : IsPurelyInseparable κA (ResidueField B))
    (hsep : Algebra.IsSeparable κA (ResidueField B)) :
    residueDegree A B = 1 := by
  have hfinSep_one : Field.finSepDegree κA (ResidueField B) = 1 := by
    rw [Field.isPurelyInseparable_iff_finSepDegree_eq_one]
    exact hpi
  have hsep_eq :
      Field.finSepDegree κA (ResidueField B) =
        Module.finrank κA (ResidueField B) := by
    exact (Field.finSepDegree_eq_finrank_iff κA (ResidueField B)).2 hsep
  -- Replace the residue degree by the residue-field dimension and compare it with the separable
  -- degree.
  calc
    residueDegree A B = Module.finrank κA (ResidueField B) := residueDegree_eq_finrank (A := A) (B := B)
    _ = 1 := by rw [← hsep_eq, hfinSep_one]

-- Proof sketch: if `ξ` comes from `A`, then the Artin-Schreier polynomial defines a finite étale
-- `A`-algebra. Over a discrete valuation ring this forces either the trivial case or the
-- unramified degree-`p` case.
/-- If `ξ` lies in the discrete valuation ring `A`, then the associated Artin-Schreier extension is
either trivial or unramified of degree `p`. -/
theorem artin_schreier_eq_or_unramified_of_mem_ring
    (z : L) (hz : z ^ p - z = algebraMap K L ξ)
    (hgen : K⟮z⟯ = ⊤)
    (hξ : ∃ a : A, algebraMap A K a = ξ) :
    Module.finrank K L = 1 ∨ (Module.finrank K L = p ∧ IsUnramifiedWithRespectTo A L) := by
  have hU : IsUnramifiedWithRespectTo A L :=
    artin_schreier_isUnramified_of_mem_ring (A := A) (L := L) (p := p) (ξ := ξ) z hz hgen hξ
  rcases artin_schreier_extension_galois_and_has_ramification_case
      (A := A) (L := L) (p := p) (ξ := ξ) z hz hgen with
    ⟨_, hcases⟩
  rcases hcases with hdeg1 | hcases
  · -- The classifier already returns the trivial branch verbatim.
    exact Or.inl hdeg1
  · rcases hcases with hunram | hcases
    · -- The degree-`p` unramified branch is exactly the desired alternative.
      exact Or.inr hunram
    · rcases hcases with htot | hweak
      · rcases htot with ⟨hdegp, htot⟩
        exfalso
        have hdeg1' :
            Module.finrank K L = 1 :=
          finrank_eq_one_of_totally_ramified_and_unramified
            (A := A) (L := L) (p := p) (ξ := ξ) (z := z) (hz := hz) (hgen := hgen) hU htot
        exact (Fact.out.ne_one (hdegp.symm.trans hdeg1')).elim
      · rcases hweak with ⟨hB_dvr, _, hpi, hresdeg⟩
        letI : IsDiscreteValuationRing B := hB_dvr
        letI : (maximalIdeal B).LiesOver (maximalIdeal A) :=
          integralClosure_liesOver_maximalIdeal_of_isMaximal (A := A) (L := L) (maximalIdeal B)
        have hsep : Algebra.IsSeparable κA (ResidueField B) := by
          simpa using hU.residueField_separable (maximalIdeal B)
        have hresdeg_one :
            residueDegree A B = 1 :=
          residueDegree_eq_one_of_purelyInseparable_and_separable
            (A := A) (L := L) (p := p) (ξ := ξ) (z := z) (hz := hz) (hgen := hgen) hpi hsep
        exfalso
        exact (Fact.out.ne_one (hresdeg.symm.trans hresdeg_one)).elim

/-- Helper for Lemma 15.116.11: in the degree-one branch with `p ∣ n`, scaling a base-field root
by `π^(n / p)` makes the residue of `a` into a `p`th power in `ResidueField A`. -/
private lemma artin_schreier_residue_pth_power_of_base_root
    (π : A) (hπ : maximalIdeal A = Ideal.span ({π} : Set A))
    {n : ℕ} (hn : 0 < n) (hdiv : p ∣ n) (a : Aˣ)
    (hroot : ∃ t : K, t ^ p - t = ξ)
    (hξ : ξ = algebraMap A K (a : A) / (algebraMap A K π) ^ n) :
    ∃ b : κA, b ^ p = residue A (a : A) := by
  rcases hdiv with ⟨m, hm⟩
  rcases hroot with ⟨t, ht⟩
  let y : K := (algebraMap A K π) ^ m * t
  have hy_eq :
      y ^ p - algebraMap A K (π ^ ((p - 1) * m)) * y =
        algebraMap A K (a : A) := by
    -- Multiplying the Artin-Schreier equation by `π^(pm)` clears the denominator.
    calc
      y ^ p - algebraMap A K (π ^ ((p - 1) * m)) * y
          = algebraMap A K (π ^ (p * m)) * (t ^ p - t) := by
              dsimp [y]
              have hpow_add : (p - 1) * m + m = p * m := by
                omega
              rw [mul_pow, map_pow]
              rw [show
                algebraMap A K (π ^ ((p - 1) * m)) * ((algebraMap A K π) ^ m * t) =
                  algebraMap A K (π ^ ((p - 1) * m + m)) * t by
                    simp [← pow_add, hpow_add, mul_assoc]]
              ring
      _ = algebraMap A K (π ^ (p * m)) * ξ := by rw [ht]
      _ = algebraMap A K (π ^ (p * m)) *
            (algebraMap A K (a : A) / (algebraMap A K π) ^ (p * m)) := by
              rw [hξ, hm]
      _ = algebraMap A K (a : A) := by
              have hπK0 : algebraMap A K π ≠ 0 :=
                map_ne_zero (IsFractionRing.injective A K)
                  ((IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr hπ).ne_zero
              have hpow0 : (algebraMap A K π) ^ (p * m) ≠ 0 := pow_ne_zero _ hπK0
              field_simp [hpow0]
  let g : A[X] := X ^ p - C (π ^ ((p - 1) * m)) * X - C (a : A)
  have hg_monic : g.Monic := by
    -- The scaled equation still comes from a monic polynomial over the DVR.
    have hp_one : (1 : WithBot ℕ) < p := by
      exact_mod_cast (show 1 < p from (Fact.out : Nat.Prime p).one_lt)
    have hdeg : degree (C (π ^ ((p - 1) * m)) * X + C (a : A) : A[X]) < p := by
      refine lt_of_le_of_lt
        (degree_add_le (C (π ^ ((p - 1) * m)) * X : A[X]) (C (a : A))) ?_
      simpa using hp_one
    simpa [g, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (Polynomial.monic_X_pow_sub
        (p := (C (π ^ ((p - 1) * m)) * X + C (a : A) : A[X])) (n := p) hdeg)
  have hy_aeval : aeval y g = 0 := by
    -- Repackage the scaled equation as a polynomial relation over `A`.
    simpa [g, aeval_def, sub_eq_add_neg, add_assoc] using (sub_eq_zero.mpr hy_eq)
  have hy_integral : IsIntegral A y := ⟨g, hg_monic, hy_aeval⟩
  obtain ⟨c, hc⟩ :=
    (IsIntegrallyClosed.isIntegral_iff.mp hy_integral : ∃ c : A, algebraMap A K c = y)
  have hc_eq :
      c ^ p - π ^ ((p - 1) * m) * c = (a : A) := by
    -- Pull the scaled equation back from the fraction field to the base DVR.
    apply (IsFractionRing.injective A K)
    calc
      algebraMap A K (c ^ p - π ^ ((p - 1) * m) * c)
          = (algebraMap A K c) ^ p - algebraMap A K (π ^ ((p - 1) * m)) * algebraMap A K c := by
              simp [map_sub, map_mul]
      _ = y ^ p - algebraMap A K (π ^ ((p - 1) * m)) * y := by rw [hc]
      _ = algebraMap A K (a : A) := hy_eq
  have hexp_pos : 0 < (p - 1) * m := by
    have hp_sub_pos : 0 < p - 1 := Nat.sub_pos_of_lt (Fact.out : Nat.Prime p).one_lt
    have hm_pos : 0 < m := by
      apply Nat.pos_of_ne_zero
      intro hm_zero
      have hn_zero : n = 0 := by simpa [hm, hm_zero]
      exact (Nat.ne_of_gt hn) hn_zero
    exact Nat.mul_pos hp_sub_pos hm_pos
  have hterm_zero : residue A (π ^ ((p - 1) * m) * c) = 0 := by
    -- A positive power of the uniformizer vanishes in the residue field.
    apply (residue_eq_zero_iff _).2
    have hπ_mem : π ∈ maximalIdeal A := by
      rw [hπ]
      exact Ideal.subset_span (by simp)
    have hpow_mem_pow :
        π ^ ((p - 1) * m) ∈ maximalIdeal A ^ ((p - 1) * m) := by
      simpa using
        (Ideal.pow_mem_pow hπ_mem ((p - 1) * m) :
          π ^ ((p - 1) * m) ∈ maximalIdeal A ^ ((p - 1) * m))
    have hpow_mem : π ^ ((p - 1) * m) ∈ maximalIdeal A := by
      exact (Ideal.pow_le_self (I := maximalIdeal A) (Nat.ne_of_gt hexp_pos)) hpow_mem_pow
    exact Ideal.mul_mem_left _ _ hpow_mem
  refine ⟨residue A c, ?_⟩
  -- Reducing the integral scaled equation modulo `maximalIdeal A` leaves the required `p`th root.
  have hres := congrArg (residue A) hc_eq
  simpa [map_sub, map_mul, hterm_zero] using hres

/-- Helper for Lemma 15.116.11: in a separable characteristic-`p` field extension, a `p`th root
of an element from the base field already comes from the base field. -/
private lemma exists_pth_root_in_base_of_isSeparable
    {F : Type*} {E : Type*} [Field F] [Field E] [Algebra F E]
    {a : F} {y : E} [CharP F p] [Algebra.IsSeparable F E]
    (hy : y ^ p = algebraMap F E a) :
    ∃ x : F, x ^ p = a := by
  have hpow_mem : ∃ n : ℕ, y ^ p ^ n ∈ (algebraMap F E).range := by
    -- The displayed `p`th-power relation already witnesses that `y` generates a purely
    -- inseparable simple subextension.
    refine ⟨1, ?_⟩
    refine ⟨a, ?_⟩
    simpa [hy, pow_one]
  haveI : IsPurelyInseparable F F⟮y⟯ := by
    rw [IntermediateField.isPurelyInseparable_adjoin_simple_iff_pow_mem (F := F) (E := E) p]
    simpa using hpow_mem
  have hy_sep : IsSeparable F y := Algebra.IsSeparable.isSeparable F y
  haveI : Algebra.IsSeparable F F⟮y⟯ :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable F E).2 hy_sep
  have hadjoin_bot : F⟮y⟯ = (⊥ : IntermediateField F E) :=
    IntermediateField.eq_bot_of_isPurelyInseparable_of_isSeparable (F := F) (E := E) F⟮y⟯
  have hy_mem : y ∈ (⊥ : IntermediateField F E) := by
    rw [← hadjoin_bot]
    exact IntermediateField.mem_adjoin_simple_self F y
  rcases (IntermediateField.mem_bot (F := F) (E := E)).mp hy_mem with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  apply FaithfulSMul.algebraMap_injective F E
  simpa [hx] using hy

/-- Helper for Lemma 15.116.11: in the totally ramified branch with `p ∣ n`, scaling the chosen
Artin-Schreier root by `π^(n / p)` produces a residue-field `p`th root of the image of `a`. -/
private lemma artin_schreier_residue_pth_power_of_totally_ramified_branch
    (z : L) (hz : z ^ p - z = algebraMap K L ξ)
    (π : A) (hπ : maximalIdeal A = Ideal.span ({π} : Set A))
    {n : ℕ} (hn : 0 < n) (hdiv : p ∣ n) (a : Aˣ)
    (hξ : ξ = algebraMap A K (a : A) / (algebraMap A K π) ^ n)
    (hT : IsTotallyRamifiedWithRespectTo A L) :
    ∃ b : κA, b ^ p = residue A (a : A) := by
  rcases hdiv with ⟨m, hm⟩
  obtain ⟨P, hPmax, hPover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := B) (maximalIdeal A)
  letI : P.IsMaximal := hPmax
  letI : P.LiesOver (maximalIdeal A) := hPover
  let Pbranch : (maximalIdeal A).primesOver B :=
    ⟨P, Ideal.IsMaximal.isPrime hPmax, hPover⟩
  have hsingle :
      (maximalIdeal A).primesOver B = {Pbranch} := by
    ext Q
    constructor
    · intro hQ
      have hQeq : Q = Pbranch := by
        apply Subtype.ext
        exact hT.unique_maximalIdeal Q.1 P
      simpa [hQeq]
    · intro hQ
      simpa using hQ
  have hbranches :
      ((maximalIdeal A).primesOver B).ncard = 1 := by
    simpa [hsingle]
  letI : IsDiscreteValuationRing B :=
    integralClosure_isDiscreteValuationRing_of_unique_branch
      (A := A) (L := L) hbranches
  letI : (maximalIdeal B).LiesOver (maximalIdeal A) :=
    integralClosure_liesOver_maximalIdeal_of_isMaximal (A := A) (L := L) (maximalIdeal B)
  let yL : L := (algebraMap A L π) ^ m * z
  have hyL_eq :
      yL ^ p - algebraMap A L (π ^ ((p - 1) * m)) * yL =
        algebraMap A L (a : A) := by
    -- Scale the Artin-Schreier equation by `π^(pm)` so the right-hand side becomes integral.
    calc
      yL ^ p - algebraMap A L (π ^ ((p - 1) * m)) * yL
          = algebraMap A L (π ^ (p * m)) * (z ^ p - z) := by
              dsimp [yL]
              have hpow_add : (p - 1) * m + m = p * m := by
                omega
              rw [mul_pow, map_pow]
              rw [show
                algebraMap A L (π ^ ((p - 1) * m)) * ((algebraMap A L π) ^ m * z) =
                  algebraMap A L (π ^ ((p - 1) * m + m)) * z by
                    simp [map_mul, ← pow_add, hpow_add, mul_assoc]]
              ring
      _ = algebraMap A L (π ^ (p * m)) * algebraMap K L ξ := by rw [hz]
      _ = algebraMap A L (π ^ (p * m)) *
            algebraMap K L
              (algebraMap A K (a : A) / (algebraMap A K π) ^ (p * m)) := by
              rw [hξ, hm]
      _ = algebraMap A L (a : A) := by
              have hπK0 : algebraMap A K π ≠ 0 :=
                map_ne_zero (IsFractionRing.injective A K)
                  ((IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr hπ).ne_zero
              have hpow0 : (algebraMap A K π) ^ (p * m) ≠ 0 := pow_ne_zero _ hπK0
              field_simp [hpow0]
  let g : A[X] := X ^ p - C (π ^ ((p - 1) * m)) * X - C (a : A)
  have hg_monic : g.Monic := by
    -- The scaled equation is still cut out by a monic polynomial over `A`.
    have hp_one : (1 : WithBot ℕ) < p := by
      exact_mod_cast (show 1 < p from (Fact.out : Nat.Prime p).one_lt)
    have hdeg : degree (C (π ^ ((p - 1) * m)) * X + C (a : A) : A[X]) < p := by
      refine lt_of_le_of_lt
        (degree_add_le (C (π ^ ((p - 1) * m)) * X : A[X]) (C (a : A))) ?_
      simpa using hp_one
    simpa [g, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (Polynomial.monic_X_pow_sub
        (p := (C (π ^ ((p - 1) * m)) * X + C (a : A) : A[X])) (n := p) hdeg)
  have hyL_aeval : aeval yL g = 0 := by
    -- Repackage the scaled equation as a monic polynomial relation over `A`.
    simpa [g, aeval_def, sub_eq_add_neg, add_assoc] using (sub_eq_zero.mpr hyL_eq)
  have hyL_integral : IsIntegral A yL := ⟨g, hg_monic, hyL_aeval⟩
  let y : B := ⟨yL, hyL_integral⟩
  have hy_eq :
      y ^ p - algebraMap A B (π ^ ((p - 1) * m)) * y =
        algebraMap A B (a : A) := by
    -- Pull the scaled equation back from `L` to the integral-closure DVR `B`.
    apply (IsFractionRing.injective B L)
    calc
      algebraMap B L (y ^ p - algebraMap A B (π ^ ((p - 1) * m)) * y)
          = (algebraMap B L y) ^ p -
              algebraMap A L (π ^ ((p - 1) * m)) * algebraMap B L y := by
                simp [map_sub, map_mul, IsScalarTower.algebraMap_eq A B L,
                  mul_comm, mul_left_comm, mul_assoc]
      _ = yL ^ p - algebraMap A L (π ^ ((p - 1) * m)) * yL := by
            simp [y, yL]
      _ = algebraMap A L (a : A) := hyL_eq
      _ = algebraMap B L (algebraMap A B (a : A)) := by
            simp [IsScalarTower.algebraMap_eq A B L]
  have hexp_pos : 0 < (p - 1) * m := by
    have hp_sub_pos : 0 < p - 1 := Nat.sub_pos_of_lt (Fact.out : Nat.Prime p).one_lt
    have hm_pos : 0 < m := by
      apply Nat.pos_of_ne_zero
      intro hm_zero
      have hn_zero : n = 0 := by simpa [hm, hm_zero]
      exact (Nat.ne_of_gt hn) hn_zero
    exact Nat.mul_pos hp_sub_pos hm_pos
  have hpi_mem_A : π ∈ maximalIdeal A := by
    rw [hπ]
    exact Ideal.subset_span (by simp)
  have hpi_mem_B : algebraMap A B π ∈ maximalIdeal B := by
    rwa [← Ideal.mem_comap] at hpi_mem_A
  have hterm_zero : residue B (algebraMap A B (π ^ ((p - 1) * m)) * y) = 0 := by
    -- The correction term contains a positive power of the maximal-ideal element `π`.
    apply (residue_eq_zero_iff _).2
    have hpow_mem_pow :
        algebraMap A B (π ^ ((p - 1) * m)) ∈ maximalIdeal B ^ ((p - 1) * m) := by
      simpa [RingHom.map_pow] using
        (Ideal.pow_mem_pow hpi_mem_B ((p - 1) * m) : (algebraMap A B π) ^ ((p - 1) * m) ∈
          maximalIdeal B ^ ((p - 1) * m))
    have hpow_mem :
        algebraMap A B (π ^ ((p - 1) * m)) ∈ maximalIdeal B := by
      exact (Ideal.pow_le_self (I := maximalIdeal B) (Nat.ne_of_gt hexp_pos)) hpow_mem_pow
    exact Ideal.mul_mem_left _ _ hpow_mem
  have hresB :
      residue B y ^ p = residue B (algebraMap A B (a : A)) := by
    -- Reducing the scaled equation modulo the maximal ideal leaves only a `p`th-power relation.
    have hres := congrArg (residue B) hy_eq
    simpa [map_sub, map_mul, hterm_zero] using hres
  have hbij :
      Function.Bijective
        (Ideal.ResidueField.map (maximalIdeal A) (maximalIdeal B) (algebraMap A B)
          ((maximalIdeal B).over_def (maximalIdeal A))) :=
    hT.residueField_bijective (maximalIdeal B)
  have hbij' : Function.Bijective (algebraMap κA (ResidueField B)) := by
    simpa [integralClosure_residueField_map_eq_algebraMap (A := A) (L := L)
      (P := maximalIdeal B)] using hbij
  obtain ⟨b, hb⟩ := hbij'.2 (residue B y)
  refine ⟨b, ?_⟩
  apply hbij'.1
  calc
    algebraMap κA (ResidueField B) (b ^ p)
        = (algebraMap κA (ResidueField B) b) ^ p := by simp
    _ = residue B y ^ p := by rw [hb]
    _ = residue B (algebraMap A B (a : A)) := hresB
    _ = algebraMap κA (ResidueField B) (residue A (a : A)) := by
          rw [← integralClosure_residueField_map_eq_algebraMap (A := A) (L := L)
            (P := maximalIdeal B)]
          simp

/-- Helper for Lemma 15.116.11: in the unramified branch with `p ∣ n`, reducing the scaled
Artin-Schreier equation modulo any maximal branch of the integral closure produces a `p`th root of
the image of `a`, and separability descends that root back to `κA`. -/
private lemma artin_schreier_unramified_branch_residue_pth_power
    (z : L) (hz : z ^ p - z = algebraMap K L ξ)
    (π : A) (hπ : maximalIdeal A = Ideal.span ({π} : Set A))
    {n : ℕ} (hn : 0 < n) (hdiv : p ∣ n) (a : Aˣ)
    (hξ : ξ = algebraMap A K (a : A) / (algebraMap A K π) ^ n)
    (hU : IsUnramifiedWithRespectTo A L) :
    ∃ b : κA, b ^ p = residue A (a : A) := by
  rcases hdiv with ⟨m, hm⟩
  obtain ⟨P, hPmax, hPover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := B) (maximalIdeal A)
  letI : P.IsMaximal := hPmax
  letI : P.LiesOver (maximalIdeal A) := hPover
  letI : Algebra κA P.ResidueField := ResidueField.instAlgebra
  let yL : L := (algebraMap A L π) ^ m * z
  have hyL_eq :
      yL ^ p - algebraMap A L (π ^ ((p - 1) * m)) * yL =
        algebraMap A L (a : A) := by
    -- Scale the Artin-Schreier equation by `π^(pm)` so the pole disappears upstairs.
    calc
      yL ^ p - algebraMap A L (π ^ ((p - 1) * m)) * yL
          = algebraMap A L (π ^ (p * m)) * (z ^ p - z) := by
              dsimp [yL]
              have hpow_add : (p - 1) * m + m = p * m := by
                omega
              rw [mul_pow, map_pow]
              rw [show
                algebraMap A L (π ^ ((p - 1) * m)) * ((algebraMap A L π) ^ m * z) =
                  algebraMap A L (π ^ ((p - 1) * m + m)) * z by
                    simp [map_mul, ← pow_add, hpow_add, mul_assoc]]
              ring
      _ = algebraMap A L (π ^ (p * m)) * algebraMap K L ξ := by rw [hz]
      _ = algebraMap A L (π ^ (p * m)) *
            algebraMap K L
              (algebraMap A K (a : A) / (algebraMap A K π) ^ (p * m)) := by
              rw [hξ, hm]
      _ = algebraMap A L (a : A) := by
              have hπK0 : algebraMap A K π ≠ 0 :=
                map_ne_zero (IsFractionRing.injective A K)
                  ((IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr hπ).ne_zero
              have hpow0 : (algebraMap A K π) ^ (p * m) ≠ 0 := pow_ne_zero _ hπK0
              field_simp [hpow0]
  let g : A[X] := X ^ p - C (π ^ ((p - 1) * m)) * X - C (a : A)
  have hg_monic : g.Monic := by
    -- The scaled equation is still cut out by a monic polynomial over `A`.
    have hp_one : (1 : WithBot ℕ) < p := by
      exact_mod_cast (show 1 < p from (Fact.out : Nat.Prime p).one_lt)
    have hdeg : degree (C (π ^ ((p - 1) * m)) * X + C (a : A) : A[X]) < p := by
      refine lt_of_le_of_lt
        (degree_add_le (C (π ^ ((p - 1) * m)) * X : A[X]) (C (a : A))) ?_
      simpa using hp_one
    simpa [g, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (Polynomial.monic_X_pow_sub
        (p := (C (π ^ ((p - 1) * m)) * X + C (a : A) : A[X])) (n := p) hdeg)
  have hyL_aeval : aeval yL g = 0 := by
    -- Repackage the scaled equation as a monic polynomial relation over `A`.
    simpa [g, aeval_def, sub_eq_add_neg, add_assoc] using (sub_eq_zero.mpr hyL_eq)
  have hyL_integral : IsIntegral A yL := ⟨g, hg_monic, hyL_aeval⟩
  let y : B := ⟨yL, hyL_integral⟩
  have hy_eq :
      y ^ p - algebraMap A B (π ^ ((p - 1) * m)) * y =
        algebraMap A B (a : A) := by
    -- Pull the scaled equation back from `L` to the normalization `B`.
    apply (IsFractionRing.injective B L)
    calc
      algebraMap B L (y ^ p - algebraMap A B (π ^ ((p - 1) * m)) * y)
          = (algebraMap B L y) ^ p -
              algebraMap A L (π ^ ((p - 1) * m)) * algebraMap B L y := by
                simp [map_sub, map_mul, IsScalarTower.algebraMap_eq A B L,
                  mul_comm, mul_left_comm, mul_assoc]
      _ = yL ^ p - algebraMap A L (π ^ ((p - 1) * m)) * yL := by
            simp [y, yL]
      _ = algebraMap A L (a : A) := hyL_eq
      _ = algebraMap B L (algebraMap A B (a : A)) := by
            simp [IsScalarTower.algebraMap_eq A B L]
  have hexp_pos : 0 < (p - 1) * m := by
    have hp_sub_pos : 0 < p - 1 := Nat.sub_pos_of_lt (Fact.out : Nat.Prime p).one_lt
    have hm_pos : 0 < m := by
      apply Nat.pos_of_ne_zero
      intro hm_zero
      have hn_zero : n = 0 := by simpa [hm, hm_zero]
      exact (Nat.ne_of_gt hn) hn_zero
    exact Nat.mul_pos hp_sub_pos hm_pos
  have hpi_mem_A : π ∈ maximalIdeal A := by
    rw [hπ]
    exact Ideal.subset_span (by simp)
  have hpi_mem_P : algebraMap A B π ∈ P := by
    rwa [← Ideal.mem_comap, P.over_def (maximalIdeal A)] at hpi_mem_A
  have hterm_zero :
      algebraMap B P.ResidueField
        (algebraMap A B (π ^ ((p - 1) * m)) * y) = 0 := by
    -- The correction term vanishes modulo the chosen branch because it contains a positive power
    -- of the image of the uniformizer.
    apply Ideal.Quotient.eq_zero_iff_mem.2
    have hpow_mem_pow :
        algebraMap A B (π ^ ((p - 1) * m)) ∈ P ^ ((p - 1) * m) := by
      simpa [RingHom.map_pow] using
        (Ideal.pow_mem_pow hpi_mem_P ((p - 1) * m) :
          (algebraMap A B π) ^ ((p - 1) * m) ∈ P ^ ((p - 1) * m))
    have hpow_mem :
        algebraMap A B (π ^ ((p - 1) * m)) ∈ P := by
      exact (Ideal.pow_le_self (I := P) (Nat.ne_of_gt hexp_pos)) hpow_mem_pow
    exact Ideal.mul_mem_left _ _ hpow_mem
  have hresP :
      (algebraMap B P.ResidueField y) ^ p =
        algebraMap κA P.ResidueField (residue A (a : A)) := by
    -- Reducing the scaled equation modulo the chosen branch leaves only a `p`th-power relation.
    have hres := congrArg (algebraMap B P.ResidueField) hy_eq
    calc
      (algebraMap B P.ResidueField y) ^ p
          = algebraMap B P.ResidueField (algebraMap A B (a : A)) := by
              simpa [map_sub, map_mul, hterm_zero] using hres
      _ = algebraMap κA P.ResidueField (residue A (a : A)) := by
            rw [← integralClosure_residueField_map_eq_algebraMap (A := A) (L := L) (P := P)]
            simp
  have hsep : Algebra.IsSeparable κA P.ResidueField := by
    -- Unramifiedness says every branch residue-field extension is separable.
    simpa using hU.residueField_separable P
  -- Descend the branchwise `p`th root back to the base residue field by separability.
  exact
    exists_pth_root_in_base_of_isSeparable
      (p := p) (a := residue A (a : A)) (y := algebraMap B P.ResidueField y) hresP

/-- Helper for Lemma 15.116.11: multiplying by a unit does not change the associated class. -/
private lemma associated_of_unit_mul_left {M : Type*} [CommMonoid M] (u : Units M) (x : M) :
    Associated ((u : M) * x) x := by
  -- Cancel the displayed unit on the right to witness the same associated class.
  refine ⟨u⁻¹, ?_⟩
  simp [mul_assoc, mul_comm]

/-- Helper for Lemma 15.116.11: an association can be rewritten as equality up to a left unit. -/
private lemma eq_unit_mul_of_associated {M : Type*} [CommMonoid M] {x y : M}
    (hxy : Associated x y) :
    ∃ u : Units M, x = (u : M) * y := by
  -- Reverse the association so that the unit multiplies the target into the source.
  rcases hxy.symm with ⟨u, hu⟩
  refine ⟨u, ?_⟩
  simpa [mul_comm] using hu.symm

/-- Helper for Lemma 15.116.11: transporting `ξ = a / π^n` to a discrete-valuation branch rewrites
it as a unit divided by the target uniformizer to the ramification exponent. -/
private lemma artin_schreier_branch_parameter_eq_unit_div_uniformizer_pow
    {C : Type*} {F : Type*}
    [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    [Field F] [Algebra A C] [IsExtensionOfDiscreteValuationRings A C]
    [Algebra C F] [IsFractionRing C F] [Algebra K F]
    [IsScalarTower A C F] [IsScalarTower A K F]
    (π : A) (hπ : maximalIdeal A = Ideal.span ({π} : Set A))
    (τ : C) (hτ : maximalIdeal C = Ideal.span ({τ} : Set C))
    {n : ℕ} (a : Aˣ) :
    ∃ u : Cˣ,
      algebraMap K F (algebraMap A K (a : A) / (algebraMap A K π) ^ n) =
        algebraMap C F (u : C) / (algebraMap C F τ) ^ (n * ramificationIndex A C) := by
  let e : ℕ := ramificationIndex A C
  have hassoc :
      Associated (algebraMap A C π) (τ ^ e) :=
    uniformizer_image_associated_uniformizer_pow_ramificationIndex
      (A := A) (B := C) π τ hπ hτ
  rcases eq_unit_mul_of_associated hassoc with ⟨v, hv⟩
  let u : Cˣ := Units.map (algebraMap A C) a * v⁻¹ ^ n
  have hmapπ :
      algebraMap A F π = algebraMap C F ((v : C) * τ ^ e) := by
    -- Rewrite the branch image of the chosen source uniformizer through the associated target
    -- uniformizer power.
    calc
      algebraMap A F π = algebraMap C F (algebraMap A C π) := by
        simpa [RingHom.comp_apply] using
          DFunLike.congr_fun (IsScalarTower.algebraMap_eq A C F) π
      _ = algebraMap C F ((v : C) * τ ^ e) := by rw [hv]
  refine ⟨u, ?_⟩
  -- Expand the branch image of `π` and absorb the induced unit factor into the numerator.
  calc
    algebraMap K F (algebraMap A K (a : A) / (algebraMap A K π) ^ n)
        =
          algebraMap C F ((Units.map (algebraMap A C) a : Cˣ) : C) /
            (algebraMap C F ((v : C) * τ ^ e)) ^ n := by
              simp [div_eq_mul_inv, hmapπ, IsScalarTower.algebraMap_eq A C F]
    _ = algebraMap C F (u : C) / (algebraMap C F τ) ^ (n * e) := by
          -- The denominator unit contributes only to the numerator after taking the inverse.
          simp [u, e, div_eq_mul_inv, map_mul, map_pow, mul_pow, pow_mul, mul_assoc, mul_comm,
            mul_left_comm, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-- Helper for Lemma 15.116.11: in a DVR fraction field, a positive pole for `x ^ p - x` forces
`x` itself to be a unit divided by a positive power of the chosen uniformizer. -/
private lemma artin_schreier_solution_eq_unit_div_uniformizer_pow
    {C : Type*} {F : Type*}
    [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    [Field F] [Algebra C F] [IsFractionRing C F] [CharP F p]
    (x : F) (τ : C) (hτ : maximalIdeal C = Ideal.span ({τ} : Set C))
    {m : ℕ} (hm : 0 < m) (u : Cˣ)
    (hx :
      x ^ p - x = algebraMap C F (u : C) / (algebraMap C F τ) ^ m) :
    ∃ k : ℕ, 0 < k ∧ ∃ w : Cˣ,
      x = algebraMap C F (w : C) / (algebraMap C F τ) ^ k := by
  let t : F := algebraMap C F τ
  have hp_ne_zero : p ≠ 0 := Fact.out.ne_zero
  have hτirr : Irreducible τ :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer τ).2 hτ
  have ht_ne_zero : t ≠ 0 := by
    intro ht_zero
    exact hτirr.ne_zero ((IsFractionRing.to_map_eq_zero_iff (R := C) (K := F)).1 <| by
      simpa [t] using ht_zero)
  have hrhs_ne_zero : algebraMap C F (u : C) / t ^ m ≠ 0 := by
    have hu_ne_zero : algebraMap C F (u : C) ≠ 0 := by
      intro hu_zero
      exact Units.ne_zero u ((IsFractionRing.to_map_eq_zero_iff (R := C) (K := F)).1 hu_zero)
    exact div_ne_zero hu_ne_zero
      (pow_ne_zero _ ht_ne_zero)
  have hx_ne_zero : x ≠ 0 := by
    intro hx0
    have hlhs_zero : x ^ p - x = 0 := by simp [hx0, hp_ne_zero]
    have hrhs_zero : algebraMap C F (u : C) / t ^ m = 0 := by simpa [hx] using hlhs_zero
    exact hrhs_ne_zero hrhs_zero
  obtain ⟨a, b, hb, hfrac⟩ := IsFractionRing.div_surjective C x
  have hb_ne_zero : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hbF_ne_zero : algebraMap C F b ≠ 0 := by
    intro hb_zero
    exact hb_ne_zero ((IsFractionRing.to_map_eq_zero_iff (R := C) (K := F)).1 hb_zero)
  by_cases ha_zero : a = 0
  · have hx_zero : x = 0 := by
      simpa [ha_zero] using hfrac.symm
    exact (hx_ne_zero hx_zero).elim
  obtain ⟨i, ua, ha⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (R := C) ha_zero hτirr
  obtain ⟨j, ub, hbpow⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (R := C) hb_ne_zero hτirr
  by_cases hij : j ≤ i
  · let c : C := (((ua * ub⁻¹ : Cˣ) : C) * τ ^ (i - j))
    have hx_integral : x = algebraMap C F c := by
      -- Rewrite the fraction with nonnegative exponent difference as an honest element of `C`.
      have hfrac_eq : algebraMap C F a / algebraMap C F b = algebraMap C F c := by
        apply (div_eq_iff hbF_ne_zero).2
        rw [ha, hbpow]
        have hpow : t ^ i = t ^ (i - j) * t ^ j := by
          rw [Nat.sub_add_cancel hij, pow_add]
        simp [c, t, map_mul, map_pow, hpow, mul_assoc, mul_left_comm, mul_comm]
      exact hfrac.symm.trans hfrac_eq
    have hcross : algebraMap C F (c ^ p - c) * t ^ m = algebraMap C F (u : C) := by
      -- Multiplying by the denominator shows the right-hand side would come from `C`.
      calc
        algebraMap C F (c ^ p - c) * t ^ m
            = (x ^ p - x) * t ^ m := by
                rw [hx_integral]
                simp [t, map_sub, map_pow, map_mul, mul_assoc, mul_left_comm, mul_comm]
        _ = (algebraMap C F (u : C) / t ^ m) * t ^ m := by rw [hx]
        _ = algebraMap C F (u : C) := by
              field_simp [pow_ne_zero _ ht_ne_zero]
    have hcrossC : (c ^ p - c) * τ ^ m = (u : C) := by
      apply (IsFractionRing.injective C F)
      simpa [t, map_mul, map_pow] using hcross
    have hτm_unit : IsUnit (τ ^ m) := by
      have hunit_mul : IsUnit ((c ^ p - c) * τ ^ m) := by simpa [hcrossC] using u.isUnit
      have hunit_mul' : IsUnit (τ ^ m * (c ^ p - c)) := by simpa [mul_comm] using hunit_mul
      exact isUnit_of_mul_isUnit_left hunit_mul'
    have hτ_unit : IsUnit τ := by
      have hτ_dvd : τ ∣ τ ^ m := by
        rcases m with _ | n
        · exact (Nat.lt_irrefl 0 hm).elim
        · exact ⟨τ ^ n, by simp [pow_succ]⟩
      exact isUnit_of_dvd_unit hτ_dvd hτm_unit
    exact (hτirr.not_isUnit hτ_unit).elim
  · have hlt : i < j := lt_of_not_ge hij
    let k : ℕ := j - i
    have hk_pos : 0 < k := Nat.sub_pos_of_lt hlt
    let w : Cˣ := ua * ub⁻¹
    refine ⟨k, hk_pos, w, ?_⟩
    -- After isolating the negative exponent difference, `x` has the required unit-over-power form.
    have hfrac_eq : algebraMap C F a / algebraMap C F b = algebraMap C F (w : C) / t ^ k := by
      apply (div_eq_div_iff hbF_ne_zero (pow_ne_zero _ ht_ne_zero)).2
      rw [ha, hbpow]
      have hpow : t ^ j = t ^ i * t ^ (j - i) := by
        rw [Nat.sub_add_cancel (Nat.le_of_lt hlt), pow_add]
      simp [k, w, t, map_mul, map_pow, hpow, mul_assoc, mul_left_comm, mul_comm]
    exact hfrac.symm.trans hfrac_eq

/-- Helper for Lemma 15.116.11: the numerator in the normalized Artin-Schreier pole computation
remains a unit because the correction term lies in the maximal ideal. -/
private lemma artin_schreier_rhs_numerator_isUnit
    {C : Type*}
    [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    (τ : C) (hτ : maximalIdeal C = Ideal.span ({τ} : Set C))
    (w : Cˣ) {k : ℕ} (hk : 0 < k) :
    IsUnit ((w : C) ^ p - (w : C) * τ ^ ((p - 1) * k)) := by
  have hp_sub_pos : 0 < p - 1 := Nat.sub_pos_of_lt (Fact.out : Nat.Prime p).one_lt
  have hexp_pos : 0 < (p - 1) * k := Nat.mul_pos hp_sub_pos hk
  have hτ_mem : τ ∈ maximalIdeal C := by
    rw [hτ]
    exact Ideal.subset_span (by simp)
  have hpow_mem_pow : τ ^ ((p - 1) * k) ∈ maximalIdeal C ^ ((p - 1) * k) := by
    simpa using (Ideal.pow_mem_pow hτ_mem ((p - 1) * k) : τ ^ ((p - 1) * k) ∈
      maximalIdeal C ^ ((p - 1) * k))
  have hpow_mem : τ ^ ((p - 1) * k) ∈ maximalIdeal C := by
    exact (Ideal.pow_le_self (I := maximalIdeal C) (Nat.ne_of_gt hexp_pos)) hpow_mem_pow
  have hscaled_mem :
      (((((w⁻¹ : Cˣ) : C) ^ (p - 1)) * τ ^ ((p - 1) * k)) : C) ∈ maximalIdeal C := by
    exact Ideal.mul_mem_left _ _ hpow_mem
  have hJac : maximalIdeal C ≤ Ring.jacobson C := by
    simpa [Ideal.jacobson_bot] using
      (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal C))
  have hinner_unit :
      IsUnit
        (1 - (((w⁻¹ : Cˣ) : C) ^ (p - 1) * τ ^ ((p - 1) * k) : C)) := by
    have hneg_mem :
        -((((w⁻¹ : Cˣ) : C) ^ (p - 1) * τ ^ ((p - 1) * k) : C)) ∈ maximalIdeal C := by
      exact (maximalIdeal C).neg_mem hscaled_mem
    simpa [sub_eq_add_neg, add_comm] using
      (ideal_le_ring_jacobson_iff_isUnit_one_add (R := C) (I := maximalIdeal C)).1 hJac
        (-((((w⁻¹ : Cˣ) : C) ^ (p - 1) * τ ^ ((p - 1) * k) : C))) hneg_mem
  -- Factor off the obvious unit and apply the local-ring criterion to the correction term.
  have hfactor :
      (w : C) ^ p - (w : C) * τ ^ ((p - 1) * k) =
        (w : C) ^ p * (1 - (((w⁻¹ : Cˣ) : C) ^ (p - 1) * τ ^ ((p - 1) * k)) : C) := by
    have hcancel :
        (w : C) ^ p * (((w⁻¹ : Cˣ) : C) ^ (p - 1)) = (w : C) := by
      simp [mul_assoc, mul_left_comm, mul_comm]
    calc
      (w : C) ^ p - (w : C) * τ ^ ((p - 1) * k)
          = (w : C) ^ p - (w : C) ^ p * (((w⁻¹ : Cˣ) : C) ^ (p - 1) * τ ^ ((p - 1) * k)) := by
              rw [mul_assoc, mul_assoc, mul_assoc]
              simp [hcancel, mul_assoc, mul_left_comm, mul_comm]
      _ = (w : C) ^ p * (1 - (((w⁻¹ : Cˣ) : C) ^ (p - 1) * τ ^ ((p - 1) * k)) : C) := by
            ring
  rw [hfactor]
  exact (w.isUnit.pow p).mul hinner_unit

/-- Helper for Lemma 15.116.11: once `x` is normalized to `unit / τ^k`, the pole order of
`x ^ p - x` is exactly `p * k`. -/
private lemma artin_schreier_rhs_exponent_eq_char_mul
    {C : Type*} {F : Type*}
    [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    [Field F] [Algebra C F] [IsFractionRing C F] [CharP F p]
    (x : F) (τ : C) (hτ : maximalIdeal C = Ideal.span ({τ} : Set C))
    {m k : ℕ} (hk : 0 < k) (u w : Cˣ)
    (hxw : x = algebraMap C F (w : C) / (algebraMap C F τ) ^ k)
    (hx :
      x ^ p - x = algebraMap C F (u : C) / (algebraMap C F τ) ^ m) :
    m = p * k := by
  let t : F := algebraMap C F τ
  let num : C := (w : C) ^ p - (w : C) * τ ^ ((p - 1) * k)
  have ht_ne_zero : t ≠ 0 := by
    have hτirr : Irreducible τ :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer τ).2 hτ
    intro ht_zero
    exact hτirr.ne_zero ((IsFractionRing.to_map_eq_zero_iff (R := C) (K := F)).1 <| by
      simpa [t] using ht_zero)
  have hnum_unit : IsUnit num :=
    artin_schreier_rhs_numerator_isUnit (p := p) τ hτ w hk
  have hx_num :
      x ^ p - x = algebraMap C F num / t ^ (p * k) := by
    -- Put both terms over the common denominator `τ^(pk)` and collect the numerator.
    have hmul :
        (x ^ p - x) * t ^ (p * k) = algebraMap C F num := by
      rw [hxw]
      field_simp [num, t, pow_ne_zero _ ht_ne_zero]
      simp [map_sub, map_mul, map_pow, pow_mul, mul_assoc, mul_left_comm, mul_comm]
    apply (eq_div_iff (pow_ne_zero _ ht_ne_zero)).2
    simpa [mul_comm] using hmul
  have hfrac :
      algebraMap C F num / t ^ (p * k) =
        algebraMap C F (u : C) / t ^ m := by
    exact hx_num.symm.trans hx
  have hcross :
      algebraMap C F num * t ^ m =
        algebraMap C F (u : C) * t ^ (p * k) := by
    exact (div_eq_div_iff (pow_ne_zero _ ht_ne_zero) (pow_ne_zero _ ht_ne_zero)).1 hfrac
  have hcrossC : num * τ ^ m = (u : C) * τ ^ (p * k) := by
    apply (IsFractionRing.injective C F)
    simpa [t, map_mul, map_pow, mul_assoc, mul_left_comm, mul_comm] using hcross
  rcases hnum_unit with ⟨v, hv⟩
  have hleft : Associated (num * τ ^ m) (τ ^ m) := by
    simpa [hv, mul_comm] using associated_of_unit_mul_left v (τ ^ m)
  have hright : Associated ((u : C) * τ ^ (p * k)) (τ ^ (p * k)) := by
    simpa [mul_comm] using associated_of_unit_mul_left u (τ ^ (p * k))
  have hpow :
      Associated (τ ^ m) (τ ^ (p * k)) := by
    have heq_assoc : Associated (num * τ ^ m) ((u : C) * τ ^ (p * k)) := by
      simpa [hcrossC] using (Associated.refl (num * τ ^ m))
    exact Associated.trans hleft.symm <| Associated.trans heq_assoc hright
  exact uniformizer_power_associated_injective τ hτ hpow

/-- Helper for Lemma 15.116.11: in a DVR fraction field, a negative Artin-Schreier pole has order
divisible by `p`. -/
private lemma artin_schreier_pole_order_exponent_dvd_char
    {C : Type*} {F : Type*}
    [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    [Field F] [Algebra C F] [IsFractionRing C F] [CharP F p]
    (x : F) (τ : C) (hτ : maximalIdeal C = Ideal.span ({τ} : Set C))
    {m : ℕ} (hm : 0 < m) (u : Cˣ)
    (hx :
      x ^ p - x = algebraMap C F (u : C) / (algebraMap C F τ) ^ m) :
    p ∣ m := by
  rcases artin_schreier_solution_eq_unit_div_uniformizer_pow
      (p := p) (x := x) τ hτ hm u hx with ⟨k, hk, w, hxw⟩
  have hmk : m = p * k :=
    artin_schreier_rhs_exponent_eq_char_mul
      (p := p) (x := x) τ hτ hk u w hxw hx
  exact ⟨k, hmk⟩

/-- Helper for Lemma 15.116.11: every non-totally-ramified branch in the `p ∤ n` denominator case
should contradict the source valuation computation. -/
private lemma artin_schreier_non_totally_ramified_cases_contradict_uniformizer_denominator
    (z : L) (hz : z ^ p - z = algebraMap K L ξ)
    (hgen : K⟮z⟯ = ⊤)
    (π : A) (hπ : maximalIdeal A = Ideal.span ({π} : Set A))
    {n : ℕ} (hn : 0 < n) (hndiv : ¬ p ∣ n) (a : Aˣ)
    (hξ : ξ = algebraMap A K (a : A) / (algebraMap A K π) ^ n) :
    ¬ (Module.finrank K L = 1 ∨
        (Module.finrank K L = p ∧ IsUnramifiedWithRespectTo A L) ∨
        ∃ (_ : IsDiscreteValuationRing B),
          WeaklyUnramified A B ∧
            IsPurelyInseparable κA (ResidueField B) ∧
            residueDegree A B = p) := by
  intro hcases
  rcases hcases with hdeg1 | hcases
  · rcases exists_base_root_of_finrank_eq_one
      (A := A) (L := L) (p := p) (ξ := ξ) z hz hgen hdeg1 with ⟨t, ht⟩
    have hdiv :
        p ∣ n :=
      artin_schreier_pole_order_exponent_dvd_char
        (p := p) (C := A) (F := K) (x := t) π hπ hn a <| by
          simpa [hξ] using ht
    exact hndiv hdiv
  · rcases hcases with hunram | hweak
    · -- Route correction: localize at one maximal branch `P`, use unramifiedness to get the
      -- branch-local maximal-ideal equality, convert that to ramification index `1`, and then
      -- transport the denominator equation to the localized DVR branch.
      obtain ⟨P, hPmax, hPover⟩ :=
        Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := B) (maximalIdeal A)
      letI : P.IsMaximal := hPmax
      letI : P.LiesOver (maximalIdeal A) := hPover
      let C := Localization.AtPrime P
      letI : IsDomain C := inferInstance
      letI : Algebra A C :=
        (Localization.localRingHom (maximalIdeal A) P
          (algebraMap A B) (P.over_def (maximalIdeal A))).toAlgebra
      letI : IsScalarTower A B C := by
        refine ⟨fun x ↦ ?_⟩
        simp [C, Localization.localRingHom_to_map]
      letI : IsDedekindDomain B :=
        integralClosure_isDedekindDomain_of_ringKrullDim_eq_one
          (IsPrincipalIdealRing.ringKrullDim_eq_one A
            (IsDiscreteValuationRing.not_a_field A))
      have hP_ne_bot : P ≠ ⊥ :=
        Ideal.ne_bot_of_liesOver_of_ne_bot
          (IsDiscreteValuationRing.not_a_field A) P
      letI : IsDiscreteValuationRing C := by
        simpa [C] using
          (IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
            B hP_ne_bot (Localization.AtPrime P))
      have hBC_local : IsLocalHom (algebraMap B C) := by
        simpa [C, Localization.localRingHom_to_map] using
          (Localization.isLocalHom_localRingHom
            P P (algebraMap B B) rfl)
      have hBC_injective : Function.Injective (algebraMap B C) :=
        IsLocalization.injective C P.primeCompl_le_nonZeroDivisors
      letI : IsExtensionOfDiscreteValuationRings B C :=
        { toIsLocalHom := hBC_local
          algebraMap_injective := hBC_injective }
      letI : IsExtensionOfDiscreteValuationRings A C :=
        IsExtensionOfDiscreteValuationRings.of_tower A B C
      let branchToL : C →ₐ[B] L :=
        Localization.mapToFractionRing
          L P.primeCompl C P.primeCompl_le_nonZeroDivisors
      letI : Algebra C L := branchToL.toAlgebra
      letI : IsScalarTower B C L := by
        refine ⟨fun x ↦ ?_⟩
        exact branchToL.commutes x
      letI : IsScalarTower A C L := by
        refine ⟨fun x ↦ ?_⟩
        -- Compare the localized branch map with the ambient `A → L` structure through `B`.
        rw [show algebraMap A C x =
          (Localization.localRingHom (maximalIdeal A) P
            (algebraMap A B) (P.over_def (maximalIdeal A))) x by
              rfl]
        rw [Localization.localRingHom_to_map]
        calc
          branchToL ((algebraMap B C) (algebraMap A B x))
              = algebraMap B L (algebraMap A B x) := by
                  exact branchToL.commutes (algebraMap A B x)
          _ = algebraMap A L x := by
                rw [IsScalarTower.algebraMap_eq A B L]
                rfl
      letI : IsFractionRing C L :=
        IsFractionRing.isFractionRing_of_isLocalization
          P.primeCompl C L P.primeCompl_le_nonZeroDivisors
      obtain ⟨τ, _, hτ⟩ := exists_uniformizer_generator C
      have hAt : Algebra.IsUnramifiedAt A P :=
        (IsUnramifiedWithRespectTo.iff_isUnramifiedAt (A := A) (L := L)).1 hunram.2 P
      have hmap_maximal :
          Ideal.map (algebraMap A C) (maximalIdeal A) = maximalIdeal C :=
        (Algebra.isUnramifiedAt_iff_map_eq A (maximalIdeal A) P).mp hAt |>.2
      have hweakAC : WeaklyUnramified A C :=
        (weaklyUnramified_iff_map_maximalIdeal (A := A) (B := C)).2 hmap_maximal
      have hram_one : ramificationIndex A C = 1 :=
        (weaklyUnramified_iff_ramificationIndex_eq_one (A := A) (B := C)).1 hweakAC
      obtain ⟨u, hu⟩ :=
        artin_schreier_branch_parameter_eq_unit_div_uniformizer_pow
          (A := A) (K := K) (C := C) (F := L) π hπ τ hτ (n := n) a
      have hm_pos : 0 < n * ramificationIndex A C := by
        simpa [hram_one] using hn
      have hz_branch :
          z ^ p - z =
            algebraMap C L (u : C) / (algebraMap C L τ) ^
              (n * ramificationIndex A C) := by
        -- Rewrite the Artin-Schreier parameter through the localized branch denominator data.
        calc
          z ^ p - z = algebraMap K L ξ := hz
          _ =
              algebraMap K L
                (algebraMap A K (a : A) / (algebraMap A K π) ^ n) := by rw [hξ]
          _ =
              algebraMap C L (u : C) / (algebraMap C L τ) ^
                (n * ramificationIndex A C) := hu
      have hdiv :
          p ∣ n * ramificationIndex A C :=
        artin_schreier_pole_order_exponent_dvd_char
          (p := p) (C := C) (F := L) (x := z) τ hτ hm_pos u hz_branch
      have hn_div : p ∣ n := by simpa [hram_one] using hdiv
      exact hndiv hn_div
    · rcases hweak with ⟨hB_dvr, hweakAB, _, _⟩
      letI : IsDiscreteValuationRing B := hB_dvr
      letI : (maximalIdeal B).LiesOver (maximalIdeal A) :=
        integralClosure_liesOver_maximalIdeal_of_isMaximal (A := A) (L := L) (maximalIdeal B)
      obtain ⟨τ, _, hτ⟩ := exists_uniformizer_generator B
      obtain ⟨u, hu⟩ :=
        artin_schreier_branch_parameter_eq_unit_div_uniformizer_pow
          (A := A) (K := K) (C := B) (F := L) π hπ τ hτ (n := n) a
      have hram_one : ramificationIndex A B = 1 :=
        (weaklyUnramified_iff_ramificationIndex_eq_one (A := A) (B := B)).1 hweakAB
      have hm_pos : 0 < n * ramificationIndex A B := by
        simpa [hram_one] using hn
      have hz_branch :
          z ^ p - z =
            algebraMap B L (u : B) / (algebraMap B L τ) ^ (n * ramificationIndex A B) := by
        -- Rewrite the Artin-Schreier parameter through the branch-specific unit/uniformizer shape.
        calc
          z ^ p - z = algebraMap K L ξ := hz
          _ =
              algebraMap K L
                (algebraMap A K (a : A) / (algebraMap A K π) ^ n) := by rw [hξ]
          _ =
              algebraMap B L (u : B) / (algebraMap B L τ) ^
                (n * ramificationIndex A B) := hu
      have hdiv :
          p ∣ n * ramificationIndex A B :=
        artin_schreier_pole_order_exponent_dvd_char
          (p := p) (C := B) (F := L) (x := z) τ hτ hm_pos u hz_branch
      have hn_div : p ∣ n := by simpa [hram_one] using hdiv
      exact hndiv hn_div

/-- Helper for Lemma 15.116.11: outside the weakly-unramified purely inseparable residue branch,
the `p ∣ n` denominator case should force the residue of `a` to become a `p`th power in `κA`. -/
private lemma artin_schreier_non_weakly_unramified_residue_cases_force_pth_power
    (z : L) (hz : z ^ p - z = algebraMap K L ξ)
    (hgen : K⟮z⟯ = ⊤)
    (π : A) (hπ : maximalIdeal A = Ideal.span ({π} : Set A))
    {n : ℕ} (hn : 0 < n) (hdiv : p ∣ n) (a : Aˣ)
    (hξ : ξ = algebraMap A K (a : A) / (algebraMap A K π) ^ n) :
    (Module.finrank K L = 1 ∨
      (Module.finrank K L = p ∧ IsUnramifiedWithRespectTo A L) ∨
      (Module.finrank K L = p ∧ IsTotallyRamifiedWithRespectTo A L)) →
        ∃ b : κA, b ^ p = residue A (a : A) := by
  intro hcases
  rcases hcases with hdeg1 | hcases
  · -- The degree-one branch already gives a base-field root, so the base scaling argument applies.
    have hroot :
        ∃ t : K, t ^ p - t = ξ :=
      exists_base_root_of_finrank_eq_one
        (A := A) (L := L) (p := p) (ξ := ξ) z hz hgen hdeg1
    exact
      artin_schreier_residue_pth_power_of_base_root
        (A := A) (p := p) (ξ := ξ) π hπ hn hdiv a hroot hξ
  · rcases hcases with hunram | htot
    · -- Route correction: reduce the scaled equation modulo an arbitrary maximal branch of the
      -- normalization and descend the resulting residue-field root by separability.
      exact
        artin_schreier_unramified_branch_residue_pth_power
          (A := A) (L := L) (p := p) (ξ := ξ) z hz π hπ hn hdiv a hξ hunram.2
    · -- In the totally ramified branch, the integral closure is a DVR and the scaled-root
      -- calculation can be carried out directly there.
      exact
        artin_schreier_residue_pth_power_of_totally_ramified_branch
          (A := A) (L := L) (p := p) (ξ := ξ) z hz π hπ hn hdiv a hξ htot.2

-- Proof sketch: write the chosen root `z` in a localization of the integral closure of `A` and
-- compare valuations in the equation `z ^ p - z = ξ`. When the pole order `n` of `ξ` is positive
-- and not divisible by `p`, the valuation computation shows that the ramification index is
-- divisible by `p`; since the degree is at most `p`, the integral closure must be a discrete
-- valuation ring and the extension is totally ramified with ramification index `p`.
/-- If `ξ = π^{-n} a` with `n > 0`, `p ∤ n`, and `a` a unit of `A`, then the associated
Artin-Schreier extension is in the totally ramified case with ramification index `p`. -/
theorem artin_schreier_totally_ramified_of_uniformizer_denominator
    (z : L) (hz : z ^ p - z = algebraMap K L ξ)
    (hgen : K⟮z⟯ = ⊤)
    (π : A) (hπ : maximalIdeal A = Ideal.span ({π} : Set A))
    {n : ℕ} (hn : 0 < n) (hndiv : ¬ p ∣ n) (a : Aˣ)
    (hξ : ξ = algebraMap A K (a : A) / (algebraMap A K π) ^ n) :
    Module.finrank K L = p ∧ IsTotallyRamifiedWithRespectTo A L := by
  rcases artin_schreier_extension_galois_and_has_ramification_case
      (A := A) (L := L) (p := p) (ξ := ξ) z hz hgen with
    ⟨_, hcases⟩
  rcases hcases with hdeg1 | hcases
  · have hroot :
        ∃ t : K, t ^ p - t = ξ :=
      exists_base_root_of_finrank_eq_one
        (A := A) (L := L) (p := p) (ξ := ξ) z hz hgen hdeg1
    -- Route correction: the degree-one branch is one of the three cases ruled out by the
    -- denominator obstruction frontier packaged just above.
    exfalso
    exact
      artin_schreier_non_totally_ramified_cases_contradict_uniformizer_denominator
        (A := A) (L := L) (p := p) (ξ := ξ) z hz hgen π hπ hn hndiv a hξ
        (Or.inl hdeg1)
  · rcases hcases with hunram | hcases
    · -- The unramified degree-`p` branch is ruled out by the same local denominator obstruction.
      exfalso
      exact
        artin_schreier_non_totally_ramified_cases_contradict_uniformizer_denominator
          (A := A) (L := L) (p := p) (ξ := ξ) z hz hgen π hπ hn hndiv a hξ
          (Or.inr <| Or.inl hunram)
    · rcases hcases with htot | hweak
      · -- The totally ramified degree-`p` branch is exactly the desired conclusion.
        exact htot
      · -- The weakly unramified DVR branch is the final non-total case excluded by the frontier.
        exfalso
        exact
          artin_schreier_non_totally_ramified_cases_contradict_uniformizer_denominator
            (A := A) (L := L) (p := p) (ξ := ξ) z hz hgen π hπ hn hndiv a hξ
            (Or.inr <| Or.inr hweak)

-- Proof sketch: after multiplying the Artin-Schreier equation by the `p`th power of a
-- uniformizer, rewrite it in integral form over `A`. The resulting integral closure is weakly
-- unramified over `A`, and the assumption that the residue of `a` is not a `p`th power forces the
-- residue-field extension to be purely inseparable of degree `p`.
/-- If `ξ = π^{-n} a` with `n > 0`, `p ∣ n`, and the residue class of the unit `a` is not a `p`th
power in `ResidueField A`, then `B = integralClosure A L` is a discrete valuation ring such that
`A ⊆ B` is weakly unramified and the residue-field extension `ResidueField B / ResidueField A` is
purely inseparable of degree `p`. -/
theorem artin_schreier_weakly_unramified_residue_case_of_uniformizer_denominator
    (z : L) (hz : z ^ p - z = algebraMap K L ξ)
    (hgen : K⟮z⟯ = ⊤)
    (π : A) (hπ : maximalIdeal A = Ideal.span ({π} : Set A))
    {n : ℕ} (hn : 0 < n) (hdiv : p ∣ n) (a : Aˣ)
    (ha : ¬ ∃ b : κA, b ^ p = residue A (a : A))
    (hξ : ξ = algebraMap A K (a : A) / (algebraMap A K π) ^ n) :
    ∃ (_ : IsDiscreteValuationRing B),
      WeaklyUnramified A B ∧
        IsPurelyInseparable κA (ResidueField B) ∧
        residueDegree A B = p := by
  rcases artin_schreier_extension_galois_and_has_ramification_case
      (A := A) (L := L) (p := p) (ξ := ξ) z hz hgen with
    ⟨_, hcases⟩
  rcases hcases with hdeg1 | hcases
  · have hroot :
        ∃ t : K, t ^ p - t = ξ :=
      exists_base_root_of_finrank_eq_one
        (A := A) (L := L) (p := p) (ξ := ξ) z hz hgen hdeg1
    -- Route correction: handle the degree-one branch directly in `K` by scaling the base root.
    exfalso
    exact ha <|
      artin_schreier_residue_pth_power_of_base_root
        (A := A) (p := p) (ξ := ξ) π hπ hn hdiv a hroot hξ
  · rcases hcases with hunram | hcases
    · -- The unramified branch is ruled out once the branch-local residue computation is supplied.
      exfalso
      exact ha <|
        artin_schreier_non_weakly_unramified_residue_cases_force_pth_power
          (A := A) (L := L) (p := p) (ξ := ξ) z hz hgen π hπ hn hdiv a hξ
          (Or.inr <| Or.inl hunram)
    · rcases hcases with htot | hweak
      · -- The totally ramified branch is ruled out by the same residue computation frontier.
        exfalso
        exact ha <|
          artin_schreier_non_weakly_unramified_residue_cases_force_pth_power
            (A := A) (L := L) (p := p) (ξ := ξ) z hz hgen π hπ hn hdiv a hξ
            (Or.inr <| Or.inr htot)
      · -- The weakly unramified purely inseparable residue branch is the desired conclusion.
        exact hweak

end ArtinSchreierGenerator

end
