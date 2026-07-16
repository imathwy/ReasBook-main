import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_60_10
import stacks_proof.stacks_project.Chap10.Definition_10_160_1
import stacks_proof.stacks_project.Chap10.Definition_10_160_5
import stacks_proof.stacks_project.Chap10.Lemma_10_106_3
import stacks_proof.stacks_project.Chap10.Lemma_10_112_8
import stacks_proof.stacks_project.Chap10.Lemma_10_128_2
import stacks_proof.stacks_project.Chap10.Remark_10_160_9

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open RingTheory Sequence
open CategoryTheory CommRingCat

universe u

section

variable {A B : Type u} [CommRing A] [CommRing B]
variable (f : A →+* B) [IsNoetherianRing A] [IsNoetherianRing B]
variable [IsCompleteLocalRing A] [IsCompleteLocalRing B] [IsLocalHom f]

/- Domain-style sampling for Lemma 15.39.3:
- primary domain: local homomorphisms of Noetherian complete local rings presented by finite-index
  formal power series rings;
- sampled owner declarations:
  * `exists_ringEquiv_mvPowerSeries_residueField_of_equalCharacteristic`,
  * `exists_powerSeries_model_of_regular_completeLocalRing`,
  * `IsRegularSystemOfParameters`,
  * `IsPartOfRegularSystemOfParameters`;
- source/core/bridge triage:
  * `source-facing`: the existence of a commutative power-series presentation for a local map
    `A → B` with the parameter clause from the source and the flat/regular-fiber consequences used
    later in the chapter;
  * `core/canonical`: `MvPowerSeries σ R` with `[Finite σ]`, the owner predicates
    `IsRegularSystemOfParameters` and `IsPartOfRegularSystemOfParameters`, together with
    `RingHom.Flat`, `Ideal.Fiber`, and `IsRegularLocalRing`;
  * `bridge/view`: the chosen surjective maps `P → A`, `Q → B`, and `P → Q` forming the
    comparison square.
- best owner abstraction: the canonical owners here are the power-series rings themselves together
  with the regular-parameter predicates. The public theorem surface should therefore expose those
  primitive clauses directly instead of hiding them behind a local packaging predicate, and the
  equal-characteristic field branch should be stated with the canonical equal-characteristic
  condition rather than the narrower `CharZero` special case.
- primitive data: finite source and target variable types, coefficient field or Cohen-ring data,
  the three ring maps in the commutative square, and a chosen regular system of parameters on the
  source, indexed by `(maximalIdeal P).spanFinrank`, whose image is part of one on the target.
- derived API: flatness of the vertical map `rToS.Flat` and regularity of the closed fiber
  `(maximalIdeal P).Fiber Q`. -/

-- Proof sketch: in equal characteristic, use the Chapter 10 residue-field presentation owner
-- `exists_ringEquiv_mvPowerSeries_residueField_of_equalCharacteristic` on the regular complete
-- local source and target presentation rings; in residue characteristic `p > 0`, use the Chapter
-- 10 Cohen-ring owner `exists_powerSeries_model_of_regular_completeLocalRing`. In both cases
-- Lemmas `15.39.1` and `15.37.5` produce the comparison map `P → Q`, and the parameter,
-- flatness, and regular-fiber clauses are then expressed directly by the canonical owners
-- `IsRegularSystemOfParameters`, `IsPartOfRegularSystemOfParameters`, `RingHom.Flat`, and
-- `IsRegularLocalRing`.
/-- Helper for Lemma 15.39.3: mapping a chosen parameter family termwise identifies the
corresponding parameter ideals. -/
lemma parameterIdeal_map_eq_parameterIdeal_of_forall
    {P Q : Type u} [CommRing P] [CommRing Q] [IsLocalRing P] [IsLocalRing Q]
    (φ : P →+* Q) {d : ℕ}
    (x : Fin d → maximalIdeal P) (z : Fin d → maximalIdeal Q)
    (hφx : ∀ i, φ (x i : P) = (z i : Q)) :
    Ideal.map φ (parameterIdeal x) = parameterIdeal z := by
  -- Rewrite both parameter ideals as spans of their chosen generators.
  rw [IsLocalRing.parameterIdeal_eq_span, IsLocalRing.parameterIdeal_eq_span, Ideal.map_span]
  have hrange :
      φ '' Set.range (fun i ↦ ((x i : maximalIdeal P) : P)) =
        Set.range fun i ↦ ((z i : maximalIdeal Q) : Q) := by
    ext q
    constructor
    · rintro ⟨p, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (hφx i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨x i, ⟨i, rfl⟩, hφx i⟩
  rw [hrange]

/-- Helper for Lemma 15.39.3: once a commutative surjective square carries a regular system of
parameters of the source to part of one on the target, flatness and regularity of the closed fiber
follow formally from the Chapter 10 parameter lemmas. -/
theorem flat_and_regularFiber_of_parameter_image
    {P Q : Type u} [CommRing P] [CommRing Q] [IsLocalRing P] [IsLocalRing Q]
    [IsRegularLocalRing P] [IsRegularLocalRing Q] [IsNoetherianRing Q]
    [Algebra P Q] [IsLocalHom (algebraMap P Q)]
    {d : ℕ} (x : Fin d → maximalIdeal P) (z : Fin d → maximalIdeal Q)
    (hx : IsRegularSystemOfParameters x)
    (hmap : ∀ i, algebraMap P Q (x i : P) = (z i : Q))
    (hz : IsPartOfRegularSystemOfParameters (maximalIdeal Q).spanFinrank z) :
    (algebraMap P Q).Flat ∧ IsRegularLocalRing ((maximalIdeal P).Fiber Q) := by
  -- The image family is regular because it is part of a regular system of parameters on `Q`.
  have himage_regular :
      Sequence.IsRegular Q (List.ofFn fun i ↦ algebraMap P Q (x i : P)) := by
    simpa [hmap] using
      (IsPartOfRegularSystemOfParameters.isRegular hz :
        Sequence.IsRegular Q (List.ofFn fun i ↦ (z i : Q)))
  have hflatAlg : Module.Flat P Q :=
    flat_of_regularSystemOfParameters_image_isRegular x hx himage_regular
  have hmapIdeal :
      Ideal.map (algebraMap P Q) (parameterIdeal x) = parameterIdeal z :=
    parameterIdeal_map_eq_parameterIdeal_of_forall (algebraMap P Q) x z hmap
  have hclosedQuot :
      IsRegularLocalRing (Q ⧸ Ideal.map (algebraMap P Q) (maximalIdeal P)) := by
    -- The closed-fiber quotient is exactly the quotient by the target parameter ideal.
    have hmapMax :
        Ideal.map (algebraMap P Q) (maximalIdeal P) = parameterIdeal z := by
      rw [← hx.2]
      exact hmapIdeal
    exact
      hmapMax.symm ▸
        (IsPartOfRegularSystemOfParameters.isRegularLocalRing_quotient_parameterIdeal hz :
          IsRegularLocalRing (Q ⧸ parameterIdeal z))
  let _ : IsRegularLocalRing (Q ⧸ Ideal.map (algebraMap P Q) (maximalIdeal P)) := hclosedQuot
  have hclosedFiber : IsRegularLocalRing ((maximalIdeal P).Fiber Q) := by
    -- Chapter 10 identifies the closed fiber with that regular quotient.
    simpa using (isRegularLocalRing_closedFiber_of_quotient (R := P) (S := Q))
  refine ⟨?_, hclosedFiber⟩
  exact RingHom.flat_algebraMap_iff.mpr hflatAlg

/-- Helper for Lemma 15.39.3: a quotient presentation immediately yields the corresponding
surjective map from the source ring. -/
lemma surjective_of_quotient_presentation
    {P R : Type u} [CommRing P] [CommRing R]
    (I : Ideal P) (e : P ⧸ I ≃+* R) :
    Function.Surjective ((e : P ⧸ I →+* R).comp (Ideal.Quotient.mk I)) := by
  -- First hit the target through the quotient presentation equivalence.
  intro r
  rcases e.surjective r with ⟨q, rfl⟩
  -- Then lift the quotient class back to an element of the source ring.
  rcases Ideal.Quotient.mk_surjective q with ⟨p, rfl⟩
  exact ⟨p, rfl⟩

/-- Helper for Lemma 15.39.3: the residue-characteristic element of a Cohen coefficient ring
remains in the maximal ideal after passing to a finite-variable formal power series ring. -/
lemma residueChar_coeff_mem_maximalIdeal_mvPowerSeries_fin
    {Λ : Type u} [CommRing Λ] [IsCohenRing Λ] {n : ℕ} :
    algebraMap Λ (MvPowerSeries (Fin n) Λ) (ringChar (ResidueField Λ)) ∈
      maximalIdeal (MvPowerSeries (Fin n) Λ) := by
  -- If the coefficient became a unit upstairs, its constant coefficient would already be a unit.
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ⊢
  intro hunit
  exact IsCohenRing.residueChar_not_isUnit <| by
    simpa [MvPowerSeries.c_eq_algebraMap] using MvPowerSeries.isUnit_constantCoeff _ hunit

/-- Helper for Lemma 15.39.3: the mixed-characteristic distinguished parameter in
`Λ[[X_0, …, X_{n-1}]]` is the coefficient image of the residue characteristic. -/
noncomputable def mixed_residueChar_parameter
    (Λ : Type u) [CommRing Λ] [IsCohenRing Λ] (n : ℕ) :
    maximalIdeal (MvPowerSeries (Fin n) Λ) :=
  ⟨algebraMap Λ (MvPowerSeries (Fin n) Λ) (ringChar (ResidueField Λ)),
    residueChar_coeff_mem_maximalIdeal_mvPowerSeries_fin (Λ := Λ) (n := n)⟩

/-- Helper for Lemma 15.39.3: in the maximal-ideal-adic topology, any finite family of elements
of the maximal ideal admits formal power-series evaluation. -/
lemma hasEval_of_finite_mem_maximalIdeal_madic
    {σ : Type*} [Finite σ] {R : Type u} [CommRing R] [IsLocalRing R]
    (a : σ → maximalIdeal R) :
    letI : TopologicalSpace R := Ideal.adicTopology (maximalIdeal R)
    MvPowerSeries.HasEval (fun s ↦ (a s : R)) := by
  letI : TopologicalSpace R := Ideal.adicTopology (maximalIdeal R)
  letI : WithIdeal R := ⟨maximalIdeal R⟩
  refine ⟨?_, ?_⟩
  · -- In the defining adic topology, every element of the maximal ideal is topologically
    -- nilpotent.
    intro s
    simpa using (WithIdeal.isTopologicallyNilpotent_of_mem (R := R) (a s).2)
  · -- For a finite index type, the cofinite filter contains every subset, so convergence to zero
    -- is automatic.
    rw [Filter.tendsto_def]
    intro U hU
    rw [Filter.mem_cofinite]
    exact Set.toFinite _

/-- Helper for Lemma 15.39.3: surjectivity can be recovered from the induced surjective quotient
map once the chosen target parameter ideal is already known to lie in the image. -/
lemma surjective_of_surjective_quotient_by_parameterIdeal_of_parameterIdeal_subset_range
    {Q R : Type u} [CommRing Q] [CommRing R] [IsLocalRing Q] [IsLocalRing R]
    (φ : Q →+* R) {d : ℕ}
    (J : Ideal Q) (z : Fin d → maximalIdeal R)
    (hJ : J ≤ Ideal.comap φ (parameterIdeal z))
    (hquot :
      Function.Surjective
        (Ideal.quotientMap (parameterIdeal z) φ hJ))
    (hparam :
      ∀ r ∈ parameterIdeal z, ∃ q : Q, φ q = r) :
    Function.Surjective φ := by
  let I : Ideal R := parameterIdeal z
  let φbar : Q ⧸ J →+* R ⧸ I :=
    Ideal.quotientMap I φ hJ
  -- Lift a target element through the surjective quotient map.
  intro r
  obtain ⟨qbar, hqbar⟩ := hquot (Ideal.Quotient.mk I r)
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective qbar
  -- The quotient equality shows that the discrepancy lies in the target parameter ideal.
  have hmemI : r - φ q ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    calc
      Ideal.Quotient.mk I (r - φ q)
          = Ideal.Quotient.mk I r - Ideal.Quotient.mk I (φ q) := by
              rw [map_sub]
      _ = φbar (Ideal.Quotient.mk J q) - Ideal.Quotient.mk I (φ q) := by
              rw [hqbar]
      _ = φbar (Ideal.Quotient.mk J q) - φbar (Ideal.Quotient.mk J q) := by
              rw [Ideal.quotientMap_mk]
      _ = 0 := sub_self _
  -- Pull the discrepancy back through the explicit range hypothesis and absorb it into the lift.
  obtain ⟨q', hq'eq⟩ := hparam (r - φ q) hmemI
  refine ⟨q + q', ?_⟩
  calc
    φ (q + q') = φ q + φ q' := by rw [map_add]
    _ = φ q + (r - φ q) := by rw [hq'eq]
    _ = r := by abel

-- Proof sketch: the unresolved input is the explicit equal-characteristic presentation package
-- before adding the formal flatness and regular-fiber consequences handled above.
/-- Helper for Lemma 15.39.3: the remaining equal-characteristic blocker is to construct a
commutative surjective field-valued power-series presentation together with the parameter-image
clause. -/
theorem exists_field_powerSeries_comparison_data_of_localHom_completeLocal
    (hAeqchar : ringChar A = ringChar (ResidueField A)) :
    ∃ (σ τ : Type u) (_ : Finite σ) (_ : Finite τ)
      (K L : Type u) (_ : Field K) (_ : Field L)
      (_ : IsRegularLocalRing (MvPowerSeries σ K))
      (_ : IsRegularLocalRing (MvPowerSeries τ L))
      (_ : IsNoetherianRing (MvPowerSeries τ L))
      (rToA : MvPowerSeries σ K →+* A)
      (sToB : MvPowerSeries τ L →+* B)
      (rToS : MvPowerSeries σ K →+* MvPowerSeries τ L),
      Function.Surjective rToA ∧
        Function.Surjective sToB ∧
        CommSq (ofHom rToS) (ofHom rToA) (ofHom sToB) (ofHom f) ∧
        (∃ (x : Fin (maximalIdeal (MvPowerSeries σ K)).spanFinrank →
              maximalIdeal (MvPowerSeries σ K))
          (z : Fin (maximalIdeal (MvPowerSeries σ K)).spanFinrank →
              maximalIdeal (MvPowerSeries τ L)),
            IsRegularSystemOfParameters x ∧
              (∀ i, rToS (x i : MvPowerSeries σ K) = (z i : MvPowerSeries τ L)) ∧
              IsPartOfRegularSystemOfParameters
                (maximalIdeal (MvPowerSeries τ L)).spanFinrank z) := by
  -- Route correction: the unresolved step is precisely the controlled presentation package, not
  -- the Chapter 10 flatness/regular-fiber consequences that now follow from it formally.
  -- TODO: first obtain field-valued surjective covers of `A` and `B` in the equal-characteristic
  -- branch, then use `surjective_of_quotient_presentation` to recover the actual quotient maps.
  -- The previous abstract quotient-surjectivity lemma was too weak, because ideal-map membership
  -- does not supply a single-image witness. The remaining blocker is the missing dependency-closed
  -- API that gives those initial field-valued covers for arbitrary complete local rings without
  -- reintroducing the timed-out `Lemma_15_39_2` quotient-tail route. Once those covers are
  -- available, Lemma `15.37.5` and the source-faithful translation step should build `rToS`.
  sorry

-- Proof sketch: this is the equal-characteristic branch of Lemma `15.39.3`, matching the Chapter
-- 10 field-presentation owner in arbitrary equal characteristic.
/-- Helper for Lemma 15.39.3: if `A` has the same characteristic as its
residue field, then the coefficient rings in the presentation can be taken to be fields. -/
theorem exists_field_powerSeries_presentation_of_localHom_completeLocal
    (hAeqchar : ringChar A = ringChar (ResidueField A)) :
    ∃ (σ τ : Type u) (_ : Finite σ) (_ : Finite τ)
      (K L : Type u) (_ : Field K) (_ : Field L),
      let P := MvPowerSeries σ K
      let Q := MvPowerSeries τ L
      ∃ (rToA : P →+* A) (sToB : Q →+* B) (rToS : P →+* Q),
        let _ : Algebra P Q := rToS.toAlgebra
        Function.Surjective rToA ∧
          Function.Surjective sToB ∧
          CommSq (ofHom rToS) (ofHom rToA) (ofHom sToB) (ofHom f) ∧
          (∃ (x : Fin (maximalIdeal P).spanFinrank → maximalIdeal P)
            (z : Fin (maximalIdeal P).spanFinrank → maximalIdeal Q),
                IsRegularSystemOfParameters x ∧
                (∀ i, rToS (x i : P) = (z i : Q)) ∧
                IsPartOfRegularSystemOfParameters (maximalIdeal Q).spanFinrank z) ∧
          rToS.Flat ∧ IsRegularLocalRing ((maximalIdeal P).Fiber Q) := by
  -- First obtain the controlled field-valued presentation data.
  obtain ⟨σ, τ, hσ, hτ, K, L, hK, hL, hPreg, hQreg, hQnoeth,
      rToA, sToB, rToS, hrToA, hsToB, hsq, x, z, hx, hmap, hz⟩ :=
    exists_field_powerSeries_comparison_data_of_localHom_completeLocal (f := f) hAeqchar
  let _ : Finite σ := hσ
  let _ : Finite τ := hτ
  let _ : Field K := hK
  let _ : Field L := hL
  let _ : IsRegularLocalRing (MvPowerSeries σ K) := hPreg
  let _ : IsRegularLocalRing (MvPowerSeries τ L) := hQreg
  let _ : IsNoetherianRing (MvPowerSeries τ L) := hQnoeth
  let _ : Algebra (MvPowerSeries σ K) (MvPowerSeries τ L) := rToS.toAlgebra
  let _ : IsLocalHom rToA := Function.Surjective.isLocalHom _ hrToA
  let _ : IsLocalHom sToB := Function.Surjective.isLocalHom _ hsToB
  have hcomp : sToB.comp rToS = f.comp rToA := by
    ext p
    simpa [CommRingCat.hom_comp, RingHom.comp_apply] using congr(($hsq.w) p)
  let _ : IsLocalHom (sToB.comp rToS) := hcomp ▸ inferInstance
  let _ : IsLocalHom rToS := isLocalHom_of_comp rToS sToB
  let _ : IsLocalHom (algebraMap (MvPowerSeries σ K) (MvPowerSeries τ L)) := by
    simpa [RingHom.algebraMap_toAlgebra] using (inferInstance : IsLocalHom rToS)
  -- The remaining flatness and regular-fiber clauses are formal consequences of the parameter
  -- image package.
  have hflatFiber :
      (algebraMap (MvPowerSeries σ K) (MvPowerSeries τ L)).Flat ∧
        IsRegularLocalRing
          ((maximalIdeal (MvPowerSeries σ K)).Fiber
            (MvPowerSeries τ L)) := by
    exact flat_and_regularFiber_of_parameter_image
      (x := x) (z := z) hx
      (by
        intro i
        simpa [RingHom.algebraMap_toAlgebra] using hmap i)
      hz
  have hflat : rToS.Flat := by
    simpa [RingHom.algebraMap_toAlgebra] using hflatFiber.1
  refine ⟨σ, τ, hσ, hτ, K, L, hK, hL, ?_⟩
  exact ⟨rToA, sToB, rToS, hrToA, hsToB, hsq, ⟨x, z, hx, hmap, hz⟩, hflat, hflatFiber.2⟩

-- Proof sketch: the unresolved input is the explicit mixed-characteristic presentation package
-- before adding the formal flatness and regular-fiber consequences handled above.
/-- Helper for Lemma 15.39.3: the remaining mixed-characteristic blocker is to construct a
commutative surjective Cohen-ring power-series presentation together with the parameter-image
clause. -/
theorem exists_cohen_powerSeries_comparison_data_of_localHom_completeLocal
    (p : ℕ) (hp : Nat.Prime p) (hAp : CharP (ResidueField A) p) :
    ∃ (σ τ : Type u) (_ : Finite σ) (_ : Finite τ)
      (R₀ S₀ : Type u) (_ : CommRing R₀) (_ : CommRing S₀)
      (_ : IsCohenRing R₀) (_ : IsCohenRing S₀)
      (_ : IsRegularLocalRing (MvPowerSeries σ R₀))
      (_ : IsRegularLocalRing (MvPowerSeries τ S₀))
      (_ : IsNoetherianRing (MvPowerSeries τ S₀))
      (rToA : MvPowerSeries σ R₀ →+* A)
      (sToB : MvPowerSeries τ S₀ →+* B)
      (rToS : MvPowerSeries σ R₀ →+* MvPowerSeries τ S₀),
      Function.Surjective rToA ∧
        Function.Surjective sToB ∧
        CommSq (ofHom rToS) (ofHom rToA) (ofHom sToB) (ofHom f) ∧
        (∃ (x : Fin (maximalIdeal (MvPowerSeries σ R₀)).spanFinrank →
              maximalIdeal (MvPowerSeries σ R₀))
          (z : Fin (maximalIdeal (MvPowerSeries σ R₀)).spanFinrank →
              maximalIdeal (MvPowerSeries τ S₀)),
            IsRegularSystemOfParameters x ∧
              (∀ i, rToS (x i : MvPowerSeries σ R₀) = (z i : MvPowerSeries τ S₀)) ∧
              IsPartOfRegularSystemOfParameters
                (maximalIdeal (MvPowerSeries τ S₀)).spanFinrank z) := by
  -- Route correction: the unresolved step is again the controlled presentation package, now over
  -- Cohen rings, while the downstream flatness and closed-fiber regularity are already formal.
  -- TODO: first obtain Cohen-ring surjective covers of `A` and `B` in the mixed-characteristic
  -- branch, then use `surjective_of_quotient_presentation` to recover the actual quotient maps.
  -- The previous abstract quotient-surjectivity lemma was too weak, because ideal-map membership
  -- does not supply a single-image witness. The remaining blocker is the missing dependency-closed
  -- API that gives those initial Cohen-ring covers for arbitrary complete local rings while
  -- keeping the distinguished residue-characteristic parameter explicit. Once those covers are
  -- available, Lemma `15.37.5` and the source-faithful translation step should build `rToS`.
  sorry

-- Proof sketch: in positive residue characteristic, use the Cohen structure theorem to present
-- both `A` and `B` as quotients of finite-index power series rings over Cohen rings. As above,
-- Lemmas `15.39.1` and `15.37.5` lift the composite source presentation to the target power
-- series ring, and the parameter clause is expressed through the canonical owner
-- `IsPartOfRegularSystemOfParameters (maximalIdeal Q).spanFinrank` after reordering the chosen
-- target regular system. Flatness and regularity of the closed fiber are then the same canonical
-- consequences as in the equal-characteristic case.
/-- Helper for Lemma 15.39.3: if the residue field of `A` has
characteristic `p > 0`, then the coefficient rings in the presentation can be taken to be Cohen
rings. -/
theorem exists_cohen_powerSeries_presentation_of_localHom_completeLocal
    (p : ℕ) (hp : Nat.Prime p) (hAp : CharP (ResidueField A) p) :
    ∃ (σ τ : Type u) (_ : Finite σ) (_ : Finite τ)
      (R₀ S₀ : Type u) (_ : CommRing R₀) (_ : CommRing S₀)
      (_ : IsCohenRing R₀) (_ : IsCohenRing S₀),
      let P := MvPowerSeries σ R₀
      let Q := MvPowerSeries τ S₀
      ∃ (rToA : P →+* A) (sToB : Q →+* B) (rToS : P →+* Q),
        let _ : Algebra P Q := rToS.toAlgebra
        Function.Surjective rToA ∧
          Function.Surjective sToB ∧
          CommSq (ofHom rToS) (ofHom rToA) (ofHom sToB) (ofHom f) ∧
          (∃ (x : Fin (maximalIdeal P).spanFinrank → maximalIdeal P)
            (z : Fin (maximalIdeal P).spanFinrank → maximalIdeal Q),
                IsRegularSystemOfParameters x ∧
                (∀ i, rToS (x i : P) = (z i : Q)) ∧
                IsPartOfRegularSystemOfParameters (maximalIdeal Q).spanFinrank z) ∧
          rToS.Flat ∧ IsRegularLocalRing ((maximalIdeal P).Fiber Q) := by
  -- First obtain the controlled Cohen-ring presentation data.
  obtain ⟨σ, τ, hσ, hτ, R₀, S₀, hR₀, hS₀, hcohenR₀, hcohenS₀,
      hPreg, hQreg, hQnoeth, rToA, sToB, rToS, hrToA, hsToB, hsq, x, z, hx, hmap, hz⟩ :=
    exists_cohen_powerSeries_comparison_data_of_localHom_completeLocal (f := f) p hp hAp
  let _ : Finite σ := hσ
  let _ : Finite τ := hτ
  let _ : CommRing R₀ := hR₀
  let _ : CommRing S₀ := hS₀
  let _ : IsCohenRing R₀ := hcohenR₀
  let _ : IsCohenRing S₀ := hcohenS₀
  let _ : IsRegularLocalRing (MvPowerSeries σ R₀) := hPreg
  let _ : IsRegularLocalRing (MvPowerSeries τ S₀) := hQreg
  let _ : IsNoetherianRing (MvPowerSeries τ S₀) := hQnoeth
  let _ : Algebra (MvPowerSeries σ R₀) (MvPowerSeries τ S₀) := rToS.toAlgebra
  let _ : IsLocalHom rToA := Function.Surjective.isLocalHom _ hrToA
  let _ : IsLocalHom sToB := Function.Surjective.isLocalHom _ hsToB
  have hcomp : sToB.comp rToS = f.comp rToA := by
    ext p'
    simpa [CommRingCat.hom_comp, RingHom.comp_apply] using congr(($hsq.w) p')
  let _ : IsLocalHom (sToB.comp rToS) := hcomp ▸ inferInstance
  let _ : IsLocalHom rToS := isLocalHom_of_comp rToS sToB
  let _ : IsLocalHom (algebraMap (MvPowerSeries σ R₀) (MvPowerSeries τ S₀)) := by
    simpa [RingHom.algebraMap_toAlgebra] using (inferInstance : IsLocalHom rToS)
  -- The remaining flatness and regular-fiber clauses are formal consequences of the parameter
  -- image package.
  have hflatFiber :
      (algebraMap (MvPowerSeries σ R₀) (MvPowerSeries τ S₀)).Flat ∧
        IsRegularLocalRing
          ((maximalIdeal (MvPowerSeries σ R₀)).Fiber
            (MvPowerSeries τ S₀)) := by
    exact flat_and_regularFiber_of_parameter_image
      (x := x) (z := z) hx
      (by
        intro i
        simpa [RingHom.algebraMap_toAlgebra] using hmap i)
      hz
  have hflat : rToS.Flat := by
    simpa [RingHom.algebraMap_toAlgebra] using hflatFiber.1
  refine
    ⟨σ, τ, hσ, hτ, R₀, S₀,
      hR₀, hS₀, hcohenR₀, hcohenS₀, ?_⟩
  exact ⟨rToA, sToB, rToS, hrToA, hsToB, hsq, ⟨x, z, hx, hmap, hz⟩, hflat, hflatFiber.2⟩

/-- Lemma 15.39.3: a local homomorphism `A → B` of Noetherian complete local rings admits a
commutative surjective presentation by finite-index formal power series rings in which a regular
system of parameters of the source maps to part of one on the target, the vertical map is flat,
and its closed fiber is regular local. In equal characteristic the coefficient rings can be taken
to be fields; in residue characteristic `p > 0` they can be taken to be Cohen rings. -/
@[stacks 07NN]
theorem exists_powerSeries_presentation_of_localHom_completeLocal :
    (∃ _ : ringChar A = ringChar (ResidueField A),
      ∃ (σ τ : Type u) (_ : Finite σ) (_ : Finite τ)
        (K L : Type u) (_ : Field K) (_ : Field L),
        let P := MvPowerSeries σ K
        let Q := MvPowerSeries τ L
        ∃ (rToA : P →+* A) (sToB : Q →+* B) (rToS : P →+* Q),
          let _ : Algebra P Q := rToS.toAlgebra
          Function.Surjective rToA ∧
            Function.Surjective sToB ∧
            CommSq (ofHom rToS) (ofHom rToA) (ofHom sToB) (ofHom f) ∧
            (∃ (x : Fin (maximalIdeal P).spanFinrank → maximalIdeal P)
              (z : Fin (maximalIdeal P).spanFinrank → maximalIdeal Q),
                IsRegularSystemOfParameters x ∧
                  (∀ i, rToS (x i : P) = (z i : Q)) ∧
                  IsPartOfRegularSystemOfParameters (maximalIdeal Q).spanFinrank z) ∧
            rToS.Flat ∧ IsRegularLocalRing ((maximalIdeal P).Fiber Q))
      ∨
      ∃ (p : ℕ) (_ : Nat.Prime p), CharP (ResidueField A) p ∧
        ∃ (σ τ : Type u) (_ : Finite σ) (_ : Finite τ)
          (R₀ S₀ : Type u) (_ : CommRing R₀) (_ : CommRing S₀)
          (_ : IsCohenRing R₀) (_ : IsCohenRing S₀),
          let P := MvPowerSeries σ R₀
          let Q := MvPowerSeries τ S₀
          ∃ (rToA : P →+* A) (sToB : Q →+* B) (rToS : P →+* Q),
            let _ : Algebra P Q := rToS.toAlgebra
            Function.Surjective rToA ∧
              Function.Surjective sToB ∧
              CommSq (ofHom rToS) (ofHom rToA) (ofHom sToB) (ofHom f) ∧
              (∃ (x : Fin (maximalIdeal P).spanFinrank → maximalIdeal P)
                (z : Fin (maximalIdeal P).spanFinrank → maximalIdeal Q),
                  IsRegularSystemOfParameters x ∧
                    (∀ i, rToS (x i : P) = (z i : Q)) ∧
                    IsPartOfRegularSystemOfParameters (maximalIdeal Q).spanFinrank z) ∧
              rToS.Flat ∧ IsRegularLocalRing ((maximalIdeal P).Fiber Q) := by
  by_cases hAeqchar : ringChar A = ringChar (ResidueField A)
  · -- In equal characteristic, the field-valued branch theorem already provides the whole
    -- presentation package.
    left
    refine ⟨hAeqchar, ?_⟩
    exact exists_field_powerSeries_presentation_of_localHom_completeLocal
      (f := f) hAeqchar
  · let p : ℕ := ringChar (ResidueField A)
    have hAp : CharP (ResidueField A) p := by
      simpa [p] using (ringChar.charP (ResidueField A))
    have hp_ne_zero : p ≠ 0 := by
      intro hp0
      have hAcast_zero : ((ringChar A : ℕ) : A) = 0 :=
        (ringChar.spec A (ringChar A)).2 dvd_rfl
      have hκmap_zero : residue A (((ringChar A : ℕ) : A)) = 0 := by
        rw [hAcast_zero]
        simp
      have hκcast_zero : ((ringChar A : ℕ) : ResidueField A) = 0 := by
        change residue A (((ringChar A : ℕ) : A)) = 0
        exact hκmap_zero
      have hκdvd : p ∣ ringChar A := by
        simpa [p] using (ringChar.spec (ResidueField A) (ringChar A)).mp hκcast_zero
      have hAchar_zero : ringChar A = 0 := by
        rw [hp0] at hκdvd
        simpa using hκdvd
      apply hAeqchar
      simpa [p, hp0] using hAchar_zero
    have hp : Nat.Prime p := by
      rcases CharP.char_is_prime_or_zero (ResidueField A) p with hp | hp0
      · exact hp
      · exact False.elim (hp_ne_zero hp0)
    -- In mixed characteristic, the Cohen-ring branch theorem supplies the corresponding package.
    right
    refine ⟨p, hp, hAp, ?_⟩
    exact exists_cohen_powerSeries_presentation_of_localHom_completeLocal
      (f := f) p hp hAp

end
