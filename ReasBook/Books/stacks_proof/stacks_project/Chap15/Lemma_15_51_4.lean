import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_97_3
import stacks_proof.stacks_project.Chap10.Definition_10_37_11
import stacks_proof.stacks_project.Chap15.Definition_15_41_1
import stacks_proof.stacks_project.Chap15.Definition_15_50_1
import stacks_proof.stacks_project.Chap15.Lemma_15_41_2_Regular_is_a_local_property
import stacks_proof.stacks_project.Chap15.Lemma_15_41_4_Composition_of_regular_maps
import stacks_proof.stacks_project.Chap15.Lemma_15_45_3
import stacks_proof.stacks_project.Chap15.Proposition_15_50_6
import stacks_proof.stacks_project.Chap15.Lemma_15_50_7
import stacks_proof.stacks_project.Chap15.Lemma_15_51_1

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

universe u

namespace FieldAlgebraProperty

/- Domain sampling pass:
- primary domain: Chapter 15 formal-fiber permanence axioms for `FieldAlgebraProperty`;
- sampled owner declarations:
  `FieldAlgebraProperty.HasPropertyA`,
  `FieldAlgebraProperty.HasPropertyB`,
  `IsPRing`,
  `LocalFormalFibersHaveProperty`;
- best owner abstraction: `FieldAlgebraProperty`, with the reusable axioms `(C)` and `(D)` owned
  as inferable classes, matching the existing owner form for `(A)` and `(B)`;
- primitive data: the field-algebra predicate `P` together with the regular-ascent and faithfully
  flat local-descent laws on fibers, plus the local formal-fiber predicate itself;
- derived API: the maximal-ideal criterion for `IsPRing`.

Source/core/bridge triage:
- `source-facing`: `LocalFormalFibersHaveProperty` and
  `isPRing_iff_localFormalFibersHaveProperty_atMaximal`;
- `core/canonical`: `P.HasPropertyC` and `P.HasPropertyD`;
- `bridge/view`: none needed.
-/

section

/-- A field-algebra property has property `(C)` if it ascends along regular morphisms on fibers of
flat maps of Noetherian rings. -/
class HasPropertyC (P : FieldAlgebraProperty) : Prop where
  /-- Property `(C)` ascends from the fibers of `A → B` to the fibers of `A → C` when `A → B` is
  flat and `B → C` is regular. -/
  regularAscent (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
      [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
      [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
      [Module.Flat A B] [(algebraMap B C).IsRegularRingMap]
      (hB : ∀ q : PrimeSpectrum A, P q.asIdeal.ResidueField (q.asIdeal.Fiber B))
      (q : PrimeSpectrum A) :
      P q.asIdeal.ResidueField (q.asIdeal.Fiber C)

/-- A field-algebra property has property `(D)` if it descends along faithfully flat local
extensions on closed fibers of Noetherian local rings. -/
class HasPropertyD (P : FieldAlgebraProperty) : Prop where
  /-- Property `(D)` descends from the closed fiber over `A → C` to the closed fiber over `A → B`
  along a faithfully flat local extension `B → C`. -/
  closedFiberDescent (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
      [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
      [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
      [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]
      [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap B C)]
      (hBC : RingHom.FaithfullyFlat (algebraMap B C))
      (hC : P (ResidueField A) ((maximalIdeal A).Fiber C)) :
      P (ResidueField A) ((maximalIdeal A).Fiber B)

end

end FieldAlgebraProperty

section

/-- A local ring has formal fibers with property `P` if every fiber of its completion map to the
maximal-ideal adic completion has property `P`. -/
abbrev LocalFormalFibersHaveProperty
    (P : FieldAlgebraProperty) (A : Type u) [CommRing A] [IsLocalRing A] :
    Prop :=
  ∀ q : PrimeSpectrum A,
    P q.asIdeal.ResidueField (q.asIdeal.Fiber (AdicCompletion (maximalIdeal A) A))

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- Helper for Lemma 15.51.4: the formal fibers of the maximal localization `R_m` may be indexed
by the primes of `R` contained in `m`. -/
lemma localFormalFibersHaveProperty_localizationAtMaximal_iff_primePair
    (P : FieldAlgebraProperty) (m : MaximalSpectrum R) :
    LocalFormalFibersHaveProperty P (Localization.AtPrime m.asIdeal) ↔
      ∀ q : PrimeSpectrum R, q.asIdeal ≤ m.asIdeal →
        P q.asIdeal.ResidueField (q.asIdeal.Fiber (R̂_[m.toPrimeSpectrum])) := by
  constructor
  · intro h q hqm
    let q' : PrimeSpectrum (Localization.AtPrime m.asIdeal) :=
      (IsLocalization.AtPrime.primeSpectrumOrderIso
        (Localization.AtPrime m.asIdeal) m.asIdeal).symm ⟨q, hqm⟩
    -- Proof comment: reindex the fiber of `R_m` by the corresponding prime of the localization.
    simpa [LocalFormalFibersHaveProperty, q'] using h q'
  · intro h q
    let q0 : PrimeSpectrum R :=
      PrimeSpectrum.comap (algebraMap R (Localization.AtPrime m.asIdeal)) q
    have hq0m : q0.asIdeal ≤ m.asIdeal := by
      -- Proof comment: every prime of `R_m` contracts to a prime of `R` lying under `m`.
      change Ideal.comap (algebraMap R (Localization.AtPrime m.asIdeal)) q.asIdeal ≤ m.asIdeal
      intro x hx
      exact
        ((IsLocalization.AtPrime.primeSpectrumOrderIso
          (Localization.AtPrime m.asIdeal) m.asIdeal) q).2 hx
    -- Proof comment: apply the prime-pair formulation to the contracted prime.
    simpa [LocalFormalFibersHaveProperty, q0] using h q0 hq0m

/-- Helper for Lemma 15.51.4: at a maximal ideal, the `P`-ring condition on the localization is
equivalent to asking that its formal fibers have property `P`. -/
lemma isPRing_localizationAtMaximal_iff_localFormalFibersHaveProperty
    (P : FieldAlgebraProperty) (m : MaximalSpectrum R) :
    IsPRing P (Localization.AtPrime m.asIdeal) ↔
      LocalFormalFibersHaveProperty P (Localization.AtPrime m.asIdeal) := by
  -- Proof comment: both sides rewrite to the same prime-pair statement indexed by `q ≤ m`.
  rw [isPRing_localizationAtPrime_iff (P := P) m.toPrimeSpectrum]
  exact
    localFormalFibersHaveProperty_localizationAtMaximal_iff_primePair
      (P := P) (m := m)

/-- Helper for Lemma 15.51.4: localizing a Noetherian ring at a prime is a regular map because it
is the localization of the identity map. -/
lemma algebraMap_localizationAtPrime_isRegularRingMap
    {S : Type u} [CommRing S] [IsNoetherianRing S] (q : PrimeSpectrum S) :
    (algebraMap S (Localization.AtPrime q.asIdeal)).IsRegularRingMap := by
  have hid : (RingHom.id S).IsRegularRingMap := inferInstance
  have hloc :
      (Localization.localRingHom q.asIdeal q.asIdeal (RingHom.id S) rfl).IsRegularRingMap :=
    RingHom.IsRegularRingMap.localized_isRegularRingMap (f := RingHom.id S) hid q
  have halg :
      Localization.localRingHom q.asIdeal q.asIdeal (RingHom.id S) rfl =
        algebraMap S (Localization.AtPrime q.asIdeal) := by
    -- Proof comment: both maps are the canonical localization morphism from `S` to `S_q`.
    refine Localization.localRingHom_unique q.asIdeal q.asIdeal (RingHom.id S) rfl ?_
    intro x
    simp [Localization.localRingHom_to_map]
  -- Proof comment: rewrite the localized identity map into the standard localization algebra map.
  simpa [halg] using hloc

/-- Helper for Lemma 15.51.4: after choosing a branch `r` of the completion `A^∧`, the source
proof's upstairs composite `A^∧ → (A^∧)_r → ((A^∧)_r)^∧` is regular. -/
lemma lifted_branch_completion_regular
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (r : PrimeSpectrum (AdicCompletion (maximalIdeal A) A)) :
    (algebraMap (AdicCompletion (maximalIdeal A) A)
      (AdicCompletion (maximalIdeal (Localization.AtPrime r.asIdeal))
        (Localization.AtPrime r.asIdeal))).IsRegularRingMap := by
  let Ahat := AdicCompletion (maximalIdeal A) A
  let Ar := Localization.AtPrime r.asIdeal
  let C := AdicCompletion (maximalIdeal Ar) Ar
  let _ : IsNoetherianRing Ahat :=
    adicCompletion_isNoetherianRing (R := A) (I := maximalIdeal A)
  let _ : IsCompleteLocalRing Ahat :=
    completion_isCompleteLocalRing_of_maximalIdeal_fg (S := A)
      (Ideal.fg_of_isNoetherianRing (maximalIdeal A))
  let _ : IsGRing Ahat := inferInstance
  have hloc :
      (algebraMap Ahat Ar).IsRegularRingMap :=
    algebraMap_localizationAtPrime_isRegularRingMap (S := Ahat) r
  have hcompletion :
      (algebraMap Ar C).IsRegularRingMap :=
    IsGRing.regular_localization_completion (R := Ahat) r
  -- Proof comment: compose regularity of the localization step with regularity of the local
  -- completion step supplied by the `G`-ring structure on the complete local ring `A^∧`.
  simpa [Ahat, Ar, C] using
    (RingHom.IsRegularRingMap.comp_of_noetherianFibers hloc hcompletion)

/-- Helper for Lemma 15.51.4: the branch source `((R_m)_{p_A})^∧` is canonically the completed
localization `R̂_[p]`. -/
noncomputable lemma branch_source_completion_algEquiv
    (p : PrimeSpectrum R) (m : MaximalSpectrum R)
    (pA : PrimeSpectrum (Localization.AtPrime m.asIdeal))
    (hpA : PrimeSpectrum.comap (algebraMap R (Localization.AtPrime m.asIdeal)) pA = p) :
    AdicCompletion (maximalIdeal (Localization.AtPrime pA.asIdeal))
      (Localization.AtPrime pA.asIdeal) ≃+* R̂_[p] := by
  let eLoc : Localization.AtPrime p.asIdeal ≃ₐ[R] Localization.AtPrime pA.asIdeal :=
    localizationAtPrime_algEquiv_of_maximalLocalization_comap
      (R := R) p m pA hpA
  let f : Localization.AtPrime p.asIdeal →+* Localization.AtPrime pA.asIdeal := eLoc.toRingHom
  letI : Algebra (Localization.AtPrime p.asIdeal) (Localization.AtPrime pA.asIdeal) := f.toAlgebra
  letI : IsLocalHom f := Function.Surjective.isLocalHom _ eLoc.surjective
  letI : Module.Flat (Localization.AtPrime p.asIdeal) (Localization.AtPrime pA.asIdeal) :=
    RingHom.flat_algebraMap_iff.mp <| by
      -- Proof comment: the branch-local identification is a ring equivalence, hence flat.
      simpa [f, RingHom.algebraMap_toAlgebra] using
        (RingHom.Flat.of_bijective eLoc.bijective : f.Flat)
  have hmax :
      Ideal.map (algebraMap (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime pA.asIdeal)) (maximalIdeal (Localization.AtPrime p.asIdeal)) =
          maximalIdeal (Localization.AtPrime pA.asIdeal) := by
    -- Proof comment: a surjective local map sends the maximal ideal onto the maximal ideal.
    simpa [f, RingHom.algebraMap_toAlgebra] using
      (IsLocalRing.map_maximalIdeal_of_surjective f eLoc.surjective)
  have hres :
      Function.Bijective
        (ResidueField.map (algebraMap (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime pA.asIdeal))) := by
    -- Proof comment: the same surjective local map induces an isomorphism on residue fields.
    simpa [f, RingHom.algebraMap_toAlgebra] using
      (residueField_bijective_of_surjective_localHom (f := f) eLoc.surjective)
  -- Proof comment: transport the local-ring equivalence to maximal-ideal completions.
  simpa using
    (completion_comparison_equiv_of_flat_of_residueFieldBijective
      (A := Localization.AtPrime p.asIdeal)
      (B := Localization.AtPrime pA.asIdeal)
      hmax hres).symm

/-- Helper for Lemma 15.51.4: the transported branch comparison map from `R̂_[p]` to the
completed localization above the lifted prime `r`. -/
noncomputable def branch_completion_compare
    (p : PrimeSpectrum R) (m : MaximalSpectrum R)
    (pA : PrimeSpectrum (Localization.AtPrime m.asIdeal))
    (hpA : PrimeSpectrum.comap (algebraMap R (Localization.AtPrime m.asIdeal)) pA = p)
    (r : PrimeSpectrum (R̂_[m.toPrimeSpectrum]))
    (hr : PrimeSpectrum.comap
      (algebraMap (Localization.AtPrime m.asIdeal) (R̂_[m.toPrimeSpectrum])) r = pA) :
    R̂_[p] →+*
      AdicCompletion (maximalIdeal (Localization.AtPrime r.asIdeal))
        (Localization.AtPrime r.asIdeal) :=
  let fpr :=
    Localization.localRingHom pA.asIdeal r.asIdeal
      (algebraMap (Localization.AtPrime m.asIdeal) (R̂_[m.toPrimeSpectrum])) hr
  (maximalIdealCompletionMap fpr).comp
    (branch_source_completion_algEquiv (R := R) p m pA hpA).symm.toRingHom

/-- Helper for Lemma 15.51.4: the transported branch comparison map is a local homomorphism. -/
lemma branch_completion_compare_isLocalHom
    (p : PrimeSpectrum R) (m : MaximalSpectrum R)
    (pA : PrimeSpectrum (Localization.AtPrime m.asIdeal))
    (hpA : PrimeSpectrum.comap (algebraMap R (Localization.AtPrime m.asIdeal)) pA = p)
    (r : PrimeSpectrum (R̂_[m.toPrimeSpectrum]))
    (hr : PrimeSpectrum.comap
      (algebraMap (Localization.AtPrime m.asIdeal) (R̂_[m.toPrimeSpectrum])) r = pA) :
    IsLocalHom (branch_completion_compare (R := R) p m pA hpA r hr) := by
  let Ap := Localization.AtPrime pA.asIdeal
  let Ar := Localization.AtPrime r.asIdeal
  let C := AdicCompletion (maximalIdeal Ar) Ar
  let fpr :=
    Localization.localRingHom pA.asIdeal r.asIdeal
      (algebraMap (Localization.AtPrime m.asIdeal) (R̂_[m.toPrimeSpectrum])) hr
  let e := branch_source_completion_algEquiv (R := R) p m pA hpA
  let _ : IsLocalHom fpr := inferInstance
  let _ : IsCompleteLocalRing (AdicCompletion (maximalIdeal Ap) Ap) :=
    completion_isCompleteLocalRing_of_maximalIdeal_fg (S := Ap)
      (Ideal.fg_of_isNoetherianRing (maximalIdeal Ap))
  let _ : IsCompleteLocalRing C :=
    completion_isCompleteLocalRing_of_maximalIdeal_fg (S := Ar)
      (Ideal.fg_of_isNoetherianRing (maximalIdeal Ar))
  let _ : IsLocalHom (maximalIdealCompletionMap fpr) := by infer_instance
  let _ : IsLocalHom e.symm.toRingHom :=
    Function.Surjective.isLocalHom _ e.symm.surjective
  -- Proof comment: the transported branch comparison is the composite of two local maps.
  simpa [branch_completion_compare, Ap, Ar, C, fpr, e] using
    (inferInstance :
      IsLocalHom ((maximalIdealCompletionMap fpr).comp e.symm.toRingHom))

/-- Helper for Lemma 15.51.4: the transported branch comparison map is faithfully flat. -/
lemma branch_completion_compare_faithfullyFlat
    (p : PrimeSpectrum R) (m : MaximalSpectrum R)
    (pA : PrimeSpectrum (Localization.AtPrime m.asIdeal))
    (hpA : PrimeSpectrum.comap (algebraMap R (Localization.AtPrime m.asIdeal)) pA = p)
    (r : PrimeSpectrum (R̂_[m.toPrimeSpectrum]))
    (hr : PrimeSpectrum.comap
      (algebraMap (Localization.AtPrime m.asIdeal) (R̂_[m.toPrimeSpectrum])) r = pA) :
    RingHom.FaithfullyFlat (branch_completion_compare (R := R) p m pA hpA r hr) := by
  let Ap := Localization.AtPrime pA.asIdeal
  let Ar := Localization.AtPrime r.asIdeal
  let C := AdicCompletion (maximalIdeal Ar) Ar
  let fpr :=
    Localization.localRingHom pA.asIdeal r.asIdeal
      (algebraMap (Localization.AtPrime m.asIdeal) (R̂_[m.toPrimeSpectrum])) hr
  let e := branch_source_completion_algEquiv (R := R) p m pA hpA
  let g := branch_completion_compare (R := R) p m pA hpA r hr
  let _ : Algebra Ap Ar := fpr.toAlgebra
  let _ : IsLocalHom fpr := inferInstance
  have hfpr_flat : fpr.Flat := by
    -- Proof comment: the localized branch map is flat because localizations are flat.
    exact RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat Ap Ar)
  have hcompletion_flat : (maximalIdealCompletionMap fpr).Flat := by
    -- Proof comment: completion preserves flatness for local maps of Noetherian local rings.
    exact (flat_iff_flat_maximalIdealCompletionMap fpr).2 hfpr_flat
  have he_flat : e.symm.toRingHom.Flat :=
    RingHom.Flat.of_bijective e.symm.bijective
  have hg_flat : g.Flat := by
    -- Proof comment: the transported branch comparison is a flat composite.
    simpa [g, branch_completion_compare, Ap, Ar, C, fpr, e] using
      (RingHom.Flat.comp he_flat hcompletion_flat)
  let _ : IsLocalHom g :=
    branch_completion_compare_isLocalHom (R := R) p m pA hpA r hr
  let _ : Algebra R̂_[p] C := g.toAlgebra
  let _ : Module.Flat R̂_[p] C := by
    exact RingHom.flat_algebraMap_iff.mp <| by
      simpa [g, RingHom.algebraMap_toAlgebra] using hg_flat
  -- Proof comment: a flat local map is faithfully flat, so the branch comparison is suitable
  -- for axiom `(D)`.
  simpa [g, RingHom.algebraMap_toAlgebra] using
    (RingHom.faithfullyFlat_algebraMap_iff.mpr
      (Module.FaithfullyFlat.of_flat_of_isLocalHom : Module.FaithfullyFlat R̂_[p] C))

/-- Helper for Lemma 15.51.4: after localizing at `q`, the closed fiber is exactly the
`q`-fiber written in the original prime-pair notation. -/
lemma prime_localization_closedFiber_compare
    (P : FieldAlgebraProperty) (q : PrimeSpectrum R)
    {S : Type u} [CommRing S] [Algebra R S]
    [Algebra (Localization.AtPrime q.asIdeal) S]
    [IsScalarTower R (Localization.AtPrime q.asIdeal) S] :
    P (ResidueField (Localization.AtPrime q.asIdeal))
      ((maximalIdeal (Localization.AtPrime q.asIdeal)).Fiber S) ↔
      P q.asIdeal.ResidueField (q.asIdeal.Fiber S) := by
  constructor
  · intro h
    -- Proof comment: both presentations are definitionally the same local fiber algebra.
    simpa using h
  · intro h
    -- Proof comment: rewrite back from the prime-pair notation to the closed-fiber notation.
    simpa using h

/-- Helper for Lemma 15.51.4: maximal-local formal fibers imply the prime-pair criterion after
transporting from a maximal localization down to the chosen prime localization. -/
lemma prime_pair_property_of_maximal_local_formal_fibers
    (P : FieldAlgebraProperty) [P.HasPropertyC] [P.HasPropertyD]
    (hmax : ∀ m : MaximalSpectrum R,
      LocalFormalFibersHaveProperty P (Localization.AtPrime m.asIdeal)) :
    SatisfiesPPrimePairCondition P R := by
  intro p q hqp
  obtain ⟨m, hmmax, hpm⟩ := p.asIdeal.exists_le_maximal p.2.1
  let m' : MaximalSpectrum R := ⟨m, hmmax⟩
  let A := Localization.AtPrime m'.asIdeal
  let Ahat := R̂_[m'.toPrimeSpectrum]
  have hqm : q.asIdeal ≤ m'.asIdeal := le_trans hqp hpm
  let pA : PrimeSpectrum A :=
    (IsLocalization.AtPrime.primeSpectrumOrderIso A m'.asIdeal).symm ⟨p, hpm⟩
  let qA : PrimeSpectrum A :=
    (IsLocalization.AtPrime.primeSpectrumOrderIso A m'.asIdeal).symm ⟨q, hqm⟩
  let Ap := Localization.AtPrime pA.asIdeal
  have hpA :
      PrimeSpectrum.comap (algebraMap R A) pA = p := by
    -- Proof comment: `pA` was chosen as the prime of `R_m` corresponding to `p ⊆ m`.
    exact Subtype.ext_iff.mp <|
      (IsLocalization.AtPrime.primeSpectrumOrderIso A m'.asIdeal).apply_symm_apply ⟨p, hpm⟩
  have hff_completion :
      RingHom.FaithfullyFlat (algebraMap A Ahat) :=
    maximalIdeal_adicCompletion_algebraMap_faithfullyFlat A
  obtain ⟨r, hr⟩ :=
    (PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := A) (B := Ahat)) pA
  let Ar := Localization.AtPrime r.asIdeal
  let fpr := Localization.localRingHom pA.asIdeal r.asIdeal (algebraMap A Ahat) hr
  let C := AdicCompletion (maximalIdeal Ar) Ar
  -- Route correction: abandon the previous too-coarse `IsPRing R_m` wrapper and keep the source
  -- proof's explicit diagram `R_m → (R_m)^∧ → ((R_m)^∧)_r → C`.
  have hAhatC_regular :
      (algebraMap Ahat C).IsRegularRingMap := by
    -- Proof comment: this is exactly the regular upstairs composite from the source proof.
    simpa [Ahat, C] using lifted_branch_completion_regular (A := A) r
  have hqC :
      P q.asIdeal.ResidueField (q.asIdeal.Fiber C) := by
    -- Proof comment: now apply axiom `(C)` to the flat completion `A → A^∧` and the regular
    -- composite `A^∧ → C`, then rewrite the chosen prime of `A` back to the original `q ⊆ m`.
    simpa [A, Ahat, C, qA] using
      (FieldAlgebraProperty.HasPropertyC.regularAscent
        (P := P) A Ahat C (hmax m') qA)
  have hApCompletion :
      AdicCompletion (maximalIdeal Ap) Ap ≃+* R̂_[p] := by
    -- Proof comment: the source branch `(R_m)_{p_A}` is exactly `R_p`, and so are their
    -- maximal-ideal completions.
    simpa [Ap] using branch_source_completion_algEquiv
      (R := R) p m' pA hpA
  let Aq := Localization.AtPrime q.asIdeal
  let g : R̂_[p] →+* C :=
    branch_completion_compare (R := R) p m' pA hpA r hr
  let _ : IsNoetherianRing (R̂_[p]) :=
    adicCompletion_isNoetherianRing (R := Aq) (I := maximalIdeal Aq)
  let _ : IsNoetherianRing C :=
    adicCompletion_isNoetherianRing (R := Ar) (I := maximalIdeal Ar)
  let _ : IsCompleteLocalRing (R̂_[p]) :=
    completion_isCompleteLocalRing_of_maximalIdeal_fg (S := Aq)
      (Ideal.fg_of_isNoetherianRing (maximalIdeal Aq))
  let _ : IsCompleteLocalRing C :=
    completion_isCompleteLocalRing_of_maximalIdeal_fg (S := Ar)
      (Ideal.fg_of_isNoetherianRing (maximalIdeal Ar))
  let _ : Algebra Aq (R̂_[p]) := inferInstance
  let _ : Algebra R̂_[p] C := g.toAlgebra
  let _ : Algebra Aq C := (g.comp (algebraMap Aq (R̂_[p]))).toAlgebra
  let _ : IsScalarTower Aq (R̂_[p]) C := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsLocalHom (algebraMap Aq (R̂_[p])) :=
    completion_isLocalHom_of_local_ring (S := Aq)
  let _ : IsLocalHom (algebraMap (R̂_[p]) C) := by
    simpa [g, RingHom.algebraMap_toAlgebra] using
      branch_completion_compare_isLocalHom (R := R) p m' pA hpA r hr
  have hqC_closed :
      P (ResidueField Aq) ((maximalIdeal Aq).Fiber C) := by
    -- Proof comment: rewrite the upstairs `q`-fiber into the closed fiber over `R_q`.
    simpa [Aq] using
      (prime_localization_closedFiber_compare (P := P) (q := q) (S := C)).2 hqC
  have hqRhat_closed :
      P (ResidueField Aq) ((maximalIdeal Aq).Fiber (R̂_[p])) := by
    -- Proof comment: axiom `(D)` descends the closed-fiber property from the branch completion to
    -- the actual completed localization `R̂_[p]`.
    exact
      (FieldAlgebraProperty.HasPropertyD.closedFiberDescent
        (P := P) Aq (R̂_[p]) C
        (hBC := by
          simpa [g, RingHom.algebraMap_toAlgebra] using
            branch_completion_compare_faithfullyFlat (R := R) p m' pA hpA r hr)
        hqC_closed)
  -- Proof comment: translate the descended closed-fiber statement back to the original
  -- prime-pair formulation.
  exact
    (prime_localization_closedFiber_compare (P := P) (q := q) (S := R̂_[p])).1 <|
      by simpa [Aq] using hqRhat_closed

/-- Helper for Lemma 15.51.4: faithful flatness of maximal-ideal completion lifts a prime of the
maximal localization `R_m` to a prime of its completion. -/
lemma exists_prime_over_completed_maximal_localization
    (m : MaximalSpectrum R) (p : PrimeSpectrum R) (hpm : p.asIdeal ≤ m.asIdeal) :
    ∃ r : PrimeSpectrum (R̂_[m.toPrimeSpectrum]),
      PrimeSpectrum.comap
        (algebraMap (Localization.AtPrime m.asIdeal) (R̂_[m.toPrimeSpectrum])) r =
          (IsLocalization.AtPrime.primeSpectrumOrderIso
            (Localization.AtPrime m.asIdeal) m.asIdeal).symm ⟨p, hpm⟩ := by
  let A := Localization.AtPrime m.asIdeal
  let Ahat := R̂_[m.toPrimeSpectrum]
  let pA : PrimeSpectrum A :=
    (IsLocalization.AtPrime.primeSpectrumOrderIso A m.asIdeal).symm ⟨p, hpm⟩
  have hff :
      RingHom.FaithfullyFlat (algebraMap A Ahat) :=
    maximalIdeal_adicCompletion_algebraMap_faithfullyFlat A
  -- Proof comment: use the canonical surjectivity on spectra for faithfully flat maps.
  exact
    (PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := A) (B := Ahat)) pA

-- Proof sketch: the forward implication is the specialization of the `P`-ring condition to the
-- maximal prime `m`. For the converse, fix `p : Spec(R)` and choose a maximal ideal `m ⊇ p`.
-- The hypothesis gives `P` on the fibers of `R_m → (R_m)^∧`. After choosing a prime of
-- `(R_m)^∧` over `pR_m` using faithful flatness of completion, apply Proposition `15.50.6` and
-- Lemma `15.41.4` to obtain a regular map from `(R_m)^∧` to the relevant completed localization,
-- then use `(C)` to transfer `P` to those fibers and `(D)` to descend from that faithfully flat
-- local extension to the fibers of `R_p → (R_p)^∧`.
/-- Lemma 15.51.4: let `R` be a Noetherian ring, and assume the field-algebra property `P`
satisfies `(C)` and `(D)`. Then `R` is a `P`-ring if and only if, for every maximal ideal `m` of
`R`, the local ring `R_m` has formal fibers with property `P`. -/
@[stacks 0BIU]
theorem isPRing_iff_localFormalFibersHaveProperty_atMaximal
    (P : FieldAlgebraProperty)
    [P.HasPropertyC] [P.HasPropertyD] :
    IsPRing P R ↔
      ∀ m : MaximalSpectrum R,
        LocalFormalFibersHaveProperty P (Localization.AtPrime m.asIdeal) := by
  constructor
  · intro h m
    -- Proof comment: rewrite the local formal-fiber condition at `m` as the prime-pair statement
    -- and specialize the global `P`-ring hypothesis to `q ≤ m`.
    rw [localFormalFibersHaveProperty_localizationAtMaximal_iff_primePair
      (P := P) (m := m)]
    intro q hqm
    exact h.satisfiesPPrimePairCondition m.toPrimeSpectrum q hqm
  · intro hmax
    -- Proof comment: the converse is exactly the prime-pair criterion assembled from the
    -- maximal-local hypotheses.
    exact
      isPRing_of_satisfiesPPrimePairCondition
        (P := P)
        (R := R)
        (prime_pair_property_of_maximal_local_formal_fibers
          (P := P) (hmax := hmax))

end
