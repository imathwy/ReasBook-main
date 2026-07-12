import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section Length

open IsLocalRing LocalizedModule

local notation "AtPrime" => LocalizedModule.AtPrime

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- Domain triage:
- primary domain: finite-length modules and composition series of submodules;
- sampled owner API:
  `JordanHolderModule.instJordanHolderLattice`,
  `Module.length_compositionSeries`,
  `covBy_iff_quot_is_simple`,
  `IsSimpleModule.annihilator_isMaximal`;
- core/canonical owner: `CompositionSeries (Submodule R M)`;
- layer split: the quotient module `s.factor i` is a short reusable view of the owner quotient
  attached to the cover `s.step i`, while simplicity, annihilator, and localization statements are
  derived API.
-/

/- Lemma 10.52.11: for a maximal chain of submodules from `0` to `M`, the number of strict
inclusions is the length of `M`. This is exactly the canonical theorem
`Module.length_compositionSeries`. -/
recall Module.length_compositionSeries

namespace CompositionSeries

/-- Helper for Chap10 Lemma 10 52 11: localizing an `R`-linear equivalence at a prime ideal
preserves module length. -/
private theorem localizedLength_eq_of_linearEquiv
    {N : Type*} [AddCommGroup N] [Module R N]
    (m : Ideal R) [m.IsPrime] (e : M ≃ₗ[R] N) :
    Module.length (Localization.AtPrime m) (AtPrime m M) =
      Module.length (Localization.AtPrime m) (AtPrime m N) := by
  -- Build the localized equivalence from the localized linear map and its bijectivity.
  let eLoc :
      AtPrime m M ≃ₗ[Localization.AtPrime m] AtPrime m N :=
    LinearEquiv.ofBijective
      (LocalizedModule.map m.primeCompl e.toLinearMap)
      ⟨LocalizedModule.map_injective m.primeCompl e.toLinearMap e.injective,
        LocalizedModule.map_surjective m.primeCompl e.toLinearMap e.surjective⟩
  simpa using eLoc.length_eq

/-- Helper for Chap10 Lemma 10 52 11: localizing the top submodule has the same length as
localizing the ambient module. -/
private theorem localizedTopLength_eq
    (m : Ideal R) [m.IsPrime] :
    Module.length (Localization.AtPrime m) (AtPrime m (⊤ : Submodule R M)) =
      Module.length (Localization.AtPrime m) (AtPrime m M) := by
  -- Transport the comparison through the canonical linear equivalence from the top submodule.
  simpa using localizedLength_eq_of_linearEquiv (R := R)
    (M := (⊤ : Submodule R M)) (m := m)
    (Submodule.topEquiv : (⊤ : Submodule R M) ≃ₗ[R] M)

/-- Helper for Chap10 Lemma 10 52 11: localizing the quotient `R ⧸ I` at `p` identifies it with
the quotient of the localized ring by the image of `I`. -/
private noncomputable def localizedQuotientAtPrimeLinearEquivQuotientMap
    (I p : Ideal R) [p.IsPrime] :
    AtPrime p (R ⧸ I) ≃ₗ[Localization.AtPrime p]
      (Localization.AtPrime p) ⧸ Ideal.map (algebraMap R (Localization.AtPrime p)) I :=
  (LocalizedModule.equivTensorProduct p.primeCompl (R ⧸ I)).trans
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot
      (Localization.AtPrime p) I).symm.toLinearEquiv

/-- The `i`-th successive quotient in a composition series of submodules. -/
abbrev factor (s : CompositionSeries (Submodule R M)) (i : Fin s.length) :=
  s i.succ ⧸ (s i.castSucc).comap (s i.succ).subtype

-- Proof sketch: the step relation in a composition series says `s (Fin.castSucc i)` is maximal in
-- `s (Fin.succ i)`, and `covBy_iff_quot_is_simple` identifies such maximal submodule quotients with
-- simple modules.
/-- Each successive quotient in the chosen maximal chain is a simple `R`-module. -/
theorem factor_isSimpleModule (s : CompositionSeries (Submodule R M)) (i : Fin s.length) :
    IsSimpleModule R (s.factor i) := by
  simpa [factor] using
    (covBy_iff_quot_is_simple (CovBy.le (s.step i))).mp (s.step i)

-- Proof sketch: apply clause (1) to see that the factor is simple. Over a commutative ring, a
-- simple module is canonically a quotient by its annihilator ideal, and that annihilator is
-- maximal.
/-- The annihilator of each successive factor is a maximal ideal. -/
theorem factor_annihilator_isMaximal (s : CompositionSeries (Submodule R M)) (i : Fin s.length) :
    (Module.annihilator R (s.factor i)).IsMaximal := by
  let _ : IsSimpleModule R (s.factor i) := s.factor_isSimpleModule i
  exact IsSimpleModule.annihilator_isMaximal

/-- Each successive factor is linearly isomorphic to the quotient of `R` by its annihilator. -/
theorem factor_isomorphic_quotient_annihilator
    (s : CompositionSeries (Submodule R M)) (i : Fin s.length) :
    Nonempty (s.factor i ≃ₗ[R] R ⧸ Module.annihilator R (s.factor i)) := by
  have hsimple : IsSimpleModule R (s.factor i) := s.factor_isSimpleModule i
  obtain ⟨I, _, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hsimple
  have hAnn : Module.annihilator R (s.factor i) = I := by
    rw [e.annihilator_eq, I.annihilator_quotient]
  exact ⟨e.trans <| Submodule.quotEquivOfEq _ _ hAnn.symm⟩

/-- Helper for Chap10 Lemma 10 52 11: after localizing at a maximal ideal `m`, each simple
composition factor contributes length `1` exactly when its annihilator is `m`, and contributes
length `0` otherwise. -/
private theorem localizedFactorLength_eq_ite
    (s : CompositionSeries (Submodule R M)) (i : Fin s.length)
    (m : Ideal R) [m.IsMaximal] :
    Module.length (Localization.AtPrime m) (AtPrime m (s.factor i)) =
      if Module.annihilator R (s.factor i) = m then 1 else 0 := by
  let J : Ideal R := Module.annihilator R (s.factor i)
  by_cases hJ : J = m
  · -- Replace the factor by the quotient by its annihilator, then localize that quotient.
    obtain ⟨e⟩ := s.factor_isomorphic_quotient_annihilator i
    have hfactor :
        Module.length (Localization.AtPrime m) (AtPrime m (s.factor i)) =
          Module.length (Localization.AtPrime m) (AtPrime m (R ⧸ J)) := by
      simpa [J] using localizedLength_eq_of_linearEquiv (R := R) (M := s.factor i)
        (m := m) e
    let eJm : (R ⧸ J) ≃ₗ[R] (R ⧸ m) := Submodule.quotEquivOfEq _ _ hJ
    have hquot :
        Module.length (Localization.AtPrime m) (AtPrime m (R ⧸ J)) =
          Module.length (Localization.AtPrime m) (AtPrime m (R ⧸ m)) := by
      simpa using localizedLength_eq_of_linearEquiv (R := R) (M := R ⧸ J) (m := m) eJm
    let eQuot₀ :
        AtPrime m (R ⧸ m) ≃ₗ[Localization.AtPrime m]
          Localization.AtPrime m ⧸ Ideal.map (algebraMap R (Localization.AtPrime m)) m :=
      localizedQuotientAtPrimeLinearEquivQuotientMap (R := R) m m
    let eQuot :
        AtPrime m (R ⧸ m) ≃ₗ[Localization.AtPrime m]
          Localization.AtPrime m ⧸ maximalIdeal (Localization.AtPrime m) :=
      eQuot₀.trans <|
        Submodule.quotEquivOfEq _ _ (Localization.AtPrime.map_eq_maximalIdeal (I := m))
    have hsimple :
        IsSimpleModule (Localization.AtPrime m)
          (Localization.AtPrime m ⧸ maximalIdeal (Localization.AtPrime m)) := by
      rw [isSimpleModule_iff_isCoatom]
      exact Ideal.isMaximal_def.mp (maximalIdeal.isMaximal (Localization.AtPrime m))
    let _ :
        IsSimpleModule (Localization.AtPrime m)
          (Localization.AtPrime m ⧸ maximalIdeal (Localization.AtPrime m)) := hsimple
    -- The localized quotient by `m` is the residue field of the local ring, hence has length `1`.
    calc
      Module.length (Localization.AtPrime m) (AtPrime m (s.factor i))
          = Module.length (Localization.AtPrime m) (AtPrime m (R ⧸ J)) := by
              simpa using hfactor
      _ = Module.length (Localization.AtPrime m) (AtPrime m (R ⧸ m)) := hquot
      _ = Module.length (Localization.AtPrime m)
            (Localization.AtPrime m ⧸ maximalIdeal (Localization.AtPrime m)) := by
              simpa using eQuot.length_eq
      _ = 1 := by
            simpa using
              (Module.length_eq_one
                (R := Localization.AtPrime m)
                (M := Localization.AtPrime m ⧸ maximalIdeal (Localization.AtPrime m)))
      _ = if Module.annihilator R (s.factor i) = m then 1 else 0 := by
            simp [J, hJ]
  · -- If the annihilator is a different maximal ideal, a denominator from `m.primeCompl`
    -- kills the whole quotient after localization, so the localized factor has length `0`.
    have hJmax : J.IsMaximal := by
      simpa [J] using s.factor_annihilator_isMaximal i
    have hnotle : ¬ J ≤ m := by
      intro hle
      exact hJ <| hJmax.eq_of_le ‹m.IsMaximal›.ne_top hle
    classical
    obtain ⟨r, hrJ, hrm⟩ : ∃ r : R, r ∈ J ∧ r ∉ m := by
      simpa [SetLike.le_def] using hnotle
    obtain ⟨e⟩ := s.factor_isomorphic_quotient_annihilator i
    have hfactor :
        Module.length (Localization.AtPrime m) (AtPrime m (s.factor i)) =
          Module.length (Localization.AtPrime m) (AtPrime m (R ⧸ J)) := by
      simpa [J] using localizedLength_eq_of_linearEquiv (R := R) (M := s.factor i)
        (m := m) e
    have hsub :
        Subsingleton (AtPrime m (R ⧸ J)) := by
      rw [LocalizedModule.subsingleton_iff (S := m.primeCompl) (M := R ⧸ J)]
      intro x
      refine ⟨r, hrm, ?_⟩
      have hr0 : Ideal.Quotient.mk J r = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hrJ
      simpa [Algebra.smul_def, hr0]
    -- A subsingleton localized factor has length `0`.
    calc
      Module.length (Localization.AtPrime m) (AtPrime m (s.factor i))
          = Module.length (Localization.AtPrime m) (AtPrime m (R ⧸ J)) := by
              simpa using hfactor
      _ = 0 := Module.length_eq_zero_iff.mpr hsub
      _ = if Module.annihilator R (s.factor i) = m then 1 else 0 := by
            simp [J, hJ]

/-- Helper for Chap10 Lemma 10 52 11: localizing one step of the composition series adds the
localized length of the new simple factor. -/
private theorem localizedStepLength_eq_add_factorLength
    (s : CompositionSeries (Submodule R M)) (i : Fin s.length)
    (m : Ideal R) [m.IsMaximal] :
    Module.length (Localization.AtPrime m) (AtPrime m (s i.succ)) =
      Module.length (Localization.AtPrime m) (AtPrime m (s i.castSucc)) +
        Module.length (Localization.AtPrime m) (AtPrime m (s.factor i)) := by
  let P : Submodule R M := s i.succ
  let Q : Submodule R M := s i.castSucc
  let N : Submodule R P := Q.comap P.subtype
  have hQP : Q ≤ P := by
    intro x hx
    exact CovBy.le (s.step i) hx
  have hN :
      Module.length (Localization.AtPrime m) (AtPrime m N) =
        Module.length (Localization.AtPrime m) (AtPrime m Q) := by
    let e₀ := N.equivMapOfInjective P.subtype (Submodule.injective_subtype _)
    have hmap : N.map P.subtype = Q := by
      rw [Submodule.map_comap_subtype, inf_of_le_right hQP]
    let e : N ≃ₗ[R] Q := e₀.trans <| LinearEquiv.ofEq _ _ hmap
    simpa [Q] using localizedLength_eq_of_linearEquiv (R := R) (M := N) (m := m) e
  let f :
      AtPrime m N →ₗ[Localization.AtPrime m] AtPrime m P :=
    LocalizedModule.map m.primeCompl N.subtype
  let g :
      AtPrime m P →ₗ[Localization.AtPrime m] AtPrime m (P ⧸ N) :=
    LocalizedModule.map m.primeCompl (Submodule.mkQ N)
  have hf : Function.Injective f := by
    simpa [f] using
      (LocalizedModule.map_injective m.primeCompl N.subtype (Submodule.subtype_injective _))
  have hg : Function.Surjective g := by
    simpa [g] using
      (LocalizedModule.map_surjective m.primeCompl (Submodule.mkQ N) (Submodule.mkQ_surjective N))
  have hex : Function.Exact f g := by
    simpa [f, g] using
      (LocalizedModule.map_exact m.primeCompl N.subtype (Submodule.mkQ N)
        (LinearMap.exact_subtype_mkQ N))
  have hlen :
      Module.length (Localization.AtPrime m) (AtPrime m P) =
        Module.length (Localization.AtPrime m) (AtPrime m N) +
          Module.length (Localization.AtPrime m) (AtPrime m (P ⧸ N)) := by
    -- Apply additivity of length to the localized short exact sequence.
    exact Module.length_eq_add_of_exact f g hf hg hex
  calc
    Module.length (Localization.AtPrime m) (AtPrime m (s i.succ))
        = Module.length (Localization.AtPrime m) (AtPrime m P) := by
            rfl
    _ =
        Module.length (Localization.AtPrime m) (AtPrime m N) +
          Module.length (Localization.AtPrime m) (AtPrime m (P ⧸ N)) := hlen
    _ =
        Module.length (Localization.AtPrime m) (AtPrime m Q) +
          Module.length (Localization.AtPrime m) (AtPrime m (P ⧸ N)) := by
            rw [hN]
    _ =
        Module.length (Localization.AtPrime m) (AtPrime m (s i.castSucc)) +
          Module.length (Localization.AtPrime m) (AtPrime m (s.factor i)) := by
            rfl

-- Proof sketch: localize the composition series at `m`; exactness of localization turns the
-- successive quotients into the localizations of the factors, and the localized factor is nonzero
-- exactly when the corresponding simple factor has annihilator `m`.
/-- Chap10 Lemma 10 52 11: for a maximal ideal `m`, the number of successive quotients whose
annihilator is `m` is the length of the localization of `M` at `m`. -/
theorem factor_count_eq_length_localizedModule
    (s : CompositionSeries (Submodule R M)) (h₀ : s.head = ⊥) (h₁ : s.last = ⊤)
    (m : Ideal R) [m.IsMaximal] :
    ENat.card { i : Fin s.length // Module.annihilator R (s.factor i) = m } =
      Module.length (Localization.AtPrime m) (AtPrime m M) := by
  have hprefix :
      ∀ n : ℕ, ∀ hn : n ≤ s.length,
        Module.length (Localization.AtPrime m)
            (AtPrime m (s ⟨n, Nat.lt_succ_of_le hn⟩)) =
          ∑ i : Fin n,
            Module.length (Localization.AtPrime m)
              (AtPrime m (s.factor ⟨i, Nat.lt_of_lt_of_le i.isLt hn⟩)) := by
    intro n
    induction n with
    | zero =>
        intro hn
        have hs0' : s ⟨0, Nat.lt_succ_of_le hn⟩ = ⊥ := by
          simpa using h₀
        -- The localized initial stage is zero because the composition series starts at `⊥`.
        rw [hs0']
        simp
    | succ n ih =>
        intro hn
        have hn' : n ≤ s.length := Nat.le_of_succ_le hn
        let i : Fin s.length := ⟨n, Nat.lt_of_succ_le hn⟩
        -- Add the next localized factor via the localized short exact sequence.
        calc
          Module.length (Localization.AtPrime m)
              (AtPrime m (s ⟨n + 1, Nat.lt_succ_of_le hn⟩))
              =
                Module.length (Localization.AtPrime m)
                  (AtPrime m (s ⟨n, Nat.lt_succ_of_le hn'⟩)) +
                Module.length (Localization.AtPrime m)
                  (AtPrime m (s.factor i)) := by
                    simpa [i] using s.localizedStepLength_eq_add_factorLength i m
          _ = (∑ j : Fin n,
                Module.length (Localization.AtPrime m)
                  (AtPrime m (s.factor ⟨j, Nat.lt_of_lt_of_le j.isLt hn'⟩))) +
                Module.length (Localization.AtPrime m)
                  (AtPrime m (s.factor i)) := by
                    rw [ih hn']
          _ = ∑ j : Fin (n + 1),
                Module.length (Localization.AtPrime m)
                  (AtPrime m (s.factor ⟨j, Nat.lt_of_lt_of_le j.isLt hn⟩)) := by
                    symm
                    simpa [i] using
                      (Fin.sum_univ_castSucc
                        (f := fun j : Fin (n + 1) ↦
                          Module.length (Localization.AtPrime m)
                            (AtPrime m (s.factor ⟨j, Nat.lt_of_lt_of_le j.isLt hn⟩))))
  have hcount :
      ENat.card { i : Fin s.length // Module.annihilator R (s.factor i) = m } =
        ∑ i : Fin s.length,
          if Module.annihilator R (s.factor i) = m then 1 else 0 := by
    calc
      ENat.card { i : Fin s.length // Module.annihilator R (s.factor i) = m }
          = ((Finset.univ.filter
                (fun i : Fin s.length => Module.annihilator R (s.factor i) = m)).card : ENat) := by
              simp [ENat.card_eq_coe_fintype_card, Fintype.card_subtype]
      _ = ∑ i : Fin s.length,
            if Module.annihilator R (s.factor i) = m then 1 else 0 := by
            simp
  have hlast :
      Module.length (Localization.AtPrime m) (AtPrime m s.last) =
        ∑ i : Fin s.length,
          Module.length (Localization.AtPrime m) (AtPrime m (s.factor i)) := by
    simpa [RelSeries.last] using hprefix s.length le_rfl
  have htop :
      Module.length (Localization.AtPrime m) (AtPrime m (⊤ : Submodule R M)) =
        Module.length (Localization.AtPrime m) (AtPrime m M) := by
    -- Record the final transport from the terminal submodule back to the ambient module.
    exact localizedTopLength_eq (R := R) (M := M) m
  -- Convert the cardinality to an indicator sum, rewrite each term as the localized factor length,
  -- and then telescope along the localized composition series.
  calc
    ENat.card { i : Fin s.length // Module.annihilator R (s.factor i) = m }
        = ∑ i : Fin s.length,
            if Module.annihilator R (s.factor i) = m then 1 else 0 := hcount
    _ = ∑ i : Fin s.length,
          Module.length (Localization.AtPrime m) (AtPrime m (s.factor i)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simpa using (s.localizedFactorLength_eq_ite i m).symm
    _ = Module.length (Localization.AtPrime m) (AtPrime m s.last) := by
          symm
          exact hlast
    _ = Module.length (Localization.AtPrime m) (AtPrime m (⊤ : Submodule R M)) := by
          rw [h₁]
    _ = Module.length (Localization.AtPrime m) (AtPrime m M) := htop

end CompositionSeries

end Length
