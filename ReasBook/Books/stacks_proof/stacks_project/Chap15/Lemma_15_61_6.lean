import Mathlib
import Mathlib.Tactic.TFAE
import StacksProject_2024.Chap15.Definition_15_61_1
import StacksProject_2024.Chap10.Lemma_10_23_1
import StacksProject_2024.Chap15.Lemma_15_61_4
import StacksProject_2024.Chap15.Lemma_15_61_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

noncomputable section

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]

/- Domain triage:
* primary domain: Tor-vanishing for commutative algebras and its behavior under localization;
* sampled owner declarations in the chapter/project:
  `IsTorIndependent`,
  `CategoryTheory.Tor`,
  `torBaseChangeComparison`,
  `IsTorIndependent.baseChange`;
* best owner abstraction: the canonical `Tor` object in `ModuleCat`, with `IsTorIndependent` as
  the source-facing vanishing predicate;
* primitive data: the rings `R`, `A`, `B` and the canonical `Tor` objects;
* derived API: the canonical `(A ⊗[R] B)`-module structure on `Tor_i^R(A, B)` and its
  localizations at prime ideals of `A ⊗[R] B`.

Source/core/bridge triage:
* `source-facing`: the TFAE statement comparing Tor independence with its localizations;
* `core/canonical`: `IsTorIndependent` and the owner bifunctor `Tor`;
* `bridge/view`: the canonical `(A ⊗[R] B)`-linear realization of the underlying `Tor` carrier,
  needed only to form `LocalizedModule.AtPrime`.
-/
set_option quotPrecheck false in
local notation "TorMod[" S ", " i "](" M ", " N ")" =>
  ↑(Tor[S, i](M, N))

private noncomputable def torLeftAction (i : ℕ) :
    A →ₐ[R] Module.End R (TorMod[R, i](A, B)) := sorry

private noncomputable def torRightAction (i : ℕ) :
    B →ₐ[R] Module.End R (TorMod[R, i](A, B)) := sorry

/-- Helper for Lemma 15.61.6: the Tor endomorphisms induced by the two variables commute by
naturality of the bifunctor `Tor`. -/
private theorem tor_left_right_endomorphisms_commute
    (i : ℕ) (a : A) (b : B) :
    let F := Tor (ModuleCat R) i
    let eA : End (ModuleCat.of R A) ≃+* Module.End R A := (ModuleCat.of R A).endRingEquiv
    let eB : End (ModuleCat.of R B) ≃+* Module.End R B := (ModuleCat.of R B).endRingEquiv
    let eT : End (Tor[R, i](A, B)) ≃+* Module.End R (TorMod[R, i](A, B)) :=
      (Tor[R, i](A, B)).endRingEquiv
    Commute
      (eT <| ((F.map (eA.symm (Module.toModuleEnd R A a))).app (ModuleCat.of R B)))
      (eT <| (((F.obj (ModuleCat.of R A)).map (eB.symm (Module.toModuleEnd R B b))))) := by
  -- The left-variable action is a natural transformation in the right variable, so it commutes
  -- with the right-variable map after evaluating at `B`.
  dsimp
  rw [Commute, SemiconjBy]
  exact congrArg ModuleCat.Hom.hom
    (NatTrans.naturality
      (NatTrans.leftDerived
        ((MonoidalCategory.tensoringLeft (ModuleCat R)).map
          ((ModuleCat.of R A).endRingEquiv.symm (DistribSMul.toLinearMap R A a))) i)
      ((ModuleCat.of R B).endRingEquiv.symm (DistribSMul.toLinearMap R B b)))

private noncomputable def torTensorAction (i : ℕ) :
    A ⊗[R] B →ₐ[R] Module.End R (TorMod[R, i](A, B)) := sorry

private noncomputable instance torTensorProductModule (i : ℕ) :
    Module (A ⊗[R] B) (TorMod[R, i](A, B)) := by
  let _ : Module (Module.End R (TorMod[R, i](A, B))) (TorMod[R, i](A, B)) := inferInstance
  simpa using (Module.compHom (TorMod[R, i](A, B)) (torTensorAction i).toRingHom :
    Module (A ⊗[R] B) (TorMod[R, i](A, B)))

/-- Helper for Lemma 15.61.6: if a Tor group is already zero globally, then every localization of
its canonical `A ⊗[R] B`-module at a tensor prime is also zero. -/
private theorem isZero_localized_tor_of_isZero_tor
    {i : ℕ}
    (hTor : IsZero (Tor[R, i](A, B)))
    (s : PrimeSpectrum (A ⊗[R] B)) :
    IsZero
      (ModuleCat.of (Localization.AtPrime s.asIdeal)
        (LocalizedModule.AtPrime s.asIdeal (TorMod[R, i](A, B)))) := by
  -- The source Tor carrier is already subsingleton, and prime localization preserves that
  -- subsingleton carrier structure.
  let hsub : Subsingleton (TorMod[R, i](A, B)) := ModuleCat.subsingleton_of_isZero hTor
  let hloc :
      Subsingleton (LocalizedModule.AtPrime s.asIdeal (TorMod[R, i](A, B))) :=
    IsLocalizedModule.subsingleton_of_subsingleton s.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap s.asIdeal.primeCompl (TorMod[R, i](A, B)))
  exact ModuleCat.isZero_of_subsingleton _

/-- Helper for Lemma 15.61.6: if every localization of the canonical `A ⊗[R] B`-module attached
to a Tor group is zero, then the global Tor group is zero. -/
private theorem isZero_tor_of_isZero_localized_tor
    {i : ℕ}
    (hlocalized :
      ∀ s : PrimeSpectrum (A ⊗[R] B),
        IsZero
          (ModuleCat.of (Localization.AtPrime s.asIdeal)
            (LocalizedModule.AtPrime s.asIdeal (TorMod[R, i](A, B))))) :
    IsZero (Tor[R, i](A, B)) := by
  -- Apply the Chapter 10 local-global criterion over the tensor-product ring and feed it the
  -- prime-local vanishing hypothesis obtained from `hlocalized`.
  have hprime :
      ∀ (P : Ideal (A ⊗[R] B)) [P.IsPrime],
        Subsingleton (LocalizedModule.AtPrime P (TorMod[R, i](A, B))) := by
    intro P _
    let s : PrimeSpectrum (A ⊗[R] B) := ⟨P, inferInstance⟩
    simpa using ModuleCat.subsingleton_of_isZero (hlocalized s)
  have hsub :
      Subsingleton (TorMod[R, i](A, B)) := by
    exact
      ((module_zero_localization_tfae
        (R := A ⊗[R] B) (M := TorMod[R, i](A, B))).out 1 0).mp hprime
  exact ModuleCat.isZero_of_subsingleton _

/-- Helper for Lemma 15.61.6: the contraction of a tensor-product prime to `A` still lies over
the contracted prime in `R`. -/
private theorem tensor_prime_under_left_liesOver
    (s : PrimeSpectrum (A ⊗[R] B)) :
    (s.asIdeal.under A).LiesOver (s.asIdeal.under R) := by
  -- The two successive contractions agree because the tensor product carries the usual scalar
  -- tower `R → A → A ⊗[R] B`.
  rw [Ideal.liesOver_iff, Ideal.under_def, Ideal.under_def]
  change Ideal.comap (algebraMap R (A ⊗[R] B)) s.asIdeal =
    Ideal.comap (algebraMap R A) (Ideal.comap (algebraMap A (A ⊗[R] B)) s.asIdeal)
  simpa [RingHom.comp_apply] using
    (Ideal.comap_comap (algebraMap R A) (algebraMap A (A ⊗[R] B)) s.asIdeal).symm

/-- Helper for Lemma 15.61.6: the contraction of a tensor-product prime to `B` still lies over
the contracted prime in `R`. -/
private theorem tensor_prime_under_right_liesOver
    (s : PrimeSpectrum (A ⊗[R] B)) :
    (s.asIdeal.under B).LiesOver (s.asIdeal.under R) := by
  -- The same contraction argument works along the scalar tower `R → B → A ⊗[R] B`.
  rw [Ideal.liesOver_iff, Ideal.under_def, Ideal.under_def]
  change Ideal.comap (algebraMap R (A ⊗[R] B)) s.asIdeal =
    Ideal.comap (algebraMap R B) (Ideal.comap (algebraMap B (A ⊗[R] B)) s.asIdeal)
  simpa [RingHom.comp_apply] using
    (Ideal.comap_comap (algebraMap R B) (algebraMap B (A ⊗[R] B)) s.asIdeal).symm

/-- Helper for Lemma 15.61.6: a tensor-product prime canonically determines the compatible prime
of `A` lying over its contraction to `R`. -/
private noncomputable def tensor_prime_left_primesOver
    (s : PrimeSpectrum (A ⊗[R] B)) :
    (s.asIdeal.under R).primesOver A := by
  letI : (s.asIdeal.under A).LiesOver (s.asIdeal.under R) :=
    tensor_prime_under_left_liesOver (R := R) (A := A) (B := B) s
  exact Ideal.primesOver.mk (s.asIdeal.under R) (s.asIdeal.under A)

/-- Helper for Lemma 15.61.6: a tensor-product prime canonically determines the compatible prime
of `B` lying over its contraction to `R`. -/
private noncomputable def tensor_prime_right_primesOver
    (s : PrimeSpectrum (A ⊗[R] B)) :
    (s.asIdeal.under R).primesOver B := by
  letI : (s.asIdeal.under B).LiesOver (s.asIdeal.under R) :=
    tensor_prime_under_right_liesOver (R := R) (A := A) (B := B) s
  exact Ideal.primesOver.mk (s.asIdeal.under R) (s.asIdeal.under B)

/-- Helper for Lemma 15.61.6: Tor independence survives the flat localization of the base ring at
`r`. -/
private theorem isTorIndependent_localized_base_of_isTorIndependent
    (h : IsTorIndependent R A B)
    (r : PrimeSpectrum R) :
    IsTorIndependent (Localization.AtPrime r.asIdeal)
      (A ⊗[R] Localization.AtPrime r.asIdeal)
      (B ⊗[R] Localization.AtPrime r.asIdeal) := by
  letI : Module.Flat R (Localization.AtPrime r.asIdeal) := inferInstance
  -- Proof comment: this is the direct flat base-change step from Lemma 15.61.4 applied to the
  -- localization map `R → R_𝔯`.
  simpa using IsTorIndependent.baseChange
    (R := R) (R' := Localization.AtPrime r.asIdeal) (A := A) (B := B) h

/-- Helper for Lemma 15.61.6: Tor independence over the contracted prime localizations should
force the localization of the global Tor module at the tensor prime to vanish. -/
private theorem isZero_localized_tor_of_local_tor_independent
    (hlocal :
      ∀ r : PrimeSpectrum R,
        ∀ p : r.asIdeal.primesOver A,
          ∀ q : r.asIdeal.primesOver B,
            IsTorIndependent (Localization.AtPrime r.asIdeal)
              (Localization.AtPrime p.1) (Localization.AtPrime q.1))
    (s : PrimeSpectrum (A ⊗[R] B))
    (i : ℕ) (hi : 0 < i) :
    IsZero
      (ModuleCat.of (Localization.AtPrime s.asIdeal)
        (LocalizedModule.AtPrime s.asIdeal (TorMod[R, i](A, B)))) := by
  let r : PrimeSpectrum R := ⟨s.asIdeal.under R, inferInstance⟩
  let p : r.asIdeal.primesOver A :=
    tensor_prime_left_primesOver (R := R) (A := A) (B := B) s
  let q : r.asIdeal.primesOver B :=
    tensor_prime_right_primesOver (R := R) (A := A) (B := B) s
  have hlocal_zero :
      IsZero (Tor[Localization.AtPrime r.asIdeal, i](Localization.AtPrime p.1,
        Localization.AtPrime q.1)) :=
    hlocal r p q i hi
  -- Route correction: the remaining work is the source-faithful base-change comparison from
  -- Lemma 15.61.3 at the contracted primes of `s`.
  -- TODO(Lemma 15.61.6): compare the localized global Tor module with the local Tor module over
  -- `R_r` from `hlocal_zero`, then transport the resulting `IsZero` statement across that
  -- canonical comparison isomorphism.
  sorry

/-- Helper for Lemma 15.61.6: global Tor independence should descend to every compatible triple
of prime localizations. -/
private theorem isTorIndependent_localizationAtPrimes_of_isTorIndependent
    (h : IsTorIndependent R A B)
    (r : PrimeSpectrum R)
    (p : r.asIdeal.primesOver A)
    (q : r.asIdeal.primesOver B) :
    IsTorIndependent (Localization.AtPrime r.asIdeal)
      (Localization.AtPrime p.1) (Localization.AtPrime q.1) := by
  have hbase :
      IsTorIndependent (Localization.AtPrime r.asIdeal)
        (A ⊗[R] Localization.AtPrime r.asIdeal)
        (B ⊗[R] Localization.AtPrime r.asIdeal) :=
    isTorIndependent_localized_base_of_isTorIndependent
      (R := R) (A := A) (B := B) h r
  intro i hi
  have hbase_zero :
      IsZero
        (Tor[Localization.AtPrime r.asIdeal, i](
          (A ⊗[R] Localization.AtPrime r.asIdeal)
          , (B ⊗[R] Localization.AtPrime r.asIdeal))) :=
    hbase i hi
  -- Route correction: the source proof uses the direct `(1 → 2)` step, not the old `(3 → 2)`
  -- localization-only route. The established prefix is now the vanishing of the positive Tor
  -- group after the first flat base change `R → R_𝔯`; only the comparison from that base-changed
  -- pair to the prime localizations `(A_𝔭, B_𝔮)` remains.
  -- TODO(Lemma 15.61.6): compare the global Tor group above with
  -- `Tor_i^{R_𝔯}(A_𝔭, B_𝔮)` using the canonical maps
  -- `A ⊗[R] R_𝔯 → A_𝔭` and `R_𝔯 ⊗[R] B → B_𝔮`, then transport `hbase_zero` across the resulting
  -- Lemma 15.61.3 isomorphism.
  let _ := hbase_zero
  sorry

-- Proof sketch: use Lemma `15.61.3` to identify Tor after localizing at primes and after passing to
-- the local tensor product, so the local Tor-independence condition and the localized vanishing
-- condition are both equivalent to the vanishing of the global positive Tor groups. Then apply the
-- standard criterion that a module is zero iff all of its localizations at prime ideals vanish.
/-- Lemma 15.61.6: for commutative `R`-algebras `A` and `B`, the following are equivalent: `A`
and `B` are Tor independent over `R`; for every prime `𝔯` of `R` and primes `𝔭` of `A`, `𝔮` of
`B` lying over `𝔯`, the local rings `A_𝔭` and `B_𝔮` are Tor independent over `R_𝔯`; and for every
prime `𝔰` of `A ⊗[R] B`, the canonical `(A ⊗[R] B)`-linear positive Tor groups `Tor_i^R(A, B)`
become zero after localizing at `𝔰`. -/
@[stacks 08HX]
theorem isTorIndependent_tfae_localizationAtPrimes_and_localizedTor :
    List.TFAE
      [ IsTorIndependent R A B
      , ∀ r : PrimeSpectrum R,
          ∀ p : r.asIdeal.primesOver A,
            ∀ q : r.asIdeal.primesOver B,
              IsTorIndependent (Localization.AtPrime r.asIdeal)
                (Localization.AtPrime p.1) (Localization.AtPrime q.1)
      , ∀ s : PrimeSpectrum (A ⊗[R] B),
          ∀ i : ℕ, 0 < i →
            IsZero
              (ModuleCat.of (Localization.AtPrime s.asIdeal)
                (LocalizedModule.AtPrime s.asIdeal (TorMod[R, i](A, B))))
      ] := by
  tfae_have 1 → 3 := by
    intro h s i hi
    -- Localize the globally vanishing positive Tor group at the chosen tensor prime.
    exact isZero_localized_tor_of_isZero_tor (A := A) (B := B) (R := R) (h i hi) s
  tfae_have 3 → 1 := by
    intro h i hi
    -- Detect global vanishing from the vanishing of all prime localizations over `A ⊗[R] B`.
    exact isZero_tor_of_isZero_localized_tor (A := A) (B := B) (R := R)
      (i := i) (fun s ↦ h s i hi)
  tfae_have 2 → 3 := by
    intro h s i hi
    -- Reduce to the source-faithful local Tor comparison at the contracted primes of `s`.
    exact isZero_localized_tor_of_local_tor_independent
      (A := A) (B := B) (R := R) h s i hi
  tfae_have 1 → 2 := by
    intro h r p q
    -- Route correction: use the source-faithful direct base-change step at the compatible triple.
    exact isTorIndependent_localizationAtPrimes_of_isTorIndependent
      (A := A) (B := B) (R := R) h r p q
  tfae_finish

end
