import Mathlib
import Mathlib.Tactic.TFAE
import stacks_project.Chap15.Definition_15_61_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

noncomputable section

universe u

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
    A →ₐ[R] Module.End R (TorMod[R, i](A, B)) := by
  let F := Tor (ModuleCat R) i
  let eA : End (ModuleCat.of R A) ≃+* Module.End R A := (ModuleCat.of R A).endRingEquiv
  let eT : End (Tor[R, i](A, B)) ≃+* Module.End R (TorMod[R, i](A, B)) :=
    (Tor[R, i](A, B)).endRingEquiv
  refine
    { toFun := fun a ↦ eT <| ((F.map (eA.symm (Module.toModuleEnd R A a))).app (ModuleCat.of R B))
      map_one' := sorry
      map_mul' := sorry
      map_zero' := sorry
      map_add' := sorry
      commutes' := sorry }

private noncomputable def torRightAction (i : ℕ) :
    B →ₐ[R] Module.End R (TorMod[R, i](A, B)) := by
  let F := ((Tor (ModuleCat R) i).obj (ModuleCat.of R A))
  let eB : End (ModuleCat.of R B) ≃+* Module.End R B := (ModuleCat.of R B).endRingEquiv
  let eT : End (Tor[R, i](A, B)) ≃+* Module.End R (TorMod[R, i](A, B)) :=
    (Tor[R, i](A, B)).endRingEquiv
  refine
    { toFun := fun b ↦ eT <| F.map (eB.symm (Module.toModuleEnd R B b))
      map_one' := sorry
      map_mul' := sorry
      map_zero' := sorry
      map_add' := sorry
      commutes' := sorry }

private noncomputable def torTensorAction (i : ℕ) :
    A ⊗[R] B →ₐ[R] Module.End R (TorMod[R, i](A, B)) :=
  Algebra.TensorProduct.lift (torLeftAction i) (torRightAction i) <| by
    intro a b
    sorry

private noncomputable instance torTensorProductModule (i : ℕ) :
    Module (A ⊗[R] B) (TorMod[R, i](A, B)) := by
  let _ : Module (Module.End R (TorMod[R, i](A, B))) (TorMod[R, i](A, B)) := inferInstance
  simpa using (Module.compHom (TorMod[R, i](A, B)) (torTensorAction i).toRingHom :
    Module (A ⊗[R] B) (TorMod[R, i](A, B)))

-- Proof sketch: use Lemma `15.61.3` to identify Tor after localizing at primes and after passing to
-- the local tensor product, so the local Tor-independence condition and the localized vanishing
-- condition are both equivalent to the vanishing of the global positive Tor groups. Then apply the
-- standard criterion that a module is zero iff all of its localizations at prime ideals vanish.
/-- Lemma 15.61.6: for commutative `R`-algebras `A` and `B`, the following are equivalent: `A`
and `B` are Tor independent over `R`; for every prime `𝔯` of `R` and primes `𝔭` of `A`, `𝔮` of
`B` lying over `𝔯`, the local rings `A_𝔭` and `B_𝔮` are Tor independent over `R_𝔯`; and for every
prime `𝔰` of `A ⊗[R] B`, the canonical `(A ⊗[R] B)`-linear positive Tor groups `Tor_i^R(A, B)`
become zero after localizing at `𝔰`. -/
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
      ] := sorry

end
