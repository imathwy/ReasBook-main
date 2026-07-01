import stacks_project.Chap10.Definition_10_54_1
import stacks_project.Chap10.Remark_10_75_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits

universe u v

section

variable {R : Type u} {S : Type v} {M : Type u}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [Module.FinitePresentation S M]

/- Domain-style sampling for the approximation-based flatness criterion:
- primary domain: flatness of a finitely presented module over an essentially finitely presented
  local map, detected from a quotient-flatness hypothesis and a `Tor₁` vanishing hypothesis;
- sampled owner declarations of the same kind:
  `RingHom.EssFinitePresentation`,
  `DirectedLocalEssFinitePresentationModuleApproximation`,
  `flat_of_tor_one_quotient_vanishing_and_flat_mod_ideal`,
  `Tor₁[R](M, N)`;
- best owner abstraction: the source-facing theorem here still concludes in the canonical owner
  `Module.Flat`, and its homological hypothesis should reuse the chapter owner notation
  `Tor₁[R](M, R ⧸ I)` rather than a raw derived-functor term;
- primitive data: the local map `R → S`, the essentially finitely presented hypothesis, the
  finitely presented `S`-module `M`, the proper ideal `I`, the vanishing of `Tor₁^R(M, R / I)`,
  and flatness of `M / IM` over `R / I`;
- derived API: flatness of `M` over `R`.

Source/core/bridge triage:
- `source-facing`: Lemma 10.128.7 itself;
- `core/canonical`: `Module.Flat`, `RingHom.EssFinitePresentation`, and the chapter owner notation
  `Tor₁[R](M, N)`;
- `bridge/view`: the directed approximation owner
  `DirectedLocalEssFinitePresentationModuleApproximation` and the stagewise descent/ascent lemmas
  `10.127.13`, `10.128.3`, `10.99.12`, and `10.99.10`, which belong to the proof route rather
  than to the public statement.
-/

-- Proof sketch: use Lemma `10.127.13` to approximate the local map `R → S` and the finitely
-- presented `S`-module `M` by finite type stage data. Descend flatness of `M / IM` to a stage via
-- Lemma `10.128.3`, then use finite generation of the stage `Tor₁` module together with the
-- vanishing of `Tor₁^R(M, R / I)` and the surjectivity-up-to-localization statement from
-- Lemma `10.99.12` to force stagewise vanishing of `Tor₁`. Finally apply the variant of the local
-- criterion from Lemma `10.99.10` at that stage and pass back to the limit.
/-- Lemma 10.128.7: let `R → S` be a local homomorphism of local rings, let `I ≠ R` be an ideal of
`R`, and let `M` be an `S`-module. If `S` is essentially of finite presentation over `R`, `M` is
of finite presentation over `S`, `Tor₁^R(M, R / I)` vanishes, and `M / IM` is flat over `R / I`,
then `M` is flat over `R`. -/
theorem flat_of_tor_one_quotient_vanishing_and_flat_mod_ideal_of_essFinitePresentation
    (hess : (algebraMap R S).EssFinitePresentation)
    (I : Ideal R) (hI : I ≠ ⊤)
    (hTor : IsZero (Tor₁[R](M, R ⧸ I)))
    (hflat : Module.Flat (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M))) :
    Module.Flat R M := sorry

end
