import Mathlib
import StacksProject_2024.Chap10.Definition_10_137_10
import StacksProject_2024.Chap16.Situation_16_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra IsLocalRing
open RamificationOneDvrFactorizationSituation

universe u x

noncomputable section

section

/-
Domain-style sampling pass for Lemma 16.4.4.

Primary domain: source-facing smoothness at prime-spectrum points in a DVR factorization
situation, together with the cotangent module `Ω[A⁄R]` after base change to `Λ`.

Sampled owner declarations:
* `Algebra.SmoothAtPrime`;
* `Algebra.smoothAtPrime_iff_isSmoothAt`;
* `RamificationOneDvrFactorizationSituation.q`;
* `RamificationOneDvrFactorizationSituation.p`;
* `PrimeSpectrum.comap`.

Best owner abstraction: the chapter’s source-facing smoothness owner is
`Algebra.SmoothAtPrime` on prime-spectrum points. The factorization data are already owned by
`RamificationOneDvrFactorizationSituation`; the ideals `S.q` and `S.p` are derived from that
owner, the points of `Spec(S.A)` are canonically `⟨S.q, inferInstance⟩` and `⟨S.p, inferInstance⟩`,
and the pullback point of `Spec(B)` is canonically
`PrimeSpectrum.comap ψ.toRingHom ⟨S.p, inferInstance⟩`. The local predicate `IsSmoothAt` is only a
proof bridge via `smoothAtPrime_iff_isSmoothAt`.

Primitive-vs-derived split:
* primitive data: `S : RamificationOneDvrFactorizationSituation` and the explicit surjection
  `ψ : B →ₐ[S.R] S.A`;
* derived API: the induced `S.A`-algebra structure on `S.L`, the scalar tower `S.R → S.A → S.L`,
  the ideals `S.q` and `S.p`, the corresponding points `⟨S.q, inferInstance⟩` and
  `⟨S.p, inferInstance⟩`, and the pullback point
  `PrimeSpectrum.comap ψ.toRingHom ⟨S.p, inferInstance⟩`.

Source/core/bridge triage:
* `source-facing`: the smoothness statement at the points `⟨S.q, inferInstance⟩`,
  `⟨S.p, inferInstance⟩`, and `PrimeSpectrum.comap ψ.toRingHom ⟨S.p, inferInstance⟩`;
* `core/canonical`: `RamificationOneDvrFactorizationSituation`, `S.q`, `S.p`,
  `Algebra.SmoothAtPrime`, and `PrimeSpectrum.comap`;
* `bridge/view`: the local formal-smoothness criterion `smoothAtPrime_iff_isSmoothAt`.
-/

variable (S : RamificationOneDvrFactorizationSituation)

-- Proof sketch: use the exact conormal sequence for the surjection `B ↠ A` to identify the source
-- cokernel hypothesis with freeness of `S.L ⊗[S.A] Ω[S.A⁄S.R]`. Smoothness at `S.q` gives
-- freeness of the differential module at the generic point with rank equal to the relative
-- dimension there; flatness of `S.A` over `S.R` compares the fiber dimensions at `S.q` and at
-- `S.p`. Then rewrite through `smoothAtPrime_iff_isSmoothAt` and apply the local cotangent-space
-- criterion for smoothness at `S.p`.
/-- Lemma 16.4.4: let `S : RamificationOneDvrFactorizationSituation`, so `φ : A → Λ` is the
factorization map with `𝔮 = ker(φ)` and `𝔭 = φ⁻¹(\mathfrak m_Λ)`. Let `ψ : B →ₐ[S.R] S.A` be a
surjective `R`-algebra map, formalized as `Function.Surjective ψ`. Assume `R → A` is smooth at
`𝔮`, formalized as `Algebra.SmoothAtPrime S.R S.A ⟨S.q, inferInstance⟩`; assume `R → B` is smooth
at the pullback of `𝔭`, formalized as
`Algebra.SmoothAtPrime S.R B (PrimeSpectrum.comap ψ.toRingHom ⟨S.p, inferInstance⟩)`; and assume
the canonical cokernel hypothesis is expressed in the library-facing form that
`S.L ⊗[S.A] Ω[S.A⁄S.R]` is a free `S.L`-module. Then `R → A` is smooth at `𝔭`, formalized as
`Algebra.SmoothAtPrime S.R S.A ⟨S.p, inferInstance⟩`. -/
theorem smoothAtPrime_p_of_smoothAtPrime_q_of_source_smoothAtPrime_of_free_kaehler_baseChange
    (S : RamificationOneDvrFactorizationSituation)
    {B : Type x} [CommRing B] [Algebra S.R B]
    (ψ : B →ₐ[S.R] S.A)
    (hψ : Function.Surjective ψ)
    (hAq : Algebra.SmoothAtPrime S.R S.A ⟨S.q, inferInstance⟩)
    (hB : Algebra.SmoothAtPrime S.R B (PrimeSpectrum.comap ψ.toRingHom ⟨S.p, inferInstance⟩))
    (hfree : Module.Free S.L (S.L ⊗[S.A] Ω[S.A⁄S.R])) :
    Algebra.SmoothAtPrime S.R S.A ⟨S.p, inferInstance⟩ := sorry

end
