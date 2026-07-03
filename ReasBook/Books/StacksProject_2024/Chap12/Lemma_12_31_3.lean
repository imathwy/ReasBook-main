import Mathlib
import StacksProject_2024.Chap12.Definition_12_31_2

open CategoryTheory.Limits

noncomputable section

namespace CategoryTheory

namespace SequentialInverseSystem

local notation "AbSeq" => SequentialInverseSystem AddCommGrpCat

/- Domain-style sampling for Lemma 12.31.3 in the inverse-limit / Mittag-Leffler domain:
- owner abstractions:
  * `SequentialInverseSystem` and `SequentialInverseSystem.IsMittagLeffler` from
    `Definition_12_31_2`
  * `Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono`
  * `ShortComplex.ShortExact.mk'`
  * `ShortComplex.exact_and_mono_f_iff_f_is_kernel`
- primitive data: a short exact sequence `S` of sequential inverse systems together with, for (2)
  and (3), the owner Mittag-Leffler hypothesis on one term
- derived API: the induced short complex `S.map lim` on inverse limits and its exactness,
  monomorphism, and short-exactness consequences
- source/core/bridge triage:
  * `source-facing`: the textbook statements about inverse limits and Mittag-Leffler towers
  * `core/canonical`: the owner exactness criteria for `ShortComplex` under `lim`
  * `bridge/view`: the abelian-group specialization from a short exact sequence of towers to the
    induced exactness properties on inverse limits

These lemmas should therefore live under the chapter owner `SequentialInverseSystem`; the short
complex on inverse limits is derived from `lim`, not packaged as a separate public wrapper. -/

variable (S : ShortComplex AbSeq)

-- Proof sketch: inverse limits of abelian groups are left exact. Apply the owner exact-functor
-- criterion for `lim` preserving finite limits to the given short exact sequence of sequential
-- inverse systems.
/-- Lemma 12.31.3 (1): for a short exact sequence of sequential inverse systems of abelian groups,
the induced sequence on inverse limits is left exact; equivalently, the map
`\varprojlim A_i \to \varprojlim B_i` is monic and the short complex
`\varprojlim A_i \to \varprojlim B_i \to \varprojlim C_i` is exact. -/
theorem inverseLimit_exact_and_mono_of_shortExact
    (hS : S.ShortExact)
    : (S.map lim).Exact ∧ Mono (S.map lim).f := by
  simpa using
    (S.map lim).exact_and_mono_f_iff_f_is_kernel.2
      ⟨KernelFork.mapIsLimit _ hS.fIsKernel lim⟩

-- Proof sketch: evaluate the short exact sequence at each stage, where the right map is
-- surjective. The image-stabilization condition for the middle inverse system then passes to the
-- quotient inverse system, so the right term is again Mittag-Leffler.
/-- Lemma 12.31.3 (2): if the middle term of a short exact sequence of sequential inverse systems
of abelian groups is Mittag-Leffler, then the quotient inverse system is also Mittag-Leffler. -/
theorem isMittagLeffler_right_of_shortExact
    (hS : S.ShortExact)
    (hML : S.X₂.IsMittagLeffler) :
    S.X₃.IsMittagLeffler := sorry

-- Proof sketch: this is the abelian-group specialization of the inverse-limit short-exactness
-- theorem for short exact sequences of sequential inverse systems with Mittag-Leffler left term.
/-- Lemma 12.31.3 (3): if the left term of a short exact sequence of sequential inverse systems of
abelian groups is Mittag-Leffler, then the induced sequence on inverse limits is short exact. -/
theorem inverseLimit_shortExact_of_isMittagLeffler_left
    (hS : S.ShortExact)
    (hML : S.X₁.IsMittagLeffler) :
    (S.map lim).ShortExact := sorry

end SequentialInverseSystem

end CategoryTheory
