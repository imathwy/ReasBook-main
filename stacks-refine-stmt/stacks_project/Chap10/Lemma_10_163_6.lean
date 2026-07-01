import Mathlib
import stacks_project.Chap10.Lemma_10_157_3
import stacks_project.Chap10.Lemma_10_163_4
import stacks_project.Chap10.Lemma_10_163_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/- Domain-style sampling pass:
* primary domain: Noetherian commutative algebra of ascent of reducedness along flat maps;
* sampled owner declarations of the same kind:
  - `IsReduced`, the owner for ring reducedness;
  - `isReduced_iff_serreConditionR_zero_and_serreConditionS_one`, the canonical owner-level
    characterization of reducedness by Serre conditions;
  - `serreConditionR_of_flat_of_fiber`, the chapter ascent theorem for `(R₀)`;
  - `serreConditionS_of_flat_of_fiber`, the chapter ascent theorem for `(S₁)`.

Best owner abstraction:
* the public target stays the source-facing reducedness theorem, but the proof should pass entirely
  through the canonical owners `IsReduced`, `SerreConditionR`, and `SerreConditionS`, instead of
  keeping a parallel reducedness-specific local wheel.

Primitive data vs. derived API:
* primitive data: the flat algebra `R → S`, the Noetherian hypotheses on `R` and `S`, the
  reduced base-ring owner `[IsReduced R]`, and the fiberwise reducedness hypothesis `hfiber`;
* derived API: the `(R₀)` and `(S₁)` instances for the base and the fibers, obtained canonically
  from the Serre criterion and then fed into the existing ascent theorems.

Source/core/bridge triage:
* `source-facing`: `isReduced_of_flat_of_fiber`, the textbook ascent statement for reducedness;
* `core/canonical`: `IsReduced`, `SerreConditionR`, `SerreConditionS`, and the criterion
  `isReduced_iff_serreConditionR_zero_and_serreConditionS_one`;
* `bridge/view`: the two ascent theorems for `(R₀)` and `(S₁)` along the flat map.
-/
-- Proof sketch: for Noetherian rings, reducedness is equivalent to Serre's conditions `(S_1)` and
-- `(R_0)` by Lemma `10.157.3`. Apply the flat ascent results `10.163.4` and `10.163.5` to the base
-- ring `R` and the reduced fiber rings `p.asIdeal.Fiber S`, then invoke Lemma `10.157.3` again to
-- recover reducedness of `S`.
/-- Lemma 10.163.6: if `R → S` is flat, `R` and `S` are Noetherian, `R` is reduced, and every
fiber ring `κ(𝔭) ⊗[R] S`, formalized as `p.asIdeal.Fiber S`, is reduced, then `S` is reduced. -/
theorem isReduced_of_flat_of_fiber
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S] [IsReduced R]
    (hfiber : ∀ p : PrimeSpectrum R, IsReduced (p.asIdeal.Fiber S)) :
    IsReduced S := by
  have hfiber_serre (p : PrimeSpectrum R) :
      SerreConditionR (p.asIdeal.Fiber S) 0 ∧ SerreConditionS (p.asIdeal.Fiber S) 1 :=
    isReduced_iff_serreConditionR_zero_and_serreConditionS_one.1 (hfiber p)
  have hSR : SerreConditionR S 0 :=
    serreConditionR_of_flat_of_fiber fun p ↦ (hfiber_serre p).1
  have hSS : SerreConditionS S 1 :=
    serreConditionS_of_flat_of_fiber fun p ↦ (hfiber_serre p).2
  exact isReduced_iff_serreConditionR_zero_and_serreConditionS_one.2 ⟨hSR, hSS⟩

end
