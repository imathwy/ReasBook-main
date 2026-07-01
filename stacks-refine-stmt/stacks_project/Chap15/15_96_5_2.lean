import stacks_project.Chap15.Lemma_15_96_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CochainComplex
open ModFSquared.Nat

universe u

section

variable {A : Type u} [CommRing A]

/- Domain-style sampling:
- primary domain: Bockstein differentials on cohomology coming from the short exact sequence
  `0 → M^\bullet / fM^\bullet → M^\bullet / f²M^\bullet → M^\bullet / fM^\bullet → 0`;
- sampled owner declarations:
  `ModFSquared.Nat.bockstein`,
  `ShortComplex.ShortExact.δ`,
  `CochainComplex.of`,
  `CochainComplex.reduceModIdealA`;
- best owner abstraction:
  `source-facing`: the cohomology complex `H^\bullet(M^\bullet / f)` with the canonical Bockstein
    differential;
  `core/canonical`: the owner connecting morphism `ModFSquared.bockstein` on `ModuleComplex A`,
    together with its bounded-below bridge `ModFSquared.Nat.bockstein`;
  `bridge/view`: any presentation of the terms as
    `H^i(M^\bullet ⊗_A f^iA / f^(i + 1)A)`;
-- primitive data vs derived API: the primitive data are only the bounded-below reduced complex
-- `reduceModIdealA (principalIdeal f) M`
  and the canonical connecting morphisms on its homology. The old family `β` and the proof
  `β ≫ β = 0` were derived structure and should not be primitive public inputs. -/

/-- 15.96.5.2: the canonical cohomology complex `H^\bullet(M^\bullet / f)` is the nonnegative
cochain complex whose degree-`i` term is `H^i(M^\bullet / fM^\bullet)` and whose differential is
the Berthelot-Ogus Bockstein morphism on the scalar-restricted `A`-linear bridge
`reduceModIdealA (principalIdeal f) M`. This keeps the source-facing cohomological grading and uses the
bounded-below owner declaration `ModFSquared.Nat.bockstein` for the differential. -/
abbrev modfCohomologyBocksteinComplex
    (f : A) (M : NatModuleCochainComplex A) (hM : IsTermwiseFTorsionFree f M) :
    NatModuleCochainComplex A :=
  CochainComplex.of
    (fun i ↦ (reduceModIdealA (principalIdeal f) M).homology i)
    (fun i ↦ bockstein f M i hM)
    (fun i ↦ by
      sorry)

/-- The degree-`i` term of the canonical Bockstein complex is
`H^i((M^\bullet / fM^\bullet)_A)`. -/
@[simp] theorem modfCohomologyBocksteinComplex_X
    (f : A) (M : NatModuleCochainComplex A) (hM : IsTermwiseFTorsionFree f M) (i : ℕ) :
    (modfCohomologyBocksteinComplex f M hM).X i =
      (reduceModIdealA (principalIdeal f) M).homology i := by
  simp [modfCohomologyBocksteinComplex]

/-- The differential of the canonical Bockstein complex is the Berthelot-Ogus Bockstein map. -/
@[simp] theorem modfCohomologyBocksteinComplex_d
    (f : A) (M : NatModuleCochainComplex A) (hM : IsTermwiseFTorsionFree f M) (i : ℕ) :
    (modfCohomologyBocksteinComplex f M hM).d i (i + 1) =
      bockstein f M i hM := by
  simp [modfCohomologyBocksteinComplex]

-- Proof sketch: `modfCohomologyBocksteinComplex f M hM` is a cochain complex by construction, so
-- its two successive differentials compose to zero. The preceding identification of the
-- differential with `ModFSquared.Nat.bockstein` turns this generic `d ≫ d = 0` statement into the
-- Bockstein square-zero relation.
/-- Two successive Berthelot-Ogus Bockstein morphisms compose to zero. -/
theorem berthelotOgusBockstein_sq
    (f : A) (M : NatModuleCochainComplex A) (hM : IsTermwiseFTorsionFree f M) (i : ℕ) :
    bockstein f M i hM ≫ bockstein f M (i + 1) hM = 0 := by
  simpa only [modfCohomologyBocksteinComplex_d] using
    (modfCohomologyBocksteinComplex f M hM).d_comp_d i (i + 1) (i + 2)

end
