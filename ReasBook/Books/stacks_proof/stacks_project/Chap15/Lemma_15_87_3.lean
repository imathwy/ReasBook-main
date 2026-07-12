import Mathlib
import StacksProject_2024.Chap12.Definition_12_31_2
import StacksProject_2024.Chap13.Definition_13_34_1
import StacksProject_2024.Chap15.Lemma_15_87_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SequentialInverseSystem
open ComplexShape

noncomputable section

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

namespace SequentialInverseSystem

local notation "AbCpxSeq" => SequentialInverseSystem (CochainComplex AddCommGrpCat ℤ)
local notation "H" => HomologicalComplex.homologyFunctor AddCommGrpCat (up ℤ)
local notation "ev" => HomologicalComplex.eval AddCommGrpCat (up ℤ)

/- Domain-style sampling for Lemma 15.87.3:
- primary domain: derived inverse limits of sequential inverse systems of abelian groups and the
  comparison map from cohomology of a termwise inverse limit to the inverse limit of cohomology;
- sampled owner declarations:
  `SequentialInverseSystem.firstDerivedLimit`,
  `SequentialInverseSystem.IsMittagLeffler`,
  `HomologicalComplex.eval`,
  `HomologicalComplex.homologyFunctor`,
  `ShortComplex.ShortExact.isIso_g_iff`;
- best owner abstraction: the vanishing hypotheses are canonically owned by
  `SequentialInverseSystem.firstDerivedLimit`, while the degree and cohomology towers are
  derived from the input tower of cochain complexes by postcomposing with
  `HomologicalComplex.eval` and `HomologicalComplex.homologyFunctor`; the source-facing
  comparison morphism itself is the canonical `limit.post A (H 0)`, and the `IsIso` conclusion is
  derived API from the more primitive short exact sequence via
  `ShortComplex.ShortExact.isIso_g_iff`;
- primitive data: the tower `A : AbCpxSeq`;
- derived API: the three `R^1 lim` objects, the canonical comparison morphism
  `limit.post A (H 0)`, the short exact sequence it fits into, and the resulting `IsIso`
  criterion.

Source/core/bridge triage:
- `source-facing`: the short exact sequence and its `IsIso` corollary with explicit vanishing
  hypotheses;
- `core/canonical`: `SequentialInverseSystem.firstDerivedLimit`, `limit.post`, and
  `ShortComplex.ShortExact.isIso_g_iff`;
- `bridge/view`: the Mittag-Leffler sufficient criterion below. -/

/-- Helper for Lemma 15.87.3: once the left term in a short exact sequence is zero, the right
map is an isomorphism. -/
private theorem isIso_of_shortExact_right_map
    {X Y Z : AddCommGrpCat}
    {ι : X ⟶ Y} {π : Y ⟶ Z}
    (hιπ : ι ≫ π = 0)
    (hshort : (ShortComplex.mk ι π hιπ).ShortExact)
    (hX : IsZero X) :
    IsIso π := by
  -- Proof comment: this is exactly the owner criterion packaged in
  -- `ShortComplex.ShortExact.isIso_g_iff`.
  exact (ShortComplex.ShortExact.isIso_g_iff hshort).2 hX

/-- Helper for Lemma 15.87.3: the last two maps on `R^1 \!\varprojlim` in the Milnor five-term
sequence form an exact pair. -/
private theorem firstDerivedLimitMap_comp_zero
    (S : ShortComplex (SequentialInverseSystem AddCommGrpCat))
    (hS : S.ShortExact) :
    SequentialInverseSystem.firstDerivedLimitMap S.f ≫
      SequentialInverseSystem.firstDerivedLimitMap S.g = 0 := by
  -- Proof comment: this is the final differential relation in the five-term exact sequence from
  -- Lemma `15.87.2`.
  simpa using (sequentialAbelianGroupLimit_exact₅ S hS).toIsComplex.zero 3

/-- Helper for Lemma 15.87.3: the two `R^1 \!\varprojlim` maps in the Milnor five-term exact
sequence form an exact short complex. -/
private theorem firstDerivedLimit_pair_exact_of_shortExact
    (S : ShortComplex (SequentialInverseSystem AddCommGrpCat))
    (hS : S.ShortExact) :
    (ShortComplex.mk
      (SequentialInverseSystem.firstDerivedLimitMap S.f)
      (SequentialInverseSystem.firstDerivedLimitMap S.g)
      (firstDerivedLimitMap_comp_zero S hS)).Exact := by
  -- Proof comment: extract the final adjacent exact pair from the five-term exact sequence.
  simpa [firstDerivedLimitMap_comp_zero] using
    (sequentialAbelianGroupLimit_exact₅ S hS).exact 3

/-- Helper for Lemma 15.87.3: if the left obstruction term `R^1 \!\varprojlim X_1` vanishes in a
short exact row `0 \to X_1 \to X_2 \to X_3 \to 0`, then inverse limit preserves short exactness
of that row. -/
private theorem inverseLimit_shortExact_of_left_firstDerivedLimit_isZero
    (S : ShortComplex (SequentialInverseSystem AddCommGrpCat))
    (hS : S.ShortExact)
    (hleft : IsZero S.X₁.firstDerivedLimit) :
    (S.map lim).ShortExact := by
  have hLimitZero :
      lim.map S.f ≫ lim.map S.g = 0 := by
    -- Proof comment: this is the first differential relation in the five-term exact sequence.
    simpa using (sequentialAbelianGroupLimit_exact₅ S hS).toIsComplex.zero 0
  have hLimitExact :
      (ShortComplex.mk (lim.map S.f) (lim.map S.g) hLimitZero).Exact := by
    -- Proof comment: exactness at `lim X₂` is the first adjacent exact pair in the five-term
    -- exact sequence.
    simpa [hLimitZero] using (sequentialAbelianGroupLimit_exact₅ S hS).exact 0
  have hMono : Mono (lim.map S.f) := sequentialAbelianGroupLimit_mono_map_f S hS
  have hδzero :
      sequentialAbelianGroupLimitδ S hS = 0 := by
    -- Proof comment: any morphism into a zero object is zero.
    exact hleft.eq_of_tgt _ _
  have hSegExact :
      (ShortComplex.mk
        (lim.map S.g)
        (sequentialAbelianGroupLimitδ S hS)
        (by
          -- Proof comment: this is the middle differential relation in the five-term exact
          -- sequence.
          simpa using (sequentialAbelianGroupLimit_exact₅ S hS).toIsComplex.zero 1)).Exact := by
    -- Proof comment: exactness of the five-term chain gives exactness at `lim X₃`.
    simpa using (sequentialAbelianGroupLimit_exact₅ S hS).exact 1
  have hEpi : Epi (lim.map S.g) := by
    -- Proof comment: once the connecting morphism dies, exactness forces `lim.map S.g` to be
    -- surjective.
    exact ((ShortComplex.mk
      (lim.map S.g)
      (sequentialAbelianGroupLimitδ S hS)
      (by simpa using (sequentialAbelianGroupLimit_exact₅ S hS).toIsComplex.zero 1)).exact_iff_epi
        hδzero).1 hSegExact
  exact ShortComplex.ShortExact.mk' hLimitExact hMono hEpi

/-- Helper for Lemma 15.87.3: in the degree-one Milnor exact pair attached to a short exact row,
vanishing of the middle term forces vanishing of the right term because the terminal map is epi.
-/
private theorem firstDerivedLimit_right_isZero_of_middle_isZero
    (S : ShortComplex (SequentialInverseSystem AddCommGrpCat))
    (hS : S.ShortExact)
    (hmid : IsZero S.X₂.firstDerivedLimit) :
    IsZero S.X₃.firstDerivedLimit := by
  have hzero :
      SequentialInverseSystem.firstDerivedLimitMap S.g = 0 := by
    -- Proof comment: any morphism out of a zero source is zero.
    exact hmid.eq_of_src _ _
  letI : Epi (SequentialInverseSystem.firstDerivedLimitMap S.g) :=
    sequentialAbelianGroupLimit_epi_map_g S hS
  -- Proof comment: an epimorphism which is already zero has zero codomain.
  exact IsZero.of_epi_eq_zero (SequentialInverseSystem.firstDerivedLimitMap S.g) hzero

/-- Helper for Lemma 15.87.3: in the degree-one Milnor exact pair attached to a short exact row,
vanishing of the left term turns the right map on `R^1 \!\varprojlim` into an isomorphism.
-/
private theorem firstDerivedLimitMap_isIso_of_left_isZero
    (S : ShortComplex (SequentialInverseSystem AddCommGrpCat))
    (hS : S.ShortExact)
    (hleft : IsZero S.X₁.firstDerivedLimit) :
    IsIso (SequentialInverseSystem.firstDerivedLimitMap S.g) := by
  have hmono :
      Mono (SequentialInverseSystem.firstDerivedLimitMap S.g) := by
    -- Proof comment: exactness at the middle term and a zero left source make the right map mono.
    exact
      ((ShortComplex.mk
        (SequentialInverseSystem.firstDerivedLimitMap S.f)
        (SequentialInverseSystem.firstDerivedLimitMap S.g)
        (firstDerivedLimitMap_comp_zero S hS)).exact_iff_mono
          (hleft.eq_of_src _ _)).1
        (firstDerivedLimit_pair_exact_of_shortExact S hS)
  letI : Mono (SequentialInverseSystem.firstDerivedLimitMap S.g) := hmono
  letI : Epi (SequentialInverseSystem.firstDerivedLimitMap S.g) :=
    sequentialAbelianGroupLimit_epi_map_g S hS
  -- Proof comment: once the right `R^1 lim` map is both mono and epi, it is an isomorphism.
  exact isIso_of_mono_of_epi (SequentialInverseSystem.firstDerivedLimitMap S.g)

/-- Under the vanishing of `R^1 \!\varprojlim` for the degree `-2` and `-1` towers, the canonical
comparison map `H^0(\lim_n A_n^\bullet) ⟶ \lim_n H^0(A_n^\bullet)` sits in the expected Milnor
short exact sequence with left term `R^1 \!\varprojlim H^{-1}(A_n^\bullet)`. -/
theorem inverse_limit_zero_cohomology_shortExact_of_vanishing_degree_r1lim
    (A : AbCpxSeq)
    (hAnegTwo : IsZero <| firstDerivedLimit (A ⋙ ev (-2)))
    (hAnegOne : IsZero <| firstDerivedLimit (A ⋙ ev (-1))) :
    ∃ (ι :
        firstDerivedLimit (A ⋙ H (-1)) ⟶
          (H 0).obj (limit A))
      (hι :
        ι ≫ limit.post A (H 0) = 0),
      (ShortComplex.mk ι (limit.post A (H 0)) hι).ShortExact := by
  -- Route correction: the source proof for Lemma `15.87.3` is the two-spectral-sequence argument
  -- from Lemma `13.21.3`, not the older Chapter `12` cycle/boundary cokernel chase.
  -- TODO: package the displayed degree window as a bounded-below complex of towers, identify the
  -- common abutment `H^0(R lim K)` with `(H 0).obj (limit A)` via the first spectral sequence,
  -- and extract the Milnor short exact row
  -- `0 → firstDerivedLimit (A ⋙ H (-1)) → H^0(R lim K) → limit (A ⋙ H 0) → 0`
  -- from the second spectral sequence.
  sorry

-- Proof sketch: first produce the canonical short exact sequence above from the vanishing of the
-- degree `-2` and `-1` obstruction towers. Then apply the owner criterion
-- `ShortComplex.ShortExact.isIso_g_iff`: vanishing of `R^1 \!\varprojlim H^{-1}(A_n^\bullet)`
-- identifies the left term with zero, so the right map is an isomorphism.
/-- Lemma 15.87.3: for a sequential inverse system of cochain complexes of abelian groups, if the
`R^1 \!\varprojlim` terms of the degree `-2`, degree `-1`, and `H^{-1}` towers vanish, then the
canonical comparison map `H^0(\lim_n A_n^\bullet) ⟶ \lim_n H^0(A_n^\bullet)` is an isomorphism.
-/
@[stacks 0918]
theorem inverse_limit_zero_cohomology_comparison_isIso_of_vanishing_r1lim
    (A : AbCpxSeq)
    (hAnegTwo : IsZero <| firstDerivedLimit (A ⋙ ev (-2)))
    (hAnegOne : IsZero <| firstDerivedLimit (A ⋙ ev (-1)))
    (hHnegOne : IsZero <| firstDerivedLimit (A ⋙ H (-1))) :
    IsIso (limit.post A (H 0)) := by
  -- Proof comment: apply the short exact sequence above and then kill its left term using the
  -- vanishing hypothesis on `R^1 lim H^{-1}`.
  rcases inverse_limit_zero_cohomology_shortExact_of_vanishing_degree_r1lim
      A hAnegTwo hAnegOne with
    ⟨ι, hι, hshort⟩
  exact isIso_of_shortExact_right_map hι hshort hHnegOne

-- Proof sketch: the Mittag-Leffler criterion from the preceding Chapter 15 development implies
-- the vanishing of `R^1 \!\varprojlim` for each of the three towers, so the main theorem above
-- applies directly.
/-- A sufficient criterion for Lemma 15.87.3: it is enough that the degree `-2`, degree `-1`,
and `H^{-1}` towers are Mittag-Leffler. -/
theorem inverse_limit_zero_cohomology_comparison_isIso_of_isMittagLeffler
    (A : AbCpxSeq)
    (hAnegTwo : IsMittagLeffler (A ⋙ ev (-2)))
    (hAnegOne : IsMittagLeffler (A ⋙ ev (-1)))
    (hHnegOne : IsMittagLeffler (A ⋙ H (-1))) :
    IsIso (limit.post A (H 0)) := by
  -- Route correction: the intended source route still factors through the vanishing theorem
  -- above, but the stable Mittag-Leffler-to-vanishing owner from Chapter `15` is not currently
  -- importable in this repo state.
  -- TODO: once the owner path is stable again, convert these Mittag-Leffler hypotheses to the
  -- three `IsZero (firstDerivedLimit ...)` hypotheses and reuse the previous theorem.
  have hAnegTwo' : IsZero <| firstDerivedLimit (A ⋙ ev (-2)) := by
    sorry
  have hAnegOne' : IsZero <| firstDerivedLimit (A ⋙ ev (-1)) := by
    sorry
  have hHnegOne' : IsZero <| firstDerivedLimit (A ⋙ H (-1)) := by
    sorry
  exact inverse_limit_zero_cohomology_comparison_isIso_of_vanishing_r1lim
    A hAnegTwo' hAnegOne' hHnegOne'

end SequentialInverseSystem

end CategoryTheory
