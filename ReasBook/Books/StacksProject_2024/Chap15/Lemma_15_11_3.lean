import Mathlib
import StacksProject_2024.Chap12.Definition_12_31_2
import StacksProject_2024.Chap15.Lemma_15_11_2
import StacksProject_2024.Chap15.Lemma_15_11_12

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SequentialInverseSystem
open CommRingCat

universe u

section

variable (F : SequentialInverseSystem CommRingCat.{u})

/- Domain-style sampling:
- primary domain: henselian pairs on inverse limits of commutative rings;
- sampled owner declarations of the same kind:
  `SequentialInverseSystem.stepMap`,
  `HenselianRing`,
  `henselianRing_of_isLocallyNilpotent`,
  `inverseSystem_limit_henselianRing`,
  `IsAdicComplete.henselianRing`;
- best owner abstraction: the sequential source-facing owner is `SequentialInverseSystem`, with
  `SequentialInverseSystem.stepMap` as the canonical stage-to-stage transition API; the core owner
  for the conclusion is `HenselianRing`, while the chapter-level inverse-limit owner is
  `inverseSystem_limit_henselianRing`; the locally nilpotent-kernel criterion from
  `henselianRing_of_isLocallyNilpotent` supplies the stagewise henselian ideals used in that
  inverse-limit owner;
- primitive data: the inverse system `F`, a stage `n`, and the stepwise transition hypotheses on
  `F.stepMap r`;
- derived API: henselianity of the kernel ideal of the projection `limit F → F.obj (op n)`.

Source/core/bridge triage:
- `source-facing`: the specialization to the projection-kernel ideal at a fixed stage `n`;
- `core/canonical`: `HenselianRing`;
- `bridge/view`: the sequential transition API `SequentialInverseSystem.stepMap` and the chapter
  owner `inverseSystem_limit_henselianRing`, fed by the stagewise locally nilpotent-kernel
  instances from `henselianRing_of_isLocallyNilpotent`.
-/

-- Proof sketch: fix `n`. Starting from the stepwise hypotheses on `A_{r + 1} → A_r`, derive the
-- corresponding surjectivity and locally nilpotent-kernel facts for the longer transition maps
-- `A_m → A_n` with `n ≤ m`. Repeated applications of `henselianRing_of_isLocallyNilpotent` then
-- make the stagewise kernel ideals henselian. Apply the inverse-limit owner
-- `inverseSystem_limit_henselianRing` to that compatible inverse system of ideals to obtain
-- henselianity of the limit ideal, which is the kernel of the projection `limit F → A_n`.
/-- Lemma 15.11.3: if `F : SequentialInverseSystem CommRingCat` is an inverse system of rings
whose stepwise transition maps `A_{r + 1} → A_r` are surjective and have locally nilpotent
kernels, then for each `n` the pair consisting of the inverse limit `limit F` and the kernel of
the projection `limit F → F.obj (op n)` is henselian. -/
instance henselianRing_limitProjection_ker_of_surjective_of_isLocallyNilpotent
    (n : ℕ)
    (h_surj : ∀ r : ℕ, Function.Surjective (F.stepMap r).hom)
    (h_locnil : ∀ r : ℕ, RingHom.ker (F.stepMap r).hom ≤ nilradical _) :
    HenselianRing ((limit F : CommRingCat.{u}) : Type u)
      (RingHom.ker (limit.π F (Opposite.op n)).hom) :=
    sorry

end
