import Mathlib
import stacks_project.Chap10.Lemma_10_69_2
import stacks_project.Chap15.Definition_15_30_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped TensorProduct
open Algebra.TensorProduct

namespace RingTheory.Sequence

section

variable {A B A' : Type u} [CommRing A] [CommRing B] [CommRing A']
variable [Algebra A B] [Algebra A A']
variable {r : ℕ}

local notation "B'" => A' ⊗[A] B

/- Domain triage:
* primary domain: quasi-regular and `H₁`-regular finite sequences under tensor base change in
  commutative algebra;
* sampled owner declarations: `IsQuasiRegularSequence` from Chapter 10, `IsH1RegularSequence`
  from Definition `15.30.1`, `IsQuasiRegular.of_flat` from Lemma `10.69.3`, and
  `koszulH1BaseChange`/`koszulH1_baseChange_surjective_of_flat_quotient` from Lemma `15.31.3`;
* best owner abstraction: the ring-valued quasi-regular statement should use the ring-level owner
  `IsQuasiRegularSequence`, while the `H₁`-regular statement should stay on the finite-family
  owner `IsH1RegularSequence`;
* primitive data vs derived API: the only primitive input is the finite family `f`; the tensor
  base-changed family is a derived view, so the public surface should reuse the existing owner
  predicates rather than restating the regular-module case through the more general
  module-valued predicate.
-/

-- Proof sketch: let `J = Ideal.span (Set.range f)`. Quasi-regularity identifies each graded piece
-- `J^n / J^(n + 1)` with a direct sum of copies of `B ⧸ J`, hence these graded pieces are flat
-- over `A`. By the flatness criterion for successive quotients, the quotients `B ⧸ J^n` remain
-- flat over `A`. After base change, the powers of the extended ideal are the tensor products of
-- the powers of `J`, so the associated graded criterion for quasi-regularity carries over to the
-- image sequence in `A' ⊗[A] B`.
/-- Lemma 15.31.4 (1): if `B ⧸ Ideal.span (Set.range f)` is flat over `A` and the finite family
`f` is quasi-regular in `B`, then its image in `A' ⊗[A] B` is quasi-regular. -/
theorem isQuasiRegularSequence_baseChange_of_flat_quotient (f : Fin r → B)
    [Module.Flat A (B ⧸ Ideal.span (Set.range f))]
    (hqr : IsQuasiRegularSequence (List.ofFn f)) :
    IsQuasiRegularSequence
      (List.ofFn fun i : Fin r ↦ (includeRight (f i) : B')) := sorry

-- Proof sketch: apply Lemma `15.31.3` to obtain a surjective comparison map from the base change
-- of `H_1(K_\bullet(B, f))` onto `H_1(K_\bullet(A' ⊗[A] B, f'))`. If `f` is `H_1`-regular, then
-- the source is zero, so surjectivity forces the target first Koszul homology to vanish as well.
/-- Lemma 15.31.4 (2): if `B ⧸ Ideal.span (Set.range f)` is flat over `A` and the finite family
`f` is `H_1`-regular in `B`, then its image in `A' ⊗[A] B` is `H_1`-regular. -/
theorem isH1RegularSequence_baseChange_of_flat_quotient (f : Fin r → B)
    [Module.Flat A (B ⧸ Ideal.span (Set.range f))]
    (hreg : IsH1RegularSequence f) :
    IsH1RegularSequence
      (fun i ↦ includeRight (f i) : Fin r → B') := sorry

end

end RingTheory.Sequence
