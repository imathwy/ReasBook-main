import Mathlib
import StacksProject_2024.Chap10.Definition_10_162_1
import StacksProject_2024.Chap15.Definition_15_112_1
import StacksProject_2024.Chap15.Lemma_15_112_2
import StacksProject_2024.Chap15.Lemma_15_112_3
import StacksProject_2024.Chap15.Lemma_15_112_4
import StacksProject_2024.Chap15.Lemma_15_115_2
import StacksProject_2024.Chap15.Definition_15_112_7
import StacksProject_2024.Chap15.Definition_15_116_1
import StacksProject_2024.Chap15.Lemma_15_116_3
import StacksProject_2024.Chap15.Lemma_15_116_4
import StacksProject_2024.Chap15.Lemma_15_116_7

-- Declarations for this item will be appended below by the statement pipeline.

open Ideal IsLocalRing
open IsExtensionOfDiscreteValuationRings

universe u v w x y

section

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [NagataRing B]
variable [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
variable [IsExtensionOfDiscreteValuationRings A B]
variable [IsExtensionOfDiscreteValuationRings B C]
local notation "K" => FractionRing A
variable {L : Type x} {M : Type y}
variable [Field L] [Algebra A L] [Algebra B L] [Algebra (FractionRing A) L] [IsFractionRing B L]
variable [IsScalarTower A B L] [IsScalarTower A (FractionRing A) L]
variable [Field M] [Algebra A M] [Algebra C M] [Algebra (FractionRing A) M] [IsFractionRing C M]
variable [Algebra L M]
variable [IsScalarTower (FractionRing A) L M] [IsScalarTower A C M]
variable [IsScalarTower A (FractionRing A) M]
variable [FiniteDimensional L M] [IsPurelyInseparable L M]
variable {p : ℕ} [Fact p.Prime] [CharP (FractionRing A) p]

/- Domain-style sampling for Lemma 15.116.9:
- primary domain: ramification elimination for purely inseparable degree-`p` extensions of
  fraction fields over towers of discrete valuation rings, organized around the canonical base
  fraction field `K = FractionRing A` in characteristic `p`;
- sampled owner declarations:
  `IsWeakSolutionFor`,
  `WeaklyUnramified`,
  `IsTotallyRamifiedWithRespectTo`,
  `weakSolutionFor_of_weakSolutionFor_comp`;
- best owner abstraction: the source-facing alternatives are still the three branches of the
  lemma, but the separable base-change branch should be phrased through the chapter owner
  `IsWeakSolutionFor A C K M K1` with the canonical owner `K = FractionRing A`, while total
  ramification of the chosen extension remains owned directly by `IsTotallyRamifiedWithRespectTo
  A K1`;
- primitive-vs-derived split: the primitive data in the separable-base-change branch are the
  degree-`p` separable extension `K1 / K`, its total ramification with respect to `A`, and the
  resulting weak-solution property for `A → C`; the integral-closure DVR instances, tensor-product
  fields, and branchwise weakly unramified maps are derived bridge data and should not remain
  primitive witness fields in the public statement.

Source/core/bridge triage:
- `source-facing`: the three alternatives in
  `ramification_elimination_of_purelyInseparable_degree_p`;
- `core/canonical`: `WeaklyUnramified`, `IsWeakSolutionFor`, and
  `IsTotallyRamifiedWithRespectTo`;
- `bridge/view`: the tensor-product fields `L ⊗[K] K1`, `M ⊗[K] K1` and the induced integral
  closures that witness a weak solution branchwise.
-/

-- Proof sketch: let `e` be the ramification index of `C` over `B`. If `e = 1`, transitivity gives
-- the weakly unramified case for `A → C`. Otherwise the purely inseparable degree-`p` hypothesis
-- forces `e = p`; writing a uniformizer of `C` as a `p`th root of `uπ`, either `u` is already a
-- `p`th power in `B`, which gives `C = B[π^(1/p)]`, or after adjoining the totally ramified
-- degree-`p` separable extension furnished by Lemma `15.116.7`, the induced normalized base change
-- is a weak solution for `A → C`.
/-- Helper for Lemma 15.116.9: if the upper step `B ⊆ C` has ramification index `1`, then the
whole tower `A ⊆ C` is weakly unramified once `A ⊆ B` already is. -/
private theorem weaklyUnramified_of_tower_of_ramificationIndex_eq_one
    (hAB : WeaklyUnramified A B) (hBC : ramificationIndex B C = 1) :
    let _ : IsExtensionOfDiscreteValuationRings A C := of_tower A B C
    WeaklyUnramified A C := by
  let _ : IsExtensionOfDiscreteValuationRings A C := of_tower A B C
  -- Multiplicativity of ramification indices reduces the tower to the two given `1`-steps.
  have hAB' : ramificationIndex A B = 1 :=
    (weaklyUnramified_iff_ramificationIndex_eq_one (A := A) (B := B)).1 hAB
  rw [weaklyUnramified_iff_ramificationIndex_eq_one]
  rw [IsExtensionOfDiscreteValuationRings.ramificationIndex_algebra_tower
    (A := A) (B := B) (C := C)]
  simp [hAB', hBC]

/-- Helper for Lemma 15.116.9: a purely inseparable degree-`p` fraction-field extension forces the
top ramification index to be either `1` or `p`. -/
private theorem ramificationIndex_eq_one_or_eq_p_of_purelyInseparable_degree_p
    (hLM : Module.finrank L M = p) :
    ramificationIndex B C = 1 ∨ ramificationIndex B C = p := by
  -- Route correction: the numerical split must first compare the chosen fields `L ⊆ M` with the
  -- canonical fraction rings `FractionRing B ⊆ FractionRing C`; without that transport, the
  -- ramification lemmas from `15.112.2` and `15.112.4` do not apply directly.
  -- TODO: prove the source-faithful numerical split by combining the purely inseparable
  -- `p`-power ramification theorem with the inequality `e * f ≤ [M : L] = p`, after packaging the
  -- transport from the chosen fraction fields `L`, `M` to `FractionRing B`, `FractionRing C`.
  sorry

/-- Helper for Lemma 15.116.9: in the ramified case `ramificationIndex B C = p`, the remaining
source-proof branch either identifies `C` with the radical extension `B[π^(1/p)]` or produces the
degree-`p` totally ramified separable weak solution over `A`. -/
private theorem radical_extension_or_weakSolution_of_ramified_case
    (π : A) (hπ : maximalIdeal A = Ideal.span ({π} : Set A))
    (hAB : WeaklyUnramified A B) (hLM : Module.finrank L M = p)
    (hram : ramificationIndex B C = p) :
    let _ : IsExtensionOfDiscreteValuationRings A C := of_tower A B C
    (∃ x : C, x ^ p = algebraMap A C π ∧ Algebra.adjoin B ({x} : Set C) = ⊤) ∨
      ∃ (K1 : Type (max u v w x y)) (_ : Field K1) (_ : Algebra A K1) (_ : Algebra K K1)
        (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1),
          Algebra.IsSeparable K K1 ∧
            IsTotallyRamifiedWithRespectTo A K1 ∧
            Module.finrank K K1 = p ∧
            IsWeakSolutionFor A C K M K1 := by
  let _ : IsExtensionOfDiscreteValuationRings A C := of_tower A B C
  -- Route correction: the bad-coefficient branch should close through the branchwise weak-solution
  -- API from `15.116.3` and `15.116.4`, rather than through a bespoke normalization argument.
  -- TODO: follow the source route in the ramified branch: choose a uniformizer `πC` of `C`,
  -- write `πC ^ p = u * π`, split by the first non-`p`th-power coefficient of `u`, and then
  -- close the two resulting branches via Lemmas `15.116.7`, `15.116.8`, and `10.162.18`.
  sorry

/-- Lemma 15.116.9: let `A ⊆ B ⊆ C` be extensions of discrete valuation rings with
`K = FractionRing A` and fraction fields `L` of `B` and `M` of `C`, let `π ∈ A` be a uniformizer,
assume `B` is Nagata, `K` has characteristic `p` with `p` prime, `A ⊆ B` is weakly unramified,
and `M / L` is purely inseparable of degree `p`. Then either `A → C` is
weakly unramified, or `C` is generated over `B` by a `p`th root of `π`, or there exists a
degree-`p` separable extension `K1 / K` totally ramified with respect to `A` such that `K1 / K`
is a weak solution for `A → C`. -/
theorem ramification_elimination_of_purelyInseparable_degree_p
    (π : A) (hπ : maximalIdeal A = Ideal.span ({π} : Set A))
    (hAB : WeaklyUnramified A B) (hLM : Module.finrank L M = p) :
    let _ : IsExtensionOfDiscreteValuationRings A C := of_tower A B C
    WeaklyUnramified A C ∨
      (∃ x : C, x ^ p = algebraMap A C π ∧ Algebra.adjoin B ({x} : Set C) = ⊤) ∨
      ∃ (K1 : Type (max u v w x y)) (_ : Field K1) (_ : Algebra A K1) (_ : Algebra K K1)
        (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1),
          Algebra.IsSeparable K K1 ∧
            IsTotallyRamifiedWithRespectTo A K1 ∧
            Module.finrank K K1 = p ∧
            IsWeakSolutionFor A C K M K1 := by
  let _ : IsExtensionOfDiscreteValuationRings A C := of_tower A B C
  -- Split first by the numerical ramification dichotomy coming from the degree-`p`
  -- purely inseparable extension of fraction fields.
  rcases
      ramificationIndex_eq_one_or_eq_p_of_purelyInseparable_degree_p
        (B := B) (C := C) (L := L) (M := M) (p := p) hLM
    with hBC | hBC
  · -- When the top step is already weakly unramified, multiplicativity finishes the tower.
    exact Or.inl <|
      weaklyUnramified_of_tower_of_ramificationIndex_eq_one
        (A := A) (B := B) (C := C) hAB hBC
  · -- The remaining source-faithful work is the ramified branch `e = p`, which splits further
    -- into the radical-extension and weak-solution alternatives.
    exact Or.inr <|
      radical_extension_or_weakSolution_of_ramified_case
        (A := A) (B := B) (C := C) (L := L) (M := M) (p := p)
        π hπ hAB hLM hBC

end
