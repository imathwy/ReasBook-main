import StacksProject_2024.Chap15.Lemma_15_96_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open HomologicalComplex
open scoped nonZeroDivisors

noncomputable section

universe u

section

variable {A : Type u} [CommRing A]

/-
Domain-style sampling:
- primary domain: Berthelot-Ogus `η_f` on cochain complexes of `A`-modules and preservation of
  quasi-isomorphisms;
- sampled chapter/project owner declarations in this domain:
  `BerthelotOgusInt.complex`,
  `BerthelotOgusInt.map`,
  `NatModuleCochainComplex`,
  `etaFMap`;
- best owner abstraction:
  `source-facing`: Lemma `15.96.3` for arbitrary `ℤ`-indexed complexes of `f`-torsion-free
    `A`-modules;
  `core/canonical`: the Berthelot-Ogus owner layer `BerthelotOgusInt.complex` and
    `BerthelotOgusInt.map` on `ModuleComplex A`;
  `bridge/view`: the bounded-below transport `etaFMap` on `NatModuleCochainComplex A`;
- primitive data vs derived API: the primitive data are only the complexes, the morphism, the
  nonzerodivisor hypothesis, and the termwise `f`-torsion-free hypotheses. The bounded-below
  `ℕ`-indexed statement is derived by transporting the owner morphism across
  `etaFExtendRestrictionIso`, so it should remain a bridge corollary rather than the main owner.
-/

namespace BerthelotOgusInt

-- Proof sketch: identify the homology of `η[f] K` and `η[f] L` with the quotients
-- `H^i(K) / H^i(K)[f]` and `H^i(L) / H^i(L)[f]` by the Berthelot-Ogus comparison, observe that
-- the induced map on these quotients is an isomorphism because `φ` is a quasi-isomorphism, and
-- use naturality of the comparison maps to conclude that `map f φ` induces isomorphisms on every
-- cohomology group.
/-- Lemma 15.96.3, owner-level form: if `f` is a nonzerodivisor in `A`,
`φ : K^\bullet ⟶ L^\bullet` is a quasi-isomorphism, and both complexes are termwise
`f`-torsion free, then the induced map `η_f K^\bullet ⟶ η_f L^\bullet` is again a
quasi-isomorphism. -/
theorem map_quasiIso
    (f : A) {K L : ModuleComplex A} (φ : K ⟶ L)
    (hf : f ∈ nonZeroDivisors A) (hφ : QuasiIso φ)
    (hK : IsTermwiseFTorsionFree f K) (hL : IsTermwiseFTorsionFree f L) :
    QuasiIso (map f φ) := by
  sorry

end BerthelotOgusInt

-- Proof sketch: transport the owner-level quasi-isomorphism theorem
-- `BerthelotOgusInt.map_quasiIso` from `M.extend ComplexShape.embeddingUpNat` and
-- `N.extend ComplexShape.embeddingUpNat` across the canonical restriction isomorphisms
-- `etaFExtendRestrictionIso`.
/-- Lemma 15.96.3, bounded-below bridge/view: if `f` is a nonzerodivisor in `A`,
`φ : M^\bullet ⟶ N^\bullet` is a quasi-isomorphism, and both nonnegative complexes are termwise
`f`-torsion free, then the induced map `η_f M^\bullet ⟶ η_f N^\bullet` is again a
quasi-isomorphism. -/
theorem etaFMap_quasiIso
    (f : A) {M N : NatModuleCochainComplex A} (φ : M ⟶ N)
    (hf : f ∈ nonZeroDivisors A) (hφ : QuasiIso φ)
    (hM : IsTermwiseFTorsionFree f M) (hN : IsTermwiseFTorsionFree f N) :
    QuasiIso (etaFMap f φ) := by
  sorry

end
