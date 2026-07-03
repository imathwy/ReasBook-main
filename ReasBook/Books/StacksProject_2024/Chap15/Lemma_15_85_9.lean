import Mathlib
import StacksProject_2024.Chap15.Lemma_15_85_5
import StacksProject_2024.Chap15.Lemma_15_85_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory.TStructure

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)

/- Domain-style sampling for Lemma 15.85.9:
- primary domain: two-term objects in the derived category of `R`-modules and the owner predicate
  `twoTermExtOneAnnihilatedByIdeal`;
- sampled owner declarations:
  `twoTermExtOneAnnihilatedByIdeal`,
  `smul_id_eq_zero_of_h0_iso_of_hneg1_epi`,
  `DerivedCategory.IsGE`,
  `DerivedCategory.IsLE`;
- best owner abstraction: this source-facing transfer lemma should stay phrased on the owner
  predicate `twoTermExtOneAnnihilatedByIdeal`, while the `H⁻¹` surjectivity assumption is best
  expressed by the canonical categorical hypothesis `Epi ((H^(-1)).map α)` rather than by the
  underlying-function view;
- primitive data vs. derived API: the primitive inputs are `K`, `K'`, `α`, the cohomological
  bounds, and the owner annihilation predicate. Surjectivity of `((H^(-1)).map α).hom` is a
  derived concrete view of the canonical `Epi` owner hypothesis. -/

-- Proof sketch: let `M = ker(H^{-1}(α))`. The hypotheses give a distinguished triangle
-- `M[1] ⟶ K ⟶ K' ⟶ M[2]`. Applying `Hom_{D(R)}(-, N[1])` yields an exact sequence in which the
-- term coming from `M[1]` vanishes because `Ext^{-1}_R(M, N) = 0`, so
-- `Ext^1_R(K', N) ↪ Ext^1_R(K, N)`. Hence any element of `I` annihilating `Ext^1_R(K, N)` also
-- annihilates `Ext^1_R(K', N)`.
/-- Lemma 15.85.9: let `I` be an ideal of `R`, and let `α : K ⟶ K'` in `D(R)` induce an
isomorphism on `H^0` and a surjection on `H^{-1}`. If `K` has cohomology only in degrees `-1`
and `0`, and if `K'` does as well, then the Ext-annihilation condition from Lemma `15.85.5 (1)`
for `K` implies the same condition for `K'`. -/
theorem twoTermExtOneAnnihilatedByIdeal_of_h0_iso_of_hneg1_epi
    (I : Ideal R)
    {K K' : DMod}
    (α : K ⟶ K')
    (hKGE : K.IsGE (-1)) (hKLE : K.IsLE 0)
    (hK'GE : K'.IsGE (-1)) (hK'LE : K'.IsLE 0)
    (hα0 : IsIso ((H^0).map α))
    (hαneg1 : Epi ((H^(-1)).map α))
    (hI : twoTermExtOneAnnihilatedByIdeal K I) :
    twoTermExtOneAnnihilatedByIdeal K' I := sorry

end

end CategoryTheory
