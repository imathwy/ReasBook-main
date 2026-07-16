import Mathlib.Algebra.Homology.QuasiIso
import stacks_proof.stacks_project.Chap15.Remark_15_96_5
import stacks_proof.stacks_project.Chap15.«15_96_5_2»
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CochainComplex
open ModFSquared.Nat

universe u

section

variable {A : Type u} [CommRing A]

/- Domain-style sampling:
- primary domain: the Berthelot-Ogus reduction complex from Remark `15.96.5` and its comparison
  with the canonical Bockstein cohomology complex;
- sampled owner declarations:
  `BerthelotOgusEtaReduction.Nat.toHomology`,
  `bockstein_factorization_naturality`,
  `modfCohomologyBocksteinComplex`,
  `QuasiIso`;
- best owner abstraction:
  `source-facing`: the scalar-restricted bounded-below bridge reduction complex
    `CochainComplex.reduceModIdealA (principalIdeal f) (η[f] M)`;
  `core/canonical`: the target complex `modfCohomologyBocksteinComplex f M hM`;
  `bridge/view`: the source-owned comparison map
    `BerthelotOgusEtaReduction.Nat.toModfCohomologyBocksteinComplex` and its quasi-isomorphism;
- primitive data vs derived API: the primitive source data are the owner declarations from Remark
  `15.96.5`. The target Bockstein complex is derived, so this file should state only the canonical
  comparison map to that target. -/

namespace BerthelotOgusEtaReduction
namespace Nat

-- Proof sketch: use the canonical reduction complex from Remark `15.96.5`. The quotient by its
-- acyclic boundary subcomplex identifies degreewise with the homology of `K^\bullet / fK^\bullet`,
-- and the induced differential on those quotients is the canonical Bockstein differential from
-- `15.96.5.2`; equivalently, this is the bounded-below source-facing specialization of the
-- factorization square from `15.96.5.1`. Hence the quotient map gives a quasi-isomorphism from
-- the canonical reduction complex to `modfCohomologyBocksteinComplex f M hM`.
/-- Helper for Lemma 15.96.6: the source proof first produces a transported lower morphism on
bounded-below homology for which the comparison map `toHomology` satisfies the owner naturality
square from `15.96.5.1`. The remaining task is to identify that transported morphism with the
public bounded-below Bockstein map from `15.96.5.2`. -/
private theorem exists_toHomology_comm_transported_owner_bockstein
    (f : A) (M : NatModuleCochainComplex A)
    (hM : IsTermwiseFTorsionFree f M) (i : ℕ) :
    ∃ β :
        (reduceModIdealA (principalIdeal f) M).homology i ⟶
          (reduceModIdealA (principalIdeal f) M).homology (i + 1),
      CommSq
        (toHomology f M i)
        ((reduceModIdealA (principalIdeal f) (η[f] M)).d i (i + 1))
        β
        (toHomology f M (i + 1)) := by
  -- Route correction: the source proof first compares `toHomology` with the owner connecting
  -- morphism on `M.extend embeddingUpNat`, and only afterwards identifies that lower map with the
  -- bounded-below Bockstein differential. This file cannot yet name that transported owner map
  -- directly because `15.96.5.2` still keeps the transport API opaque.
  -- TODO: specialize `bockstein_factorization_naturality` to the owner short exact sequence from
  -- `Remark 15.96.5`, then rewrite the vertical arrows to `BerthelotOgusEtaReduction.Nat.toHomology`
  -- using the degreewise reduction and extension identifications exported from `15.96.5.2`.
  sorry

/-- The canonical quotient maps
`(η_f M)^i / f(η_f M)^i ⟶ H^i(M^\bullet / fM^\bullet)` intertwine the differential on the
reduced Berthelot-Ogus complex with the Berthelot-Ogus Bockstein differential. -/
theorem toHomology_comm_bockstein
    (f : A) (M : NatModuleCochainComplex A)
    (hM : IsTermwiseFTorsionFree f M) (i : ℕ) :
    CommSq
      (toHomology f M i)
      ((reduceModIdealA (principalIdeal f) (η[f] M)).d i (i + 1))
      (bockstein f M i hM)
      (toHomology f M (i + 1)) := by
  obtain ⟨β, htransport⟩ :=
    exists_toHomology_comm_transported_owner_bockstein f M hM i
  -- Route correction: the transported owner square is the correct source-proof skeleton. The
  -- remaining step is only to identify the transported lower morphism `β` with the public
  -- bounded-below differential `ModFSquared.Nat.bockstein`.
  -- TODO: prove `β = bockstein f M i hM` from the concrete transport description that should be
  -- exported by `15.96.5.2`, then close this goal by `simpa [that_equality] using htransport`.
  sorry

/-- Helper for Lemma 15.96.6: the degreewise quotient maps respect the differentials of the
canonical Bockstein complex. -/
private theorem toHomology_comm_target_d
    (f : A) (M : NatModuleCochainComplex A)
    (hM : IsTermwiseFTorsionFree f M) {i j : ℕ} (hij : (ComplexShape.up ℕ).Rel i j) :
    toHomology f M i ≫ (modfCohomologyBocksteinComplex f M hM).d i j =
      (reduceModIdealA (principalIdeal f) (η[f] M)).d i j ≫ toHomology f M j := by
  -- Reduce to the adjacent-degree case and rewrite the target differential as the Bockstein map.
  rcases hij with rfl
  simpa only [modfCohomologyBocksteinComplex_d] using
    (toHomology_comm_bockstein f M hM i).w

/-- The canonical comparison morphism from the Berthelot-Ogus reduction complex to the Bockstein
cohomology complex. -/
def toModfCohomologyBocksteinComplex
    (f : A) (M : NatModuleCochainComplex A)
    (hM : IsTermwiseFTorsionFree f M) :
    reduceModIdealA (principalIdeal f) (η[f] M) ⟶ modfCohomologyBocksteinComplex f M hM where
  f i := toHomology f M i
  comm' i j hij := toHomology_comm_target_d f M hM (i := i) (j := j) hij

/-- Helper for Lemma 15.96.6: in a short complex of `A`-modules, a homology class vanishes
exactly when its cycle representative is a boundary. -/
private theorem shortComplex_homologyπ_eq_zero_iff_exists_boundary
    (S : ShortComplex (ModuleCat A)) [S.HasHomology] (q : S.cycles) :
    S.homologyπ.hom q = 0 ↔
      ∃ b : S.X₁, S.moduleCatToCycles b = S.moduleCatCyclesIso.hom q := by
  have hcomm :
      S.homologyπ ≫ S.moduleCatHomologyIso.hom =
        S.moduleCatCyclesIso.hom ≫ S.moduleCatLeftHomologyData.π := by
    -- Compare abstract homology with the concrete quotient of cycles by boundaries.
    simpa using S.π_moduleCatCyclesIso_hom
  constructor
  · intro hq
    -- Evaluate the comparison square at `q` to move vanishing into the concrete quotient.
    have hπ := congrArg (fun f : S.cycles ⟶ S.moduleCatLeftHomologyData.H ↦ f.hom q) hcomm
    change
      S.moduleCatHomologyIso.hom.hom (S.homologyπ.hom q) =
        S.moduleCatLeftHomologyData.π.hom (S.moduleCatCyclesIso.hom q)
      at hπ
    rw [hq, LinearMap.map_zero] at hπ
    have hπ' : S.moduleCatLeftHomologyData.π.hom (S.moduleCatCyclesIso.hom q) = 0 := hπ.symm
    -- Zero in the quotient means the cycle class lies in the boundary range.
    have hmem : S.moduleCatCyclesIso.hom q ∈ LinearMap.range S.moduleCatToCycles := by
      simpa using (Submodule.Quotient.mk_eq_zero (LinearMap.range S.moduleCatToCycles)).1 hπ'
    exact LinearMap.mem_range.mp hmem
  · rintro ⟨b, hb⟩
    -- A concrete boundary witness is zero in the quotient, hence also zero in homology.
    have hπ : S.moduleCatLeftHomologyData.π.hom (S.moduleCatCyclesIso.hom q) = 0 := by
      exact (Submodule.Quotient.mk_eq_zero (LinearMap.range S.moduleCatToCycles)).2
        (LinearMap.mem_range.mpr ⟨b, hb⟩)
    have hzero := congrArg (fun f : S.cycles ⟶ S.moduleCatLeftHomologyData.H ↦ f.hom q) hcomm
    change
      S.moduleCatHomologyIso.hom.hom (S.homologyπ.hom q) =
        S.moduleCatLeftHomologyData.π.hom (S.moduleCatCyclesIso.hom q)
      at hzero
    rw [hπ] at hzero
    have hinj : Function.Injective S.moduleCatHomologyIso.hom.hom :=
      (ModuleCat.mono_iff_injective S.moduleCatHomologyIso.hom).1 inferInstance
    have h0 : 0 = S.moduleCatHomologyIso.hom.hom 0 := by
      simpa using (S.moduleCatHomologyIso.hom.hom.map_zero).symm
    exact hinj (hzero.trans h0)

/-- Helper for Lemma 15.96.6: in degree `i` of a nonnegative cochain complex, a homology class
vanishes exactly when its cycle representative comes from the previous differential. -/
private theorem homology_class_eq_zero_iff_exists_boundary
    (K : NatModuleCochainComplex A) (i : ℕ) (q : K.cycles i) :
    (K.homologyπ i).hom q = 0 ↔
      ∃ b : (K.sc i).X₁, (K.sc i).moduleCatToCycles b = (K.sc i).moduleCatCyclesIso.hom q := by
  -- Rewrite degree-`i` homology through the canonical short complex `K.sc i`.
  simpa [HomologicalComplex.homologyπ, ShortComplex.homologyπ] using
    (shortComplex_homologyπ_eq_zero_iff_exists_boundary (K.sc i) q)

/-- Helper for Lemma 15.96.6: once the comparison square with the Bockstein differential is in
place, the induced map on degree-`i` homology is an isomorphism. -/
private theorem homologyMap_toModfCohomologyBocksteinComplex_isIso
    (f : A) (M : NatModuleCochainComplex A)
    (hM : IsTermwiseFTorsionFree f M) (i : ℕ) :
    IsIso (HomologicalComplex.homologyMap (toModfCohomologyBocksteinComplex f M hM) i) := by
  -- Route correction: the cycle/boundary quotient argument is already reduced to this degreewise
  -- statement. The only missing ingredient is the transported commutative square from
  -- `toHomology_comm_bockstein`, after which `homology_class_eq_zero_iff_exists_boundary`
  -- supplies the injective and surjective boundary bookkeeping.
  -- TODO: use `toHomology_comm_bockstein` to move boundaries across the comparison map, then
  -- prove bijectivity on homology classes via the source-faithful quotient-of-cycles argument.
  sorry

/-- Lemma 15.96.6: let `A` be a ring, let `f ∈ A`, and let `K^\bullet` be a cochain complex of
`A`-modules on which multiplication by `f` is injective in every degree. Then
the scalar-restricted `A`-linear view of the canonical Berthelot-Ogus reduction complex
`η_f K^\bullet / f(η_f K^\bullet)` from Remark `15.96.5` is quasi-isomorphic to the canonical
Bockstein cohomology complex `H^\bullet(K^\bullet / fK^\bullet)` of `15.96.5.2`, via the
canonical comparison map. -/
@[stacks 0F7T]
theorem toModfCohomologyBocksteinComplex_quasiIso
    (f : A) (M : NatModuleCochainComplex A)
    (hM : IsTermwiseFTorsionFree f M) :
    QuasiIso (toModfCohomologyBocksteinComplex f M hM) := by
  -- Package the degreewise homology isomorphisms using the standard quasi-isomorphism criterion.
  rw [quasiIso_iff]
  intro i
  refine QuasiIsoAt.mk ?_
  rw [CategoryTheory.ShortComplex.quasiIso_iff]
  let φ :=
    ((HomologicalComplex.shortComplexFunctor (ModuleCat A) (ComplexShape.up ℕ) i).map
      (toModfCohomologyBocksteinComplex f M hM))
  letI :
      IsIso (CategoryTheory.ShortComplex.homologyMap φ) := by
    -- The short-complex homology map is definitionally the degree-`i` homology map of the
    -- original cochain map.
    simpa [φ, HomologicalComplex.homologyMap] using
      homologyMap_toModfCohomologyBocksteinComplex_isIso f M hM i
  infer_instance

end Nat
end BerthelotOgusEtaReduction

end
