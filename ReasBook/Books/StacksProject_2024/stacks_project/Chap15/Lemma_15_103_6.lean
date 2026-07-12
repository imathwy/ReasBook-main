import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Linear
import Mathlib.Algebra.Homology.ShortComplex.Linear
import Mathlib.Algebra.Module.LocalizedModule.Away
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.RingTheory.Localization.Away.Basic

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Pretriangulated
open DerivedCategory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)

/- Domain-style sampling:
- primary domain: distinguished triangles in `D(R)`, their homology long exact sequences, and
  localization of homology modules away from a single element;
- sampled owner declarations:
  `Triangle.mk`,
  `distTriang`,
  `DerivedCategory.homologyFunctor`,
  `DerivedCategory.IsGE`,
  `DerivedCategory.isGE_iff`,
  `LocalizedModule.Away`,
  `Localization.Away`;
- best owner abstraction: the cone bound and conclusion should use the canonical t-structure owner
  `IsGE`, while the distinguished-triangle relation remains
  `Triangle.mk (f • 𝟙 M) g δ ∈ distTriang DMod`; homology and localization use the canonical
  owners `H` and `LocalizedModule.Away`;
- primitive data: the comparison maps `g : M ⟶ C` and `δ : C ⟶ M⟦1⟧` together with the
  distinguished-triangle proof for `Triangle.mk (f • 𝟙 M) g δ`, the localized negative homology
  vanishing of `M`, and the lower bound `C.IsGE (-1)`;
- derived API: the canonical conclusion `M.IsGE 0`, with the textbook negative-homology
  vanishing statement retained only as a thin bridge via `DerivedCategory.isGE_iff`.

Source/core/bridge triage:
- `source-facing`: the vanishing criterion for the cone of multiplication by `f`;
- `core/canonical`: `Triangle`, `distTriang`, `DerivedCategory.IsGE`,
  `DerivedCategory.isGE_iff`, `DerivedCategory.homologyFunctor`, and `LocalizedModule.Away`;
- `bridge/view`: the explicit cohomology-vanishing formulation from `DerivedCategory.isGE_iff`,
  together with the direct categorical packaging
  `ModuleCat.of (Localization.Away f) (LocalizedModule.Away f ((H i).obj M))` of localized
  homology modules used here and in the immediate downstream local criterion
  `Lemma_15_127_4`. -/

section

variable {M C : DerivedCategory (ModuleCat R)} {f : R} {g : M ⟶ C} {δ : C ⟶ M⟦(1 : ℤ)⟧}

/-- Helper for Lemma 15.103.6: if the cone term is concentrated in degrees `≥ -1`, then for each
negative degree `i` the induced map on `H^i` from multiplication by `f` is injective. -/
lemma mono_homology_map_smul_of_cone_isGE_neg_one
    (hT : Triangle.mk (f • 𝟙 M) g δ ∈ distTriang DMod)
    (hC : C.IsGE (-1)) (i : ℤ) (hi : i < 0) :
    Mono ((H i).map (f • 𝟙 M)) := by
  let T : Triangle DMod := Triangle.mk (f • 𝟙 M) g δ
  have hδ_zero : HomologySequence.δ T (i - 1) i (by simp) = 0 := by
    -- The connecting morphism starts in `H^(i - 1)(C)`, which vanishes because `i - 1 < -1`.
    exact
      (DerivedCategory.isZero_of_isGE C (-1) (i - 1) (by
        have hshift : i - 1 < -1 := by
          simpa using sub_lt_sub_right hi 1
        exact hshift)).eq_of_src _ _
  -- Exactness of the long exact sequence upgrades vanishing of the connecting map to monicity.
  exact (HomologySequence.mono_homologyMap_mor₁_iff T hT (i - 1) i (by omega)).2 hδ_zero

/-- Helper for Lemma 15.103.6: the degree-`i` derived homology functor sends scalar
multiplication by `f` to scalar multiplication by `f` on homology. -/
lemma homology_functor_map_smul_id (i : ℤ) (M : DMod) :
    (H i).map (f • 𝟙 M) = f • 𝟙 ((H i).obj M) := by
  let K : CochainComplex (ModuleCat R) ℤ := DerivedCategory.Q.objPreimage M
  let e : DerivedCategory.Q.obj K ≅ M := DerivedCategory.Q.objObjPreimageIso M
  have hcochain :
      HomologicalComplex.homologyMap (f • 𝟙 K) i = f • 𝟙 (K.homology i) := by
    -- On a concrete cochain complex, `H^i` is computed by a short complex, where scalar
    -- multiplication is already known to commute with homology.
    change
      ShortComplex.homologyMap
          ((HomologicalComplex.shortComplexFunctor (ModuleCat R) (ComplexShape.up ℤ) i).map
            (f • 𝟙 K)) =
        f • 𝟙 (K.homology i)
    have hshort :
        ((HomologicalComplex.shortComplexFunctor (ModuleCat R) (ComplexShape.up ℤ) i).map
          (f • 𝟙 K)) =
          f • 𝟙
            (((HomologicalComplex.shortComplexFunctor (ModuleCat R) (ComplexShape.up ℤ) i).obj K)) := by
      ext <;> rfl
    have hshort_homology :
        ShortComplex.homologyMap
            (f • 𝟙
              (((HomologicalComplex.shortComplexFunctor (ModuleCat R) (ComplexShape.up ℤ) i).obj
                K))) =
          f • 𝟙
            ((((HomologicalComplex.shortComplexFunctor (ModuleCat R) (ComplexShape.up ℤ) i).obj
              K)).homology) := by
      rw [ShortComplex.homologyMap_smul, ShortComplex.homologyMap_id]
    rw [hshort]
    simpa using hshort_homology
  have hpreimage :
      (H i).map (DerivedCategory.Q.map (f • 𝟙 K)) =
        f • 𝟙 ((H i).obj (DerivedCategory.Q.obj K)) := by
    have hα :
        (H i).map (DerivedCategory.Q.map (f • 𝟙 K)) ≫
            (DerivedCategory.homologyFunctorFactors (ModuleCat R) i).hom.app K =
          (DerivedCategory.homologyFunctorFactors (ModuleCat R) i).hom.app K ≫
            HomologicalComplex.homologyMap (f • 𝟙 K) i := by
      simpa using
        (DerivedCategory.homologyFunctorFactors_hom_naturality
          (C := ModuleCat R) (f := (f • 𝟙 K)) (n := i))
    apply
      (cancel_epi ((DerivedCategory.homologyFunctorFactors (ModuleCat R) i).hom.app K)).1
    calc
      (H i).map (DerivedCategory.Q.map (f • 𝟙 K)) ≫
          (DerivedCategory.homologyFunctorFactors (ModuleCat R) i).hom.app K
          = (DerivedCategory.homologyFunctorFactors (ModuleCat R) i).hom.app K ≫
              HomologicalComplex.homologyMap (f • 𝟙 K) i := hα
      _ = (DerivedCategory.homologyFunctorFactors (ModuleCat R) i).hom.app K ≫
            (f • 𝟙 (K.homology i)) := by rw [hcochain]
      _ = (f • 𝟙 ((H i).obj (DerivedCategory.Q.obj K))) ≫
            (DerivedCategory.homologyFunctorFactors (ModuleCat R) i).hom.app K := by
            simp [Linear.comp_smul, Linear.smul_comp]
  have hcomm :
      (f • 𝟙 M) ≫ e.inv = e.inv ≫ DerivedCategory.Q.map (f • 𝟙 K) := by
    -- The preimage isomorphism transports the scalar endomorphism back to the quotient model.
    calc
      (f • 𝟙 M) ≫ e.inv = f • e.inv := by simp [Linear.smul_comp]
      _ = e.inv ≫ (f • 𝟙 (DerivedCategory.Q.obj K)) := by simp [Linear.comp_smul]
      _ = e.inv ≫ DerivedCategory.Q.map (f • 𝟙 K) := by rw [Functor.map_smul, Functor.map_id]
  apply (cancel_mono ((H i).mapIso e).inv).1
  calc
    (H i).map (f • 𝟙 M) ≫ ((H i).mapIso e).inv
        = (H i).map ((f • 𝟙 M) ≫ e.inv) := by
            simpa using (Functor.map_comp (H i) (f • 𝟙 M) e.inv).symm
    _ = (H i).map (e.inv ≫ DerivedCategory.Q.map (f • 𝟙 K)) := by rw [hcomm]
    _ = ((H i).mapIso e).inv ≫ (H i).map (DerivedCategory.Q.map (f • 𝟙 K)) := by
            simpa using (Functor.map_comp (H i) e.inv (DerivedCategory.Q.map (f • 𝟙 K)))
    _ = ((H i).mapIso e).inv ≫ (f • 𝟙 ((H i).obj (DerivedCategory.Q.obj K))) := by rw [hpreimage]
    _ = (f • 𝟙 ((H i).obj M)) ≫ ((H i).mapIso e).inv := by
            simp [Linear.comp_smul, Linear.smul_comp]

/-- Helper for Lemma 15.103.6: if the away-localization of a module object is zero, then every
element is killed by a power of `f`. -/
lemma exists_pow_smul_eq_zero_of_localizedAway_isZero
    (N : ModuleCat R) (x : N)
    (hN :
      IsZero (ModuleCat.of (Localization.Away f) (LocalizedModule.Away f N))) :
    ∃ n : ℕ, (f ^ n : R) • x = 0 := by
  let hsub : Subsingleton (LocalizedModule.Away f N) := by
    simpa using ModuleCat.subsingleton_of_isZero hN
  -- Vanishing of the localization means exactly that some denominator from the powers of `f`
  -- annihilates `x`.
  rcases (LocalizedModule.subsingleton_iff (S := Submonoid.powers f) (M := N)).mp hsub x with
    ⟨s, hs, hsx⟩
  rcases hs with ⟨n, rfl⟩
  exact ⟨n, hsx⟩

/-- Helper for Lemma 15.103.6: if a nonzero module element is killed by a power of `f`, then some
nonzero module element is killed by `f` itself. -/
lemma exists_nonzero_smul_eq_zero_of_exists_pow_smul_eq_zero
    {N : Type*} [AddCommGroup N] [Module R N] {x : N}
    (hx : x ≠ 0) (hpow : ∃ n : ℕ, (f ^ n : R) • x = 0) :
    ∃ y : N, y ≠ 0 ∧ f • y = 0 := by
  rcases hpow with ⟨n, hn⟩
  induction n generalizing x with
  | zero =>
      -- Exponent `0` would force `x = 0`, contradicting the hypothesis.
      have hx_zero : x = 0 := by
        simpa using hn
      exact (hx hx_zero).elim
  | succ n ih =>
      by_cases hy : (f ^ n : R) • x = 0
      · -- If the previous power already kills `x`, recurse on the smaller exponent.
        exact ih hx hy
      · -- Otherwise the first nonzero stage is itself killed by one more multiplication by `f`.
        refine ⟨(f ^ n : R) • x, hy, ?_⟩
        simpa [pow_succ', smul_smul, mul_comm, mul_left_comm, mul_assoc] using hn

/-- Helper for Lemma 15.103.6: a module on which multiplication by `f` is injective and whose
away-localization at `f` is zero must itself be zero. -/
lemma isZero_of_mono_smul_and_localizedAway_isZero
    (N : ModuleCat R) (hmono : Mono (f • 𝟙 N))
    (hN :
      IsZero (ModuleCat.of (Localization.Away f) (LocalizedModule.Away f N))) :
    IsZero N := by
  refine (ModuleCat.isZero_iff_subsingleton).2 ?_
  refine ⟨?_⟩
  intro x y
  have hx_zero : x = 0 := by
    by_contra hx
    have hpow :
        ∃ n : ℕ, (f ^ n : R) • x = 0 :=
      exists_pow_smul_eq_zero_of_localizedAway_isZero (f := f) N x hN
    rcases exists_nonzero_smul_eq_zero_of_exists_pow_smul_eq_zero
        (R := R) (f := f) (x := x) hx hpow with ⟨z, hz, hzf⟩
    have hmono_inj : Function.Injective ((f • 𝟙 N).hom) :=
      (ModuleCat.mono_iff_injective _).1 hmono
    have hmap_zero : ((f • 𝟙 N).hom z) = ((f • 𝟙 N).hom 0) := by
      -- In the module category, `f • 𝟙` acts by scalar multiplication by `f`.
      simpa using hzf
    exact hz (hmono_inj hmap_zero)
  have hy_zero : y = 0 := by
    by_contra hy
    have hpow :
        ∃ n : ℕ, (f ^ n : R) • y = 0 :=
      exists_pow_smul_eq_zero_of_localizedAway_isZero (f := f) N y hN
    rcases exists_nonzero_smul_eq_zero_of_exists_pow_smul_eq_zero
        (R := R) (f := f) (x := y) hy hpow with ⟨z, hz, hzf⟩
    have hmono_inj : Function.Injective ((f • 𝟙 N).hom) :=
      (ModuleCat.mono_iff_injective _).1 hmono
    have hmap_zero : ((f • 𝟙 N).hom z) = ((f • 𝟙 N).hom 0) := by
      -- The same scalar-multiplication contradiction applies to every nonzero element.
      simpa using hzf
    exact hz (hmono_inj hmap_zero)
  simpa [hx_zero, hy_zero]

-- Proof sketch: use the long exact homology sequence of the distinguished triangle
-- `M --f·id--> M --> C --> M[1]`. If some negative homology of `M` were nonzero, its localization
-- would vanish by hypothesis, so it would contain nonzero `f`-power torsion; the kernel of
-- multiplication by `f` would then contribute nontrivially to the previous homology of the cone,
-- contradicting the vanishing of `H^i(C)` for `i < -1`.
/-- Canonical `t`-structure form of Lemma 15.103.6: let `C` be the cone of multiplication by
`f : R` on `M` in `D(R)`, written as a
distinguished triangle `M \xrightarrow{f} M \to C \to M[1]`. If the localized homology
`H^i(M)_f` vanishes for all `i < 0` and the homology of `C` vanishes for all `i < -1`, then
`M` lies in degrees `≥ 0`. -/
theorem isGE_zero_of_localized_isZero_and_cone_isGE_neg_one
    (hT : Triangle.mk (f • 𝟙 M) g δ ∈ distTriang DMod)
    (hMloc : ∀ i : ℤ, i < 0 →
      IsZero (ModuleCat.of (Localization.Away f) (LocalizedModule.Away f ((H i).obj M))))
    (hC : C.IsGE (-1)) :
    M.IsGE 0 := by
  rw [DerivedCategory.isGE_iff]
  intro i hi
  have hmono : Mono ((H i).map (f • 𝟙 M)) :=
    mono_homology_map_smul_of_cone_isGE_neg_one hT hC i hi
  have hmap :
      (H i).map (f • 𝟙 M) = f • 𝟙 ((H i).obj M) := by
    -- The auxiliary linearity bridge turns the categorical scalar endomorphism into the expected
    -- scalar action on the homology module.
    exact homology_functor_map_smul_id (R := R) (f := f) i M
  -- Combine the long-exact-sequence injectivity with the localization-torsion contradiction.
  exact
    isZero_of_mono_smul_and_localizedAway_isZero
      (f := f) ((H i).obj M) (by simpa [hmap] using hmono) (hMloc i hi)

/-- Lemma 15.103.6: let `C` be the cone of multiplication by `f : R` on `M` in `D(R)`, written as
the distinguished triangle `M \xrightarrow{f} M \to C \to M[1]`. If the localized homology
`H^i(M)_f` vanishes for all `i < 0` and the homology of `C` vanishes for all `i < -1`, then
`H^i(M)` vanishes for all `i < 0`. -/
theorem isZero_homology_of_neg_of_localized_isZero_and_cone_isZero
    (hT : Triangle.mk (f • 𝟙 M) g δ ∈ distTriang DMod)
    (hMloc : ∀ i : ℤ, i < 0 →
      IsZero (ModuleCat.of (Localization.Away f) (LocalizedModule.Away f ((H i).obj M))))
    (hC :
      ∀ i : ℤ, i < -1 →
        IsZero ((H i).obj C)) :
    ∀ i : ℤ, i < 0 →
      IsZero ((H i).obj M) := by
  simpa [DerivedCategory.isGE_iff] using
    isGE_zero_of_localized_isZero_and_cone_isGE_neg_one hT hMloc
      ((DerivedCategory.isGE_iff C (-1)).2 hC)

end

end

end CategoryTheory
