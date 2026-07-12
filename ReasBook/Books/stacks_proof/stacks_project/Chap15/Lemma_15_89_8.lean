import Mathlib
import StacksProject_2024.Chap13.Lemma_13_28_5
import StacksProject_2024.Chap15.Lemma_15_59_14
import StacksProject_2024.Chap15.Lemma_15_89_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open DerivedCategory
open DerivedCategory.TStructure
open scoped DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R] (I : Ideal R)

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "DbMod" => boundedDerivedCategory (ModuleCat R)
local notation "Hb" => boundedDerivedHomologyFunctor (ModuleCat R)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)
local notation "single₀" => (ModuleCat.single0Functor : ModuleCat R ⥤ DMod)
local notation "RmodI" =>
  Functor.obj (ModuleCat.single0Functor : ModuleCat R ⥤ DMod) (ModuleCat.of R (R ⧸ I))

/- Domain-style sampling for Lemma 15.89.8:
- primary domain: derived tensor product in `D(R)` together with the canonical t-structure on the
  bounded derived category;
- sampled owner declarations:
  `Module.IsIdealPowerTorsion`,
  `CategoryTheory.derivedTensorProduct_boundedIdealPowerTorsion_isLE_zero_of_modIdeal`,
  `DerivedCategory.IsLE`,
  `boundedDerivedHomologyFunctor`,
  `ModuleCat.single0Functor`,
  `CategoryTheory.Triangulated.TStructure.isZero`;
- best owner abstraction: the core vanishing input is the canonical t-structure bound
  `(K ⊗[R]^L M).IsLE 0`, obtained from Lemma `15.89.7` after shifting `K`;
- primitive data: the source-facing hypothesis that every cohomology module `H^i(M)` is
  `I`-power torsion and the zero-object hypothesis modulo `I`;
- derived API: the zero-object consequences for bounded complexes, single modules, and the
  quotients `R ⧸ I^n`, all routed through the chapter owner `ModuleCat.single0Functor`.

Source/core/bridge triage:
- `source-facing`: the three `IsZero` consequences in this file;
- `core/canonical`: `DerivedCategory.IsLE` / `IsGE` and the t-structure zero-object criterion;
- `bridge/view`: `ModuleCat.single0Functor`, shifting `K`, and the
  `Module.IsIdealPowerTorsion` hypotheses on the bounded-derived cohomology objects `((Hb i).obj M)`.

Accordingly, this file keeps the source-facing zero-object statements and depends directly on the
chapter owner theorem `derivedTensorProduct_boundedIdealPowerTorsion_isLE_zero_of_modIdeal`,
rather than reimporting only its lower-level ingredients. -/

variable (K : DMod) (hKI : IsZero (K ⊗[R]^L RmodI))

/-- Helper for Lemma 15.89.8: the `I`-power torsion condition on bounded-derived homology is
stable under shifting the bounded object. -/
theorem boundedDerived_homology_shift_isIdealPowerTorsion
    (M : DbMod)
    (hMtors : ∀ i : ℤ, Module.IsIdealPowerTorsion I ((Hb i).obj M))
    (d i : ℤ) :
    Module.IsIdealPowerTorsion I ((Hb i).obj ((shiftFunctor DbMod d).obj M)) := by
  -- Proof comment: transport the torsion statement across the canonical homology shift
  -- identification.
  exact
    (Module.isIdealPowerTorsion_iff_of_linearEquiv I
      (boundedDerived_homology_shift_iso (R := R) M d i).toLinearEquiv).2
      (hMtors (i + d))

/-- Helper for Lemma 15.89.8: the vanishing modulo `I` remains true after shifting the left
tensor factor. -/
theorem derivedTensorProduct_isZero_of_modIdeal_isZero_shift
    (K : DMod)
    (hKI : IsZero (K ⊗[R]^L RmodI))
    (n : ℤ) :
    IsZero ((K⟦n⟧) ⊗[R]^L RmodI) := by
  -- Proof comment: the derived tensor functor with right factor `(R ⧸ I)[0]` commutes with
  -- shifts, so the shifted tensor product is just a shift of an already zero object.
  have hShiftedZero : IsZero ((K ⊗[R]^L RmodI)⟦n⟧) := by
    exact Functor.map_isZero (shiftFunctor DMod n) hKI
  exact
    hShiftedZero.of_iso
      (((derivedTensorProduct_commShift RmodI).commShiftIso n).app K)

/-- Helper for Lemma 15.89.8: after shifting a bounded derived object into `D^{≤ 0}`, Lemma
`15.89.7 (3)` applies uniformly to every shift of the left tensor factor. -/
theorem shifted_boundedIdealPowerTorsion_isLE_zero_of_modIdeal
    (K : DMod)
    (hKI : IsZero (K ⊗[R]^L RmodI))
    (M : DbMod)
    (d : ℤ)
    (hMtors : ∀ i : ℤ, Module.IsIdealPowerTorsion I ((Hb i).obj M))
    (hMle : M.obj.IsLE d)
    (n : ℤ) :
    ((K⟦n⟧) ⊗[R]^L ((shiftFunctor DbMod d).obj M).obj).IsLE 0 := by
  have hKIshiftZero :
      IsZero ((K⟦n⟧) ⊗[R]^L RmodI) :=
    derivedTensorProduct_isZero_of_modIdeal_isZero_shift (R := R) (I := I) K hKI n
  have hKIshiftLE :
      ((K⟦n⟧) ⊗[R]^L RmodI).IsLE 0 := by
    -- Proof comment: every positive-degree homology object of a zero object vanishes.
    rw [DerivedCategory.isLE_iff]
    intro i hi
    exact Functor.map_isZero (H i) hKIshiftZero
  have hShiftedMle :
      ((shiftFunctor DbMod d).obj M).obj.IsLE 0 := by
    -- Proof comment: shifting by the upper cohomological bound normalizes the right factor into
    -- `D^{≤ 0}`.
    letI : M.obj.IsLE d := hMle
    have hAmbient : (M.obj⟦d⟧).IsLE 0 := by
      simpa using (t.isLE_shift M.obj d d 0)
    rw [DerivedCategory.isLE_iff] at hAmbient ⊢
    intro i hi
    exact
      IsZero.of_iso
        (hAmbient i hi)
        ((H i).mapIso (((ObjectProperty.ι t.bounded).commShiftIso d).app M))
  have hShiftedMtors :
      ∀ i ≤ 0, Module.IsIdealPowerTorsion I ((Hb i).obj ((shiftFunctor DbMod d).obj M)) := by
    intro i hi
    exact boundedDerived_homology_shift_isIdealPowerTorsion
      (R := R) (I := I) M hMtors d i
  -- Proof comment: the earlier bounded-complex theorem now applies directly to the shifted
  -- bounded object.
  exact
    derivedTensorProduct_boundedIdealPowerTorsion_isLE_zero_of_modIdeal
      I (K⟦n⟧) hKIshiftLE ((shiftFunctor DbMod d).obj M) hShiftedMtors hShiftedMle

/-- Helper for Lemma 15.89.8: the bounded shift in `Dᵇ(R)` matches the ambient shift in `D(R)`. -/
noncomputable def bounded_shift_obj_iso
    (M : DbMod) (d : ℤ) :
    ((shiftFunctor DbMod d).obj M).obj ≅ M.obj⟦d⟧ :=
  ((ObjectProperty.ι t.bounded).commShiftIso d).app M

/-- Helper for Lemma 15.89.8: the normalization index satisfies the final homology-degree
identity needed for the second shift transport. -/
theorem tensor_homology_shift_index_eq
    (d i : ℤ) :
    (i - 1 - d) + (1 + d) = i := by
  omega

/-- Helper for Lemma 15.89.8: the degree-`1` homology of the normalized shifted tensor product is
the degree-`i` homology of the original tensor product. -/
noncomputable def tensor_homology_shift_iso
    (K : DMod)
    (M : DbMod) (d i : ℤ) :
    (H 1).obj ((K⟦i - 1 - d⟧) ⊗[R]^L ((shiftFunctor DbMod d).obj M).obj) ≅
      (H i).obj (K ⊗[R]^L M.obj) :=
  -- Route correction: reuse the imported right-variable tensor/shift isomorphisms and only add
  -- the bounded-to-ambient shift comparison local to this file.
  ((H 1).mapIso (derivedTensorProduct_right_map_iso (R := R)
    (bounded_shift_obj_iso (R := R) M d))) ≪≫
    ((H 1).mapIso (derivedTensorProduct_right_shift_iso (R := R)
      (K⟦i - 1 - d⟧) M.obj d)) ≪≫
      (((H 0).shiftIso d 1 (1 + d) (add_comm d 1)).app
        ((K⟦i - 1 - d⟧) ⊗[R]^L M.obj)) ≪≫
        ((H (1 + d)).mapIso
          (((derivedTensorProduct_commShift M.obj).commShiftIso (i - 1 - d)).app K)) ≪≫
          (((H 0).shiftIso (i - 1 - d) (1 + d) i
            (tensor_homology_shift_index_eq d i)).app (K ⊗[R]^L M.obj))

/-- Helper for Lemma 15.89.8: every cohomology object of `K ⊗^L M` vanishes once `M` has bounded
`I`-power torsion cohomology and `K ⊗^L (R ⧸ I)[0]` is zero. -/
theorem tensor_homology_isZero_of_boundedIdealPowerTorsion
    (K : DMod)
    (hKI : IsZero (K ⊗[R]^L RmodI))
    (M : DbMod)
    (hMtors : ∀ i : ℤ, Module.IsIdealPowerTorsion I ((Hb i).obj M))
    (i : ℤ) :
    IsZero ((H i).obj (K ⊗[R]^L M.obj)) := by
  rcases (derivedCategory_t_bounded_iff M.obj).1 M.property with ⟨_, ⟨d, hd⟩⟩
  have hMle : M.obj.IsLE d := by
    -- Proof comment: keep the upper cohomological bound coming from boundedness.
    rw [DerivedCategory.isLE_iff]
    intro j hj
    exact hd j hj
  have hNorm :
      ((K⟦i - 1 - d⟧) ⊗[R]^L ((shiftFunctor DbMod d).obj M).obj).IsLE 0 := by
    -- Proof comment: shift `M` into `D^{≤ 0}` and invoke the previously established shifted
    -- version of Lemma `15.89.7 (3)`.
    exact
      shifted_boundedIdealPowerTorsion_isLE_zero_of_modIdeal
        (R := R) (I := I) K hKI M d hMtors hMle (i - 1 - d)
  have hDegreeOneZero :
      IsZero
        ((H 1).obj ((K⟦i - 1 - d⟧) ⊗[R]^L ((shiftFunctor DbMod d).obj M).obj)) := by
    -- Proof comment: degree `1` lies strictly above the normalized `IsLE 0` cutoff.
    letI :
        ((K⟦i - 1 - d⟧) ⊗[R]^L ((shiftFunctor DbMod d).obj M).obj).IsLE 0 := hNorm
    exact DerivedCategory.isZero_of_isLE _ 0 1 (by omega)
  -- Proof comment: transport the normalized degree-`1` vanishing back to degree `i`.
  exact hDegreeOneZero.of_iso ((tensor_homology_shift_iso (R := R) K M d i).symm)

/-- Helper for Lemma 15.89.8: the bounded degree-zero complex attached to an `I`-power torsion
module has `I`-power torsion bounded-derived homology in every degree. -/
theorem single0_bounded_homology_torsion
    (N : ModuleCat R) (hN : Module.IsIdealPowerTorsion I N) :
    ∀ i : ℤ,
      Module.IsIdealPowerTorsion I
        ((Hb i).obj ((singleFunctorToBoundedDerived (A := ModuleCat R)).obj N)) := by
  intro i
  by_cases hi : i = 0
  · subst hi
    -- Proof comment: in degree `0`, the bounded-derived homology of `N[0]` is canonically `N`.
    let e : ((H 0).obj ((single₀).obj N)) ≅ N :=
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) (0 : ℤ)).app N
    change Module.IsIdealPowerTorsion I ((H 0).obj ((single₀).obj N))
    exact (Module.isIdealPowerTorsion_iff_of_linearEquiv I e.toLinearEquiv).2 hN
  · have hZero :
        IsZero
          ((Hb i).obj ((singleFunctorToBoundedDerived (A := ModuleCat R)).obj N)) := by
      -- Proof comment: away from degree `0`, a degree-zero complex has zero cohomology.
      dsimp [boundedDerivedHomologyFunctor, singleFunctorToBoundedDerived]
      exact single_zero_complex_homology_isZero_of_ne (A := ModuleCat R) N i hi
    have hZeroTors :
        Module.IsIdealPowerTorsion I
          ((Hb i).obj ((singleFunctorToBoundedDerived (A := ModuleCat R)).obj N)) := by
      -- Proof comment: a zero object in `ModuleCat R` is subsingleton, so every element is
      -- already equal to zero.
      rw [Module.isIdealPowerTorsion_iff]
      intro x
      let _ : Subsingleton ((Hb i).obj ((singleFunctorToBoundedDerived (A := ModuleCat R)).obj N))
        := ModuleCat.subsingleton_of_isZero hZero
      refine ⟨1, ?_⟩
      intro a
      simpa [Subsingleton.elim x
        (0 : ((Hb i).obj ((singleFunctorToBoundedDerived (A := ModuleCat R)).obj N)))] using
        (smul_zero (a : R) :
          (a : R) •
              (0 : ((Hb i).obj ((singleFunctorToBoundedDerived (A := ModuleCat R)).obj N))) =
            0)
    exact hZeroTors

-- Proof sketch: apply Lemma `15.89.7 (3)` to every shift `K[i]`; since the hypothesis says
-- `K ⊗_R^L (R ⧸ I)[0]` is the zero object, the same holds for all shifts, so every cohomology
-- object of `K ⊗_R^L M` vanishes. Then use the standard criterion that an object of `D(R)` with
-- zero cohomology in every degree is itself zero.
/-- Lemma 15.89.8: if `K \otimes_R^{\mathbf L} (R ⧸ I)[0]` is zero in `D(R)`, then
`K \otimes_R^{\mathbf L} M` is zero for every bounded derived `R`-complex whose cohomology
modules are `I`-power torsion. -/
@[stacks 0G1T]
theorem derivedTensorProduct_isZero_of_boundedIdealPowerTorsion_of_modIdeal_isZero
    (K : DMod)
    (hKI : IsZero (K ⊗[R]^L RmodI))
    (M : DbMod)
    (hMtors : ∀ i : ℤ, Module.IsIdealPowerTorsion I ((Hb i).obj M)) :
    IsZero (K ⊗[R]^L M.obj) := by
  have hGE :
      (K ⊗[R]^L M.obj).IsGE 1 := by
    -- Proof comment: every negative cohomology object vanishes by the shifted application of
    -- Lemma `15.89.7 (3)`.
    rw [DerivedCategory.isGE_iff]
    intro i hi
    exact
      tensor_homology_isZero_of_boundedIdealPowerTorsion
        (R := R) (I := I) K hKI M hMtors i
  have hLE :
      (K ⊗[R]^L M.obj).IsLE (-1) := by
    -- Proof comment: the same homology-vanishing computation kills all positive degrees.
    rw [DerivedCategory.isLE_iff]
    intro i hi
    exact
      tensor_homology_isZero_of_boundedIdealPowerTorsion
        (R := R) (I := I) K hKI M hMtors i
  letI : (K ⊗[R]^L M.obj).IsGE 1 := hGE
  letI : (K ⊗[R]^L M.obj).IsLE (-1) := hLE
  -- Proof comment: an object lying simultaneously in `D^{≥ 1}` and `D^{≤ -1}` is zero.
  exact t.isZero (K ⊗[R]^L M.obj) (-1) 1 (by omega)

-- Proof sketch: regard the `I`-power torsion module `N` as an object of `D^b(R)` concentrated in
-- degree `0`, observe that its only nonzero cohomology object is `N` itself, and apply the main
-- bounded-derived vanishing theorem.
/-- If `K \otimes_R^{\mathbf L} (R ⧸ I)[0]` is zero, then `K \otimes_R^{\mathbf L} N[0]` is zero
for every `I`-power torsion `R`-module `N`. -/
theorem derivedTensorProduct_isZero_of_idealPowerTorsionModule_of_modIdeal_isZero
    (K : DMod)
    (hKI : IsZero (K ⊗[R]^L RmodI))
    (N : ModuleCat R) (hN : Module.IsIdealPowerTorsion I N) :
    IsZero (K ⊗[R]^L (single₀).obj N) := by
  let M : DbMod := (singleFunctorToBoundedDerived (A := ModuleCat R)).obj N
  have hMtors : ∀ i : ℤ, Module.IsIdealPowerTorsion I ((Hb i).obj M) :=
    single0_bounded_homology_torsion (R := R) (I := I) N hN
  -- Proof comment: package `N[0]` as a bounded derived object and invoke the main theorem.
  simpa [M, singleFunctorToBoundedDerived] using
    derivedTensorProduct_isZero_of_boundedIdealPowerTorsion_of_modIdeal_isZero
      (R := R) (I := I) K hKI M hMtors

-- Proof sketch: the quotient `R ⧸ I^n` is `I`-power torsion for every `n` by Lemma `15.89.2`,
-- so this is the previous module case specialized to `N = R ⧸ I^n`.
/-- If `K \otimes_R^{\mathbf L} (R ⧸ I)[0]` is zero, then
`K \otimes_R^{\mathbf L} (R ⧸ I^n)[0]` is zero for every `n`. -/
theorem derivedTensorProduct_isZero_of_modIdealPow_of_modIdeal_isZero
    (K : DMod)
    (hKI : IsZero (K ⊗[R]^L RmodI))
    (n : ℕ) :
    IsZero (K ⊗[R]^L (single₀).obj (ModuleCat.of R (R ⧸ I ^ n))) := by
  -- Proof comment: the quotient `R ⧸ I^n` is `I`-power torsion, so this is the module case.
  exact
    derivedTensorProduct_isZero_of_idealPowerTorsionModule_of_modIdeal_isZero
      (R := R) (I := I) K hKI (ModuleCat.of R (R ⧸ I ^ n))
      (Module.isIdealPowerTorsion_quotient_pow I n)

end

end CategoryTheory
