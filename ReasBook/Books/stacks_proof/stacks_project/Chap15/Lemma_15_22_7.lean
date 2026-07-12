import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Algebra.Module.Lattice
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/-
Domain-style sampling:
- primary domain: finite modules over domains, torsion-freeness, and embeddings into finite free
  modules;
- sampled owner API:
  `Module.IsTorsionFree`,
  `Basis.isTorsionFree`,
  `Function.Injective.moduleIsTorsionFree`,
  `Module.Finite.exists_fin'`,
  `LinearIndependent.iff_fractionRing`;
- best owner abstraction: `Module.IsTorsionFree`, with `Fin n → R` as the canonical finite free
  model used by `Module.Finite.exists_fin'`;
- source-facing layer: the Stacks equivalence between torsion-freeness and embeddability into a
  finite free module;
- core/canonical layer: the torsion-free owner `Module.IsTorsionFree`;
- bridge/view layer: the canonical finite free model `Fin n → R` and injective linear maps
  `M →ₗ[R] (Fin n → R)`.

Primitive data are only the finite `R`-module `M` and the owner predicate
`Module.IsTorsionFree R M`. Mathlib provides the owner abstractions used in the proof, but not this
exact equivalence as a canonical theorem, so the source-facing statement should remain here instead
of being replaced by a less usable existential package around `Module.Free`.
-/

section

open Module
open nonZeroDivisors

variable {R : Type u} {M : Type v}
variable [CommRing R] [IsDomain R]
variable [AddCommGroup M] [Module R M] [Module.Finite R M]

local notation "NZD" => nonZeroDivisors R

/-- Helper for Lemma 15.22.7: a basis of the generic fiber can be lifted to elements of `M` whose
localized images are denominator multiples of the basis vectors, and these lifts stay linearly
independent over `R`. -/
lemma localized_basis_lift_with_denominators
    (n : ℕ) (b : Basis (Fin n) (FractionRing R) (LocalizedModule NZD M)) :
    ∃ w : Fin n → M, ∃ s : Fin n → NZD,
      (∀ i, IsLocalizedModule.mk' (LocalizedModule.mkLinearMap NZD M) (w i) (s i) = b i) ∧
      LinearIndependent R w := by
  classical
  have hsurj :
      ∀ i : Fin n,
        ∃ ms : M × NZD, IsLocalizedModule.mk' (LocalizedModule.mkLinearMap NZD M) ms.1 ms.2 = b i :=
    fun i ↦ IsLocalizedModule.mk'_surjective NZD (LocalizedModule.mkLinearMap NZD M) (b i)
  choose ms hms using hsurj
  let w : Fin n → M := fun i ↦ (ms i).1
  let s : Fin n → NZD := fun i ↦ (ms i).2
  have hs : ∀ i, IsLocalizedModule.mk' (LocalizedModule.mkLinearMap NZD M) (w i) (s i) = b i := hms
  have hs_ne_zero : ∀ i, algebraMap R (FractionRing R) (s i : R) ≠ 0 := by
    intro i hzero
    have hzero' : algebraMap R (FractionRing R) (s i : R) = algebraMap R (FractionRing R) 0 := by
      simpa using hzero
    exact
      mem_nonZeroDivisors_iff_ne_zero.mp (s i).2
        ((IsFractionRing.injective R (FractionRing R)) hzero')
  refine ⟨w, s, hs, ?_⟩
  have hscaled :
      ∀ i,
        (LocalizedModule.mkLinearMap NZD M) (w i) =
          (Units.mk0 (algebraMap R (FractionRing R) (s i : R)) (hs_ne_zero i) :
            (FractionRing R)ˣ) • b i := by
    intro i
    -- Rewrite each lifted vector as a unit multiple of the chosen basis vector.
    have hs' :
        (LocalizedModule.mkLinearMap NZD M) (w i) = (s i : NZD) • b i :=
      (IsLocalizedModule.mk'_eq_iff (S := NZD) (f := LocalizedModule.mkLinearMap NZD M)).mp (hs i)
    simpa [Submonoid.smul_def, Units.val_mk0] using hs'
  have hlocalized :
      LinearIndependent (FractionRing R) (fun i ↦ (LocalizedModule.mkLinearMap NZD M) (w i)) := by
    -- Unit rescaling preserves linear independence in the fraction field.
    let u : Fin n → (FractionRing R)ˣ := fun i ↦
      Units.mk0 (algebraMap R (FractionRing R) (s i : R)) (hs_ne_zero i)
    have hu : LinearIndependent (FractionRing R) (fun i ↦ u i • b i) :=
      b.linearIndependent.units_smul u
    simpa [u, hscaled] using hu
  have hlocalizedR :
      LinearIndependent R (fun i ↦ (LocalizedModule.mkLinearMap NZD M) (w i)) := by
    -- Over a fraction field, `R`- and `K`-linear independence coincide.
    rw [LinearIndependent.iff_fractionRing (R := R) (K := FractionRing R)]
    exact hlocalized
  -- Linear independence descends from the localized image back to the original family.
  exact LinearIndependent.of_comp (LocalizedModule.mkLinearMap NZD M) hlocalizedR

/-- Helper for Lemma 15.22.7: if every basis vector of the generic fiber lies in the localized span
of a submodule, then that localized submodule is the whole generic fiber. -/
lemma localized_span_eq_top_of_basis_mem
    (n : ℕ) (b : Basis (Fin n) (FractionRing R) (LocalizedModule NZD M))
    (P : Submodule R M)
    (hmem : ∀ i, b i ∈ Submodule.localized (p := NZD) P) :
    Submodule.localized (p := NZD) P = ⊤ := by
  -- A basis belongs to a submodule exactly when that submodule is the whole space.
  rw [Submodule.eq_top_iff_forall_basis_mem (b := b)]
  exact hmem

/-- Helper for Lemma 15.22.7: if a submodule has full generic fiber, then the localization of the
quotient by that submodule is trivial. -/
lemma subsingleton_localized_quotient_of_localized_eq_top
    (P : Submodule R M) (hP : Submodule.localized (p := NZD) P = ⊤) :
    Subsingleton (LocalizedModule NZD (M ⧸ P)) := by
  let e : (LocalizedModule NZD M ⧸ Submodule.localized (p := NZD) P) ≃ₗ[FractionRing R]
      LocalizedModule NZD (M ⧸ P) :=
    localizedQuotientEquiv NZD P
  have hquot :
      Subsingleton (LocalizedModule NZD M ⧸ Submodule.localized (p := NZD) P) := by
    rw [hP]
    infer_instance
  -- Transport the quotient-by-`⊤` subsingleton structure across the localization equivalence.
  letI : Subsingleton (LocalizedModule NZD M ⧸ Submodule.localized (p := NZD) P) := hquot
  exact e.symm.toEquiv.subsingleton

/-- Helper for Lemma 15.22.7: if the generic fiber of a finite module is zero, then one nonzero
scalar annihilates the whole module. -/
lemma exists_nonzero_smul_eq_zero_of_localized_subsingleton
    {N : Type*} [AddCommGroup N] [Module R N] [Module.Finite R N]
    (hsub : Subsingleton (LocalizedModule NZD N)) :
    ∃ a : R, a ≠ 0 ∧ ∀ x : N, a • x = 0 := by
  classical
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin' R N
  have hkill_basis :
      ∀ i : Fin n, ∃ s : R⁰, (s : R) • g (Pi.basisFun R (Fin n) i) = 0 := by
    intro i
    rcases (LocalizedModule.subsingleton_iff (S := NZD) (M := N)).mp hsub
        (g (Pi.basisFun R (Fin n) i)) with ⟨s, hs, hzero⟩
    exact ⟨⟨s, hs⟩, hzero⟩
  choose s hs using hkill_basis
  let a : R := ∏ i, (s i : R)
  refine ⟨a, ?_, ?_⟩
  · -- The product of nonzero denominators is again nonzero in a domain.
    exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ mem_nonZeroDivisors_iff_ne_zero.mp (s i).2
  · intro x
    obtain ⟨y, rfl⟩ := hg x
    have hmap : (a • g : (Fin n → R) →ₗ[R] N) = 0 := by
      -- It suffices to check the map on the standard basis of the finite free source.
      apply (Pi.basisFun R (Fin n)).ext
      intro i
      have hdiv : (s i : R) ∣ a := by
        exact Finset.dvd_prod_of_mem (fun j ↦ (s j : R)) (by simp)
      rcases hdiv with ⟨c, hc⟩
      change a • g (Pi.basisFun R (Fin n) i) = 0
      have hc' : a = c * (s i : R) := by simpa [mul_comm] using hc
      rw [hc', mul_smul, hs i, smul_zero]
    simpa [a] using LinearMap.congr_fun hmap y

/-- Helper for Lemma 15.22.7: codrestricting multiplication by a nonzero scalar into a submodule
remains injective on a torsion-free module. -/
lemma smul_codRestrict_injective (P : Submodule R M) {a : R} (ha : a ≠ 0)
    (hP : ∀ x : M, a • x ∈ P) (hTF : Module.IsTorsionFree R M) :
    Function.Injective (LinearMap.codRestrict P ((a : R) • LinearMap.id) hP) := by
  intro x y hxy
  have hsmul : a • x = a • y := by
    exact congrArg Subtype.val hxy
  -- Torsion-freeness turns equality after multiplying by `a ≠ 0` back into equality of vectors.
  exact (hTF.isSMulRegular (r := a) (IsRegular.of_ne_zero ha)) hsmul

-- Proof sketch: if `M` embeds into `Fin n → R`, then it is torsion free because submodules of a
-- torsion-free module are torsion free. Conversely, tensor `M` with the fraction field of `R`,
-- choose a basis of the resulting finite-dimensional vector space, clear denominators on a finite
-- generating set of `M`, and obtain an injective map from `M` into `R^n`.
/-- Lemma 15.22.7: a finite module over a domain is torsion free if and only if it admits an
injective linear map into a finite free module, expressed here in the canonical model
`Fin n → R`. -/
@[stacks 0AUU]
theorem isTorsionFree_iff_exists_injective_to_fin_fun :
    Module.IsTorsionFree R M ↔
      ∃ n : ℕ, ∃ f : M →ₗ[R] (Fin n → R), Function.Injective f := by
  constructor
  · intro hTF
    -- Route correction: replace the earlier rank-transport stub by the source-faithful generic
    -- fiber argument controlled by a basis of the localized module.
    let n : ℕ := Module.finrank (FractionRing R) (LocalizedModule NZD M)
    let b : Basis (Fin n) (FractionRing R) (LocalizedModule NZD M) :=
      Module.finBasis (FractionRing R) (LocalizedModule NZD M)
    obtain ⟨w, s, hs, hw⟩ := localized_basis_lift_with_denominators (R := R) (M := M) n b
    let P : Submodule R M := Submodule.span R (Set.range w)
    have hbasis_mem :
        ∀ i, b i ∈ Submodule.localized (p := NZD) P := by
      intro i
      -- Each basis vector is represented by a lifted numerator lying in the chosen span.
      refine ⟨w i, Submodule.subset_span ⟨i, rfl⟩, s i, ?_⟩
      exact hs i
    have hlocalized_top : Submodule.localized (p := NZD) P = ⊤ :=
      localized_span_eq_top_of_basis_mem (R := R) (M := M) n b P hbasis_mem
    have hquot_sub :
        Subsingleton (LocalizedModule NZD (M ⧸ P)) :=
      subsingleton_localized_quotient_of_localized_eq_top (R := R) (M := M) P hlocalized_top
    obtain ⟨a, ha, hkill⟩ :=
      exists_nonzero_smul_eq_zero_of_localized_subsingleton (R := R) (N := M ⧸ P) hquot_sub
    have hsmul_mem : ∀ x : M, a • x ∈ P := by
      intro x
      -- Killing the quotient means scalar multiplication lands inside the spanning submodule.
      have hqx : a • (Submodule.Quotient.mk x : M ⧸ P) = 0 :=
        hkill (Submodule.Quotient.mk x)
      simpa using (Submodule.Quotient.mk_eq_zero P).mp hqx
    let hcod :=
      smul_codRestrict_injective (R := R) (M := M) P ha hsmul_mem hTF
    let bP : Basis (Fin n) R P := Basis.span hw
    let f : M →ₗ[R] (Fin n → R) :=
      (bP.equivFun.toLinearMap).comp (LinearMap.codRestrict P ((a : R) • LinearMap.id) hsmul_mem)
    refine ⟨n, f, ?_⟩
    intro x y hxy
    apply hcod
    exact bP.equivFun.injective hxy
  · rintro ⟨n, f, hf⟩
    -- Pull torsion-freeness back along the given embedding into the finite free module `R^n`.
    let _ : Module.IsTorsionFree R (Fin n → R) := inferInstance
    exact Function.Injective.moduleIsTorsionFree f hf (fun r x ↦ by simp)

end
