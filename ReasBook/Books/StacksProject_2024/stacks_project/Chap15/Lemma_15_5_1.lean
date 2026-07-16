import Mathlib.Algebra.Algebra.Prod
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import StacksProject_2024.stacks_project.Chap10.Lemma_10_51_7_Artin_Tate

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open AlgHom
open scoped BigOperators

variable {R A B C : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
variable [Algebra R A] [Algebra R B] [Algebra R C]

/-
Domain-style sampling:
- primary domain: finite-type and finite-module arguments for fibre products in commutative
  algebra;
- sampled owner declarations: `AlgHom.equalizer`, `AlgHom.mem_equalizer`,
  `AlgHom.Finite.of_surjective`, and the Artin-Tate consequence
  `Subalgebra.finiteType_of_finite`.
- primitive data: the two comparison maps into `B`, the finite-type hypotheses on `A` and `C`,
  the surjectivity of `f`, and the finiteness of `g`;
- derived API: the finite-type conclusion for the fibre product comes from the Artin-Tate bridge
  once `A × C` is finite over the equalizer.

Source/core/bridge triage:
- `source-facing`: the fibre product is the canonical owner `AlgHom.equalizer` of the two maps
  `A × C →ₐ[R] B`;
- `bridge/view`: the internal module-finite bridge showing that `A × C` is finite as a module
  over that equalizer;
- `core/canonical`: once that bridge is available, the finite-type conclusion is the canonical
  Artin-Tate consequence `Subalgebra.finiteType_of_finite`.
-/
-- Proof sketch: realize `A ×_B C` as the equalizer subalgebra of the two maps
-- `A × C →ₐ[R] B`. Internally, the module-finite bridge identifies `A × C` as finite over that
-- equalizer, and the finite-type conclusion is then the canonical Artin-Tate consequence
-- `Subalgebra.finiteType_of_finite`.
/-- Helper for Lemma 15.5.1: a pair `(a, c)` belongs to the equalizer whenever its two images in
`B` agree. -/
lemma pair_mem_equalizer_of_eq
    (f : A →ₐ[R] B) (g : C →ₐ[R] B) {a : A} {c : C} (h : f a = g c) :
    (a, c) ∈ equalizer (f.comp (fst R A C)) (g.comp (snd R A C)) := by
  -- Membership in the equalizer is exactly the compatibility relation `f a = g c`.
  rw [AlgHom.mem_equalizer]
  simpa using h

/-- Bridge lemma for Lemma 15.5.1: under the surjective/finite hypotheses, the ambient product
`A × C` is finite as a module over the equalizer subalgebra defining the fibre product. -/
theorem moduleFinite_prod_over_equalizer_of_surjective_of_finite
    (f : A →ₐ[R] B) (g : C →ₐ[R] B) (hf : Function.Surjective f) (hg : g.Finite) :
    Module.Finite (equalizer (f.comp (fst R A C)) (g.comp (snd R A C))) (A × C) := by
  classical
  let D : Subalgebra R (A × C) := equalizer (f.comp (fst R A C)) (g.comp (snd R A C))
  letI : Algebra C B := g.toRingHom.toAlgebra
  letI : Module.Finite C B := by
    simpa [AlgHom.Finite, RingHom.Finite] using hg
  have hBfg : (⊤ : Submodule C B).FG := Module.Finite.fg_top
  obtain ⟨T, hTfinite, hTspan⟩ := Submodule.fg_def.mp hBfg
  let s : Finset B := hTfinite.toFinset
  have hs_span : Submodule.span C (s : Set B) = ⊤ := by
    simpa [s] using hTspan
  choose x hx using fun y : s ↦ hf y.1
  let gen : Option (Option s) → A × C
    | none => (1, 0)
    | some none => (0, 1)
    | some (some y) => (x y, 0)
  let M : Submodule D (A × C) := Submodule.span D (Set.range gen)
  have hMtop : M = ⊤ := by
    -- Follow the source proof: generate the `C`-part by `(0, 1)` and the `A`-part by `1` plus
    -- lifts of a finite `C`-generating family of `B`.
    exact top_le_iff.mp <| by
      intro z hz
      rcases z with ⟨a, c⟩
      have hgen_one : ((1 : A), (0 : C)) ∈ M := by
        exact Submodule.subset_span ⟨none, rfl⟩
      have hgen_right : ((0 : A), (1 : C)) ∈ M := by
        exact Submodule.subset_span ⟨some none, rfl⟩
      have hgen_left : ∀ y : s, ((x y : A), (0 : C)) ∈ M := by
        intro y
        exact Submodule.subset_span ⟨some (some y), rfl⟩
      have hCmem : ((0 : A), c) ∈ M := by
        obtain ⟨a₀, ha₀⟩ := hf (g c)
        let d₀ : D := ⟨(a₀, c), pair_mem_equalizer_of_eq f g ha₀⟩
        have hd₀ : d₀ • ((0 : A), (1 : C)) = ((0 : A), c) := by
          simp [Algebra.smul_def, d₀]
        rw [← hd₀]
        exact Submodule.smul_mem M d₀ hgen_right
      have hA0mem : (a, (0 : C)) ∈ M := by
        have hfa_span : f a ∈ Submodule.span C (Set.range fun y : s ↦ (y : B)) := by
          have hfa_top : f a ∈ Submodule.span C (s : Set B) := by
            rw [hs_span]
            exact Submodule.mem_top
          simpa using hfa_top
        obtain ⟨coeff, hcoeff⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hfa_span
        have hcoeff_sum :
            coeff.sum (fun y c ↦ g c * (y : B)) = f a := by
          simpa [Finsupp.sum, Algebra.smul_def] using hcoeff
        choose aCoeff haCoeff using fun y : s ↦ hf (g (coeff y))
        let liftedSum : A := coeff.sum fun y c ↦ aCoeff y * x y
        have hsum_mem :
            coeff.support.sum (fun y ↦ ((aCoeff y * x y : A), (0 : C))) ∈ M := by
          refine Submodule.sum_mem M ?_
          intro y hy
          let dCoeff : D := ⟨(aCoeff y, coeff y), pair_mem_equalizer_of_eq f g (haCoeff y)⟩
          have hdCoeff : dCoeff • ((x y : A), (0 : C)) = ((aCoeff y * x y : A), (0 : C)) := by
            simp [Algebra.smul_def, dCoeff]
          rw [← hdCoeff]
          exact Submodule.smul_mem M dCoeff (hgen_left y)
        have hsum_mem' :
            (coeff.sum fun y c ↦ ((aCoeff y * x y : A), (0 : C))) ∈ M := by
          simpa [Finsupp.sum] using hsum_mem
        have hsum_map :
            f liftedSum = coeff.sum (fun y c ↦ g c * (y : B)) := by
          simp [liftedSum, Finsupp.sum, map_sum, haCoeff, hx]
        have hker :
            f (a - liftedSum) = 0 := by
          rw [map_sub, hsum_map, hcoeff_sum, sub_self]
        have hker_eq :
            f (a - liftedSum) = g (0 : C) := by
          simpa using hker
        let dKer : D := ⟨
          (a - liftedSum, (0 : C)),
          pair_mem_equalizer_of_eq f g hker_eq⟩
        have hdKer :
            dKer • ((1 : A), (0 : C)) =
              (a - liftedSum, (0 : C)) := by
          simp [Algebra.smul_def, dKer]
        have hker_mem :
            (a - liftedSum, (0 : C)) ∈ M := by
          rw [← hdKer]
          exact Submodule.smul_mem M dKer hgen_one
        have hsum_pair :
            coeff.sum (fun y c ↦ ((aCoeff y * x y : A), (0 : C))) = (liftedSum, (0 : C)) := by
          ext
          · simp [liftedSum, Finsupp.sum, Prod.fst_sum]
          · simp [Finsupp.sum, Prod.snd_sum]
        have hsplit :
            (a, (0 : C)) =
              (a - liftedSum, (0 : C)) +
                coeff.sum (fun y c ↦ ((aCoeff y * x y : A), (0 : C))) := by
          rw [hsum_pair]
          ext <;> simp [sub_eq_add_neg, add_assoc]
        rw [hsplit]
        exact Submodule.add_mem M hker_mem hsum_mem'
      have hsplit : (a, c) = (a, (0 : C)) + ((0 : A), c) := by
        ext <;> simp
      rw [hsplit]
      exact Submodule.add_mem M hA0mem hCmem
  have hMfg : M.FG := Submodule.fg_span (Set.finite_range gen)
  letI : Module.Finite D M := Module.Finite.of_fg hMfg
  -- Once the finite spanning submodule is all of `A × C`, finite generation descends by the
  -- canonical top-submodule equivalence.
  exact Module.Finite.equiv ((LinearEquiv.ofEq M ⊤ hMtop).trans Submodule.topEquiv)

variable [IsNoetherianRing R] [Algebra.FiniteType R A] [Algebra.FiniteType R C]

/-- Lemma 15.5.1: if `R` is Noetherian, `A` and `C` are of finite type over `R`,
`f : A →ₐ[R] B` is surjective, and `g : C →ₐ[R] B` is finite, then the fibre product
`A ×_B C`, realized as the equalizer subalgebra of `A × C`, is of finite type over `R`. -/
theorem finiteType_fiberProduct_of_surjective_of_finite
    (f : A →ₐ[R] B) (g : C →ₐ[R] B) (hf : Function.Surjective f) (hg : g.Finite) :
    Algebra.FiniteType R (equalizer (f.comp (fst R A C)) (g.comp (snd R A C))) := by
  let left : A × C →ₐ[R] B := f.comp (fst R A C)
  let right : A × C →ₐ[R] B := g.comp (snd R A C)
  let T : Subalgebra R (A × C) := equalizer left right
  change Algebra.FiniteType R T
  let _ : Module.Finite T (A × C) := by
    simpa [T, left, right] using moduleFinite_prod_over_equalizer_of_surjective_of_finite f g hf hg
  exact Subalgebra.finiteType_of_finite T

end
