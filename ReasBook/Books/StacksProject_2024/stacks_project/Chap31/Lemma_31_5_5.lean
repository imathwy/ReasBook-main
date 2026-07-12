import StacksProject_2024.Chap10.Lemma_10_66_5
import StacksProject_2024.Chap31.Lemma_31_5_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

variable (ℱ : X.Modules)

/-- The weakly associated locus is empty exactly when no point is weakly associated. -/
theorem weakAss_eq_empty_iff :
    ℱ.weakAss = (∅ : Set X) ↔ ∀ x : X, ¬ ℱ.weaklyAssociatedAt x := by
  constructor
  · intro h x hx
    have : x ∈ ℱ.weakAss := by
      rwa [mem_weakAss_iff]
    simp [h] at this
  · intro h
    ext x
    constructor
    · intro hx
      exact False.elim <| h x ((mem_weakAss_iff ℱ x).1 hx)
    · intro hx
      cases hx

variable [ℱ.IsQuasicoherent]

-- Semantic recall: local Chapter 31 precedent fixes the source-facing weak-association owner as
-- `Scheme.Modules.weakAss`, while the zero-module side is the categorical owner `IsZero`. The
-- pointwise companion below exposes the empty-set condition through Definition 31.5.1.

/-- Lemma 31.5.5: for a quasi-coherent `\mathcal O_X`-module `\mathcal F` on a scheme `X`,
`\mathcal F = (0)` if and only if `WeakAss(\mathcal F) = \emptyset`. -/
@[stacks 05AP]
theorem isZero_iff_weakAss_eq_empty :
    IsZero ℱ ↔ ℱ.weakAss = (∅ : Set X) := by
  constructor
  · intro hzero
    rw [weakAss_eq_empty_iff]
    intro x hx
    have hx_zero : IsZero (RingedSpace.stalkModuleCat ℱ x) :=
      Functor.map_isZero (RingedSpace.stalkModuleFunctor x) hzero
    letI : Subsingleton (RingedSpace.stalkModuleCat ℱ x) :=
      ModuleCat.subsingleton_of_isZero hx_zero
    have hEmpty :
        weaklyAssociatedPrimes (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x) = ∅ := by
      simpa using
        (weaklyAssociatedPrimes.eq_empty_of_subsingleton :
          weaklyAssociatedPrimes (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x) = ∅)
    have hmem :
        IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∈
          weaklyAssociatedPrimes (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x) := by
      simpa [mem_weakAss_iff, mem_weaklyAssociatedPrimes_iff] using hx
    simpa [hEmpty] using hmem
  · intro hEmpty
    by_contra hzero
    have hid : (𝟙 ℱ : ℱ ⟶ ℱ) ≠ 0 := by
      intro h
      exact hzero ((IsZero.iff_id_eq_zero ℱ).2 h)
    obtain ⟨U, hU⟩ : ∃ U : X.Opens, ((𝟙 ℱ : ℱ ⟶ ℱ).app U) ≠ 0 := by
      by_contra h
      apply hid
      apply hom_ext
      intro U
      by_cases hU' : ((𝟙 ℱ : ℱ ⟶ ℱ).app U) = 0
      · exact hU'
      · exact False.elim <| h ⟨U, hU'⟩
    obtain ⟨s, hs⟩ : ∃ s : Γ(ℱ, U), ((𝟙 ℱ : ℱ ⟶ ℱ).app U) s ≠ 0 := by
      by_contra h
      apply hU
      ext s
      by_cases hs' : ((𝟙 ℱ : ℱ ⟶ ℱ).app U) s = 0
      · exact hs'
      · exact False.elim <| h ⟨s, hs'⟩
    have hs : s ≠ 0 := by
      simpa using hs
    let F : TopCat.Sheaf Ab X := ⟨ℱ.presheaf, ℱ.isSheaf⟩
    obtain ⟨x, hxU, hxg⟩ :
        ∃ x : X, ∃ hxU : x ∈ U, F.presheaf.germ U x hxU s ≠ 0 := by
      by_contra h
      have hg : ∀ x : X, ∀ hxU : x ∈ U, F.presheaf.germ U x hxU s = 0 := by
        intro x hxU
        by_cases hxg : F.presheaf.germ U x hxU s = 0
        · exact hxg
        · exact False.elim <| h ⟨x, hxU, hxg⟩
      exact hs <| TopCat.Presheaf.section_ext F U s 0 fun x hxU ↦ by simpa using hg x hxU
    obtain ⟨W, hW, hxW, hWU'⟩ := exists_isAffineOpen_mem_and_subset hxU
    have hWU : W ≤ U := hWU'
    let t : Γ(ℱ, W) := ℱ.presheaf.map (homOfLE hWU).op s
    have ht : t ≠ 0 := by
      intro ht
      apply hxg
      calc
        F.presheaf.germ U x hxU s = F.presheaf.germ W x hxW t := by
          symm
          simpa [F, t] using (F.presheaf.germ_res_apply (homOfLE hWU) x hxW s)
        _ = 0 := by simpa [F, t, ht]
    letI : Nontrivial Γ(ℱ, W) := (nontrivial_iff_exists_ne (0 : Γ(ℱ, W))).2 ⟨t, ht⟩
    obtain ⟨p, hp⟩ : (weaklyAssociatedPrimes (Γ(X, W)) (Γ(ℱ, W))).Nonempty :=
      weaklyAssociatedPrimes.nonempty
    let p' : PrimeSpectrum (Γ(X, W)) := ⟨p, hp.isPrime⟩
    have hp' : p'.asIdeal ∈ weaklyAssociatedPrimes (Γ(X, W)) (Γ(ℱ, W)) := by
      simpa [p'] using hp
    have hmem : hW.fromSpec p' ∈ ℱ.weakAss := by
      exact (mem_weaklyAssociatedPrimes_sections_iff_fromSpec_mem_weakAss ℱ hW p').1 hp'
    have : hW.fromSpec p' ∈ (∅ : Set X) := by
      simpa [hEmpty] using hmem
    simpa using this

/-- Pointwise reformulation of `isZero_iff_weakAss_eq_empty`. -/
theorem isZero_iff_forall_not_weaklyAssociatedAt :
    IsZero ℱ ↔ ∀ x : X, ¬ ℱ.weaklyAssociatedAt x := by
  rw [isZero_iff_weakAss_eq_empty, weakAss_eq_empty_iff]

end AlgebraicGeometry.Scheme.Modules
