import Mathlib
import stacks_project.Chap10.Lemma_10_82_13

open IsLocalRing
open CategoryTheory

section CriteriaForFlatness

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
variable [IsNoetherianRing S]
variable {n : ℕ}
variable {F : Fin (n + 2) → Type v}
variable [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)] [∀ i, Module R (F i)]
variable [∀ i, IsScalarTower R S (F i)]

/- Domain-style sampling:
* primary domain: finite exact sequences of modules over a local ring map, together with reduction
  modulo the maximal ideal.
* inspected owner declarations:
  `CategoryTheory.ComposableArrows.Exact`,
  `CategoryTheory.ComposableArrows.mkOfObjOfMapSucc`,
  `CategoryTheory.HomologicalComplex.ExactAt`,
  `LinearMap.quotientMapByIdeal`.
* best owner abstraction: the finite family of differentials should be organized by the canonical
  finite-sequence owner `ComposableArrows`, with exactness carried by `ComposableArrows.Exact`;
  the leftmost injectivity clause remains separate source-facing edge data for the augmented
  sequence `0 → F_{n+1} → ⋯ → F₀`.
* primitive data: the maps `d i : F_{i+1} → F_i`, the finite/flat hypotheses on the modules, and
  the reduction modulo `maximalIdeal R`.
* derived API: the finite sequence `finiteSequence d` and the reduced sequence
  `reducedFiniteSequence R d`, together with their owner predicate `.Exact`.
* source/core/bridge triage:
  `source-facing`: the two lemmas about exactness and flat cokernels for a finite sequence of
    `S`-modules;
  `core/canonical`: `ComposableArrows.Exact`;
  `bridge/view`: `finiteSequence` and `reducedFiniteSequence`, which package the displayed maps into
    the canonical owner object.
-/

namespace CriteriaForFlatness

/-- The finite sequence
`F_{n+1} ⟶ F_n ⟶ ⋯ ⟶ F_0`
attached to the displayed differentials, organized by the canonical owner
`ComposableArrows (ModuleCat S) (n + 1)`. -/
noncomputable abbrev finiteSequence
    (d : ∀ i : Fin (n + 1), F i.succ →ₗ[S] F i.castSucc) :
    ComposableArrows (ModuleCat S) (n + 1) :=
  ComposableArrows.mkOfObjOfMapSucc
    (fun i ↦ ModuleCat.of S (F i.rev))
    (fun i ↦ by
      change ModuleCat.of S (F i.castSucc.rev) ⟶ ModuleCat.of S (F i.succ.rev)
      rw [Fin.rev_castSucc, Fin.rev_succ]
      exact ModuleCat.ofHom (d i.rev))

variable (R) in
/-- The reduction modulo `maximalIdeal R` of the finite sequence
`F_{n+1} ⟶ F_n ⟶ ⋯ ⟶ F_0`,
organized by the same canonical owner `ComposableArrows`. -/
noncomputable abbrev reducedFiniteSequence
    (d : ∀ i : Fin (n + 1), F i.succ →ₗ[S] F i.castSucc) :
    ComposableArrows (ModuleCat R) (n + 1) :=
  ComposableArrows.mkOfObjOfMapSucc
    (fun i ↦
      ModuleCat.of R
        (F i.rev ⧸ (maximalIdeal R • (⊤ : Submodule R (F i.rev)))))
    (fun i ↦ by
      change
        ModuleCat.of R
            (F i.castSucc.rev ⧸ (maximalIdeal R • (⊤ : Submodule R (F i.castSucc.rev)))) ⟶
          ModuleCat.of R
            (F i.succ.rev ⧸ (maximalIdeal R • (⊤ : Submodule R (F i.succ.rev))))
      rw [Fin.rev_castSucc, Fin.rev_succ]
      exact ModuleCat.ofHom
        (((d i.rev).restrictScalars R).quotientMapByIdeal (maximalIdeal R)))

end CriteriaForFlatness

/-- Lemma 10.99.5 (1): for a local homomorphism `R → S` of local rings with `S` Noetherian, if
`0 → F_{n+1}/𝔪F_{n+1} → F_n/𝔪F_n → ⋯ → F_0/𝔪F_0` is exact and every `F_i` is a finite `S`-module
flat over `R`, then `0 → F_{n+1} → F_n → ⋯ → F_0` is exact. The middle exactness is organized by
the canonical finite-sequence owner `ComposableArrows.Exact`, while injectivity of the leftmost
map remains the separate source-facing edge condition. -/
-- Proof sketch: argue by induction on `n + 1`. The base case is Lemma `10.99.1`, applied to the
-- leftmost map. For the inductive step, first use Lemma `10.99.1` on `F_{n+1} → F_n` to obtain
-- injectivity and flatness of its cokernel, then apply the induction hypothesis to the shortened
-- sequence obtained by replacing `F_n` with that cokernel.
theorem finiteComplexExact_of_reducedFiniteComplexExact
    (d : ∀ i : Fin (n + 1), F i.succ →ₗ[S] F i.castSucc)
    (hfinite : ∀ i, Module.Finite S (F i))
    (hflat : ∀ i, Module.Flat R (F i))
    (hexact_mod :
      Function.Injective
          (((d (Fin.last n)).restrictScalars R).quotientMapByIdeal (maximalIdeal R)) ∧
        (CriteriaForFlatness.reducedFiniteSequence R d).Exact) :
    Function.Injective (d (Fin.last n)) ∧
      (CriteriaForFlatness.finiteSequence d).Exact := sorry

/-- Lemma 10.99.5 (2): under the same hypotheses, the cokernel of `F₁ → F₀` is flat over `R`. -/
-- Proof sketch: after part (1) gives exactness of the original sequence, the same induction on
-- the length of the sequence shows that the cokernel of the rightmost differential is obtained
-- from a shorter exact sequence whose terms are still finite over `S` and flat over `R`; the base
-- case is again Lemma `10.99.1`.
theorem flat_cokernel_of_reducedFiniteComplexExact
    (d : ∀ i : Fin (n + 1), F i.succ →ₗ[S] F i.castSucc)
    (hfinite : ∀ i, Module.Finite S (F i))
    (hflat : ∀ i, Module.Flat R (F i))
    (hexact_mod :
      Function.Injective
          (((d (Fin.last n)).restrictScalars R).quotientMapByIdeal (maximalIdeal R)) ∧
        (CriteriaForFlatness.reducedFiniteSequence R d).Exact) :
    Module.Flat R (F 0 ⧸ LinearMap.range (d 0)) := sorry

end CriteriaForFlatness
