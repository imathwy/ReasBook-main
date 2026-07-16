import Mathlib.CategoryTheory.Limits.Cones
import Mathlib.CategoryTheory.Limits.IsLimit
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.DividedPowers.SubDPIdeal
import Mathlib.RingTheory.Localization.Away.Basic
import StacksProject_2024.stacks_project.Chapters.Chap23.section03

noncomputable section

open AdicCompletion
open CategoryTheory
open CategoryTheory.Limits
open DividedPowers

universe u

-- Semantic Lean search hits used here: `AdicCompletion`, `DividedPowers.isSubDPIdeal_ker`,
-- and `DividedPowers.Quotient.dividedPowers`.

namespace DividedPowers

section

variable {A : Type u} [CommRing A]
variable {p : ℕ} [Fact p.Prime]

local notation "pIdeal" => Ideal.span ({(p : A)} : Set A)

/-- The map from the `p`-adic completion of `A` to `A ⧸ I` induced by any stage
`A ⧸ pIdeal ^ t → A ⧸ I`. -/
def padicCompletionToQuotient (I : Ideal A) (t : ℕ) (hpt : pIdeal ^ t ≤ I) :
    AdicCompletion pIdeal A →+* A ⧸ I :=
  (Ideal.Quotient.factor hpt).comp (AdicCompletion.evalₐ pIdeal t).toRingHom

/-- The quotient `A ⧸ pIdeal ^ e` with the image of `I` and a chosen induced divided power
structure, viewed through the chapter's canonical owner `DividedPowerRing`. -/
abbrev quotientDividedPowerRing (I : Ideal A) (e : ℕ)
    (γe : DividedPowers (I.map (Ideal.Quotient.mk (pIdeal ^ e)))) : DividedPowerRing :=
  DividedPowerRing.of (A ⧸ pIdeal ^ e) (I.map (Ideal.Quotient.mk (pIdeal ^ e))) γe

/-- The completed ring together with the kernel of the map to `A ⧸ I` and a chosen extended
divided power structure on that kernel. -/
abbrev completionKernelDividedPowerRing (I : Ideal A) (t : ℕ) (hpt : pIdeal ^ t ≤ I)
    (γhat : DividedPowers (RingHom.ker (padicCompletionToQuotient I t hpt))) :
    DividedPowerRing :=
  DividedPowerRing.of (AdicCompletion pIdeal A)
    (RingHom.ker (padicCompletionToQuotient I t hpt)) γhat

/-- A cone over an eventual quotient tower whose point is the completed divided power ring and
whose legs are identified with the quotient divided power rings. -/
structure IsEventualQuotientTowerLimit (I : Ideal A) (γ : DividedPowers I) (t : ℕ)
    (hpt : pIdeal ^ t ≤ I)
    (γhat : DividedPowers (RingHom.ker (padicCompletionToQuotient I t hpt)))
    (F : ℕᵒᵖ ⥤ DividedPowerRing) (c : Cone F) : Prop where
  isDPMorphism : IsDPMorphism γ γhat (algebraMap A (AdicCompletion pIdeal A))
  pt_eq : c.pt = completionKernelDividedPowerRing I t hpt γhat
  obj_spec (e : ℕ) :
    ∃ γe : DividedPowers (I.map (Ideal.Quotient.mk (pIdeal ^ (e + t)))),
      F.obj (Opposite.op e) = quotientDividedPowerRing I (e + t) γe ∧
        IsDPMorphism γ γe (Ideal.Quotient.mk (pIdeal ^ (e + t)))
  isLimit : Nonempty (IsLimit c)

namespace IsEventualQuotientTowerLimit

section

variable {I : Ideal A} {γ : DividedPowers I} {t : ℕ} {hpt : pIdeal ^ t ≤ I}
variable {γhat : DividedPowers (RingHom.ker (padicCompletionToQuotient I t hpt))}
variable {F : ℕᵒᵖ ⥤ DividedPowerRing} {c : Cone F}

/-- Each stage of an eventual quotient tower limit is a quotient divided power ring
`(A ⧸ pIdeal ^ (e + t), I / pIdeal ^ (e + t), γe)` for some induced divided powers `γe`. -/
theorem obj_eq (h : IsEventualQuotientTowerLimit I γ t hpt γhat F c) (e : ℕ) :
    ∃ γe : DividedPowers (I.map (Ideal.Quotient.mk (pIdeal ^ (e + t)))),
      F.obj (Opposite.op e) = quotientDividedPowerRing I (e + t) γe := by
  rcases h.obj_spec e with ⟨γe, hobj, -⟩
  exact ⟨γe, hobj⟩

/-- The divided powers on each stage of an eventual quotient tower limit are induced from the
original divided powers on `I`. -/
theorem obj_isDPMorphism (h : IsEventualQuotientTowerLimit I γ t hpt γhat F c) (e : ℕ) :
    ∃ γe : DividedPowers (I.map (Ideal.Quotient.mk (pIdeal ^ (e + t)))),
      IsDPMorphism γ γe (Ideal.Quotient.mk (pIdeal ^ (e + t))) := by
  rcases h.obj_spec e with ⟨γe, -, hγe⟩
  exact ⟨γe, hγe⟩

end

end IsEventualQuotientTowerLimit

variable (I : Ideal A) (γ : DividedPowers I)

/-- Lemma 23.4.5 (1): after choosing `t` with `pIdeal ^ t ≤ I`, the `p`-adic completion of `A`
surjects onto `A ⧸ I`. -/
@[stacks 07KD]
theorem padicCompletionToQuotient_surjective (t : ℕ) (hpt : pIdeal ^ t ≤ I) :
    Function.Surjective (padicCompletionToQuotient I t hpt) := sorry

/-- Lemma 23.4.5 (2): after choosing `t` with `pIdeal ^ t ≤ I`, an element of the `p`-adic
completion of `A` maps to zero in `A ⧸ I` exactly when it comes from the `p`-adic completion of
the ideal `I`. -/
@[stacks 07KD]
theorem mem_ker_padicCompletionToQuotient_iff (t : ℕ) (hpt : pIdeal ^ t ≤ I)
    {x : AdicCompletion pIdeal A} :
    x ∈ RingHom.ker (padicCompletionToQuotient I t hpt) ↔
      ∃ y : AdicCompletion pIdeal I, AdicCompletion.map pIdeal I.subtype y = x := sorry

/-- Lemma 23.4.5 (3): after choosing `t` with `pIdeal ^ t ≤ I`, the divided powers on `I` extend
to the kernel of the map from the `p`-adic completion of `A` to `A ⧸ I`. -/
@[stacks 07KD]
theorem exists_completionKernelDividedPowers (t : ℕ) (hpt : pIdeal ^ t ≤ I) :
    ∃ γhat : DividedPowers (RingHom.ker (padicCompletionToQuotient I t hpt)),
      IsDPMorphism γ γhat (algebraMap A (AdicCompletion pIdeal A)) := sorry

/-- Lemma 23.4.5 (4): if `A` is a `ℤ_(p)`-algebra, then after choosing `t` with
`pIdeal ^ t ≤ I`, for all sufficiently large `e` the ideal `pIdeal ^ e` is contained in `I`, is
stable under the divided powers on `I`, and the quotient `A ⧸ pIdeal ^ e` carries the induced
divided power structure on the image of `I`. -/
@[stacks 07KD]
theorem eventually_exists_quotientDividedPowers [Algebra (Localization.Away (p : ℤ)) A]
    (t : ℕ) (hpt : pIdeal ^ t ≤ I) :
    ∃ e0 : ℕ, ∀ e ≥ e0,
      ∃ hpeI : pIdeal ^ e ≤ I,
        IsSubDPIdeal γ (pIdeal ^ e ⊓ I) ∧
          ∃ γe : DividedPowers (I.map (Ideal.Quotient.mk (pIdeal ^ e))),
            IsDPMorphism γ γe (Ideal.Quotient.mk (pIdeal ^ e)) := sorry

/-- Lemma 23.4.5 (5): if `A` is a `ℤ_(p)`-algebra, then after choosing `t` with
`pIdeal ^ t ≤ I`, the completed divided power ring is the limit in `DividedPowerRing` of an
eventual inverse system of quotient divided power rings `(A ⧸ pIdeal ^ (e + t), I/(pIdeal ^ (e +
t)), γe)`. -/
@[stacks 07KD]
theorem exists_eventualQuotientTowerLimit [Algebra (Localization.Away (p : ℤ)) A]
    (t : ℕ) (hpt : pIdeal ^ t ≤ I) :
    ∃ γhat : DividedPowers (RingHom.ker (padicCompletionToQuotient I t hpt)),
      ∃ F : ℕᵒᵖ ⥤ DividedPowerRing, ∃ c : Cone F,
        IsEventualQuotientTowerLimit I γ t hpt γhat F c := sorry

end

end DividedPowers
