import Mathlib
import StacksProject_2024.Chap20.«20_23_6_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace

noncomputable section

universe u v

variable {X : TopCat.{u}} {ι : Type v} [LinearOrder ι]

/- Domain-style sampling for Item 20.23.6.2:
- primary domain: explicit homotopies between semi-ordered and ordered Čech cochains on a linearly
  ordered cover;
- sampled owner API:
  `orderedCechTerm`,
  `cechDuplicateTransport`,
  `Monotone.strictMono_iff_injective`,
  `Fin.orderHom_injective_iff`;
- best owner abstraction: the source-facing second homotopy stays on semi-ordered Čech terms, while
  the repeated-entry transport reuses the chapter owner `cechDuplicateTransport` and the repeated
  adjacent-index detection is derived from the canonical injectivity characterizations for monotone
  finite tuples.

Source/core/bridge triage:
- `source-facing`: `semiOrderedCechSecondHomotopyToFun`;
- `core/canonical`: `cechDuplicateTransport` from `20_23_6_1`, together with
  `Monotone.strictMono_iff_injective` and `Fin.orderHom_injective_iff` from mathlib;
- `bridge/view`: the monotone specialization `σ.comp (Fin.predAboveOrderHom a.succ)` of the
  duplicate-entry transport owner.

Primitive data versus derived API:
- primitive data: semi-ordered tuples and the chosen first repeated adjacent index in a
  non-strict tuple;
- derived API: the second homotopy formula and its strict-mono vanishing lemma. -/

/-- The degree `p` term of the semi-ordered Čech complex: sections indexed by weakly increasing
`(p + 1)`-tuples of the ordered index type. -/
abbrev semiOrderedCechTerm (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v})
    (p : ℕ) : AddCommGrpCat.{max u v} :=
  AddCommGrpCat.of
    ((σ : Fin (p + 1) →o ι) → F.obj (op (cechIntersection 𝒰 σ)))

-- Proof sketch: for an order hom on `Fin (p + 1)`, failure of strict monotonicity is equivalent to
-- failure of injectivity, and mathlib's `Fin.orderHom_injective_iff` identifies that with an
-- adjacent equality.
/-- A weakly increasing finite tuple that is not strictly increasing has an adjacent repeated
value. -/
theorem exists_adjacent_eq_of_not_strictMono {p : ℕ} (σ : Fin (p + 1) →o ι)
    (hσ : ¬ StrictMono σ) :
    ∃ a : Fin p, σ a.castSucc = σ a.succ := by
  have hσ' : ¬ Function.Injective σ := by
    rwa [σ.monotone.strictMono_iff_injective] at hσ
  rw [Fin.orderHom_injective_iff] at hσ'
  push Not at hσ'
  exact hσ'

/-- A chosen adjacent repeated index in a weakly increasing tuple that is not strictly
increasing. -/
private noncomputable def firstRepeatedIndex {p : ℕ} (σ : Fin (p + 1) →o ι)
    (hσ : ¬ StrictMono σ) : Fin p :=
  Classical.choose (exists_adjacent_eq_of_not_strictMono σ hσ)

/-- 20.23.6.2: the degree-`p` component of the second homotopy on the semi-ordered Čech complex
vanishes on strictly increasing tuples and otherwise inserts one extra copy of the first repeated
adjacent index with sign `(-1)^a`. -/
def semiOrderedCechSecondHomotopyToFun (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    semiOrderedCechTerm 𝒰 F (p + 1) → semiOrderedCechTerm 𝒰 F p :=
  fun s σ ↦
    if hσ : StrictMono σ then
      0
    else
      let a := firstRepeatedIndex σ hσ
      (-1 : ℤ) ^ (a : ℕ) •
        cechDuplicateTransport 𝒰 F σ a.succ
          (s (σ.comp (Fin.predAboveOrderHom a.succ)))

-- Proof sketch: unfold `semiOrderedCechSecondHomotopyToFun`; the strict-increasing branch is the
-- first clause of the defining case split.
/-- The second semi-ordered Čech homotopy vanishes on strictly increasing tuples. -/
@[simp] theorem semiOrderedCechSecondHomotopyToFun_apply_of_strictMono (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s : semiOrderedCechTerm 𝒰 F (p + 1)) (σ : Fin (p + 1) →o ι) (hσ : StrictMono σ) :
    semiOrderedCechSecondHomotopyToFun 𝒰 F p s σ = 0 := by
  simp [semiOrderedCechSecondHomotopyToFun, hσ]
