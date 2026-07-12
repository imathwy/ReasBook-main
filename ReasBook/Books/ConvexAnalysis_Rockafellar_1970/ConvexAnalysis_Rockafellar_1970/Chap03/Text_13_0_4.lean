import Mathlib
import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_7_11
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Rockafellar

universe u v w

variable {R : Type w} [ConditionallyCompleteLattice R]
variable {X : Type u} {Y : Type v}
variable [HasPairing X Y R]

local instance instHasPairingYX : HasPairing Y X R :=
  HasPairing.swap (X := X) (Y := Y) (L := R)

local instance instHasPairingYXWithTopBot : HasPairing Y X (WithTopBot R) :=
  (show HasPairing Y X (WithBotTop R) from inferInstance)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 13.0.4 names the barrier cone of `C` and identifies it with the effective
  domain of the support function `δᵛ(· | C)`.
- `core/canonical`: the owner abstractions are the existing declarations `barr[R](C)` on the
  primal/dual pairing layer and the effective-domain owner
  `dom((δᵛ(· | C) : Y → WithTopBot R))`.
- `bridge/view`: finiteness of the codomain-lifted support value
  `(δᵛ(xStar | C) : WithTopBot R)` is the companion pointwise form of membership in
  `dom((δᵛ(· | C) : Y → WithTopBot R))`.

Domain-style sampling used here:
- the existing project owner `barrierCone`;
- the set-level membership theorem `mem_barrier_iff`;
- the support-function owner `supportFunction`;
- the specification theorem `supportFunction_def`;
- the effective-domain bridge `mem_effectiveDomain`.

Primitive data vs derived API:
- primitive objects: the subset `(barr[R](C) : Set Y)` and the effective-domain owner
  `dom((δᵛ(· | C) : Y → WithTopBot R))`;
- derived bridge: the pointwise finiteness criterion
  `(δᵛ(xStar | C) : WithTopBot R) < ⊤`.

This file uses one primitive pairing orientation `HasPairing X Y R`; the reverse orientation
needed by `supportFunction` is the canonical swapped view `HasPairing.swap`.

The source's convexity and nonemptiness hypotheses are redundant for this definition-level item:
both sides of the displayed equality make sense for an arbitrary subset of a primal space paired
with a dual space.
-/

/- Text 13.0.4: the barrier cone of a subset `C` is the canonical project declaration
`barr[R](C)`, and it is exactly the effective domain
`dom((δᵛ(· | C) : Y → WithTopBot R))`. -/
recall barrierCone

/-- A functional belongs to the barrier cone exactly when it belongs to the effective domain of
the support function. -/
theorem mem_barrierCone_iff_mem_effectiveDomain_supportFunction
    {C : Set X} {xStar : Y} :
    xStar ∈ barr[R](C) ↔ xStar ∈ dom((δᵛ(· | C) : Y → WithTopBot R)) := by
  rw [mem_effectiveDomain]
  rw [mem_barrier_iff_exists_bound, supportFunction_def]
  constructor
  · rintro ⟨β, hβ⟩
    have hβ_top : ((β : WithTopBot R) : WithTopBot R) < (⊤ : WithTopBot R) := by
      change (((β : WithBot R) : WithTop (WithBot R)) < (⊤ : WithTop (WithBot R)))
      exact WithTop.coe_lt_top (β : WithBot R)
    refine lt_of_le_of_lt (iSup_le ?_) hβ_top
    intro y
    have hyβ : (⟪xStar, y.1⟫ₚ : R) ≤ β := hβ y.1 y.2
    change (((⟪xStar, y.1⟫ₚ : R) : WithTopBot R) ≤ (β : WithTopBot R))
    exact (WithTop.coe_le_coe).2 ((WithBot.coe_le_coe).2 hyβ)
  · intro hfinite
    by_cases hC_nonempty : C.Nonempty
    · rcases hC_nonempty with ⟨x0, hx0⟩
      let s : WithTopBot R := (⨆ y : C, ((⟪xStar, y.1⟫ₚ : R) : WithTopBot R))
      have hs_finite : s < (⊤ : WithTopBot R) := by
        change (⨆ y : C, ((⟪xStar, y.1⟫ₚ : R) : WithTopBot R)) < (⊤ : WithTopBot R)
        exact hfinite
      have hbot_lt :
          (⊥ : WithTopBot R) < s := by
        have hbot_lt_x0 :
            (⊥ : WithTopBot R) < ((⟪xStar, x0⟫ₚ : R) : WithTopBot R) := by
          change ((⊥ : WithTop (WithBot R)) <
              (((⟪xStar, x0⟫ₚ : R) : WithBot R) : WithTop (WithBot R)))
          exact (WithTop.coe_lt_coe).2 (WithBot.bot_lt_coe (⟪xStar, x0⟫ₚ : R))
        exact
          lt_of_lt_of_le hbot_lt_x0
            (by
              change
                ((⟪xStar, x0⟫ₚ : R) : WithTopBot R) ≤
                  (⨆ y : C, ((⟪xStar, y.1⟫ₚ : R) : WithTopBot R))
              exact
                le_iSup (f := fun y : C ↦ ((⟪xStar, y.1⟫ₚ : R) : WithTopBot R)) ⟨x0, hx0⟩)
      have hs_ne_top : s ≠ (⊤ : WithTopBot R) := ne_of_lt hs_finite
      rcases
          (CanLift.prf (x := s) hs_ne_top :
            ∃ s' : WithBot R, ((s' : WithTopBot R) = s)) with
        ⟨s', hs'⟩
      have hs'_ne_bot : s' ≠ (⊥ : WithBot R) := by
        intro hs'_bot
        apply (bot_lt_iff_ne_bot.mp hbot_lt)
        calc
          s = (s' : WithTopBot R) := hs'.symm
          _ = (⊥ : WithTopBot R) := by simp [hs'_bot]
      rcases
          (CanLift.prf (x := s') hs'_ne_bot :
            ∃ β : R, ((β : WithBot R) = s')) with
        ⟨β, hβ⟩
      refine ⟨β, fun x hxC ↦ ?_⟩
      have hx_le :
          ((⟪xStar, x⟫ₚ : R) : WithTopBot R) ≤
            s := by
        change
          ((⟪xStar, x⟫ₚ : R) : WithTopBot R) ≤
            (⨆ y : C, ((⟪xStar, y.1⟫ₚ : R) : WithTopBot R))
        exact
          le_iSup (f := fun y : C ↦ ((⟪xStar, y.1⟫ₚ : R) : WithTopBot R)) ⟨x, hxC⟩
      have hs'_eq_β :
          (s' : WithTopBot R) = (β : WithTopBot R) := by
        simpa using congrArg (fun t : WithBot R ↦ (t : WithTopBot R)) hβ.symm
      have hxβ :
          ((⟪xStar, x⟫ₚ : R) : WithTopBot R) ≤ (β : WithTopBot R) := by
        calc
          ((⟪xStar, x⟫ₚ : R) : WithTopBot R) ≤ s := hx_le
          _ = (s' : WithTopBot R) := hs'.symm
          _ = (β : WithTopBot R) := hs'_eq_β
      have hxβ' :
          ((⟪xStar, x⟫ₚ : R) : WithBot R) ≤ (β : WithBot R) :=
        (WithTop.coe_le_coe).1 hxβ
      exact (WithBot.coe_le_coe).1 hxβ'
    · classical
      let β : R := Classical.choice (inferInstance : Nonempty R)
      refine ⟨β, fun x hxC ↦ ?_⟩
      exact (hC_nonempty ⟨x, hxC⟩).elim

/-- A functional belongs to the barrier cone exactly when the support function is finite there. -/
theorem mem_barrierCone_iff_supportFunction_lt_top
    {C : Set X} {xStar : Y} :
    xStar ∈ barr[R](C) ↔ (δᵛ(xStar | C) : WithTopBot R) < (⊤ : WithTopBot R) := by
  exact
    (mem_barrierCone_iff_mem_effectiveDomain_supportFunction (C := C) (xStar := xStar)).trans
      mem_effectiveDomain

/-- The barrier cone is exactly the effective domain of the support function. -/
theorem barrierCone_eq_effectiveDomain_supportFunction
    (C : Set X) :
    (barr[R](C) : Set Y) = dom((δᵛ(· | C) : Y → WithTopBot R)) := by
  ext xStar
  exact mem_barrierCone_iff_mem_effectiveDomain_supportFunction (C := C) (xStar := xStar)

section SelfPairing

variable {Z : Type*} [HasPairing Z Z R]

/-- In the self-pairing setting, barrier-cone membership is equivalent to effective-domain
membership for the source-facing support function owner `δᵛ(· | C)`. -/
theorem mem_barrierCone_iff_mem_effectiveDomain_supportFunction_self
    {C : Set Z} {zStar : Z} :
    zStar ∈ barr[R](C) ↔ zStar ∈ dom((δᵛ(· | C) : Z → WithTopBot R)) := by
  simpa using
    (mem_barrierCone_iff_mem_effectiveDomain_supportFunction
      (R := R) (X := Z) (Y := Z) (C := C) (xStar := zStar))

/-- Self-pairing set-level form of
`mem_barrierCone_iff_mem_effectiveDomain_supportFunction_self`. -/
theorem barrierCone_eq_effectiveDomain_supportFunction_self
    (C : Set Z) :
    (barr[R](C) : Set Z) = dom((δᵛ(· | C) : Z → WithTopBot R)) := by
  refine Set.ext ?_
  intro zStar
  exact mem_barrierCone_iff_mem_effectiveDomain_supportFunction_self
    (R := R) (C := C) (zStar := zStar)

end SelfPairing

end
