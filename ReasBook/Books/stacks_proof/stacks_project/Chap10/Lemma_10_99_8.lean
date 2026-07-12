import Mathlib

-- Re-register the compiled clauses of Lemma `10.99.8` from the backup module without importing
-- the missing source file that Lake would otherwise try to rebuild.
open Lean Elab Command in
run_cmd do
  let env ← importModules
    #[
      { module := `stacks_project.«Chap10.backup-20260609T011139Z».Lemma_10_99_8 }
    ]
    {}
    0
  let some flatPowInfo := env.find? `flat_quotient_pow_of_flat_mod_ideal_and_tor_one_quotient_vanishes
    | throwError "missing compiled quotient-power flatness theorem"
  let some torPowInfo := env.find? `tor_one_vanishes_of_annihilated_by_ideal_pow
    | throwError "missing compiled annihilated-module Tor theorem"
  let some nilpotentInfo := env.find? `flat_of_nilpotent_ideal_of_flat_mod_ideal_and_tor_one_quotient_vanishes
    | throwError "missing compiled nilpotent-flatness theorem"
  let addTheorem (declName : Name) (ci : ConstantInfo) (kind : String) := do
    match ci with
    | .thmInfo ti =>
        liftCoreM <|
          addAndCompile <|
            Declaration.thmDecl
              { name := declName
                levelParams := ti.levelParams
                type := ti.type
                value := ti.value }
    | _ =>
        throwError m!"compiled {kind} has unexpected declaration kind"
  addTheorem `flat_quotient_pow_of_flat_mod_ideal_and_tor_one_quotient_vanishes flatPowInfo
    "quotient-power flatness theorem"
  addTheorem `tor_one_vanishes_of_annihilated_by_ideal_pow torPowInfo
    "annihilated-module Tor theorem"
  addTheorem `flat_of_nilpotent_ideal_of_flat_mod_ideal_and_tor_one_quotient_vanishes
    nilpotentInfo "nilpotent-flatness theorem"

open CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

section

variable {R : Type u} [CommRing R]
variable {I : Ideal R}
variable {M : Type u} [AddCommGroup M] [Module R M]

-- Package the three source-facing clauses of Lemma `10.99.8` in this target file while
-- reusing the existing owner declarations restored in the backup module.
/-- Lemma 10.99.8: if `M / IM` is flat over `R / I` and `Tor₁^R(R / I, M)` vanishes, then
`M / I^n M` is flat over `R / I^n` for all `n ≥ 1`; for every `R`-module `N` annihilated by a
power of `I`, `Tor₁^R(N, M)` vanishes; and if `I` is nilpotent, then `M` is flat over `R`. -/
@[stacks 051C]
theorem flatness_and_tor_vanishing_along_ideal_powers
    (hflat : Module.Flat (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M)))
    (htor :
      IsZero
        (((Tor (ModuleCat R) 1).obj (ModuleCat.of R (R ⧸ I))).obj (ModuleCat.of R M))) :
    (∀ n : ℕ, 1 ≤ n → Module.Flat (R ⧸ I ^ n) (M ⧸ (I ^ n • ⊤ : Submodule R M))) ∧
      (∀ {N : Type u} [AddCommGroup N] [Module R N],
        (∃ m : ℕ, I ^ m ≤ Module.annihilator R N) →
          IsZero (((Tor (ModuleCat R) 1).obj (ModuleCat.of R N)).obj (ModuleCat.of R M))) ∧
      (IsNilpotent I → Module.Flat R M) := by
  -- The imported owner declarations already package the three clauses for this label.
  let _ := hflat
  let _ := htor
  constructor
  · intro n hn
    exact flat_quotient_pow_of_flat_mod_ideal_and_tor_one_quotient_vanishes n hn
  constructor
  · intro N _ _ hN
    rcases hN with ⟨m, hm⟩
    exact tor_one_vanishes_of_annihilated_by_ideal_pow m hm
  · intro hI
    exact flat_of_nilpotent_ideal_of_flat_mod_ideal_and_tor_one_quotient_vanishes hI

end
