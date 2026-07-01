import stacks_project.Chap15.Lemma_15_8_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Matrix

/-
Domain-style sampling for Definition 15.8.3:
- primary domain: determinantal/Fitting ideals of modules over a commutative ring, built from
  finite free presentations;
- sampled owner-level declarations:
  `Matrix.minorIdeal`,
  `presentationFittingIdeal`,
  `fittingIdeal`,
  `fittingIdealNegOne`,
  `fittingIdeal_eq_presentationFittingIdeal`;
- best owner abstraction: `presentationFittingIdeal` is the presentation-level owner attached to a
  chosen surjective finite free presentation, while `fittingIdeal` is the source-facing intrinsic
  finite-module owner obtained by taking the infimum over all such presentations, together with the
  source convention `Fit_{-1}(M) = 0`;
- primitive data: a surjective finite free presentation `π : R^n → M` for the presentation-level
  owner;
- derived API: presentation independence, the induced intrinsic module-level Fitting ideal, and
  the owner-side predecessor helper `precedingFittingIdeal`.

Source/core/bridge triage:
- `source-facing`: `fittingIdeal`, `fittingIdealNegOne`;
- `core/canonical`: `presentationFittingIdeal`;
- `bridge/view`: `fittingIdeal_eq_presentationFittingIdeal`, `precedingFittingIdeal`. -/

section

variable (R : Type u) [CommRing R]

/-- Definition 15.8.3 also fixes the convention `Fit_{-1}(M) = 0`. -/
abbrev fittingIdealNegOne : Ideal R :=
  (⊥ : Ideal R)

@[simp] theorem fittingIdealNegOne_eq_bot :
    fittingIdealNegOne R = (⊥ : Ideal R) :=
  rfl

end

section

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- The `k`th Fitting ideal attached to a finite free presentation map `R^n → M`, using the
kernel-vector matrix and the chapter's determinantal-ideal owner `Matrix.minorIdeal`. Surjectivity
is imposed only when relating this presentation-level construction to the intrinsic Fitting ideal
of `M`. -/
def presentationFittingIdeal (k : ℕ) {n : ℕ} (π : (Fin n → R) →ₗ[R] M) : Ideal R :=
  I_((n - k))((fun i x ↦ x.1 i : Matrix (Fin n) (LinearMap.ker π) R))

-- Proof sketch: stabilize two surjective finite free presentations by adding trivial summands and
-- compare the resulting kernel-vector determinant ideals after changing bases in the source free
-- modules. The determinant ideals are invariant under these operations, so the presentation ideal
-- depends only on `M` and `k`.
/-- Any two surjective finite free presentations of `M` determine the same presentation Fitting
ideal. -/
theorem presentationFittingIdeal_eq_of_surjective {n n' k : ℕ}
    (π : (Fin n → R) →ₗ[R] M) (π' : (Fin n' → R) →ₗ[R] M)
    (hπ : Function.Surjective π) (hπ' : Function.Surjective π') :
    presentationFittingIdeal R M k π = presentationFittingIdeal R M k π' := sorry

section

variable [Module.Finite R M]

private abbrev SurjectivePresentation :=
  Σ n : ℕ, { π : (Fin n → R) →ₗ[R] M // Function.Surjective π }

/-- Definition 15.8.3: for a finite `R`-module `M`, the `k`th Fitting ideal is the intrinsic
ideal obtained from the presentation-independent construction of Lemma 15.8.2; concretely, it is
the infimum of `presentationFittingIdeal k π` over all surjective maps `π : R^n → M`. -/
def fittingIdeal : ℕ → Ideal R := fun k ↦
  sInf <| Set.range fun P : SurjectivePresentation R M ↦ presentationFittingIdeal R M k P.2.1

namespace FittingIdeal

scoped notation "Fit[" R "]_(" k ")(" M ")" => fittingIdeal R M k

end FittingIdeal

open scoped FittingIdeal

/-- The Fitting ideal one step below `Fit_r(M)`, using the owner convention `Fit_{-1}(M) = 0`. -/
abbrev precedingFittingIdeal (r : ℕ) : Ideal R :=
  if r = 0 then fittingIdealNegOne R else Fit[R]_(r - 1)(M)

@[simp] theorem precedingFittingIdeal_zero :
    precedingFittingIdeal R M 0 = ⊥ := by
  simp [precedingFittingIdeal]

@[simp] theorem precedingFittingIdeal_succ (r : ℕ) :
    precedingFittingIdeal R M (r + 1) = Fit[R]_(r)(M) := by
  simp [precedingFittingIdeal]

-- Proof sketch: a surjective presentation `π` contributes the ideal
-- `presentationFittingIdeal k π` to the defining family for `fittingIdeal`. Any other
-- surjective presentation contributes the same ideal by
-- `presentationFittingIdeal_eq_of_surjective`, so the infimum of the family is exactly this
-- common value.
/-- The intrinsic Fitting ideal agrees with the Fitting ideal computed from any surjective finite
free presentation. -/
theorem fittingIdeal_eq_presentationFittingIdeal (k : ℕ) {n : ℕ}
    (π : (Fin n → R) →ₗ[R] M) (hπ : Function.Surjective π) :
    Fit[R]_(k)(M) = presentationFittingIdeal R M k π := sorry

/-- The intrinsic Fitting ideal is invariant under linear equivalence of finite modules. -/
theorem fittingIdeal_eq_of_linearEquiv {M' : Type*} [AddCommGroup M'] [Module R M']
    (k : ℕ) (e : M ≃ₗ[R] M') :
    let _ : Module.Finite R M' := Module.Finite.of_surjective (e : M →ₗ[R] M') e.surjective
    Fit[R]_(k)(M) = Fit[R]_(k)(M') := sorry

end

end
