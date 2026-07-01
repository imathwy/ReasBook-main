import stacks_project.Chap15.Lemma_15_97_1

noncomputable section

universe u

section

variable {A : Type u} [CommRing A]

local notation "CpxA" => CochainComplex (ModuleCat A) ℤ

open scoped EtaDeterminantalIdeal

/- Domain-style sampling:
- primary domain: determinantal ideals of cochain-complex presentation maps, expressed through the
  chapter Fitting-ideal owner API;
- sampled owner declarations:
  `etaDeterminantalIdeal`,
  `etaPresentationLinearMap`,
  `etaPresentationQuotient`,
  `fittingIdeal_eq_of_linearEquiv`;
- best owner abstraction:
  `source-facing`: `etaDeterminantalIdeal`, the degree-`i` ideal attached to `(f, d^i)`;
  `core/canonical`: the intrinsic Fitting ideal of the presentation quotient;
  `bridge/view`: the quotient linear equivalence induced by rescaling the first summand by a unit.
- primitive data vs. derived API: the primitive data are the degree-`i` presentation map and its
  quotient. The invariance statement is derived by transporting that quotient along the canonical
  target automorphism `LinearEquiv.prodCongr (LinearEquiv.smulOfUnit u) (LinearEquiv.refl A _)`. -/

-- Proof sketch: rescaling the first summand of the target product by the unit `u` carries the
-- presentation map `(f, d^i)` to `((u : A) * f, d^i)`, so it induces a canonical linear
-- equivalence between the corresponding presentation quotients.
private noncomputable def etaPresentationQuotient_unitMulEquiv
    (f : A) (u : Aˣ) (M : CpxA) (i : ℤ) :
    etaPresentationQuotient f M i ≃ₗ[A] etaPresentationQuotient ((u : A) * f) M i :=
  let e :=
    LinearEquiv.prodCongr (LinearEquiv.smulOfUnit u) (LinearEquiv.refl A (M.X (i + 1)))
  let η := etaPresentationLinearMap f M i
  let ηu := etaPresentationLinearMap ((u : A) * f) M i
  let hη : ηu = e.toLinearMap.comp η := by
    ext x
    · change ((u : A) * f) • x = (u : A) • (f • x)
      rw [smul_smul]
    · rfl
  let hrange : LinearMap.range ηu = (LinearMap.range η).map e.toLinearMap := by
    simpa [hη] using LinearMap.range_comp η e.toLinearMap
  Submodule.Quotient.equiv (LinearMap.range η) (LinearMap.range ηu) e hrange.symm

/-- Lemma 15.97.2: multiplying `f` by a unit does not change the degree-`i` determinantal ideal
of a cochain complex. -/
theorem etaDeterminantalIdeal_eq_unit_mul
    (M : CpxA) (i : ℤ)
    [Module.Free A (M.X i)] [Module.Finite A (M.X i)]
    [Module.Free A (M.X (i + 1))] [Module.Finite A (M.X (i + 1))]
    (f : A) (u : Aˣ) :
    I[f]_(i)(M) = I[(u : A) * f]_(i)(M) := by
  let bi := Module.Free.chooseBasis A (M.X i)
  let bi1 := Module.Free.chooseBasis A (M.X (i + 1))
  let _ : Module.Finite A (M.X i × M.X (i + 1)) :=
    Module.Finite.of_basis (bi.prod bi1)
  let _ : Module.Finite A (etaPresentationQuotient f M i) :=
    Module.Finite.quotient A (LinearMap.range (etaPresentationLinearMap f M i))
  simpa [etaDeterminantalIdeal] using
    fittingIdeal_eq_of_linearEquiv A
      (etaPresentationQuotient f M i)
      (Module.finrank A (M.X (i + 1)))
      (etaPresentationQuotient_unitMulEquiv f u M i)

end
