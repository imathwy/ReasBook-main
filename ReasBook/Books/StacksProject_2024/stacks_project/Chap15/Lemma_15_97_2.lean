import StacksProject_2024.stacks_project.Chap15.Lemma_15_97_1

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

/-- Helper for Lemma 15.97.2: the target automorphism that rescales the first summand by the unit
`u` and fixes the second summand. -/
private abbrev etaPresentationUnitMulTargetEquiv
    (u : Aˣ) (M : CpxA) (i : ℤ) :
    (↑(M.X i) × ↑(M.X (i + 1))) ≃ₗ[A] (↑(M.X i) × ↑(M.X (i + 1))) :=
  LinearEquiv.prodCongr
    (LinearEquiv.smulOfUnit (R := A) (M := ↑(M.X i)) u)
    (LinearEquiv.refl A ↑(M.X (i + 1)))

/-- Helper for Lemma 15.97.2: multiplying `f` by a unit only postcomposes the presentation map by
the canonical target automorphism. -/
private lemma etaPresentationLinearMap_unit_mul_factorization
    (f : A) (u : Aˣ) (M : CpxA) (i : ℤ) :
    etaPresentationLinearMap ((u : A) * f) M i =
      (LinearEquiv.toLinearMap (etaPresentationUnitMulTargetEquiv (A := A) u M i)).comp
        (etaPresentationLinearMap f M i) := by
  -- The first coordinate gains the extra unit factor, while the differential coordinate is fixed.
  ext x
  · simp only [LinearMap.prod_apply, Pi.prod, LinearMap.smul_apply, LinearMap.id_coe, id_eq,
      LinearEquiv.coe_prodCongr, LinearEquiv.refl_toLinearMap, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.prodMap_apply, map_smul, LinearEquiv.coe_coe]
    calc
      ((u : A) * f) • x = (u : A) • f • x := (smul_smul (u : A) f x).symm
      _ = f • u • x := by simpa using (smul_comm (u : A) f x)
  · simp [etaPresentationLinearMap, etaPresentationUnitMulTargetEquiv]

/-- Helper for Lemma 15.97.2: the unit-rescaled presentation map has range equal to the image of
the original range under the target automorphism. -/
private lemma etaPresentationLinearMap_unit_mul_range
    (f : A) (u : Aˣ) (M : CpxA) (i : ℤ) :
    LinearMap.range (etaPresentationLinearMap ((u : A) * f) M i) =
      (LinearMap.range (etaPresentationLinearMap f M i)).map
        (LinearEquiv.toLinearMap (etaPresentationUnitMulTargetEquiv (A := A) u M i)) := by
  -- The factorization lemma turns the new range computation into the standard `range_comp` shape.
  simpa [etaPresentationLinearMap_unit_mul_factorization]
    using
      LinearMap.range_comp
        (etaPresentationLinearMap f M i)
        (LinearEquiv.toLinearMap (etaPresentationUnitMulTargetEquiv (A := A) u M i))

-- Proof sketch: rescaling the first summand of the target product by the unit `u` carries the
-- presentation map `(f, d^i)` to `((u : A) * f, d^i)`, so it induces a canonical linear
-- equivalence between the corresponding presentation quotients.
/-- Helper for Lemma 15.97.2: the two presentation quotients are linearly equivalent after
rescaling `f` by a unit. -/
private noncomputable def etaPresentationQuotient_unitMulEquiv
    (f : A) (u : Aˣ) (M : CpxA) (i : ℤ) :
    etaPresentationQuotient f M i ≃ₗ[A] etaPresentationQuotient ((u : A) * f) M i :=
  Submodule.Quotient.equiv
    (LinearMap.range (etaPresentationLinearMap f M i))
    (LinearMap.range (etaPresentationLinearMap ((u : A) * f) M i))
    (etaPresentationUnitMulTargetEquiv (A := A) u M i)
    (etaPresentationLinearMap_unit_mul_range (A := A) f u M i).symm

/-- Lemma 15.97.2: multiplying `f` by a unit does not change the degree-`i` determinantal ideal
of a cochain complex. -/
theorem etaDeterminantalIdeal_eq_unit_mul
    (M : CpxA) (i : ℤ)
    [Module.Free A (M.X i)] [Module.Finite A (M.X i)]
    [Module.Free A (M.X (i + 1))] [Module.Finite A (M.X (i + 1))]
    (f : A) (u : Aˣ) :
    I[f]_(i)(M) = I[(u : A) * f]_(i)(M) := by
  -- Choose bases so the product term is manifestly finite, then pass finiteness to the quotient.
  let bi := Module.Free.chooseBasis A (M.X i)
  let bi1 := Module.Free.chooseBasis A (M.X (i + 1))
  let _ : Module.Finite A (M.X i × M.X (i + 1)) :=
    Module.Finite.of_basis (bi.prod bi1)
  let _ : Module.Finite A (etaPresentationQuotient f M i) :=
    Module.Finite.quotient A (LinearMap.range (etaPresentationLinearMap f M i))
  -- The determinantal ideal is the Fitting ideal of the presentation quotient, so the quotient
  -- equivalence from the unit-rescaling step gives equality immediately.
  simpa [etaDeterminantalIdeal] using
    fittingIdeal_eq_of_linearEquiv A
      (etaPresentationQuotient f M i)
      (Module.finrank A (M.X (i + 1)))
      (etaPresentationQuotient_unitMulEquiv f u M i)

end
