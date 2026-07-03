import Mathlib

open Filter
open scoped Topology
open ContinuousLinearMap

section ImplicitFunctionWithParameters

variable {X Z : Type*}
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z] [CompleteSpace Z]

/-- The implicit equation `f x z = y`, viewed as the zero locus of a function on
`((y, z), x)`. -/
private def parameterEquation (f : X → Z → X) : (X × Z) × X → X :=
  fun p ↦ f p.2 p.1.2 - p.1.1

private def parameterEquationArgs : ((X × Z) × X) →L[ℂ] X × Z :=
  (snd ℂ (X × Z) X).prod ((snd ℂ X Z).comp (fst ℂ (X × Z) X))

private def parameterEquationDeriv (f' : (X × Z) →L[ℂ] X) : ((X × Z) × X) →L[ℂ] X :=
  f'.comp parameterEquationArgs - (fst ℂ X Z).comp (fst ℂ (X × Z) X)

omit [CompleteSpace X] [CompleteSpace Z] in
private theorem hasStrictFDerivAt_parameterEquation
    {f : X → Z → X} {a : X} {c : Z} {f' : (X × Z) →L[ℂ] X}
    (hf : HasStrictFDerivAt (Function.uncurry f) f' (a, c)) :
    HasStrictFDerivAt (parameterEquation f) (parameterEquationDeriv f') ((f a c, c), a) := by
  have hcomp :
      HasStrictFDerivAt (fun p : (X × Z) × X ↦ f p.2 p.1.2)
        (f'.comp parameterEquationArgs) ((f a c, c), a) := by
    simpa [parameterEquationArgs] using
      hf.comp ((f a c, c), a) parameterEquationArgs.hasStrictFDerivAt
  simpa [parameterEquation, parameterEquationDeriv] using
    hcomp.sub ((fst ℂ X Z).comp (fst ℂ (X × Z) X)).hasStrictFDerivAt

omit [CompleteSpace X] [CompleteSpace Z] in
private theorem fderiv_slice_eq_comp_inl
    {f : X → Z → X} {a : X} {c : Z} {f' : (X × Z) →L[ℂ] X}
    (hf : HasStrictFDerivAt (Function.uncurry f) f' (a, c)) :
    fderiv ℂ (fun x ↦ f x c) a = f' ∘L inl ℂ X Z := by
  have hpair : HasStrictFDerivAt (fun x : X ↦ (x, c)) (inl ℂ X Z) a := by
    simpa using (hasStrictFDerivAt_id a).prodMk (hasStrictFDerivAt_const c a)
  have hcomp : HasStrictFDerivAt (fun x ↦ f x c) (f' ∘L inl ℂ X Z) a := by
    simpa using hf.comp a hpair
  exact hcomp.hasFDerivAt.fderiv

omit [CompleteSpace X] [CompleteSpace Z] in
private theorem parameterEquationDeriv_comp_inr
    {f' : (X × Z) →L[ℂ] X} :
    parameterEquationDeriv f' ∘L inr ℂ (X × Z) X = f' ∘L inl ℂ X Z := by
  ext x
  simp [parameterEquationDeriv, parameterEquationArgs]

omit [CompleteSpace X] [CompleteSpace Z] in
private theorem parameterEquationDeriv_invertible
    {f' : (X × Z) →L[ℂ] X} (hfx : (f' ∘L inl ℂ X Z).IsInvertible) :
    (parameterEquationDeriv f' ∘L inr ℂ (X × Z) X).IsInvertible := by
  simpa [parameterEquationDeriv_comp_inr] using hfx

/-- The local solution `x = g y z` of the implicit equation `y = f x z`, obtained from the
canonical product-domain implicit-function owner. -/
noncomputable def implicitFunctionWithParameters
    {f : X → Z → X} {a : X} {c : Z} {f' : (X × Z) →L[ℂ] X}
    (hf : HasStrictFDerivAt (Function.uncurry f) f' (a, c))
    (hfx : (f' ∘L inl ℂ X Z).IsInvertible) :
    X → Z → X :=
  Function.curry <|
    (hasStrictFDerivAt_parameterEquation hf).implicitFunctionOfProdDomain
      (parameterEquationDeriv_invertible hfx)

theorem implicitFunctionWithParameters_apply_base
    {f : X → Z → X} {a : X} {c : Z} {f' : (X × Z) →L[ℂ] X}
    (hf : HasStrictFDerivAt (Function.uncurry f) f' (a, c))
    (hfx : (f' ∘L inl ℂ X Z).IsInvertible) :
    implicitFunctionWithParameters hf hfx (f a c) c = a := by
  simpa [implicitFunctionWithParameters] using
    eq_of_tendsto_nhds
      ((hasStrictFDerivAt_parameterEquation hf).tendsto_implicitFunctionOfProdDomain
        (parameterEquationDeriv_invertible hfx))

theorem eventually_leftInverse_implicitFunctionWithParameters
    {f : X → Z → X} {a : X} {c : Z} {f' : (X × Z) →L[ℂ] X}
    (hf : HasStrictFDerivAt (Function.uncurry f) f' (a, c))
    (hfx : (f' ∘L inl ℂ X Z).IsInvertible) :
    ∀ᶠ q : X × Z in 𝓝 (a, c),
      implicitFunctionWithParameters hf hfx (f q.1 q.2) q.2 = q.1 := by
  let ψ :=
    (hasStrictFDerivAt_parameterEquation hf).implicitFunctionOfProdDomain
      (parameterEquationDeriv_invertible hfx)
  have hnear :
      ∀ᶠ v : (X × Z) × X in 𝓝 (((f a c, c), a)),
        parameterEquation f v = parameterEquation f (((f a c, c), a)) ↔ ψ v.1 = v.2 :=
    (hasStrictFDerivAt_parameterEquation hf).eventually_apply_eq_iff_implicitFunctionOfProdDomain
      (parameterEquationDeriv_invertible hfx)
  have ht :
      Tendsto (fun q : X × Z ↦ ((f q.1 q.2, q.2), q.1)) (𝓝 (a, c))
        (𝓝 (((f a c, c), a))) := by
    exact ((hf.continuousAt.prodMk continuousAt_snd).prodMk continuousAt_fst).tendsto
  exact (ht.eventually hnear).mono fun q h ↦ by
    simpa [implicitFunctionWithParameters, parameterEquation, sub_eq_zero, ψ] using h

theorem eventually_rightInverse_implicitFunctionWithParameters
    {f : X → Z → X} {a : X} {c : Z} {f' : (X × Z) →L[ℂ] X}
    (hf : HasStrictFDerivAt (Function.uncurry f) f' (a, c))
    (hfx : (f' ∘L inl ℂ X Z).IsInvertible) :
    ∀ᶠ r : X × Z in 𝓝 (f a c, c),
      f (implicitFunctionWithParameters hf hfx r.1 r.2) r.2 = r.1 := by
  exact
    ((hasStrictFDerivAt_parameterEquation hf).eventually_apply_implicitFunctionOfProdDomain
      (parameterEquationDeriv_invertible hfx)).mono fun r h ↦ by
        simpa [implicitFunctionWithParameters, parameterEquation, sub_eq_zero] using h

omit [CompleteSpace X] [CompleteSpace Z] in
private theorem analyticAt_parameterEquation
    {f : X → Z → X} {a : X} {c : Z}
    (hf : AnalyticAt ℂ (Function.uncurry f) (a, c)) :
    AnalyticAt ℂ (parameterEquation f) ((f a c, c), a) := by
  have hargs : AnalyticAt ℂ (fun p : (X × Z) × X ↦ (p.2, p.1.2)) ((f a c, c), a) := by
    simpa [parameterEquationArgs] using parameterEquationArgs.analyticAt ((f a c, c), a)
  have hcomp :
      AnalyticAt ℂ (fun p : (X × Z) × X ↦ f p.2 p.1.2) ((f a c, c), a) := by
    simpa using hf.comp_of_eq hargs rfl
  simpa [parameterEquation] using
    hcomp.sub (((fst ℂ X Z).comp (fst ℂ (X × Z) X)).analyticAt ((f a c, c), a))

/-- Proposition 6.1: the local implicit function attached to `y = f x z` is holomorphic near
`(f a c, c)`. -/
theorem analytic_implicit_function_with_parameters
    {f : X → Z → X} {a : X} {c : Z}
    (hf : AnalyticAt ℂ (Function.uncurry f) (a, c))
    (hfx : (fderiv ℂ (fun x ↦ f x c) a).IsInvertible) :
    AnalyticAt ℂ
      (Function.uncurry <|
        implicitFunctionWithParameters hf.hasStrictFDerivAt
          (by
            simpa [fderiv_slice_eq_comp_inl hf.hasStrictFDerivAt] using hfx))
      (f a c, c) := by
  let ifx : ((fderiv ℂ (Function.uncurry f) (a, c)) ∘L inl ℂ X Z).IsInvertible := by
    simpa [fderiv_slice_eq_comp_inl hf.hasStrictFDerivAt] using hfx
  let φ :=
    (hasStrictFDerivAt_parameterEquation hf.hasStrictFDerivAt).implicitFunctionDataOfProdDomain
      (parameterEquationDeriv_invertible ifx)
  let i :
      ((X × Z) × X) ≃L[ℂ] X × (X × Z) :=
    φ.leftDeriv.equivProdOfSurjectiveOfIsCompl
      φ.rightDeriv φ.range_leftDeriv φ.range_rightDeriv φ.isCompl_ker
  have hφ :
      AnalyticAt ℂ φ.toOpenPartialHomeomorph φ.pt := by
    simpa [φ] using (analyticAt_parameterEquation hf).prod (analyticAt_fst : AnalyticAt ℂ
      (fun p : (X × Z) × X ↦ p.1) ((f a c, c), a))
  have hi :
      fderiv ℂ φ.toOpenPartialHomeomorph φ.pt = i := by
    simpa [i, φ, ImplicitFunctionData.toOpenPartialHomeomorph_coe] using
      φ.hasStrictFDerivAt.hasFDerivAt.fderiv
  have hsymm :
      AnalyticAt ℂ φ.toOpenPartialHomeomorph.symm (φ.prodFun φ.pt) := by
    exact φ.toOpenPartialHomeomorph.analyticAt_symm' φ.pt_mem_toOpenPartialHomeomorph_source hφ hi
  have himp :
      AnalyticAt ℂ φ.implicitFunction.uncurry (φ.prodFun φ.pt) := by
    simpa [ImplicitFunctionData.implicitFunction_def, Function.uncurry_curry] using hsymm
  have hbase :
      AnalyticAt ℂ
        (fun p : X × Z ↦ (parameterEquation f (((f a c, c), a)), p))
        (f a c, c) := by
    simpa using
      ((analyticAt_const : AnalyticAt ℂ
          (fun _ : X × Z ↦ parameterEquation f (((f a c, c), a))) (f a c, c)).prod analyticAt_id)
  have hslice :
      AnalyticAt ℂ (fun p : X × Z ↦ φ.implicitFunction (parameterEquation f (((f a c, c), a))) p)
        (f a c, c) := by
    simpa [parameterEquation, φ] using himp.comp_of_eq hbase rfl
  simpa [implicitFunctionWithParameters, HasStrictFDerivAt.implicitFunctionOfProdDomain_def,
    parameterEquation, φ, ifx] using
    analyticAt_snd.comp hslice

end ImplicitFunctionWithParameters
