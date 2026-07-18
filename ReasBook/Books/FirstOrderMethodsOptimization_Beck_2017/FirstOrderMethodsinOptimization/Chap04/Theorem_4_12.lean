import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap03.Definition_3_2
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap04.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 4.12 is `source-facing` in the chapter Fenchel-conjugacy API. Its owner declarations
are already upstream: `IsProperExtendedRealFunction` and `is_convex_function` from Chapter 2,
`extendedRealSubdifferential` from Chapter 3, `conjugate_function` from Chapter 4, and the bridge/view
theorems `pairing_eq_add_conjugate_iff_eval_mem_subdifferential_conjugate`,
`conjugate_function_eq_iff_isMaxOn_pairing_sub_function`, and
`self_eq_pairing_sub_conjugate_iff_isMaxOn_dual_of_closed_convex` from the preceding theorem
files. The only extra view language used here is Mathlib's `IsMaxOn`/`IsMinOn` over `Set.univ`, so
this file states only the textbook argmax/argmin characterizations on top of those owners instead
of introducing parallel local set wrappers.

The nonempty-effective-domain part of properness is semantically active for parts (1) and (3):
without it, `f ≡ ⊤` gives an empty extendedRealSubdifferential but every dual vector is an argmax/minimizer on
the right-hand side. For parts (2) and (4), properness is also semantically active because the
owner bridge
`pairing_eq_add_conjugate_iff_eval_mem_subdifferential_conjugate`
requires `IsProperExtendedRealFunction f`: if `f ≡ ⊥`, then `extendedRealSubdifferential (conjugate_function f)
y` is empty while the primal argmax/image set is nonempty. Lower semicontinuity and convexity are
still needed there to identify `f**` with `f`. -/

recall IsProperExtendedRealFunction
recall is_convex_function
recall extendedRealSubdifferential
recall conjugate_function
recall IsMaxOn
recall IsMinOn

-- Proof sketch: combine the Fenchel--Young equality characterization of `y ∈ ∂f(x)` with the
-- biconjugate identity for proper closed convex functions and rewrite the resulting attainment
-- statement using `IsMaxOn ... Set.univ`.
/-- Theorem 4.12 (1): for a proper closed convex extended-real-valued function, the
extendedRealSubdifferential at `x` is exactly the set of dual vectors maximizing `y' ↦ y' x - f*(y')`. -/
theorem subdifferential_eq_argmax_affine_minus_conjugate
    (f : E → EReal) (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f) (hf_convex : is_convex_function f) (x : E) :
    extendedRealSubdifferential f x =
      {y | IsMaxOn (fun y' : Module.Dual ℝ E ↦ (y' x : EReal) - conjugate_function f y')
        Set.univ y} := sorry

-- Proof sketch: specialize part (1) at `x = 0`; the affine term `y 0` vanishes, so maximizing
-- `y ↦ y 0 - f*(y)` is exactly minimizing `f*`.
/-- Theorem 4.12 (3): for a proper closed convex extended-real-valued function, the
extendedRealSubdifferential at the origin is exactly the minimizer set of the conjugate `f*`. -/
theorem subdifferential_zero_eq_argmin_conjugate
    (f : E → EReal) (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f) (hf_convex : is_convex_function f) :
    extendedRealSubdifferential f (0 : E) =
      {y | IsMinOn (conjugate_function f) Set.univ y} := sorry

-- Proof sketch: use the conjugate-side Fenchel--Young equality characterization from
-- `pairing_eq_add_conjugate_iff_eval_mem_subdifferential_conjugate`, then rewrite the primal
-- attainment statement with `conjugate_function_eq_iff_isMaxOn_pairing_sub_function`. Properness
-- is semantically active through the owner bridge on the conjugate side, while closedness and
-- convexity are what identify `f**` with `f`.
/-- Theorem 4.12 (2): for a proper closed convex extended-real-valued function, the extendedRealSubdifferential of
the conjugate at `y` is the image under the canonical double-dual map `Module.Dual.eval ℝ E` of
the maximizers of `x' ↦ y x' - f(x')`. -/
theorem subdifferential_conjugate_eq_eval_image_argmax_affine_minus
    (f : E → EReal) (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f) (hf_convex : is_convex_function f) (y : Module.Dual ℝ E) :
    extendedRealSubdifferential (conjugate_function f) y =
      (Module.Dual.eval ℝ E) ''
        {x | IsMaxOn (fun x' : E ↦ (y x' : EReal) - f x') Set.univ x} := sorry

-- Proof sketch: specialize part (2) at the zero dual vector; the affine objective becomes
-- `x ↦ -f x`, so its maximizers are exactly the minimizers of `f`, then transport them to `E**`
-- by `Module.Dual.eval ℝ E`.
/-- Theorem 4.12 (4): for a proper closed convex extended-real-valued function, at the zero dual vector
the extendedRealSubdifferential of the conjugate is the canonical double-dual image of the minimizer set of
`f`. -/
theorem subdifferential_conjugate_zero_eq_eval_image_argmin
    (f : E → EReal) (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f) (hf_convex : is_convex_function f) :
    extendedRealSubdifferential (conjugate_function f) (0 : Module.Dual ℝ E) =
      (Module.Dual.eval ℝ E) '' {x | IsMinOn f Set.univ x} := sorry

end
